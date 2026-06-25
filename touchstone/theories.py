"""Specialized theories decided directly in Z3 or by enumeration/induction: IEEE-754 floats,
bounded and inductive concurrency, the agent reference monitor, dynamic typing, separation logic,
sum-of-squares nonnegativity, sequences, strings, dictionaries, the compositional IR functor law,
definite assignment, and specification mining."""
import ast
import hashlib
import inspect
import random
import sys
import textwrap
import math as _math
from fractions import Fraction as _Fr
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Tuple
import z3
from . import core
from .core import *
from .engines import *
from .domains import *


def verify_interleavings(prop, target, threads, shared0, post, semaphores=None, cooperative=False) -> Verdict:
    """A general bounded shared-memory interleaving model. Each thread is a list of primitive
    ops on shared integer variables and thread-local registers:
        ("acq", L) / ("rel", L)        acquire / release a lock (mutual exclusion)
        ("sacq", S) / ("srel", S)      acquire / release a counting semaphore (blocks at count 0)
        ("cwait", C, L) / ("cnotify", C)   condition-variable wait (release L, block until signalled) / notify
        ("await",)                     a cooperative yield point (async); a switch happens only here
        ("rd", reg, var)               reg <- shared[var]
        ("wr", var, reg)               shared[var] <- reg
        ("set", reg, fn)               reg <- fn(locals)        (local compute, fn: dict -> int)
        ("cwr", var, reg, cond)        shared[var] <- reg  if cond(locals)  (guarded write)
    Every sequentially-consistent interleaving that respects per-thread order and lock / semaphore mutual
    exclusion is simulated; the property `post(final_shared)` must hold on all of them. `semaphores` gives each
    semaphore's initial count; `cooperative` (async) restricts context switches to await points, a subset of the
    preemptive schedules (so both PROVED and REFUTED stay sound). A violating schedule is the counterexample."""
    n = len(threads)
    lengths = [len(t) for t in threads]
    sem0 = dict(semaphores or {})
    # a condition variable's notify is lost when no thread waits; this model instead lets a notify accumulate (a
    # superset of the real schedules), which is sound for PROVED but means a REFUTED is withheld (semaphores, whose
    # releases really do accumulate, stay exact).
    uses_cv = any(op[0] in ("cwait", "cnotify") for t in threads for op in t)

    def schedules(idx, run=None):
        if all(idx[i] == lengths[i] for i in range(n)):
            yield []
            return
        # cooperative (async): once a task is running, keep advancing it until it yields at an await or ends,
        # so a context switch happens only at await points (or when the running task is exhausted).
        choices = range(n) if (not cooperative or run is None or idx[run] == lengths[run]) else [run]
        for i in choices:
            if idx[i] < lengths[i]:
                nxt = list(idx); nxt[i] += 1
                nrun = None if (cooperative and threads[i][idx[i]][0] == "await") else i
                for rest in schedules(nxt, nrun if cooperative else None):
                    yield [(i, idx[i])] + rest

    feasible = bad = 0
    witness = None
    for sched in schedules([0] * n):
        shared = dict(shared0)
        locals_ = [dict() for _ in range(n)]
        held = {}
        sem = dict(sem0)
        signalled = {}                                       # condition-variable name -> outstanding notifies
        ok = True
        for tid, step in sched:
            op = threads[tid][step]
            if op[0] == "acq":
                if op[1] in held and held[op[1]] != tid:
                    ok = False; break                        # lock held: this schedule cannot occur
                held[op[1]] = tid
            elif op[0] == "rel":
                held.pop(op[1], None)
            elif op[0] == "sacq":
                if sem.get(op[1], 0) <= 0:
                    ok = False; break                        # semaphore at 0: the acquire blocks here
                sem[op[1]] -= 1
            elif op[0] == "srel":
                sem[op[1]] = sem.get(op[1], 0) + 1
            elif op[0] == "cwait":
                if signalled.get(op[1], 0) <= 0:
                    ok = False; break                        # no pending notify: the wait blocks here
                signalled[op[1]] -= 1; held.pop(op[2], None)   # consume a notify, release the monitor lock
            elif op[0] == "cnotify":
                signalled[op[1]] = signalled.get(op[1], 0) + 1
            elif op[0] == "await":
                pass                                         # a cooperative yield point: no state change
            elif op[0] == "rd":
                locals_[tid][op[1]] = shared.get(op[2], 0)
            elif op[0] == "wr":
                shared[op[1]] = locals_[tid][op[2]]
            elif op[0] == "set":
                locals_[tid][op[1]] = op[2](locals_[tid])
            elif op[0] == "cwr":
                if op[3](locals_[tid]):                       # a one-sided branch writes only when taken
                    shared[op[1]] = locals_[tid][op[2]]
            else:
                return Verdict(UNKNOWN, prop, target, "interleaving model", reason=f"bad op {op[0]}")
        if not ok:
            continue
        feasible += 1
        if not post(shared):
            bad += 1
            if witness is None:
                witness = (sched, dict(shared))
    if bad:
        if uses_cv:                                          # an accumulated-notify schedule may not be real: withhold
            return Verdict(UNKNOWN, prop, target, "interleaving model (condition variables)",
                           reason="a violating schedule rests on a condition-variable notify that may be lost; not certified")
        return Verdict(REFUTED, prop, target, "interleaving model (threads + locks)",
                       counterexample=f"a schedule yields {witness[1]} ({bad} of {feasible} violate the property)")
    return Verdict(PROVED, prop, target, "interleaving model (all sequentially-consistent schedules)",
                   reason=f"{feasible} feasible schedules, property holds on every one")


def _thread_reg_eval(node, regs, namemap):
    """Evaluate a thread statement's right-hand side over the register dict, with shared variables
    mapped to the registers they were read into."""
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
        return node.value
    if isinstance(node, ast.Name):
        return regs[namemap.get(node.id, node.id)]
    if isinstance(node, ast.BinOp):
        l = _thread_reg_eval(node.left, regs, namemap)
        r = _thread_reg_eval(node.right, regs, namemap)
        if isinstance(node.op, ast.Add): return l + r
        if isinstance(node.op, ast.Sub): return l - r
        if isinstance(node.op, ast.Mult): return l * r
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -_thread_reg_eval(node.operand, regs, namemap)
    raise Unsupported(f"thread expression {type(node).__name__}")


def _thread_cond_eval(node, regs, namemap):
    """Evaluate a branch condition over the register dict to a Python bool; shared variables resolve
    to the registers they were read into."""
    if isinstance(node, ast.BoolOp):
        vals = [_thread_cond_eval(v, regs, namemap) for v in node.values]
        return all(vals) if isinstance(node.op, ast.And) else any(vals)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return not _thread_cond_eval(node.operand, regs, namemap)
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        l = _thread_reg_eval(node.left, regs, namemap)
        r = _thread_reg_eval(node.comparators[0], regs, namemap)
        op = node.ops[0]
        if isinstance(op, ast.Lt): return l < r
        if isinstance(op, ast.LtE): return l <= r
        if isinstance(op, ast.Gt): return l > r
        if isinstance(op, ast.GtE): return l >= r
        if isinstance(op, ast.Eq): return l == r
        if isinstance(op, ast.NotEq): return l != r
        raise Unsupported("thread comparison operator")
    return _thread_reg_eval(node, regs, namemap) != 0        # bare value: truthiness


def _thread_ops(src, shared, sem_names=(), cv_names=()):
    """Translate a thread function body into interleaving ops over the shared variables. A statement
    that touches a shared variable becomes a read of each shared operand into a fresh register, a local
    compute, and (for a shared target) a write -- so a read-modify-write is three interleavable steps.
    Lock calls and `with` blocks mark critical sections."""
    mod = ast.parse(textwrap.dedent(src))                    # raw AST so `with` survives desugaring
    fn = next((n for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
    if fn is None:
        raise Unsupported("no thread function")
    ctr = [0]

    def fresh():
        ctr[0] += 1
        return f"_t{ctr[0]}"

    def emit(stmts):
        ops = []
        for s in stmts:
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Call):
                f = s.value.func
                if isinstance(f, ast.Name) and f.id == "acquire_lock":
                    ops.append(("acq", "_lock"))
                elif isinstance(f, ast.Name) and f.id == "release_lock":
                    ops.append(("rel", "_lock"))
                elif isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.attr == "acquire":
                    ops.append(("sacq" if f.value.id in sem_names else "acq", f.value.id))   # semaphore vs lock
                elif isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.attr == "release":
                    ops.append(("srel" if f.value.id in sem_names else "rel", f.value.id))
                elif isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.attr == "wait" \
                        and f.value.id in cv_names:
                    ops.append(("cwait", f.value.id, "_lock"))                              # condition-variable wait
                elif isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) \
                        and f.attr in ("notify", "notify_all") and f.value.id in cv_names:
                    ops.append(("cnotify", f.value.id))                                      # condition-variable notify
                else:
                    raise Unsupported("thread call other than a lock / semaphore / condition-variable operation")
            elif isinstance(s, ast.Expr) and isinstance(s.value, ast.Await):
                ops.append(("await",))                                                       # cooperative yield (async)
            elif isinstance(s, ast.With):
                locks = [it.context_expr.id for it in s.items if isinstance(it.context_expr, ast.Name)]
                ops += [("acq", L) for L in locks] + emit(s.body) + [("rel", L) for L in reversed(locks)]
            elif isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
                tgt = s.target.id                            # t op= e  ==  t = t op e
                expr = ast.BinOp(left=ast.Name(id=tgt, ctx=ast.Load()), op=s.op, right=s.value)
                reads = sorted({nd.id for nd in ast.walk(expr) if isinstance(nd, ast.Name) and nd.id in shared})
                namemap = {}
                for v in reads:
                    rg = fresh(); ops.append(("rd", rg, v)); namemap[v] = rg
                compute = (lambda nm, ex: (lambda regs: _thread_reg_eval(ex, regs, nm)))(namemap, expr)
                if tgt in shared:
                    rg = fresh(); ops.append(("set", rg, compute)); ops.append(("wr", tgt, rg))
                else:
                    ops.append(("set", tgt, compute))
            elif isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
                tgt, expr = s.targets[0].id, s.value
                reads = sorted({nd.id for nd in ast.walk(expr) if isinstance(nd, ast.Name) and nd.id in shared})
                namemap = {}
                for v in reads:
                    rg = fresh(); ops.append(("rd", rg, v)); namemap[v] = rg
                compute = (lambda nm, ex: (lambda regs: _thread_reg_eval(ex, regs, nm)))(namemap, expr)
                if tgt in shared:
                    rg = fresh(); ops.append(("set", rg, compute)); ops.append(("wr", tgt, rg))
                else:
                    ops.append(("set", tgt, compute))
            elif isinstance(s, ast.If):
                # Conditional update: the condition is read once, each branch is a value read, a compute,
                # and a guarded write (cwr) firing only when taken. Branches assign shared names only.
                def _branch(block):
                    out = {}
                    for st in block:
                        if not (isinstance(st, ast.Assign) and len(st.targets) == 1
                                and isinstance(st.targets[0], ast.Name) and st.targets[0].id in shared):
                            raise Unsupported("thread branch is not a simple assignment to a shared variable")
                        out[st.targets[0].id] = st.value
                    return out
                body_a, else_a = _branch(s.body), _branch(s.orelse)
                cmap = {}
                for v in sorted({nd.id for nd in ast.walk(s.test) if isinstance(nd, ast.Name) and nd.id in shared}):
                    rg = fresh(); ops.append(("rd", rg, v)); cmap[v] = rg
                cond_t = (lambda nm, test: (lambda regs: _thread_cond_eval(test, regs, nm)))(cmap, s.test)
                cond_f = (lambda f: (lambda regs: not f(regs)))(cond_t)
                for guard, arm in ((cond_t, body_a), (cond_f, else_a)):
                    for tgt in sorted(arm):
                        vmap = {}
                        for v in sorted({nd.id for nd in ast.walk(arm[tgt]) if isinstance(nd, ast.Name) and nd.id in shared}):
                            rg = fresh(); ops.append(("rd", rg, v)); vmap[v] = rg
                        compute = (lambda nm, ex: (lambda regs: _thread_reg_eval(ex, regs, nm)))(vmap, arm[tgt])
                        rg = fresh(); ops.append(("set", rg, compute)); ops.append(("cwr", tgt, rg, guard))
            elif (isinstance(s, ast.For) and isinstance(s.target, ast.Name)
                  and isinstance(s.iter, ast.Call) and isinstance(s.iter.func, ast.Name)
                  and s.iter.func.id == "range"):
                # Bounded loop: a constant range unrolls into one op-sequence per iteration, the loop
                # variable bound to each value as a thread-local. No break here, so any else always runs.
                if s.target.id in shared:
                    raise Unsupported("thread for-loop variable shadows a shared variable")
                def _ci(node):
                    if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
                        return node.value
                    if (isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub)
                            and isinstance(node.operand, ast.Constant)):
                        return -node.operand.value
                    raise Unsupported("thread for-loop needs a constant range")
                a = [_ci(x) for x in s.iter.args]
                if len(a) == 1: rng = range(0, a[0])
                elif len(a) == 2: rng = range(a[0], a[1])
                elif len(a) == 3 and a[2] != 0: rng = range(a[0], a[1], a[2])
                else: raise Unsupported("range() arity or zero step")
                rng = list(rng)
                if len(rng) > 64:
                    raise Unsupported("thread for-loop range too large to unroll")
                for iv in rng:
                    ops.append(("set", s.target.id, (lambda c: (lambda regs: c))(iv)))
                    ops += emit(s.body)
                ops += emit(s.orelse)
            else:
                raise Unsupported(f"thread statement {type(s).__name__}")
        return ops

    return emit(fn.body)


def verify_threads(prop, target, thread_srcs, shared0, post, semaphores=None, cooperative=False) -> Verdict:
    """Analyze the concurrency of thread bodies written as Python. Each thread function is translated
    into reads of the shared variables, local computes, writes, and lock acquire/release, then every
    sequentially-consistent interleaving is checked against `post(final_shared)`. A read-modify-write
    on a shared variable decomposes into a read, a compute, and a write, exposing a lost update;
    `with L:` and L.acquire()/L.release() mark critical sections; an `if`/`else` whose branches assign
    shared variables is a conditional update. `semaphores` (name -> initial count) routes S.acquire()/
    S.release() to the counting-semaphore ops and C.wait()/C.notify() to the condition variable ops;
    `cooperative` (async) makes `await` the only context-switch point. `shared0` is the initial shared
    state; any name not in it is a thread-local register."""
    sem_names = set(semaphores or {})
    cv_names = {nd.value.id for s in thread_srcs for nd in ast.walk(ast.parse(textwrap.dedent(s)))
                if isinstance(nd, ast.Attribute) and isinstance(nd.value, ast.Name)
                and nd.attr in ("wait", "notify", "notify_all")}
    try:
        threads = [_thread_ops(s, shared0, sem_names, cv_names) for s in thread_srcs]
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "concurrency (threads)", reason=str(u))
    return verify_interleavings(prop, target, threads, shared0, post, semaphores=semaphores, cooperative=cooperative)


def _atomic_section(fn):
    """The straight-line body of a thread that is one atomic critical section -- `with L: <body>`, or
    acquire_lock(); <body>; release_lock() -- or None if the thread is not so structured (and thus
    cannot soundly be treated as a single atomic step)."""
    def is_lock(call, names):
        f = call.func
        return ((isinstance(f, ast.Name) and f.id in names)
                or (isinstance(f, ast.Attribute) and f.attr in names))
    if len(fn.body) == 1 and isinstance(fn.body[0], ast.With):
        return fn.body[0].body
    ss = fn.body
    if (len(ss) >= 2 and isinstance(ss[0], ast.Expr) and isinstance(ss[0].value, ast.Call)
            and is_lock(ss[0].value, {"acquire_lock", "acquire"})
            and isinstance(ss[-1], ast.Expr) and isinstance(ss[-1].value, ast.Call)
            and is_lock(ss[-1].value, {"release_lock", "release"})):
        return ss[1:-1]
    return None


def verify_atomic_threads(prop, target, thread_src, shared0, post) -> Verdict:
    """Prove a property for ANY number of identical threads whose body is one atomic (lock-protected)
    critical section -- the all-depths complement to the bounded interleaving check. The section's net
    effect on the shared state is computed once as a transition, and an inductive relation over
    (thread_count, shared_state) discharges the property for every count via Spacer. `shared0` is the
    initial shared state; `post(count, shared)` is a Z3 Bool over the thread count and the shared
    terms. UNKNOWN unless the body is a single lock-protected straight-line section."""
    mod = ast.parse(textwrap.dedent(thread_src))
    fn = next((n for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
    if fn is None:
        return Verdict(UNKNOWN, prop, target, "concurrency (atomic, inductive)", reason="no thread function")
    body = _atomic_section(fn)
    if body is None:
        return Verdict(UNKNOWN, prop, target, "concurrency (atomic, inductive)",
                       reason="thread body is not a single lock-protected critical section")
    shared = sorted(shared0)
    ctx = Ctx({}); ctx.traps = []; ctx.pc = z3.BoolVal(True)
    cur = {v: z3.Int("s_" + v) for v in shared}
    try:
        after = _apply_assigns(body, dict(cur), ctx)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "concurrency (atomic, inductive)", reason=str(u))
    if ctx.traps:
        return Verdict(UNKNOWN, prop, target, "concurrency (atomic, inductive)", reason="trap in critical section")
    trans = {v: after.get(v, cur[v]) for v in shared}            # shared_v' as a function of the shared state
    R = z3.Function("ReachAT", *([z3.IntSort()] * (len(shared) + 1)), z3.BoolSort())
    Bad = z3.Function("BadAT", z3.BoolSort())
    fp = z3.Fixedpoint(); fp.set(engine="spacer"); fp.set("timeout", 8000)
    fp.register_relation(R); fp.register_relation(Bad)
    k = z3.Int("k")
    fp.declare_var(k, *cur.values())
    fp.rule(R(z3.IntVal(0), *[z3.IntVal(shared0[v]) for v in shared]))         # no threads done: initial state
    fp.rule(R(k + 1, *[trans[v] for v in shared]), [R(k, *[cur[v] for v in shared])])   # one atomic step
    try:
        fp.rule(Bad(), [R(k, *[cur[v] for v in shared]), k >= 0, z3.Not(post(k, dict(cur)))])
        r = core._fp_query(fp, Bad())
    except (z3.Z3Exception, TypeError, KeyError) as e:
        return Verdict(UNKNOWN, prop, target, "concurrency (atomic, inductive)", reason=str(e))
    if r == z3.unsat:
        return Verdict(PROVED, prop, target, "concurrency (atomic, inductive, all thread counts)")
    if r == z3.sat:
        return Verdict(REFUTED, prop, target, "concurrency (atomic, inductive)")
    return Verdict(UNKNOWN, prop, target, "concurrency (atomic, inductive)", reason="engine returned unknown")


def verify_float_finite(prop, target, src, finite_inputs=False) -> Verdict:
    """Prove a loop-free float function returns a finite value (no NaN, no Inf). By default the
    obligation ranges over every double, with Inf and NaN as first-class inputs, so a function that
    does not guard them is refuted; `isnan`, `isinf`, and `isfinite` (bare or `math.`-qualified) are
    modeled so a guarded function proves over the whole domain. Pass finite_inputs=True to restrict
    the claim to finite inputs. Branches, assignments, abs/min/max, and a conditional expression are
    modeled; division by 0.0 yields Inf or NaN by IEEE, so it is caught by the finiteness query."""
    fn = _parse(src).body[0]
    args = [a.arg for a in fn.args.args]
    sort, rm = z3.Float64(), z3.RNE()
    z3args = {a: z3.FP(a, sort) for a in args}

    def fev(node, env):
        if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
            return z3.FPVal(float(node.value), sort)
        if isinstance(node, ast.Name):
            if node.id not in env: raise Unsupported(f"free var {node.id}")
            return env[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return z3.fpNeg(fev(node.operand, env))
        if isinstance(node, ast.BinOp):
            l, r = fev(node.left, env), fev(node.right, env)
            if isinstance(node.op, ast.Add): return z3.fpAdd(rm, l, r)
            if isinstance(node.op, ast.Sub): return z3.fpSub(rm, l, r)
            if isinstance(node.op, ast.Mult): return z3.fpMul(rm, l, r)
            if isinstance(node.op, ast.Div): return z3.fpDiv(rm, l, r)
            raise Unsupported("float binop")
        if isinstance(node, ast.IfExp):
            return z3.If(fcond(node.test, env), fev(node.body, env), fev(node.orelse, env))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            nm = node.func.id
            if nm == "abs" and len(node.args) == 1:
                return z3.fpAbs(fev(node.args[0], env))
            if nm in ("min", "max") and node.args:
                vals = [fev(a, env) for a in node.args]; acc = vals[0]
                for x in vals[1:]:
                    acc = z3.If(z3.fpLT(x, acc), x, acc) if nm == "min" else z3.If(z3.fpGT(x, acc), x, acc)
                return acc
        raise Unsupported(f"float expr {type(node).__name__}")

    def fcond(node, env):
        if isinstance(node, ast.BoolOp):
            parts = [fcond(v, env) for v in node.values]
            return z3.And(*parts) if isinstance(node.op, ast.And) else z3.Or(*parts)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return z3.Not(fcond(node.operand, env))
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            l, r = fev(node.left, env), fev(node.comparators[0], env)
            op = node.ops[0]
            if isinstance(op, ast.Lt): return z3.fpLT(l, r)
            if isinstance(op, ast.LtE): return z3.fpLEQ(l, r)
            if isinstance(op, ast.Gt): return z3.fpGT(l, r)
            if isinstance(op, ast.GtE): return z3.fpGEQ(l, r)
            if isinstance(op, ast.Eq): return z3.fpEQ(l, r)
            if isinstance(op, ast.NotEq): return z3.fpNEQ(l, r)
        if isinstance(node, ast.Call):                       # isnan / isinf / isfinite domain guards
            nm = (node.func.attr if isinstance(node.func, ast.Attribute)
                  else node.func.id if isinstance(node.func, ast.Name) else None)
            if nm in ("isnan", "isinf", "isfinite") and len(node.args) == 1:
                x = fev(node.args[0], env)
                if nm == "isnan": return z3.fpIsNaN(x)
                if nm == "isinf": return z3.fpIsInf(x)
                return z3.Not(z3.Or(z3.fpIsNaN(x), z3.fpIsInf(x)))
        raise Unsupported("float condition")

    rets = []                                            # (path_cond, output_fp)

    def walk(stmts, env, pc):
        falls = [(dict(env), pc)]
        for s in stmts:
            nxt = []
            for e, p in falls:
                if isinstance(s, ast.Return):
                    if s.value is None: raise Unsupported("float function returns None")
                    rets.append((p, fev(s.value, e)))
                elif isinstance(s, ast.Assign):
                    if len(s.targets) != 1 or not isinstance(s.targets[0], ast.Name):
                        raise Unsupported("float complex target")
                    e2 = dict(e); e2[s.targets[0].id] = fev(s.value, e); nxt.append((e2, p))
                elif isinstance(s, ast.If):
                    c = fcond(s.test, e)
                    nxt += walk(s.body, e, z3.And(p, c))
                    nxt += walk(s.orelse, e, z3.And(p, z3.Not(c)))
                else:
                    raise Unsupported(f"float statement {type(s).__name__}")
            falls = nxt
        return falls

    try:
        walk(fn.body, z3args, z3.BoolVal(True))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "IEEE-754", reason=str(u))
    if not rets:
        return Verdict(UNKNOWN, prop, target, "IEEE-754", reason="no float return reached")
    domain = z3.And(*[z3.Not(z3.fpIsNaN(z3args[a])) for a in args],          # finite_inputs=True restricts to
                    *[z3.Not(z3.fpIsInf(z3args[a])) for a in args]) \
        if finite_inputs and args else z3.BoolVal(True)                       # finite inputs; the default is total
    bad = z3.Or(*[z3.And(pc, z3.Or(z3.fpIsNaN(out), z3.fpIsInf(out))) for pc, out in rets])
    st, model = _solve(z3.And(domain, bad))
    if st == PROVED:
        scope = "finite inputs" if finite_inputs else "every double"
        return Verdict(PROVED, prop, target, f"IEEE-754 double (always finite over {scope})")
    if st == REFUTED:
        cex = ", ".join(f"{a}={model.eval(z3args[a])}" for a in args)
        scope = "a finite input" if finite_inputs else "an input in the full double domain"
        return Verdict(REFUTED, prop, target, "IEEE-754 double",
                       counterexample=cex, reason=f"result can be NaN or Inf for {scope}")
    return Verdict(UNKNOWN, prop, target, "IEEE-754", reason="solver unknown")


def verify_two_thread_counter(prop, target, atomic, n=1) -> Verdict:
    import itertools
    ops = []
    for t in ("A", "B"):
        for k in range(n):
            ops += [("inc", t)] if atomic else [("r", t, k), ("w", t, k)]

    def legal(perm):
        pos = {op: i for i, op in enumerate(perm)}
        for t in ("A", "B"):
            for k in range(n):
                if not atomic and pos[("r", t, k)] > pos[("w", t, k)]:
                    return False
                if not atomic and k > 0:
                    if pos[("w", t, k - 1)] > pos[("r", t, k)]:
                        return False
        return True

    worst = None
    for perm in itertools.permutations(ops):
        if not legal(perm):
            continue
        x = 0; tmp = {"A": 0, "B": 0}
        for op in perm:
            if op[0] == "inc": x += 1
            elif op[0] == "r": tmp[op[1]] = x
            else: x = tmp[op[1]] + 1
        worst = x if worst is None else min(worst, x)
    if worst == 2 * n:
        return Verdict(PROVED, prop, target, "interleaving model (all schedules)",
                       reason=f"final counter == {2 * n} on every schedule")
    return Verdict(REFUTED, prop, target, "interleaving model",
                   counterexample=f"a schedule yields final counter {worst} (lost update)")


def verify_agent_policy(prop, target, actions, granted, budget) -> Verdict:
    for nm, perm, cost, g in actions:
        if perm not in granted:
            return Verdict(REFUTED, prop, target, "reference monitor",
                           counterexample=f"action '{nm}' needs permission '{perm}' not granted")
    gvars = {g: z3.Bool(g) for _, _, _, g in actions}
    total = z3.IntVal(0)
    for nm, perm, cost, g in actions:
        total = total + z3.If(gvars[g], z3.IntVal(cost), z3.IntVal(0))
    st, model = _solve_corro(total > budget)
    if st == PROVED:
        return Verdict(PROVED, prop, target, "reference monitor (all traces)",
                       reason=f"every action permitted, worst-case spend <= {budget}")
    if st == REFUTED:
        taken = [nm for nm, perm, cost, g in actions if z3.is_true(model.eval(gvars[g]))]
        return Verdict(REFUTED, prop, target, "reference monitor",
                       counterexample=f"trace {taken} exceeds budget {budget}")
    return Verdict(UNKNOWN, prop, target, "reference monitor", reason="solver unknown")


def verify_dynamic_dispatch(prop, target) -> Verdict:
    Value = z3.Datatype("Value")
    Value.declare("I", ("ival", z3.IntSort()))
    Value.declare("B", ("bval", z3.BoolSort()))
    Value.declare("NoneV")
    Value = Value.create()
    x, y = z3.Const("x", Value), z3.Const("y", Value)
    both_int = z3.And(Value.is_I(x), Value.is_I(y))
    # dynamic '+': Int+Int dispatches to integer addition, anything else is a type error
    add = z3.If(both_int, Value.I(Value.ival(x) + Value.ival(y)), Value.NoneV)
    claim = Value.is_I(add) == both_int                 # result is Int iff both are Int
    st, _ = _solve_corro(z3.Not(claim))
    if st == PROVED:
        return Verdict(PROVED, prop, target, "dynamic types (tagged union)",
                       reason="dispatch yields Int iff both operands are Int")
    return Verdict(st, prop, target, "dynamic types")


def verify_heap_frame(prop, target) -> Verdict:
    h = z3.Array("h", z3.IntSort(), z3.IntSort())
    p, q, v = z3.Ints("p q v")
    h2 = z3.Store(h, p, v)                               # *p := v
    frame = z3.Implies(q != p, z3.Select(h2, q) == z3.Select(h, q))
    st, _ = _solve_corro(z3.Not(frame))
    if st == PROVED:
        return Verdict(PROVED, prop, target, "separation logic (frame rule)",
                       reason="store through p preserves every disjoint cell q")
    return Verdict(st, prop, target, "separation logic")


def verify_array_disjoint(prop, target) -> Verdict:
    """Two arrays are disjoint regions of one heap; a write inside region A leaves every
    cell of region B unchanged. This is exactly the non-aliasing condition under which the
    functional two-array model (verify_array_loop) is sound, made explicit and proved."""
    h = z3.Array("h", z3.IntSort(), z3.IntSort())
    a_lo, a_hi, b_lo, b_hi, i, j, v = z3.Ints("a_lo a_hi b_lo b_hi i j v")
    disjoint = z3.Or(a_hi <= b_lo, b_hi <= a_lo)
    h2 = z3.Store(h, i, v)                                          # write within region A
    claim = z3.Implies(z3.And(disjoint, a_lo <= i, i < a_hi, b_lo <= j, j < b_hi),
                       z3.Select(h2, j) == z3.Select(h, j))
    st, _ = _solve_corro(z3.Not(claim))
    if st == PROVED:
        return Verdict(PROVED, prop, target, "separation logic (disjoint regions)",
                       reason="a write in region A preserves every cell of a disjoint region B")
    return Verdict(st, prop, target, "separation logic (disjoint regions)")


def verify_sl_entailment(prop, target) -> Verdict:
    """Separation-logic entailments in the points-to fragment, over the footprint
    semantics: a separating conjunction x|->a * y|->b has disjoint singleton footprints,
    which forces x != y, and the conjunction reads back its cells. Proved over all heaps."""
    h = z3.Array("h", z3.IntSort(), z3.IntSort())
    x, y, a, b, z = z3.Ints("x y a b z")
    dom1 = lambda w: w == x                                         # footprint of x|->a
    dom2 = lambda w: w == y                                         # footprint of y|->b
    disjoint = z3.ForAll([z], z3.Not(z3.And(dom1(z), dom2(z))))    # separating conjunction
    pts = z3.And(z3.Select(h, x) == a, z3.Select(h, y) == b)
    facts = [z3.Implies(disjoint, x != y),                         # sep conj => distinctness
             z3.Implies(z3.And(disjoint, pts), z3.Select(h, x) == a)]   # read-back of a cell
    st, _ = _solve_corro(z3.Not(z3.And(*facts)))
    if st == PROVED:
        return Verdict(PROVED, prop, target, "separation logic (entailment)",
                       reason="separating conjunction forces x != y and entails its cells")
    return Verdict(st, prop, target, "separation logic (entailment)")


def _cvc5_sl_entails(make):
    """Decide a separation-logic entailment with cvc5's native SL theory. `make(s, Int, Kind)` returns
    a term asserting (premise AND negated conclusion); the entailment holds over all heaps when that is
    UNSAT. Returns PROVED / REFUTED / UNKNOWN (UNKNOWN if cvc5 or its SL theory is unavailable)."""
    try:
        import cvc5
        from cvc5 import Kind
    except Exception:
        return UNKNOWN
    try:
        s = cvc5.Solver()
        s.setOption("incremental", "false")             # cvc5's SL theory is non-incremental
        s.setLogic("QF_ALL")
        Int = s.getIntegerSort()
        s.declareSepHeap(Int, Int)                      # one heap from addresses to values
        s.assertFormula(make(s, Int, Kind))
        return {"unsat": PROVED, "sat": REFUTED}.get(str(s.checkSat()), UNKNOWN)
    except Exception:
        return UNKNOWN


def verify_sl_frame_rule(prop, target) -> Verdict:
    """The separation-logic frame rule, as the adjunction between separating conjunction and the magic
    wand: any heaplet R entails P -* (P * R), so a derivation {P} c {Q} extends to {P * R} c {Q * R}
    over a disjoint frame R. cvc5's separation-logic theory proves it over every heap, beyond the
    fixed points-to cells of the older fragment."""
    def make(s, Int, K):
        x, v, y, b = (s.mkConst(Int, n) for n in "xvyb")
        P = s.mkTerm(K.SEP_PTO, x, v)
        R = s.mkTerm(K.SEP_PTO, y, b)
        adjunction = s.mkTerm(K.SEP_WAND, P, s.mkTerm(K.SEP_STAR, P, R))   # P -* (P * R)
        return s.mkTerm(K.AND, R, s.mkTerm(K.NOT, adjunction))             # R and not the adjunction
    st = _cvc5_sl_entails(make)
    if st == UNKNOWN:
        return Verdict(UNKNOWN, prop, target, "separation logic (frame rule)",
                       reason="cvc5 separation-logic theory unavailable")
    return Verdict(st, prop, target, "separation logic (frame rule via the * / -* adjunction)",
                   reason="R entails P -* (P * R): a derivation extends over any disjoint frame")


def verify_sl_magic_wand(prop, target) -> Verdict:
    """Modus ponens for the magic wand: P * (P -* Q) entails Q, over every heap. The wand is the
    spatial implication the points-to-only fragment cannot state."""
    def make(s, Int, K):
        x, v, y, b = (s.mkConst(Int, n) for n in "xvyb")
        P = s.mkTerm(K.SEP_PTO, x, v)
        Q = s.mkTerm(K.SEP_PTO, y, b)
        lhs = s.mkTerm(K.SEP_STAR, P, s.mkTerm(K.SEP_WAND, P, Q))
        return s.mkTerm(K.AND, lhs, s.mkTerm(K.NOT, Q))
    st = _cvc5_sl_entails(make)
    if st == UNKNOWN:
        return Verdict(UNKNOWN, prop, target, "separation logic (wand)",
                       reason="cvc5 separation-logic theory unavailable")
    return Verdict(st, prop, target, "separation logic (magic wand modus ponens)",
                   reason="P * (P -* Q) entails Q")


def verify_sl_separating_conjunction(prop, target, n=3) -> Verdict:
    """The separating conjunction of n single-cell assertions forces all n addresses distinct: the
    footprints are disjoint singletons, so star_{i} x_i |-> v_i entails x_i != x_j for every i != j.
    Proved over all heaps for an arbitrary n, generalizing the two-cell points-to entailment."""
    def make(s, Int, K):
        xs = [s.mkConst(Int, f"x{i}") for i in range(n)]
        vs = [s.mkConst(Int, f"v{i}") for i in range(n)]
        star = s.mkTerm(K.SEP_PTO, xs[0], vs[0])
        for i in range(1, n):
            star = s.mkTerm(K.SEP_STAR, star, s.mkTerm(K.SEP_PTO, xs[i], vs[i]))
        clash = s.mkTerm(K.OR, *[s.mkTerm(K.EQUAL, xs[i], xs[j])
                                 for i in range(n) for j in range(i + 1, n)])
        return s.mkTerm(K.AND, star, clash)
    st = _cvc5_sl_entails(make)
    if st == UNKNOWN:
        return Verdict(UNKNOWN, prop, target, "separation logic (separating conjunction)",
                       reason="cvc5 separation-logic theory unavailable")
    return Verdict(st, prop, target, f"separation logic (separating conjunction of {n} cells)",
                   reason=f"star of {n} cells forces all {n} addresses pairwise distinct")


def _sl_star(terms, s, K):
    h = terms[0]
    for t in terms[1:]:
        h = s.mkTerm(K.SEP_STAR, h, t)
    return h


def _cvc5_sl_eval(node, env, current, cells, s, K):
    """A Python int/bool expression over loaded values, initial cell values, and parameters to a cvc5
    term; p.<field> reads the current value of cell p."""
    if isinstance(node, ast.Constant) and isinstance(node.value, bool):
        return s.mkBoolean(node.value)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return s.mkInteger(node.value)
    if isinstance(node, ast.Name):
        if node.id not in env:
            raise Unsupported(f"sl: free variable {node.id}")
        return env[node.id]
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id in cells:
        return current[node.value.id]                                   # load p.field
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return s.mkTerm(K.NEG, _cvc5_sl_eval(node.operand, env, current, cells, s, K))
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return s.mkTerm(K.NOT, _cvc5_sl_eval(node.operand, env, current, cells, s, K))
    if isinstance(node, ast.BinOp):
        op = {ast.Add: K.ADD, ast.Sub: K.SUB, ast.Mult: K.MULT}.get(type(node.op))
        if op is None:
            raise Unsupported(f"sl: operator {type(node.op).__name__}")
        return s.mkTerm(op, _cvc5_sl_eval(node.left, env, current, cells, s, K),
                        _cvc5_sl_eval(node.right, env, current, cells, s, K))
    if isinstance(node, ast.BoolOp):
        op = K.AND if isinstance(node.op, ast.And) else K.OR
        return s.mkTerm(op, *[_cvc5_sl_eval(v, env, current, cells, s, K) for v in node.values])
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        l = _cvc5_sl_eval(node.left, env, current, cells, s, K)
        r = _cvc5_sl_eval(node.comparators[0], env, current, cells, s, K)
        cmp = {ast.Lt: K.LT, ast.LtE: K.LEQ, ast.Gt: K.GT, ast.GtE: K.GEQ, ast.Eq: K.EQUAL}.get(type(node.ops[0]))
        if cmp is not None:
            return s.mkTerm(cmp, l, r)
        if isinstance(node.ops[0], ast.NotEq):
            return s.mkTerm(K.NOT, s.mkTerm(K.EQUAL, l, r))
    raise Unsupported(f"sl: expression {type(node).__name__}")


def _sl_is_alloc(val):
    """True if a call expression allocates a fresh cell: object(), or a class/Node/cell constructor."""
    return (isinstance(val, ast.Call) and isinstance(val.func, ast.Name)
            and (val.func.id == "object" or val.func.id[:1].isupper()
                 or val.func.id in ("node", "cell", "new")))


def verify_sl_code(prop, target, src, cells=(), post=None, pre=None) -> Verdict:
    """Prove a separation-logic specification about the pointer code a loop-free function runs. Each name
    in `cells` is a pre-existing pointer to a one-slot heap cell; `x = object()` (or a `Node()` / `node()`
    constructor) allocates a fresh, separated cell. `p.<field>` loads a cell's value and `p.<field> = e`
    stores; using a cell name as a value gives its address, so a function can link nodes into a list.
    `post` maps every cell (parameters and allocated) to a Python expression for its final value over
    `init_<name>` (a parameter cell's initial value), other cell names (their addresses), the parameters,
    and integers; `pre` is an optional boolean constraint. cvc5's native separation-logic theory discharges
    it: the separating conjunction (cells distinct), the frame (untouched cells preserved), and a built list
    segment (a chain of separated points-to to null), all over user code. UNKNOWN if cvc5's SL theory is absent
    or the body is outside the alloc / load / store / integer-arithmetic fragment."""
    try:
        import cvc5
        from cvc5 import Kind as K
    except Exception:
        return Verdict(UNKNOWN, prop, target, "separation logic (code)", reason="cvc5 SL theory unavailable")
    fn = _fndef(src)
    params = [a.arg for a in fn.args.args]
    try:
        s = cvc5.Solver()
        s.setOption("incremental", "false")
        s.setLogic("QF_ALL")
        Int = s.getIntegerSort()
        s.declareSepHeap(Int, Int)
        allcells = list(cells)
        addr = {c: s.mkConst(Int, "addr_" + c) for c in allcells}
        env = {p: s.mkConst(Int, "param_" + p) for p in params if p not in allcells}
        for c in allcells:
            env["init_" + c] = s.mkConst(Int, "init_" + c)
            env[c] = addr[c]                                            # a cell name used as a value is its address
        current = {c: env["init_" + c] for c in allcells}
        for st in fn.body:
            if isinstance(st, (ast.Return, ast.Pass)):
                continue
            if not (isinstance(st, ast.Assign) and len(st.targets) == 1):
                raise Unsupported("sl: only single assignments, allocations, loads, and stores")
            tgt = st.targets[0]
            if isinstance(tgt, ast.Name) and _sl_is_alloc(st.value):
                c = tgt.id                                              # allocation: a fresh, separated cell
                if c not in addr:
                    addr[c] = s.mkConst(Int, "addr_" + c)
                    allcells.append(c)
                current[c] = s.mkInteger(0)                            # a fresh cell's field is null
                env[c] = addr[c]
                continue
            rhs = _cvc5_sl_eval(st.value, env, current, allcells, s, K)
            if isinstance(tgt, ast.Attribute) and isinstance(tgt.value, ast.Name) and tgt.value.id in addr:
                current[tgt.value.id] = rhs                            # store p.field = e
            elif isinstance(tgt, ast.Name):
                env[tgt.id] = rhs                                      # local binding (incl. a load)
            else:
                raise Unsupported("sl: assignment target")
        if post is None or set(post) != set(allcells):
            raise Unsupported("sl: post must give a value for each cell (parameters and allocated)")
        sp = _sl_star([s.mkTerm(K.SEP_PTO, addr[c], current[c]) for c in allcells], s, K)
        q = _sl_star([s.mkTerm(K.SEP_PTO, addr[c],
                               _cvc5_sl_eval(ast.parse(post[c], mode="eval").body, env, current, allcells, s, K))
                      for c in allcells], s, K)
        formula = s.mkTerm(K.AND, sp, s.mkTerm(K.NOT, q))
        if pre is not None:
            formula = s.mkTerm(K.AND, formula,
                               _cvc5_sl_eval(ast.parse(pre, mode="eval").body, env, current, allcells, s, K))
        s.assertFormula(formula)
        r = str(s.checkSat())
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "separation logic (code)", reason=str(u))
    except Exception as e:
        return Verdict(UNKNOWN, prop, target, "separation logic (code)", reason=str(e))
    if r == "unsat":
        return Verdict(PROVED, prop, target, "separation logic (code: points-to, separation, frame, lseg)")
    if r == "sat":
        return Verdict(REFUTED, prop, target, "separation logic (code)",
                       reason="the post-heap does not follow from the code under separation")
    return Verdict(UNKNOWN, prop, target, "separation logic (code)", reason="cvc5 returned unknown")


def _det(m):
    n = len(m)
    if n == 1:
        return m[0][0]
    if n == 2:
        return m[0][0] * m[1][1] - m[0][1] * m[1][0]
    return z3.Sum([(1 if j % 2 == 0 else -1) * m[0][j] *
                   _det([row[:j] + row[j + 1:] for row in m[1:]]) for j in range(n)])


def _z3_to_frac(v):
    """A z3 numeral as an exact Fraction, or None if it is not rational (e.g. an algebraic irrational)."""
    v = z3.simplify(v)
    if z3.is_int_value(v):
        return _Fr(v.as_long())
    if z3.is_rational_value(v):
        return _Fr(v.numerator_as_long(), v.denominator_as_long())
    return None


def _frac_det(m):
    n = len(m)
    if n == 1:
        return m[0][0]
    return sum((1 if j % 2 == 0 else -1) * m[0][j] * _frac_det([r[:j] + r[j + 1:] for r in m[1:]]) for j in range(n))


def _sos_certificate_valid(poly, nvars, degree, exps, Qf):
    """Check the certificate p = b^T Q b in exact rational arithmetic: Q symmetric PSD (every principal minor >= 0)
    and the identity holds on the grid [-degree, degree]^nvars (which pins a degree-<=degree identity)."""
    import itertools
    k = len(exps)
    for i in range(k):
        for j in range(k):
            if Qf[i][j] != Qf[j][i]:
                return False
    for size in range(1, k + 1):
        for idx in itertools.combinations(range(k), size):
            if _frac_det([[Qf[i][j] for j in idx] for i in idx]) < 0:
                return False

    def mono(e, vals):
        r = _Fr(1)
        for i in range(nvars):
            r *= _Fr(vals[i]) ** e[i]
        return r
    for grid in itertools.product(range(-degree, degree + 1), repeat=nvars):
        pv = z3.simplify(poly([z3.IntVal(g) for g in grid]))
        if not z3.is_int_value(pv):
            return False
        if _Fr(pv.as_long()) != sum(Qf[i][j] * mono(exps[i], grid) * mono(exps[j], grid)
                                    for i in range(k) for j in range(k)):
            return False
    return True


def verify_sos_nonneg(prop, target, poly, nvars, degree=2) -> Verdict:
    import itertools
    if not callable(poly):
        raise TypeError("poly must be a callable mapping a variable list to a z3 term")
    if not isinstance(nvars, int) or nvars < 1:
        raise TypeError("nvars must be a positive int, got %r" % (nvars,))
    if not isinstance(degree, int) or degree < 2 or degree % 2:
        raise TypeError("degree must be an even int >= 2, got %r" % (degree,))
    half = degree // 2
    xs = [z3.Int(f"x{i}") for i in range(nvars)]
    exps = []                                                    # monomial basis up to degree half
    for total in range(half + 1):
        for combo in itertools.combinations_with_replacement(range(nvars), total):
            e = [0] * nvars
            for c in combo:
                e[c] += 1
            exps.append(tuple(e))
    k = len(exps)

    def mono_z3(e, vals):
        r = z3.IntVal(1)
        for i in range(nvars):
            for _ in range(e[i]):
                r = r * (z3.IntVal(vals[i]) if vals is not None else xs[i])
        return r

    Q = [[z3.Real(f"q_{min(i, j)}_{max(i, j)}") for j in range(k)] for i in range(k)]
    s = z3.Solver(); s.set("rlimit", core.SOS_RLIMIT); s.set("timeout", 60000)   # rlimit binds; timeout a backstop
    for grid in itertools.product(range(-degree, degree + 1), repeat=nvars):   # coefficient match
        pv = z3.simplify(z3.substitute(poly(xs), *[(xs[i], z3.IntVal(grid[i])) for i in range(nvars)]))
        bvals = [mono_z3(e, list(grid)) for e in exps]
        s.add(z3.ToReal(pv) == z3.Sum([Q[i][j] * z3.ToReal(bvals[i]) * z3.ToReal(bvals[j])
                                       for i in range(k) for j in range(k)]))
    for size in range(1, k + 1):                                 # PSD: all principal minors >= 0
        for idx in itertools.combinations(range(k), size):
            s.add(_det([[Q[i][j] for j in idx] for i in idx]) >= 0)
    if s.check() != z3.sat:
        return Verdict(UNKNOWN, prop, target, "SOS", reason=f"no degree-{degree} SOS over the basis")
    m = s.model()
    Qv = [[m.eval(Q[i][j], model_completion=True) for j in range(k)] for i in range(k)]
    Qf = [[_z3_to_frac(Qv[i][j]) for j in range(k)] for i in range(k)]
    if all(x is not None for row in Qf for x in row) and _sos_certificate_valid(poly, nvars, degree, exps, Qf):
        return Verdict(PROVED, prop, target, f"sum-of-squares (Positivstellensatz, degree {degree})",
                       reason="p = b^T Q b, Q positive semidefinite; certificate checked in exact rational arithmetic",
                       certificate=proof_certificate("checked SOS certificate (exact rational)"))
    bsym = [mono_z3(e, None) for e in exps]                       # fall back to the solver-checked identity
    quad_sym = z3.Sum([Qv[i][j] * z3.ToReal(bsym[i]) * z3.ToReal(bsym[j])
                       for i in range(k) for j in range(k)])
    chk, _ = _solve_corro(z3.ToReal(poly(xs)) != quad_sym)
    if chk == PROVED:
        return Verdict(PROVED, prop, target, f"sum-of-squares (Positivstellensatz, degree {degree})",
                       reason="p = b^T Q b with Q positive semidefinite (identity verified)")
    return Verdict(UNKNOWN, prop, target, "SOS", reason="candidate decomposition was not exact")


def verify_list_segment(prop, target, buggy=False) -> Verdict:
    Addr = z3.IntSort()
    ArrS = z3.ArraySort(Addr, Addr)
    null = z3.IntVal(0)
    wf = z3.Function("wf", ArrS, Addr, Addr, z3.BoolSort())             # length-n list to null
    Bad = z3.Function("BadSL", z3.BoolSort())
    fp = z3.Fixedpoint(); fp.set(engine="spacer"); fp.set("timeout", 8000)
    fp.register_relation(wf); fp.register_relation(Bad)
    h = z3.Const("h", ArrS)
    x, n = z3.Consts("x n", Addr)
    fp.declare_var(h, x, n)
    fp.rule(wf(h, null, z3.IntVal(0)))                                  # empty list is null, length 0
    if buggy:
        fp.rule(wf(h, null, z3.IntVal(1)))                             # corrupt: null with length 1
    fp.rule(wf(h, x, n), [x != null, n > 0, wf(h, z3.Select(h, x), n - 1)])
    # structural invariants of the recursive predicate: a non-empty list has a non-null
    # head, and every well-formed list has non-negative length.
    fp.rule(Bad(), [wf(h, x, n), n > 0, x == null])
    fp.rule(Bad(), [wf(h, x, n), n < 0])
    try:
        r = core._fp_query(fp, Bad())
    except z3.Z3Exception as e:
        return Verdict(UNKNOWN, prop, target, "separation logic (lseg)", reason=str(e))
    if r == z3.unsat:
        return Verdict(PROVED, prop, target, "separation logic (recursive predicate)",
                       reason="wf list invariant: a non-empty list has a non-null head, length >= 0")
    if r == z3.sat:
        return Verdict(REFUTED, prop, target, "separation logic (recursive predicate)",
                       reason="the recursive predicate admits an ill-formed list")
    return Verdict(UNKNOWN, prop, target, "separation logic (lseg)", reason="engine returned unknown")


def verify_ir_functor(prop, target, src1, src2) -> Verdict:
    p, q = lower_to_ir(src1), lower_to_ir(src2)
    names = {v for v, _ in p + q}
    for _v, e in p + q:
        names |= {n.id for n in ast.walk(e) if isinstance(n, ast.Name)}
    state = {v: z3.Int(v) for v in sorted(names)}
    ctx = Ctx({})
    lhs = denote_ir(compose_ir(p, q), state, ctx)                # denote(p ++ q)
    rhs = denote_ir(q, denote_ir(p, state, ctx), ctx)           # denote q . denote p
    st, _ = _solve_corro(z3.Not(z3.And(*[lhs[v] == rhs[v] for v in state])))
    if st == PROVED:
        return Verdict(PROVED, prop, target, "core IR (functor composition law)",
                       reason="denote(p++q) == denote q . denote p on all inputs")
    return Verdict(st, prop, target, "core IR")


def verify_seq_property(prop, target) -> Verdict:
    IntSeq = z3.SeqSort(z3.IntSort())
    a, b = z3.Consts("a b", IntSeq)
    x, i = z3.Int("x"), z3.Int("i")
    facts = [z3.Length(z3.Concat(a, z3.Unit(x))) == z3.Length(a) + 1,           # append grows by 1
             z3.Length(z3.Concat(a, b)) == z3.Length(a) + z3.Length(b),         # concat is additive
             z3.Implies(z3.And(0 <= i, i < z3.Length(a)),
                        z3.Length(z3.Extract(a, i, 1)) == 1)]                    # slice a[i:i+1]
    st, _ = _solve_corro(z3.Not(z3.And(*facts)))
    if st == PROVED:
        return Verdict(PROVED, prop, target, "sequence theory (lists)",
                       reason="append and concat lengths and in-bounds slicing are sound")
    return Verdict(st, prop, target, "sequence theory")


def verify_concurrent_counter(prop, target, threads, atomic) -> Verdict:
    import itertools
    ops = []
    for t in range(threads):
        ops += [("inc", t)] if atomic else [("r", t), ("w", t)]
    worst = None
    for perm in itertools.permutations(range(len(ops))):
        seq = [ops[k] for k in perm]
        ok = True
        for t in range(threads):                                   # per-thread program order
            if not atomic and seq.index(("r", t)) > seq.index(("w", t)):
                ok = False; break
        if not ok:
            continue
        x = 0; tmp = {}
        for o in seq:
            if o[0] == "inc": x += 1
            elif o[0] == "r": tmp[o[1]] = x
            else: x = tmp[o[1]] + 1
        worst = x if worst is None else min(worst, x)
    if worst == threads:
        return Verdict(PROVED, prop, target, "interleaving model (all schedules)",
                       reason=f"final == {threads} on every schedule (race-free)")
    return Verdict(REFUTED, prop, target, "interleaving model",
                   counterexample=f"a schedule yields final {worst} < {threads} (lost update)")


def verify_locked_counter(prop, target) -> Verdict:
    """N threads each increment a shared counter once under a lock (atomic critical
    section). Prove the final value equals N for EVERY thread count, by induction over
    the number of completed threads (CHC), rather than enumerating schedules."""
    Counter = z3.Function("Counter", z3.IntSort(), z3.IntSort(), z3.BoolSort())   # (done, val)
    Bad = z3.Function("BadCnt", z3.IntSort(), z3.BoolSort())
    fp = z3.Fixedpoint(); fp.set(engine="spacer"); fp.set("timeout", 8000)
    fp.register_relation(Counter); fp.register_relation(Bad)
    N, k, v = z3.Ints("N k v")
    fp.declare_var(N, k, v)
    fp.rule(Counter(0, 0))                                       # no threads done, count 0
    fp.rule(Counter(k + 1, v + 1), [Counter(k, v)])             # one atomic increment
    fp.rule(Bad(N), [Counter(N, v), N >= 0, v != N])
    try:
        r = core._fp_query(fp, Bad(N))
    except z3.Z3Exception as e:
        return Verdict(UNKNOWN, prop, target, "concurrency (inductive)", reason=str(e))
    if r == z3.unsat:
        return Verdict(PROVED, prop, target, "concurrency (inductive, all thread counts)",
                       reason="a lock-serialized counter ends at N for every N")
    return Verdict(REFUTED, prop, target, "concurrency (inductive)")


def verify_concurrent_counter_inductive(prop, target, atomic) -> Verdict:
    """Decide race-freedom of an N-thread counter for EVERY thread count at once, by
    induction (CHC), not by enumerating one fixed N's schedules. Atomic increments end
    at N for all N (proved). A non-atomic read-modify-write admits a lost-update
    schedule -- every thread reads the same initial 0 and writes 1 -- whose final count
    is 1, and 1 < N for every N >= 2, refuted here by an inductive witness relation."""
    fp = z3.Fixedpoint(); fp.set(engine="spacer"); fp.set("timeout", 8000)
    N, k, v = z3.Ints("N k v")
    if atomic:
        Counter = z3.Function("CounterAI", z3.IntSort(), z3.IntSort(), z3.BoolSort())  # (done, val)
        Bad = z3.Function("BadAI", z3.IntSort(), z3.BoolSort())
        fp.register_relation(Counter); fp.register_relation(Bad)
        fp.declare_var(N, k, v)
        fp.rule(Counter(0, 0))
        fp.rule(Counter(k + 1, v + 1), [Counter(k, v)])         # one atomic increment
        fp.rule(Bad(N), [Counter(N, v), N >= 0, v != N])
        try:
            r = core._fp_query(fp, Bad(N))
        except z3.Z3Exception as e:
            return Verdict(UNKNOWN, prop, target, "concurrency (inductive)", reason=str(e))
        if r == z3.unsat:
            return Verdict(PROVED, prop, target, "concurrency (inductive, all thread counts)",
                           reason="atomic increments end at N for every N")
        return Verdict(REFUTED, prop, target, "concurrency (inductive)")
    Wit = z3.Function("WitNAI", z3.IntSort(), z3.IntSort(), z3.BoolSort())   # (threads, a reachable final)
    Bad = z3.Function("BadNAI", z3.IntSort(), z3.BoolSort())
    fp.register_relation(Wit); fp.register_relation(Bad)
    fp.declare_var(N, k, v)
    fp.rule(Wit(1, 1))                                          # one increment: read 0, write 1
    fp.rule(Wit(k + 1, 1), [Wit(k, 1)])                        # the next thread also reads 0, writes 1
    fp.rule(Bad(N), [Wit(N, v), N >= 2, v != N])              # a schedule whose final value != N
    try:
        r = core._fp_query(fp, Bad(N))
    except z3.Z3Exception as e:
        return Verdict(UNKNOWN, prop, target, "concurrency (inductive)", reason=str(e))
    if r == z3.sat:
        return Verdict(REFUTED, prop, target, "concurrency (inductive, all thread counts)",
                       reason="non-atomic loses updates: a schedule ends at 1 < N for every N >= 2")
    return Verdict(UNKNOWN, prop, target, "concurrency (inductive)", reason="engine returned unknown")


def verify_rely_guarantee(prop, target, statevars, init, steps, inv, post=None) -> Verdict:
    """Establish a concurrency property for every schedule and every depth by a rely-guarantee
    argument over a global invariant, rather than by bounding the interleavings. `statevars` names the
    shared integer state; `init(s)`, `inv(s)`, and the optional `post(s)` are predicates over a state
    dict; `steps` is a list of (label, relation) where relation(s, s2) is one thread's atomic
    guarantee. The invariant must hold initially and be preserved by every thread's step, which is
    exactly stability under the rely (the union of the other threads' guarantees); a global invariant
    inductive under every step holds in every reachable state under any interleaving, so the property
    that follows from it holds for all schedules and all depths."""
    s = {v: z3.Int("s_" + v) for v in statevars}
    s2 = {v: z3.Int("t_" + v) for v in statevars}
    if _solve(z3.And(init(s), z3.Not(inv(s))))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "rely-guarantee", reason="invariant does not hold initially")
    for lbl, step in steps:                                  # inductiveness under each guarantee = rely-stability
        if _solve(z3.And(inv(s), step(s, s2), z3.Not(inv(s2))))[0] != PROVED:
            return Verdict(UNKNOWN, prop, target, "rely-guarantee",
                           reason=f"invariant not stable under thread step '{lbl}'")
    if post is not None and _solve(z3.And(inv(s), z3.Not(post(s))))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "rely-guarantee", reason="the invariant does not imply the property")
    return Verdict(PROVED, prop, target, "rely-guarantee (stable under every thread; all schedules, all depths)",
                   reason="global invariant inductive under every thread's guarantee")


def verify_deadlock_free(prop, target, same_order) -> Verdict:
    # two threads each acquire locks L0 and L1; deadlock iff they can hold one and wait
    # for the other. Consistent acquisition order makes that unreachable.
    import itertools
    order_a = [0, 1]
    order_b = [0, 1] if same_order else [1, 0]
    deadlock = False
    # interleave the two acquire sequences; a deadlock state = A holds order_a[0],
    # B holds order_b[0], and each next wants a lock the other holds.
    for interleave in itertools.permutations(["a0", "a1", "b0", "b1"]):
        held = {}                                          # lock -> owner
        stuck = False
        seq_a, seq_b = list(order_a), list(order_b)
        ia = ib = 0
        for step in interleave:
            who = step[0]; want = order_a[ia] if who == "a" else order_b[ib]
            if want in held and held[want] != who:
                stuck = True                               # blocked, cannot proceed in this order
                break
            held[want] = who
            if who == "a": ia += 1
            else: ib += 1
        if stuck and len(held) == 2 and len(set(held.values())) == 2:
            deadlock = True; break
    if not deadlock:
        return Verdict(PROVED, prop, target, "deadlock freedom (lock ordering)",
                       reason="consistent lock acquisition order: no circular wait")
    return Verdict(REFUTED, prop, target, "deadlock freedom",
                   counterexample="inconsistent acquisition order admits a circular wait")


def verify_definite_assignment(prop, target, src) -> Verdict:
    bad = _use_before_def(src)
    if bad:
        return Verdict(REFUTED, prop, target, "definite assignment",
                       counterexample=f"possible use before assignment: {bad}")
    return Verdict(PROVED, prop, target, "definite assignment",
                   reason="every variable is assigned before use on all paths")


def mine_spec(src, repo=None):
    repo = repo or {}
    args = _argnames(src)
    mined = []
    r = infer_and_verify_range("mine", "f", src)
    if r.status == PROVED:
        mined.append(r.reason)
    cands = [("out >= 0", lambda za, o: o >= 0), ("out <= 0", lambda za, o: o <= 0),
             ("out is even", lambda za, o: o % 2 == 0)]
    for a in args:
        cands.append((f"out >= {a}", lambda za, o, a=a: o >= za[a]))
        cands.append((f"out <= {a}", lambda za, o, a=a: o <= za[a]))
    for lbl, pred in cands:
        try:
            if verify_predicate("mine", "f", src, pred, repo).status == PROVED:
                mined.append(lbl)
        except Exception:
            pass
    return mined


def verify_string_property(prop, target) -> Verdict:
    a, b = z3.Strings("a b")
    facts = [z3.Length(z3.Concat(a, b)) == z3.Length(a) + z3.Length(b),
             z3.Implies(z3.Contains(a, b), z3.Length(b) <= z3.Length(a)),
             z3.Concat(z3.Empty(z3.StringSort()), a) == a]
    st, _ = _solve_corro(z3.Not(z3.And(*facts)))
    if st == PROVED:
        return Verdict(PROVED, prop, target, "string theory",
                       reason="concatenation length, containment length, and empty identity hold")
    return Verdict(st, prop, target, "string theory")


def verify_dict_property(prop, target) -> Verdict:
    K, V = z3.IntSort(), z3.IntSort()
    d = z3.Array("d", K, V)
    present = z3.Array("present", K, z3.BoolSort())
    k1, k2, v = z3.Ints("k1 k2 v")
    d2 = z3.Store(d, k1, v)
    p2 = z3.Store(present, k1, z3.BoolVal(True))
    facts = [z3.Select(d2, k1) == v,                                    # read-after-write
             z3.Implies(k2 != k1, z3.Select(d2, k2) == z3.Select(d, k2)),   # frame
             z3.Select(p2, k1) == True]                                 # key now present
    st, _ = _solve_corro(z3.Not(z3.And(*facts)))
    if st == PROVED:
        return Verdict(PROVED, prop, target, "dictionary (array + key set)",
                       reason="read-after-write, frame on other keys, and membership hold")
    return Verdict(st, prop, target, "dictionary")


__all__ = [
    'verify_interleavings',
    '_thread_reg_eval',
    '_thread_cond_eval',
    '_thread_ops',
    'verify_threads',
    '_atomic_section',
    'verify_atomic_threads',
    'verify_float_finite',
    'verify_two_thread_counter',
    'verify_agent_policy',
    'verify_dynamic_dispatch',
    'verify_heap_frame',
    'verify_array_disjoint',
    'verify_sl_entailment',
    'verify_sl_frame_rule',
    'verify_sl_magic_wand',
    'verify_sl_separating_conjunction',
    '_sl_star',
    '_cvc5_sl_eval',
    '_sl_is_alloc',
    'verify_sl_code',
    '_det',
    'verify_sos_nonneg',
    'verify_list_segment',
    'verify_ir_functor',
    'verify_seq_property',
    'verify_concurrent_counter',
    'verify_locked_counter',
    'verify_concurrent_counter_inductive',
    'verify_rely_guarantee',
    'verify_deadlock_free',
    'verify_definite_assignment',
    'mine_spec',
    'verify_string_property',
    'verify_dict_property',
]
