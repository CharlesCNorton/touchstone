"""Core: verdicts, the modeled-subset parser, symbolic execution into Z3, the exact
integer-division encoding, and the solver portfolio. Everything else builds on this."""
import ast
import hashlib
import inspect
import os
import random
import struct
import subprocess
import sys
import textwrap
from fractions import Fraction as _Fr
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Callable, Dict, List, Optional, Tuple
import z3

z3.set_param("smt.random_seed", 1)
z3.set_param("sat.random_seed", 1)
z3.set_param("fp.spacer.random_seed", 0)     # the Fixedpoint/Spacer engines, deterministic across machines
for _stream in (sys.stdout, sys.stderr):
    try:
        _stream.reconfigure(encoding="utf-8")
    except (AttributeError, ValueError):
        pass

# Runtime flags (single home; read elsewhere as core.<flag> so live toggling propagates).
ALLOW_SUBJECT_EXECUTION = False
BEST_EFFORT = False                      # opt-in (off by default): assume an unmodeled call / trapping method
#                                          is well-behaved instead of abstaining. Lower trust; relaxes traps only.
BEST_EFFORT_ASSUMED = False              # taint: a best-effort assumption was actually used (else verdict = full trust)
REQUIRE_CORROBORATION = True             # confirm a PROVED with a second procedure (cvc5, SOS certificate, or
#                                          real-relaxation nlsat); False is a labeled single-solver lower-trust mode
CROSS_VALIDATE_DOMAINS = True
RECORD_OBLIGATIONS = None                # when a list, _solve appends each PROVED refutation query, so a
#                                          corpus run collects the engine's real obligations for SMTCoq export
CHECK_MACHINE_OVERFLOW = True            # run the fixed-width companion alongside integer proofs
MACHINE_WIDTH = 64                       # default signed width for that companion (no per-call choice)
SANDBOX_SUBJECT = True                   # run the concrete differential check in an isolated process,
#                                          which lets it default on without trusting the subject in-process
# Scan triage budgets: a whole-repo scan triages every unit, so one pathological unit (a giant generated body or
# a runaway engine path) must not stall or OOM the run. SCAN_UNIT_NODE_BUDGET is the deterministic primary guard
# -- a unit whose AST exceeds it is skipped to UNKNOWN before any engine runs (reproducible). SCAN_UNIT_TIMEOUT_S
# is a per-unit wall-clock backstop (SIGALRM, main thread only) for a small-but-pathological unit the size cap
# misses; 0 disables it for a fully deterministic (rlimit-only) scan. Both are scan-only; a direct check / prove
# is not bounded here and stays rlimit-bound.
SCAN_UNIT_NODE_BUDGET = 10000            # skip (UNKNOWN) a scanned function / method whose AST exceeds this
SCAN_UNIT_TIMEOUT_S = 30                 # per-unit wall-clock backstop for a scan; 0 disables
_SCAN_CRASH_ON = None                    # test hook only: a scan unit whose label contains this aborts its worker,
#                                          exercising the crash-tolerant pool (engines._run_unit_pool). None in use.
# Solver tuning, configurable rather than hardcoded (see configure()).
SOLVE_TIMEOUT_MS = 60000                 # wall-clock backstop only; the rlimit below is the binding,
#                                          machine-independent cutoff, so this is set high to not bind first
FP_SOLVE_TIMEOUT_MS = 60000              # wall-clock backstop for a bit-blasted floating-point solve
SOLVE_RLIMIT = 16000000                  # deterministic resource bound: identical input yields an identical
#                                          verdict on every machine, independent of wall-clock speed
FP_SOLVE_RLIMIT = 400000000              # deterministic bound for the bit-blasted float path; set high enough
#                                          not to bind on a decidable FP query (a double bit-blast costs far
#                                          more than the integer path)
CVC5_RLIMIT = 12000000                   # deterministic resource bound for cvc5 (rlimit, not wall-clock tlimit)
SOS_RLIMIT = 80000000                    # deterministic bound for the (nonlinear) SOS Gram-matrix synthesis
BUDGET_ESCALATE_CAP = 200000000          # rlimit ceiling for one auto-escalation of a budget-bound UNKNOWN
_BUDGET_ESCALATING = False               # re-entrancy guard so an escalated retry does not escalate again
CHC_FAST_MS = 2000                       # single-loop Spacer budget before invariant synthesis kicks in
_TRAPFREE = False                        # trap-freedom over-approximation: the value engine is total -- loops
#                                          are checked by havoc, complex targets and unmodeled operations
#                                          (opaque truthiness/equality, None/bytes) raise no trap. Set only by
#                                          _trap_free_via_symexec, so the exact equivalence engines are unaffected.

# z3's own memory cap (MB): a runaway engine path (e.g. a giant generated body unrolled into an enormous z3
# term) grows z3-allocated memory unbounded -- neither the rlimit (it bounds solving work, not term building)
# nor a wall-clock signal (a Unix signal is deferred through a long z3 C call) catches that. memory_max_size
# makes z3 raise a catchable "out of memory" at the next allocation past the cap, so a scan degrades the unit
# to UNKNOWN instead of OOMing the process. Caps only z3's own allocations (not the repo dict), so it is safe
# on the serial path too; global and applied at import, so every spawn worker that re-imports the package gets
# it without extra plumbing. Generous, so it binds only a genuine runaway, never a normal solve.
Z3_MAX_MEMORY_MB = 3000
z3.set_param("memory_max_size", Z3_MAX_MEMORY_MB)


def configure(**kw):
    """Set solver tuning parameters at runtime instead of editing the source. Recognized keys:
    solve_timeout_ms, fp_solve_timeout_ms, chc_fast_ms, machine_width. Unknown keys raise, so a
    typo fails loudly rather than being silently ignored. Returns the prior values."""
    keys = {"solve_timeout_ms": "SOLVE_TIMEOUT_MS", "fp_solve_timeout_ms": "FP_SOLVE_TIMEOUT_MS",
            "chc_fast_ms": "CHC_FAST_MS", "machine_width": "MACHINE_WIDTH", "solve_rlimit": "SOLVE_RLIMIT",
            "fp_solve_rlimit": "FP_SOLVE_RLIMIT", "cvc5_rlimit": "CVC5_RLIMIT", "sos_rlimit": "SOS_RLIMIT"}
    g = globals()
    prior = {}
    for k, v in kw.items():
        if k not in keys:
            raise ValueError(f"unknown setting {k!r}; known: {sorted(keys)}")
        prior[k] = g[keys[k]]
        g[keys[k]] = v
    return prior


def _best_effort_assume():
    """Set the taint: a best-effort assumption was used on this run."""
    global BEST_EFFORT_ASSUMED
    BEST_EFFORT_ASSUMED = True


def _note_overapprox(ctx, what):
    """Mark the over-approximation channel used, recording the FIRST abstraction's provenance (the operation
    and the line being evaluated), so an approximation UNKNOWN names its real cause instead of a canned string."""
    ctx.overapprox = True
    if ctx.overapprox_reason is None:
        ln = getattr(ctx, "_cur_line", None)
        ctx.overapprox_reason = "%s yields an over-approximated value%s" % (
            what, " (line %d)" % ln if ln else "")


def _overapprox(ctx, label, sort, name):
    """The over-approximation-channel guard shared by the str abstractions (strip / case maps, the is*
    predicates, count, replace, pad). With no facts carried, return a fresh unconstrained term of `sort`
    when only traps matter (_TRAPFREE), else the op has no sound channel and is Unsupported. With facts
    carried, record the abstraction's provenance and return None so the caller builds its constrained
    result."""
    if ctx.facts is None:
        if _TRAPFREE:
            return z3.FreshConst(sort, name)
        raise Unsupported(f"{label} needs the over-approximation channel (use prove / verify_predicate)")
    _note_overapprox(ctx, label)
    return None


class _TrapList(list):
    """A trap-condition list that also records, per appended condition, the source line being evaluated
    (ctx._cur_line at append time), so a trap refutation can name the offending line symbolically -- with no
    execution and without instrumenting every trap site (it IS a list, so every reader is unchanged)."""
    def __init__(self, ctx):
        super().__init__()
        self.lines = []
        self._ctx = ctx

    def append(self, cond):
        super().append(cond)
        self.lines.append(getattr(self._ctx, "_cur_line", None))


def _unchain_compare(node):
    """`a < b < c` -> `(a < b) and (b < c)`; a single-op compare is returned unchanged. The middle operands are
    re-read in each conjunct, which matches Python exactly here because spec and body expressions are pure."""
    if not isinstance(node, ast.Compare) or len(node.ops) <= 1:
        return node
    operands = [node.left] + node.comparators
    parts = [ast.Compare(left=operands[i], ops=[node.ops[i]], comparators=[operands[i + 1]])
             for i in range(len(node.ops))]
    return ast.BoolOp(op=ast.And(), values=parts)


class _SpecDesugar(ast.NodeTransformer):
    """Chained-comparison desugaring for a require/ensure expression -- the only body desugaring a pure spec
    needs, applied without the statement-level rewrites (for, with, aug-assign) that cannot occur in a spec."""
    def visit_Compare(self, node):
        self.generic_visit(node)
        return _unchain_compare(node)


def parse_spec(s):
    """Parse a require/ensure expression to an AST node, desugaring a chained comparison `0 <= a <= 1` to
    `0 <= a and a <= 1` the way a function body is, so the spec language accepts it identically."""
    node = ast.parse(textwrap.dedent(s), mode="eval").body
    node = _SpecDesugar().visit(node)
    ast.fix_missing_locations(node)
    return node


class _Desugar(ast.NodeTransformer):
    def __init__(self, classes=None, suppress_names=None):
        self._tmp = 0
        self._classes = classes or {}                # module classes, for a context manager's __exit__ suppression
        self._suppress = suppress_names or set()     # names bound to contextlib.suppress (from contextlib import suppress)

    def _bump(self):
        self._tmp += 1
        return self._tmp

    def visit_AugAssign(self, node):
        self.generic_visit(node)
        tgt = node.target
        if isinstance(tgt, ast.Name):
            load = ast.Name(id=tgt.id, ctx=ast.Load())
            store = ast.Name(id=tgt.id, ctx=ast.Store())
        elif isinstance(tgt, ast.Subscript):                 # a[i] += e  ->  a[i] = a[i] + e
            load = ast.Subscript(value=tgt.value, slice=tgt.slice, ctx=ast.Load())
            store = ast.Subscript(value=tgt.value, slice=tgt.slice, ctx=ast.Store())
        elif isinstance(tgt, ast.Attribute):                 # o.f += e  ->  o.f = o.f + e
            load = ast.Attribute(value=tgt.value, attr=tgt.attr, ctx=ast.Load())
            store = ast.Attribute(value=tgt.value, attr=tgt.attr, ctx=ast.Store())
        else:
            return node
        return ast.Assign(targets=[store],
                          value=ast.BinOp(left=load, op=node.op, right=node.value))

    def visit_AnnAssign(self, node):
        self.generic_visit(node)
        if node.value is None:
            return None                                    # a bare annotation `x: T` binds nothing at runtime -> drop
        return ast.copy_location(                          # `x: T = v` is `x = v` (the annotation has no runtime effect)
            ast.Assign(targets=[node.target], value=node.value), node)

    def visit_Compare(self, node):
        self.generic_visit(node)
        return _unchain_compare(node)                      # a < b < c -> (a<b) and (b<c)

    def visit_For(self, node):
        self.generic_visit(node)
        unrolled = self._unroll_for(node)                    # for x in (constant iterable): ...
        if unrolled is not None:
            return unrolled
        # `for x in sorted/reversed/list/tuple/set/frozenset(E)` (no key=) visits E's elements: sorted/reversed/
        # list/tuple are the same multiset and count, set/frozenset a deduplicated subset -- so for trap freedom
        # (the loop is havoc'd over a symbolic-length container, order-independent) iterating E over-approximates
        # all of them. Rewrite and re-desugar so a `sorted(range(...))` still becomes the range loop.
        it = node.iter
        if (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and len(it.args) == 1 and not it.keywords
                and it.func.id in ("sorted", "reversed", "list", "tuple", "set", "frozenset")):
            node.iter = it.args[0]
            return self.visit_For(node)
        # `for i, x in enumerate(C[, start])` -> i = start; for x in C: <body>; i = i + 1. The counter tracks the
        # position; under the loop havoc i becomes an arbitrary int (so a body that self-indexes C[i] stays
        # UNKNOWN, sound), exact enough for the common enumerate that uses i arithmetically rather than to index.
        if (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "enumerate"
                and not it.keywords and 1 <= len(it.args) <= 2
                and isinstance(node.target, ast.Tuple) and len(node.target.elts) == 2
                and all(isinstance(t, ast.Name) for t in node.target.elts)):
            iname, xname = node.target.elts[0].id, node.target.elts[1].id
            start = it.args[1] if len(it.args) == 2 else ast.Constant(value=0)
            st = lambda nm: ast.Name(id=nm, ctx=ast.Store())
            incr = ast.Assign(targets=[st(iname)], value=ast.BinOp(
                left=ast.Name(id=iname, ctx=ast.Load()), op=ast.Add(), right=ast.Constant(value=1)))
            inner = ast.For(target=st(xname), iter=it.args[0], body=node.body + [incr], orelse=node.orelse)
            lowered = self.visit(inner)                       # the inner for-loop may itself lower to a list (range)
            tail = lowered if isinstance(lowered, list) else [lowered]
            return [ast.Assign(targets=[st(iname)], value=start)] + tail
        # `for x in A + B: body` -> for x in A: body; for x in B: body. Iterating a concatenation of two
        # sequences visits A's then B's elements -- same multiset, same count, same state flow -- so it is the
        # two loops; the split also lets each `for x in A` type A a sequence. Only the plain case (no else / break).
        if (isinstance(it, ast.BinOp) and isinstance(it.op, ast.Add) and not node.orelse
                and not any(isinstance(n, (ast.Break, ast.Continue)) for s in node.body for n in ast.walk(s))):
            import copy
            left = ast.For(target=node.target, iter=it.left, body=node.body, orelse=[])
            right = ast.For(target=copy.deepcopy(node.target), iter=it.right,
                            body=[copy.deepcopy(s) for s in node.body], orelse=[])
            out = []
            for sub in (self.visit(left), self.visit(right)):
                out += sub if isinstance(sub, list) else [sub]
            return out
        # for i in range(...) -> i = start; while i < stop: <body>; i = i + step (else preserved)
        if not (isinstance(node.target, ast.Name) and isinstance(node.iter, ast.Call)
                and isinstance(node.iter.func, ast.Name) and node.iter.func.id == "range"):
            return node
        a = node.iter.args
        if len(a) == 1:
            start, stop, step = ast.Constant(value=0), a[0], ast.Constant(value=1)
        elif len(a) == 2:
            start, stop, step = a[0], a[1], ast.Constant(value=1)
        elif len(a) == 3:
            start, stop, step = a
        else:
            return node
        sv = step.value if isinstance(step, ast.Constant) and isinstance(step.value, int) else (
            -step.operand.value if isinstance(step, ast.UnaryOp) and isinstance(step.op, ast.USub)
            and isinstance(step.operand, ast.Constant) and isinstance(step.operand.value, int) else None)
        if sv is None or sv == 0:                          # nonzero constant step (`-1` parses as a unary minus)
            return node
        i = node.target.id
        ctr = "__forc%d" % self._bump()                    # a fresh counter, independent of the loop variable: a
        #                                                    nested loop that reuses the name (for i ...: for i ...)
        #                                                    must not clobber this one, as Python's iterator does not
        init = ast.Assign(targets=[ast.Name(id=ctr, ctx=ast.Store())], value=start)
        bind = ast.Assign(targets=[ast.Name(id=i, ctx=ast.Store())],   # rebind the loop variable each iteration from
                          value=ast.Name(id=ctr, ctx=ast.Load()))      # the hidden counter, the way the protocol does
        incr = ast.Assign(targets=[ast.Name(id=ctr, ctx=ast.Store())],
                          value=ast.BinOp(left=ast.Name(id=ctr, ctx=ast.Load()), op=ast.Add(), right=step))
        # ascending range stops at the counter >= stop, descending at <= stop
        cmp = ast.Lt() if sv > 0 else ast.Gt()
        test = ast.Compare(left=ast.Name(id=ctr, ctx=ast.Load()), ops=[cmp], comparators=[stop])
        return [init, ast.While(test=test, body=[bind] + node.body + [incr], orelse=node.orelse)]

    def _unroll_for(self, node):
        """Unroll a for-loop over a constant iterable (a tuple/list literal, or enumerate/zip of
        them) into straight-line assignments + body copies, with the else clause appended (no
        break occurred). Returns None when the loop has a break/continue or is not constant."""
        if any(isinstance(n, (ast.Break, ast.Continue)) for n in node.body):
            return None
        rows = self._const_rows(node.iter)
        if rows is None:
            return None
        out = []
        for row in rows:
            out += self._bind_target(node.target, row)
            out += node.body
        return out + node.orelse

    def _const_rows(self, it):
        """The constant rows a for-iterable yields, each row a list of element exprs (one for a
        plain element, several for enumerate/zip), or None if not a constant iterable."""
        if isinstance(it, (ast.Tuple, ast.List)):
            if any(isinstance(el, ast.Starred) for el in it.elts):
                return None                                  # a star-unpacked literal is not constant rows; the normal
            return [[el] for el in it.elts]                  # for-loop path handles it as a sized container
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name):
            if it.func.id == "enumerate" and len(it.args) == 1:
                inner = self._const_rows(it.args[0])
                if inner is None or any(len(r) != 1 for r in inner):
                    return None
                return [[ast.Constant(value=i), r[0]] for i, r in enumerate(inner)]
            if it.func.id == "zip" and it.args:
                cols = [self._const_rows(a) for a in it.args]
                if any(c is None or any(len(r) != 1 for r in c) for c in cols):
                    return None
                n = min(len(c) for c in cols)
                return [[cols[j][i][0] for j in range(len(cols))] for i in range(n)]
        return None

    def visit_Match(self, node):
        self.generic_visit(node)
        # match subj: case p: body ...  ->  _m = subj; if test(p): binds+body elif ...
        try:
            tmp = f"_m{self._bump()}"
            ld = ast.Name(id=tmp, ctx=ast.Load())
            cases, default = [], None
            for case in node.cases:
                test, binds = self._match_pattern(case.pattern, ld)
                if case.guard is not None:
                    bm = {a.targets[0].id: a.value for a in binds
                          if isinstance(a, ast.Assign) and isinstance(a.targets[0], ast.Name)}
                    guard = _subst_names(case.guard, bm)     # captures aren't bound until the body runs
                    test = guard if test is None else ast.BoolOp(ast.And(), [test, guard])
                body = binds + case.body
                if test is None:                             # unguarded capture/wildcard: the default
                    default = body
                    break
                cases.append((test, body))
        except Unsupported:
            return node                                      # unsupported pattern: leave match unmodeled
        chain = default if default is not None else []
        for test, body in reversed(cases):
            chain = [ast.If(test=test, body=body, orelse=chain)]
        return [ast.Assign(targets=[ast.Name(id=tmp, ctx=ast.Store())], value=node.subject)] + chain

    def _match_pattern(self, pat, ld):
        """A (test, binds) pair for a case pattern over the subject `ld`: test is the match
        condition (None when the pattern always matches) and binds are capture assignments."""
        if isinstance(pat, ast.MatchValue):
            return ast.Compare(left=ld, ops=[ast.Eq()], comparators=[pat.value]), []
        if isinstance(pat, ast.MatchSingleton):
            return ast.Compare(left=ld, ops=[ast.Eq()], comparators=[ast.Constant(value=pat.value)]), []
        if isinstance(pat, ast.MatchAs):
            if pat.pattern is None:                          # `case name` (capture) or `case _` (wildcard)
                binds = [] if pat.name is None else [ast.Assign(
                    targets=[ast.Name(id=pat.name, ctx=ast.Store())], value=ld)]
                return None, binds
            test, binds = self._match_pattern(pat.pattern, ld)   # `case PAT as name`
            if pat.name is not None:
                binds = [ast.Assign(targets=[ast.Name(id=pat.name, ctx=ast.Store())], value=ld)] + binds
            return test, binds
        if isinstance(pat, ast.MatchOr):
            subs = [self._match_pattern(p, ld) for p in pat.patterns]
            if any(b for _t, b in subs):
                raise Unsupported("or-pattern with captures")
            if any(t is None for t, _b in subs):
                return None, []                              # one alternative always matches
            return ast.BoolOp(ast.Or(), [t for t, _b in subs]), []
        raise Unsupported(f"match pattern {type(pat).__name__}")

    def visit_With(self, node):
        self.generic_visit(node)
        # with A as a, B as b: body  ->  a = A; b = B; try: body finally: pass (cleanup on both paths).
        # __enter__ is modeled as the value itself (it returns self for the usual managers). A context manager
        # whose __exit__ provably returns a truthy constant suppresses the body's exceptions, modeled as
        # try: body except BaseException: pass; otherwise __exit__ is the finally and exceptions propagate.
        binds = []
        for item in node.items:
            if item.optional_vars is not None:
                if not isinstance(item.optional_vars, ast.Name):
                    return node                              # non-Name with-target stays unmodeled
                binds.append(ast.Assign(targets=[ast.Name(id=item.optional_vars.id, ctx=ast.Store())],
                                        value=item.context_expr))
        # contextlib.suppress(ExcTypes): the body's matching exceptions are swallowed, so model it as
        # try: body except (ExcTypes): pass -- a raise of a suppressed type does not escape (the finally model
        # below would wrongly let it propagate), while a raise outside the suppressed set still does.
        sup = [self._suppress_types(item.context_expr) for item in node.items]
        if sup and all(t is not None for t in sup):
            names = [n for ts in sup for n in ts]                # the union of every suppress(...)'s types
            htype = (ast.Name(id=names[0], ctx=ast.Load()) if len(names) == 1
                     else ast.Tuple(elts=[ast.Name(id=n, ctx=ast.Load()) for n in names], ctx=ast.Load()))
            handler = ast.ExceptHandler(type=htype, name=None, body=[ast.Pass()])
            return binds + [ast.Try(body=node.body, handlers=[handler], orelse=[], finalbody=[])]
        if all(self._cm_suppresses(item.context_expr) for item in node.items):
            catchall = ast.ExceptHandler(type=ast.Name(id="BaseException", ctx=ast.Load()), name=None,
                                         body=[ast.Pass()])
            return binds + [ast.Try(body=node.body, handlers=[catchall], orelse=[], finalbody=[])]
        return binds + [ast.Try(body=node.body, handlers=[], orelse=[], finalbody=[ast.Pass()])]

    def _suppress_types(self, expr):
        """The exception-type names a contextlib.suppress(...) manager swallows, or None if `expr` is not a
        recognized suppress -- contextlib.suppress(...), or a suppress(...) whose name is imported from
        contextlib. Conservative: a no-argument or non-Name-argument call declines (so the exception then
        propagates as before, never unsoundly swallowed)."""
        if not isinstance(expr, ast.Call):
            return None
        f = expr.func
        is_sup = ((isinstance(f, ast.Attribute) and f.attr == "suppress"
                   and isinstance(f.value, ast.Name) and f.value.id == "contextlib")
                  or (isinstance(f, ast.Name) and f.id in self._suppress))
        if not (is_sup and expr.args and all(isinstance(a, ast.Name) for a in expr.args)):
            return None
        return [a.id for a in expr.args]

    def _cm_suppresses(self, expr):
        """Whether the context manager `expr` (a module class C, used as C() or C) has an __exit__ that
        provably suppresses every exception: its body is exactly `return <truthy constant>`, so it returns
        truthy on every path. Conservative -- False otherwise, so the exception then propagates as before."""
        if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name):
            cls = self._classes.get(expr.func.id)
        elif isinstance(expr, ast.Name):
            cls = self._classes.get(expr.id)
        else:
            cls = None
        if cls is None:
            return False
        ex = next((n for n in cls.body if isinstance(n, ast.FunctionDef) and n.name == "__exit__"), None)
        return (ex is not None and len(ex.body) == 1 and isinstance(ex.body[0], ast.Return)
                and isinstance(ex.body[0].value, ast.Constant) and bool(ex.body[0].value.value))

    def _bind_target(self, target, row):
        """Assignments binding a for-target (a Name, or a tuple of Names) to one constant row."""
        if isinstance(target, ast.Name) and len(row) == 1:
            return [ast.Assign(targets=[ast.Name(id=target.id, ctx=ast.Store())], value=row[0])]
        if isinstance(target, (ast.Tuple, ast.List)) and len(target.elts) == len(row) \
                and all(isinstance(t, ast.Name) for t in target.elts):
            return [ast.Assign(targets=[ast.Name(id=t.id, ctx=ast.Store())], value=v)
                    for t, v in zip(target.elts, row)]
        raise Unsupported("for-target does not match the iterable rows")

    def visit_Assign(self, node):
        self.generic_visit(node)
        # parallel/tuple assignment: (x1,...,xk) = (e1,...,ek). Python evaluates the whole
        # right side before binding, so route through temporaries (this makes a, b = b, a work).
        if (len(node.targets) == 1 and isinstance(node.targets[0], (ast.Tuple, ast.List))
                and isinstance(node.value, (ast.Tuple, ast.List))
                and len(node.targets[0].elts) == len(node.value.elts)
                and all(isinstance(t, ast.Name) for t in node.targets[0].elts)):
            names = [t.id for t in node.targets[0].elts]
            temps = [f"_pa{self._bump()}" for _ in names]
            out = [ast.Assign(targets=[ast.Name(id=tp, ctx=ast.Store())], value=val)
                   for tp, val in zip(temps, node.value.elts)]
            out += [ast.Assign(targets=[ast.Name(id=nm, ctx=ast.Store())],
                               value=ast.Name(id=tp, ctx=ast.Load()))
                    for nm, tp in zip(names, temps)]
            return out
        # accumulator comprehension: t = sum([elt for v in range(...)]) -> a counting loop.
        if (len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name)
                and node.value.func.id == "sum" and len(node.value.args) == 1
                and isinstance(node.value.args[0], (ast.ListComp, ast.GeneratorExp))):
            lowered = self._lower_sum(node.targets[0].id, node.value.args[0])
            if lowered is not None:
                return lowered
        # comprehensions over a constant iterable: r = [e for x in (..) if c]  ->  build loop
        if (len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp))):
            lowered = self._lower_comp(node.targets[0].id, node.value)
            if lowered is not None:
                return lowered
        return node

    def _lower_comp(self, name, comp):
        """Lower a list/set/dict comprehension or generator expression over a constant iterable to
        statements that build the collection element by element, with the filter as a guarded
        append/add/store. Returns None unless the iterable is constant and has a single clause."""
        if len(comp.generators) != 1:
            return None
        gen = comp.generators[0]
        if getattr(gen, "is_async", 0):
            return None
        rows = self._const_rows(gen.iter)
        if rows is None:
            return None
        st = lambda: ast.Name(id=name, ctx=ast.Store())
        ld = lambda: ast.Name(id=name, ctx=ast.Load())
        meth = lambda m, *a: ast.Expr(ast.Call(ast.Attribute(value=ld(), attr=m, ctx=ast.Load()), list(a), []))
        if isinstance(comp, (ast.ListComp, ast.GeneratorExp)):
            init, one = ast.Assign([st()], ast.List(elts=[], ctx=ast.Load())), lambda: meth("append", comp.elt)
        elif isinstance(comp, ast.SetComp):
            init, one = ast.Assign([st()], ast.Call(ast.Name("set", ast.Load()), [], [])), lambda: meth("add", comp.elt)
        else:                                                # DictComp
            init = ast.Assign([st()], ast.Dict(keys=[], values=[]))
            one = lambda: ast.Assign([ast.Subscript(value=ld(), slice=comp.key, ctx=ast.Store())], comp.value)
        try:
            out = [init]
            for row in rows:
                out += self._bind_target(gen.target, row)
                body = [one()]
                if gen.ifs:
                    cond = gen.ifs[0] if len(gen.ifs) == 1 else ast.BoolOp(ast.And(), gen.ifs)
                    body = [ast.If(test=cond, body=body, orelse=[])]
                out += body
        except Unsupported:
            return None
        return out

    def _lower_sum(self, tname, comp):
        if len(comp.generators) != 1:
            return None
        gen = comp.generators[0]
        if gen.ifs or getattr(gen, "is_async", 0) or not isinstance(gen.target, ast.Name):
            return None
        it = gen.iter
        if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range"):
            return None
        a = it.args
        if len(a) == 1:
            start, stop, step = ast.Constant(value=0), a[0], ast.Constant(value=1)
        elif len(a) == 2:
            start, stop, step = a[0], a[1], ast.Constant(value=1)
        elif len(a) == 3:
            start, stop, step = a
        else:
            return None
        if not (isinstance(step, ast.Constant) and isinstance(step.value, int) and step.value > 0):
            return None
        v, elt = gen.target.id, comp.elt
        st = lambda nm: ast.Name(id=nm, ctx=ast.Store())
        ld = lambda nm: ast.Name(id=nm, ctx=ast.Load())
        acc = ast.Assign(targets=[st(tname)], value=ast.BinOp(left=ld(tname), op=ast.Add(), right=elt))
        incr = ast.Assign(targets=[st(v)], value=ast.BinOp(left=ld(v), op=ast.Add(), right=step))
        test = ast.Compare(left=ld(v), ops=[ast.Lt()], comparators=[stop])
        return [ast.Assign(targets=[st(tname)], value=ast.Constant(value=0)),
                ast.Assign(targets=[st(v)], value=start),
                ast.While(test=test, body=[acc, incr], orelse=[])]


def _subst_names(node, mapping):
    """Replace each loaded Name in `mapping` with its expression (used to inline match-case
    captures into a guard, which is evaluated before the capture bindings run)."""
    class _S(ast.NodeTransformer):
        def visit_Name(self, n):
            return mapping[n.id] if (isinstance(n.ctx, ast.Load) and n.id in mapping) else n
    return _S().visit(node)


def _clone_ast(node):
    """A fast deep copy of an AST node -- ~4x quicker than copy.deepcopy (no __reduce__ / memo machinery):
    fresh node objects and lists, with immutable leaf values (a Constant's value, identifier strings) shared.
    This is the independent tree _parse hands out, so a caller's mutation never reaches the memoized template."""
    if isinstance(node, ast.AST):
        new = node.__class__()
        for field in node._fields:
            setattr(new, field, _clone_ast(getattr(node, field, None)))
        for attr in node._attributes:
            if hasattr(node, attr):
                setattr(new, attr, getattr(node, attr))
        return new
    if type(node) is list:
        return [_clone_ast(x) for x in node]
    return node


@lru_cache(maxsize=256)
def _parse_template(src: str) -> ast.Module:
    """The desugared parse of `src`, memoized: the engine re-parses the same source dozens of times per
    function (check, symexec, the definite-assignment / self-recursion / use-before-def predicates). The
    template is never handed out directly -- _parse returns a fast deep clone -- so a caller that mutates its
    tree (symexec's async strip, a contract-decorator strip) cannot corrupt the cache or another caller's tree."""
    parsed = ast.parse(textwrap.dedent(src))
    classes = {n.name: n for n in parsed.body if isinstance(n, ast.ClassDef)}
    suppress_names = {a.asname or a.name for n in ast.walk(parsed)        # `from contextlib import suppress`
                      if isinstance(n, ast.ImportFrom) and n.module == "contextlib"
                      for a in n.names if a.name == "suppress"}
    tree = _Desugar(classes, suppress_names).visit(parsed)
    return ast.fix_missing_locations(tree)


def _parse(src: str) -> ast.Module:
    return _clone_ast(_parse_template(src))


def _fndef(src: str):
    """The first function definition in a module source, skipping leading imports and global
    assignments, so an engine never mistakes a leading `import` for the function it verifies."""
    for n in _parse(src).body:
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return n
    raise Unsupported("no function definition")


class _StripAsync(ast.NodeTransformer):
    """Desugar an async function to the synchronous body that runs when its coroutine is driven: an
    `async def` becomes a `def`, `await e` becomes `e` (the value the await yields), and `async for` /
    `async with` become their synchronous forms. Sound for reasoning about the value a coroutine produces
    when awaited and the traps it reaches; the coroutine object a bare call returns is never the subject."""
    def visit_AsyncFunctionDef(self, node):
        self.generic_visit(node)
        f = ast.FunctionDef(name=node.name, args=node.args, body=node.body,
                            decorator_list=node.decorator_list, returns=node.returns,
                            type_comment=getattr(node, "type_comment", None))
        return ast.copy_location(f, node)

    def visit_Await(self, node):
        self.generic_visit(node)
        return node.value                                    # await e -> e (the awaited result)

    def visit_AsyncFor(self, node):
        self.generic_visit(node)
        return ast.copy_location(ast.For(target=node.target, iter=node.iter, body=node.body,
                                         orelse=node.orelse), node)

    def visit_AsyncWith(self, node):
        self.generic_visit(node)
        return ast.copy_location(ast.With(items=node.items, body=node.body), node)


class _StripYields(ast.NodeTransformer):
    """Replace `yield e` / `yield from e` with the expression `e` (and a bare `yield` with a constant), so a
    generator body becomes a plain function body whose statements trap-check exactly as iteration would: the
    division, index, or key a yielded expression evaluates surfaces as the iteration trap it is. Sound for
    modeling a branching generator as the lazily-yielded sequence its consumer observes."""
    def visit_Yield(self, node):
        return node.value if node.value is not None else ast.Constant(value=0)

    def visit_YieldFrom(self, node):
        return node.value


def _strip_yields(fn):
    """A copy of generator function `fn` with its yields stripped to expression statements (see _StripYields),
    so the value engine can run its body and collect the traps that arise during iteration."""
    import copy
    new = ast.FunctionDef(name=fn.name, args=fn.args,
                          body=[_StripYields().visit(copy.deepcopy(s)) for s in fn.body],
                          decorator_list=[], returns=None)
    return ast.fix_missing_locations(ast.copy_location(new, fn))


def _strip_async(src):
    """The source with every async function desugared to the synchronous body that runs when its coroutine
    is driven (see _StripAsync), so the engines reason about the coroutine's awaited result and its traps.
    Returns the source unchanged when it has no async construct, or on a parse failure."""
    try:
        tree = ast.parse(textwrap.dedent(src))
    except SyntaxError:
        return src
    if not any(isinstance(n, (ast.AsyncFunctionDef, ast.Await, ast.AsyncFor, ast.AsyncWith))
               for n in ast.walk(tree)):
        return src
    return ast.unparse(ast.fix_missing_locations(_StripAsync().visit(tree)))


PROVED, REFUTED, UNKNOWN = "PROVED", "REFUTED", "UNKNOWN"


@dataclass
class Verdict:
    status: str
    prop: str
    target: str
    technique: str
    counterexample: Optional[str] = None
    reason: str = ""
    counterexample_inputs: Optional[Dict[str, int]] = None
    trace: Optional[str] = None                          # execution trace of a counterexample (filled by explain)
    certificate: Optional[str] = None                    # reproducibility record attached to a corroborated PROVED


def proof_certificate(corroborator=None) -> str:
    """The reproducibility certificate for a PROVED: the corroborating procedure and the deterministic,
    rlimit-bounded configuration. `corroborator` names the second procedure that backed it (z3 + cvc5, a
    checked SOS certificate, real-relaxation nlsat); None falls back to the cvc5 availability label."""
    cfg = f"deterministic (rlimit={SOLVE_RLIMIT}, seed=0)"
    if corroborator and corroborator != "z3 only":
        return f"corroborated by {corroborator}; {cfg}"
    if corroborator == "z3 only" or not cvc5_available():
        return f"z3 only (single-solver, lower trust); {cfg}"
    return f"corroborated by z3 + cvc5; {cfg}"


def find_extracted(stem):
    """Path to the built proofs/ binary `stem` (or stem.exe), or None. Searches $TOUCHSTONE_<STEM>,
    then proofs/ beside the package, then proofs/ under the working directory."""
    env = os.environ.get("TOUCHSTONE_" + stem.upper())
    if env and os.path.isfile(env) and os.access(env, os.X_OK):
        return env
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    for base in (root, os.getcwd()):
        for name in (stem, stem + ".exe"):
            cand = os.path.join(base, "proofs", name)
            if os.path.isfile(cand) and os.access(cand, os.X_OK):
                return cand
    return None


def encoding_executable():
    """Path to the Coq-extracted division encoding built by proofs/build_encoding.sh, or None."""
    return find_extracted("encoding")


def extracted_encoding_batch(pairs, exe=None):
    """Run the extracted encoding on (a, b) pairs in one invocation; return the (floordiv, mod)
    results aligned with pairs, or None if the binary is not built."""
    exe = exe or encoding_executable()
    if exe is None or not pairs:
        return [] if exe is not None else None
    inp = "".join(f"{a} {b}\n" for a, b in pairs)
    out = subprocess.run([exe], input=inp, capture_output=True, text=True, timeout=300)
    return [tuple(int(t) for t in r.split()) for r in out.stdout.strip("\n").split("\n")]


class Unsupported(Exception):
    """Raised when the symbolic front end meets a construct outside the modeled
    subset. Callers convert it to an UNKNOWN verdict carrying the reason."""


class NonConvergence(RuntimeError):
    """A widening sequence did not reach a fixpoint within the iteration cap. The
    transfer functions are monotone over a finite-height (after widening) lattice,
    so reaching the cap is a lattice bug, not a normal outcome: it is raised, not
    silently returned as a non-fixpoint."""


def py_floordiv(a, b):
    # Z3 integer div/mod are Euclidean (0 <= a%b < |b|); Python uses floor division. They
    # agree for b > 0; for b < 0 with a nonzero remainder Python's quotient is one less.
    # Division by zero is a trap, emitted as a nonzero obligation at each use site.
    # touchstone_encoding.v proves this equals Python's // for every nonzero divisor.
    qe = a / b
    re = a % b
    return z3.If(z3.And(re != 0, b < 0), qe - 1, qe)


def py_mod(a, b):
    return a - py_floordiv(a, b) * b


_BINOPS = {
    ast.Add: lambda a, b: a + b,
    ast.Sub: lambda a, b: a - b,
    ast.Mult: lambda a, b: a * b,
    ast.FloorDiv: py_floordiv,
    ast.Mod: py_mod,
}


_CMP = {
    ast.Lt: lambda a, b: a < b, ast.LtE: lambda a, b: a <= b,
    ast.Gt: lambda a, b: a > b, ast.GtE: lambda a, b: a >= b,
    ast.Eq: lambda a, b: a == b, ast.NotEq: lambda a, b: a != b,
}

# operator-module functions that mirror a Python operator: each is modeled by re-evaluating the corresponding
# BinOp / UnaryOp / Compare (operator.add(a, b) == a + b), reusing the existing operator semantics and their traps.
_OPERATOR_BINOP = {"add": ast.Add, "sub": ast.Sub, "mul": ast.Mult, "truediv": ast.Div, "floordiv": ast.FloorDiv,
                   "mod": ast.Mod, "pow": ast.Pow, "lshift": ast.LShift, "rshift": ast.RShift, "and_": ast.BitAnd,
                   "or_": ast.BitOr, "xor": ast.BitXor, "matmul": ast.MatMult}
_OPERATOR_UNARY = {"neg": ast.USub, "pos": ast.UAdd, "invert": ast.Invert, "inv": ast.Invert, "not_": ast.Not}
_OPERATOR_CMP = {"lt": ast.Lt, "le": ast.LtE, "eq": ast.Eq, "ne": ast.NotEq, "gt": ast.Gt, "ge": ast.GtE,
                 "is_": ast.Is, "is_not": ast.IsNot}


_F64 = z3.Float64()
import math as _math
import struct as _struct
import string as _pystr
# math module float constants, exact as IEEE-754 doubles: math.pi / math.e / math.tau / math.inf / math.nan,
# and the same bare names under `from math import pi`. Reading one never traps, so arithmetic over it is modeled.
_MATH_CONSTS = {"pi": z3.FPVal(_math.pi, _F64), "e": z3.FPVal(_math.e, _F64), "tau": z3.FPVal(_math.tau, _F64),
                "inf": z3.fpPlusInfinity(_F64), "nan": z3.fpNaN(_F64)}
# string module constants are fixed literals, so string.digits[i] bounds-checks against length 10, etc.
_STRING_CONSTS = {n: getattr(_pystr, n) for n in ("ascii_lowercase", "ascii_uppercase", "ascii_letters", "digits",
                  "hexdigits", "octdigits", "punctuation", "whitespace", "printable")}
_RM = z3.RNE()


def _is_fp(x):
    return z3.is_fp(x)


def _to_fp(x):
    """Promote an int-, bool-, or exact-rational-valued term to Float64 (Python int / bool / Fraction
    -> float). A Fraction is rounded to the nearest double, as Python does when a Fraction meets a float."""
    if isinstance(x, (_Opaque, _Closure)):
        if BEST_EFFORT and type(x) is _Opaque:               # best-effort: an opaque result is assumed to be a float
            _best_effort_assume()
            return z3.FreshConst(_F64, "be_fp")
        raise Unsupported("arithmetic on an unmodeled value")
    if z3.is_fp(x):
        return x
    if z3.is_real(x):
        return z3.fpToFP(_RM, x, _F64)                       # an exact rational to the nearest double
    if z3.is_bool(x):
        x = z3.If(x, z3.IntVal(1), z3.IntVal(0))
    return z3.fpToFP(_RM, z3.ToReal(x), _F64)


def _is_str(x):
    return z3.is_string(x) or (z3.is_seq(x) and x.sort() == z3.StringSort())


def _is_real(x):
    return z3.is_real(x)


def _to_real(x):
    """Coerce an int- or bool-valued term to Real (exact); a Real is returned unchanged."""
    if isinstance(x, (_Opaque, _Closure)):
        if BEST_EFFORT and type(x) is _Opaque:               # best-effort: an opaque result is assumed to be a rational
            _best_effort_assume()
            return z3.ToReal(z3.FreshInt("be_real"))
        raise Unsupported("arithmetic on an unmodeled value")
    if z3.is_real(x):
        return x
    if z3.is_bool(x):
        x = z3.If(x, z3.IntVal(1), z3.IntVal(0))
    return z3.ToReal(x)


class _Complex:
    """A complex value as a pair of Float64 components; Python complex is double-based, so
    its arithmetic rounds exactly as the float model does."""
    __slots__ = ("re", "im")
    def __init__(self, re, im): self.re, self.im = re, im


class _Lambda:
    """A lambda (or, later, a function) as a first-class value: its parameter names, body
    expression, and the environment captured at definition (a closure)."""
    __slots__ = ("params", "body", "env")
    def __init__(self, params, body, env): self.params, self.body, self.env = params, body, env


class _FuncRef:
    """A reference to a named repo function used as a first-class value (passed as a callback,
    returned, or stored). Calling it inlines the function specialized to its arguments."""
    __slots__ = ("name",)
    def __init__(self, name): self.name = name


class _Closure:
    """A nested function with a statement body as an opaque first-class value: defining, returning, or
    storing it raises no trap, and calling it is not modeled (it is neither a _Lambda nor a _FuncRef, so a
    call falls through to the unmodeled-call path). Its body is checked separately when needed."""
    __slots__ = ("name",)
    def __init__(self, name): self.name = name


class _Opaque:
    """A value the engine holds but cannot reason about, e.g. a free or imported name. Returning, storing, or
    passing it raises no trap, but any operation on it (arithmetic, subscript, call, truth test, type test) is
    unmodeled and surfaces as UNKNOWN. Reading such a name raises at most NameError, which is not a modeled trap."""
    __slots__ = ("name",)
    def __init__(self, name): self.name = name


class _FieldVal(_Opaque):
    """An attribute of an opaque object parameter (o.x). Opaque for len / method / subscript / truth (trap free,
    never refuted), but a stable int in arithmetic and comparison (numeric duck-typing); the name is the path."""
    __slots__ = ()


class _NoneVal(_Opaque):
    """The literal None. Stored or passed it raises nothing, and `is` / `is not` test it exactly, but arithmetic
    on it raises TypeError (None + x), a reachable trap. Subclassing _Opaque keeps every other operation opaque;
    only the operations that genuinely raise on None become traps."""
    __slots__ = ()
    def __init__(self): super().__init__("None")


class _ListLit(tuple):
    """A list literal value -- a tuple of its element terms, so every existing tuple handling (indexing, unpacking,
    concatenation, sum, len) applies unchanged, but distinguished from a genuine tuple literal so that in-place item
    assignment a[i] = v is a bounds-checked mutation rather than a TypeError. (A tuple literal stays a plain tuple,
    whose item assignment is the TypeError it is in CPython.)"""
    __slots__ = ()


class _SafeContainer(_Opaque):
    """A parameter inferred or annotated as a sequence: iteration and len on it raise no trap and its
    elements are arbitrary integers. An integer index c[i] is bounds-checked against c's symbolic length
    (IndexError when out of [-len, len)); the oracle samples an indexed parameter as a real list so that
    out-of-range trap is witnessable, and an iteration- or method-only one as a benign stand-in. `immutable`
    marks a tuple, whose item assignment c[i] = v always raises (TypeError)."""
    __slots__ = ("immutable", "length", "unindexable", "byteslike", "elem", "unsized", "tuple_arity")
    def __init__(self, name, immutable=False, length=None, unindexable=False, byteslike=False, elem=None,
                 unsized=False, tuple_arity=None):
        super().__init__(name)
        self.immutable = immutable
        self.length = length        # an explicit, provably-nonnegative length term (a range); else a fresh
        #                             symbolic length keyed by name (an opaque list/tuple parameter)
        self.unindexable = unindexable   # a set / frozenset: sized and iterable, but s[i] raises TypeError
        self.byteslike = byteslike       # a bytes / bytearray: an element is an int in [0, 255]
        self.unsized = unsized      # a lazy iterator (zip / itertools.chain / ...): `length` is the count it yields
        #                             (list(it) / sorted(it) / a for-loop size correctly), but len(it) / it[i] TypeError
        self.elem = elem            # a _SafeContainer prototype when elements are themselves sequences (a
        #                             list[list[...]] / list[tuple[...]] parameter); an element c[i] is then a
        #                             bounds-checked inner sequence with a per-index symbolic length. None = scalar.
        self.tuple_arity = tuple_arity   # N when each element is a fixed N-tuple of scalars (zip / enumerate /
        #                             dict.items): an element is a Python N-tuple, so c[i][0..N-1] decide, c[i] + 1
        #                             is a TypeError (abstains, never a false PROVED), and a, b = c[i] unpacks.


class _SetExpr(_SafeContainer):
    """A set operation (union | intersection & difference - symmetric ^) of two set-like operands. Membership is
    the operands' combination (x in a|b iff x in a or x in b, etc.); the length carries the size relation."""
    __slots__ = ("op", "left", "right")
    def __init__(self, op, left, right, length=None):
        super().__init__("setexpr", unindexable=True, length=length)   # name unused: membership recurses, length explicit
        self.op, self.left, self.right = op, left, right


class _DictParam(_Opaque):
    """A parameter annotated `dict`: a read d[k] traps (KeyError) unless k is provably a key, tracked by a
    stable membership predicate so a `k in d` guard or a `for k in d` iteration makes d[k] safe. A store
    d[k] = v never traps (a dict accepts any key). The oracle samples it as a real dict. `valproto` is a
    prototype of the annotated value type (dict[K, V]); for a read-only dict, a read d[k] is modeled as a fresh
    V-typed value (memoized per key) so d[k][i] / d[k].append / len(d[k]) decide rather than staying opaque."""
    __slots__ = ("valproto",)
    def __init__(self, name, valproto=None):
        super().__init__(name)
        self.valproto = valproto


class _DictLit(_Opaque):
    """A dict literal built locally: a key assignment d[k] = v never traps (a dict accepts any key), so
    the common build-a-result pattern is trap free. Reading d[k] may KeyError, so it is left UNKNOWN.
    Used for a dict the value engine cannot track exactly (a {**other} unpacking, or a dict that escapes)."""
    __slots__ = ()


class _DefaultDict(_Opaque):
    """A collections.defaultdict / Counter: a dict whose missing-key read returns a default (the factory's
    value, or 0 for Counter) rather than raising, so d[k] never traps -- the defining property of these
    collections. A store never traps; len / membership / iteration are total. Built at the construction site;
    the value a read yields is opaque (value-independent)."""
    __slots__ = ()


class _NdArray(_Opaque):
    """A numpy ndarray (or torch tensor) modeled by its shape -- a tuple of provably-nonnegative dimension
    terms -- with opaque, value-independent elements. len() is shape[0] (a 0-d array raises TypeError); a.shape
    is the dimension tuple, a.ndim / a.size derived; an integer or tuple index bounds-checks each axis and
    yields the lower-rank subarray (a scalar at full depth); reshape adjusts the shape with a total-size-mismatch
    trap; element-wise arithmetic broadcasts (a non-broadcastable pair is a ValueError); a min / max reduction
    of a zero-size array is a ValueError; a negative constructed dimension is a ValueError. Constructed only for
    an N-d (tuple) shape or a nested-list array; a 1-D scalar-shape array stays a _SafeContainer."""
    __slots__ = ("shape",)
    def __init__(self, shape):
        super().__init__("ndarray")
        self.shape = tuple(shape)


class _Column(_NdArray):
    """A pandas / pyarrow Series: a 1-D sized column with opaque cells. It is an ndarray for length, the
    positional .iloc index, .values, and the empty-reduction trap, but a DIRECT subscript s[i] is LABEL-based
    (a KeyError when the label is absent, even for an in-range integer on a non-default index), so it is left
    UNKNOWN -- never claimed in bounds -- while .iloc[i] is the positional access."""
    __slots__ = ()


class _MapVal(_Opaque):
    """A dict value with its entries tracked: parallel key/value term lists in store order, resolved
    newest-first (last write wins). A read d[k] returns the value of the most recent stored key provably
    equal to k, with a KeyError trap when k matches no key -- exactly the heap engine's dict semantics,
    carried in the value engine so prove / check decide d = {}; d[k] = v; d[k]. Built only for a dict
    used solely as name[...] (see _tracked_dict_names); a dict that escapes is a _DictLit instead."""
    __slots__ = ("keys", "vals")
    def __init__(self, keys=None, vals=None):
        super().__init__("dict")
        self.keys = list(keys) if keys else []
        self.vals = list(vals) if vals else []
    def store(self, k, v):
        return _MapVal(self.keys + [k], self.vals + [v])


class _StrSeq(_Opaque):
    """A sequence of strings (str.split / rsplit / splitlines, or map(str/repr, ...)). `length` is its nonnegative
    length: >= 1 for split/rsplit with a separator, unconstrained for split()/splitlines. An index returns a fresh
    string bounds-checked against `length`. `unsized` marks a lazy iterator: join(it) is a string, but len(it) and
    it[i] are TypeErrors."""
    __slots__ = ("length", "unsized")
    def __init__(self, name, length=None, unsized=False):
        super().__init__(name)
        self.length = length
        self.unsized = unsized


def _cx(v):
    return v if isinstance(v, _Complex) else _Complex(_to_fp(v), z3.FPVal(0.0, _F64))


def _cx_binop(op, a, b):
    a, b = _cx(a), _cx(b)
    if op is ast.Add:
        return _Complex(z3.fpAdd(_RM, a.re, b.re), z3.fpAdd(_RM, a.im, b.im))
    if op is ast.Sub:
        return _Complex(z3.fpSub(_RM, a.re, b.re), z3.fpSub(_RM, a.im, b.im))
    if op is ast.Mult:
        return _Complex(z3.fpSub(_RM, z3.fpMul(_RM, a.re, b.re), z3.fpMul(_RM, a.im, b.im)),
                        z3.fpAdd(_RM, z3.fpMul(_RM, a.re, b.im), z3.fpMul(_RM, a.im, b.re)))
    raise Unsupported(f"complex operator {op.__name__}")


def _fp_arith(op, l, r):
    """IEEE-754 round-to-nearest arithmetic for a binop with a float operand; the other
    operand is promoted from int/bool. Floor division and modulo go through _fp_divmod."""
    l, r = _to_fp(l), _to_fp(r)
    if op is ast.Add: return z3.fpAdd(_RM, l, r)
    if op is ast.Sub: return z3.fpSub(_RM, l, r)
    if op is ast.Mult: return z3.fpMul(_RM, l, r)
    if op is ast.Div: return z3.fpDiv(_RM, l, r)
    if op is ast.FloorDiv: return _fp_divmod(l, r)[0]
    if op is ast.Mod: return _fp_divmod(l, r)[1]
    raise Unsupported(f"float operator {op.__name__}")


def _fp_fmod(a, b):
    """C fmod(a, b): the exact remainder with the truncated quotient, sign of `a`, |result| < |b|.
    Z3's fpRem is the round-to-nearest remainder (range [-|b|/2, |b|/2]); it differs from fmod by 0 or
    one b, so a sign correction recovers fmod, and the corrected sum is exact (it is representable)."""
    r = z3.fpRem(a, b)
    absb = z3.fpAbs(b)
    corr = z3.If(z3.fpIsNegative(a), z3.fpNeg(absb), absb)               # copysign(|b|, a)
    need = z3.And(z3.Not(z3.fpIsZero(r)), z3.Xor(z3.fpIsNegative(r), z3.fpIsNegative(a)))
    return z3.If(need, z3.fpAdd(_RM, r, corr), r)


def _fp_divmod(a, b):
    """Python float a // b and a % b, transcribing CPython's float_divmod (the modulo takes the
    divisor's sign; the quotient is floored with CPython's half-correction). Exact, hence sound both
    ways; validated bit-for-bit in float_divmod_audit. Returns (floordiv, mod); a zero divisor traps."""
    one, half = z3.FPVal(1.0, _F64), z3.FPVal(0.5, _F64)
    mod0 = _fp_fmod(a, b)
    div0 = z3.fpDiv(_RM, z3.fpSub(_RM, a, mod0), b)
    adj = z3.And(z3.Not(z3.fpIsZero(mod0)), z3.Xor(z3.fpIsNegative(b), z3.fpIsNegative(mod0)))
    mod1 = z3.If(adj, z3.fpAdd(_RM, mod0, b), mod0)                      # bring the remainder to b's sign
    div1 = z3.If(adj, z3.fpSub(_RM, div0, one), div0)
    zero_b = z3.If(z3.fpIsNegative(b), z3.FPVal(-0.0, _F64), z3.FPVal(0.0, _F64))   # copysign(0, b)
    mod = z3.If(z3.fpIsZero(mod0), zero_b, mod1)
    fl = z3.fpRoundToIntegral(z3.RTN(), div1)                           # floor(div1)
    floordiv_nz = z3.If(z3.fpGT(z3.fpSub(_RM, div1, fl), half), z3.fpAdd(_RM, fl, one), fl)
    zero_ab = z3.If(z3.fpIsNegative(z3.fpDiv(_RM, a, b)), z3.FPVal(-0.0, _F64), z3.FPVal(0.0, _F64))
    floordiv = z3.If(z3.fpIsZero(div1), zero_ab, floordiv_nz)
    return floordiv, mod


def _sqrt_model(a, ctx):
    """math.sqrt as the IEEE-754 square root (correctly rounded, what CPython computes), with a
    negative argument a domain error: math.sqrt(x) raises ValueError for x < 0, so it is a trap,
    while -0.0, +0.0, +Inf, and NaN pass through. The argument is promoted from int/bool."""
    a = _to_fp(a)
    if ctx.traps is not None:
        ctx.traps.append(z3.And(ctx.pc, z3.fpLT(a, z3.FPVal(0.0, _F64))))
    return z3.fpSqrt(_RM, a)


_SIN = z3.Function("py_sin", _F64, _F64)
_COS = z3.Function("py_cos", _F64, _F64)
_EXP = z3.Function("py_exp", _F64, _F64)
_LOG = z3.Function("py_log", _F64, _F64)
_TRANSCENDENTAL = {"sin", "cos", "exp", "log"}
# Builtin methods that can raise a modeled trap on valid inputs; an unmodeled call to one stays UNKNOWN.
# Every other method is assumed trap free (the modular notion). differential_method_audit guards the set.
_TRAPPING_METHODS = frozenset({
    "pop", "popleft", "remove", "index", "rindex", "popitem", "sort",   # list / deque / dict / set value traps
    "encode", "decode", "format", "format_map", "translate", "join",  # str / bytes encode / format traps
    "split", "rsplit", "splitlines", "maketrans", "fromhex", "to_bytes", "from_bytes",
})
# exception names the verifier models as traps; raising one is a reachable trap.
_MODELED_TRAP_NAMES = frozenset({"ValueError", "TypeError", "KeyError", "IndexError",
                                 "ZeroDivisionError", "AssertionError"})
# builtins that raise no modeled trap on any argument, so an unmodeled call to one is trap free.
_SAFE_BUILTINS_TF = frozenset({"getattr", "setattr", "delattr", "hasattr", "type", "isinstance",
                               "issubclass", "callable", "print", "repr", "id", "object"})

# Pure stdlib functions that raise no MODELED trap (ValueError / TypeError / KeyError / IndexError /
# ZeroDivisionError / AssertionError) on a well-typed argument -- only an unmodeled exception (OSError,
# re.error) or a wrong-TYPE TypeError, which the engine's duck-typed assumption already excludes, exactly as
# a method call on an opaque local value is assumed trap free. A parser / converter that ValueErrors on a
# valid-typed argument (int, float, json.loads, ast.literal_eval, strptime) is deliberately excluded -- it
# stays UNKNOWN. Each maps to the sort its result inhabits, so a downstream operation on it composes.
# stdlib_trapfree_audit validates the no-modeled-trap claim against CPython.
def _reg_tf(d, ret, names):
    for nm in names.split():
        d[nm] = ret


_STDLIB_TF: Dict[str, str] = {}
_reg_tf(_STDLIB_TF, "int", "os.getpid os.getppid os.getuid os.getgid os.geteuid os.getegid os.getpgrp "
        "os.cpu_count os.path.getsize os.path.getmtime os.path.getctime sys.getsizeof sys.getrecursionlimit "
        "sys.getrefcount sys.getallocatedblocks time.time_ns time.monotonic_ns time.perf_counter_ns "
        "time.process_time_ns bisect.bisect bisect.bisect_left bisect.bisect_right")
_reg_tf(_STDLIB_TF, "float", "time.time time.monotonic time.perf_counter time.process_time time.thread_time")
_reg_tf(_STDLIB_TF, "str", "os.getcwd os.getcwdb os.getlogin os.strerror os.fspath os.path.join os.path.dirname "
        "os.path.basename os.path.normpath os.path.normcase os.path.abspath os.path.realpath os.path.expanduser "
        "os.path.expandvars os.path.commonprefix sys.getdefaultencoding sys.getfilesystemencoding "
        "sys.intern time.ctime time.asctime time.strftime re.escape textwrap.dedent textwrap.fill textwrap.indent "
        "textwrap.shorten string.capwords platform.system platform.machine platform.release platform.version "
        "platform.platform platform.node platform.processor platform.python_version socket.gethostname "
        "shutil.which uuid.uuid4 uuid.uuid1 base64.b64encode")
_reg_tf(_STDLIB_TF, "bool", "os.path.exists os.path.lexists os.path.isfile os.path.isdir os.path.islink "
        "os.path.isabs os.path.ismount sys.is_finalizing")
_reg_tf(_STDLIB_TF, "opaque", "os.getenv os.environ.get os.stat os.listdir os.scandir os.walk "
        "sys.exc_info time.gmtime time.localtime itertools.count itertools.cycle itertools.repeat "
        "itertools.chain itertools.compress itertools.dropwhile itertools.takewhile itertools.filterfalse "
        "itertools.starmap itertools.tee itertools.zip_longest itertools.product itertools.accumulate "
        "itertools.pairwise functools.partial functools.cmp_to_key copy.copy copy.deepcopy "
        "logging.getLogger logging.debug logging.info logging.warning logging.error logging.critical "
        "logging.exception logging.log logging.basicConfig collections.deque hashlib.md5 hashlib.sha1 "
        "hashlib.sha256 hashlib.sha512 hashlib.sha224 hashlib.sha384 warnings.warn warnings.filterwarnings "
        "warnings.simplefilter random.random random.seed random.getstate json.dumps "
        "os.path.split os.path.splitext bisect.insort bisect.insort_left bisect.insort_right heapq.heapify "
        "heapq.heappush heapq.nlargest heapq.nsmallest itertools.batched collections.OrderedDict "
        "pathlib.Path pathlib.PurePath pathlib.PurePosixPath pathlib.PureWindowsPath")
_reg_tf(_STDLIB_TF, "str", "html.escape html.unescape urllib.parse.quote urllib.parse.quote_plus "
        "urllib.parse.unquote urllib.parse.unquote_plus shlex.quote")     # total str transforms: no raise on any str
_reg_tf(_STDLIB_TF, "opaque", "binascii.hexlify")                          # total bytes -> hex bytes, no raise
# the bare imported leaf names (from os.path import dirname), minus leaves that collide with a builtin, a str
# method, or a common identifier -- those keep the qualified form only.
_TF_BARE_DENY = frozenset({"join", "split", "get", "copy", "error", "system", "log", "reduce", "ref", "walk",
                           "exists", "count", "repeat", "chain", "product", "warn", "seed", "random", "info",
                           "debug", "warning", "critical", "exception", "version", "release", "node", "machine"})
_STDLIB_TF_BARE: Dict[str, str] = {q.split(".")[-1]: r for q, r in _STDLIB_TF.items()
                                   if q.split(".")[-1] not in _TF_BARE_DENY}


def _safe_stdlib_result(qual):
    """A trap-free fresh value of the sort `qual` (a dotted stdlib name) returns, or None when `qual` is not a
    known trap-free stdlib function. Used under trap freedom for a pure stdlib call that raises no modeled trap."""
    ret = _STDLIB_TF.get(qual)
    if ret is None:
        return None
    if ret == "int":
        return z3.FreshInt("tf_" + qual.split(".")[-1])
    if ret == "float":
        return z3.FreshConst(_F64, "tf_" + qual.split(".")[-1])
    if ret == "str":
        return z3.FreshConst(_SS, "tf_" + qual.split(".")[-1])
    if ret == "bool":
        return z3.FreshConst(z3.BoolSort(), "tf_" + qual.split(".")[-1])
    return _Opaque("tf_stdlib")


def _dotted_callee(func):
    """The dotted module path of an attribute-call callee (os.path.join -> 'os.path.join'), rooted at a Name,
    or None when the chain is not a pure name.attr…attr."""
    parts = []
    n = func
    while isinstance(n, ast.Attribute):
        parts.append(n.attr)
        n = n.value
    if not isinstance(n, ast.Name):
        return None
    parts.append(n.id)
    return ".".join(reversed(parts))


def _transcendental(name, arg, ctx):
    """math.sin / cos / exp / log as a sound over-approximation: an uninterpreted Float64 function
    constrained by axioms true of the real function (sin/cos range, exp sign, exp(0)=1, log(1)=0), with
    domain and overflow errors as traps. The domain / overflow trap goes into the trap channel unconditionally
    (as _sqrt_model does for sqrt), so trap-freedom triage catches a math.log(0) crash even with the value
    over-approximation channel (ctx.facts) absent; the value axioms need that channel. A satisfiable value
    query is UNKNOWN, not REFUTED (the axioms do not pin the value), so only PROVED is reported there."""
    if name not in _TRANSCENDENTAL:
        raise Unsupported(f"transcendental {name}")
    x = _to_fp(arg)
    z, one = z3.FPVal(0.0, _F64), z3.FPVal(1.0, _F64)
    if ctx.traps is not None:                                                     # the domain / overflow trap, always
        if name in ("sin", "cos"):
            ctx.traps.append(z3.And(ctx.pc, z3.fpIsInf(x)))                       # ValueError on +-inf
        elif name == "exp":                                                       # OverflowError for large x
            ctx.traps.append(z3.And(ctx.pc, z3.Not(z3.fpIsInf(x)), z3.fpGT(x, z3.FPVal(709.0, _F64))))
        else:                                                                     # log: ValueError on x <= 0 (incl +-0)
            ctx.traps.append(z3.And(ctx.pc, z3.fpLEQ(x, z)))
    if _TRAPFREE:                                                                 # trap-freedom: an arbitrary double,
        return z3.FreshConst(_F64, "trans_" + name)                              # the domain trap above being exact
    if ctx.facts is None:
        raise Unsupported(f"math.{name} needs the over-approximation channel (use prove / verify_predicate)")
    _note_overapprox(ctx, "math.%s" % name)
    finite = z3.And(z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsInf(x)))
    if name in ("sin", "cos"):
        r = (_SIN if name == "sin" else _COS)(x)
        ctx.facts.append(z3.Implies(finite, z3.And(z3.fpLEQ(z3.FPVal(-1.0, _F64), r), z3.fpLEQ(r, one),
                                                   z3.Not(z3.fpIsNaN(r)), z3.Not(z3.fpIsInf(r)))))
        ctx.facts.append(z3.Implies(z3.fpIsNaN(x), z3.fpIsNaN(r)))                # sin(nan) = nan
        ctx.facts.append(z3.Implies(z3.fpEQ(x, z), z3.fpEQ(r, z if name == "sin" else one)))   # sin(0)=0, cos(0)=1
        return r
    if name == "exp":
        r = _EXP(x)
        ctx.facts.append(z3.Implies(z3.Not(z3.fpIsNaN(x)), z3.fpGEQ(r, z)))       # exp >= 0 (underflow to +0)
        ctx.facts.append(z3.Implies(z3.fpIsNaN(x), z3.fpIsNaN(r)))
        ctx.facts.append(z3.Implies(z3.fpEQ(x, z), z3.fpEQ(r, one)))             # exp(0) = 1
        ctx.facts.append(z3.Implies(z3.And(finite, z3.fpGEQ(x, z)), z3.fpGEQ(r, one)))   # x >= 0 -> exp(x) >= 1
        ctx.facts.append(z3.Implies(z3.And(finite, z3.fpLEQ(x, z)), z3.fpLEQ(r, one)))   # x <= 0 -> exp(x) <= 1
        return r
    if name == "log":
        r = _LOG(x)
        ctx.facts.append(z3.Implies(z3.And(finite, z3.fpGT(x, z)),
                                    z3.And(z3.Not(z3.fpIsNaN(r)), z3.Not(z3.fpIsInf(r)))))
        ctx.facts.append(z3.Implies(z3.fpIsNaN(x), z3.fpIsNaN(r)))
        ctx.facts.append(z3.Implies(z3.fpEQ(x, one), z3.fpEQ(r, z)))            # log(1) = 0
        ctx.facts.append(z3.Implies(z3.And(finite, z3.fpGEQ(x, one)), z3.fpGEQ(r, z)))   # x >= 1 -> log(x) >= 0
        ctx.facts.append(z3.Implies(z3.And(finite, z3.fpGT(x, z), z3.fpLEQ(x, one)),     # 0 < x <= 1 -> log(x) <= 0
                                    z3.fpLEQ(r, z)))
        return r
    raise Unsupported(f"transcendental {name}")


# math functions with a domain ValueError, modeled as: emit the trap each raises, return a sound-typed
# over-approximation. The pure (never-trapping) math functions are in _STDLIB instead. math_domain_audit
# validates every trap against CPython. An overflow (OverflowError) is not a modeled trap, so it is not emitted.
_MATH_INT_DOMAIN = frozenset({"factorial", "comb", "perm", "isqrt"})
_MATH_FLOAT_DOMAIN = frozenset({"log2", "log10", "log1p", "asin", "acos", "acosh", "atanh", "fmod", "remainder"})
_MATH_PURE_FLOAT = frozenset({"expm1", "atan", "atan2", "asinh", "sinh", "cosh", "tanh", "degrees", "radians",
                              "hypot", "dist", "erf", "erfc", "exp2", "cbrt", "ldexp", "nextafter", "ulp"})
_MATH_FUNCS = (_MATH_INT_DOMAIN | _MATH_FLOAT_DOMAIN | _MATH_PURE_FLOAT
               | frozenset({"floor", "ceil", "trunc", "gcd", "lcm"}))


def _math_call(name, args, ctx):
    """A trap-bearing or rounding math function: emit the (exact) domain ValueError it raises and return a
    sound-typed over-approximated result. The result value is over-approximated only off the trap-freedom path
    (so an exact domain trap still refutes under check, matching _transcendental). Returns None when `name` is
    not modeled here (the caller's _STDLIB / unmodeled path applies)."""
    a0 = args[0] if args else None
    F, Z = _F64, z3.FPVal(0.0, _F64)

    def trap(cond):
        if ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, cond))

    def over():                                              # the value is over-approximated, but the domain trap
        if not _TRAPFREE:                                   # is exact, so trap freedom must still see the trap
            _note_overapprox(ctx, "math.%s" % name)

    def isfloat(v):
        return z3.is_expr(v) and (z3.is_int(v) or z3.is_bool(v) or _is_fp(v))
    if name in ("floor", "ceil", "trunc"):
        if not isfloat(a0):
            return None
        if z3.is_expr(a0) and (z3.is_int(a0) or z3.is_bool(a0)):
            if _TRAPFREE or ctx.facts is not None:
                return _as_int(a0)                           # floor / ceil / trunc of a real int is the int
            return None                                      # the integer engine models a float param as int and
            #                                                  cannot see the inf / nan trap: defer to the value engine
        f = _to_fp(a0)
        mf = z3.simplify(f)
        if z3.is_fp_value(mf):                               # a constant float (incl. a negated literal) folds exactly
            pf = _fp_to_py(mf)
            if pf is not None and not (_math.isinf(pf) or _math.isnan(pf)):
                return z3.IntVal(getattr(_math, name)(pf))
        trap(z3.Or(z3.fpIsInf(f), z3.fpIsNaN(f)))            # ValueError converting inf / nan to an integer
        over()
        return z3.FreshInt("m_" + name)
    if name in ("gcd", "lcm"):
        if any(not (z3.is_expr(x) and (z3.is_int(x) or z3.is_bool(x))) for x in args):
            return None
        over()
        r = z3.FreshInt(name)                                # never traps; the result is nonnegative
        if ctx.facts is not None:
            ctx.facts.append(r >= 0)
        return r
    if name == "pow":
        # math.pow(x, y): always a float (never complex). ValueError iff a negative finite base with a non-integral
        # finite exponent, or zero base with a finite negative exponent (validated by math_pow_axiom_audit). The
        # value is an uninterpreted Float64 pow with the libm anchors x ** 0 == 1, 1 ** y == 1, nonneg base ->
        # nonneg, 0 ** y == 0 (y > 0).
        if len(args) < 2 or not isfloat(a0) or not isfloat(args[1]):
            return None                                      # a non-numeric argument: abstain (its own TypeError)
        x, y = _to_fp(a0), _to_fp(args[1])
        fin = lambda v: z3.And(z3.Not(z3.fpIsInf(v)), z3.Not(z3.fpIsNaN(v)))
        integral = z3.fpEQ(y, z3.fpRoundToIntegral(z3.RNE(), y))   # y is a whole number (finite y)
        trap(z3.Or(z3.And(fin(x), z3.fpLT(x, Z), fin(y), z3.Not(integral)),   # negative finite base ** fractional
                   z3.And(z3.fpIsZero(x), fin(y), z3.fpLT(y, Z))))            # zero base ** finite negative
        over()
        r = z3.Function("py_math_pow", F, F, F)(x, y)
        if ctx.facts is not None:
            one = z3.FPVal(1.0, F)
            ctx.facts.append(z3.Implies(z3.fpIsZero(y), z3.fpEQ(r, one)))                     # x ** 0 == 1
            ctx.facts.append(z3.Implies(z3.fpEQ(x, one), z3.fpEQ(r, one)))                    # 1 ** y == 1
            ctx.facts.append(z3.Implies(z3.And(z3.Not(z3.fpIsNaN(x)), z3.Not(z3.fpIsNaN(y)),
                                               z3.fpGEQ(x, Z)), z3.fpGEQ(r, Z)))              # nonneg base -> nonneg
            ctx.facts.append(z3.Implies(z3.And(z3.fpIsZero(x), z3.fpGT(y, Z)), z3.fpIsZero(r)))   # 0 ** y (y>0) == 0
        return r
    if name in _MATH_INT_DOMAIN:
        if not (z3.is_expr(a0) and (z3.is_int(a0) or z3.is_bool(a0))):
            return None                                      # a non-integer argument: abstain (its own trap)
        n = _as_int(a0)
        if name in ("comb", "perm"):
            k = _as_int(args[1]) if len(args) > 1 and z3.is_expr(args[1]) and z3.is_int(args[1]) else None
            if k is None:
                return None
            trap(z3.Or(n < 0, k < 0))                        # ValueError: a negative argument
        else:
            trap(n < 0)                                      # factorial / isqrt of a negative: ValueError
        over()
        r = z3.FreshInt(name)
        if ctx.facts is not None:
            ctx.facts.append(r >= (1 if name == "factorial" else 0))
        return r
    if name in _MATH_FLOAT_DOMAIN:
        if name in ("fmod", "remainder"):
            if len(args) < 2 or not isfloat(a0) or not isfloat(args[1]):
                return None
            trap(z3.Or(z3.fpIsInf(_to_fp(a0)), z3.fpIsZero(_to_fp(args[1]))))   # ValueError: an infinite dividend or zero divisor
        else:
            if not isfloat(a0):
                return None
            f = _to_fp(a0)
            one, neg1 = z3.FPVal(1.0, F), z3.FPVal(-1.0, F)
            if name in ("log2", "log10"):
                trap(z3.fpLEQ(f, Z))                         # log of a non-positive: ValueError
            elif name == "log1p":
                trap(z3.fpLEQ(f, neg1))
            elif name in ("asin", "acos"):
                trap(z3.Or(z3.fpLT(f, neg1), z3.fpGT(f, one)))   # outside [-1, 1]
            elif name == "acosh":
                trap(z3.fpLT(f, one))                        # x < 1
            else:                                            # atanh
                trap(z3.Or(z3.fpLEQ(f, neg1), z3.fpGEQ(f, one)))
        over()
        return z3.FreshConst(F, "m_" + name)
    if name in _MATH_PURE_FLOAT:
        for x in args:
            if not isfloat(x):
                return None                                  # a non-numeric argument: abstain
            _to_fp(x)                                        # trap-check (already evaluated)
        over()
        return z3.FreshConst(F, "m_" + name)
    return None


_SS = z3.StringSort()
# The Unicode codepoint bijection ord <-> chr over [0, 0x10FFFF], as a pair of mutually-inverse uninterpreted
# functions. ord(c) of a single character lands in the range and round-trips (chr(ord(c)) == c); chr(n) of a
# valid codepoint is one character and round-trips (ord(chr(n)) == n). A constant argument folds to its exact
# value instead. The relations are exact (sound for PROVED and REFUTED); only the unconstrained codepoint of a
# symbolic character is over-approximated.
_MAXCP = 0x10FFFF
_ORD = z3.Function("py_ord", _SS, z3.IntSort())
_CHR = z3.Function("py_chr", z3.IntSort(), _SS)
_STR_STRIP_METHODS = {"strip", "lstrip", "rstrip"}
_STR_CASE_METHODS = {"upper", "lower", "capitalize", "title", "swapcase", "casefold"}
_STR_METHODS = _STR_STRIP_METHODS | _STR_CASE_METHODS
# the is* predicates: Python returns False for "" on all but isprintable / isascii (True for "")
_STR_PREDS = {"isdigit", "isalpha", "isalnum", "isspace", "isupper", "islower", "isnumeric",
              "isdecimal", "istitle", "isidentifier", "isprintable", "isascii"}
_STR_PRED_FN = {}


def _str_method(name, s, ctx):
    """strip / lstrip / rstrip and the case maps (upper / lower / capitalize / title / swapcase /
    casefold), which z3's theory lacks, as sound over-approximations: strip leaves a substring no longer
    than s (lstrip drops a prefix, rstrip a suffix); a case map is empty exactly when s is (Unicode-safe,
    since 'ss'.upper() and 'ß'.upper() change length). PROVED where it follows, else UNKNOWN."""
    over = _overapprox(ctx, "str." + name, _SS, "str_" + name)
    if over is not None:
        return over
    L = z3.Length
    r = z3.Function("py_str_" + name, _SS, _SS)(s)
    if name == "strip":
        ctx.facts += [z3.Contains(s, r), L(r) <= L(s)]
    elif name == "lstrip":
        ctx.facts += [z3.SuffixOf(r, s), L(r) <= L(s)]
    elif name == "rstrip":
        ctx.facts += [z3.PrefixOf(r, s), L(r) <= L(s)]
    else:                                                # case maps: empty iff empty
        ctx.facts.append((L(s) == 0) == (L(r) == 0))
    return r


def _str_predicate(name, s, ctx):
    """An is* predicate as a sound over-approximation: an uninterpreted Bool whose only axiom is its
    empty-string value (False for "", except isprintable / isascii which are True). PROVED where it
    follows, else UNKNOWN."""
    over = _overapprox(ctx, "str." + name, z3.BoolSort(), "str_" + name)
    if over is not None:
        return over
    if name not in _STR_PRED_FN:
        _STR_PRED_FN[name] = z3.Function("py_str_" + name, _SS, z3.BoolSort())
    r = _STR_PRED_FN[name](s)
    empty = z3.Length(s) == 0
    ctx.facts.append(z3.Implies(empty, r if name in ("isprintable", "isascii") else z3.Not(r)))
    return r


_STR_COUNT = z3.Function("py_str_count", _SS, _SS, z3.IntSort())
_STR_REPLACE = z3.Function("py_str_replace", _SS, _SS, _SS, _SS)
_STR_PAD_FN = {}


def _str_count(s, sub, ctx):
    """str.count as a sound over-approximation: a count >= 0 that is 0 when sub is absent from s."""
    over = _overapprox(ctx, "str.count", z3.IntSort(), "str_count")
    if over is not None:
        return over
    r = _STR_COUNT(s, sub)
    ctx.facts += [r >= 0, z3.Implies(z3.Not(z3.Contains(s, sub)), r == 0)]
    return r


def _str_replace(s, old, new, ctx):
    """str.replace(old, new): folded exactly when s, old, and new are all constant strings (Python computes
    it); otherwise a sound over-approximation -- an uninterpreted result equal to s when old is absent. z3's
    solver does not reason about replace_all symbolically (it returns unknown), so a symbolic replace cannot be
    made exact and stays PROVED-only on what the absent-fact forces."""
    if z3.is_string_value(s) and z3.is_string_value(old) and z3.is_string_value(new) and old.as_string() != "":
        return z3.StringVal(s.as_string().replace(old.as_string(), new.as_string()))
    over = _overapprox(ctx, "str.replace", _SS, "str_replace")
    if over is not None:
        return over
    r = _STR_REPLACE(s, old, new)
    ctx.facts.append(z3.Implies(z3.Not(z3.Contains(s, old)), r == s))
    return r


def _str_pad(name, s, width, ctx):
    """ljust / rjust / center / zfill as a sound over-approximation: the result has length max(len(s),
    width) -- s unchanged when already at least that wide, otherwise padded to exactly width."""
    over = _overapprox(ctx, "str." + name, _SS, "str_" + name)
    if over is not None:
        return over
    if name not in _STR_PAD_FN:
        _STR_PAD_FN[name] = z3.Function("py_str_" + name, _SS, z3.IntSort(), _SS)
    r = _STR_PAD_FN[name](s, width)
    L = z3.Length
    ctx.facts.append(L(r) == z3.If(width > L(s), width, L(s)))
    return r


def _str_partition(s, sep, last):
    """str.partition / rpartition, exactly: split s at the first (last) occurrence of sep into the
    3-tuple (head, sep-or-empty, tail), with the not-found cases (s,'','') / ('','',s)."""
    idx = z3.LastIndexOf(s, sep) if last else z3.IndexOf(s, sep, z3.IntVal(0))
    found = idx >= 0
    ls, lsep = z3.Length(s), z3.Length(sep)
    before = z3.SubString(s, z3.IntVal(0), idx)
    tail = z3.SubString(s, idx + lsep, ls - idx - lsep)
    empty = z3.StringVal("")
    if last:
        return (z3.If(found, before, empty), z3.If(found, sep, empty), z3.If(found, tail, s))
    return (z3.If(found, before, s), z3.If(found, sep, empty), z3.If(found, tail, empty))


def _str_format(fmt, args, ctx, kwnames=None):
    """str.format on a literal format string, as a sound over-approximation: the result is a fresh string of
    unknown content (over-approximation channel) when every replacement field is a positional field satisfied by
    the arguments or a plain named field {name} whose keyword the call supplies (`kwnames`), and is spec-free. A
    positional index beyond the arguments, or a named field with no matching keyword, is an IndexError / KeyError
    trap. A nested or attribute field ({0.x} / {a[k]}, which may itself trap), a format spec, mixed
    automatic/manual numbering, or a malformed format string is left unmodeled (None; the caller reports
    UNKNOWN)."""
    import string as _string
    try:
        parsed = list(_string.Formatter().parse(fmt))
    except (ValueError, IndexError):
        return None                                          # malformed format string
    auto = 0
    saw_auto = saw_manual = missing_named = False
    max_index = -1
    for _text, field, spec, _conv in parsed:
        if field is None:
            continue                                         # literal text / escaped brace: no field
        if spec:
            return None                                      # a format spec can raise ValueError
        if field == "":
            saw_auto = True; idx = auto; auto += 1            # automatic numbering: {}
        elif field.isdigit():
            saw_manual = True; idx = int(field)               # manual numbering: {0}
        else:                                                # a named field {name}, or nested {name.x} / {name[k]}
            base = field.split(".")[0].split("[")[0]
            if base != field:
                return None                                  # a nested / attribute access on the argument: may trap
            if kwnames is None or base not in kwnames:        # no keyword argument supplies this named field
                missing_named = True
            continue
        max_index = max(max_index, idx)
    if saw_auto and saw_manual:
        return None                                          # mixing automatic and manual numbering raises
    if missing_named or max_index >= len(args):
        if ctx.traps is not None:
            ctx.traps.append(ctx.pc)                         # KeyError (named field) / IndexError (positional): no argument
        return _Opaque("format")
    _note_overapprox(ctx, "str.format")
    return z3.FreshConst(_SS, "fmt")                         # a string of statically-unknown content


import re as _re
_ALIGN_SPEC = _re.compile(r"(?:.?[<>^])?(?:[1-9]\d*)?")       # [fill]<>^ then an optional non-zero-leading width


def _alignment_only_spec(spec_node):
    """The format-spec text if it is a constant alignment-and-width-only spec -- an optional [fill]<>^ alignment
    then an optional non-zero-leading width -- which str.__format__ applies to a str / int / float / bool value
    without raising, else None. A sign, 0-fill, grouping, precision, or presentation type can raise on an
    incompatible value, and a leading-0 width implies the '=' alignment a string rejects, so any of those is
    left unmodeled. An empty spec ({x:}) is a no-op and qualifies."""
    if not isinstance(spec_node, ast.JoinedStr):
        return None
    if not spec_node.values:
        return ""                                            # {x:} -- an empty spec
    if not (len(spec_node.values) == 1 and isinstance(spec_node.values[0], ast.Constant)
            and isinstance(spec_node.values[0].value, str)):
        return None                                          # a dynamic nested spec ({x:{w}}): unmodeled
    text = spec_node.values[0].value
    return text if _ALIGN_SPEC.fullmatch(text) else None


_FMT_SPEC = _re.compile(r"(?:(?P<fill>.)?(?P<align>[<>=^]))?(?P<sign>[-+ ])?(?P<zc>z)?(?P<alt>\#)?"
                        r"(?P<zero>0)?(?P<width>\d+)?(?P<group>[,_])?(?:\.(?P<prec>\d+))?(?P<type>[bcdeEfFgGnosxX%])?$")


def _format_spec_safe(spec, v):
    """Whether format(value-of-v's-modeled-type, spec) provably never raises, for a recognized constant spec.
    A float takes the float-presentation types; an int / bool takes the integer types without a precision or a
    float type with one; a string takes the string / empty type with no numeric flags. Conservative -- an
    unrecognized spec or a type-incompatible pairing returns False. Validated against CPython in format_spec_audit."""
    m = _FMT_SPEC.fullmatch(spec)
    if m is None:
        return False
    g = m.groupdict()
    typ = g["type"] or ""
    if _is_fp(v):
        return typ in ("", "f", "F", "e", "E", "g", "G", "%", "n")
    if z3.is_expr(v) and (z3.is_int(v) or z3.is_bool(v)):
        if g["zc"]:
            return False                                     # the z coercion flag needs a floating type
        if typ in ("f", "F", "e", "E", "g", "G", "%"):       # a float presentation of an int: coerced, precision allowed
            return True
        if typ in ("", "d", "n", "b", "o", "x", "X"):        # an integer presentation: a precision is a ValueError
            return g["prec"] is None
        return False                                         # 'c' (an out-of-range chr), or an unknown type
    if _is_str(v):
        return (typ in ("", "s") and g["align"] != "=" and not
                (g["sign"] or g["zc"] or g["alt"] or g["zero"] or g["group"]))
    return False


def _const_format_spec_safe(spec_node, v):
    """Whether a constant f-string format spec applied to modeled scalar `v` provably never raises. Extracts the
    constant spec text (a dynamic nested spec declines) and defers the type compatibility to _format_spec_safe."""
    if not isinstance(spec_node, ast.JoinedStr):
        return False
    if not spec_node.values:
        return True                                          # {x:} : an empty spec is a no-op
    if not (len(spec_node.values) == 1 and isinstance(spec_node.values[0], ast.Constant)
            and isinstance(spec_node.values[0].value, str)):
        return False                                         # a dynamic nested spec ({x:{w}})
    return _format_spec_safe(spec_node.values[0].value, v)


def _str_call(meth, s, a, ctx, kwnames=None):
    """Model a string method call s.meth(*a) to a Z3 term, or return None if it is not modeled. Methods
    z3's theory supports are exact; the rest are sound over-approximations (needing ctx.facts). Methods
    returning a dynamic list of strings (split / join / splitlines) and translate are left to the caller to
    report UNKNOWN. `kwnames` are the call's keyword names, used to satisfy str.format named fields."""
    L = z3.Length
    if meth in ("startswith", "endswith") and len(a) == 1:
        op = z3.PrefixOf if meth == "startswith" else z3.SuffixOf
        if isinstance(a[0], tuple):                                  # a tuple of prefixes/suffixes: any
            ps = [p for p in a[0] if _is_str(p)]
            return z3.Or(*[op(p, s) for p in ps]) if ps else z3.BoolVal(False)
        return op(a[0], s) if _is_str(a[0]) else None
    if meth in ("startswith", "endswith") and 2 <= len(a) <= 3 and _is_str(a[0]) \
            and z3.is_expr(s) and s.sort() == z3.StringSort() \
            and all(z3.is_int_value(x) and x.as_long() >= 0 for x in a[1:]):
        # startswith/endswith with a non-negative integer start (and optional end) is exact over s[start:end], so the
        # prefix/suffix test keeps the length correlation (a true result implies s is long enough). A variable or
        # negative bound falls through to UNKNOWN rather than a fresh bool, which would lose that correlation.
        length = (a[2] - a[1]) if len(a) == 3 else (z3.Length(s) - a[1])
        sub = z3.SubString(s, a[1], length)
        op = z3.PrefixOf if meth == "startswith" else z3.SuffixOf
        return op(a[0], sub)
    if meth in ("removeprefix", "removesuffix") and len(a) == 1 and _is_str(a[0]):
        p = a[0]
        if meth == "removeprefix":
            return z3.If(z3.PrefixOf(p, s), z3.SubString(s, L(p), L(s) - L(p)), s)
        return z3.If(z3.SuffixOf(p, s), z3.SubString(s, z3.IntVal(0), L(s) - L(p)), s)
    if meth == "find" and 1 <= len(a) <= 2 and _is_str(a[0]):
        return z3.IndexOf(s, a[0], _as_int(a[1]) if len(a) == 2 else z3.IntVal(0))
    if meth == "rfind" and len(a) == 1 and _is_str(a[0]):
        return z3.LastIndexOf(s, a[0])
    if ((meth == "find" and len(a) == 3) or (meth == "rfind" and len(a) in (2, 3))) \
            and _is_str(a[0]) and ctx.facts is not None:
        # a start/end window on find/rfind: z3's IndexOf/LastIndexOf carries no end bound, so the result is the sound
        # over-approximation -- an index in [-1, len(s)) (find/rfind return -1 when the substring is absent and never
        # raise) -- which decides a later end + 1 or a slice on the result.
        for arg in a[1:]:
            _as_int(arg)                                         # the start / end positions are trap-checked
        k = z3.FreshInt("find"); ctx.facts.append(z3.And(k >= -1, k < z3.Length(s)))
        return k
    if meth in ("index", "rindex") and len(a) == 1 and _is_str(a[0]):
        idx = z3.LastIndexOf(s, a[0]) if meth == "rindex" else z3.IndexOf(s, a[0], z3.IntVal(0))
        if ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, idx < 0))               # ValueError when sub is not found
        return idx
    if meth == "index" and len(a) == 2 and _is_str(a[0]):           # index(sub, start): search from start, raising
        idx = z3.IndexOf(s, a[0], _as_int(a[1]))                    # ValueError if sub is absent in s[start:]
        if ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, idx < 0))
        return idx
    if meth in ("partition", "rpartition") and len(a) == 1 and _is_str(a[0]):
        return _str_partition(s, a[0], meth == "rpartition")
    if meth in _STR_METHODS and not a:
        return _str_method(meth, s, ctx)
    if meth in _STR_PREDS and not a:
        return _str_predicate(meth, s, ctx)
    if meth == "count" and len(a) == 1 and _is_str(a[0]):
        return _str_count(s, a[0], ctx)
    if meth == "count" and 2 <= len(a) <= 3 and _is_str(a[0]) and z3.is_expr(s) \
            and s.sort() == z3.StringSort() and ctx.facts is not None:
        for arg in a[1:]:
            _as_int(arg)                                         # the start / end positions are trap-checked
        k = z3.FreshInt("count"); ctx.facts.append(z3.And(k >= 0, k <= z3.Length(s)))
        return k                                                 # count in a window: a sound count in [0, len(s)]
    if meth == "replace" and len(a) == 2 and _is_str(a[0]) and _is_str(a[1]):
        return _str_replace(s, a[0], a[1], ctx)
    if meth == "replace" and len(a) == 3 and _is_str(a[0]) and _is_str(a[1]):
        _as_int(a[2])                                            # the count argument is trap-checked
        return z3.FreshConst(z3.StringSort(), "replaced")        # replace(old, new, count) never raises; a string
        #                                                          result, over-approximated (the count limit unpinned)
    if meth in ("ljust", "rjust", "center", "zfill") and len(a) >= 1:
        return _str_pad(meth, s, _as_int(a[0]), ctx)
    if meth == "join" and len(a) == 1 and isinstance(a[0], tuple) and all(_is_str(x) for x in a[0]):
        parts = a[0]                                                 # s.join(parts): separator between parts
        if not parts:
            return z3.StringVal("")
        acc = parts[0]
        for p in parts[1:]:
            acc = z3.Concat(acc, s, p)
        return acc
    if meth == "join" and len(a) == 1 and isinstance(a[0], _StrSeq):    # sep.join(a string sequence, e.g. a split
        return z3.FreshConst(z3.StringSort(), "joined")                 # result): a string result, trap free (the
        #                                                                 parts are strings, so no TypeError)
    if meth in ("split", "rsplit"):                                  # a list of strings
        if not a:                                                    # s.split(): split on whitespace -- CAN be empty
            k = z3.FreshInt("splitlen")                              # ('  '.split() == []), so its length is only >= 0
            if ctx.facts is not None:
                ctx.facts.append(k >= 0)
            return _StrSeq("split", length=k)
        if 1 <= len(a) <= 2 and _is_str(a[0]):                       # s.split(sep[, maxsplit]): empty sep raises
            if ctx.traps is not None:
                ctx.traps.append(z3.And(ctx.pc, z3.Length(a[0]) == 0))   # ValueError on an empty separator
            if len(a) == 2:
                _as_int(a[1])                                        # maxsplit is trap-checked
            k = z3.FreshInt("splitlen")                              # a non-empty separator yields >= 1 part (the whole
            if ctx.facts is not None:                                # string if absent), so split(sep)[0] / [-1] decide
                ctx.facts.append(k >= 1)
            return _StrSeq("split", length=k)
        return None
    if meth == "splitlines" and len(a) <= 1:
        k = z3.FreshInt("splitlen")                                  # splitlines() of '' is [] -- only >= 0
        if ctx.facts is not None:
            ctx.facts.append(k >= 0)
        return _StrSeq("splitlines", length=k)
    if meth == "format" and z3.is_string_value(s):           # a literal format string: sound over-approximation
        return _str_format(s.as_string(), a, ctx, kwnames)   # (a non-literal receiver / format_map stays UNKNOWN)
    if meth == "encode" and z3.is_expr(s) and s.sort() == z3.StringSort() and ctx.facts is not None and not kwnames:
        # s.encode() / s.encode('utf-8'): the default utf-8 -- and the utf-8 family by name -- encodes every str
        # without raising, producing bytes of length >= len(s) (each character is one to four bytes), so a later
        # encode()[i] under a len(s) guard stays sound. A lossy codec (ascii / latin-1) can raise UnicodeEncodeError,
        # and a keyword form (encoding= / errors=) hides the codec, so only a no-arg or explicit-utf-8 positional
        # form is modeled; anything else is left UNKNOWN.
        _u8 = not a or (len(a) == 1 and z3.is_string_value(a[0])
                        and a[0].as_string().lower().replace("-", "").replace("_", "") in ("utf8", "u8"))
        if _u8:
            k = z3.FreshInt("enc"); ctx.facts.append(k >= 0)
            return _SafeContainer("encoded", byteslike=True, length=z3.Length(s) + k)
    return None


def _int_method(meth, n, ctx):
    """An int method call n.meth() to a Z3 term, or None if not modeled. __index__ / conjugate are n itself;
    bit_length / bit_count are nonnegative ints over-approximated (bit_length is 0 exactly when n is). None traps."""
    if meth in ("__index__", "conjugate"):
        return n
    if meth in ("bit_length", "bit_count"):
        if ctx.facts is None:
            return z3.FreshInt(meth) if _TRAPFREE else None
        _note_overapprox(ctx, "int.%s" % meth)
        r = z3.FreshInt(meth)
        ctx.facts.append(r >= 0)
        if meth == "bit_length":
            ctx.facts.append((r == 0) == (n == 0))           # bit_length(0) == 0, >= 1 otherwise
        return r
    return None


_FP_CMP = {ast.Lt: z3.fpLT, ast.LtE: z3.fpLEQ, ast.Gt: z3.fpGT, ast.GtE: z3.fpGEQ,
           ast.Eq: z3.fpEQ, ast.NotEq: z3.fpNEQ}


def _as_bool(x, ctx=None):
    """Python truthiness of an evaluated term: a bool stays a bool, an int is != 0, a float is nonzero (NaN is
    truthy, +-0.0 are falsy), a tuple or list literal is truthy iff it is non-empty. A value with no decidable
    truth -- an opaque receiver, an object field (`if o.x:`, whose runtime type may be a str/list/None, not the
    int it duck-types as in arithmetic), a dict-get / unmodeled-call result, a set or map -- is NOT treated as
    truthy (Python's default object truth); under the total trap-free engine it becomes a fresh bool so BOTH
    branches stay live (a pruned else would hide its traps), and the path is over-approximated so a resulting
    trap withholds REFUTED (the opaque truth has no concrete witness)."""
    if isinstance(x, tuple):
        return z3.BoolVal(len(x) > 0)
    if isinstance(x, _NoneVal):                              # None is always falsy: `if d.get(k):` / `x or default`
        return z3.BoolVal(False)                             # guard a possibly-None value (the value engine's own None,
        #                                                       beyond the literal-None cases the None engine catches)
    if isinstance(x, _StrSeq) and not x.unsized and x.length is not None:
        return x.length != 0                                 # a sized split result is truthy iff non-empty, tied to
        #                  its [i] bounds-check length (an unsized iterator falls through -- always truthy)
    if isinstance(x, _SafeContainer) and not x.unsized:      # truthy iff non-empty, using the SAME length its c[i]
        n = x.length if getattr(x, "length", None) is not None else z3.Int("len_" + x.name)
        return n != 0                                        # bounds check uses (explicit for a comprehension / split
        #                  result, else by name), so `if c: c[0]` proves
    if isinstance(x, _DictParam):                            # bool(dict) is len(d) != 0, the SAME length len(d) and
        n = x.length if getattr(x, "length", None) is not None else z3.Int("len_" + x.name)
        return n != 0                                        # d.popitem() / max(d.values()) use, so `if d:` guards them
    if isinstance(x, _NdArray):                              # bool(ndarray / Series) is a ValueError for more than one
        raise Unsupported("truth value of an array is ambiguous "   # element (numpy/pandas), so its truthiness is not
                          "(use .any() / .all() or a size check)")  # a benign bool -- abstain rather than over-approximate
    if _is_str(x):
        return z3.Length(x) != 0                              # a string is truthy iff non-empty
    if z3.is_bool(x):
        return x
    if z3.is_fp(x):
        return z3.fpNEQ(x, z3.FPVal(0.0, _F64))
    if z3.is_expr(x):
        return x != 0                                        # a z3 int / bitvector: truthy iff nonzero
    if _TRAPFREE:                                            # an _Opaque / object field / dict-get / set / map / lambda:
        if ctx is not None:                                 # truth value unknown, so a fresh bool keeps BOTH branches
            ctx.overapprox = True                           # live (no false PROVED on a pruned else) and the path is
        return z3.FreshConst(z3.BoolSort(), "hb")           # over-approximated so a trap on either branch withholds
    raise Unsupported("truthiness of an unmodeled value")   # REFUTED (the opaque truth has no concrete witness)


def _as_int(x):
    """Coerce a bool term to its integer value (True -> 1, False -> 0); int and float
    terms are returned unchanged."""
    if isinstance(x, _FieldVal):                             # an opaque object's field: a stable int (numeric duck-typing)
        return z3.Int("fldval_" + x.name)
    if isinstance(x, (_Opaque, _Closure)):
        if BEST_EFFORT and type(x) is _Opaque:               # best-effort: an opaque result is assumed to be an int
            _best_effort_assume()
            return z3.FreshInt("be_int")
        raise Unsupported("arithmetic on an unmodeled value")
    return z3.If(x, z3.IntVal(1), z3.IntVal(0)) if z3.is_bool(x) else x


def _is_zero(x):
    """The divisor-is-zero condition for a term used as a true-division denominator;
    Python raises ZeroDivisionError for both int and float division by zero."""
    return z3.fpEQ(x, z3.FPVal(0.0, _F64)) if _is_fp(x) else (_as_int(x) == 0)


def _term_eq(a, b):
    """Structural (Leibniz) value equality of two evaluated values, recursing into tuples
    element-wise. This is the right notion for equivalence: two results are the same value iff
    bit-identical, so NaN equals NaN and +0.0 differs from -0.0 (it is not Python's float ==)."""
    if isinstance(a, tuple) or isinstance(b, tuple):
        if not (isinstance(a, tuple) and isinstance(b, tuple) and len(a) == len(b)):
            return z3.BoolVal(False)
        return z3.And(*[_term_eq(x, y) for x, y in zip(a, b)]) if a else z3.BoolVal(True)
    if isinstance(a, _Complex) or isinstance(b, _Complex):
        a, b = _cx(a), _cx(b)
        return z3.And(a.re == b.re, a.im == b.im)
    if not (z3.is_expr(a) and z3.is_expr(b)):
        raise Unsupported("equality of an unmodeled value")
    if a.sort() != b.sort():                                 # values of different types are never equal
        return z3.BoolVal(False)
    return a == b


def _term_neq(a, b):
    return z3.Not(_term_eq(a, b))


_NUMERIC_SORTS = (z3.Z3_INT_SORT, z3.Z3_REAL_SORT, z3.Z3_FLOATING_POINT_SORT)


def _is_numeric_sort(s):
    try:
        return s.kind() in _NUMERIC_SORTS
    except z3.Z3Exception:
        return False


def _map_key(t):
    """The canonical dict-key term: a bool collapses to its 0/1 integer, since Python hashes True as 1 and
    False as 0, so a bool key and the matching int are the same key. Other terms are returned unchanged."""
    return _as_int(t) if (z3.is_expr(t) and z3.is_bool(t)) else t


def _key_match(q, k):
    """Whether dict-key term q provably equals stored key k (True), provably differs (False), or cannot be
    decided syntactically (None). Concrete int / string / bool values compare by value; otherwise only the
    syntactically-identical case is decided (so a stored key that is the same term as q matches)."""
    if not (z3.is_expr(q) and z3.is_expr(k)):
        return None                                          # a tuple / complex / opaque key: undecided here
    if z3.is_int_value(q) and z3.is_int_value(k):
        return q.as_long() == k.as_long()
    if z3.is_string_value(q) and z3.is_string_value(k):
        return q.as_string() == k.as_string()
    if z3.eq(q, k):
        return True
    return None


def _map_get(m, q, ctx):
    """The value dict `m` yields at key term `q`, with a KeyError trap (on ctx.traps) when q matches no
    stored key. Newest-first, so the last write to a key wins; a read whose key is provably a stored key
    returns that value with no trap. Defers (Unsupported) on a dict whose value types differ across keys
    or whose keys mix numeric types (Python conflates 1, 1.0, True), which the engine cannot resolve."""
    q = _map_key(q)
    keys = [_map_key(k) for k in m.keys]
    for k, v in zip(reversed(keys), reversed(m.vals)):       # the most recent provably-equal key wins
        d = _key_match(q, k)
        if d is True:
            return v
        if d is None:
            break                                            # an undecidable newer key shadows older ones
    if not keys:
        if ctx.traps is not None:
            ctx.traps.append(ctx.pc)                         # an empty dict: every read is a KeyError
        return _Opaque("keyerror")
    if not all(z3.is_expr(v) for v in m.vals):
        raise Unsupported("dict value is not a modeled scalar")
    if len({v.sort() for v in m.vals}) != 1:
        raise Unsupported("dict with heterogeneous value types")
    if z3.is_expr(q) and _is_numeric_sort(q.sort()) and any(
            z3.is_expr(k) and k.sort() != q.sort() and _is_numeric_sort(k.sort()) for k in keys):
        raise Unsupported("dict with mixed numeric key types")   # 1 / 1.0 / True conflate; not resolved here
    contains = z3.Or(*[_term_eq(q, k) for k in keys])
    if ctx.traps is not None:
        ctx.traps.append(z3.And(ctx.pc, z3.Not(contains)))  # KeyError when q is none of the keys
    res = z3.FreshConst(m.vals[0].sort(), "kdef")           # never trusted: a matching branch always wins
    for k, v in zip(keys, m.vals):                          # oldest first, so the newest entry is outermost
        res = z3.If(_term_eq(q, k), v, res)
    return res


def _subst(v, subs):
    """z3.substitute lifted over tuple and complex values (substitutes each component)."""
    if isinstance(v, tuple):
        return tuple(_subst(x, subs) for x in v)
    if isinstance(v, _Complex):
        return _Complex(_subst(v.re, subs), _subst(v.im, subs))
    if not z3.is_expr(v):                                    # _Opaque / _Closure / _FuncRef / _Lambda: nothing to substitute
        return v
    return z3.substitute(v, *subs) if subs else v


def _pow_expand(base, expnode):
    """Integer base ** k for a constant non-negative integer k (<= 64), expanded to exact repeated
    multiplication. A float base, or a variable/negative/large exponent, is not modeled."""
    if not (isinstance(expnode, ast.Constant) and isinstance(expnode.value, int)
            and not isinstance(expnode.value, bool) and 0 <= expnode.value <= 64):
        raise Unsupported("** requires a constant non-negative integer exponent <= 64")
    if _is_fp(base):
        raise Unsupported("float ** matches CPython's libm pow only approximately; not modeled")
    base = _as_int(base)
    acc = z3.IntVal(1)
    for _ in range(expnode.value):
        acc = acc * base
    return acc


def _pow_axioms(b, e, r):
    """Sound facts for an integer b ** e over-approximated by r, constraining the e >= 0 case."""
    return [z3.Implies(z3.And(b >= 0, e >= 0), r >= 0),
            z3.Implies(z3.And(b >= 1, e >= 0), r >= 1),
            z3.Implies(e == 0, r == 1),
            z3.Implies(b == 1, r == 1),
            z3.Implies(z3.And(b == 0, e > 0), r == 0)]


def _const_num(node):
    """The int/float a constant AST expression denotes, folding a leading unary minus (x ** -1); None otherwise."""
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)) and not isinstance(node.value, bool):
        return node.value
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        v = _const_num(node.operand)
        return None if v is None else -v
    return None


def _fp_pow(base, expnode, ctx):
    """Float x ** n for a constant integral exponent n (int or integral-valued float). x ** 0 / x ** 1 exact;
    |n| >= 2 an uninterpreted Float64 pow with sign/anchor axioms (nonneg base -> nonneg, even power -> nonneg,
    1 ** n == 1, 0 ** n == 0 for n > 0, NaN ** n == NaN); a negative exponent traps at base 0. A fractional or
    non-constant exponent is not modeled (a negative base yields complex -- math.pow handles the fractional case)."""
    base = _to_fp(base)
    e = _const_num(expnode)                              # folds a leading unary minus: x ** -1 is UnaryOp, not Constant
    if e is None:
        raise Unsupported("float ** with a non-constant exponent is not modeled")
    if isinstance(e, float):                              # an integral-valued float exponent (2.0, -1.0) is real for
        if not _math.isfinite(e) or e != int(e):         # any base; a fractional one yields a complex negative power
            raise Unsupported("float ** with a non-integral exponent is not modeled (a negative base yields complex)")
        e = int(e)
    n = e
    if n == 0:
        return z3.FPVal(1.0, _F64)                       # x ** 0 == 1.0 for every double, NaN and Inf included
    if n == 1:
        return base                                       # x ** 1 == x (bit-exact)
    if ctx.facts is None:
        if n < 0 and ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, z3.fpIsZero(base)))   # 0.0 ** (negative integer) -> ZeroDivisionError
        if _TRAPFREE:                                    # trap freedom: a power |n| >= 2 raises only at base 0 (n < 0)
            return z3.FreshConst(_F64, "fpow")           # the value is opaque, but the trap channel is exact
        raise Unsupported("float ** to a power |n| >= 2 needs the over-approximation channel (use prove / verify_predicate)")
    _note_overapprox(ctx, "float ** (a constant integral power)")
    z, one = z3.FPVal(0.0, _F64), z3.FPVal(1.0, _F64)
    if n < 0 and ctx.traps is not None:
        ctx.traps.append(z3.And(ctx.pc, z3.fpIsZero(base)))   # 0.0 ** (negative integer) -> ZeroDivisionError
    r = z3.Function("py_fpow_%s%d" % ("m" if n < 0 else "", abs(n)), _F64, _F64)(base)
    finite = z3.And(z3.Not(z3.fpIsNaN(base)), z3.Not(z3.fpIsInf(base)))
    if n > 0:
        ctx.facts.append(z3.Implies(z3.And(finite, z3.fpGEQ(base, z)), z3.fpGEQ(r, z)))   # nonneg finite base -> nonneg
        if n % 2 == 0:
            ctx.facts.append(z3.Implies(finite, z3.fpGEQ(r, z)))                          # even power of a real base -> nonneg
        else:
            ctx.facts.append(z3.Implies(z3.And(finite, z3.fpLEQ(base, z)), z3.fpLEQ(r, z)))   # odd power: nonpos base -> nonpos
        ctx.facts.append(z3.Implies(z3.fpEQ(base, z), z3.fpEQ(r, z)))                     # 0 ** n == 0 (n > 0)
    else:                                                # a negative power can underflow to +/-0, so only the
        ctx.facts.append(z3.Implies(z3.And(finite, z3.fpGT(base, z)), z3.fpGEQ(r, z)))    # nonstrict sign bound holds: positive base -> nonneg
        if n % 2 == 0:
            ctx.facts.append(z3.Implies(z3.And(finite, z3.Not(z3.fpIsZero(base))), z3.fpGEQ(r, z)))   # even power, nonzero base -> nonneg
        else:
            ctx.facts.append(z3.Implies(z3.And(finite, z3.fpLT(base, z)), z3.fpLEQ(r, z)))            # odd power: negative base -> nonpos
    ctx.facts.append(z3.Implies(z3.fpEQ(base, one), z3.fpEQ(r, one)))                 # 1 ** n == 1
    ctx.facts.append(z3.Implies(z3.fpIsNaN(base), z3.fpIsNaN(r)))                     # NaN ** n == NaN
    return r


def _bitwise_overapprox(kind, l, r, ctx):
    """Bitwise & / | / ^ on unbounded integers as a sound over-approximation. Linear integer arithmetic cannot
    encode the exact value (that needs the bitvector engine), so the result is a fresh integer constrained by
    the bounds that hold whenever both operands are nonnegative: 0 <= a & b <= min(a, b), max(a, b) <= a | b <=
    a + b, 0 <= a ^ b <= a + b. A property that follows from the bounds is a sound PROVED; a satisfiable query is
    withheld (REFUTED downgrades to UNKNOWN under an over-approximation). Needs the over-approximation channel
    (ctx.facts); returns None without it (a bitwise op never traps, so trap freedom is unaffected)."""
    if ctx.facts is None:
        return None
    _note_overapprox(ctx, "bitwise %s (unbounded operands)" % kind)
    R = z3.FreshInt("bit" + kind)
    nonneg = z3.And(l >= 0, r >= 0)
    if kind == "and":
        bound = z3.And(R >= 0, R <= l, R <= r)
    elif kind == "or":
        bound = z3.And(R >= l, R >= r, R <= l + r)
    else:                                                    # xor
        bound = z3.And(R >= 0, R <= l + r)
    ctx.facts.append(z3.Implies(nonneg, bound))
    return R


def _bitwise_exact(kind, l, r, width, ctx):
    """Exact bitwise & / | / ^ via fixed-width bitvectors. ctx.bv_signed reads the operands as two's complement
    in [-2^(w-1), 2^(w-1)) and interprets the result signed (so negative operands decide); else unsigned in
    [0, 2^w). The in-range obligation goes to ctx.bv_obligs, discharged from the precondition, transferring the
    bitvector verdict to Python's unbounded integers."""
    signed = getattr(ctx, "bv_signed", False)
    if ctx.bv_obligs is not None:
        if signed:
            half = 1 << (width - 1)
            ctx.bv_obligs.append(z3.Implies(ctx.pc, z3.And(l >= -half, l < half, r >= -half, r < half)))
        else:
            cap = z3.IntVal(1 << width)
            ctx.bv_obligs.append(z3.Implies(ctx.pc, z3.And(l >= 0, l < cap, r >= 0, r < cap)))
    bl, br = z3.Int2BV(l, width), z3.Int2BV(r, width)
    bv = bl & br if kind == "and" else (bl | br if kind == "or" else bl ^ br)
    return z3.BV2Int(bv, is_signed=signed)


def _fp_to_py(mv):
    """A z3 Float64 numeral as the Python float with the same IEEE-754 bits (NaN, +-Inf, signed
    zero, subnormals included), via the bit pattern, or None if it is not a 64-bit FP value."""
    try:
        bits = z3.simplify(z3.fpToIEEEBV(mv))
        if z3.is_bv_value(bits) and bits.size() == 64:
            return struct.unpack(">d", struct.pack(">Q", bits.as_long() & ((1 << 64) - 1)))[0]
    except z3.Z3Exception:
        pass
    return None


def _model_cex(model, z3args, args):
    """Format a counterexample over possibly-typed parameters and return a replayable {name: value}
    dict. Integers, booleans, strings, and floats are extracted as the Python value with matching
    semantics (a float keeps its exact IEEE bits), so a counterexample of any of these types can be
    re-run against CPython, not only an integer one."""
    parts, vals = [], {}
    for a in args:
        if not z3.is_expr(z3args[a]):                            # a container / opaque parameter has no scalar
            continue                                             # model value: skip it rather than crash
        mv = model.eval(z3args[a], model_completion=True)
        parts.append(f"{a}={mv}")
        if z3.is_int_value(mv):
            vals[a] = mv.as_long()
        elif z3.is_true(mv):
            vals[a] = True
        elif z3.is_false(mv):
            vals[a] = False
        elif z3.is_string_value(mv):
            vals[a] = mv.as_string()
        elif z3.is_fp_value(mv):
            f = _fp_to_py(mv)
            if f is not None:
                vals[a] = f
    return ", ".join(parts), vals


_CONTRACT_DECOS = frozenset({"require", "ensure", "pre", "post"})


def _obviously_trapfree(node):
    """True if expression `node` provably raises no modeled trap: a name, a constant, an attribute load, or a
    literal list / tuple / set / dict of such (the right-hand sides a dataclass-style __init__ stores)."""
    if isinstance(node, (ast.Name, ast.Constant)):
        return True
    if isinstance(node, ast.Attribute):
        return _obviously_trapfree(node.value)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return all(_obviously_trapfree(e) for e in node.elts)
    if isinstance(node, ast.Dict):
        return all(k is not None and _obviously_trapfree(k) and _obviously_trapfree(v)
                   for k, v in zip(node.keys, node.values))
    return False


def _init_trapfree(init):
    """True if a class __init__ raises no modeled trap by inspection: its body is only `self.attr = <trap-free>`
    stores, pass, and a docstring (the dataclass / config constructor). A non-trivial __init__ returns False so the
    constructor abstains rather than being wrongly modeled trap free."""
    self_name = init.args.args[0].arg if init.args.args else None
    for s in init.body:
        if isinstance(s, ast.Pass):
            continue
        if isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant):    # a docstring / bare constant
            continue
        if isinstance(s, ast.Assign) and len(s.targets) == 1:
            tgt, val = s.targets[0], s.value
        elif isinstance(s, ast.AnnAssign):
            tgt, val = s.target, s.value
        else:
            return False
        if not (isinstance(tgt, ast.Attribute) and isinstance(tgt.value, ast.Name)
                and tgt.value.id == self_name and (val is None or _obviously_trapfree(val))):
            return False
    return True


def _callee_contract(src):
    """(ensure_node, require_node, formal_names) from a function's @ensure / @require contract decorators (the
    contracts / icontract style: a string condition or a lambda over the formals, and `result` for an ensure),
    conjoined; None if it carries no @ensure. The conditions reference the formals and `result` by name."""
    try:
        fn = _fndef(src)
    except Exception:
        return None
    reqs, enss = [], []
    for d in fn.decorator_list:
        if not (isinstance(d, ast.Call) and d.args):
            continue
        f = d.func
        nm = f.attr if isinstance(f, ast.Attribute) else (f.id if isinstance(f, ast.Name) else None)
        if nm not in _CONTRACT_DECOS:
            continue
        a = d.args[0]
        if isinstance(a, ast.Constant) and isinstance(a.value, str):
            try:
                node = ast.parse(a.value, mode="eval").body
            except SyntaxError:
                continue
        elif isinstance(a, ast.Lambda):
            node = a.body
        else:
            continue
        node = _SpecDesugar().visit(node)                  # `0 <= a <= 1` in a contract, as in a body
        ast.fix_missing_locations(node)
        (reqs if nm in ("require", "pre") else enss).append(node)
    if not enss:
        return None

    def conj(nodes):
        n = nodes[0]
        for m in nodes[1:]:
            n = ast.BoolOp(op=ast.And(), values=[n, m])
        return ast.fix_missing_locations(n)
    return conj(enss), (conj(reqs) if reqs else None), [a.arg for a in fn.args.args]


def _callee_recursive(src, name):
    """Whether function `src` calls `name` (direct self-recursion -- the inliner bails on it)."""
    try:
        fn = _fndef(src)
    except Exception:
        return False
    return any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == name
               for n in ast.walk(fn))


class Ctx:
    """Carries the repo (for interprocedural inlining), memoized summaries, and an
    optional trap sink. When `traps` is a list, every division or modulo emits the
    Z3 condition under which its divisor is zero (guarded by the current path
    condition `pc`), exactly as array indexing emits in-bounds obligations."""
    def __init__(self, repo: Dict[str, str]):
        self.repo = repo
        self._summary: Dict[str, tuple] = {}
        self._contract: Dict[str, tuple] = {}                # name -> (ensure_node, require_node, formals) or None
        self._stack: List[str] = []
        self.traps: Optional[List[z3.ExprRef]] = None
        self.pc: z3.ExprRef = z3.BoolVal(True)
        # division-linearization channel: when `divaux` is a list, floor division a//b is
        # encoded as a fresh quotient q (collected in `divvars`) with the linear side
        # constraints b*q <= a < b*q+b (b>0) etc. appended to `divaux`, so the CHC engine
        # handles division without an uninterpreted div symbol.
        self.divaux: Optional[List[z3.ExprRef]] = None
        self.divvars: List[z3.ExprRef] = []
        # call-summary channel: when `summaries` maps a callee name to its summary
        # relation Sum(args, ret), a call becomes a fresh result var (in `callvars`) with
        # the subgoal Sum(args, r) appended to `callsub`, instead of being inlined.
        self.summaries: Optional[Dict[str, z3.FuncDeclRef]] = None
        self.callsub: Optional[List[z3.ExprRef]] = None
        self.callvars: List[z3.ExprRef] = []
        # over-approximation channel: when `facts` is a list, a transcendental (math.sin/cos/exp/log)
        # is modeled as an uninterpreted function whose value axioms are collected here and conjoined
        # into the query; `overapprox` records that such a function was used, so the engine reports
        # UNKNOWN rather than REFUTED on a satisfiable query (the axioms do not pin the value).
        self.facts: Optional[List[z3.ExprRef]] = None
        self.exact_traps: Optional[List[z3.ExprRef]] = None   # precise first-iteration loop traps (refutable under havoc)
        self.hard_traps: Optional[List[z3.ExprRef]] = None    # exact traps refutable even under the value over-approx
        #                                                       (0 ** negative, when the operands are not themselves over-approximated)
        self.overapprox: bool = False
        self.overapprox_reason: Optional[str] = None          # provenance: the operation and line where the first
        self._cur_line: Optional[int] = None                  # over-approximation was introduced (for the UNKNOWN reason)
        # exact-bitwise channel: when `bv_width` is a width, a bitwise & / | / ^ between variables is encoded
        # exactly through fixed-width bitvectors (Int2BV), and the in-range obligation each one needs to be
        # faithful (both operands nonnegative and below 2^width) is collected in `bv_obligs` for the caller to
        # discharge under the precondition -- so a bounded bitwise claim is decided both ways, not over-approximated.
        self.bv_width: Optional[int] = None
        self.bv_signed: bool = False                          # read the operands as two's-complement signed (negatives)
        self.bv_obligs: Optional[List[z3.ExprRef]] = None
        self.track_trap_lines: bool = False                   # collect the firing-trap line (for a symbolic trap report)
        self.havoc: bool = False                              # set when a loop is over-approximated by havoc
        self.none_havoc: bool = False                         # set when a possibly-None variable is havoc'd to a
        #                                                       fresh int, which would mask a real None-trap, so
        #                                                       a PROVED from that over-approximation is withheld
        self.tracked_dicts: frozenset = frozenset()          # local names modeled as value-engine dicts (per symexec)
        self.readonly_dicts: frozenset = frozenset()         # dict params provably never mutated: d[k] is memoized so
        self.dval_cache: dict = {}                           # re-reading one key gives one value (per symexec run)
        self.mutate_once: frozenset = frozenset()            # container names mutated by exactly one .pop()/.remove()
        self.numeric_params: frozenset = frozenset()         # params annotated int/float/bool: a method on one is
        #                                                      an AttributeError, not an opaque-safe call (per symexec)
        #                  (per symexec): that single mutation's empty/missing trap is modeled against the stable
        #                  length/membership, safe because one mutation in loop-free code runs at most once per path
        self.trapfree_callees: frozenset = frozenset()       # recursive callees verified trap free standalone: the
        #                  inliner cannot unfold them, so a call is modeled as a fresh result with no imported trap
        #                  (the orchestration sets this only after proving each callee trap free, so it is sound)
        self.func_aliases: frozenset = frozenset()           # names the module binds to torch.nn.functional (per symexec)

    def summary(self, name: str):
        if name in self._summary:
            return self._summary[name]
        if name in self.trapfree_callees:
            # a recursive callee the orchestration verified trap free standalone: inline it as a fresh,
            # unconstrained result with no imported trap, so a caller's check proceeds symbolically instead of
            # bailing on the recursion. Sound for trap freedom (the callee adds no trap); the result value is an
            # over-approximation (its range is not modeled), so overapprox is set -- a trap-free use still PROVES,
            # while a trap that rests on the unknown result (a division by it) withholds REFUTED rather than
            # fabricating a non-replayable counterexample.
            self.overapprox = True
            fn = _fndef(self.repo[name])
            formals = [a.arg for a in fn.args.args]
            z3args = {f: z3.FreshInt("rc_" + f) for f in formals}
            s = (formals, z3args, [(z3.BoolVal(True), z3.FreshInt("rcret_" + name))], [], z3.BoolVal(False))
            self._summary[name] = s
            return s
        if name in self._stack:
            raise Unsupported(f"recursion through {name}")
        self._stack.append(name)
        try:
            s = symexec(self.repo[name], self)
        finally:
            self._stack.pop()
        self._summary[name] = s
        return s

    def _contract_for(self, name):
        if name not in self._contract:
            self._contract[name] = (_callee_contract(self.repo[name]) if name in self.repo else None)
        return self._contract[name]

    def _contract_summary(self, name, cc, argvals):
        """Summarize a recursive callee by its @ensure contract instead of unfolding it: a fresh result the
        contract constrains (require(args) -> ensure(args, result)), so a property following from the contract is
        PROVED modularly. The result is not pinned (overapprox), so a REFUTED resting on it is withheld; trap
        freedom is unaffected (a contract callee adds no modeled trap of its own here)."""
        ens, req, formals = cc
        if len(formals) != len(argvals):
            raise Unsupported(f"arity mismatch calling {name}")
        env = dict(zip(formals, argvals))
        r = z3.FreshInt("csum_" + name)
        self.overapprox = True
        if self.facts is not None:
            env2 = dict(env); env2["result"] = r
            post = ev_bool(ens, env2, self)
            self.facts.append(z3.Implies(ev_bool(req, env, self), post) if req is not None else post)
        return r

    def inline(self, name: str, argvals: List[z3.ExprRef]) -> z3.ExprRef:
        if name in self.trapfree_callees:            # a recursive callee verified trap free standalone: a fresh,
            self.overapprox = True                   # arg-independent result with no imported trap. Returned directly
            return z3.FreshInt("rcret_" + name)      # (the args are already trap-checked at the call site); no
        #                                              substitution, whose pairs a container formal cannot satisfy.
        cc = self._contract_for(name)                # a recursive callee the inliner cannot unfold: summarize it by
        if cc is not None and _callee_recursive(self.repo.get(name, ""), name):   # its @ensure contract (modular)
            return self._contract_summary(name, cc, argvals)
        formals, z3args, rets, callee_traps, _none = self.summary(name)
        if len(formals) != len(argvals):
            raise Unsupported(f"arity mismatch calling {name}")
        subs = [(z3args[f], v) for f, v in zip(formals, argvals)]
        if self.traps is not None:
            for t in callee_traps:               # import the callee's traps,
                self.traps.append(z3.And(self.pc, z3.substitute(t, *subs)))
        return _subst(fold(rets), subs)          # _subst lifts over tuple (generator) values


# --------------------------------------------------------------------------- #
# Standard-library contracts. A registry of trusted models for pure library functions,    #
# each a Z3 term over the evaluated arguments. Calls of the form `math.fabs(x)` (module     #
# attribute) and the imported bare name dispatch here. Entries must be exact or a sound     #
# over-approximation; the registry is extensible by adding entries.                         #
# --------------------------------------------------------------------------- #
def _b01(b):
    return z3.If(b, z3.IntVal(1), z3.IntVal(0))              # a Bool predicate as Python's 0/1


_STDLIB = {
    "math.fabs": lambda a: z3.fpAbs(_to_fp(a[0])),
    "math.copysign": lambda a: z3.If(z3.fpIsNegative(_to_fp(a[1])),
                                     z3.fpNeg(z3.fpAbs(_to_fp(a[0]))), z3.fpAbs(_to_fp(a[0]))),
    "math.isnan": lambda a: _b01(z3.fpIsNaN(_to_fp(a[0]))),
    "math.isinf": lambda a: _b01(z3.fpIsInf(_to_fp(a[0]))),
    "math.isfinite": lambda a: _b01(z3.And(z3.Not(z3.fpIsNaN(_to_fp(a[0]))), z3.Not(z3.fpIsInf(_to_fp(a[0]))))),
}
# the imported bare name (`from math import fabs`) resolves to the same model
for _qn in list(_STDLIB):
    _STDLIB.setdefault(_qn.split(".")[-1], _STDLIB[_qn])


# numpy scalar functions: the same value contracts as the math models, plus numpy's own, so code calling
# np.sqrt(x), np.abs(x), np.sign(x), ... on a scalar verifies instead of abstaining. numpy returns NaN on a
# domain error rather than raising, so these are total (no trap). Registered under both the numpy. and np.
# qualified names (the near-universal `import numpy as np`); an array argument falls back to UNKNOWN because
# _to_fp declines an opaque value, and the type-aware models keep an integer argument integral.
def _np_abs(a):
    x = a[0]
    return z3.If(x < 0, -x, x) if z3.is_int(x) else z3.fpAbs(_to_fp(x))


def _np_square(a):
    x = a[0]
    return x * x if z3.is_int(x) else z3.fpMul(_RM, _to_fp(x), _to_fp(x))


def _np_sign(a):
    x = a[0]
    if z3.is_int(x):
        return z3.If(x < 0, z3.IntVal(-1), z3.If(x > 0, z3.IntVal(1), z3.IntVal(0)))
    f, zero = _to_fp(x), z3.FPVal(0.0, _F64)
    return z3.If(z3.fpIsNaN(f), f, z3.If(z3.fpLT(f, zero), z3.FPVal(-1.0, _F64),
                                         z3.If(z3.fpGT(f, zero), z3.FPVal(1.0, _F64), zero)))


_NUMPY = {
    "fabs": lambda a: z3.fpAbs(_to_fp(a[0])),
    "absolute": _np_abs,
    "abs": _np_abs,
    "copysign": _STDLIB["math.copysign"],
    "isnan": _STDLIB["math.isnan"],
    "isinf": _STDLIB["math.isinf"],
    "isfinite": _STDLIB["math.isfinite"],
    "sqrt": lambda a: z3.fpSqrt(_RM, _to_fp(a[0])),         # NaN for x < 0 (no trap), unlike math.sqrt
    "square": _np_square,
    "sign": _np_sign,
}
for _fn, _model in _NUMPY.items():
    _STDLIB["numpy." + _fn] = _model
    _STDLIB["np." + _fn] = _model


# numpy 1-D array constructors, modeled as sized sequences (a sound over-approximation, handled in ev where
# the trap channel is available -- not in _STDLIB, whose models take no ctx).
_NP_ARRAY_CTORS = frozenset({"zeros", "ones", "empty", "full", "arange", "array"})


def _np_array_ctor(name, node, env, ctx):
    """A numpy 1-D array constructor as a _SafeContainer whose length is the array's shape[0]: len(), indexing
    (IndexError outside [-n, n)), iteration, and an empty-reduction trap are then checked exactly as for any
    sequence, while numpy-specific operations on the result (elementwise arithmetic, .shape, .sum) stay opaque
    and come back UNKNOWN. zeros/ones/empty/full(n) raise ValueError for a negative n (emitted as a trap);
    arange yields an empty array for a nonpositive count (no trap). A non-scalar shape (a tuple: 2-D+), a
    float/opaque size, the 3-argument arange, or an unmodeled np.array argument abstains -- Unsupported
    (UNKNOWN), or an opaque array under best-effort -- so nothing numpy could trap on is assumed safe."""
    args = [ev(a, env, ctx) for a in node.args]               # trap-check every positional argument
    for kw in node.keywords:                                  # and keyword arguments (dtype=..., etc.)
        ev(kw.value, env, ctx)

    def _abstain():
        if BEST_EFFORT:
            _best_effort_assume()                             # the numpy construction is assumed safe (tainted)
            return _Opaque("besteffort")
        raise Unsupported(f"unmodeled numpy.{name} shape at line {getattr(node, 'lineno', '?')}")

    if name == "array":
        a0 = node.args[0] if node.args else None
        if isinstance(a0, (ast.List, ast.Tuple)) and not any(isinstance(e, ast.Starred) for e in a0.elts):
            shp = _nested_list_shape(a0)
            if shp is not None and len(shp) > 1:
                return _NdArray(tuple(z3.IntVal(d) for d in shp))                  # array([[..], [..]]) -> an N-d ndarray
            return _NdArray((z3.IntVal(len(a0.elts)),))                            # array([...]) -> a 1-D ndarray
        if args and isinstance(args[0], _SafeContainer) and not args[0].unindexable:
            return _NdArray((_container_len(args[0], ctx),))                       # array(seq) -> a 1-D ndarray of seq's length
        return _abstain()

    if name == "arange":
        if not args or len(args) > 2 or any(not (z3.is_expr(x) and z3.is_int(x)) for x in args):
            return _abstain()                                 # float range, 3-arg step, or opaque -> abstain
        n = args[0] if len(args) == 1 else args[1] - args[0]
        return _NdArray((z3.If(n < 0, z3.IntVal(0), n),))     # a 1-D ndarray, empty for a nonpositive count

    if args and isinstance(args[0], tuple):                   # zeros / ones / empty / full((m, n, ...)): an N-d ndarray
        dims = list(args[0])
        if all(z3.is_expr(d) and z3.is_int(d) for d in dims):
            if ctx.traps is not None:
                for d in dims:
                    ctx.traps.append(z3.And(ctx.pc, d < 0))   # ValueError: negative dimensions are not allowed
            return _NdArray(tuple(z3.If(d < 0, z3.IntVal(0), d) for d in dims))
        return _abstain()                                     # a float / opaque dimension in the shape tuple
    if not args or not (z3.is_expr(args[0]) and z3.is_int(args[0])):   # zeros / ones / empty / full: arg 0 is shape
        return _abstain()                                     # a float or an opaque size
    n = args[0]
    if ctx.traps is not None:
        ctx.traps.append(z3.And(ctx.pc, n < 0))               # ValueError: negative dimensions are not allowed
    return _NdArray((z3.If(n < 0, z3.IntVal(0), n),))         # a 1-D ndarray


def _nd_size(shape):
    """The product of an ndarray's dimension terms (its element count); 1 for a 0-d array."""
    s = z3.IntVal(1)
    for d in shape:
        s = s * d
    return s


def _nested_list_shape(node):
    """The shape of a (possibly nested) list/tuple literal of uniform sublists, as a tuple of ints, or None when
    it is ragged, not a list literal, or contains a starred element (so the array's shape is not statically a
    regular grid)."""
    if not isinstance(node, (ast.List, ast.Tuple)) or any(isinstance(e, ast.Starred) for e in node.elts):
        return None
    n = len(node.elts)
    if n == 0:
        return (0,)
    subs = [_nested_list_shape(e) for e in node.elts]
    if all(s is None for s in subs):
        return (n,)                                           # a flat row of scalars
    if subs[0] is not None and all(s == subs[0] for s in subs):
        return (n,) + subs[0]                                 # uniform sublists: prepend this dimension
    return None                                               # ragged: not a regular ndarray


def _nd_binop(l, r, ctx):
    """Element-wise arithmetic on a numpy ndarray: ndarray OP scalar keeps the ndarray's shape; ndarray OP
    ndarray broadcasts (each dimension pair, aligned from the right, must be equal or one must be 1, else a
    ValueError). Element values are opaque, so only the shape (and the broadcast trap) is tracked. An ndarray
    with a non-scalar, non-ndarray operand is left unmodeled (Unsupported)."""
    cls = _Column if (isinstance(l, _Column) or isinstance(r, _Column)) else _NdArray   # a pandas column stays a column
    if isinstance(l, _NdArray) and isinstance(r, _NdArray):
        sl, sr = l.shape, r.shape
        out, ok = [], z3.BoolVal(True)
        for k in range(1, max(len(sl), len(sr)) + 1):
            dl = sl[-k] if k <= len(sl) else z3.IntVal(1)
            dr = sr[-k] if k <= len(sr) else z3.IntVal(1)
            ok = z3.And(ok, z3.Or(dl == dr, dl == 1, dr == 1))
            out.append(z3.If(dl == 1, dr, dl))
        if ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, z3.Not(ok)))     # operands could not be broadcast together: ValueError
        return cls(tuple(reversed(out)))
    nd = l if isinstance(l, _NdArray) else r
    other = r if isinstance(l, _NdArray) else l
    if z3.is_expr(other) and (z3.is_int(other) or z3.is_bool(other) or _is_fp(other)):
        return cls(nd.shape)                                 # ndarray / column OP scalar: same shape, opaque elements
    raise Unsupported("ndarray operation with a non-scalar operand")


def _broadcast_shapes(shapes):
    """Broadcast a list of dimension tuples (right-aligned, each pair equal or one of them 1), returning
    (out_shape_tuple, ok_bool): ok holds when every aligned pair is broadcastable."""
    out, ok = [], z3.BoolVal(True)
    rank = max((len(s) for s in shapes), default=0)
    for k in range(1, rank + 1):
        dim = z3.IntVal(1)
        for s in shapes:
            d = s[-k] if k <= len(s) else z3.IntVal(1)
            ok = z3.And(ok, z3.Or(d == dim, d == 1, dim == 1))
            dim = z3.If(dim == 1, d, dim)
        out.append(dim)
    return tuple(reversed(out)), ok


def _matmul(l, r, ctx):
    """Matrix multiply (@ / matmul / mm / bmm / dot / mv) as shape algebra with an inner-dimension-mismatch
    trap; 1-D @ 1-D is a scalar, the batched N-D form broadcasts the leading axes. Elements stay opaque."""
    if not (isinstance(l, _NdArray) and isinstance(r, _NdArray)):
        raise Unsupported("matrix multiply with a non-tensor operand")
    sl, sr = l.shape, r.shape
    if not sl or not sr:                                      # a 0-d operand is a RuntimeError
        if ctx.traps is not None:
            ctx.traps.append(ctx.pc)
        return _Opaque("matmul")
    cls = _Column if (isinstance(l, _Column) or isinstance(r, _Column)) else _NdArray
    if len(sl) == 1 and len(sr) == 1:                        # dot product -> scalar
        if ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, sl[0] != sr[0]))
        return _Opaque("matmul")
    if len(sl) == 1:                                         # (k) @ (..., k, n) -> (..., n)
        ok, out = sl[0] == sr[-2], sr[:-2] + (sr[-1],)
    elif len(sr) == 1:                                       # (..., m, k) @ (k) -> (..., m)
        ok, out = sl[-1] == sr[0], sl[:-2] + (sl[-2],)
    else:                                                    # (..., m, k) @ (..., k, n) -> (broadcast..., m, n)
        batch, bok = _broadcast_shapes([sl[:-2], sr[:-2]])
        ok, out = z3.And(sl[-1] == sr[-2], bok), batch + (sl[-2], sr[-1])
    if ctx.traps is not None:
        ctx.traps.append(z3.And(ctx.pc, z3.Not(ok)))
    return cls(out) if out else _Opaque("matmul")


def _cat_shape(tensors, dim, ctx):
    """Concatenate tensors along `dim`: the rank and every non-`dim` axis must match (a mismatch traps); the
    result's `dim` axis is their sum. A non-tensor element or out-of-range axis leaves the result opaque."""
    nds = [t for t in tensors if isinstance(t, _NdArray)]
    if not nds or len(nds) != len(tensors) or len({len(t.shape) for t in nds}) != 1:
        if ctx.traps is not None and nds and len({len(t.shape) for t in nds}) != 1:
            ctx.traps.append(ctx.pc)                          # tensors of different rank
        return _Opaque("cat")
    rank = len(nds[0].shape)
    d = dim if dim >= 0 else rank + dim
    if not (0 <= d < rank):
        if ctx.traps is not None:
            ctx.traps.append(ctx.pc)
        return _Opaque("cat")
    base, total = nds[0].shape, nds[0].shape[d]
    for t in nds[1:]:
        if ctx.traps is not None:
            for k in range(rank):
                if k != d:
                    ctx.traps.append(z3.And(ctx.pc, base[k] != t.shape[k]))   # a mismatched non-cat axis
        total = total + t.shape[d]
    return _NdArray(base[:d] + (total,) + base[d + 1:])


def _stack_shape(tensors, dim, ctx):
    """Stack equal-shaped tensors: insert a new axis of size len(tensors) at `dim` (a shape mismatch traps)."""
    nds = [t for t in tensors if isinstance(t, _NdArray)]
    if not nds or len(nds) != len(tensors):
        return _Opaque("stack")
    s0 = nds[0].shape
    if ctx.traps is not None:
        for t in nds[1:]:
            if len(t.shape) != len(s0):
                ctx.traps.append(ctx.pc)
            else:
                for x, y in zip(s0, t.shape):
                    ctx.traps.append(z3.And(ctx.pc, x != y))
    rank = len(s0)
    d = dim if dim >= 0 else rank + 1 + dim
    d = max(0, min(d, rank))
    return _NdArray(s0[:d] + (z3.IntVal(len(nds)),) + s0[d:])


def _nd_method(arr, meth, a, node, env, ctx):
    """A numpy ndarray / torch tensor method: reshape / view (total-size-mismatch ValueError), the axis
    reductions sum / mean / min / max / prod / std / var / argmin / argmax (axis=None -> an opaque scalar, a
    constant axis -> the shape without that axis; a min / max / argmin / argmax of a zero-size array is a
    ValueError), ravel / flatten / transpose / t, and the shape-preserving copy / astype / to / detach / float.
    Returns the modeled value, or None for a method not modeled here (the caller's opaque-safe path applies)."""
    for kw in node.keywords:                                 # trap-check keyword arguments once (a modeled branch
        ev(kw.value, env, ctx)                               # returns before the caller's own keyword check runs)
    if meth in ("reshape", "view"):
        raw = list(a[0]) if (len(a) == 1 and isinstance(a[0], tuple)) else a
        if not raw or not all(z3.is_expr(d) and (z3.is_int(d) or z3.is_bool(d)) for d in raw):
            raise Unsupported("reshape with a non-integer dimension")
        dims = [z3.simplify(_as_int(d)) for d in raw]         # fold -1 (a unary minus) to a literal for the infer check
        infer = any(z3.is_int_value(d) and d.as_long() == -1 for d in dims)
        if not infer and ctx.traps is not None:
            prod = z3.IntVal(1)
            for d in dims:
                prod = prod * d
            ctx.traps.append(z3.And(ctx.pc, prod != _nd_size(arr.shape)))   # cannot reshape: total size mismatch
        new = tuple(z3.FreshInt("rs") if (z3.is_int_value(d) and d.as_long() == -1) else d for d in dims)
        return _NdArray(new) if new else z3.FreshInt("ndelem")
    if meth == "size":                                       # torch t.size(): the shape; t.size(k): dimension k
        if a and z3.is_expr(a[0]) and z3.is_int_value(a[0]):
            k = a[0].as_long()
            kk = k if k >= 0 else len(arr.shape) + k
            if 0 <= kk < len(arr.shape):
                return arr.shape[kk]
            if ctx.traps is not None:
                ctx.traps.append(ctx.pc)                      # IndexError: dimension out of range
            return z3.FreshInt("ndsize")
        return arr.shape
    if meth == "dim":
        return z3.IntVal(len(arr.shape))
    if meth == "numel":
        return _nd_size(arr.shape)
    if meth == "item":                                       # .item() requires exactly one element, else ValueError
        if ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, _nd_size(arr.shape) != 1))
        return _Opaque("nditem")
    if meth in ("sum", "mean", "min", "max", "prod", "std", "var", "argmin", "argmax", "amin", "amax",
                "median", "nanmean", "nansum", "all", "any", "count_nonzero", "logsumexp", "norm"):
        if meth in ("min", "max", "amin", "amax", "argmin", "argmax", "median") and ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, _nd_size(arr.shape) == 0))      # ValueError: zero-size reduction
        keepdim = any(k.arg in ("keepdim", "keepdims") and isinstance(k.value, ast.Constant)
                      and bool(k.value.value) for k in node.keywords)
        cand = a[0] if a else next((ev(k.value, env, ctx) for k in node.keywords
                                    if k.arg in ("axis", "dim")), None)
        axes = None
        if isinstance(cand, tuple):                          # a tuple of axes: reduce each
            ix = [v.as_long() for v in cand if z3.is_expr(v) and z3.is_int_value(v)]
            axes = ix if len(ix) == len(cand) else None
        elif z3.is_expr(cand) and z3.is_int_value(cand):
            axes = [cand.as_long()]
        if meth in ("all", "any") and axes is None:
            return z3.FreshConst(z3.BoolSort(), "ndall")     # a.all() / a.any() with no axis: a scalar bool
        if axes is None:
            return _Opaque("ndreduce")                       # full reduction: an opaque scalar
        norm = [(x if x >= 0 else len(arr.shape) + x) for x in axes]
        if any(not (0 <= x < len(arr.shape)) for x in norm):
            if ctx.traps is not None:
                ctx.traps.append(ctx.pc)                      # axis out of range: AxisError (a ValueError subclass)
            return _Opaque("ndreduce")
        rest = (tuple(z3.IntVal(1) if k in norm else d for k, d in enumerate(arr.shape)) if keepdim
                else tuple(d for k, d in enumerate(arr.shape) if k not in norm))
        if meth in ("all", "any"):
            return _NdArray(rest) if rest else z3.FreshConst(z3.BoolSort(), "ndall")
        return _NdArray(rest) if rest else _Opaque("ndreduce")
    if meth in ("ravel", "flatten"):
        return _NdArray((_nd_size(arr.shape),)) if not a else _Opaque("flatten")   # full flatten -> 1-D; partial -> opaque
    if meth == "unsqueeze" and a and z3.is_expr(a[0]) and z3.is_int_value(a[0]):
        d, rank = a[0].as_long(), len(arr.shape)
        dd = max(0, min(d if d >= 0 else rank + 1 + d, rank))
        return _NdArray(arr.shape[:dd] + (z3.IntVal(1),) + arr.shape[dd:])         # insert a size-1 axis
    if meth in ("permute", "movedim", "swapaxes") or (meth == "transpose" and a):
        dims = list(a[0]) if (len(a) == 1 and isinstance(a[0], tuple)) else a
        ix = [d.as_long() for d in dims if z3.is_expr(d) and z3.is_int_value(d)]
        rank = len(arr.shape)
        if meth == "permute" and len(ix) == rank and sorted(i % rank for i in ix if rank) == list(range(rank)):
            return _NdArray(tuple(arr.shape[i % rank] for i in ix))               # reorder axes
        if meth in ("swapaxes", "transpose", "movedim") and len(ix) == 2 and rank:
            sh = list(arr.shape); i, j = ix[0] % rank, ix[1] % rank; sh[i], sh[j] = sh[j], sh[i]
            return _NdArray(tuple(sh))                                            # swap two axes
        return _Opaque("permute")                                                # non-constant axes: opaque, trap-free
    if meth in ("expand", "broadcast_to", "expand_as", "reshape_as", "view_as"):
        if meth in ("expand_as", "reshape_as", "view_as"):
            return _NdArray(a[0].shape) if (a and isinstance(a[0], _NdArray)) else _Opaque("expand")
        dims = list(a[0]) if (len(a) == 1 and isinstance(a[0], tuple)) else a
        if dims and all(z3.is_expr(d) and z3.is_int(d) for d in dims):
            return _NdArray(tuple(arr.shape[k] if (z3.is_int_value(d) and d.as_long() == -1) else d
                                  for k, d in enumerate(dims)))                   # a -1 keeps the original axis
        return _Opaque("expand")
    if meth in ("repeat", "tile", "repeat_interleave"):
        reps = list(a[0]) if (len(a) == 1 and isinstance(a[0], tuple)) else a
        if meth != "repeat_interleave" and reps and all(z3.is_expr(r) and z3.is_int(r) for r in reps) \
                and len(reps) >= len(arr.shape):
            pad = [z3.IntVal(1)] * (len(reps) - len(arr.shape)) + list(arr.shape)
            return _NdArray(tuple(p * r for p, r in zip(pad, reps)))             # each axis repeated reps[k] times
        return _Opaque("repeat")
    if meth == "narrow" and len(a) == 3 and z3.is_expr(a[0]) and z3.is_int_value(a[0]) and len(arr.shape):
        dd = a[0].as_long() % len(arr.shape)
        return _NdArray(arr.shape[:dd] + (a[2],) + arr.shape[dd + 1:])           # axis dd shrinks to the given length
    if meth == "select" and len(a) == 2 and z3.is_expr(a[0]) and z3.is_int_value(a[0]) and len(arr.shape):
        dd = a[0].as_long() % len(arr.shape)
        rest = arr.shape[:dd] + arr.shape[dd + 1:]
        return _NdArray(rest) if rest else _Opaque("select")                     # drop an axis
    if meth in ("matmul", "mm", "bmm", "mv", "dot") and a and isinstance(a[0], _NdArray):
        return _matmul(arr, a[0], ctx)
    if meth in ("scatter", "scatter_add", "scatter_reduce", "masked_scatter", "index_put", "index_add",
                "index_copy", "index_fill"):
        return _NdArray(arr.shape)                            # writes into a copy of self: the same shape
    if meth == "gather" and len(a) >= 2 and isinstance(a[1], _NdArray):
        return _NdArray(a[1].shape)                           # gather: the result takes the index tensor's shape
    if meth == "index_select" and len(a) == 2 and z3.is_expr(a[0]) and z3.is_int_value(a[0]) \
            and isinstance(a[1], _NdArray) and a[1].shape and arr.shape:
        dd = a[0].as_long() % len(arr.shape)
        return _NdArray(arr.shape[:dd] + (a[1].shape[0],) + arr.shape[dd + 1:])    # axis dd shrinks to len(index)
    if meth in ("squeeze", "unique", "nonzero", "masked_select", "gather", "take", "bincount", "topk",
                "kthvalue", "sort", "mode", "unbind", "split", "chunk", "tensor_split", "tolist", "data_ptr",
                "rot90", "diag", "diagonal", "trace", "outer", "kron", "cross", "einsum", "histc"):
        return _Opaque(meth)                                 # data-dependent / rank-changing / tuple: trap-free, shape opaque
    if meth == "numpy":
        return _NdArray(arr.shape)                            # .numpy(): the same shape, an ndarray view
    if meth in ("cumsum", "cumprod", "logcumsumexp", "softmax", "log_softmax", "sigmoid", "relu", "tanh",
                "abs", "exp", "log", "log2", "log10", "sqrt", "rsqrt", "neg", "sign", "clamp", "clip",
                "clamp_min", "clamp_max", "nan_to_num", "masked_fill", "flip", "roll", "round", "floor",
                "ceil", "frac", "reciprocal", "pow", "tril", "triu", "sin", "cos", "tan", "gelu", "silu",
                "elu", "softplus", "erf", "isnan", "isinf", "isfinite", "logical_not", "argsort", "to_sparse",
                "to_dense", "to_sparse_csr", "coalesce", "dequantize", "conj", "resolve_conj", "conj_physical",
                "angle", "sgn"):
        return _NdArray(arr.shape)                            # element-wise / shape-preserving / storage cast, opaque elements
    if meth in ("backward", "retain_grad", "zero_grad", "register_hook"):
        return _NoneVal()                                    # an autograd side-effect: returns None
    if meth in ("bool", "int", "half", "short", "char", "byte", "type_as", "fix", "as_subclass"):
        return _NdArray(arr.shape)                            # dtype conversion: same shape
    if meth in ("transpose", "t"):
        return _NdArray(tuple(reversed(arr.shape)))           # no-argument transpose: reverse every axis
    if meth in ("copy", "astype", "to", "detach", "cpu", "cuda", "float", "double", "long", "contiguous",
                "clone", "requires_grad_") or meth.endswith("_"):
        return _NdArray(arr.shape)                            # shape-preserving (incl. an in-place op): returns self
    return None                                              # another method: the caller's opaque-safe path applies


def _nd_store_traps(base, slc, env, ctx):
    """Emit the IndexError traps for storing into an ndarray / tensor at index `slc`, bounds-checking each axis
    exactly as a read does, so an out-of-bounds a[i] = v REFUTES rather than being falsely proved. A slice store
    is clamped (no trap); a pandas Series label store s[i] = v is left unmodeled (use .iloc)."""
    if isinstance(base, _Column) and not isinstance(slc, ast.Slice):
        ev(slc, env, ctx)
        raise Unsupported("pandas Series label store s[i] = v is not modeled (use .iloc)")
    if isinstance(slc, ast.Slice):
        for b in (slc.lower, slc.upper, slc.step):
            if b is not None:
                ev(b, env, ctx)
        return
    idxs = list(slc.elts) if isinstance(slc, ast.Tuple) else [slc]
    if any(isinstance(ix, ast.Slice) for ix in idxs):
        raise Unsupported("ndarray mixed slice store is not modeled")
    if len(idxs) > len(base.shape):
        if ctx.traps is not None:
            ctx.traps.append(ctx.pc)                          # too many indices for the rank: IndexError
        return
    for k, ix in enumerate(idxs):
        iv = ev(ix, env, ctx)
        if not (z3.is_expr(iv) and iv.sort() == z3.IntSort()):
            raise Unsupported("ndarray store index is not an integer")
        if ctx.traps is not None:
            nk = base.shape[k]
            ctx.traps.append(z3.And(ctx.pc, z3.Or(iv < -nk, iv >= nk)))   # IndexError on axis k


# torch tensor constructors, reused through the numpy ndarray (_NdArray) shape model.
_TORCH_CTORS = frozenset({"zeros", "ones", "empty", "full", "rand", "randn", "tensor", "arange",
                          "zeros_like", "ones_like", "empty_like", "rand_like", "randn_like", "eye"})


def _torch_tensor_ctor(name, node, env, ctx):
    """A torch tensor constructor as a shape-aware _NdArray (the same model as numpy): zeros / ones / empty /
    rand / randn take the shape as separate dimensions or one tuple/list, full a (shape, fill), tensor a nested
    list, arange a count, eye a square/rectangular shape, and *_like the source tensor's shape. A negative
    dimension is the RuntimeError torch raises (a modeled trap). Element values stay opaque. Returns None for an
    unmodeled signature, so the caller abstains (UNKNOWN) rather than guessing."""
    args = [ev(a, env, ctx) for a in node.args]               # each argument trap-checked as it is evaluated
    for kw in node.keywords:
        ev(kw.value, env, ctx)

    def _shaped(dims):
        if not dims or not all(z3.is_expr(d) and z3.is_int(d) for d in dims):
            return None
        if ctx.traps is not None:
            for d in dims:
                ctx.traps.append(z3.And(ctx.pc, d < 0))       # RuntimeError: a negative dimension
        return _NdArray(tuple(z3.If(d < 0, z3.IntVal(0), d) for d in dims))

    if name in ("zeros_like", "ones_like", "empty_like", "rand_like", "randn_like"):
        return _NdArray(args[0].shape) if (args and isinstance(args[0], _NdArray)) else None
    if name == "tensor":
        a0 = node.args[0] if node.args else None
        shp = _nested_list_shape(a0) if isinstance(a0, (ast.List, ast.Tuple)) else None
        if shp is None:
            return None
        return _NdArray(tuple(z3.IntVal(d) for d in shp)) if len(shp) > 1 else _NdArray((z3.IntVal(shp[0]),))
    if name == "arange":
        if not args or len(args) > 2 or any(not (z3.is_expr(x) and z3.is_int(x)) for x in args):
            return None
        n = args[0] if len(args) == 1 else args[1] - args[0]
        return _NdArray((z3.If(n < 0, z3.IntVal(0), n),))
    if name == "eye":
        ints = [a for a in args if z3.is_expr(a) and z3.is_int(a)]
        if not ints:
            return None
        nrow, ncol = ints[0], (ints[1] if len(ints) > 1 else ints[0])
        if ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, z3.Or(nrow < 0, ncol < 0)))   # RuntimeError: a negative dimension
        return _NdArray((z3.If(nrow < 0, z3.IntVal(0), nrow), z3.If(ncol < 0, z3.IntVal(0), ncol)))
    if name == "full":
        return _shaped(list(args[0])) if (args and isinstance(args[0], tuple)) else None
    dims = list(args[0]) if (len(args) == 1 and isinstance(args[0], tuple)) else args   # separate dims or one tuple/list
    return _shaped(dims)


# torch / numpy module-level tensor functions, modeled through the _NdArray shape algebra.
_TORCH_FUNCS = frozenset({
    "cat", "concat", "concatenate", "stack", "hstack", "vstack", "dstack", "column_stack", "row_stack",
    "matmul", "mm", "bmm", "mv", "dot", "inner", "outer", "tensordot", "einsum", "where", "kron", "cross",
    "transpose", "permute", "movedim", "swapaxes", "squeeze", "unsqueeze", "flatten", "ravel", "reshape",
    "flip", "roll", "rot90", "narrow", "select", "gather", "scatter", "scatter_add", "index_select",
    "masked_select", "take", "split", "chunk", "unbind", "tensor_split", "sort", "argsort", "topk",
    "kthvalue", "unique", "nonzero", "bincount", "cumsum", "cumprod", "logcumsumexp", "sum", "mean", "min",
    "max", "prod", "std", "var", "argmin", "argmax", "amin", "amax", "median", "norm", "all", "any",
    "count_nonzero", "logsumexp", "sigmoid", "relu", "tanh", "softmax", "log_softmax", "abs", "exp", "log",
    "sqrt", "neg", "sign", "clamp", "clip", "nan_to_num", "masked_fill", "round", "floor", "ceil",
    "reciprocal", "pow", "tril", "triu", "sin", "cos", "tan", "isnan", "isinf", "isfinite", "meshgrid",
    "one_hot", "diag", "diagonal", "trace", "repeat_interleave", "tile", "broadcast_to",
})


def _torch_func(name, node, env, ctx):
    """A torch / numpy module-level tensor function M.f(...): cat / stack combine a sequence, the matmul family
    the shape algebra, where broadcasts, and a tensor-first function reuses _nd_method. None for a scalar arg."""
    if name in ("cat", "concat", "concatenate", "stack", "hstack", "vstack", "dstack",
                "column_stack", "row_stack"):
        seq = ev(node.args[0], env, ctx) if node.args else None
        for nd in node.args[1:]:
            ev(nd, env, ctx)
        for kw in node.keywords:
            ev(kw.value, env, ctx)
        if not isinstance(seq, tuple):
            return _Opaque("cat")                            # a non-literal tensor sequence: opaque, trap-free
        dim = 0
        if len(node.args) >= 2 and z3.is_expr(s := ev(node.args[1], env, ctx)) and z3.is_int_value(s):
            dim = s.as_long()
        else:
            kv = next((ev(k.value, env, ctx) for k in node.keywords if k.arg in ("dim", "axis")), None)
            if z3.is_expr(kv) and z3.is_int_value(kv):
                dim = kv.as_long()
        if name in ("cat", "concat", "concatenate"):
            return _cat_shape(list(seq), dim, ctx)
        if name == "stack":
            return _stack_shape(list(seq), dim, ctx)
        return _Opaque("stack")                              # hstack / vstack / dstack / column_stack: shape opaque
    args = [ev(a, env, ctx) for a in node.args]
    for kw in node.keywords:
        ev(kw.value, env, ctx)
    if name in ("matmul", "mm", "bmm", "mv", "dot", "inner") and len(args) >= 2 \
            and isinstance(args[0], _NdArray) and isinstance(args[1], _NdArray):
        return _matmul(args[0], args[1], ctx)
    if name == "outer" and len(args) >= 2 and isinstance(args[0], _NdArray) and isinstance(args[1], _NdArray):
        if args[0].shape and args[1].shape:
            return _NdArray((args[0].shape[0], args[1].shape[0]))
        return _Opaque("outer")
    if name == "where" and len(args) == 3 and any(isinstance(x, _NdArray) for x in args):
        out, ok = _broadcast_shapes([x.shape for x in args if isinstance(x, _NdArray)])
        if ctx.traps is not None:
            ctx.traps.append(z3.And(ctx.pc, z3.Not(ok)))     # non-broadcastable operands
        return _NdArray(out) if out else _Opaque("where")
    if name in ("meshgrid", "one_hot", "tensordot", "einsum", "kron", "cross", "diag", "diagonal", "trace"):
        return _Opaque(name)                                 # data-dependent shape: trap-free, opaque
    if args and isinstance(args[0], _NdArray):               # a tensor-first function reuses the method model
        return _nd_method(args[0], name, args[1:], node, env, ctx)
    if name in _NN_ACTIVATION_TRAPFREE:                       # an activation on a shape-untracked tensor: trap free
        return _Opaque(name)
    return None


# torch.nn.functional layers that preserve the input shape (elementwise activations and normalization). The
# shape-changing layers (linear, conv, embedding, pooling) and the losses are opaque, value-independent.
_F_SHAPE_PRESERVING = frozenset({
    "relu", "relu6", "gelu", "elu", "selu", "celu", "leaky_relu", "rrelu", "hardtanh", "hardswish",
    "hardsigmoid", "hardshrink", "softshrink", "tanhshrink", "mish", "sigmoid", "tanh", "logsigmoid",
    "softplus", "softsign", "threshold", "prelu", "silu", "softmax", "log_softmax", "softmin", "gumbel_softmax",
    "dropout", "dropout1d", "dropout2d", "dropout3d", "alpha_dropout", "feature_alpha_dropout", "layer_norm",
    "batch_norm", "group_norm", "instance_norm", "local_response_norm", "normalize", "rms_norm",
})

# torch.nn activations taking no axis/shape argument: never raise on a tensor, so torch.relu(x) / F.gelu(x) on a
# bare (shape-untracked) tensor param is trap free. Unary-math names (abs/sqrt/exp/sin) are excluded -- they resolve
# through the scalar np.abs / math.* model, which a trap-free opaque would shadow (losing np.abs(x) >= 0).
_NN_ACTIVATION_TRAPFREE = frozenset({
    "relu", "relu6", "gelu", "silu", "elu", "selu", "celu", "leaky_relu", "rrelu", "hardtanh", "hardswish",
    "hardsigmoid", "hardshrink", "softshrink", "tanhshrink", "mish", "logsigmoid", "softplus", "softsign",
    "prelu", "threshold", "sigmoid", "dropout", "alpha_dropout",
})

# statistics reducers whose only trap is too-few data points (StatisticsError). geometric_mean / harmonic_mean
# (value-domain traps) and median_grouped (interval params) are excluded -- they stay UNKNOWN.
_STATISTICS_REDUCERS = frozenset({
    "mean", "fmean", "median", "median_low", "median_high", "mode", "stdev", "variance", "pstdev", "pvariance",
})


def _functional_call(name, node, env, ctx):
    """A `torch.nn.functional.X(tensor, ...)` call: an elementwise activation or normalization preserves the
    input shape, a shape-changing layer (linear, conv, embedding, pooling) or a loss is opaque. None for a
    non-tensor first argument so the caller falls through to the unmodeled-call path."""
    args = [ev(a, env, ctx) for a in node.args]
    for kw in node.keywords:
        ev(kw.value, env, ctx)
    if not (args and isinstance(args[0], _NdArray)):
        if name in _NN_ACTIVATION_TRAPFREE:                  # F.relu(x) / F.gelu(x) on a bare tensor param: trap free
            return _Opaque(name)
        return None
    if name in _F_SHAPE_PRESERVING:
        return _NdArray(args[0].shape)
    return _Opaque("functional")                             # a shape-changing layer or a loss: trap-free, opaque


def _functional_aliases(module):
    """The names a module binds to `torch.nn.functional` -- `import torch.nn.functional as F`, `from torch.nn
    import functional as F` -- so an `F.relu(t)` call is dispatched soundly only where the import establishes it.
    A bare `import torch.nn.functional` (no alias) is reached through the full dotted path instead."""
    out = set()
    for n in ast.walk(module):
        if isinstance(n, ast.Import):
            for al in n.names:
                if al.name == "torch.nn.functional" and al.asname:
                    out.add(al.asname)
        elif isinstance(n, ast.ImportFrom) and n.module == "torch.nn":
            for al in n.names:
                if al.name == "functional":
                    out.add(al.asname or "functional")
    return frozenset(out)


# pandas / pyarrow constructors recognized by the value engine.
_PANDAS_CTORS = frozenset({"Series"})


def _pandas_ctor(name, node, env, ctx):
    """A pandas constructor as a sized typed column with opaque cells: Series(data) -> a 1-D sized column (an
    _NdArray of one dimension) whose length, positional .iloc index, and empty-reduction trap decide while cell
    values abstain. Built from a list/tuple literal or a sized container; another argument, and the DataFrame /
    pd.array constructors (whose construction can raise on mismatched data -- an unmodeled trap), return None so
    the caller abstains (UNKNOWN), never a false PROVED."""
    args = [ev(a, env, ctx) for a in node.args]               # each argument trap-checked as it is evaluated
    for kw in node.keywords:
        ev(kw.value, env, ctx)
    if name == "Series":
        a0 = node.args[0] if node.args else None
        if isinstance(a0, (ast.List, ast.Tuple)) and not any(isinstance(e, ast.Starred) for e in a0.elts):
            return _Column((z3.IntVal(len(a0.elts)),))        # Series([...]) -> a column of literal length
        if args and isinstance(args[0], _SafeContainer) and not args[0].unindexable:
            return _Column((_container_len(args[0], ctx),))   # Series(seq) -> the sequence's length
        if args and isinstance(args[0], _NdArray) and len(args[0].shape) == 1:
            return _Column(args[0].shape)
    return None


# collections constructors recognized by the value engine, reachable as collections.X(...) and as the bare
# imported name (from collections import defaultdict). defaultdict / Counter are dicts with no missing-key
# trap; OrderedDict is a regular dict; namedtuple builds a class.
_COLLECTIONS_CTORS = frozenset({"defaultdict", "Counter", "OrderedDict", "namedtuple"})


def _collections_ctor(name, node, env, ctx):
    """A collections constructor as a sound model: defaultdict / Counter -> a dict whose missing-key read
    returns a default (never KeyError); OrderedDict() -> an empty tracked dict and OrderedDict(arg) -> an opaque
    dict (a regular dict, so a read may KeyError); namedtuple(...) -> an opaque class. Every argument and keyword
    is trap-checked as it is evaluated. Returns None when `name` is not a modeled collections constructor."""
    if name not in _COLLECTIONS_CTORS:
        return None
    for a in node.args:                                       # the default_factory / iterable / field list, etc.
        ev(a.value if isinstance(a, ast.Starred) else a, env, ctx)
    for kw in node.keywords:
        ev(kw.value, env, ctx)
    if name in ("defaultdict", "Counter"):
        return _DefaultDict(name)
    if name == "OrderedDict":
        if not node.args and not node.keywords:
            return _MapVal()                                  # OrderedDict() -> an empty tracked dict (like dict())
        return _DictLit("ordereddict")                        # OrderedDict(arg): an opaque dict (a read may KeyError)
    return _Opaque("namedtuple")                              # namedtuple(...) -> a class (a total construction)


def _call_repo(name, argvals, ctx):
    """Call a repo function with given argument values. When an argument is itself a callable
    (a lambda or function reference), inline the callee specialized to those arguments so the
    calls it makes to its functional parameters resolve; otherwise use the memoized summary."""
    if any(isinstance(a, (_Lambda, _FuncRef)) for a in argvals):
        _a, _z, rets, ctraps, _none = symexec(ctx.repo[name], Ctx(ctx.repo), argvals=argvals)
        if ctx.traps is not None:
            for tcond in ctraps:
                ctx.traps.append(z3.And(ctx.pc, tcond))
        return fold(rets)
    return ctx.inline(name, argvals)


def _eval_args(argnodes, env, ctx):
    """Evaluate positional call arguments, splicing a starred argument `*t` whose value is a
    tuple (the common `f(*args)` call form)."""
    out = []
    for a in argnodes:
        if isinstance(a, ast.Starred):
            v = ev(a.value, env, ctx)
            if not isinstance(v, tuple):
                raise Unsupported("starred call argument is not a tuple")
            out.extend(v)
        else:
            out.append(ev(a, env, ctx))
    return out


def _bind_call(callee, call, env, ctx):
    """Match a call's positional and keyword arguments to a callee's parameters, filling
    defaults, so the callee is always invoked with one value per positional/keyword-only
    parameter. Returns the ordered values for `args` then `kwonlyargs`."""
    pos = [a.arg for a in callee.args.args]
    kwonly = [a.arg for a in callee.args.kwonlyargs]
    posdef = callee.args.defaults
    kwdef = callee.args.kw_defaults
    # a positional *xs splat of a variable-length sequence into the callee's named parameters: Python binds
    # xs[0..n-1] to them and raises TypeError unless len(xs) equals the parameter count. Model that for a
    # single *xs (the sole positional argument, a bound name) filling a plain fixed-arity callee -- no
    # defaults, callee *args, keyword-only parameters, or keywords -- so an unguarded g(*xs) refutes on a
    # length mismatch and a len()-guarded one binds and inlines (each parameter then an arbitrary element).
    # A constant-tuple splat (not a _SafeContainer) falls through to _eval_args, which splices it exactly.
    if (len(call.args) == 1 and isinstance(call.args[0], ast.Starred)
            and isinstance(call.args[0].value, ast.Name) and not call.keywords
            and not callee.args.vararg and not kwonly and not posdef):
        xs = ev(call.args[0].value, env, ctx)                # a bound name: side-effect-free, no double-eval
        if isinstance(xs, _SafeContainer):
            if ctx.traps is not None:
                ctx.traps.append(z3.And(ctx.pc, _container_len(xs, ctx) != len(pos)))   # wrong arity -> TypeError
            return [z3.FreshInt("splat") for _ in pos]       # xs[i] is an arbitrary element of the sequence
    posvals = _eval_args(call.args, env, ctx)                # positional (handles *splat)
    kwmap = {kw.arg: ev(kw.value, env, ctx) for kw in call.keywords if kw.arg is not None}
    splatted = []
    for kw in call.keywords:                                 # **d splat: splice a constant-string-keyed dict literal
        if kw.arg is not None:                               # into the named parameters (the call-site counterpart of
            continue                                         # the *tuple splat _eval_args handles)
        if not (isinstance(kw.value, ast.Dict)
                and all(isinstance(k, ast.Constant) and isinstance(k.value, str) for k in kw.value.keys)):
            raise Unsupported("** splat of a non-literal (symbolic-key) mapping")
        for k, val in zip(kw.value.keys, kw.value.values):
            if k.value in kwmap:                             # duplicate keyword: Python raises TypeError -- decline
                raise Unsupported("** splat duplicates keyword '%s'" % k.value)
            kwmap[k.value] = ev(val, env, ctx)               # the value is trap-checked as it is evaluated
            splatted.append(k.value)
    for key in splatted:                                     # a spliced key must name a free named parameter, else
        if key not in pos and key not in kwonly:             # Python raises TypeError (unexpected / feeds **kwargs)
            raise Unsupported("** splat key '%s' is not a named parameter" % key)   # -- decline rather than claim safe
        if key in pos[:len(posvals)]:
            raise Unsupported("** splat key '%s' already given positionally" % key)
    if len(posvals) > len(pos):
        if callee.args.vararg is not None and _TRAPFREE:
            pass                                             # the extras (already trap-checked) feed the callee's *args
        elif callee.args.vararg is None and _TRAPFREE:       # too many positional args, no *args: TypeError
            if ctx.traps is not None:
                ctx.traps.append(ctx.pc)
        else:
            raise Unsupported("too many positional arguments (callee *args not modeled)")
    out = []
    for i, p in enumerate(pos):
        if i < len(posvals):
            out.append(posvals[i])
        elif p in kwmap:
            out.append(kwmap[p])
        elif i >= len(pos) - len(posdef):
            out.append(ev(posdef[i - (len(pos) - len(posdef))], env, ctx))
        else:
            raise Unsupported(f"missing argument for parameter {p}")
    for j, p in enumerate(kwonly):                           # keyword-only parameters
        if p in kwmap:
            out.append(kwmap[p])
        elif kwdef[j] is not None:
            out.append(ev(kwdef[j], env, ctx))
        else:
            raise Unsupported(f"missing keyword-only argument {p}")
    return out


def _enumerate_iter(node, env, ctx):
    """The concrete element values of an iterable expression, or None when it is not statically enumerable.
    Handles a list / tuple literal, range(...) with constant integer arguments (capped so a huge range does
    not blow up), and any expression that evaluates to a Python tuple (a constant-length sequence in the value
    model). A symbolic-length collection (an opaque list parameter) returns None, so a quantifier over it is
    declined rather than unsoundly unrolled."""
    if isinstance(node, (ast.List, ast.Tuple)):
        return [ev(e, env, ctx) for e in node.elts]
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range":
        vals = []
        for a in node.args:
            if isinstance(a, ast.Constant) and isinstance(a.value, int) and not isinstance(a.value, bool):
                vals.append(a.value)
            else:
                return None
        if not (1 <= len(vals) <= 3):
            return None
        rng = list(range(*vals))
        if len(rng) > 256:
            return None                                          # too large to unroll soundly into a finite conjunction
        return [z3.IntVal(i) for i in rng]
    v = ev(node, env, ctx)
    return list(v) if isinstance(v, tuple) else None


def _spec_quantify(gen, env, ctx):
    """The per-element boolean conditions of a generator expression `gen` whose iterable is concretely
    enumerable, or None. One generator with a plain Name target and no filter clause is required, so
    all(p(x) for x in <concrete>) / any(...) unrolls to a sound finite And / Or over those conditions."""
    if len(gen.generators) != 1:
        return None
    g = gen.generators[0]
    if not isinstance(g.target, ast.Name) or g.ifs or getattr(g, "is_async", 0):
        return None
    items = _enumerate_iter(g.iter, env, ctx)
    if items is None:
        return None
    out = []
    for it in items:
        e2 = dict(env); e2[g.target.id] = it
        out.append(_as_bool(ev(gen.elt, e2, ctx), ctx))
    return out


def ev(node, env: Dict[str, z3.ExprRef], ctx: Ctx) -> z3.ExprRef:
    _ln = getattr(node, "lineno", None)                       # track the line being evaluated, for overapprox provenance
    if _ln is not None:
        ctx._cur_line = _ln
    if isinstance(node, ast.Constant) and isinstance(node.value, bool):
        return z3.BoolVal(node.value)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return z3.IntVal(node.value)
    if isinstance(node, ast.Constant) and isinstance(node.value, float):
        return z3.FPVal(node.value, _F64)
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return z3.StringVal(node.value)
    if isinstance(node, ast.Constant) and isinstance(node.value, complex):
        c = node.value
        return _Complex(z3.FPVal(c.real, _F64), z3.FPVal(c.imag, _F64))
    if isinstance(node, ast.Constant) and node.value is None:   # None is a distinct value: arithmetic on it traps
        return _NoneVal()
    if isinstance(node, ast.Constant) and isinstance(node.value, bytes):   # a bytes literal: a byteslike container of
        return _SafeContainer("bytelit", byteslike=True, immutable=True,   # the known length (so b"" + b concatenates,
                              length=z3.IntVal(len(node.value)))            # b"abc"[i] bounds-checks against 3)
    if _TRAPFREE and isinstance(node, ast.Constant):         # Ellipsis / other: opaque, trap free to produce
        return _Opaque("const")
    if isinstance(node, ast.JoinedStr):                      # f-string: concat of parts
        out = z3.StringVal("")
        for part in node.values:
            if isinstance(part, ast.Constant) and isinstance(part.value, str):
                out = z3.Concat(out, z3.StringVal(part.value))
            elif isinstance(part, ast.FormattedValue):
                if part.conversion not in (-1, 115, 114, 97):   # allow !s / !r / !a: str/repr/ascii never trap
                    raise Unsupported("f-string conversion")
                v = ev(part.value, env, ctx)                # trap-check the interpolated expression
                if part.format_spec is not None:
                    scalar = z3.is_expr(v) and (z3.is_int(v) or z3.is_bool(v) or _is_fp(v) or _is_str(v))
                    if _TRAPFREE:                            # the value engine: the term's sort is the value's real type,
                        if not (scalar and _const_format_spec_safe(part.format_spec, v)):   # so a type-compatible spec is safe
                            raise Unsupported("f-string format spec")
                        return z3.FreshConst(_SS, "fstr")    # the whole f-string is a string (opaque value, str type)
                    # the CHC / equivalence engines model every parameter as Int, so only a type-independent
                    # alignment / width spec (safe for any scalar) is sound here; a typed spec abstains.
                    if not (scalar and _alignment_only_spec(part.format_spec) is not None):
                        raise Unsupported("f-string format spec")
                    _note_overapprox(ctx, "an f-string format spec")
                    return z3.FreshConst(_SS, "fstr")
                if part.conversion in (114, 97) or not _is_str(v):   # !r / !a, or str() of a non-string: a string of
                    if _TRAPFREE:                                     # unknown content, but definitely str-typed
                        return z3.FreshConst(_SS, "fstr")
                    raise Unsupported("f-string interpolation of a non-string value")
                out = z3.Concat(out, v)                      # a plain str field (or !s on a str): the string itself
            else:
                raise Unsupported("f-string part")
        return out
    if isinstance(node, ast.NamedExpr):                      # walrus (x := e): bind the target, yield the value
        val = ev(node.value, env, ctx)
        if isinstance(node.target, ast.Name):
            env[node.target.id] = val
        return val
    if isinstance(node, ast.Name):
        if node.id in env:
            return env[node.id]
        if node.id in ctx.repo:
            return _FuncRef(node.id)                          # a named function used as a value
        if node.id in _MATH_CONSTS:                           # `from math import pi` / e / tau / inf / nan
            return _MATH_CONSTS[node.id]
        return _Opaque(node.id)                               # a free/imported name: opaque, reading it traps at most NameError
    if isinstance(node, ast.Tuple) and not any(isinstance(e, ast.Starred) for e in node.elts):
        return tuple(ev(e, env, ctx) for e in node.elts)     # tuple packing -> a Python tuple of terms
    if _TRAPFREE and isinstance(node, ast.Tuple):            # (*a, *b, x): a NEW immutable tuple of length
        return _SafeContainer("tupleunpack", immutable=True, length=_star_seq_len(node.elts, env, ctx))
    if isinstance(node, ast.List) and not any(isinstance(e, ast.Starred) for e in node.elts):
        return _ListLit(ev(e, env, ctx) for e in node.elts)  # list literal -> a tuple of element terms (tagged mutable
        #                                                      for a[i] = v); each element is evaluated, trap-checked
    if _TRAPFREE and isinstance(node, ast.List):             # [*a, *b, x]: a NEW list of length sum(len(*list)) + the
        return _SafeContainer("listunpack", length=_star_seq_len(node.elts, env, ctx))   # plain-element count
    if isinstance(node, ast.Set):                            # set literal: evaluate the elements for their
        for e in node.elts:                                  # traps, then an opaque value
            ev(e.value if isinstance(e, ast.Starred) else e, env, ctx)
        return _Opaque("set")
    if isinstance(node, ast.Dict):
        if any(k is None for k in node.keys):                # {**other}: keys not enumerable -> opaque dict
            for k, v in zip(node.keys, node.values):
                if k is not None:
                    ev(k, env, ctx)
                ev(v, env, ctx)
            return _DictLit("dict")
        keys = [_map_key(ev(k, env, ctx)) for k in node.keys]   # a tracked dict literal: its keyed entries,
        vals = [ev(v, env, ctx) for v in node.values]           # so d[k] reads the value (or KeyErrors)
        return _MapVal(keys, vals)

    if isinstance(node, ast.Lambda):                         # lambda as a first-class value (a closure)
        return _Lambda([a.arg for a in node.args.args], node.body, dict(env))
    if isinstance(node, ast.Call) and (isinstance(node.func, ast.Lambda)
            or (isinstance(node.func, ast.Name) and isinstance(env.get(node.func.id), (_Lambda, _FuncRef)))):
        callee = ev(node.func, env, ctx) if isinstance(node.func, ast.Lambda) else env[node.func.id]
        argvals = _eval_args(node.args, env, ctx)
        if isinstance(callee, _FuncRef):                      # a function-valued variable, called
            return _call_repo(callee.name, argvals, ctx)
        if len(callee.params) != len(argvals):
            raise Unsupported("lambda called with the wrong number of arguments")
        callenv = dict(callee.env)
        for pname, av in zip(callee.params, argvals):
            callenv[pname] = av
        return ev(callee.body, callenv, ctx)
    if isinstance(node, ast.BinOp):
        op = type(node.op)
        l = ev(node.left, env, ctx)
        r = ev(node.right, env, ctx)
        if isinstance(l, _NoneVal) or isinstance(r, _NoneVal):   # None + x and every arithmetic/bitwise op on None
            if ctx.traps is not None:                            # raise TypeError: a reachable trap
                ctx.traps.append(ctx.pc)
            return _Opaque("noneop")
        if op in (ast.BitOr, ast.BitAnd, ast.Sub, ast.BitXor) and _is_set_like(l) and _is_set_like(r):
            return _set_binop({ast.BitOr: "|", ast.BitAnd: "&", ast.Sub: "-", ast.BitXor: "^"}[op], l, r, ctx)
        if op is ast.BitOr and isinstance(l, (_DictParam, _DictLit, _MapVal)) \
                and isinstance(r, (_DictParam, _DictLit, _MapVal)):
            # dict | dict (PEP 584): a new dict whose keys are the union of the two, never raising. Its size is in
            # [max(len a, len b), len a + len b]; membership is its own, so c = a | b then a guarded c[k] / len(c)
            # decides while an unguarded c[k] still refutes (a regular dict's read may KeyError).
            merged = _DictParam(z3.FreshInt("dmerge").decl().name())
            if ctx.facts is not None:
                la, lb, lm = _container_len(l, ctx), _container_len(r, ctx), _container_len(merged, ctx)
                ctx.facts.append(z3.And(lm >= la, lm >= lb, lm <= la + lb))
            return merged
        if isinstance(l, _NdArray) or isinstance(r, _NdArray):   # element-wise ndarray arithmetic (broadcasting)
            if op is ast.MatMult:                                # a @ b: matrix multiply, not element-wise
                return _matmul(l, r, ctx)
            return _nd_binop(l, r, ctx)
        if op is ast.Mod and _is_str(l):                     # str % args -- printf formatting, even when args is a
            if not z3.is_string_value(l) and _TRAPFREE and not BEST_EFFORT:   # tuple (which would look like a tuple op)
                # a NON-constant format string can mismatch its args at runtime (a TypeError / ValueError the engine
                # does not model), so trap freedom abstains rather than claim the % cannot raise; a CONSTANT format
                # string stays the assume-the-args-match over-approximation (trap free, with the args trap-checked).
                raise Unsupported("string formatting with a non-constant format string may raise (not modeled)")
            _note_overapprox(ctx, "string % formatting")     # a trap-free string, the args already trap-checked
            return z3.FreshConst(_SS, "strmod")
        if isinstance(l, tuple) or isinstance(r, tuple):
            if op is ast.Add:
                if isinstance(l, tuple) and isinstance(r, tuple):
                    return l + r                             # list / tuple concatenation
                other = r if isinstance(l, tuple) else l     # the operand added to a sequence literal
                if isinstance(other, _Opaque) and not (isinstance(other, _SafeContainer)
                                                       and (other.byteslike or other.unindexable)):
                    # a list-kind container (list + list is valid, but a literal collapses to a tuple so list + list
                    # vs tuple + list is ambiguous), an ndarray (numpy broadcasts -- no raise), or an opaque value:
                    # undecided. Abstain rather than fabricate a TypeError trap (a false refutation of xs + [1]).
                    raise Unsupported("adding a sequence literal to a container / ndarray / opaque value is undecided")
                if ctx.traps is not None:                    # sequence literal + a scalar / str / bytes / set: TypeError
                    ctx.traps.append(ctx.pc)
                return _Opaque("seqop")
            if op is ast.Mult:
                tv, kv = (l, r) if isinstance(l, tuple) else (r, l)
                if z3.is_int_value(kv):
                    return tv * kv.as_long()                 # tuple repetition by a constant
                if z3.is_expr(kv) and (z3.is_int(kv) or z3.is_bool(kv)):   # seq * a symbolic int / bool (True == 1):
                    if _TRAPFREE:                            # trap free; the length is the count times the repeated
                        k = z3.If(kv, z3.IntVal(1), z3.IntVal(0)) if z3.is_bool(kv) else kv   # width, clamped at 0 for a
                        return _SafeContainer("seqrep", length=z3.If(k >= 0, z3.IntVal(len(tv)) * k, z3.IntVal(0)))  # non-
                    raise Unsupported("tuple repetition by a non-constant count")                                    # positive count
                if isinstance(kv, _Opaque) and not isinstance(kv, _SafeContainer):
                    raise Unsupported("sequence repetition by an ndarray / opaque value")   # numpy broadcasts: abstain
                if ctx.traps is not None:                    # seq * a sequence / str / float / Fraction: TypeError
                    ctx.traps.append(ctx.pc)
                return _Opaque("seqop")
            if ctx.traps is not None:                        # any other operator on a list/tuple (-, /, //, **, &, ...) is a TypeError
                ctx.traps.append(ctx.pc)
            return _Opaque("seqop")
        if (isinstance(l, _SafeContainer) and isinstance(r, _SafeContainer) and op is ast.Add
                and not l.unindexable and not r.unindexable and l.byteslike == r.byteslike):
            # bytes + bytes or list + list concatenation: a container whose length is the sum, so a later index into
            # the result is bounds-checked against len(l) + len(r); byteslike is preserved (elements stay in [0, 255]).
            return _SafeContainer("concat", byteslike=l.byteslike,
                                  length=_container_len(l, ctx) + _container_len(r, ctx))
        if (isinstance(l, _SafeContainer) or isinstance(r, _SafeContainer)) and op is ast.Mult:
            sc, k = (l, r) if isinstance(l, _SafeContainer) else (r, l)
            if (not sc.unindexable and sc.tuple_arity is None and sc.elem is None
                    and z3.is_expr(k) and (z3.is_int(k) or z3.is_bool(k))):
                # list / bytes * int repeats it: a NEW sequence of length max(count, 0) * len(seq), trap free; the
                # element kind (byteslike) is preserved. A nested / tuple-element source falls through (aliasing).
                kk = z3.If(k, z3.IntVal(1), z3.IntVal(0)) if z3.is_bool(k) else k
                n = _container_len(sc, ctx)
                return _SafeContainer("seqrep", byteslike=sc.byteslike,
                                      length=z3.If(kk >= 0, n * kk, z3.IntVal(0)))
        if isinstance(l, _Complex) or isinstance(r, _Complex):
            return _cx_binop(op, l, r)
        if (_is_real(l) or _is_real(r)) and not (_is_fp(l) or _is_fp(r)):   # exact rational (Fraction) arithmetic;
            a, b = _to_real(l), _to_real(r)                  # a mixed Fraction/float falls through to the float
            #                                                  path below, where Python coerces the Fraction to float
            if op is ast.Add: return a + b
            if op is ast.Sub: return a - b
            if op is ast.Mult: return a * b
            if op is ast.Div:
                if ctx.traps is not None:
                    ctx.traps.append(z3.And(ctx.pc, b == 0))
                return a / b
            raise Unsupported(f"rational operator {op.__name__}")
        if _is_str(l) or _is_str(r):
            other = l if not _is_str(l) else r               # the non-string operand, if any
            if type(other) is _Opaque:                       # a string op whose other operand is unmodeled: not
                if BEST_EFFORT:                              # provably a non-string, so abstain unless best-effort
                    _best_effort_assume()
                    return _Opaque("be_strop")
                raise Unsupported("operation on an unmodeled value")
            if op is ast.Add and _is_str(l) and _is_str(r):
                return z3.Concat(l, r)
            if op is ast.Mult:                               # string repetition by a constant count
                sv, kv = (l, r) if _is_str(l) else (r, l)
                if z3.is_int_value(kv):
                    k = kv.as_long()
                    return z3.StringVal("") if k <= 0 else z3.Concat(*([sv] * k))
                if _is_str(kv) or _is_fp(kv) or _is_real(kv):   # str * str / float: TypeError
                    if ctx.traps is not None:
                        ctx.traps.append(ctx.pc)
                    return _Opaque("strop")
                if _TRAPFREE:                                # str * a symbolic int: trap free, content opaque
                    _note_overapprox(ctx, "string repetition by a variable count")
                    return z3.FreshConst(_SS, "strrep")
                raise Unsupported("string repetition by a non-constant count")
            if op is ast.Add:                                # str + a non-string: TypeError (unsupported operands)
                if ctx.traps is not None:
                    ctx.traps.append(ctx.pc)
                return _Opaque("strop")
            if op is ast.Mod:                                # str % args: printf-style formatting, over-approximated
                _note_overapprox(ctx, "string % formatting")  # as a trap-free string -- the same assume-the-format-
                return z3.FreshConst(_SS, "strmod")           # matches over-approximation the f-string / print() paths
                #                                               make; the arguments were already trap-checked
            if ctx.traps is not None:                        # str with -, /, //, **, shifts, or bitwise: TypeError
                ctx.traps.append(ctx.pc)
            return _Opaque("strop")
        if op is ast.Div:                                    # true division -> float
            if _is_fp(l) or _is_fp(r):
                if ctx.traps is not None:
                    ctx.traps.append(z3.And(ctx.pc, _is_zero(r)))   # ZeroDivisionError
                return z3.fpDiv(_RM, _to_fp(l), _to_fp(r))          # a float operand: CPython coerces, then divides
            la, lb = _as_int(l), _as_int(r)                         # int / int: correctly rounded, signed
            if ctx.traps is not None:
                ctx.traps.append(z3.And(ctx.pc, lb == 0))                     # ZeroDivisionError
            mag = z3.fpToFP(_RM, z3.ToReal(z3.If(la < 0, -la, la)) / z3.ToReal(z3.If(lb < 0, -lb, lb)), _F64)
            return z3.If(z3.Xor(la < 0, lb < 0), z3.fpNeg(mag), mag)          # sign = sign(a) xor sign(b)
        if op is ast.Pow:
            if _is_fp(l):
                return _fp_pow(l, node.right, ctx)        # x ** 0 / x ** 1 exact; x ** n (n>=2) over-approximated
            try:
                return _pow_expand(l, node.right)         # integer base ** constant 0..64: exact
            except Unsupported:
                int_ops = (z3.is_expr(l) and z3.is_expr(r)
                           and (z3.is_int(l) or z3.is_bool(l)) and (z3.is_int(r) or z3.is_bool(r)))
                if int_ops and (_TRAPFREE or ctx.facts is not None):
                    # integer base ** variable exponent: 0 ** (negative) traps; the value is a fresh int
                    # over-approximated by the power axioms.
                    base_i, exp_i = _as_int(l), _as_int(r)
                    if ctx.traps is not None:
                        trap = z3.And(ctx.pc, base_i == 0, exp_i < 0)   # 0 ** (negative): ZeroDivisionError
                        hard = getattr(ctx, "hard_traps", None)
                        if (hard is not None and not getattr(ctx, "overapprox", False)
                                and not getattr(ctx, "havoc", False)):
                            # the operands are exact (no over-approximation / havoc in scope), so this trap is real
                            # and refutes even though the RESULT value below is over-approximated (a fresh int).
                            hard.append(trap)
                        else:
                            ctx.traps.append(trap)             # operands possibly over-approximated: leave it suppressible
                    over_cap = (isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
                                and not isinstance(node.right.value, bool) and node.right.value > 64)
                    _note_overapprox(ctx, "** with a constant exponent over the unroll cap (64)" if over_cap
                                     else "** with a variable exponent")
                    r2 = z3.FreshInt("pow")
                    if ctx.facts is not None:
                        ctx.facts.extend(_pow_axioms(base_i, exp_i, r2))
                    return r2
                raise
        if op in (ast.FloorDiv, ast.Mod) and (_is_fp(l) or _is_fp(r)):
            lf, rf = _to_fp(l), _to_fp(r)
            if ctx.traps is not None:
                ctx.traps.append(z3.And(ctx.pc, z3.fpIsZero(rf)))       # float // 0.0 / % 0.0: ZeroDivisionError
            return _fp_arith(op, lf, rf)
        if _is_fp(l) or _is_fp(r):
            return _fp_arith(op, l, r)
        if op is ast.MatMult:
            raise Unsupported("matrix multiply @ is outside the scalar subset")
        l, r = _as_int(l), _as_int(r)                        # bool operands -> their 0/1 value
        if op is ast.LShift or op is ast.RShift:             # a constant shift is exact; a variable one is over-approximated
            if (isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
                    and not isinstance(node.right.value, bool) and node.right.value >= 0):
                k = node.right.value
                return l * (2 ** k) if op is ast.LShift else py_floordiv(l, z3.IntVal(2 ** k))
            if _TRAPFREE:                                    # x << k / x >> k by a variable count: a negative count is
                if ctx.traps is not None:                    # a ValueError, the value an over-approximation (2**k is nonlinear)
                    trap = z3.And(ctx.pc, r < 0)             # negative shift count: ValueError (an exact trap condition)
                    hard = getattr(ctx, "hard_traps", None)
                    if (hard is not None and not getattr(ctx, "overapprox", False)
                            and not getattr(ctx, "havoc", False)):
                        hard.append(trap)                    # operands exact: refutes despite the over-approximated value
                    else:
                        ctx.traps.append(trap)               # operands possibly over-approximated: leave it suppressible
                _note_overapprox(ctx, "a variable bit shift")
                return z3.FreshInt("shift")
            raise Unsupported(f"{op.__name__} requires a constant non-negative shift")
        if op is ast.BitAnd:                                 # masking the low k bits is exact for every int:
            for a, b in ((node.left, node.right), (node.right, node.left)):   # a & (2^k - 1) == a % 2^k
                m = b.value if isinstance(b, ast.Constant) and isinstance(b.value, int) \
                    and not isinstance(b.value, bool) else None
                if m is not None and m >= 0 and (m & (m + 1)) == 0:           # m is 2^k - 1 (all low bits set)
                    operand = l if a is node.left else r
                    return py_mod(operand, z3.IntVal(m + 1))
            if ctx.bv_width is not None:                      # the exact bitvector decision (both operands bounded)
                return _bitwise_exact("and", l, r, ctx.bv_width, ctx)
            over = _bitwise_overapprox("and", l, r, ctx)     # a fresh integer with nonnegative-operand bounds, so
            if over is not None:                             # the result is usable in arithmetic (REFUTED withheld)
                return over
            if _TRAPFREE:                                    # no over-approximation channel, but a bitwise op never
                return _Opaque("bitop")                      # traps -- the result is opaque but trap free
            raise Unsupported("bitwise And on unbounded integers other than a low-bit mask (use the bitvector engine)")
        if op in (ast.BitOr, ast.BitXor):                    # no exact unbounded-integer encoding
            if ctx.bv_width is not None:                      # the exact bitvector decision (both operands bounded)
                return _bitwise_exact("or" if op is ast.BitOr else "xor", l, r, ctx.bv_width, ctx)
            over = _bitwise_overapprox("or" if op is ast.BitOr else "xor", l, r, ctx)
            if over is not None:                             # a fresh integer with nonnegative-operand bounds
                return over
            if _TRAPFREE:                                    # no over-approximation channel, but a bitwise op never
                return _Opaque("bitop")                      # traps -- the result is opaque but trap free
            raise Unsupported(f"bitwise {op.__name__} on unbounded integers (use the bitvector engine)")
        if op not in _BINOPS:
            raise Unsupported(f"binop {op.__name__}")
        if op in (ast.FloorDiv, ast.Mod):
            if ctx.traps is not None:
                ctx.traps.append(z3.And(ctx.pc, r == 0))
            if ctx.divaux is not None:                       # linearize for the CHC engine
                q = z3.Int(f"_dq{len(ctx.divvars)}"); ctx.divvars.append(q)
                ctx.divaux.append(z3.Implies(r > 0, z3.And(r * q <= l, l < r * q + r)))
                ctx.divaux.append(z3.Implies(r < 0, z3.And(r * q >= l, l > r * q + r)))
                return q if op is ast.FloorDiv else (l - r * q)
        return _BINOPS[op](l, r)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        v = ev(node.operand, env, ctx)
        return z3.fpNeg(v) if _is_fp(v) else -_as_int(v)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Invert):
        v = ev(node.operand, env, ctx)
        if _is_fp(v):
            raise Unsupported("~ on a float")
        return -_as_int(v) - 1                               # Python: ~a == -(a + 1)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return z3.If(_as_bool(ev(node.operand, env, ctx), ctx), z3.IntVal(0), z3.IntVal(1))
    if isinstance(node, ast.BoolOp):
        # Python value semantics: 'a and b' is b if a is truthy else a; 'a or b' is
        # a if a is truthy else b. Short-circuiting threads the trap path condition.
        is_and = isinstance(node.op, ast.And)
        old = ctx.pc

        def fold(i, guard):
            ctx.pc = guard
            v = ev(node.values[i], env, ctx)
            if i == len(node.values) - 1:
                return _as_int(v)
            cond = _as_bool(v, ctx)
            nxt = z3.And(guard, cond) if is_and else z3.And(guard, z3.Not(cond))
            rest = fold(i + 1, nxt)
            return z3.If(cond, rest, _as_int(v)) if is_and else z3.If(cond, _as_int(v), rest)

        result = fold(0, old)
        ctx.pc = old
        return result
    if isinstance(node, ast.Compare):
        if len(node.ops) != 1:
            raise Unsupported("chained comparison")
        op = type(node.ops[0])
        l = ev(node.left, env, ctx)
        if (op is ast.In or op is ast.NotIn) and isinstance(node.comparators[0], ast.Set) \
                and all(not isinstance(e, ast.Starred) for e in node.comparators[0].elts):
            elems = [ev(e, env, ctx) for e in node.comparators[0].elts]   # x in {literal set}: membership is
            if all(not isinstance(e, (_Opaque, _Closure)) and not isinstance(e, tuple) for e in elems):
                c = z3.Or(*[_term_eq(l, e) for e in elems]) if elems else z3.BoolVal(False)   # a disjunction of ==
                return c if op is ast.In else z3.Not(c)
        r = ev(node.comparators[0], env, ctx)
        if (op is ast.In or op is ast.NotIn) and isinstance(r, _DictParam):
            mem = _dict_member(r, l)                          # k in d : the dict's stable membership predicate
            if mem is not None:
                return mem if op is ast.In else z3.Not(mem)
        if (op is ast.In or op is ast.NotIn) and isinstance(r, _SafeContainer) and ctx.traps is not None:
            mem = _seq_member(r, l, ctx)                      # x in xs : the sequence's stable membership predicate,
            if mem is not None:                              # connecting an `x in xs` guard to index/remove and length
                return mem if op is ast.In else z3.Not(mem)
        if (op is ast.Is or op is ast.IsNot) and (isinstance(l, _NoneVal) or isinstance(r, _NoneVal)):
            other = r if isinstance(l, _NoneVal) else l       # x is None: exact for None, definite-false for a
            if isinstance(other, _NoneVal):                   # concrete value, unknown for another opaque
                res = z3.BoolVal(True)
            elif isinstance(other, (_Opaque, _Closure)):
                res = z3.FreshConst(z3.BoolSort(), "isnone")
            else:
                res = z3.BoolVal(False)
            return res if op is ast.Is else z3.Not(res)
        if op in (ast.Lt, ast.LtE, ast.Gt, ast.GtE):
            _unord = (_SafeContainer, _DictParam, _DictLit, _MapVal, _NoneVal)   # a container or None
            _scal = lambda v: z3.is_expr(v) and (z3.is_int(v) or z3.is_bool(v) or _is_fp(v))
            if (isinstance(l, _unord) and _scal(r)) or (_scal(l) and isinstance(r, _unord)):
                raise Unsupported("ordering a container or None against a number (TypeError, not a bool)")
        if (isinstance(l, _NdArray) or isinstance(r, _NdArray)) \
                and op in (ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.Eq, ast.NotEq):
            return _nd_binop(l, r, ctx)                       # an ndarray rich comparison is ELEMENT-WISE: an array of
            #                                                   booleans (broadcast), not a scalar -- so `if a == b:`
            #                                                   then meets _as_bool's ambiguous-truth-value abstention
        if (isinstance(l, _FieldVal) or isinstance(r, _FieldVal)) and op in _CMP:
            # an opaque object's field is duck-typed numeric in a comparison too (o.x > o.y, o.x == k), as long as
            # the other operand is also numeric or a field; a field against a string / container falls through.
            ln = isinstance(l, _FieldVal) or (z3.is_expr(l) and (z3.is_int(l) or z3.is_bool(l) or _is_fp(l)))
            rn = isinstance(r, _FieldVal) or (z3.is_expr(r) and (z3.is_int(r) or z3.is_bool(r) or _is_fp(r)))
            if ln and rn:
                li = _as_int(l) if isinstance(l, _FieldVal) else l
                ri = _as_int(r) if isinstance(r, _FieldVal) else r
                if _is_fp(li) or _is_fp(ri):
                    return _FP_CMP[op](_to_fp(li), _to_fp(ri))
                return _CMP[op](li, ri)
        if isinstance(l, (_Opaque, _Closure)) or isinstance(r, (_Opaque, _Closure)):
            if _TRAPFREE:                                     # comparison / membership of an opaque value, assuming
                return z3.FreshConst(z3.BoolSort(), "hc")     # the program compares compatible values: arbitrary bool
            raise Unsupported("comparison of an unmodeled value")
        if op is ast.In or op is ast.NotIn:                  # membership in a tuple or substring
            if isinstance(r, tuple):
                c = z3.Or(*[_term_eq(l, e) for e in r]) if r else z3.BoolVal(False)
            elif _is_str(l) and _is_str(r):
                c = z3.Contains(r, l)
            elif BEST_EFFORT:                                # membership in an unmodeled container: a bool (lower trust)
                _best_effort_assume()
                c = z3.FreshConst(z3.BoolSort(), "be_in")
            else:
                raise Unsupported("membership outside strings and tuples")
            return c if op is ast.In else z3.Not(c)
        if isinstance(l, tuple) or isinstance(r, tuple):
            if op is ast.Eq:
                return _term_eq(l, r)
            if op is ast.NotEq:
                return _term_neq(l, r)
            raise Unsupported("tuple ordering comparison")
        if isinstance(l, _Complex) or isinstance(r, _Complex):
            if op is ast.Eq:
                return _term_eq(l, r)
            if op is ast.NotEq:
                return _term_neq(l, r)
            raise Unsupported("complex ordering comparison")
        if _is_str(l) != _is_str(r):                         # one string, one number: a type mismatch
            if op is ast.Eq:
                return z3.BoolVal(False)                     # CPython: "a" == 1 is False, not an error
            if op is ast.NotEq:
                return z3.BoolVal(True)                      # CPython: "a" != 1 is True
            if ctx.traps is not None:                        # ordering str against a number is a TypeError,
                ctx.traps.append(z3.And(ctx.pc, z3.BoolVal(True)))   # a trap on this path, like div-by-zero
            return z3.BoolVal(False)                         # poison: never trusted once the trap fires
        if op is ast.Is or op is ast.IsNot:                  # identity of two non-None values is opaque; `is` never raises
            res = z3.FreshConst(z3.BoolSort(), "is")
            return res if op is ast.Is else z3.Not(res)
        if _is_fp(l) or _is_fp(r):
            return _FP_CMP[op](_to_fp(l), _to_fp(r))
        return _CMP[op](l, r)
    if isinstance(node, ast.IfExp):
        t = _as_bool(ev(node.test, env, ctx), ctx)
        # a ternary `b if test else o` whose branches share a z3 sort is one z3.If. Branches of different sorts
        # (a value-or-None idiom `x[i] if x else None`, or a mixed int/str) have no common z3.If: both are still
        # evaluated under their path conditions, so each is trap-checked, and the result is an opaque union -- a
        # bare return of it is trap-free, and any operation on it abstains (Unsupported -> UNKNOWN), so the union
        # never yields a false trap.
        def _ifexp(b, o):
            if z3.is_expr(b) and z3.is_expr(o):
                if b.sort() == o.sort():
                    return z3.If(t, b, o)
                if all(z3.is_int(x) or z3.is_bool(x) for x in (b, o)):   # bool and int share no sort: coerce both to int (False -> 0)
                    return z3.If(t, _as_int(b), _as_int(o))
            return _Opaque("ifexp")
        if ctx.traps is None:
            return _ifexp(ev(node.body, env, ctx), ev(node.orelse, env, ctx))
        old = ctx.pc
        ctx.pc = z3.And(old, t); b = ev(node.body, env, ctx)
        ctx.pc = z3.And(old, z3.Not(t)); o = ev(node.orelse, env, ctx)
        ctx.pc = old
        return _ifexp(b, o)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        name = node.func.id
        if name in env and isinstance(env[name], _NoneVal):  # calling a name bound to None raises TypeError: a trap
            if ctx.traps is not None:
                ctx.traps.append(ctx.pc)
            return _Opaque("nonecall")
        if name == "abs" and len(node.args) == 1:
            a = ev(node.args[0], env, ctx)
            if _is_fp(a):
                return z3.fpAbs(a)
            a = _as_int(a)
            return z3.If(a >= 0, a, -a)
        if name in ("bin", "hex", "oct") and name not in ctx.repo and len(node.args) == 1:
            a = ev(node.args[0], env, ctx)                    # bin / hex / oct of an int -> str; never a modeled trap
            if z3.is_expr(a) and (z3.is_int(a) or z3.is_bool(a)):
                _note_overapprox(ctx, name)
                return z3.FreshConst(_SS, name)
            raise Unsupported(f"{name}() of a non-integer value")
        if name in ("ascii", "format") and name not in ctx.repo and 1 <= len(node.args) <= 2:
            v = ev(node.args[0], env, ctx)                    # ascii(x) / format(x): a string, never traps;
            if name == "format" and len(node.args) == 2:      # format(x, spec) raises on an incompatible spec
                spec = ev(node.args[1], env, ctx)
                scalar = z3.is_expr(v) and (z3.is_int(v) or z3.is_bool(v) or _is_fp(v) or _is_str(v))
                ok = (isinstance(node.args[1], ast.Constant) and isinstance(node.args[1].value, str)
                      and scalar and _format_spec_safe(node.args[1].value, v))
                if not ok:
                    if _TRAPFREE and not (isinstance(node.args[1], ast.Constant)
                                          and isinstance(node.args[1].value, str)):
                        ctx.overapprox = True                 # a dynamic spec: assume well-formed (over-approx)
                        return z3.FreshConst(_SS, "format")
                    raise Unsupported("format() with a spec that may raise on this value")
            _note_overapprox(ctx, name)
            return z3.FreshConst(_SS, name)
        if name == "chr" and "chr" not in ctx.repo and len(node.args) == 1:
            a = _as_int(ev(node.args[0], env, ctx))           # chr(n): ValueError outside [0, 0x10FFFF]
            am = z3.simplify(a)
            if z3.is_int_value(am):                           # a constant codepoint folds to its exact character
                k = am.as_long()
                if 0 <= k <= _MAXCP:
                    return z3.StringVal(chr(k))
                if ctx.traps is not None:
                    ctx.traps.append(ctx.pc)                  # a constant out of range: always ValueError
                return z3.FreshConst(_SS, "chr")
            if ctx.traps is not None:
                ctx.traps.append(z3.And(ctx.pc, z3.Or(a < 0, a > _MAXCP)))
            if not _TRAPFREE:                                 # the range trap is exact; the codepoint is over-approximated
                _note_overapprox(ctx, "chr")
            r = _CHR(a)                                        # one character with codepoint a; round-trips with ord
            if ctx.facts is not None:
                ctx.facts.append(z3.Implies(z3.And(a >= 0, a <= _MAXCP),
                                            z3.And(z3.Length(r) == 1, _ORD(r) == a)))
            return r
        if name == "ord" and "ord" not in ctx.repo and len(node.args) == 1:
            a = ev(node.args[0], env, ctx)                    # ord(s): TypeError unless s is a length-1 string
            if _is_str(a):
                am = z3.simplify(a)
                if z3.is_string_value(am) and len(am.as_string()) == 1:   # a constant character folds to its codepoint
                    return z3.IntVal(ord(am.as_string()))
                if ctx.traps is not None:
                    ctx.traps.append(z3.And(ctx.pc, z3.Length(a) != 1))
                if not _TRAPFREE:                            # the length trap is exact; the codepoint is over-approximated
                    _note_overapprox(ctx, "ord")
                r = _ORD(a)                                    # in [0, 0x10FFFF] and round-trips with chr (single char)
                if ctx.facts is not None:
                    ctx.facts.append(z3.Implies(z3.Length(a) == 1,
                                                z3.And(r >= 0, r <= _MAXCP, _CHR(r) == a)))
                return r
            raise Unsupported("ord() of a non-string value")
        if name == "hash" and "hash" not in ctx.repo and len(node.args) == 1:
            a = ev(node.args[0], env, ctx)                    # hash of a hashable scalar / string / tuple -> int
            if z3.is_expr(a) or isinstance(a, tuple):
                _note_overapprox(ctx, "hash")
                return z3.FreshInt("hash")
            raise Unsupported("hash() of a possibly-unhashable value")
        if name == "int" and "int" not in ctx.repo:
            args = node.args
            kws = {k.arg: k.value for k in node.keywords if k.arg is not None}
            base_node = args[1] if len(args) == 2 else kws.get("base")
            base_ok = base_node is None or (isinstance(base_node, ast.Constant)
                                            and isinstance(base_node.value, int) and not isinstance(base_node.value, bool))
            if not args and not kws:
                return z3.IntVal(0)                           # int() -> 0
            if (1 <= len(args) <= 2 and set(kws) <= {"base"} and base_ok
                    and isinstance(args[0], ast.Constant) and isinstance(args[0].value, str)):
                # int(str_literal [, base]) parses exactly as CPython does (base positional or base=, default 10): a
                # valid (digits, base) pair has a known value, an invalid digit string or an out-of-range base (which
                # must be 0 or 2..36) always raises ValueError. (A base= keyword must use this base, not base 10.)
                base = base_node.value if base_node is not None else 10
                try:
                    return z3.IntVal(int(args[0].value, base))
                except ValueError:
                    if ctx.traps is not None:
                        ctx.traps.append(ctx.pc)
                    return z3.IntVal(0)                       # poison: never trusted once the trap fires
            if len(args) == 1 and not kws:
                a = ev(args[0], env, ctx)                      # the argument is trap-checked as it is evaluated
                if z3.is_expr(a) and (z3.is_int(a) or z3.is_bool(a)):
                    return _as_int(a)                         # int(int) / int(bool): exact, never traps
                if _is_fp(a) or (_TRAPFREE and isinstance(a, _Opaque)
                                 and not isinstance(a, (_SafeContainer, _DictParam, _DictLit, _MapVal))):
                    _note_overapprox(ctx, "int() of a float")    # truncation toward zero of a finite float --
                    return z3.FreshInt("int")                    # some int (REFUTED withheld; PROVED still sound)
                raise Unsupported("int() of a string, container, or unmodeled value (may raise ValueError/TypeError)")
            raise Unsupported("int() with an unmodeled signature (a non-constant base, or extra arguments)")
        if name == "float" and "float" not in ctx.repo and len(node.args) <= 1:
            if not node.args:
                return z3.FPVal(0.0, _F64)                    # float() -> 0.0
            if isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str):
                # float('1.5') / float('inf') / float('nan') is exactly CPython's parse: a valid literal is total
                # and its IEEE-754 value is known, an unparseable one (float('abc')) always raises ValueError.
                try:
                    return z3.FPVal(float(node.args[0].value), _F64)
                except ValueError:
                    if ctx.traps is not None:
                        ctx.traps.append(ctx.pc)
                    return z3.FPVal(0.0, _F64)                # poison: never trusted once the trap fires
            a = ev(node.args[0], env, ctx)                    # the argument is trap-checked as it is evaluated
            if _is_fp(a):
                return a                                      # float(float): identity
            if z3.is_expr(a) and (z3.is_int(a) or z3.is_bool(a)):
                return _to_fp(a)                              # float(int) / float(bool): the exact IEEE-754 value
            raise Unsupported("float() of a non-literal string or unmodeled value (may raise ValueError)")
        if name in ("bytes", "bytearray") and name not in ctx.repo and len(node.args) <= 1:
            # bytes(n) / bytearray(n) is n zero bytes -- ValueError on a negative count -- so the result is a byteslike
            # sequence of length n (its elements are valid bytes in [0, 255]). bytes()/bytearray() is empty; a bytes /
            # bytearray argument is copied (same length). A str / general iterable / opaque argument is declined.
            if not node.args:
                return _SafeContainer(name, byteslike=True, immutable=(name == "bytes"), length=z3.IntVal(0))
            a = ev(node.args[0], env, ctx)                    # the argument is trap-checked as it is evaluated
            if z3.is_expr(a) and (z3.is_int(a) or z3.is_bool(a)):
                n = _as_int(a)
                if ctx.traps is not None:                     # ValueError: negative count
                    ctx.traps.append(z3.And(ctx.pc, n < 0))
                return _SafeContainer(name, byteslike=True, immutable=(name == "bytes"),
                                      length=z3.If(n >= 0, n, z3.IntVal(0)))
            if isinstance(a, _SafeContainer) and a.byteslike:   # bytes(b) / bytearray(b): a copy of equal length
                return _SafeContainer(name, byteslike=True, immutable=(name == "bytes"), length=_container_len(a, ctx))
            raise Unsupported("bytes()/bytearray() of a string, iterable, or unmodeled value")
        if name == "bool" and "bool" not in ctx.repo and len(node.args) <= 1:
            if not node.args:
                return z3.BoolVal(False)                      # bool() -> False
            a = ev(node.args[0], env, ctx)                    # the argument is trap-checked as it is evaluated
            if z3.is_expr(a) and z3.is_bool(a):
                return a                                      # bool(bool): identity
            if z3.is_expr(a) and z3.is_int(a):
                return a != 0                                 # bool(int): nonzero
            if _is_fp(a):
                return z3.Not(z3.fpIsZero(a))                 # bool(float): nonzero (nan truthy, +-0.0 falsy)
            raise Unsupported("bool() of a string, container, or unmodeled value needs its truthiness; not modeled")
        if name == "str" and "str" not in ctx.repo and len(node.args) <= 1 and not node.keywords:
            # str() is the empty string; str(x) for a modeled value (number, bool, None, string, list/dict/
            # tuple) calls a builtin __str__ that cannot raise, so it is a fresh string of unknown content (the
            # over-approximation channel). A bare opaque object (a custom __str__ may raise) and str(bytes,
            # encoding) (UnicodeDecodeError) stay unmodeled.
            if not node.args:
                return z3.StringVal("")
            a = ev(node.args[0], env, ctx)                    # the argument is trap-checked as it is evaluated
            if type(a) is _Opaque:
                raise Unsupported("str() of an opaque object whose __str__ may raise")
            _note_overapprox(ctx, "str()")
            return z3.FreshConst(_SS, "str")
        if name == "range" and "range" not in ctx.repo and 1 <= len(node.args) <= 3 and not node.keywords:
            # range(...) used as a VALUE (the for-loop iterable form is desugared earlier, before ev sees it):
            # a sized, immutable integer sequence. Model it as a container carrying its EXACT length, so
            # len(range(n)) == n, an index bounds-checks precisely, and sum/iteration see a sized sequence.
            ra = [_as_int(ev(a, env, ctx)) for a in node.args]   # each argument is trap-checked as evaluated
            if not all(z3.is_int(x) for x in ra):
                raise Unsupported("range() needs integer arguments")
            if len(ra) == 1:
                start, stop, step = z3.IntVal(0), ra[0], z3.IntVal(1)
            elif len(ra) == 2:
                start, stop, step = ra[0], ra[1], z3.IntVal(1)
            else:
                start, stop, step = ra
            step = z3.simplify(step)                          # a negative literal is USub of a Constant: fold it
            if not z3.is_int_value(step):
                if _TRAPFREE:                                # a symbolic step: ValueError iff step == 0, length opaque
                    if ctx.traps is not None:
                        ctx.traps.append(z3.And(ctx.pc, step == 0))
                    return _SafeContainer("range", immutable=True)
                raise Unsupported("range() with a non-constant step")
            s = step.as_long()
            if s == 0:
                if ctx.traps is not None:
                    ctx.traps.append(ctx.pc)                  # range() arg 3 must not be zero: ValueError
                return _SafeContainer("range", immutable=True)   # a consumable value past the trap, so list(range(
                #                                                  0, 10, 0)) reaches the trap instead of choking
            # length = ceil((stop - start) / step) clamped at 0; dividing by a positive quantity (s or -s) makes
            # the floor identity floor((k + s - 1) / s) == ceil(k / s) exact, and the clamp handles the empty case.
            length = (stop - start + (s - 1)) / s if s > 0 else (start - stop + (-s - 1)) / (-s)
            length = z3.If(length > 0, length, z3.IntVal(0))
            return _SafeContainer("range", immutable=True, length=length)
        if name in ("set", "frozenset") and name not in ctx.repo and len(node.args) <= 1 and not node.keywords:
            # set(it) / frozenset(it): a sized, iterable, membership-queryable container that is not subscriptable.
            # Empty with no argument; an iterable argument is trap-checked; a non-iterable scalar abstains.
            if not node.args:
                return _SafeContainer(name, unindexable=True, length=z3.IntVal(0))
            x = ev(node.args[0], env, ctx)
            if (isinstance(x, (_SafeContainer, tuple, _DictParam, _DictLit, _MapVal, _DefaultDict, _Opaque))
                    or _is_str(x)):
                return _SafeContainer(name, unindexable=True)
            if BEST_EFFORT:                                  # assume the argument is iterable (lower trust)
                _best_effort_assume()
                return _SafeContainer(name, unindexable=True)
            raise Unsupported(f"{name}() of a possibly non-iterable value")
        if name == "tuple" and "tuple" not in ctx.repo and len(node.args) <= 1 and not node.keywords:
            # tuple(it): an immutable sized sequence -- a constant sequence is itself, else a container of its length.
            if not node.args:
                return ()
            x = ev(node.args[0], env, ctx)
            if isinstance(x, tuple):
                return x
            if isinstance(x, _SafeContainer):
                return _SafeContainer("tuple", immutable=True, length=_container_len(x, ctx))
            if _is_str(x):
                return _SafeContainer("tuple", immutable=True, length=z3.Length(x))
            if isinstance(x, (_DictParam, _DictLit, _MapVal, _DefaultDict, _Opaque)):
                return _SafeContainer("tuple", immutable=True)
            if BEST_EFFORT:                                  # assume the argument is iterable (lower trust)
                _best_effort_assume()
                return _SafeContainer("tuple", immutable=True)
            raise Unsupported("tuple() of a possibly non-iterable value")
        if name == "reversed" and name not in ctx.repo and len(node.args) == 1 and not node.keywords:
            # reversed(seq): an indexable sized sequence (list / str / tuple / range / bytes) gives a NEW sequence of
            # the SAME length (trap free, indexable, so list(reversed(xs)) decides). A set / frozenset is NOT
            # reversible (TypeError). A dict (reversible since 3.8) or an opaque iterable is reversed lazily (opaque).
            x = ev(node.args[0], env, ctx)
            if isinstance(x, _SafeContainer) and x.unindexable:
                if ctx.traps is not None:
                    ctx.traps.append(ctx.pc)                      # set / frozenset: reversed() raises TypeError
                return _Opaque("reversed")                        # poison: never trusted once the trap fires
            if isinstance(x, _SafeContainer):                     # list / bytes / range: a reversed sized sequence
                return _SafeContainer("reversed", byteslike=x.byteslike, length=_container_len(x, ctx), unsized=True)
            if _is_str(x):
                return _SafeContainer("reversed", length=z3.Length(x), unsized=True)
            if isinstance(x, tuple):                              # a list / tuple literal of known length
                return _SafeContainer("reversed", length=z3.IntVal(len(x)), unsized=True)
            if isinstance(x, (_DictParam, _DictLit, _MapVal, _DefaultDict, _Opaque)):
                return _Opaque("reversed")                        # dict (3.8+) / opaque iterable: lazy, trap free
            if BEST_EFFORT:
                _best_effort_assume()
                return _Opaque("reversed")
            raise Unsupported("reversed() of a possibly non-iterable value")
        if name in ("iter", "enumerate") and name not in ctx.repo and 1 <= len(node.args) <= 2 and not node.keywords:
            # iter / enumerate over an iterable: a for-loop over it havocs its targets. enumerate(seq) over a sized
            # container is a lazy iterator of (index, element) 2-tuples of the container's length, so list(enumerate(
            # seq)) sizes and an element unpacks; iter and other iterables stay opaque.
            x = ev(node.args[0], env, ctx)
            for a in node.args[1:]:
                ev(a, env, ctx)
            if name == "enumerate" and isinstance(x, _SafeContainer) and not x.unindexable and not x.unsized:
                return _SafeContainer("enumerate", length=_container_len(x, ctx), unsized=True, tuple_arity=2)
            if (isinstance(x, (_SafeContainer, tuple, _DictParam, _DictLit, _MapVal, _DefaultDict, _Opaque))
                    or _is_str(x)):
                return _Opaque(name)
            if BEST_EFFORT:                                  # assume the argument is iterable (lower trust)
                _best_effort_assume()
                return _Opaque(name)
            raise Unsupported(f"{name}() of a possibly non-iterable value")
        if name == "next" and "next" not in ctx.repo and 1 <= len(node.args) <= 2:
            # next(it[, default]): the yielded value (over-approximated); StopIteration is not a modeled trap.
            for a in node.args:
                ev(a, env, ctx)
            _note_overapprox(ctx, "next()")
            return _Opaque("next")
        if name in ("sorted", "list") and name not in ctx.repo and len(node.args) == 1 and (
                not node.keywords or (name == "sorted" and all(kw.arg in ("reverse", "key") for kw in node.keywords))):
            # sorted(it[, reverse][, key=f]) / list(it): a sized container of the iterable's length. reverse= is
            # trap-checked then ignored; a key= lambda is applied to a freely-chosen element (per-element traps
            # surface; a bare builtin key declines). A non-iterable argument is declined.
            x = ev(node.args[0], env, ctx)                    # the iterable is trap-checked as it is evaluated
            for kw in node.keywords:
                if kw.arg == "key":
                    _apply_key_callable(kw.value, x, env, ctx)   # surface the key callable's per-element traps
                else:
                    ev(kw.value, env, ctx)                    # sorted(..., reverse=cond): trap-check the flag value
            if isinstance(x, _SafeContainer):
                n = _container_len(x, ctx)
            elif _is_str(x):
                # list(s) / sorted(s) of a string is a list of 1-char STRINGS (not ints): a _StrSeq, so an element is a
                # string (s[i].upper() works, s[i] + 1 is a refutable TypeError) and ''.join(sorted(s)) proves.
                return _StrSeq(name, length=z3.Length(x))
            elif isinstance(x, tuple):
                n = z3.IntVal(len(x))
            elif isinstance(x, (_DictParam, _DictLit, _MapVal)):
                n = z3.FreshInt("itlen")
                if ctx.facts is not None:
                    ctx.facts.append(n >= 0)
            elif BEST_EFFORT:                                # assume the argument is iterable (lower trust)
                _best_effort_assume()
                n = z3.FreshInt("be_itlen")
                if ctx.facts is not None:
                    ctx.facts.append(n >= 0)
            else:
                raise Unsupported(f"{name}() of a possibly non-iterable value")
            ta = x.tuple_arity if isinstance(x, _SafeContainer) else None   # list(zip / enumerate / items) keeps the
            return _SafeContainer(name, length=n, tuple_arity=ta)            # fixed-arity tuple element
        if name == "print" and "print" not in ctx.repo:
            # print(...) writes str() of each argument and returns None, raising no modeled trap (the same
            # assume-str-safe over-approximation an f-string interpolation already makes). Each argument and
            # keyword (sep / end / file / flush) is trap-checked as it is evaluated; the result is None.
            for a in node.args:
                ev(a.value if isinstance(a, ast.Starred) else a, env, ctx)
            for kw in node.keywords:
                ev(kw.value, env, ctx)
            return _NoneVal()
        if name == "sum" and "sum" not in ctx.repo and 1 <= len(node.args) <= 2:
            if isinstance(node.args[0], ast.GeneratorExp):   # sum of a generator: trap-check the element (loop
                ev(node.args[0], env, ctx)                   # var havoc'd to an int element), the sum over-approximated
                if len(node.args) == 2:
                    ev(node.args[1], env, ctx)
                _note_overapprox(ctx, "sum() over a generator")
                return z3.FreshInt("sum")
            seq = ev(node.args[0], env, ctx)
            start = ev(node.args[1], env, ctx) if len(node.args) == 2 else z3.IntVal(0)
            if isinstance(seq, tuple):                       # sum of a constant-length sequence: exact
                vals = [start, *seq]
                if any(_is_fp(v) for v in vals):
                    acc = _to_fp(vals[0])
                    for v in vals[1:]:
                        acc = acc + _to_fp(v)
                else:
                    acc = _as_int(vals[0])
                    for v in vals[1:]:
                        acc = acc + _as_int(v)
                return acc
            if _TRAPFREE and isinstance(seq, _SafeContainer):   # the sum of an arbitrary container is an arbitrary int
                return z3.Int("__sum_" + seq.name)              # that never traps; a stable named int (not a withheld
                #                                                 over-approximation) so a guard `if sum(xs): ...`
                #                                                 constrains it, and a division by it or by an
                #                                                 independent len(xs) refutes -- both sound, since the
                #                                                 sum can be zero (the empty list, or [1, -1])
            raise Unsupported("sum() over an unmodeled iterable")
        if name == "sqrt" and len(node.args) == 1 and name not in ctx.repo:   # from math import sqrt
            return _sqrt_model(ev(node.args[0], env, ctx), ctx)
        if name in _TRANSCENDENTAL and len(node.args) == 1 and name not in ctx.repo:   # from math import sin, ...
            return _transcendental(name, ev(node.args[0], env, ctx), ctx)
        if name in _MATH_FUNCS and name not in ctx.repo and name not in env:   # from math import floor, gcd, ...
            res = _math_call(name, [ev(a, env, ctx) for a in node.args], ctx)
            if res is not None:
                return res
        if name in ("min", "max") and node.args:
            if len(node.args) == 1:                          # min/max over ONE iterable, not over values
                seq = ev(node.args[0], env, ctx)             # only a non-empty literal is total and exact;
                _kw = {k.arg for k in node.keywords}
                if isinstance(seq, tuple) and seq:           # a non-empty literal is total and exact
                    vals = list(seq)
                elif isinstance(seq, tuple):                 # an empty literal: min([]) raises ValueError; a
                    _has_dflt = False; dflt = None           # default= makes it total, returning that default
                    for k in node.keywords:
                        if k.arg == "default":
                            dflt = ev(k.value, env, ctx); _has_dflt = True
                        else:
                            ev(k.value, env, ctx)
                    if _has_dflt:
                        return dflt
                    if _TRAPFREE and ctx.traps is not None:
                        ctx.traps.append(ctx.pc)             # min/max of an empty sequence always raises
                        return z3.FreshInt(name)
                    raise Unsupported(f"{name}() of an empty sequence raises ValueError")
                elif (_TRAPFREE and isinstance(seq, _SafeContainer) and ctx.traps is not None):
                    keynode = None                           # an opaque sequence parameter: ValueError when empty,
                    for k in node.keywords:                  # against its symbolic length, so a len() / truthiness
                        if k.arg == "key":                   # guard proves it safe; a default= never raises
                            keynode = k.value
                        else:
                            ev(k.value, env, ctx)
                    if keynode is not None:                  # a key= callable's per-element traps refute (10 // x on a
                        _apply_key_callable(keynode, seq, env, ctx)   # zero element); a bare builtin key declines
                    if "default" not in _kw:
                        ctx.traps.append(z3.And(ctx.pc, _container_len(seq, ctx) <= 0))
                    return z3.FreshInt(name)                 # an arbitrary element of the sequence (or the default)
                else:                                        # an empty or otherwise opaque iterable may be empty
                    raise Unsupported(f"{name}() over a possibly-empty iterable is not modeled (empty raises ValueError)")
            else:
                vals = [ev(a, env, ctx) for a in node.args]
            vals = [_to_fp(v) for v in vals] if any(_is_fp(v) for v in vals) else [_as_int(v) for v in vals]
            acc = vals[0]
            for x in vals[1:]:
                acc = z3.If(x < acc, x, acc) if name == "min" else z3.If(x > acc, x, acc)
            return acc
        if name == "round" and 1 <= len(node.args) <= 2:
            x = ev(node.args[0], env, ctx)
            if len(node.args) == 2:
                ev(node.args[1], env, ctx)               # the ndigits argument (trap-checked)
            if isinstance(x, (_Opaque, _Closure, _Lambda, _FuncRef, _Complex)) or isinstance(x, tuple):
                if _TRAPFREE and not isinstance(x, tuple):
                    return z3.FreshInt("round")          # round of an opaque number raises no trap
                raise Unsupported("round of an unmodeled value")
            if not _is_fp(x):
                return _as_int(x)                        # round(int) and round(int, n) are the integer itself
            # round(float): the nearest integer (ties to even); round(float, n): a float. The exact value is
            # CPython's correctly-rounded result, left as a fresh term of the right type (an over-approximation).
            return z3.FreshConst(_F64, "round") if len(node.args) == 2 else z3.FreshInt("round")
        if name == "divmod" and len(node.args) == 2:         # divmod(a, b) == (a // b, a % b), same zero-divisor trap
            fd = ast.copy_location(ast.BinOp(left=node.args[0], op=ast.FloorDiv(), right=node.args[1]), node)
            md = ast.copy_location(ast.BinOp(left=node.args[0], op=ast.Mod(), right=node.args[1]), node)
            return (ev(fd, env, ctx), ev(md, env, ctx))      # reuses the Rocq-verified // and % encoding and its trap
        if name == "pow" and name not in ctx.repo and len(node.args) in (2, 3):
            p = ast.copy_location(ast.BinOp(left=node.args[0], op=ast.Pow(), right=node.args[1]), node)
            if len(node.args) == 3:                          # pow(a, b, m) == (a ** b) % m -- the three-arg modular
                p = ast.copy_location(ast.BinOp(left=p, op=ast.Mod(), right=node.args[2]), node)   # form, m == 0 traps
            return ev(p, env, ctx)                           # reuses the modeled ** (constant exponent) and % encoding
        if name == "len" and len(node.args) == 1:
            a = ev(node.args[0], env, ctx)
            if isinstance(a, tuple):
                return z3.IntVal(len(a))
            if _is_str(a):
                return z3.Length(a)
            if isinstance(a, _StrSeq):
                if a.unsized:                                # a lazy map(str, ...) iterator has no len(): TypeError
                    if ctx.traps is not None:
                        ctx.traps.append(ctx.pc)
                    return z3.FreshInt("maplen")
                if a.length is not None:                     # split(sep) is >= 1 part, so split(sep)[0] / [-1] decide
                    return a.length
                if ctx.facts is not None:
                    _note_overapprox(ctx, "len of a split result")
                    r = z3.FreshInt("splitlen")
                    ctx.facts.append(r >= 0)
                    return r
                if _TRAPFREE:
                    return z3.FreshInt("hlen")
                raise Unsupported("len of a split result needs the over-approximation channel")
            if isinstance(a, _NoneVal):                      # len(None): None is not sized -- TypeError, every input
                if ctx.traps is not None:
                    ctx.traps.append(ctx.pc)
                return z3.FreshInt("nonelen")
            if isinstance(a, _NdArray):                      # len(ndarray): shape[0] (a 0-d array is not sized: TypeError)
                if not a.shape:
                    if ctx.traps is not None:
                        ctx.traps.append(ctx.pc)
                    return z3.FreshInt("ndlen")
                return a.shape[0]
            if _TRAPFREE and isinstance(a, _SafeContainer):  # a container parameter: a stable nonneg length,
                if a.unsized:                                # a lazy iterator (zip / chain / ...) has no len(): the
                    if ctx.traps is not None:                # an iterator has no len(): TypeError
                        ctx.traps.append(ctx.pc)
                    return z3.FreshInt("iterlen")
                return _container_len(a, ctx)                # shared with the bounds check on a[i]
            if _TRAPFREE and isinstance(a, _DictParam):       # len(d) for a dict parameter: a stable by-name nonneg
                return _container_len(a, ctx)                 # length, shared with its d.keys() / d.values() view
            if _TRAPFREE and isinstance(a, _Opaque):         # other opaque container (view / attribute / call result):
                r = z3.FreshInt("hlen")                      # len() is nonnegative, so 10 // (len(d) + 1) is trap free,
                if ctx.facts is not None:                    # not a spurious ZeroDivisionError
                    ctx.facts.append(r >= 0)
                return r
            if BEST_EFFORT:                                  # len of an unmodeled value: a nonneg int (lower trust)
                _best_effort_assume()
                return z3.FreshInt("be_len")
            raise Unsupported("len of a non-string, non-tuple value")
        if name in ("any", "all") and len(node.args) == 1:   # over a constant-length tuple or a concrete generator
            arg = node.args[0]
            if isinstance(arg, ast.GeneratorExp):            # any/all(p(x) for x in <iterable>)
                conds = _spec_quantify(arg, env, ctx)
                if conds is not None:                        # a concrete iterable: unroll, exact
                    agg = z3.Or(*conds) if name == "any" else z3.And(*conds)
                    return agg if conds else z3.BoolVal(name == "all")
                if _TRAPFREE:                                # a symbolic container: trap-check the predicate (loop var
                    ev(arg, env, ctx)                        # havoc'd to an int element), the boolean over-approximated
                    _note_overapprox(ctx, "%s() over a container" % name)
                    return z3.FreshConst(z3.BoolSort(), name)
                raise Unsupported(f"{name}(...) over a non-enumerable (symbolic-length) iterable")
            seq = ev(arg, env, ctx)
            if isinstance(seq, tuple):
                conds = [_as_bool(x, ctx) for x in seq]
                agg = z3.Or(*conds) if name == "any" else z3.And(*conds)
                return agg if conds else (z3.BoolVal(name == "all"))
            if _TRAPFREE and isinstance(seq, _SafeContainer):   # any / all over a container: element truthiness never
                _note_overapprox(ctx, "%s() over a container" % name)   # traps, so the result is over-approximated
                return z3.FreshConst(z3.BoolSort(), name)
            raise Unsupported(f"{name}() over a non-tuple iterable")
        if name == "isinstance" and len(node.args) == 2:     # static type test from the value's sort
            v = ev(node.args[0], env, ctx)
            if not (z3.is_expr(v) or isinstance(v, tuple)):   # an opaque/unmodeled value: its type is unknown,
                if _TRAPFREE:                                 # isinstance never traps; the result is arbitrary
                    return z3.FreshConst(z3.BoolSort(), "hi")
                raise Unsupported("isinstance of an unmodeled value")   # so do not answer (False could mask a trap)
            tnode = node.args[1]
            tnames = [t.id for t in (tnode.elts if isinstance(tnode, ast.Tuple) else [tnode]) if isinstance(t, ast.Name)]
            ok = (("int" in tnames and (z3.is_int(v) or z3.is_bool(v)))
                  or ("bool" in tnames and z3.is_bool(v))
                  or ("float" in tnames and _is_fp(v))
                  or ("str" in tnames and _is_str(v)))
            return z3.BoolVal(bool(ok))
        if name == "map" and len(node.args) == 2:            # map(f, constant tuple) -> a tuple
            seq = ev(node.args[1], env, ctx)
            if not isinstance(seq, tuple):
                fn = node.args[0]                            # map(str, X) / map(repr, X) over a known iterable yields a
                if (isinstance(fn, ast.Name) and fn.id in ("str", "repr") and fn.id not in env and fn.id not in ctx.repo
                        and (isinstance(seq, (_SafeContainer, _StrSeq, _DictParam, _DictLit, _MapVal)) or _is_str(seq))):
                    return _StrSeq("map", unsized=True)      # lazy iterator of strings (str / repr is total), so
                    #                                          sep.join(map(str, X)) is a trap-free string
                if BEST_EFFORT:                              # map over an unmodeled iterable: opaque (lower trust)
                    ev(node.args[0], env, ctx)
                    _best_effort_assume()
                    return _Opaque("be_map")
                raise Unsupported("map() over a non-tuple iterable")
            fnode = node.args[0]
            lam = ev(fnode, env, ctx) if isinstance(fnode, ast.Lambda) else \
                (env.get(fnode.id) if isinstance(fnode, ast.Name) else None)
            out = []
            for x in seq:
                if isinstance(lam, _Lambda):                 # apply a lambda value to each element
                    le = dict(lam.env); le[lam.params[0]] = x
                    out.append(ev(lam.body, le, ctx))
                elif isinstance(fnode, ast.Name) and fnode.id in ctx.repo:
                    out.append(ctx.inline(fnode.id, [x]))    # apply a repo function to each element
                else:
                    raise Unsupported("map() function is not a modeled callable")
            return tuple(out)
        if name == "zip" and "zip" not in ctx.repo:
            parts = [ev(arg, env, ctx) for arg in node.args]   # trap-check each iterable argument
            _strict = False
            for kw in node.keywords:
                ev(kw.value, env, ctx)                       # a zip(..., strict=...) keyword value
                if kw.arg == "strict" and not (isinstance(kw.value, ast.Constant) and kw.value.value is False):
                    _strict = True                           # strict=True / non-literal: a length mismatch raises on
                    #                                          consumption, so do not size it -- keep it lazy/opaque
            if parts and not _strict and all(isinstance(p, _SafeContainer) or _is_str(p) or isinstance(p, tuple)
                                             for p in parts):
                # zip stops at the SHORTEST argument, so list(zip(a, b, ...)) has the minimum length (trap free; the
                # elements are opaque tuples). A non-sized argument keeps it an opaque, lazily-consumed iterable.
                lens = [_container_len(p, ctx) if isinstance(p, _SafeContainer)
                        else z3.Length(p) if _is_str(p) else z3.IntVal(len(p)) for p in parts]
                m = lens[0]
                for ln in lens[1:]:
                    m = z3.If(ln < m, ln, m)
                return _SafeContainer("zip", length=m, unsized=True, tuple_arity=len(parts))   # elements are k-tuples
            if any(_definitely_not_iterable(p) for p in parts) and not BEST_EFFORT:
                raise Unsupported("zip() of a possibly non-iterable value")   # a scalar argument raises TypeError,
                #                                                               as enumerate() over a scalar declines
            return _Opaque("zip")                            # an iterable of tuples; a for-loop over it havocs the targets
        if name == "Fraction" and 1 <= len(node.args) <= 2:  # exact rational over Z3 Real
            num = _to_real(ev(node.args[0], env, ctx))
            if len(node.args) == 1:
                return num
            den = _to_real(ev(node.args[1], env, ctx))
            if ctx.traps is not None:
                ctx.traps.append(z3.And(ctx.pc, den == 0))
            return num / den
        if name == "complex" and 1 <= len(node.args) <= 2:
            re = _to_fp(ev(node.args[0], env, ctx))
            im = _to_fp(ev(node.args[1], env, ctx)) if len(node.args) == 2 else z3.FPVal(0.0, _F64)
            return _Complex(re, im)
        if name == "dict" and not node.args and not node.keywords and "dict" not in ctx.repo:
            return _MapVal()                                 # dict() -> an empty tracked dict
        if name in _COLLECTIONS_CTORS and name not in ctx.repo and name not in env:
            res = _collections_ctor(name, node, env, ctx)    # the bare imported name (from collections import ...)
            if res is not None:
                return res
        if ctx.summaries is not None and name in ctx.summaries:    # call -> summary subgoal
            argvals = [ev(a, env, ctx) for a in node.args]
            r = z3.Int(f"_cr{len(ctx.callvars)}"); ctx.callvars.append(r)
            ctx.callsub.append(ctx.summaries[name](*argvals, r))
            return r
        if name in ctx.repo:
            _node0 = _parse(ctx.repo[name]).body[0]
            if isinstance(_node0, ast.ClassDef):                 # a repo class: model its constructor (an opaque
                _eval_args(node.args, env, ctx)                  # instance), with the arguments trap-checked and
                for kw in node.keywords:                         # __init__ confirmed trap free (a dataclass-style
                    ev(kw.value, env, ctx)                       # constructor); a non-trivial __init__ abstains
                _init = next((m for m in _node0.body if isinstance(m, ast.FunctionDef) and m.name == "__init__"), None)
                if _init is not None and not _init_trapfree(_init):
                    raise Unsupported(f"constructor {name}(...) has a non-trivial __init__")
                return _Opaque(name.lower())
            return _call_repo(name, _bind_call(_node0, node, env, ctx), ctx)
        if name in _STDLIB:                                  # imported stdlib function (bare name)
            return _STDLIB[name](_eval_args(node.args, env, ctx))
        if _TRAPFREE and name == "getattr" and 2 <= len(node.args) <= 3 \
                and isinstance(node.args[1], ast.Constant) and isinstance(node.args[1].value, str):
            obj = ev(node.args[0], env, ctx)                 # getattr(o, "x"[, default]) with a constant name: model as
            if len(node.args) == 3:                          # the field o.x (a stable value, duck-typed numeric in
                ev(node.args[2], env, ctx)                   # arithmetic), so arithmetic on it decides; default trap-checked
            b = getattr(obj, "name", None)
            return _FieldVal(b + "." + node.args[1].value) if b is not None else _Opaque("getattr")
        if _TRAPFREE and name in _SAFE_BUILTINS_TF:          # getattr / type / print / ... raise no modeled trap
            _eval_args(node.args, env, ctx)                  # arguments are still trap-checked
            for kw in node.keywords:
                ev(kw.value, env, ctx)
            return _Opaque("call")
        if _TRAPFREE and name in _STDLIB_TF_BARE and name not in env:   # a bare-imported trap-free stdlib function
            _eval_args(node.args, env, ctx)                  # (from os.path import dirname); arguments trap-checked
            for kw in node.keywords:
                ev(kw.value, env, ctx)
            return _safe_stdlib_result(next(q for q in _STDLIB_TF if q.split(".")[-1] == name))
        if BEST_EFFORT:                                      # assume the unmodeled call is well-behaved (tainted)
            _eval_args(node.args, env, ctx)
            for kw in node.keywords:
                ev(kw.value, env, ctx)
            _best_effort_assume()
            return _Opaque("besteffort")
        raise Unsupported(f"unmodeled call {name}(...) at line {getattr(node, 'lineno', '?')}")
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
        if (isinstance(node.func.value, ast.Attribute) and isinstance(node.func.value.value, ast.Name)
                and node.func.value.value.id == "itertools" and node.func.value.attr == "chain"
                and node.func.attr == "from_iterable" and "itertools" not in env and len(node.args) == 1):
            # itertools.chain.from_iterable(xss): a lazy iterator over the concatenated inner iterables. Its length is
            # the unknown sum of inner lengths (a fresh nonnegative int); the result is an unsized iterator.
            ev(node.args[0], env, ctx)                       # trap-check the outer iterable
            n = z3.FreshInt("chainfi")
            if ctx.facts is not None:
                ctx.facts.append(n >= 0)
            return _SafeContainer("chainfi", length=n, unsized=True)
        if (isinstance(node.func.value, ast.Attribute) and isinstance(node.func.value.value, ast.Name)
                and node.func.value.value.id == "os" and node.func.value.attr == "path" and "os" not in env):
            # os.path string functions never raise on str input. split / splitext / splitdrive return a 2-tuple of
            # strings; basename / dirname / join / normpath / normcase / commonprefix return a string; isabs / exists /
            # isfile / isdir / islink / lexists / ismount return a bool. Filesystem-raising ones (getsize, ...) decline.
            ospm = node.func.attr
            if ospm in ("split", "splitext", "splitdrive", "basename", "dirname", "join", "normpath", "normcase",
                        "commonprefix", "isabs", "exists", "isfile", "isdir", "islink", "lexists", "ismount"):
                for a in node.args:
                    ev(a.value if isinstance(a, ast.Starred) else a, env, ctx)   # trap-check arguments
                for kw in node.keywords:
                    ev(kw.value, env, ctx)
                if ospm in ("split", "splitext", "splitdrive"):
                    return (z3.FreshConst(z3.StringSort(), "osp_a"), z3.FreshConst(z3.StringSort(), "osp_b"))
                if ospm in ("isabs", "exists", "isfile", "isdir", "islink", "lexists", "ismount"):
                    return z3.FreshConst(z3.BoolSort(), "osp_b")
                return z3.FreshConst(z3.StringSort(), "osp")
        if isinstance(node.func.value, ast.Name):            # module function: math.fabs(x), ...
            qual = node.func.value.id + "." + node.func.attr
            if qual == "math.sqrt" and len(node.args) == 1:
                return _sqrt_model(ev(node.args[0], env, ctx), ctx)
            if qual == "math.pow" and len(node.args) == 2:   # always a float, with its exact domain trap
                res = _math_call("pow", [ev(a, env, ctx) for a in node.args], ctx)
                if res is not None:
                    return res
            if node.func.value.id == "math" and node.func.attr in _TRANSCENDENTAL and len(node.args) == 1:
                return _transcendental(node.func.attr, ev(node.args[0], env, ctx), ctx)
            if (node.func.value.id == "math" and node.func.attr == "log"
                    and "math" not in env and len(node.args) == 2 and not node.keywords):
                # math.log(x, base) = log(x)/log(base): a ValueError when x <= 0 or base <= 0, a ZeroDivisionError
                # when base == 1 (log(1) is a zero divisor). The domain trap goes in unconditionally (as the single-
                # argument log does), so an unguarded call refutes and a guard (x > 0 and base > 0, base != 1) proves;
                # the value is an arbitrary double (over-approximated for prove).
                xa = _to_fp(ev(node.args[0], env, ctx))
                ba = _to_fp(ev(node.args[1], env, ctx))
                if ctx.traps is not None:
                    ctx.traps.append(z3.And(ctx.pc, z3.Or(z3.fpLEQ(xa, z3.FPVal(0.0, _F64)),
                                                          z3.fpLEQ(ba, z3.FPVal(0.0, _F64)),
                                                          z3.fpEQ(ba, z3.FPVal(1.0, _F64)))))
                if not _TRAPFREE:
                    _note_overapprox(ctx, "math.log (2-argument)")
                return z3.FreshConst(_F64, "log2arg")
            if node.func.value.id == "math" and node.func.attr in _MATH_FUNCS and "math" not in env:
                res = _math_call(node.func.attr, [ev(a, env, ctx) for a in node.args], ctx)
                if res is not None:
                    return res
            if (node.func.value.id == "math" and node.func.attr == "isclose"
                    and "math" not in env and len(node.args) == 2 and not node.keywords):
                # math.isclose(a, b) -> a bool, total over numbers with the default (non-negative) tolerances. The two
                # values are trap-checked and required to be numeric; the result is an arbitrary bool. (A rel_tol /
                # abs_tol keyword, which could be a negative-tolerance ValueError, is declined.)
                a0 = ev(node.args[0], env, ctx)
                a1 = ev(node.args[1], env, ctx)
                if not all((z3.is_expr(v) and (z3.is_int(v) or z3.is_bool(v))) or _is_fp(v) or _is_real(v)
                           for v in (a0, a1)):
                    raise Unsupported("math.isclose of a non-numeric value")
                return _b01(z3.FreshConst(z3.BoolSort(), "isclose"))
            if node.func.value.id in ("np", "numpy") and node.func.attr in _NP_ARRAY_CTORS:
                return _np_array_ctor(node.func.attr, node, env, ctx)
            if node.func.value.id == "torch" and node.func.attr in _TORCH_CTORS and "torch" not in env:
                res = _torch_tensor_ctor(node.func.attr, node, env, ctx)
                if res is not None:
                    return res
            if node.func.value.id in ("torch", "np", "numpy") and node.func.attr in _TORCH_FUNCS \
                    and node.func.value.id not in env:
                res = _torch_func(node.func.attr, node, env, ctx)   # cat / matmul / where / a reduction over a tensor
                if res is not None:                                 # (a scalar / non-tensor arg falls through to _STDLIB)
                    return res
            if node.func.value.id in ("pd", "pandas") and node.func.attr in _PANDAS_CTORS \
                    and node.func.value.id not in env:
                res = _pandas_ctor(node.func.attr, node, env, ctx)
                if res is not None:
                    return res
            if node.func.value.id == "collections" and node.func.attr in _COLLECTIONS_CTORS \
                    and "collections" not in env:
                res = _collections_ctor(node.func.attr, node, env, ctx)
                if res is not None:
                    return res
            if (node.func.value.id == "itertools" and node.func.attr == "chain"
                    and "itertools" not in env and not node.keywords):
                # itertools.chain(a, b, ...) concatenates its iterables lazily. Consuming it is trap free when each
                # argument is a known iterable (a sized sequence), and the chain then has the summed length -- so a
                # later len() / list() / index into list(chain(...)) decides. A non-sized (possibly non-iterable)
                # argument is declined.
                parts = [ev(a, env, ctx) for a in node.args]   # each argument trap-checked as it is evaluated
                if all(isinstance(p, _SafeContainer) or _is_str(p) or isinstance(p, tuple) for p in parts):
                    total = z3.IntVal(0)
                    for p in parts:
                        total = total + (_container_len(p, ctx) if isinstance(p, _SafeContainer)
                                         else z3.Length(p) if _is_str(p) else z3.IntVal(len(p)))
                    return _SafeContainer("chain", length=total, unsized=True)
                return _Opaque("chain")                        # lazy construction raises nothing; consuming an opaque
                #                                                argument (list(chain(...))) then abstains, as before
            if (node.func.value.id == "itertools" and node.func.attr == "repeat"
                    and "itertools" not in env and len(node.args) == 2 and not node.keywords):
                # itertools.repeat(x, count) yields `count` copies (a negative count gives none), so list(repeat(x, n))
                # has length max(n, 0) -- trap free for an integer count. repeat(x) without a count is infinite and is
                # left opaque (consuming it would not terminate).
                ev(node.args[0], env, ctx)                     # the repeated value is trap-checked
                cnt = ev(node.args[1], env, ctx)
                if z3.is_expr(cnt) and (z3.is_int(cnt) or z3.is_bool(cnt)):
                    k = _as_int(cnt)
                    return _SafeContainer("repeat", length=z3.If(k >= 0, k, z3.IntVal(0)), unsized=True)
                raise Unsupported("itertools.repeat with a non-integer count")
            if (node.func.value.id == "itertools" and node.func.attr == "islice"
                    and "itertools" not in env and len(node.args) == 2 and not node.keywords):
                # itertools.islice(it, stop): the first `stop` elements (stop=None -> all of it). For a sized iterable
                # it is trap free with length min(len(it), stop) when stop is a non-negative int (a negative stop is a
                # ValueError); stop=None gives len(it). A non-sized iterable or the start/stop/step form is declined.
                it = ev(node.args[0], env, ctx)
                stop = ev(node.args[1], env, ctx)
                if not (isinstance(it, _SafeContainer) or _is_str(it) or isinstance(it, tuple)):
                    raise Unsupported("itertools.islice of a non-sized iterable")
                n = (_container_len(it, ctx) if isinstance(it, _SafeContainer)
                     else z3.Length(it) if _is_str(it) else z3.IntVal(len(it)))
                if isinstance(node.args[1], ast.Constant) and node.args[1].value is None:
                    return _SafeContainer("islice", length=n, unsized=True)   # islice(it, None) -> all of it
                if z3.is_expr(stop) and z3.is_int(stop):
                    if ctx.traps is not None:
                        ctx.traps.append(z3.And(ctx.pc, stop < 0))   # ValueError: a negative stop
                    return _SafeContainer("islice", length=z3.If(stop < 0, z3.IntVal(0),
                                                                  z3.If(stop < n, stop, n)), unsized=True)   # min(stop, len)
                raise Unsupported("itertools.islice with a non-integer stop")
            if (node.func.value.id == "itertools" and node.func.attr == "zip_longest"
                    and "itertools" not in env):
                # itertools.zip_longest(a, b, ..., fillvalue=...) pads to the LONGEST argument, so list(zip_longest(...))
                # has the MAXIMUM length of its sized arguments (trap free; elements are opaque tuples) -- the dual of
                # zip's minimum. The fillvalue keyword is benign. A non-sized argument keeps it opaque.
                parts = [ev(a, env, ctx) for a in node.args]
                for kw in node.keywords:
                    ev(kw.value, env, ctx)                     # fillvalue is trap-checked
                if parts and all(isinstance(p, _SafeContainer) or _is_str(p) or isinstance(p, tuple) for p in parts):
                    m = None
                    for p in parts:
                        ln = (_container_len(p, ctx) if isinstance(p, _SafeContainer)
                              else z3.Length(p) if _is_str(p) else z3.IntVal(len(p)))
                        m = ln if m is None else z3.If(ln > m, ln, m)
                    return _SafeContainer("zip_longest", length=m, unsized=True)
                return _Opaque("zip_longest")
            if (node.func.value.id == "itertools" and node.func.attr == "product"
                    and "itertools" not in env and not node.keywords):
                # itertools.product(a, b, ...) is the cartesian product, so list(product(...)) has length equal to the
                # PRODUCT of the argument lengths (trap free; product() with no args is the single empty tuple, length
                # 1). A non-sized argument keeps it an opaque, lazily-consumed iterable.
                parts = [ev(a, env, ctx) for a in node.args]
                if all(isinstance(p, _SafeContainer) or _is_str(p) or isinstance(p, tuple) for p in parts):
                    total = z3.IntVal(1)
                    for p in parts:
                        total = total * (_container_len(p, ctx) if isinstance(p, _SafeContainer)
                                         else z3.Length(p) if _is_str(p) else z3.IntVal(len(p)))
                    return _SafeContainer("product", length=total, unsized=True)
                return _Opaque("product")
            if (node.func.value.id == "itertools" and node.func.attr == "pairwise"
                    and "itertools" not in env and len(node.args) == 1 and not node.keywords):
                # itertools.pairwise(it): consecutive overlapping 2-tuples, so its length is max(len(it) - 1, 0); a
                # lazy iterator of 2-tuples.
                it = ev(node.args[0], env, ctx)
                if isinstance(it, _SafeContainer) and not it.unindexable:
                    n = _container_len(it, ctx)
                elif _is_str(it):
                    n = z3.Length(it)
                else:
                    raise Unsupported("itertools.pairwise of a non-sized iterable")
                return _SafeContainer("pairwise", length=z3.If(n - 1 >= 0, n - 1, z3.IntVal(0)),
                                      unsized=True, tuple_arity=2)
            if (node.func.value.id == "itertools" and node.func.attr == "accumulate"
                    and "itertools" not in env and 1 <= len(node.args) <= 2 and not node.keywords):
                # itertools.accumulate(it[, func]) yields len(it) running accumulations (a lazy iterator). The default
                # (add) is trap free; a positional func lambda is applied to a freely-chosen (acc, element) pair so a
                # trapping func (a // b) refutes. Modeled for a symbolic container.
                it = ev(node.args[0], env, ctx)
                if isinstance(it, _SafeContainer):
                    if len(node.args) == 2:
                        fn = node.args[1]
                        acc = _container_element(it, ctx)
                        elem = _container_element(it, ctx)
                        saved = ctx.pc
                        ctx.pc = z3.And(ctx.pc, _container_len(it, ctx) >= 2)   # func runs only on >= 2 elements
                        try:
                            _apply_fold_fn(fn, acc, elem, env, ctx)
                        finally:
                            ctx.pc = saved
                    return _SafeContainer("accumulate", length=_container_len(it, ctx), unsized=True)
                raise Unsupported("itertools.accumulate over a non-container iterable")
            if (node.func.value.id == "functools" and node.func.attr == "reduce"
                    and "functools" not in env and 2 <= len(node.args) <= 3 and not node.keywords):
                # functools.reduce(f, it[, init]): apply f to a freely-chosen (acc, element) pair so a trapping step
                # (a // b) refutes and a total step proves; result opaque. No init + empty iterable is a TypeError.
                # Modeled only for a symbolic container (a concrete tuple would need a precise fold); f a 2-arg lambda.
                seq = ev(node.args[1], env, ctx)
                init = ev(node.args[2], env, ctx) if len(node.args) == 3 else None
                fn = node.args[0]
                if isinstance(seq, _SafeContainer):
                    acc = init if init is not None else _container_element(seq, ctx)
                    elem = _container_element(seq, ctx)
                    saved = ctx.pc
                    ctx.pc = z3.And(ctx.pc, _container_len(seq, ctx) >= 1)   # f runs only on a non-empty iterable
                    try:
                        _apply_fold_fn(fn, acc, elem, env, ctx)   # surface a per-step trap (a // b on a zero element)
                    finally:
                        ctx.pc = saved
                    if init is None and ctx.traps is not None:    # reduce of an empty iterable with no initial: TypeError
                        ctx.traps.append(z3.And(ctx.pc, _container_len(seq, ctx) <= 0))
                    return _Opaque("reduce")
                raise Unsupported("functools.reduce over a non-container iterable")
            if (node.func.value.id == "statistics" and "statistics" not in env
                    and node.func.attr in _STATISTICS_REDUCERS and len(node.args) == 1 and not node.keywords):
                # statistics.mean / median / stdev / ... raises StatisticsError on too few data points (< 1 for the
                # mean family, < 2 for stdev / variance); the result is a float. A len guard removes the trap.
                seq = ev(node.args[0], env, ctx)
                if isinstance(seq, _SafeContainer) and ctx.traps is not None:
                    need = 2 if node.func.attr in ("stdev", "variance") else 1
                    ctx.traps.append(z3.And(ctx.pc, _container_len(seq, ctx) < need))
                    return z3.FreshConst(_F64, "stat")
                raise Unsupported("statistics reducer over a non-container")
            if (node.func.value.id == "random" and node.func.attr == "choice"
                    and "random" not in env and len(node.args) == 1 and not node.keywords):
                # random.choice(seq): IndexError on an empty sequence; returns an element.
                seq = ev(node.args[0], env, ctx)
                if isinstance(seq, _SafeContainer) and not seq.unindexable and not seq.unsized and ctx.traps is not None:
                    ctx.traps.append(z3.And(ctx.pc, _container_len(seq, ctx) <= 0))
                    return _container_element(seq, ctx)
                if _is_str(seq):
                    if ctx.traps is not None:
                        ctx.traps.append(z3.And(ctx.pc, z3.Length(seq) == 0))
                    c = z3.FreshConst(z3.StringSort(), "choice")
                    if ctx.facts is not None:
                        ctx.facts.append(z3.Length(c) == 1)
                    return c
                raise Unsupported("random.choice over a non-sequence")
            if (node.func.value.id == "random" and node.func.attr == "sample"
                    and "random" not in env and len(node.args) == 2 and not node.keywords):
                # random.sample(seq, k): ValueError if k < 0 or k > len(seq); returns a list of length k.
                seq = ev(node.args[0], env, ctx)
                k = ev(node.args[1], env, ctx)
                if isinstance(seq, _SafeContainer) and z3.is_expr(k) and z3.is_int(k) and ctx.traps is not None:
                    ctx.traps.append(z3.And(ctx.pc, z3.Or(k < 0, k > _container_len(seq, ctx))))
                    return _SafeContainer("sample", length=k)
                raise Unsupported("random.sample over a non-container / non-integer k")
            if (node.func.value.id == "random" and node.func.attr == "randint"
                    and "random" not in env and len(node.args) == 2 and not node.keywords):
                # random.randint(a, b): ValueError if a > b; returns an int in [a, b].
                a0 = _as_int(ev(node.args[0], env, ctx))
                b0 = _as_int(ev(node.args[1], env, ctx))
                if ctx.traps is not None:
                    ctx.traps.append(z3.And(ctx.pc, a0 > b0))
                r = z3.FreshInt("randint")
                if ctx.facts is not None:
                    ctx.facts.append(z3.And(r >= a0, r <= b0))
                return r
            if (node.func.value.id == "heapq" and node.func.attr == "heappop"
                    and "heapq" not in env and len(node.args) == 1 and not node.keywords):
                # heapq.heappop(h): IndexError on an empty heap; returns an element. Modeled only when h is popped
                # exactly once (mutate_once), so the stable length is exact; repeated pops / a push abstain.
                seq = ev(node.args[0], env, ctx)
                nm = node.args[0].id if isinstance(node.args[0], ast.Name) else None
                if (isinstance(seq, _SafeContainer) and not seq.unindexable and not seq.unsized
                        and ctx.traps is not None and nm is not None and nm in ctx.mutate_once):
                    ctx.traps.append(z3.And(ctx.pc, _container_len(seq, ctx) <= 0))
                    return _container_element(seq, ctx)
                raise Unsupported("heapq.heappop of a non-container / multiply-mutated heap")
            if (node.func.value.id == "math" and node.func.attr == "prod"
                    and "math" not in env and len(node.args) == 1):
                # math.prod(iterable, *, start=1): the product of a scalar numeric sequence, trap free (empty -> start).
                # The result is an arbitrary int -- it can be 0 (a zero element), so 10 // math.prod(xs) refutes.
                seq = ev(node.args[0], env, ctx)
                for kw in node.keywords:
                    ev(kw.value, env, ctx)                   # start= is trap-checked
                if (isinstance(seq, _SafeContainer) and not seq.unindexable and not seq.unsized
                        and seq.elem is None):
                    return z3.FreshInt("prod")
                raise Unsupported("math.prod over a non-scalar-numeric sequence")
            if (node.func.value.id == "math" and node.func.attr == "fsum"
                    and "math" not in env and len(node.args) == 1 and not node.keywords):
                # math.fsum(iterable): the exact float sum of a scalar numeric sequence, trap free (empty -> 0.0). The
                # result is an arbitrary float that can be 0.0, so 10 // math.fsum(xs) refutes (float floor-div by 0).
                seq = ev(node.args[0], env, ctx)
                if (isinstance(seq, _SafeContainer) and not seq.unindexable and not seq.unsized
                        and seq.elem is None):
                    return z3.FreshConst(_F64, "fsum")
                raise Unsupported("math.fsum over a non-scalar-numeric sequence")
            if (node.func.value.id == "struct" and node.func.attr == "calcsize"
                    and "struct" not in env and len(node.args) == 1 and not node.keywords):
                # struct.calcsize(fmt): for a string LITERAL the size is exactly CPython's -- a valid format string
                # has a known byte size, an invalid one always raises struct.error. A non-literal format is declined.
                fmt = node.args[0]
                if not (isinstance(fmt, ast.Constant) and isinstance(fmt.value, str)):
                    raise Unsupported("struct.calcsize of a non-literal format")
                try:
                    return z3.IntVal(_struct.calcsize(fmt.value))
                except _struct.error:
                    if ctx.traps is not None:
                        ctx.traps.append(ctx.pc)               # invalid format: struct.error
                    return z3.IntVal(0)                        # poison: never trusted once the trap fires
            if node.func.value.id == "operator" and "operator" not in env and not node.keywords:
                # operator.add(a, b) / operator.lt(a, b) / operator.neg(a) ... mirror the Python operator exactly, so
                # re-evaluate the corresponding BinOp / Compare / UnaryOp -- reusing its semantics and traps (e.g.
                # operator.floordiv(a, b) is a // b, a ZeroDivisionError when b is 0). Non-operator helpers (itemgetter,
                # getitem, ...) are not mapped here and fall through.
                _attr = node.func.attr
                if _attr in _OPERATOR_BINOP and len(node.args) == 2:
                    return ev(ast.copy_location(ast.BinOp(left=node.args[0], op=_OPERATOR_BINOP[_attr](),
                                                          right=node.args[1]), node), env, ctx)
                if _attr in _OPERATOR_UNARY and len(node.args) == 1:
                    return ev(ast.copy_location(ast.UnaryOp(op=_OPERATOR_UNARY[_attr](), operand=node.args[0]),
                                                node), env, ctx)
                if _attr in _OPERATOR_CMP and len(node.args) == 2:
                    return ev(ast.copy_location(ast.Compare(left=node.args[0], ops=[_OPERATOR_CMP[_attr]()],
                                                            comparators=[node.args[1]]), node), env, ctx)
            if node.func.value.id == "str" and node.func.attr == "maketrans" and "str" not in env:
                # str.maketrans builds a translation table (modeled opaque); the two-string form raises
                # ValueError when the strings differ in length, the dict and three-argument forms do not.
                margs = [ev(a, env, ctx) for a in node.args]   # each argument trap-checked as it is evaluated
                if len(margs) == 2 and _is_str(margs[0]) and _is_str(margs[1]):
                    if ctx.traps is not None:
                        ctx.traps.append(z3.And(ctx.pc, z3.Length(margs[0]) != z3.Length(margs[1])))
                    return _Opaque("transtable")
                if len(margs) in (1, 3):
                    return _Opaque("transtable")
                raise Unsupported("str.maketrans signature")
            if (node.func.value.id == "int" and node.func.attr == "from_bytes"
                    and "int" not in env and 1 <= len(node.args) <= 2):
                # int.from_bytes(b, byteorder[, signed=]) reads a bytes value as an integer. The only modeled trap is
                # ValueError when byteorder is a string other than 'little' / 'big' (modeled exactly, so a bad literal
                # refutes, a correct or guarded one proves); the result is a non-negative int unless signed is True.
                # A non-bytes first argument is declined (its element types may not be valid byte values).
                arg0 = ev(node.args[0], env, ctx)              # trap-checked as it is evaluated
                if not (isinstance(arg0, _SafeContainer) and arg0.byteslike):
                    raise Unsupported("int.from_bytes of a non-bytes value")
                bo = ev(node.args[1], env, ctx) if len(node.args) == 2 else next(
                    (ev(kw.value, env, ctx) for kw in node.keywords if kw.arg == "byteorder"), None)
                if bo is None or not _is_str(bo):
                    raise Unsupported("int.from_bytes without a string byteorder argument")
                if ctx.traps is not None:                      # ValueError unless byteorder in ('little', 'big')
                    ctx.traps.append(z3.And(ctx.pc, bo != z3.StringVal("little"), bo != z3.StringVal("big")))
                signed = next((kw.value for kw in node.keywords if kw.arg == "signed"), None)
                if signed is not None and not isinstance(signed, ast.Constant):
                    ev(signed, env, ctx)                       # trap-check a non-literal signed flag
                r = z3.FreshInt("from_bytes")
                if ctx.facts is not None and (signed is None or (isinstance(signed, ast.Constant) and not signed.value)):
                    ctx.facts.append(r >= 0)                   # signed defaults False -> a non-negative result
                return r
            if (node.func.value.id in ("bytes", "bytearray") and node.func.attr == "fromhex"
                    and node.func.value.id not in env and len(node.args) == 1 and not node.keywords):
                # bytes.fromhex(s) / bytearray.fromhex(s): for a string LITERAL the result is exactly CPython's parse
                # -- a valid hex string (interleaved whitespace allowed) gives a byteslike value of half its non-space
                # length (its elements are valid bytes in [0, 255]), an odd-length or non-hex string always raises
                # ValueError. A non-literal argument is declined (the parse cannot be decided symbolically).
                hx = node.args[0]
                if not (isinstance(hx, ast.Constant) and isinstance(hx.value, str)):
                    raise Unsupported("bytes.fromhex of a non-literal string")
                _imm = node.func.value.id == "bytes"
                try:
                    _parsed = bytes.fromhex(hx.value)
                except ValueError:
                    if ctx.traps is not None:
                        ctx.traps.append(ctx.pc)               # invalid hex: ValueError
                    return _SafeContainer("fromhex", byteslike=True, immutable=_imm, length=z3.IntVal(0))
                return _SafeContainer("fromhex", byteslike=True, immutable=_imm, length=z3.IntVal(len(_parsed)))
            if (node.func.value.id == "re" and "re" not in env and node.func.attr in
                    ("match", "search", "fullmatch", "findall", "sub", "subn", "split", "finditer")):
                # a CONSTANT compilable pattern makes the call total; a non-constant pattern can raise re.error
                # (UNKNOWN). match/search/fullmatch return Optional[Match] (None); findall/split a list;
                # sub/subn/finditer an opaque value.
                if node.args and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str):
                    import re as _re_runtime
                    try:
                        _re_runtime.compile(node.args[0].value)
                    except _re_runtime.error:
                        raise Unsupported("re pattern does not compile (re.error)")
                    for a in node.args[1:]:
                        ev(a, env, ctx)                        # trap-check the remaining arguments
                    if node.func.attr in ("match", "search", "fullmatch"):
                        return _NoneVal()
                    if node.func.attr in ("findall", "split"):
                        return _SafeContainer(node.func.attr)
                    return _Opaque(node.func.attr)
                raise Unsupported("re with a non-constant pattern (may raise re.error)")
            if qual in _STDLIB:
                return _STDLIB[qual](_eval_args(node.args, env, ctx))
        # torch.nn.functional.X(t, ...), or F.X(t, ...) where the module binds F to torch.nn.functional
        if ((isinstance(node.func.value, ast.Name) and node.func.value.id in ctx.func_aliases
             and node.func.value.id not in env)
                or (_dotted_callee(node.func) or "").startswith("torch.nn.functional.")):
            res = _functional_call(node.func.attr, node, env, ctx)
            if res is not None:
                return res
        recv = ev(node.func.value, env, ctx)
        meth = node.func.attr
        a = [ev(x, env, ctx) for x in node.args]
        if _TRAPFREE:                                        # a pure trap-free stdlib call (os.path.join, time.time, ...)
            _dotted = _dotted_callee(node.func)              # rooted at a free module name, raising no modeled trap
            _root = node.func.value
            while isinstance(_root, ast.Attribute):
                _root = _root.value
            if _dotted is not None and isinstance(_root, ast.Name) and _root.id not in env:
                _res = _safe_stdlib_result(_dotted)
                if _res is not None:
                    for kw in node.keywords:                 # keyword arguments are trap-checked too
                        ev(kw.value, env, ctx)
                    return _res
        if isinstance(recv, _NoneVal):                       # None.method() raises AttributeError: a reachable trap
            if ctx.traps is not None:                        # (the arguments above are still trap-checked first)
                ctx.traps.append(ctx.pc)
            return _Opaque("nonemethod")
        if isinstance(recv, _NdArray):                       # ndarray / tensor methods: reshape, reductions, ...
            res = _nd_method(recv, meth, a, node, env, ctx)
            if res is not None:                              # (an unmodeled ndarray method falls through to the
                return res                                   # generic opaque-safe path below: keyword-checked, no trap)
        if _is_str(recv):
            kwn = {k.arg for k in node.keywords if k.arg is not None}   # keyword names, for str.format named fields
            res = _str_call(meth, recv, a, ctx, kwn)          # exact where z3 allows, else over-approx
            if res is not None:
                return res
        if z3.is_expr(recv) and (z3.is_int(recv) or z3.is_bool(recv)) and not a and not node.keywords:
            res = _int_method(meth, _as_int(recv), ctx)       # bit_length / bit_count / __index__ / conjugate
            if res is not None:
                return res
        if _is_fp(recv) and not a and not node.keywords:      # total float methods: no raise on ANY float, NaN / inf
            if meth == "is_integer":                          # included (is_integer -> bool, hex -> str of the float,
                return _b01(z3.FreshConst(z3.BoolSort(), "is_integer"))   # conjugate -> the real float itself)
            if meth == "hex":
                return z3.FreshConst(_SS, "fphex")
            if meth == "conjugate":
                return recv
        if (z3.is_expr(recv) and (z3.is_int(recv) or z3.is_bool(recv)) and meth == "to_bytes"
                and 1 <= len(node.args) <= 2 and all(kw.arg in ("byteorder", "signed") for kw in node.keywords)):
            # n.to_bytes(length, byteorder[, signed=]) -> a bytes value of `length` bytes. For a CONSTANT length L it
            # is total iff n fits -- unsigned 0 <= n < 256**L, signed -(256**L)//2 <= n < (256**L)//2 -- else an
            # OverflowError; byteorder must be 'little' / 'big' (ValueError, modeled exactly). A symbolic length or a
            # non-constant signed flag is declined (the fit bound is not statically known). The result is byteslike.
            nv = _as_int(recv)
            length_node = node.args[0]
            if not (isinstance(length_node, ast.Constant) and isinstance(length_node.value, int)
                    and not isinstance(length_node.value, bool) and 0 <= length_node.value <= 256):
                raise Unsupported("int.to_bytes with a non-constant or out-of-range length")
            L = length_node.value
            bo = a[1] if len(a) == 2 else next(
                (ev(kw.value, env, ctx) for kw in node.keywords if kw.arg == "byteorder"), None)
            if bo is not None and not _is_str(bo):
                raise Unsupported("int.to_bytes with a non-string byteorder")
            signed_node = next((kw.value for kw in node.keywords if kw.arg == "signed"), None)
            if signed_node is not None and not isinstance(signed_node, ast.Constant):
                ev(signed_node, env, ctx)                     # trap-check, then decline: the sign is not statically known
                raise Unsupported("int.to_bytes with a non-constant signed flag")
            signed = bool(signed_node.value) if isinstance(signed_node, ast.Constant) else False
            if ctx.traps is not None:
                if bo is not None:                            # ValueError unless byteorder in ('little', 'big')
                    ctx.traps.append(z3.And(ctx.pc, bo != z3.StringVal("little"), bo != z3.StringVal("big")))
                hi = 1 << (8 * L)                             # 256**L
                bound = z3.Or(nv < -(hi // 2), nv >= hi // 2) if signed else z3.Or(nv < 0, nv >= hi)
                ctx.traps.append(z3.And(ctx.pc, bound))       # OverflowError: n does not fit in L bytes
            return _SafeContainer("to_bytes", byteslike=True, immutable=True, length=z3.IntVal(L))
        # .pop() on a container parameter mutated exactly once (so the stable length / membership is exact):
        # list.pop() is an IndexError on an empty list and pop(i) an IndexError out of range, against the same
        # symbolic length the c[i] check uses; dict.pop(k) is a KeyError unless k is a provable key, and
        # pop(k, default) never raises. A len() / `in` guard proves it; the popped value is an arbitrary element.
        _gated = (isinstance(node.func.value, ast.Name) and node.func.value.id in ctx.mutate_once)
        if meth == "pop" and ctx.traps is not None and not BEST_EFFORT and _gated:
            if isinstance(recv, _SafeContainer) and not recv.immutable and len(a) <= 1:
                n = _container_len(recv, ctx)
                if not a:
                    ctx.traps.append(z3.And(ctx.pc, n <= 0))                       # pop() from an empty list
                elif z3.is_expr(a[0]) and a[0].sort() == z3.IntSort():
                    ctx.traps.append(z3.And(ctx.pc, z3.Or(a[0] < -n, a[0] >= n)))  # pop(i) out of range
                else:
                    raise Unsupported("list.pop with a non-integer index")
                return z3.FreshInt("pop")
            if isinstance(recv, _DictParam) and len(a) == 1:
                mem = _dict_member(recv, a[0])
                if mem is not None:
                    ctx.traps.append(z3.And(ctx.pc, z3.Not(mem)))                  # dict.pop(k) on a missing key
                    return z3.FreshInt("dpop")
            if isinstance(recv, _DictParam) and len(a) == 2:
                return z3.FreshInt("dpopdef")                                      # dict.pop(k, default): never raises
        if meth == "popitem" and isinstance(recv, _DictParam) and ctx.traps is not None and not BEST_EFFORT \
                and _gated and not a:
            n = _container_len(recv, ctx)
            ctx.traps.append(z3.And(ctx.pc, n <= 0))                               # popitem() on an empty dict: KeyError
            return (z3.FreshInt("pik"), z3.FreshInt("piv"))                        # the popped (key, value) 2-tuple
        # list.index(x) / tuple.index(x) / list.remove(x): ValueError when x is not present, against the
        # sequence's stable membership predicate, so an `x in xs` guard proves it. index is non-mutating, so it
        # is modeled on any sequence parameter -- a tuple included; remove mutates, so it is list-only (not an
        # immutable tuple) and gated to a single mutation like pop. The returned index / removed value is
        # arbitrary (an int); a non-integer / non-string element type abstains.
        if (meth in ("index", "remove") and ctx.traps is not None and not BEST_EFFORT
                and isinstance(recv, _SafeContainer) and len(a) == 1
                and (meth == "index" or (not recv.immutable and _gated))):
            mem = _seq_member(recv, a[0], ctx)
            if mem is not None:
                ctx.traps.append(z3.And(ctx.pc, z3.Not(mem)))                      # x not in the sequence: ValueError
                return z3.FreshInt(meth)
        # dict.get(k) on a dict parameter returns None when k is absent, so using the result in arithmetic, as
        # an index, or any None-trapping operation is a TypeError (modeled by the None machinery): a default
        # argument, an `is None` / truthiness guard, or an `x or default` makes it safe. With a default the
        # result is the value or that default, never None. (A locally-built dict keeps its tracked-key semantics.)
        if meth == "get" and isinstance(recv, _DictParam) and not BEST_EFFORT:
            if len(a) >= 2:
                return z3.FreshInt("getdef")                  # d.get(k, default): the value or the default, never None
            if len(a) == 1:
                return _NoneVal()                             # d.get(k): None when k is absent
        if meth in ("keys", "values", "items") and isinstance(recv, _DictParam) and not a:
            # a dict view (d.keys() / d.values() / d.items()) is sized and iterable but NOT subscriptable (like a set):
            # its length is len(d), so list(view) / sorted(view) / sum(view) decide and max(view) is the empty-dict
            # ValueError; a len(d) guard proves a guarded max. view[i] is a TypeError. items() yields (k, v) 2-tuples.
            return _SafeContainer(meth, unindexable=True, length=_container_len(recv, ctx),
                                  tuple_arity=2 if meth == "items" else None)
        # a.union(b) / a.intersection(b) / a.difference(b) / a.symmetric_difference(b) between two set-like
        # containers is the matching set operation, modeled with the operand-defined content (like | & - ^).
        if (meth in ("union", "intersection", "difference", "symmetric_difference")
                and _is_set_like(recv) and len(a) == 1 and _is_set_like(a[0]) and not node.keywords):
            return _set_binop({"union": "|", "intersection": "&", "difference": "-",
                               "symmetric_difference": "^"}[meth], recv, a[0], ctx)
        if (isinstance(recv, _SafeContainer) and recv.byteslike and not recv.unindexable
                and meth in ("find", "rfind", "index", "rindex", "count") and 1 <= len(a) <= 3
                and ctx.facts is not None):
            # bytes / bytearray search: the result is an index in [-1, len) (find/rfind, never raise) or a count in
            # [0, len], with index/rindex raising ValueError when the subsequence is absent -- decided as a sound
            # over-approximation without modeling the byte content.
            n = _container_len(recv, ctx)
            for arg in a[1:]:
                _as_int(arg)                                  # start / end positions are trap-checked
            if meth == "count":
                k = z3.FreshInt("bcount"); ctx.facts.append(z3.And(k >= 0, k <= n)); return k
            k = z3.FreshInt("bfind"); ctx.facts.append(z3.And(k >= -1, k < n))
            if meth in ("index", "rindex") and ctx.traps is not None:
                ctx.traps.append(z3.And(ctx.pc, k < 0))       # ValueError when the subsequence is not found
            return k
        if isinstance(recv, _SafeContainer) and recv.byteslike and not recv.unindexable:
            if meth == "hex" and not a:                       # bytes.hex() -> a str of hex digits, never raises
                return z3.FreshConst(z3.StringSort(), "hex")
            if (meth in ("startswith", "endswith") and len(a) >= 1 and ctx.facts is not None
                    and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, bytes)):
                sw = z3.FreshConst(z3.BoolSort(), meth)       # b.startswith(const_prefix): a bool whose truth implies b
                ctx.facts.append(z3.Implies(sw, _container_len(recv, ctx) >= len(node.args[0].value)))   # is long enough
                return sw
            if meth in ("upper", "lower", "capitalize", "title", "swapcase") and not a:   # a bytes case transform ->
                return _SafeContainer("bcase", byteslike=True, length=_container_len(recv, ctx))   # bytes of the same length
            if (meth in ("split", "rsplit") and len(a) >= 1 and isinstance(node.args[0], ast.Constant)
                    and isinstance(node.args[0].value, bytes) and node.args[0].value):
                if len(a) >= 2:
                    _as_int(a[1])                             # maxsplit is trap-checked
                if ctx.facts is not None:                     # split always yields at least one part, so result[0] is
                    k = z3.FreshInt("bsplit"); ctx.facts.append(k >= 1)   # in bounds -- an unconstrained length (>= 0)
                    return _SafeContainer("bsplit", length=k)            # would false-refute it as an IndexError
                return _StrSeq("bsplit")                      # no fact channel to register len >= 1: opaque, [i] abstains
            if meth in ("strip", "lstrip", "rstrip", "removeprefix", "removesuffix") and ctx.facts is not None:
                k = z3.FreshInt("bstrip"); ctx.facts.append(z3.And(k >= 0, k <= _container_len(recv, ctx)))
                return _SafeContainer("bstrip", byteslike=True, length=k)   # a contiguous sub-portion: length in [0, len(b)]
            if meth in ("partition", "rpartition") and len(a) == 1 and ctx.facts is not None \
                    and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, bytes) and node.args[0].value:
                n = _container_len(recv, ctx)                 # b.partition(const sep) -> (head, sep, tail), each a bytes
                parts = []                                    # sub-portion of length <= len(b); never raises
                for nm in ("phead", "psep", "ptail"):
                    k = z3.FreshInt(nm); ctx.facts.append(z3.And(k >= 0, k <= n))
                    parts.append(_SafeContainer(nm, byteslike=True, length=k))
                return tuple(parts)
            if meth in ("isalnum", "isalpha", "isascii", "isdigit", "islower", "isspace", "istitle", "isupper") \
                    and not a:
                return z3.FreshConst(z3.BoolSort(), meth)     # a bytes predicate -> a bool, never raises
        if meth in _TRAPPING_METHODS:                        # a trapping method: not assumed trap free unless best-effort
            if not BEST_EFFORT:
                raise Unsupported(f"method .{meth}() on this type")
            _best_effort_assume()                            # best-effort: the trapping method assumed safe (tainted)
        if isinstance(node.func.value, ast.Name) and node.func.value.id in ctx.numeric_params:
            # a method on a parameter explicitly typed int / float / bool -- n.append(...) -- is an
            # AttributeError. Abstain rather than assume an opaque safe method exists (which would prove a false
            # trap freedom). Keyed on the int/float/bool annotation, so a duck-typed or class-annotated receiver
            # keeps the opaque-safe path below (class dispatch still resolves o: C).
            raise Unsupported(f"method .{meth}() on a number is unmodeled (an AttributeError if absent)")
        for kw in node.keywords:                             # receiver and positional args trap-checked above;
            ev(kw.value, env, ctx)                           # check keywords too
        # A module-qualified call on a free name -- json.loads(s), re.match(p, s), os.path.join(s) -- is an
        # unmodeled module function, not a method on a modeled value. It can raise a modeled trap (json.loads
        # raises JSONDecodeError, a ValueError subclass), so assuming it trap free is unsound; treat it like a
        # bare unmodeled call -- UNKNOWN unless best-effort. A method whose receiver is rooted at a name bound in
        # env (a parameter or local value) keeps the assume-safe duck-typed behavior, where a missing attribute
        # is at most an AttributeError, not a modeled trap.
        root = node.func.value
        while isinstance(root, ast.Attribute):
            root = root.value
        if isinstance(root, ast.Name) and root.id not in env:
            if not BEST_EFFORT:
                raise Unsupported(f"unmodeled module-qualified call {root.id}.{meth}(...) "
                                  f"at line {getattr(node, 'lineno', '?')}")
            _best_effort_assume()                            # best-effort: the module-qualified call assumed safe (tainted)
        return _Opaque("method")
    if isinstance(node, ast.Call):                           # callee is an expression, not a plain name: evaluate it
        callee = ev(node.func, env, ctx)                     # (trap-checking it), then if it is a known callable
        if isinstance(callee, _NoneVal):                     # calling None (None(), or a returned/stored None) traps
            if ctx.traps is not None:
                ctx.traps.append(ctx.pc)
            _eval_args(node.args, env, ctx)                  # arguments are still trap-checked
            return _Opaque("nonecall")
        argvals = _eval_args(node.args, env, ctx)            # value apply it so its body is checked, else opaque
        if isinstance(callee, _FuncRef):
            return _call_repo(callee.name, argvals, ctx)
        if isinstance(callee, _Lambda) and len(callee.params) == len(argvals):
            callenv = dict(callee.env)
            for pname, av in zip(callee.params, argvals):
                callenv[pname] = av
            return ev(callee.body, callenv, ctx)
        return _Opaque("call")
    if isinstance(node, ast.Subscript):
        base = ev(node.value, env, ctx)
        if isinstance(base, _NoneVal):                       # None[k] raises TypeError (not subscriptable): a trap
            if ctx.traps is not None:
                ctx.traps.append(ctx.pc)
            return _Opaque("noneidx")
        if _TRAPFREE and isinstance(base, _Column):
            if isinstance(node.slice, ast.Slice):            # s[i:j]: a positional sub-column (pandas clamps, no trap)
                for b in (node.slice.lower, node.slice.upper, node.slice.step):
                    if b is not None:
                        ev(b, env, ctx)
                return _Column((z3.FreshInt("colslice"),))
            ev(node.slice, env, ctx)                         # s[label]: LABEL-based, may KeyError -> abstain (use .iloc)
            raise Unsupported("pandas Series label index s[i] is not modeled (use .iloc for positional access)")
        if _TRAPFREE and isinstance(base, _NdArray):
            if isinstance(node.slice, ast.Slice):            # a slice of axis 0: numpy clamps (no IndexError); the
                for b in (node.slice.lower, node.slice.upper, node.slice.step):   # result resizes axis 0 (opaque length)
                    if b is not None:
                        ev(b, env, ctx)
                return _NdArray((z3.FreshInt("ndslice"),) + base.shape[1:])
            idxs = list(node.slice.elts) if isinstance(node.slice, ast.Tuple) else [node.slice]
            if any(isinstance(ix, ast.Slice) for ix in idxs):
                raise Unsupported("ndarray mixed slice index is not modeled")
            if len(idxs) > len(base.shape):                  # too many indices for the array's rank: IndexError
                if ctx.traps is not None:
                    ctx.traps.append(ctx.pc)
                return _Opaque("ndidx")
            ivs = [ev(ix, env, ctx) for ix in idxs]
            if len(ivs) == 1 and isinstance(ivs[0], _NdArray):   # advanced indexing: a boolean mask a[a>0] or an index
                return _Opaque("advidx")                          # tensor a[idx] -- a new tensor, data-dependent shape
            for k, iv in enumerate(ivs):
                if not (z3.is_expr(iv) and iv.sort() == z3.IntSort()):
                    raise Unsupported("ndarray index is not an integer")
                if ctx.traps is not None:
                    nk = base.shape[k]
                    ctx.traps.append(z3.And(ctx.pc, z3.Or(iv < -nk, iv >= nk)))   # IndexError on axis k
            rest = base.shape[len(idxs):]
            return _NdArray(rest) if rest else z3.FreshInt("ndelem")   # the lower-rank subarray, or a scalar element
        if isinstance(base, _SafeContainer) and base.unindexable:   # a set / frozenset is not subscriptable: s[i]
            if ctx.traps is not None:                               # and s[i:j] both raise TypeError
                ctx.traps.append(ctx.pc)
            return _Opaque("setidx")
        if isinstance(base, _MapVal):                        # a tracked dict read: the stored value, KeyError if absent
            if isinstance(node.slice, ast.Slice):
                raise Unsupported("a dict is not sliceable")
            tracked = (isinstance(node.value, ast.Dict)      # an inline dict literal, or dict(), cannot escape
                       or (isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name)
                           and node.value.func.id == "dict")
                       or (isinstance(node.value, ast.Name) and node.value.id in ctx.tracked_dicts))
            if not tracked:                                  # a dict that escaped: its contents are not tracked
                raise Unsupported("read of an untracked dict")
            return _map_get(base, ev(node.slice, env, ctx), ctx)
        if isinstance(base, tuple):                          # tuple / list-literal indexing and slicing
            sl = node.slice
            if isinstance(sl, ast.Constant) and isinstance(sl.value, int):
                if -len(base) <= sl.value < len(base):
                    return base[sl.value]
                if ctx.traps is not None:                    # constant index out of range: always IndexError
                    ctx.traps.append(ctx.pc)
                return _Opaque("index")
            if isinstance(sl, ast.Slice):
                for b in (sl.lower, sl.upper, sl.step):       # trap-check each bound (10 // k can ZeroDivision)
                    if b is not None:
                        ev(b, env, ctx)
                if all(b is None or (isinstance(b, ast.Constant) and isinstance(b.value, int))
                       for b in (sl.lower, sl.upper, sl.step)):
                    return base[_const_int(sl.lower):_const_int(sl.upper):_const_int(sl.step)]
                raise Unsupported("slice of a tuple with a non-constant bound")
            iv = ev(sl, env, ctx)                            # variable index: IndexError when out of [-len, len)
            if z3.is_expr(iv) and iv.sort() == z3.IntSort():
                if ctx.traps is not None:
                    ctx.traps.append(z3.And(ctx.pc, z3.Or(iv < -len(base), iv >= len(base))))
                return _Opaque("index")
            raise Unsupported("tuple index is not an integer")
        if _is_str(base):
            return _str_subscript(base, node.slice, env, ctx)
        if _TRAPFREE and isinstance(base, _StrSeq) and base.length is not None:
            # a split result: an index is IndexError-checked against its length, an element is a fresh string, a slice
            # is another string list.
            if isinstance(node.slice, ast.Slice):
                for b in (node.slice.lower, node.slice.upper, node.slice.step):
                    if b is not None:
                        ev(b, env, ctx)                       # trap-check each slice bound
                sk = z3.FreshInt("slicelen")
                if ctx.facts is not None:
                    ctx.facts.append(sk >= 0)
                return _StrSeq("sliced", length=sk)
            idx = ev(node.slice, env, ctx)
            if z3.is_expr(idx) and idx.sort() == z3.IntSort():
                if ctx.traps is not None:
                    ctx.traps.append(z3.And(ctx.pc, z3.Or(idx < -base.length, idx >= base.length)))   # IndexError
                return z3.FreshConst(z3.StringSort(), "splitelem")
            raise Unsupported("split-result index is not an integer")
        if _TRAPFREE and isinstance(base, _DefaultDict):
            if isinstance(node.slice, ast.Slice):
                raise Unsupported("a dict is not sliceable")
            ev(node.slice, env, ctx)                          # trap-check the key expression
            return z3.FreshInt("ddval")                       # defaultdict / Counter: a missing key returns a default, no KeyError
        if _TRAPFREE and isinstance(base, _DictParam):
            if isinstance(node.slice, ast.Slice):
                raise Unsupported("a dict is not sliceable")
            kt = ev(node.slice, env, ctx)
            mem = _dict_member(base, kt)
            if mem is not None and ctx.traps is not None:
                ctx.traps.append(z3.And(ctx.pc, z3.Not(mem)))   # KeyError when the key is not present
                if (isinstance(node.value, ast.Name) and node.value.id in getattr(ctx, "readonly_dicts", ())):
                    # a read-only dict's d[k] is a fixed function of k -- memoize it so re-reading the same key gives
                    # ONE value, making a guard `if d[k] != 0:` protect a later `10 // d[k]` (else the two reads were
                    # independent fresh values and the division falsely refuted). For dict[K, V], the value is a fresh
                    # V (named per key, so distinct keys get distinct lengths) -- so d[k][i] / d[k].append / len(d[k])
                    # decide for dict[str, list].
                    ck = (node.value.id, str(kt))
                    if ck not in ctx.dval_cache:
                        ctx.dval_cache[ck] = _dict_value_term(base.valproto, "dval_%d" % len(ctx.dval_cache))
                    return ctx.dval_cache[ck]
                return z3.FreshInt("dval")
            raise Unsupported("dict subscript with an unmodeled key type")
        if _TRAPFREE and isinstance(base, _SafeContainer) and base.unsized:
            # a lazy iterator (zip / itertools.chain / ...) is not subscriptable: it[i] / it[a:b] are TypeErrors.
            # Trap-check the index / slice bounds, then refute.
            if isinstance(node.slice, ast.Slice):
                for b in (node.slice.lower, node.slice.upper, node.slice.step):
                    if b is not None:
                        ev(b, env, ctx)
            else:
                ev(node.slice, env, ctx)
            if ctx.traps is not None:
                ctx.traps.append(ctx.pc)
            return _Opaque("itersub")
        if _TRAPFREE and isinstance(base, _Opaque) and not isinstance(base, _DictLit):
            if isinstance(node.slice, ast.Slice):            # a slice of an opaque value never traps (Python clamps),
                if isinstance(base, _SafeContainer) and not base.unindexable:   # a list / tuple / bytes slice is a
                    L = _slice_len(_container_len(base, ctx), node.slice, env, ctx)   # sequence sized by the slice
                    return _SafeContainer("slice", immutable=base.immutable, length=L, byteslike=base.byteslike)
                for b in (node.slice.lower, node.slice.upper, node.slice.step):   # but a bound expression can (10 // k)
                    if b is not None:
                        ev(b, env, ctx)
                # a slice is a sub-sequence, never a scalar -- model it as an opaque sequence, not a fresh int,
                # so a later arithmetic op on it abstains (Unsupported -> UNKNOWN) rather than fabricating a
                # scalar trap: an opaque ndarray's a[1:] / a[:-1] (diffusers VQ-diffusion alpha_schedules) must
                # not REFUTE as a ZeroDivisionError that numpy never raises (it yields nan element-wise).
                return _SafeContainer("slice")
            idx = ev(node.slice, env, ctx)
            if isinstance(base, _SafeContainer) and ctx.traps is not None \
                    and z3.is_expr(idx) and idx.sort() == z3.IntSort():
                n = _container_len(base, ctx)                # bounds VC: IndexError when the index leaves [-len, len)
                ctx.traps.append(z3.And(ctx.pc, z3.Or(idx < -n, idx >= n)))
                if base.tuple_arity is not None:             # zip / enumerate / items element: a fixed N-tuple
                    return tuple(z3.FreshInt("telem") for _ in range(base.tuple_arity))
                if isinstance(base.elem, _SafeContainer):    # list[list[..]] etc.: the element is an inner sequence
                    pr = base.elem                           # whose length is a per-index uninterpreted function, so a
                    ilen = z3.Function("ilen_" + base.name, z3.IntSort(), z3.IntSort())(idx)   # len(c[i]) guard
                    if ctx.facts is not None:                # constrains c[i][j]; nonnegative by construction
                        ctx.facts.append(ilen >= 0)
                    return _SafeContainer(base.name + "_e", immutable=pr.immutable, length=ilen,
                                          unindexable=pr.unindexable, byteslike=pr.byteslike, elem=pr.elem)
                elem = z3.FreshInt("helem")
                if base.byteslike and ctx.facts is not None:   # a bytes / bytearray element is exactly an int in [0, 255]
                    ctx.facts.append(z3.And(elem >= 0, elem <= 255))
                return elem
            if BEST_EFFORT:                                  # the opaque index is assumed in bounds (lower trust)
                _best_effort_assume()
                return z3.FreshInt("be_idx")
            raise Unsupported("index into an opaque container may be out of range")
        if BEST_EFFORT:                                       # an unmodeled subscript is assumed well-typed (lower trust)
            if isinstance(node.slice, ast.Slice):
                for b in (node.slice.lower, node.slice.upper, node.slice.step):
                    if b is not None:
                        ev(b, env, ctx)
            else:
                ev(node.slice, env, ctx)
            _best_effort_assume()
            return _Opaque("be_sub")
        raise Unsupported("subscript of a non-string value")
    if isinstance(node, ast.Attribute):
        if (isinstance(node.value, ast.Name) and node.value.id == "math" and "math" not in env
                and node.attr in _MATH_CONSTS):
            return _MATH_CONSTS[node.attr]                   # math.pi / math.e / math.tau / math.inf / math.nan
        if (isinstance(node.value, ast.Name) and node.value.id == "string" and "string" not in env
                and node.attr in _STRING_CONSTS):
            return z3.StringVal(_STRING_CONSTS[node.attr])   # string.ascii_lowercase / digits / punctuation / ...
        v = ev(node.value, env, ctx)
        if isinstance(v, _Complex):
            if node.attr == "real":
                return v.re
            if node.attr == "imag":
                return v.im
        if isinstance(v, _NdArray):                          # ndarray shape attributes (value-independent)
            if node.attr == "shape":
                return v.shape                               # a tuple of the dimension terms (so a.shape[0] works)
            if node.attr == "ndim":
                return z3.IntVal(len(v.shape))
            if node.attr == "size":
                return _nd_size(v.shape)
            if node.attr in ("T", "mT", "mH"):
                return _NdArray(tuple(reversed(v.shape)))
            if node.attr in ("real", "imag", "grad", "data"):
                return _NdArray(v.shape)                      # a complex part / .grad / .data: the same shape
            if node.attr in ("values", "iloc"):
                return _NdArray(v.shape)                      # pandas .values / .iloc: a positional view of the column
            return _Opaque("ndattr")                         # .dtype / .device / ...: opaque, raises no modeled trap
        if isinstance(v, _NoneVal):                          # None.x raises AttributeError: a trap
            if ctx.traps is not None:
                ctx.traps.append(ctx.pc)
            return _Opaque("noneattr")
        base = getattr(v, "name", None)                      # an opaque object's field: a stable value keyed by its
        if base is not None:                                 # path (o.x, o.a.x), duck-typed numeric in arithmetic so
            return _FieldVal(base + "." + node.attr)         # o.x + o.y decides; len / a method / a subscript stay opaque
        return _Opaque("attr")                               # attribute access raises at most AttributeError
    if _TRAPFREE and isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
        env2 = dict(env)                                     # a comprehension: trap-check the iterables, element,
        iters = []                                           # and filters with the targets as arbitrary integers
        for gen in node.generators:
            it = ev(gen.iter, env2, ctx)                     # the iterable is evaluated (trap-checked) regardless
            iters.append(it)
            if (isinstance(gen.target, (ast.Tuple, ast.List))
                    and ctx.traps is not None and not BEST_EFFORT):   # `[e for a, b in xs]`: an element of non-k-tuple
                _k = len(gen.target.elts)                             # shape raises on unpack unless the iterable is a
                _ar = it.tuple_arity if isinstance(it, _SafeContainer) else None   # tracked k-tuple source or a
                if _ar != _k and not _unpack_arity_ok(gen.iter, _k):  # fixed-arity builtin (enumerate/zip/zip_longest)
                    _ne = (_container_len(it, ctx) >= 1) if isinstance(it, _SafeContainer) else z3.BoolVal(True)
                    ctx.traps.append(z3.And(ctx.pc, _ne))
            if _is_str(it) and isinstance(gen.target, ast.Name):   # iterating a string yields 1-char strings, so the
                cs = z3.String("hc_" + gen.target.id)              # element's ord(c) / len(c) / c == '?' is modeled
                if ctx.facts is not None:
                    ctx.facts.append(z3.Length(cs) == 1)
                env2[gen.target.id] = cs
            elif (isinstance(it, _SafeContainer) and it.byteslike and not it.unindexable
                  and isinstance(gen.target, ast.Name)):           # a bytes / bytearray element is an int in [0, 255]
                _be = z3.FreshInt("hc_" + gen.target.id)
                if ctx.facts is not None:
                    ctx.facts.append(z3.And(_be >= 0, _be <= 255))
                env2[gen.target.id] = _be
            else:
                for t in _target_names(gen.target):
                    env2[t] = z3.FreshInt("hc_" + t)
        # the filters and element run only when the iterable yields at least one element; for a single-generator
        # comprehension over a sized container, condition their traps on len(iterable) >= 1, so a trap in the
        # element is not flagged for an input that empties the iterable -- the 10 // n in [.. for i in range(1, n)]
        # is unreachable at n == 0 (range(1, 0) is empty), not a crash (the NormalDist.quantiles(0) false positive).
        old_pc = ctx.pc
        if len(node.generators) == 1 and isinstance(iters[0], _SafeContainer):
            ctx.pc = z3.And(old_pc, _container_len(iters[0], ctx) >= 1)
        for gen in node.generators:
            for cond in gen.ifs:
                ev(cond, env2, ctx)
        elt_val = None
        if isinstance(node, ast.DictComp):
            ev(node.key, env2, ctx); ev(node.value, env2, ctx)
        else:
            elt_val = ev(node.elt, env2, ctx)
        ctx.pc = old_pc
        # a string-element generator (str(x) for x in xs) is an unsized iterator of strings: sep.join(it) proves.
        if isinstance(node, ast.GeneratorExp) and elt_val is not None and _is_str(elt_val):
            return _StrSeq("genstr", unsized=True)
        # a single-generator list comprehension [e for x in it] is a NEW sized list, so model it as a container
        # whose length is the iterable's length when there is no filter (and a fresh nonnegative length bounded
        # by it when filtered, since a filter only drops elements): then a later c[i] is bounds-checked --
        # c = [0 for i in range(n)]; c[i] proves under 0 <= i < n. A set/dict comprehension, a generator
        # expression (not indexable), or multiple/nested generators stays opaque.
        if isinstance(node, ast.ListComp) and len(node.generators) == 1 and not node.generators[0].is_async:
            g0 = node.generators[0]
            base_len = _container_len(iters[0], ctx) if isinstance(iters[0], _SafeContainer) else None
            if base_len is not None and not g0.ifs:
                length = base_len
            else:
                length = z3.FreshInt("complen")
                if ctx.facts is not None:
                    ctx.facts.append(length >= 0)
                    if base_len is not None:
                        ctx.facts.append(length <= base_len)
            if elt_val is not None and _is_str(elt_val):     # a string-element list comp [str(x) for x in xs] is a
                return _StrSeq("strcomp", length=length)      # sized sequence of strings, so sep.join([...]) proves
            return _SafeContainer("comp", length=length)
        return _Opaque("comp")
    if BEST_EFFORT:                                          # an unmodeled expression: trap-check its children, then opaque (lower trust)
        _best_effort_assume()
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.expr):
                try:
                    ev(child, env, ctx)
                except Unsupported:
                    pass
        return _Opaque("be_expr")
    raise Unsupported(f"expression {type(node).__name__} at line {getattr(node, 'lineno', '?')}")


def _star_seq_len(elts, env, ctx):
    """The length of a star-unpacked list/tuple literal [*a, *b, x]: the sum of the plain scalar-list sources' lengths
    plus the plain-element count. Each element is trap-checked. Raises on a non-plain-list starred source (a tuple /
    nested / mapping source, whose element types would be mismodeled)."""
    total = z3.IntVal(0)
    for e in elts:
        if isinstance(e, ast.Starred):
            v = ev(e.value, env, ctx)
            if isinstance(v, _SafeContainer) and v.tuple_arity is None and v.elem is None:
                total = total + _container_len(v, ctx)
            else:
                raise Unsupported("starred unpacking of a non-plain-list iterable")
        else:
            ev(e, env, ctx)
            total = total + z3.IntVal(1)
    return total


def _container_len(c, ctx):
    """A stable nonnegative symbolic length for an opaque container parameter, shared between len(c) and
    the bounds check on c[i] so a len() guard constrains the index. z3 interns by name, so every use of
    the same container name yields the same term. A range carries its exact length explicitly (already
    nonnegative by construction), so len(range(n)) == n and an index bounds-checks precisely."""
    explicit = getattr(c, "length", None)
    if explicit is not None:
        return explicit
    n = z3.Int("len_" + c.name)
    if ctx.facts is not None:
        ctx.facts.append(n >= 0)
    return n


def _container_element(container, ctx):
    """A fresh value for an arbitrary element of `container`, the same kind container[i] yields: an inner sequence for
    list[list]/list[str], a byte in [0,255] for bytes/bytearray, else an int."""
    if isinstance(container, _SafeContainer):
        if container.tuple_arity is not None:
            return tuple(z3.FreshInt("ketelem") for _ in range(container.tuple_arity))
        if isinstance(container.elem, _SafeContainer):
            pr = container.elem
            ln = z3.FreshInt("keyilen")
            if ctx.facts is not None:
                ctx.facts.append(ln >= 0)
            return _SafeContainer(container.name + "_ke", immutable=pr.immutable, length=ln,
                                  unindexable=pr.unindexable, byteslike=pr.byteslike, elem=pr.elem)
        elem = z3.FreshInt("keyelem")
        if container.byteslike and ctx.facts is not None:
            ctx.facts.append(z3.And(elem >= 0, elem <= 255))
        return elem
    return z3.FreshInt("keyelem")


def _apply_key_callable(keynode, container, env, ctx):
    """Apply a sorted/min/max key= callable to a freely-chosen element so its per-element traps surface (key=lambda x:
    10 // x refutes); guarded by the container being non-empty. A lambda or repo function is applied; the total
    builtins str/repr never trap on any element (accepted); other bare builtins (len/abs, element-type-dependent) are
    declined to UNKNOWN."""
    if (isinstance(keynode, ast.Name) and keynode.id in ("str", "repr")
            and keynode.id not in env and keynode.id not in ctx.repo):
        return                                               # str(x) / repr(x) is total -- no per-element trap
    lam = ev(keynode, env, ctx) if isinstance(keynode, ast.Lambda) else \
        (env.get(keynode.id) if isinstance(keynode, ast.Name) else None)
    elem = _container_element(container, ctx)
    saved = ctx.pc
    if isinstance(container, _SafeContainer):
        ctx.pc = z3.And(ctx.pc, _container_len(container, ctx) >= 1)
    try:
        if isinstance(lam, _Lambda) and len(lam.params) == 1:
            le = dict(lam.env)
            le[lam.params[0]] = elem
            ev(lam.body, le, ctx)
        elif isinstance(keynode, ast.Name) and keynode.id in ctx.repo:
            ctx.inline(keynode.id, [elem])
        else:
            raise Unsupported("sorted/min/max key= is not a modeled callable (only a lambda or repo function)")
    finally:
        ctx.pc = saved


def _apply_fold_fn(fn, acc, elem, env, ctx):
    """Apply a 2-argument reduce / accumulate fold callable to (acc, elem) so its per-step trap surfaces (a // b on a
    zero element refutes). Handles a 2-arg lambda, an in-repo function, and operator.<binop> (operator.add / mul /
    floordiv / ...); raises on anything else (the caller then declines to UNKNOWN)."""
    lam = ev(fn, env, ctx) if isinstance(fn, ast.Lambda) else (env.get(fn.id) if isinstance(fn, ast.Name) else None)
    if isinstance(lam, _Lambda) and len(lam.params) == 2:
        le = dict(lam.env)
        le[lam.params[0]] = acc
        le[lam.params[1]] = elem
        ev(lam.body, le, ctx)
    elif isinstance(fn, ast.Name) and fn.id in ctx.repo:
        ctx.inline(fn.id, [acc, elem])
    elif (isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name) and fn.value.id == "operator"
          and fn.attr in _OPERATOR_BINOP and "operator" not in env):
        binop = ast.copy_location(ast.BinOp(left=ast.copy_location(ast.Name("_facc", ast.Load()), fn),
                                            op=_OPERATOR_BINOP[fn.attr](),
                                            right=ast.copy_location(ast.Name("_felem", ast.Load()), fn)), fn)
        ev(binop, {"_facc": acc, "_felem": elem}, ctx)       # operator.add(acc, x) etc.: the binop's own trap surfaces
    else:
        raise Unsupported("fold function is not a 2-arg lambda / repo function / operator binop")


def _dict_member(d, key):
    """Membership of `key` in opaque dict parameter `d`: a stable uninterpreted predicate keyed on d's name
    and the key's sort (int and string keys are tracked separately, as Python keeps them distinct), so a
    `key in d` guard or a `for key in d` iteration connects to the d[key] read. None for an unmodeled key."""
    if not z3.is_expr(key):
        return None
    s = key.sort()
    if s == z3.IntSort():
        return z3.Function("memd_i_" + d.name, z3.IntSort(), z3.BoolSort())(key)
    if s == z3.StringSort():
        return z3.Function("memd_s_" + d.name, z3.StringSort(), z3.BoolSort())(key)
    return None


def _zmin(a, b):
    return z3.If(a < b, a, b)


def _zmax(a, b):
    return z3.If(a > b, a, b)


def _const_int(node):
    """The Python int of a constant index/bound node, or None for an omitted bound; a
    non-constant bound raises Unsupported."""
    if node is None:
        return None
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
        return node.value
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub) and isinstance(node.operand, ast.Constant):
        return -node.operand.value
    raise Unsupported("a constant index/bound is required here")


def _slice_len(n, slc, env, ctx):
    """Length of x[lower:upper:step] given len(x) == n, bounds/step trap-checked (a zero step is a ValueError):
    exact for a step-1 slice (clamped upper - lower) and a full strided x[::k] (ceil(n/|k|)), else bounded by [0, n]."""
    k = _const_num(slc.step) if slc.step is not None else 1
    lo = _as_int(ev(slc.lower, env, ctx)) if slc.lower is not None else None
    hi = _as_int(ev(slc.upper, env, ctx)) if slc.upper is not None else None
    if slc.step is not None:
        sv = ev(slc.step, env, ctx)                          # trap-check the step; range step 0 is a ValueError
        if ctx.traps is not None and z3.is_expr(sv) and (z3.is_int(sv) or z3.is_bool(sv)):
            ctx.traps.append(z3.And(ctx.pc, _as_int(sv) == 0))
    if k == 1:                                               # step 1 / None: exact clamped length
        clamp = lambda x, d: d if x is None else z3.If(x < 0, _zmax(n + x, z3.IntVal(0)), _zmin(x, n))
        return _zmax(clamp(hi, n) - clamp(lo, z3.IntVal(0)), z3.IntVal(0))
    if isinstance(k, int) and k != 0 and lo is None and hi is None:
        a = abs(k)                                           # x[::k]: exactly ceil(n / |k|) == (n + |k| - 1) // |k|
        return py_floordiv(n + z3.IntVal(a - 1), z3.IntVal(a))
    L = z3.FreshInt("slicelen")                              # a strided slice with explicit bounds: bounded by [0, n]
    if ctx.facts is not None:
        ctx.facts.append(z3.And(L >= 0, L <= n))
    return L


def _str_subscript(base, slc, env, ctx):
    """Python string subscripting. A slice s[i:j] (step 1) clamps i and j into [0, len] with negative indices
    counted from the end; a strided slice s[i:j:k] (constant k != 1) has the exact length _slice_len computes with
    over-approximated content (z3 strings cannot express a stride); an index s[i] returns the one-character string
    and traps (IndexError) when out of range."""
    n = z3.Length(base)
    if isinstance(slc, ast.Slice):
        step1 = slc.step is None or (isinstance(slc.step, ast.Constant) and slc.step.value in (1, None))
        if not step1:                                        # a strided slice: exact length, over-approximated content
            L = _slice_len(n, slc, env, ctx)
            r = z3.FreshConst(_SS, "strslice")
            if ctx.facts is not None:
                ctx.facts.append(z3.Length(r) == L)          # the result is a string of the strided length
                _note_overapprox(ctx, "a strided string slice")
            elif _TRAPFREE:
                return r
            else:
                raise Unsupported("strided string slice needs the over-approximation channel")
            return r

        def bound(node_, dflt):
            if node_ is None:
                return dflt
            x = _as_int(ev(node_, env, ctx))
            return z3.If(x < 0, _zmax(n + x, z3.IntVal(0)), _zmin(x, n))

        i = bound(slc.lower, z3.IntVal(0))
        j = bound(slc.upper, n)
        return z3.SubString(base, i, _zmax(j - i, z3.IntVal(0)))
    idx = _as_int(ev(slc, env, ctx))
    real = z3.If(idx < 0, n + idx, idx)
    if ctx.traps is not None:
        ctx.traps.append(z3.And(ctx.pc, z3.Or(real < 0, real >= n)))   # IndexError
    return z3.SubString(base, real, z3.IntVal(1))


def ev_bool(node, env: Dict[str, z3.ExprRef], ctx: Ctx) -> z3.ExprRef:
    """Evaluate a node in boolean (test) context, applying Python truthiness so that
    `if x:` and `while x:` mean `x != 0` and `a and b` short-circuits as a Bool."""
    if isinstance(node, ast.BoolOp):
        is_and = isinstance(node.op, ast.And)
        old, guard, parts = ctx.pc, ctx.pc, []
        for v in node.values:
            ctx.pc = guard
            pv = ev_bool(v, env, ctx)
            parts.append(pv)
            guard = z3.And(guard, pv) if is_and else z3.And(guard, z3.Not(pv))
        ctx.pc = old
        return z3.And(*parts) if is_and else z3.Or(*parts)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return z3.Not(ev_bool(node.operand, env, ctx))
    if isinstance(node, ast.Compare):
        return ev(node, env, ctx)
    return _as_bool(ev(node, env, ctx), ctx)


_BUILTIN_TYPE_NAMES = frozenset({"int", "bool", "float", "complex", "str", "bytes", "bytearray",
                                 "list", "tuple", "set", "frozenset", "dict", "object"})


def _is_object_annotation(ann) -> bool:
    """Whether a parameter annotation denotes an opaque object -- a user class (a bare Name that is not a
    builtin scalar or container type, or a string forward reference), a qualified name (module.Class), or a
    PEP-604 union (A | B) -- rather than a modeled scalar or container. Such a parameter is an opaque
    receiver, not a sampled integer, so a scalar trap pinned only to its being a number is not a real trap."""
    if isinstance(ann, ast.Name):
        return ann.id not in _BUILTIN_TYPE_NAMES
    if isinstance(ann, ast.Constant):
        return isinstance(ann.value, str)                    # a string forward reference ("Conf")
    if isinstance(ann, ast.Attribute):
        return True                                          # a qualified class name (module.Class)
    if isinstance(ann, ast.BinOp) and isinstance(ann.op, ast.BitOr):
        return True                                          # a PEP-604 union (A | B)
    return False


def _elem_container_proto(elem_ann):
    """A _SafeContainer prototype for a sequence's element type when that element is itself a sequence -- a
    list[list[int]] / list[tuple[int]] / list[bytes] parameter -- else None. The prototype carries the inner
    sequence's flags (a tuple element is immutable, a bytes element is byteslike); its length is filled per index
    at subscript time. One level deep: the inner sequence's own elements are left scalar."""
    if isinstance(elem_ann, ast.Subscript) and isinstance(elem_ann.value, ast.Name):
        b = elem_ann.value.id
    elif isinstance(elem_ann, ast.Name):
        b = elem_ann.id
    else:
        return None
    if b in ("list", "List", "Sequence", "MutableSequence"):
        return _SafeContainer("elem")
    if b in ("tuple", "Tuple"):
        return _SafeContainer("elem", immutable=True)
    if b in ("bytes", "bytearray"):
        return _SafeContainer("elem", immutable=(b == "bytes"), byteslike=True)
    return None


def _ann_value(ann):
    """A prototype value for a type-annotation node, used as a dict's value type (dict[K, V]) so a read d[k] can be
    modeled as a V. Mirrors _param_term's type mapping for the container / string / dict cases; an int / bool / float
    or unmodeled type returns None (the read falls back to the fresh-int default)."""
    base = (ann.id if isinstance(ann, ast.Name)
            else ann.value.id if isinstance(ann, ast.Subscript) and isinstance(ann.value, ast.Name) else None)
    if base in ("list", "List", "Sequence", "MutableSequence"):
        return _SafeContainer("dvproto", elem=_elem_container_proto(ann.slice) if isinstance(ann, ast.Subscript) else None)
    if base in ("tuple", "Tuple"):
        return _SafeContainer("dvproto", immutable=True)
    if base in ("set", "frozenset", "Set", "FrozenSet", "MutableSet"):
        return _SafeContainer("dvproto", unindexable=True)
    if base in ("bytes", "bytearray"):
        return _SafeContainer("dvproto", byteslike=True, immutable=(base == "bytes"))
    if base == "str":
        return z3.String("dvproto")
    if base in ("dict", "Dict", "Mapping", "MutableMapping"):
        return _DictParam("dvproto")
    return None


def _dict_value_term(valproto, nm):
    """A fresh value of a dict value type's prototype, named `nm` (so its symbolic length is distinct per dict key).
    None / scalar prototype -> a fresh int (the default), so d[k] arithmetic stays modeled."""
    if isinstance(valproto, _SafeContainer):
        return _SafeContainer(nm, byteslike=valproto.byteslike, immutable=valproto.immutable,
                              unindexable=valproto.unindexable, elem=valproto.elem)
    if _is_str(valproto):
        return z3.String(nm)
    if isinstance(valproto, _DictParam):
        return _DictParam(nm, valproto=valproto.valproto)
    return z3.FreshInt(nm)


def _param_term(arg):
    """A parameter's symbolic term, sorted by its annotation: `int` (and unannotated) -> Int, `bool` ->
    Bool, `float` -> Float64, `str` -> Z3 String, `list` -> a bounds-checked sequence (so an integer index
    is verified against its length). An object-typed annotation is an opaque receiver; other annotations
    fall back to Int and are handled by the container-aware verifiers."""
    ann = arg.annotation
    if isinstance(ann, ast.Name):
        if ann.id == "bool":
            return z3.Bool(arg.arg)
        if ann.id == "float":
            return z3.FP(arg.arg, _F64)
        if ann.id == "str":
            return z3.String(arg.arg)
        if ann.id == "list":
            return _SafeContainer(arg.arg)
        if ann.id == "tuple":
            return _SafeContainer(arg.arg, immutable=True)
        if ann.id in ("set", "frozenset"):                  # sized and iterable, with membership; not subscriptable
            return _SafeContainer(arg.arg, unindexable=True)
        if ann.id in ("bytes", "bytearray"):                # a sized sequence of ints in [0, 255]: bounds-checked
            return _SafeContainer(arg.arg, immutable=(ann.id == "bytes"), byteslike=True)   # index, total len / slice,
        #                                                     byte elements; bytes is immutable (an item store traps)
        if ann.id == "dict":
            return _DictParam(arg.arg)
    if isinstance(ann, ast.Subscript) and isinstance(ann.value, ast.Name):
        base = ann.value.id                                 # a parameterized generic -- list[int], dict[str, int],
        if base in ("list", "List", "Sequence", "MutableSequence"):   # set[T], tuple[...], or a typing alias. A scalar
            return _SafeContainer(arg.arg, elem=_elem_container_proto(ann.slice))   # element type is still ignored; a
        if base in ("tuple", "Tuple"):                      # *sequence* element type makes c[i] a nested sequence
            sl = ann.slice                                  # tuple[T1, .., Tn] is a fixed-arity tuple of exactly n
            n = z3.IntVal(1)                                 # elements; tuple[T, ...] is variadic; tuple[T] is a 1-tuple
            if isinstance(sl, ast.Tuple):
                n = None if any(isinstance(e, ast.Constant) and e.value is Ellipsis for e in sl.elts) \
                    else z3.IntVal(len(sl.elts))             # the exact length, so x, y = t (arity n) raises no ValueError
            return _SafeContainer(arg.arg, immutable=True, length=n, elem=_elem_container_proto(sl))
        if base in ("set", "frozenset", "Set", "FrozenSet", "MutableSet"):
            return _SafeContainer(arg.arg, unindexable=True)
        if base in ("dict", "Dict", "Mapping", "MutableMapping"):
            vp = (_ann_value(ann.slice.elts[1])              # dict[K, V]: carry the value type V so a read-only
                  if isinstance(ann.slice, ast.Tuple) and len(ann.slice.elts) == 2 else None)   # d[k] models a V
            return _DictParam(arg.arg, valproto=vp)
    if _is_object_annotation(ann):                           # a class / qualified / union annotation: an opaque
        return _Opaque(arg.arg)                              # receiver, so a scalar op on it is UNKNOWN, not a trap
    return z3.Int(arg.arg)


def _gen_symexec(fn, args, z3args, ctx):
    """A finite straight-line generator denotes the tuple of values it yields, which is what its consumers
    observe; `yield from` over a finite iterable splices that iterable in. A generator with branching control
    flow is modeled as the lazily-yielded sequence its consumer observes: the object is opaque (its elements are
    left to the consumer), but the body's iteration traps are surfaced (see the branching case below)."""
    env = dict(z3args)
    yields = []
    saved, ctx.traps = ctx.traps, []
    try:
        try:
            for s in fn.body:
                if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
                    env[s.targets[0].id] = ev(s.value, env, ctx)
                elif isinstance(s, ast.Expr) and isinstance(s.value, ast.Yield) and s.value.value is not None:
                    yields.append(ev(s.value.value, env, ctx))
                elif isinstance(s, ast.Expr) and isinstance(s.value, ast.YieldFrom):
                    it = ev(s.value.value, env, ctx)
                    if not isinstance(it, tuple):
                        raise Unsupported("yield from a non-finite iterable")
                    yields.extend(it)
                elif isinstance(s, ast.Pass) or (isinstance(s, ast.Return) and s.value is None):
                    continue
                else:
                    raise Unsupported(f"generator statement {type(s).__name__} (only straight-line yields)")
            traps = ctx.traps
        except Unsupported:
            # a generator with branching control flow: the lazily-yielded sequence its consumer observes. The
            # object is opaque (its elements are left to the consumer), but the body's ITERATION traps -- a
            # division, an index, a key in a yielded expression -- surface when the consumer iterates, recovered
            # by stripping the yields to expression statements and running the value engine over that body. The
            # traps reference the parameter terms (z3 interns by name, so they match z3args). A body the value
            # engine still cannot model leaves the sequence opaque with no trap (the call recognized as total).
            try:
                _a, _z, _r, body_traps, _n = symexec(ast.unparse(_strip_yields(fn)), Ctx(ctx.repo))
            except Unsupported:
                body_traps = []
            return args, z3args, [(z3.BoolVal(True), _Opaque("generator"))], body_traps, z3.BoolVal(False)
    finally:
        ctx.traps = saved
    return args, z3args, [(z3.BoolVal(True), tuple(yields))], traps, z3.BoolVal(False)


def _stmt_assigned_names(stmts):
    """Names that appear as a Store target anywhere in `stmts`, plus nested def/class names, not descending
    into a nested function/lambda/class body. These are the variables a loop body may rewrite, so the
    trap-freedom engine havocs them when over-approximating the loop."""
    out = set()

    def rec(n):
        for c in ast.iter_child_nodes(n):
            if isinstance(c, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)):
                if hasattr(c, "name"):
                    out.add(c.name)
                continue
            if isinstance(c, ast.Name) and isinstance(c.ctx, ast.Store):
                out.add(c.id)
            rec(c)
    for s in stmts:
        rec(s)
    return out


def _target_names(t):
    return {n.id for n in ast.walk(t) if isinstance(n, ast.Name)}


def _unpack_arity_ok(iter_node, k):
    """True iff a for/comprehension iterable provably yields only k-element unpackable tuples, so
    `for <k names> in iter` cannot raise on the unpack: enumerate (k == 2), and zip / itertools.zip_longest
    over k non-starred positional arguments (each yielded element is a k-tuple). Matched only on the bare
    builtin name (or itertools.zip_longest), never a `.enumerate`/`.zip`/`.items` method, whose element
    shape is arbitrary. A bare container, an arbitrary call, or dict.items() (handled by the value engine's
    tuple_arity, which knows the receiver is a real dict) is not recognized here, so the unpack abstains."""
    if not isinstance(iter_node, ast.Call):
        return False
    f = iter_node.func
    if isinstance(f, ast.Name):
        name = f.id
    elif (isinstance(f, ast.Attribute) and f.attr == "zip_longest"
          and isinstance(f.value, ast.Name) and f.value.id == "itertools"):
        name = "zip_longest"
    else:
        return False
    if name == "enumerate":
        return k == 2
    if name in ("zip", "zip_longest"):
        args = iter_node.args
        return len(args) == k and len(args) >= 1 and not any(isinstance(a, ast.Starred) for a in args)
    return False


def _definitely_not_iterable(x):
    """True iff `x` is a modeled scalar -- an int, float, bool, or fixed-width integer -- which is never
    iterable, so enumerate(x) / zip(..., x, ...) raises TypeError. A container, string, tuple, dict, None,
    or opaque value (unknown, hence possibly iterable) is not flagged, so only a provable scalar traps."""
    if not z3.is_expr(x):
        return False
    s = x.sort()
    return s == z3.IntSort() or s == z3.RealSort() or s == z3.BoolSort() or z3.is_bv_sort(s)


def _recv_root_name(node):
    """The root name a method-call receiver is rooted at -- `a`, `a[i]`, `a.b`, and `a[i].b` all root at `a` --
    or None. A mutating method reached through any of these can change the object `a` holds, so the value
    engine forgets `a` after such a call: `[[0]] * 2` aliases ONE inner row (sequence repetition replicates the
    reference), so an append through `a[0]` grows `a[1]` too, and the engine -- which models a list as an
    immutable tuple -- must not read the stale pre-mutation row (a false `len(a[1]) == 1`)."""
    while isinstance(node, (ast.Subscript, ast.Attribute)):
        node = node.value
    return node.id if isinstance(node, ast.Name) else None


def _holds_identity(val, obj):
    """Whether `val` IS `obj`, or is a tuple transitively containing it by object identity -- used to forget
    every name that aliases or shares the object a mutating method just changed in place. The value engine
    models a list as an immutable tuple with no shared identity, so `b = a` (an alias) and `[[0]] * 2` (a shared
    inner row) both let a mutation through one name leave another name's stale value behind; this finds them."""
    if val is obj:
        return True
    if isinstance(val, tuple):
        return any(_holds_identity(x, obj) for x in val)
    return False


def _assigns_none(stmts):
    """Names a statement list assigns the None literal to directly (`nm = None`), so a loop havoc of nm
    would unsoundly drop the possibility that it is None (and mask a later None-in-arithmetic trap)."""
    out = set()
    for s in stmts:
        for n in ast.walk(s):
            if isinstance(n, ast.Assign) and isinstance(n.value, ast.Constant) and n.value.value is None:
                for t in n.targets:
                    if isinstance(t, ast.Name):
                        out.add(t.id)
    return out


def _kind_term(name, kind):
    """A trap-freedom term for a parameter whose kind was inferred from usage: a container or sequence is an
    opaque value (its length and elements are symbolic; an integer index is bounds-checked), a string is a
    Z3 string, anything else an Int."""
    if kind in ("container", "seq"):
        return _SafeContainer(name)
    if kind == "str":
        return z3.String(name)
    if kind == "dict":                                        # a parameter read d[k] with a non-integer key is a
        return _DictParam(name)                               # dict: d[k] traps (KeyError) unless k is provably a key
    if kind == "object":                                      # a parameter used only as o.attr is an opaque object, so
        return _Opaque(name)                                  # o.x is a stable field (duck-typed numeric in arithmetic)
    if kind == "float":                                       # usage commits to float (a non-integral float literal,
        return z3.FP(name, _F64)                              # or a float-only method), not the default int
    return z3.Int(name)


_MUTATING_METHODS = frozenset({"pop", "append", "insert", "remove", "extend", "clear", "popitem",
                               "add", "discard", "update", "setdefault", "sort", "reverse"})


def _mutate_once_containers(fn):
    """Container names mutated by exactly one .pop() / .remove() and nothing else in `fn`: that single
    mutation's trap (an empty pop, an out-of-range pop(i), a missing-key dict pop, a missing-element remove)
    can be modeled against the container's stable symbolic length / membership without tracking the
    post-mutation state, since one mutation in loop-free code runs at most once per path. A name with a second
    such mutation, or any other mutating call (append / insert / extend / item store), is excluded. Two
    mutations in mutually exclusive branches are excluded too."""
    tracked, other = {}, set()
    for n in ast.walk(fn):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Name):
            nm = n.func.value.id
            if n.func.attr in ("pop", "remove", "popitem"):
                tracked[nm] = tracked.get(nm, 0) + 1
            elif n.func.attr in _MUTATING_METHODS:
                other.add(nm)
            if nm == "heapq" and n.args and isinstance(n.args[0], ast.Name):
                hn = n.args[0].id                            # heapq.heappop(h) pops h; heappush / heapify / ... mutate it
                if n.func.attr == "heappop":
                    tracked[hn] = tracked.get(hn, 0) + 1
                elif n.func.attr in ("heappush", "heapify", "heapreplace", "heappushpop"):
                    other.add(hn)
        elif isinstance(n, (ast.Assign, ast.AugAssign)):
            targets = n.targets if isinstance(n, ast.Assign) else [n.target]
            for t in targets:
                if isinstance(t, ast.Subscript) and isinstance(t.value, ast.Name):
                    other.add(t.value.id)                    # an item store mutates the container too
    return frozenset(nm for nm, c in tracked.items() if c == 1 and nm not in other)


def _is_set_like(v):
    """A set / frozenset parameter or a set-operation result: a sized, iterable, non-subscriptable container
    whose membership predicate is sound (so a set operation on it can be combined)."""
    return isinstance(v, _SafeContainer) and v.unindexable


def _set_binop(opsym, l, r, ctx):
    """A set operation (| & - ^) of two set-like containers as a _SetExpr (trap free) with its size relation:
    union superset of each and <= their sum, intersection subset of each, difference drops at most |r|."""
    res = _SetExpr(opsym, l, r, length=z3.FreshInt("setlen"))
    if ctx.facts is not None:
        ln, rn, m = _container_len(l, ctx), _container_len(r, ctx), res.length
        ctx.facts.append(m >= 0)
        if opsym == "|":
            ctx.facts += [m <= ln + rn, m >= ln, m >= rn]
        elif opsym == "&":
            ctx.facts += [m <= ln, m <= rn]
        elif opsym == "-":
            ctx.facts += [m <= ln, m >= ln - rn]
        else:                                                # ^ : symmetric difference
            ctx.facts.append(m <= ln + rn)
    return res


def _seq_member(seq, x, ctx):
    """Membership of `x` in opaque sequence parameter `seq`: a stable uninterpreted predicate keyed on the
    sequence name and the element sort (int and string elements tracked separately), so an `x in seq` guard
    connects to seq.index(x) / seq.remove(x) and, via the fact member => len(seq) >= 1, to a subsequent index.
    A set-operation result combines its operands' membership. None for an element type the predicate does not model."""
    if isinstance(seq, _SetExpr):                            # membership in a set operation is its operands' combination
        ml = _seq_member(seq.left, x, ctx)
        mr = _seq_member(seq.right, x, ctx)
        if ml is None or mr is None:
            return None
        combined = {"|": z3.Or, "&": z3.And, "-": lambda a, b: z3.And(a, z3.Not(b)),
                    "^": z3.Xor}[seq.op](ml, mr)
        if ctx is not None and ctx.facts is not None:
            ctx.facts.append(z3.Implies(combined, _container_len(seq, ctx) >= 1))   # a member means non-empty
        return combined
    if not z3.is_expr(x):
        return None
    s = x.sort()
    if s not in (z3.IntSort(), z3.StringSort()):
        return None
    m = z3.Function("mem_seq_" + seq.name + "_" + ("i" if s == z3.IntSort() else "s"), s, z3.BoolSort())(x)
    if ctx is not None and ctx.facts is not None:
        ctx.facts.append(z3.Implies(m, _container_len(seq, ctx) >= 1))   # a member means the sequence is non-empty
    return m


def _tracked_dict_names(fn):
    """Local names sound to model as value-engine dicts: a name assigned a key-enumerable dict literal,
    {}, or dict() (no **), never a parameter or otherwise reassigned, and every occurrence of which is
    the base of a subscript (name[...]) or such a dict-defining assignment target. The dict is then only
    ever built and read through name[...], so it cannot escape (a call argument, a return, an alias, a
    method receiver) where a mutation the engine does not see could change its keys -- the condition that
    makes _MapVal's keyed reads and KeyError traps sound."""
    params = {a.arg for a in fn.args.posonlyargs + fn.args.args + fn.args.kwonlyargs}
    if fn.args.vararg:
        params.add(fn.args.vararg.arg)
    if fn.args.kwarg:
        params.add(fn.args.kwarg.arg)

    def is_dict_def(v):
        return ((isinstance(v, ast.Dict) and all(k is not None for k in v.keys))
                or (isinstance(v, ast.Call) and isinstance(v.func, ast.Name)
                    and v.func.id in ("dict", "OrderedDict") and not v.args and not v.keywords))

    ok_ids, defined, bad = set(), set(), set()
    for n in ast.walk(fn):
        if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name):
            ok_ids.add(id(n.value))                          # name[...] : a legitimate use
        elif isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Name):
                    (defined if is_dict_def(n.value) else bad).add(t.id)
                    if is_dict_def(n.value):
                        ok_ids.add(id(t))
        elif isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name):
            if n.value is not None and is_dict_def(n.value):
                ok_ids.add(id(n.target)); defined.add(n.target.id)
            else:
                bad.add(n.target.id)
        elif isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name):
            bad.add(n.target.id)                             # name op= ... : not a fresh dict
    cand = defined - bad - params
    for n in ast.walk(fn):                                   # every occurrence must be a sanctioned one
        if isinstance(n, ast.Name) and n.id in cand and id(n) not in ok_ids:
            cand.discard(n.id)
    return frozenset(cand)


_DICT_READONLY_METHODS = frozenset({"get", "keys", "values", "items", "copy", "fromkeys"})


def _readonly_dict_names(fn):
    """Dict parameters provably never mutated, reassigned, aliased, or passed where a callee could mutate them, so a
    read d[k] is a fixed function of k and may be memoized (a guard `if d[k] != 0:` then `10 // d[k]` is sound). Every
    Load occurrence of the name must be a sanctioned read: d[...] (load), `k in d`, `for .. in d`, len(d), or a non-
    mutating method (get / keys / values / items / copy). Any other occurrence -- a subscript store / del, a mutating
    or unknown method, a reassignment, an alias, or use as a call argument -- disqualifies the name."""
    params = {a.arg for a in fn.args.posonlyargs + fn.args.args + fn.args.kwonlyargs}
    ok_ids, bad = set(), set()
    for n in ast.walk(fn):
        if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name) and isinstance(n.ctx, ast.Load):
            ok_ids.add(id(n.value))                          # d[...] : a read (a store subscript's value is ctx=Store)
        elif isinstance(n, ast.Compare):
            for op, comp in zip(n.ops, n.comparators):
                if isinstance(op, (ast.In, ast.NotIn)) and isinstance(comp, ast.Name):
                    ok_ids.add(id(comp))                     # k in d
        elif isinstance(n, ast.For) and isinstance(n.iter, ast.Name):
            ok_ids.add(id(n.iter))                           # for .. in d
        elif isinstance(n, ast.Call):
            if (isinstance(n.func, ast.Name) and n.func.id == "len"
                    and len(n.args) == 1 and isinstance(n.args[0], ast.Name)):
                ok_ids.add(id(n.args[0]))                    # len(d)
            if (isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Name)
                    and n.func.attr in _DICT_READONLY_METHODS):
                ok_ids.add(id(n.func.value))                 # d.get(...) / d.keys() / ... (non-mutating)
        elif isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
            for t in (n.targets if isinstance(n, ast.Assign) else [n.target]):
                if isinstance(t, ast.Name):
                    bad.add(t.id)                            # d reassigned (a different / mutated dict)
    for n in ast.walk(fn):                                   # any unsanctioned Load (alias, call arg, return, ...) is bad
        if isinstance(n, ast.Name) and n.id in params and isinstance(n.ctx, ast.Load) and id(n) not in ok_ids:
            bad.add(n.id)
    return frozenset(params - bad)


def _assign_target(tgt, val, env, ctx):
    """Assign an already-evaluated value to one target -- a name, an attribute, or a (bounds-checked)
    subscript -- so a tuple unpacking with mixed targets (the in-place swap a[i], a[j] = a[j], a[i]) reuses
    the same store semantics as a single assignment. A name binds in env; an attribute store raises at most
    AttributeError (opaque, no modeled trap); a subscript store is in-bounds-checked exactly like a load (a
    tuple item store is a TypeError, a sequence index out of range an IndexError). Declines any other target."""
    if isinstance(tgt, ast.Name):
        env[tgt.id] = val
    elif isinstance(tgt, ast.Attribute):
        ev(tgt.value, env, ctx)                              # a.b = v: a store through an opaque object
    elif isinstance(tgt, ast.Subscript):
        base = ev(tgt.value, env, ctx)
        if not isinstance(base, _Opaque):
            raise Unsupported("item assignment to a possibly non-container")
        if isinstance(base, _NdArray):
            _nd_store_traps(base, tgt.slice, env, ctx)       # ndarray a[i] = v: bounds-check each axis
        else:
            idx = None if isinstance(tgt.slice, ast.Slice) else ev(tgt.slice, env, ctx)
            if isinstance(base, _SafeContainer) and (base.immutable or base.unindexable) and ctx.traps is not None:
                ctx.traps.append(ctx.pc)                     # tuple / set item assignment always raises TypeError
            elif idx is not None and isinstance(base, _SafeContainer) and ctx.traps is not None \
                    and z3.is_expr(idx) and idx.sort() == z3.IntSort():
                n = _container_len(base, ctx)
                ctx.traps.append(z3.And(ctx.pc, z3.Or(idx < -n, idx >= n)))   # IndexError on store
    else:
        raise Unsupported("complex assignment target")


def _unpack_seq(elts, val, env, ctx):
    """Bind a tuple/list of unpacking targets to a tuple value, with at most one starred sub-target and
    recursion into nested tuple/list targets ((a, b), c = ...). The value must be a tuple of matching arity
    (a non-tuple or arity mismatch raises Unsupported, so the caller abstains). Names bind in env; a starred
    name takes the middle slice. Used by the symexec walk for tuple unpacking, flat and nested."""
    if not isinstance(val, tuple):
        if BEST_EFFORT:                                      # unpack an unmodeled iterable: bind every target name fresh
            _best_effort_assume()
            for t in elts:
                for nm in ast.walk(t):
                    if isinstance(nm, ast.Name):
                        env[nm.id] = z3.FreshInt("be_unpack")
            return
        raise Unsupported("unpacking a non-tuple value")
    stars = [i for i, t in enumerate(elts) if isinstance(t, ast.Starred)]
    if len(stars) > 1:
        raise Unsupported("multiple starred targets")
    if not stars:
        if len(val) != len(elts):
            raise Unsupported("tuple unpacking arity mismatch")
        for t, vv in zip(elts, val):
            _unpack_elt(t, vv, env, ctx)
    else:
        si = stars[0]
        before, after = elts[:si], elts[si + 1:]
        if len(val) < len(before) + len(after):
            raise Unsupported("not enough values to unpack")
        for t, vv in zip(before, val[:len(before)]):
            _unpack_elt(t, vv, env, ctx)
        env[elts[si].value.id] = val[len(before):len(val) - len(after)]   # *rest -> the middle slice
        for t, vv in zip(after, val[len(val) - len(after):]):
            _unpack_elt(t, vv, env, ctx)


def _unpack_elt(tgt, val, env, ctx):
    """Bind one unpacking-target element to a value: a Name binds; a nested tuple/list target recurses through
    _unpack_seq (requiring a matching-length tuple value). Any other element declines (Unsupported)."""
    if isinstance(tgt, ast.Name):
        env[tgt.id] = val
    elif isinstance(tgt, (ast.Tuple, ast.List)):
        _unpack_seq(tgt.elts, val, env, ctx)                  # (a, b), c = ... : a nested target
    else:
        raise Unsupported("unsupported nested unpacking target")


_PASSTHROUGH_DECO = frozenset({"lru_cache", "cache", "wraps", "staticmethod", "classmethod", "property",
                               "cached_property", "abstractmethod", "abstractproperty", "final", "override"})


def _is_passthrough_decorator(d):
    """True if decorator d preserves the function's input->output behavior, so analyzing the undecorated body is
    sound: a memoizer (functools.lru_cache / cache, including the @lru_cache(maxsize=...) call form), functools.wraps,
    or a binding / marker decorator (staticmethod, classmethod, property, the abstract / typing markers)."""
    name = d.func if isinstance(d, ast.Call) else d
    if isinstance(name, ast.Attribute):
        return name.attr in _PASSTHROUGH_DECO
    if isinstance(name, ast.Name):
        return name.id in _PASSTHROUGH_DECO
    return False


def _counter_delta(nm, value):
    """The integer constant c if `value` is nm + c, c + nm, or nm - c (a counter's per-iteration step on nm), else
    None. c - nm is not a counter (it negates the accumulator each step)."""
    if not isinstance(value, ast.BinOp) or not isinstance(value.op, (ast.Add, ast.Sub)):
        return None
    if isinstance(value.left, ast.Name) and value.left.id == nm:           # nm + c  /  nm - c
        k = _const_num(value.right)
        if isinstance(k, int):
            return k if isinstance(value.op, ast.Add) else -k
    if isinstance(value.op, ast.Add) and isinstance(value.right, ast.Name) and value.right.id == nm:   # c + nm
        k = _const_num(value.left)
        if isinstance(k, int):
            return k
    return None


def _loop_counters(body):
    """{name: step} for each accumulator unconditionally stepped by an integer constant once per iteration of a loop
    body -- a top-level s = s + c (or c + s, s - c) with no other write to s -- so its post-loop value is the
    pre-loop value plus step * iteration count. A name written conditionally (under an If), more than once, or by
    any other form is excluded, since the per-iteration step would then not be a single constant."""
    inc, other = {}, set()
    for s in body:
        if (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                and s.targets[0].id not in other):
            nm = s.targets[0].id
            c = _counter_delta(nm, s.value)
            if c is not None and nm not in inc:
                inc[nm] = c
                continue
        for nm in _stmt_assigned_names([s]):       # any other write (conditional, repeated, non-counter) disqualifies
            other.add(nm); inc.pop(nm, None)
    return {nm: c for nm, c in inc.items() if nm not in other}


def _havoc_val(prev, nm):
    """A fresh value for a loop-havoc'd name, preserving a container kind so a bytes/list accumulator (string = x +
    string) stays a container, not an int -- otherwise a later concat/index on it hits 'arithmetic on an unmodeled
    value'. Sound: the loop havoc withholds REFUTED regardless, so an over-broad container kind only costs precision
    (a missed PROVED), never a wrong verdict."""
    if isinstance(prev, _SafeContainer):
        return _SafeContainer("hv_" + nm, byteslike=prev.byteslike, unindexable=prev.unindexable)
    if isinstance(prev, tuple):             # a list / tuple literal (a = [0]; a = a + [i]) crossing the loop stays a
        return _SafeContainer("hv_" + nm)   # sequence of opaque length, so a later len / index / concat is modeled
    if _is_str(prev):
        return z3.String("hv_" + nm)        # a string accumulator (out = out + c) stays a string, not an int
    if _is_fp(prev):                        # a float accumulator (x = x + 1.0) stays a float, not an int -- else a
        return z3.FreshConst(_F64, "hv_" + nm)   # later float-only op (a bitwise x & 1, a TypeError) is unsoundly
        #                                          modeled as a valid int operation
    return z3.FreshInt("hv_" + nm)


def symexec(src: str, ctx: Ctx, argvals=None, param_kinds=None):
    """Loop-free function -> (arg_names, z3_args, [(path_cond, value)], traps, none_pc).
    `traps` is the conditions under which the function divides by zero; `none_pc` is the
    condition under which it returns None (a bare return or falling off the end). When `argvals`
    is given the parameters are bound to those values (a call-site-specialized inline, used for
    higher-order calls so callable parameters resolve), instead of fresh symbolic terms."""
    _mod = _parse(src)
    fn = next((n for n in _mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
    if fn is None:
        raise Unsupported("no function definition")           # leading module-level imports are skipped
    if isinstance(fn, ast.AsyncFunctionDef) or any(           # a coroutine: reason about its awaited result, so
            isinstance(n, (ast.Await, ast.AsyncFor, ast.AsyncWith)) for n in ast.walk(fn)):   # an inlined repo
        fn = _StripAsync().visit(fn); ast.fix_missing_locations(fn)   # coroutine resolves (await e -> e); see _strip_async
    if fn.decorator_list and not all(_is_passthrough_decorator(d) for d in fn.decorator_list):
        raise Unsupported("decorated function is not modeled (the decorator may change the callable)")
    _params = list(fn.args.args) + list(fn.args.kwonlyargs)   # positional + keyword-only parameters
    args = [a.arg for a in _params]
    if argvals is not None:
        if len(argvals) != len(args):
            raise Unsupported("specialized inline arity mismatch")
        z3args = dict(zip(args, argvals))
    else:
        z3args = {a.arg: (_kind_term(a.arg, param_kinds[a.arg])     # inferred kind for an unannotated param
                          if param_kinds and a.arg in param_kinds and a.annotation is None
                          else _param_term(a)) for a in _params}
    # *args -> bounds-checked sequence, **kwargs -> dict (read traps unless key proven present); env-only.
    if fn.args.vararg is not None and fn.args.vararg.arg not in z3args:
        z3args[fn.args.vararg.arg] = _SafeContainer(fn.args.vararg.arg)
    if fn.args.kwarg is not None and fn.args.kwarg.arg not in z3args:
        z3args[fn.args.kwarg.arg] = _DictParam(fn.args.kwarg.arg)
    if any(isinstance(n, (ast.Yield, ast.YieldFrom)) for n in ast.walk(fn)):
        return _gen_symexec(fn, args, z3args, ctx)
    rets: List[Tuple[z3.ExprRef, z3.ExprRef]] = []
    none_list: List[z3.ExprRef] = []

    saved_traps, saved_pc = ctx.traps, ctx.pc
    saved_td, saved_po = ctx.tracked_dicts, ctx.mutate_once
    saved_np, saved_fa = ctx.numeric_params, ctx.func_aliases
    ctx.func_aliases = _functional_aliases(_mod)              # names bound to torch.nn.functional in this module
    ctx.tracked_dicts = _tracked_dict_names(fn)               # this function's value-engine-modeled dicts
    ctx.readonly_dicts = _readonly_dict_names(fn)             # dict params whose reads d[k] memoize to a stable value
    ctx.dval_cache = {}                                       # fresh per symexec run
    ctx.mutate_once = _mutate_once_containers(fn)             # containers whose single .pop()/.remove() is sound to model
    ctx.numeric_params = frozenset(a.arg for a in _params     # params explicitly typed int/float/bool: a number, so
                                   if isinstance(a.annotation, ast.Name)   # a method call on one is an AttributeError,
                                   and a.annotation.id in ("int", "float", "bool"))   # not a duck-typed opaque object
    local_traps = _TrapList(ctx) if getattr(ctx, "track_trap_lines", False) else []
    ctx.traps = local_traps

    def walk(stmts, env, pc):
        falls = [(dict(env), pc)]
        for s in stmts:
            nxt = []
            for e, p in falls:
                ctx.pc = p
                if isinstance(s, ast.Return):
                    if s.value is None:
                        none_list.append(p)                       # bare return -> None
                    else:
                        rets.append((p, ev(s.value, e, ctx)))
                elif isinstance(s, ast.Assign):
                    if len(s.targets) != 1:
                        if _TRAPFREE and all(isinstance(t, (ast.Name, ast.Subscript, ast.Attribute))
                                             for t in s.targets):
                            # a = b = expr, and the chained store a = b[i] = expr: Python evaluates the right
                            # side once, then assigns it to every target left to right. Store it to each target
                            # with the same bounds checks a single assignment uses -- a subscript store is
                            # IndexError-checked, an attribute store raises no modeled trap, a name binds.
                            v = ev(s.value, e, ctx); e2 = dict(e)
                            for t in s.targets:
                                _assign_target(t, v, e2, ctx)
                            nxt.append((e2, p)); continue
                        raise Unsupported("multiple assignment targets")
                    tgt = s.targets[0]
                    if isinstance(tgt, ast.Name):
                        e2 = dict(e)
                        e2[tgt.id] = ev(s.value, e2, ctx)
                        nxt.append((e2, p))
                    elif isinstance(tgt, (ast.Tuple, ast.List)) and all(
                            isinstance(t, (ast.Name, ast.Starred, ast.Tuple, ast.List)) for t in tgt.elts):
                        val = ev(s.value, e, ctx)            # tuple unpacking: x, y = expr ; a, *b, c ; (a, b), c
                        if (_TRAPFREE and isinstance(val, _SafeContainer) and ctx.traps is not None
                                and all(isinstance(t, ast.Name) for t in tgt.elts)):
                            # unpacking a sequence parameter into N names raises ValueError unless len(seq) == N
                            # (CPython requires the exact arity), so an unguarded a, b = xs is refuted on a
                            # length-mismatched witness, a len() == N guard proves it, and each name becomes an
                            # arbitrary element. A starred target (a, *b, c) is handled just below.
                            ctx.traps.append(z3.And(ctx.pc, _container_len(val, ctx) != len(tgt.elts)))
                            e2 = dict(e)
                            for nm in tgt.elts:
                                e2[nm.id] = z3.FreshInt("unpack")
                            nxt.append((e2, p)); continue
                        _stars = [t for t in tgt.elts if isinstance(t, ast.Starred)]
                        if (_TRAPFREE and isinstance(val, _SafeContainer) and ctx.traps is not None
                                and len(_stars) == 1 and isinstance(_stars[0].value, ast.Name)
                                and all(isinstance(t, ast.Name) or t is _stars[0] for t in tgt.elts)):
                            # a, *b, c = seq : ValueError unless len(seq) >= the fixed-name count; each fixed name is an
                            # arbitrary element and *b is the middle slice (length len(seq) - that count), so a later
                            # b[0] / len(b) stays sound (b is empty exactly when len(seq) == the fixed count).
                            fixed = len(tgt.elts) - 1
                            L = _container_len(val, ctx)
                            ctx.traps.append(z3.And(ctx.pc, L < fixed))
                            e2 = dict(e)
                            for t in tgt.elts:
                                if t is _stars[0]:
                                    e2[t.value.id] = _SafeContainer("unpack_star", byteslike=val.byteslike,
                                                                    length=z3.If(L >= fixed, L - fixed, z3.IntVal(0)))
                                else:
                                    e2[t.id] = z3.FreshInt("unpack")
                            nxt.append((e2, p)); continue
                        e2 = dict(e)
                        _unpack_seq(tgt.elts, val, e2, ctx)   # flat or nested ((a, b), c), with one starred target
                        nxt.append((e2, p))
                    elif (isinstance(tgt, (ast.Tuple, ast.List))
                          and all(isinstance(t, (ast.Name, ast.Subscript, ast.Attribute)) for t in tgt.elts)
                          and any(isinstance(t, (ast.Subscript, ast.Attribute)) for t in tgt.elts)):
                        # unpacking to mixed targets -- the in-place swap a[i], a[j] = a[j], a[i], or
                        # self.x, self.y = ... -- evaluates the whole right side first (Python's semantics),
                        # then stores to each target with the same bounds checks a single assignment uses.
                        val = ev(s.value, e, ctx)
                        if not isinstance(val, tuple) or len(val) != len(tgt.elts):
                            raise Unsupported("unpacking to mixed targets needs a matching-length tuple")
                        e2 = dict(e)
                        for tt, vv in zip(tgt.elts, val):
                            _assign_target(tt, vv, e2, ctx)
                        nxt.append((e2, p))
                    elif (isinstance(tgt, ast.Subscript) and isinstance(tgt.value, ast.Name)
                          and tgt.value.id in ctx.tracked_dicts and isinstance(e.get(tgt.value.id), _MapVal)):
                        if isinstance(tgt.slice, ast.Slice):     # d[k] = v on a tracked dict: record the entry
                            raise Unsupported("a dict is not sliceable")
                        kk = _map_key(ev(tgt.slice, e, ctx))
                        vv = ev(s.value, e, ctx)                 # the key and value are trap-checked here
                        e2 = dict(e); e2[tgt.value.id] = e[tgt.value.id].store(kk, vv)
                        nxt.append((e2, p))
                    elif _TRAPFREE and isinstance(tgt, ast.Attribute):
                        ev(s.value, e, ctx); ev(tgt.value, e, ctx)   # a.b = v: a store raises at most AttributeError
                        nxt.append((e, p))
                    elif _TRAPFREE and isinstance(tgt, ast.Subscript):
                        val = ev(s.value, e, ctx)            # a[i] = v: the stored value is trap-checked
                        base = ev(tgt.value, e, ctx)         # a write through an opaque container raises no modeled trap
                        if (isinstance(base, _ListLit) and isinstance(tgt.value, ast.Name)
                                and not isinstance(tgt.slice, ast.Slice)):
                            # a = [1, 2, 3]; a[i] = v -- a mutable list literal of known length: IndexError when i is
                            # out of [-n, n) (modeled exactly against the known length), else the element is updated
                            # (exact for a constant index; an opaque-element container of the same length for a
                            # symbolic one, which is sound -- the length is unchanged and elements become arbitrary).
                            n = len(base)
                            idx = ev(tgt.slice, e, ctx)
                            if not (z3.is_expr(idx) and z3.is_int(idx)):
                                raise Unsupported("list item assignment with a non-integer index")
                            if ctx.traps is not None:
                                ctx.traps.append(z3.And(p, z3.Or(idx < -n, idx >= n)))   # IndexError on store
                            e2 = dict(e)
                            if z3.is_int_value(idx) and -n <= idx.as_long() < n:
                                items = list(base); items[idx.as_long()] = val
                                e2[tgt.value.id] = _ListLit(items)            # exact element update at a constant index
                            else:
                                e2[tgt.value.id] = _SafeContainer("listmut", length=z3.IntVal(n))
                            nxt.append((e2, p)); continue
                        if not isinstance(base, _Opaque):    # a scalar -> UNKNOWN; a sequence parameter is bounds-
                            raise Unsupported("item assignment to a possibly non-container")   # checked like a load
                        if isinstance(base, _NdArray):
                            _nd_store_traps(base, tgt.slice, e, ctx)   # ndarray a[i] = v: bounds-check each axis
                        else:
                            is_slice = isinstance(tgt.slice, ast.Slice)
                            idx = None if is_slice else ev(tgt.slice, e, ctx)
                            if isinstance(base, _SafeContainer) and (base.immutable or base.unindexable) and ctx.traps is not None:
                                ctx.traps.append(p)          # item assignment to a tuple / set always raises TypeError
                            elif idx is not None and isinstance(base, _SafeContainer) and ctx.traps is not None \
                                    and z3.is_expr(idx) and idx.sort() == z3.IntSort():
                                n = _container_len(base, ctx)
                                ctx.traps.append(z3.And(p, z3.Or(idx < -n, idx >= n)))   # IndexError on store
                        nxt.append((e, p))
                    else:
                        raise Unsupported("complex assignment target")
                elif isinstance(s, ast.If):
                    c = ev_bool(s.test, e, ctx)
                    nxt += walk(s.body, e, z3.And(p, c))
                    nxt += walk(s.orelse, e, z3.And(p, z3.Not(c)))
                elif isinstance(s, (ast.Import, ast.ImportFrom, ast.Pass, ast.Global, ast.Nonlocal)):
                    nxt.append((e, p))                        # import / global / nonlocal: no-ops here
                elif isinstance(s, ast.Delete):
                    e2 = dict(e)
                    for tg in s.targets:
                        if isinstance(tg, ast.Name):
                            e2.pop(tg.id, None)               # del unbinds the name
                        elif _TRAPFREE and isinstance(tg, ast.Attribute):
                            ev(tg.value, e2, ctx)             # del o.attr: at most AttributeError, no modeled trap
                        elif _TRAPFREE and isinstance(tg, ast.Subscript):
                            load = ast.copy_location(ast.Subscript(value=tg.value, slice=tg.slice, ctx=ast.Load()), tg)
                            ev(load, e2, ctx)                 # del c[i]: the IndexError / KeyError a read would raise
                            if isinstance(tg.value, ast.Name):
                                e2[tg.value.id] = _Opaque(tg.value.id)   # the container's contents change: opaque afterward
                        else:
                            raise Unsupported("del of a non-name target")
                    nxt.append((e2, p))
                elif isinstance(s, ast.Assert) and _TRAPFREE:
                    c = ev_bool(s.test, e, ctx)
                    if ctx.traps is not None:                 # a failing assert is an AssertionError trap
                        ctx.traps.append(z3.And(p, z3.Not(c)))
                    nxt.append((e, p))
                elif isinstance(s, ast.Raise) and _TRAPFREE:
                    nm = (s.exc.func.id if isinstance(s.exc, ast.Call) and isinstance(s.exc.func, ast.Name)
                          else s.exc.id if isinstance(s.exc, ast.Name) else None)
                    if isinstance(s.exc, ast.Call):
                        for a2 in s.exc.args:                 # trap-check the exception's arguments
                            if not isinstance(a2, ast.Starred):
                                ev(a2, e, ctx)
                    if nm in _MODELED_TRAP_NAMES and ctx.traps is not None:
                        ctx.traps.append(p)                   # raising a modeled exception is a reachable trap
                    # the raise terminates this path (no fall-through)
                elif isinstance(s, (ast.Break, ast.Continue)) and _TRAPFREE:
                    pass                                      # terminates this path within the havoc'd loop
                elif isinstance(s, ast.AnnAssign) and _TRAPFREE:
                    if isinstance(s.target, ast.Name) and s.value is not None:
                        e2 = dict(e); e2[s.target.id] = ev(s.value, e2, ctx); nxt.append((e2, p))
                    else:
                        if s.value is not None:
                            ev(s.value, e, ctx)
                        nxt.append((e, p))
                elif isinstance(s, ast.FunctionDef):          # nested def: a closure over the current env
                    e2 = dict(e)
                    if len(s.body) == 1 and isinstance(s.body[0], ast.Return) and s.body[0].value is not None:
                        e2[s.name] = _Lambda([a.arg for a in s.args.args], s.body[0].value, dict(e))
                    else:                                     # statement body: opaque value, not modeled if called
                        e2[s.name] = _Closure(s.name)
                    nxt.append((e2, p))
                elif (_TRAPFREE and isinstance(s, ast.Expr) and isinstance(s.value, ast.Call)
                      and _is_noreturn_call(s.value, e)):
                    for a2 in s.value.args:                   # sys.exit / os._exit / exit() / quit(): trap-check the
                        if not isinstance(a2, ast.Starred):    # arguments, then terminate the path (SystemExit is an
                            ev(a2, e, ctx)                     # intentional exit, not a modeled crash) -- no fall-through
                elif isinstance(s, ast.Expr):                 # bare expression statement: for its traps only
                    ev(s.value, e, ctx)
                    c = s.value                               # a method call on a name -- or on a subscript /
                    rn = (_recv_root_name(c.func.value)       # attribute of one (a[0].append(x), self.xs.pop())
                          if isinstance(c, ast.Call) and isinstance(c.func, ast.Attribute) else None)
                    if rn is not None and rn in e:            # -- may mutate the container, so forget the ROOT
                        e2 = dict(e); e2[rn] = _Opaque(rn)    # name: a later read is opaque, not a stale value.
                        if c.func.attr in _MUTATING_METHODS:  # a mutator (append/pop/...) changes the object in
                            try:                              # place; the value engine has no shared identity, so an
                                _obj = ev(c.func.value, e, ctx)   # alias (b = a) or a shared row ([[0]]*2) would read
                            except Unsupported:               # a stale value -- forget every name that aliases or
                                _obj = None                   # transitively contains the mutated object, by identity
                            if _obj is not None:
                                for _nm in list(e2):
                                    if _nm != rn and _holds_identity(e2[_nm], _obj):
                                        e2[_nm] = _Opaque(_nm)
                        nxt.append((e2, p))
                    else:
                        nxt.append((e, p))
                elif isinstance(s, ast.ClassDef) and not s.decorator_list:
                    for base in s.bases:                      # nested class: its base expressions are evaluated
                        ev(base, e, ctx)                      # for traps; the body is deferred and the class
                    for kw in s.keywords:                     # name binds to an opaque value (instantiating it
                        ev(kw.value, e, ctx)                  # is unmodeled, but defining it raises no trap)
                    e2 = dict(e)
                    e2[s.name] = _Opaque(s.name)
                    nxt.append((e2, p))
                elif isinstance(s, ast.While) and _TRAPFREE:
                    ctx.havoc = True
                    he = dict(e)
                    bnone = _assigns_none(s.body)             # names set to None in the body
                    for nm in _stmt_assigned_names(s.body):   # the body rewrites these: take arbitrary values
                        if isinstance(e.get(nm), _NoneVal) or nm in bnone:   # a None that may survive the loop
                            ctx.none_havoc = True              # (0 iterations, or a body None-write) is masked by
                        he[nm] = _havoc_val(e.get(nm), nm)       # this fresh int, so a PROVED here is withheld
                    for _cn, _cs in _loop_counters(s.body).items():   # a monotonic counter (i = i + c) only moves away
                        _init = e.get(_cn)                            # from its start, so the havoc'd value keeps that
                        if (z3.is_expr(_init) and _init.sort() == z3.IntSort() and ctx.facts is not None
                                and z3.is_expr(he.get(_cn)) and he[_cn].sort() == z3.IntSort()):
                            ctx.facts.append(he[_cn] >= _init if _cs > 0 else he[_cn] <= _init)   # i >= 0: p[i] proves
                    ctx.pc = p
                    c = ev_bool(s.test, he, ctx)              # the guard is trap-checked and constrains the body
                    walk(s.body, he, z3.And(p, c))            # one arbitrary iteration under the guard
                    walk(s.orelse, he, p)
                    nxt.append((he, p))                       # after the loop (0+ iterations): havoc'd state
                elif isinstance(s, ast.For) and _TRAPFREE:
                    ctx.pc = p
                    itv = ev(s.iter, e, ctx)                  # iterable trap-checked; a tracked scalar is not
                    if not (isinstance(itv, tuple) or _is_str(itv) or isinstance(itv, _Opaque)):
                        if not BEST_EFFORT:                  # a tracked scalar is not iterable -> UNKNOWN unless best-effort
                            raise Unsupported("iteration over a possibly non-iterable value")
                        _best_effort_assume()
                    # a tuple target `for a, b in it` unpacks each element into k names. Unless the iterable is
                    # known to yield k-tuples -- the value's tuple_arity (enumerate/zip/dict.items over a tracked
                    # container) or the syntax of a fixed-arity builtin (enumerate/zip/zip_longest over anything) --
                    # an element of another shape raises TypeError/ValueError once the loop runs. Withhold the proof
                    # there, as the direct `a, b = xs` unpacking does, for a bare container OR an arbitrary call.
                    if (isinstance(s.target, (ast.Tuple, ast.List)) and ctx.traps is not None and not BEST_EFFORT):
                        _k = len(s.target.elts)
                        _ar = itv.tuple_arity if isinstance(itv, _SafeContainer) else None
                        if _ar != _k and not _unpack_arity_ok(s.iter, _k):
                            _ne = (_container_len(itv, ctx) >= 1) if isinstance(itv, _SafeContainer) else z3.BoolVal(True)
                            ctx.traps.append(z3.And(ctx.pc, _ne))
                    if ctx.exact_traps is not None and isinstance(s.target, ast.Name) and not s.orelse \
                            and isinstance(itv, _SafeContainer):
                        # the first iteration is exact (pre-loop accumulators, a freely-chosen element), so a trap
                        # here is real and witnessable -- it refutes even though later iterations are havoc'd.
                        st, se, sh = ctx.traps, ctx.exact_traps, ctx.havoc
                        first = []; ctx.traps, ctx.exact_traps, ctx.havoc = first, None, False
                        #  reset havoc so `clean` reflects only THIS body's over-approximation, not an enclosing loop's
                        #  -- a nested inner loop's first iteration (first element of an arbitrary row) is itself exact
                        e1 = dict(e); _fe = z3.FreshInt("fe_" + s.target.id)
                        if itv.byteslike and not itv.unindexable and ctx.facts is not None:   # a bytes / bytearray
                            ctx.facts.append(z3.And(_fe >= 0, _fe <= 255))                     # element is an int in
                        e1[s.target.id] = _fe                          # [0, 255]: the exact first-iteration element is
                        #                                                a real byte, never -1 (no fabricated trap)
                        enter = z3.And(p, _container_len(itv, ctx) >= 1)
                        try:
                            walk(s.body, e1, enter)
                            clean = not ctx.havoc             # the body had no nested loop / over-approximation
                        except Unsupported:
                            clean = False
                        ctx.traps, ctx.exact_traps, ctx.havoc = st, se, sh
                        if clean:
                            ctx.exact_traps.extend(first)
                    ctx.havoc = True
                    he = dict(e)
                    bnone = _assigns_none(s.body)             # names set to None in the body
                    for nm in _target_names(s.target) | _stmt_assigned_names(s.body):
                        if isinstance(e.get(nm), _NoneVal) or nm in bnone:   # a possibly-None var havoc'd to an
                            ctx.none_havoc = True              # int would mask a real None-trap, so withhold PROVED
                        he[nm] = _havoc_val(e.get(nm), nm)      # loop variable and body-written names: arbitrary
                    for _cn, _cs in _loop_counters(s.body).items():   # a monotonic counter (i = i + c, e.g. the
                        _init = e.get(_cn)                            # enumerate index from for i, x in enumerate(C, s))
                        if (z3.is_expr(_init) and _init.sort() == z3.IntSort() and ctx.facts is not None
                                and z3.is_expr(he.get(_cn)) and he[_cn].sort() == z3.IntSort()):
                            ctx.facts.append(he[_cn] >= _init if _cs > 0 else he[_cn] <= _init)   # i >= start: dead guard
                    if _is_str(itv) and isinstance(s.target, ast.Name):   # iterating a string yields 1-char strings,
                        cs = z3.String("selem_" + s.target.id)            # so a body doing ord(c) / len(c) / c == '?'
                        if ctx.facts is not None:                         # decides (an arbitrary char over-approximates
                            ctx.facts.append(z3.Length(cs) == 1)          # every element); len(c) == 1, no trap
                        he[s.target.id] = cs
                    elif isinstance(itv, _SafeContainer) and isinstance(itv.elem, _SafeContainer) \
                            and isinstance(s.target, ast.Name):           # iterating a nested container (for row in g)
                        _pr = itv.elem                                    # yields inner sequences -- an arbitrary one of
                        _il = z3.FreshInt("ielem_" + s.target.id)         # nonnegative length, so for x in row decides
                        if ctx.facts is not None:
                            ctx.facts.append(_il >= 0)
                        he[s.target.id] = _SafeContainer("ielem_" + s.target.id, immutable=_pr.immutable,
                                                         length=_il, unindexable=_pr.unindexable,
                                                         byteslike=_pr.byteslike, elem=_pr.elem)
                    elif isinstance(itv, _SafeContainer) and itv.byteslike and not itv.unindexable \
                            and isinstance(s.target, ast.Name):           # iterating bytes / bytearray yields ints in
                        _be = z3.FreshInt("belem_" + s.target.id)         # [0, 255], so an element op -- x % 16, or
                        if ctx.facts is not None:                         # 1000 // (x + 1), never 0 -- decides over
                            ctx.facts.append(z3.And(_be >= 0, _be <= 255))   # every byte rather than abstaining
                        he[s.target.id] = _be
                    body_p = p
                    if isinstance(itv, _DictParam) and isinstance(s.target, ast.Name):
                        kv = he[s.target.id]                  # iterating a dict yields keys: the loop variable is a member
                        if z3.is_expr(kv) and kv.sort() == z3.IntSort():
                            body_p = z3.And(p, _dict_member(itv, kv))
                    walk(s.body, he, body_p)
                    if (isinstance(itv, _SafeContainer) and isinstance(s.target, ast.Name)
                            and not any(isinstance(n, (ast.Break, ast.Continue))
                                        for st in s.body for n in ast.walk(st))):
                        # an unconditional constant-step counter s = s + c runs exactly len(seq) times (no early
                        # exit), so its post-loop value is the exact s_init + c * len -- not a havoc'd fresh int --
                        # and a later trap on it (10 // s, a guard len(seq) >= 1 proving it safe) is decided.
                        L = _container_len(itv, ctx)
                        for nm, c in _loop_counters(s.body).items():
                            init = e.get(nm)
                            if z3.is_expr(init) and init.sort() == z3.IntSort():
                                he[nm] = init + c * L
                    walk(s.orelse, he, p)
                    nxt.append((he, p))
                elif isinstance(s, ast.Try) and _TRAPFREE:
                    for sub in [s.body, s.orelse, s.finalbody] + [h.body for h in s.handlers]:
                        walk(sub, e, p)                       # every block is reachable: each must be trap free
                    ctx.havoc = True
                    he = dict(e)
                    for nm in _stmt_assigned_names([s]):      # where an exception fired is uncertain: havoc
                        he[nm] = _havoc_val(e.get(nm), nm)
                    nxt.append((he, p))
                elif _TRAPFREE and BEST_EFFORT:             # an unmodeled statement: havoc the names it assigns (lower trust)
                    _best_effort_assume()
                    e2 = dict(e)
                    for nm in _stmt_assigned_names([s]):
                        e2[nm] = z3.FreshInt("be_stmt")
                    nxt.append((e2, p))
                else:
                    raise Unsupported(f"statement {type(s).__name__} at line {getattr(s, 'lineno', '?')}")
            falls = nxt
        return falls

    try:
        open_falls = walk(fn.body, z3args, z3.BoolVal(True))
        for _e, p in open_falls:
            none_list.append(p)                                   # fell off the end -> None
    except z3.Z3Exception as e:
        if BEST_EFFORT:                                          # a malformed term; assume the body is well-behaved --
            _best_effort_assume()                                # a trap-free opaque result (lower trust)
            return args, z3args, [(z3.BoolVal(True), _Opaque("be_z3"))], [], z3.BoolVal(False)
        raise Unsupported(f"z3 rejected the encoding ({e})")      # a sort/type clash leaves the body unmodelable here
    finally:
        ctx.traps, ctx.pc, ctx.tracked_dicts, ctx.mutate_once = saved_traps, saved_pc, saved_td, saved_po
        ctx.numeric_params, ctx.func_aliases = saved_np, saved_fa
    none_pc = z3.Or(*none_list) if none_list else z3.BoolVal(False)
    return args, z3args, rets, local_traps, none_pc


def fold(rets) -> z3.ExprRef:
    """Fold a path list into one Z3 term (nested If). Bool return values are coerced to
    their integer value (Python True == 1), so int- and bool-returning paths unify; if any
    path returns a float, every path is promoted to Float64. The base case is unreachable
    (a fall-through with no value is carried separately as none_pc)."""
    if not rets:
        return z3.IntVal(0)
    if any(isinstance(v, (_FuncRef, _Lambda, _Closure, _Opaque)) for _, v in rets):
        if len(rets) == 1:
            return rets[0][1]                                # a single function-valued return: preserve it so a
        return _Opaque("call")                               # caller can apply it; mixed/multiple paths are opaque
    if any(isinstance(v, _Complex) for _, v in rets):        # complex returns: fold each component
        cs = [(pc, _cx(v)) for pc, v in rets]
        return _Complex(fold([(pc, c.re) for pc, c in cs]), fold([(pc, c.im) for pc, c in cs]))
    if any(isinstance(v, tuple) for _, v in rets):           # multi-value returns: fold each position
        width = len(rets[0][1])
        return tuple(fold([(pc, v[i]) for pc, v in rets]) for i in range(width))
    if any(_is_str(v) for _, v in rets):
        base, coerce = z3.StringVal(""), (lambda x: x)
    elif any(_is_real(v) for _, v in rets):
        base, coerce = z3.RealVal(0), _to_real
    elif any(z3.is_fp(v) for _, v in rets):
        base, coerce = z3.fpNaN(_F64), _to_fp
    else:
        base, coerce = z3.IntVal(0), _as_int
    expr = base
    try:
        for pc, val in reversed(rets):
            expr = z3.If(pc, coerce(val), expr)
    except (z3.Z3Exception, TypeError, AttributeError):
        # paths return values of incompatible or unmodeled sorts (e.g. a string on one branch and
        # an integer on another, or a callable/None where a scalar is expected). That is not a
        # discharged property; surface it as UNKNOWN rather than letting a sort error escape.
        raise Unsupported("incompatible or unmodeled return values across paths")
    return expr


# --------------------------------------------------------------------------- #
# General heap: object identity, aliasing, in-place mutation, frame, and lists.   #
# `object()`/`new()` allocates a fresh distinct address; aliasing copies the       #
# address term, so a write through one name is seen through every alias. Attributes  #
# are one Z3 array per name (address -> value), giving frame for free. A list is a    #
# heap object whose payload is a backing array (address -> (index -> element)) and a   #
# length (address -> Int); append/pop/store mutate those through the address, so a list  #
# mutated through one name is observed through its aliases. Index out of range and pop   #
# from empty are traps (IndexError), like division by zero. Loop-free reference code.    #
# --------------------------------------------------------------------------- #
def _heap_arr(heap):
    return heap.setdefault("@arr", z3.K(z3.IntSort(), z3.K(z3.IntSort(), z3.IntVal(0))))


def _heap_len(heap):
    return heap.setdefault("@len", z3.K(z3.IntSort(), z3.IntVal(0)))


def _heap_dval(heap):
    return heap.setdefault("@dval", z3.K(z3.IntSort(), z3.K(z3.IntSort(), z3.IntVal(0))))


def _heap_dkey(heap):
    return heap.setdefault("@dkey", z3.K(z3.IntSort(), z3.K(z3.IntSort(), z3.BoolVal(False))))


def _heap_dn(heap):
    return heap.setdefault("@dn", z3.K(z3.IntSort(), z3.IntVal(0)))


def _heap_sin(heap):
    return heap.setdefault("@sin", z3.K(z3.IntSort(), z3.K(z3.IntSort(), z3.BoolVal(False))))


def _heap_sn(heap):
    return heap.setdefault("@sn", z3.K(z3.IntSort(), z3.IntVal(0)))


def _heap_present(heap, attr):
    """The per-attribute presence array (address -> Bool): True where the attribute has been assigned on
    this path, default False. Lets hasattr / getattr-with-default decide attribute presence soundly, where
    the value arrays alone cannot distinguish an unset attribute (which reads as 0) from one set to 0."""
    return heap.setdefault("@present_" + attr, z3.K(z3.IntSort(), z3.BoolVal(False)))


def _heap_mark_present(heap, attr, addr):
    """Record that `attr` is present on the object at `addr`, at every attribute store, so a later
    hasattr(o, attr) sees it. Mirrors the value store, riding the same per-path heap-array merge."""
    heap["@present_" + attr] = z3.Store(_heap_present(heap, attr), addr, z3.BoolVal(True))


# Specification vocabulary over the heap: a postcondition that takes (z3args, ret, heap) can
# quantify over the structure a function returns, not just integer outputs.
def heap_attr(heap, addr, name):
    """Attribute `name` of the object at `addr`."""
    return z3.Select(heap.get(name, z3.K(z3.IntSort(), z3.IntVal(0))), addr)


def list_len(heap, addr):
    """Length of the list at `addr`."""
    return z3.Select(_heap_len(heap), addr)


def list_get(heap, addr, i):
    """Element `i` of the list at `addr`."""
    return z3.Select(z3.Select(_heap_arr(heap), addr), i)


def list_forall(heap, addr, body):
    """Universally quantify a predicate `body(element)` over every element of the list at `addr`."""
    j = z3.FreshInt("spec")
    return z3.ForAll([j], z3.Implies(z3.And(0 <= j, j < list_len(heap, addr)), body(list_get(heap, addr, j))))


def _kind_of(node, kinds):
    """The collection kind a value expression produces, for subscript / membership dispatch.
    Aliasing copies a name's kind; a literal or constructor fixes it; otherwise None."""
    if isinstance(node, ast.List):
        return "list"
    if isinstance(node, ast.Dict):
        return "dict"
    if isinstance(node, ast.Set):
        return "set"
    if isinstance(node, ast.Name):
        return kinds.get(node.id)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ("list", "dict", "set", "frozenset"):
        return node.func.id
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and isinstance(node.slice, ast.Slice):
        return kinds.get(node.value.id)                      # a slice of a list is itself a list
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
        return kinds.get(("@attr", node.attr))               # a container-valued instance attribute (self.items)
    if isinstance(node, ast.BinOp):                          # list concatenation/repetition is a list
        lk, rk = _kind_of(node.left, kinds), _kind_of(node.right, kinds)
        if isinstance(node.op, ast.Add) and lk == "list" and rk == "list":
            return "list"
        if isinstance(node.op, ast.Mult) and (lk == "list" or rk == "list"):
            return "list"
    return None


def _attr_kinds(classes):
    """Statically infer each instance attribute's collection kind from the `self.<attr> = <literal>`
    assignments across every method of every class, so a container-valued attribute (self.items = [])
    drives its list / dict / set operations like a local of that kind. A literal list/dict/set or a
    list()/dict()/set()/frozenset() call fixes the kind; an attribute assigned conflicting kinds across
    classes, or a non-container value, is left untracked, so its operations abstain rather than guess.
    Keyed by ("@attr", name) so it shares the `kinds` map a receiver expression is resolved through."""
    def _lit_kind(v):
        if isinstance(v, ast.List):
            return "list"
        if isinstance(v, ast.Dict):
            return "dict"
        if isinstance(v, ast.Set):
            return "set"
        if isinstance(v, ast.Call) and isinstance(v.func, ast.Name):
            if v.func.id in ("list", "dict", "set", "frozenset"):
                return v.func.id
            if v.func.id in classes:                          # self.attr = D(): an instance of a known repo class,
                return v.func.id                              # so self.attr.method() dispatches along D's MRO
        return None
    out, conflict = {}, set()
    for cnode in classes.values():
        if not isinstance(cnode, ast.ClassDef):
            continue
        for n in ast.walk(cnode):
            if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Attribute) \
                    and isinstance(n.targets[0].value, ast.Name) and n.targets[0].value.id == "self":
                key = ("@attr", n.targets[0].attr)
                k = _lit_kind(n.value)
                if k is None:                                # a non-literal assignment (a param, a call result): the
                    conflict.add(key)                        # attribute's kind is ambiguous, so abstain rather than
                    continue                                 # assume it -- dispatching on the wrong type is unsound
                if key in out and out[key] != k:
                    conflict.add(key)
                out[key] = k
    for key in conflict:
        out.pop(key, None)                                   # ambiguous across classes: abstain
    return out


def _heap_recv_expr(v, env):
    """A subscript / collection-method receiver the heap engine resolves to a heap identity: a local name,
    or a self.<attr> attribute access whose object is a bound local. (The kind, when needed to disambiguate
    list / dict / set, is _kind_of(v, kinds); an attribute with no tracked kind makes its operation abstain.)"""
    return ((isinstance(v, ast.Name) and v.id in env)
            or (isinstance(v, ast.Attribute) and isinstance(v.value, ast.Name) and v.value.id in env))


_HEAP_CONST_CODES: Dict[tuple, int] = {}
_HEAP_CONST_STRS: Dict[int, str] = {}                        # code -> the string literal it identifies (inverse)


def _heap_const_code(v) -> int:
    """An opaque distinct integer identity for a string / float / bytes literal in the integer heap:
    equal literals share a code, distinct literals get distinct codes, so a hashable key or value keeps
    its equality and distinctness (what dict/set membership and length need) without interpreting its
    content. The codes occupy a high range so they do not collide with small object addresses."""
    key = (type(v).__name__, v)
    if key not in _HEAP_CONST_CODES:
        code = (1 << 40) + len(_HEAP_CONST_CODES)
        _HEAP_CONST_CODES[key] = code
        if isinstance(v, str):
            _HEAP_CONST_STRS[code] = v                       # so a resolvable getattr/setattr name recovers it
    return _HEAP_CONST_CODES[key]


def _heap_const_str(term):
    """The string literal a heap term provably denotes (a constant string-identity code), else None: this
    is what lets a dynamic-but-resolvable attribute name -- a local or parameter bound to a string literal --
    be read back as the attribute it names, so getattr(o, name) with name == 'x' decides like getattr(o, 'x')."""
    if z3.is_expr(term) and z3.is_int_value(term):
        return _HEAP_CONST_STRS.get(term.as_long())
    return None


def _is_dynamic_class_call(node):
    """True if `node` is the three-argument type(name, bases, namespace) -- the form that dynamically
    creates a class -- with a string-literal class name, so it can be modeled as that class definition."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "type"
            and len(node.args) == 3 and not node.keywords
            and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str))


def _synthesize_class(local_name, call, classes):
    """Build the ClassDef that type(name, bases, ns) creates, registered under `local_name` so a later
    local_name(...) instantiates it. Bases must be modeled classes (or object/type, the implicit parent); ns
    is a dict literal whose string keys map to constants (class variables) or lambdas (expression-body
    methods). Anything else is declined (Unsupported), so a dynamically-created class is modeled only where
    its definition is statically resolvable -- a faithful image of type()'s class creation, never a guess."""
    bases_node, ns_node = call.args[1], call.args[2]
    if not isinstance(bases_node, (ast.Tuple, ast.List)):
        raise Unsupported("dynamic class with a non-literal base list")
    bases = []
    for b in bases_node.elts:
        if isinstance(b, ast.Name) and b.id in classes:
            bases.append(ast.Name(id=b.id, ctx=ast.Load()))
        elif isinstance(b, ast.Name) and b.id in ("object", "type"):
            continue                                          # the implicit base: no modeled parent
        else:
            raise Unsupported("dynamic class with an unmodeled base")
    if not isinstance(ns_node, ast.Dict):
        raise Unsupported("dynamic class with a non-literal namespace")
    body = []
    for kk, vv in zip(ns_node.keys, ns_node.values):
        if not (isinstance(kk, ast.Constant) and isinstance(kk.value, str)):
            raise Unsupported("dynamic class namespace key is not a string literal")
        if isinstance(vv, ast.Lambda):                        # a lambda becomes an expression-body method
            body.append(ast.FunctionDef(name=kk.value, args=vv.args,
                                        body=[ast.Return(value=vv.body)], decorator_list=[]))
        elif isinstance(vv, ast.Constant):                    # a constant becomes a class variable
            body.append(ast.Assign(targets=[ast.Name(id=kk.value, ctx=ast.Store())], value=vv))
        else:
            raise Unsupported("dynamic class namespace value is not a constant or lambda")
    cls = ast.ClassDef(name=local_name, bases=bases, keywords=[], body=body or [ast.Pass()], decorator_list=[])
    return ast.fix_missing_locations(ast.copy_location(cls, call))


def _init_subclass_seeds(classes, cname):
    """The constant class attributes a base's __init_subclass__ hook sets on `cname` at its definition. Python
    calls __init_subclass__ once per subclass with cls bound to the new class, so a hook in a base can give
    every subclass a default or flag. Returns None when no hook runs for cname (it does not run for the class
    that defines it), or a list of (attr, constant_node) for the resolvable case: a single hook among cname's
    STRICT ancestors whose body is `cls.attr = <constant>` assignments (a leading super().__init_subclass__()
    chaining to the no-op default is allowed and ignored). Raises Unsupported when a hook runs but cannot be
    resolved -- more than one in the ancestry (whose super-chaining order is not modeled), a non-simple body,
    or a non-constant value -- so the instantiation abstains (UNKNOWN) rather than leaving a hook-set
    attribute unconstrained, which could refute a true property."""
    hooks = []
    for c in _class_mro(classes, cname)[1:]:                 # strict ancestors only: the hook does not run for
        cnode = classes.get(c)                               # the class that defines it
        if cnode is None:
            continue
        h = next((s for s in cnode.body if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef))
                  and s.name == "__init_subclass__"), None)
        if h is not None:
            hooks.append(h)
    if not hooks:
        return None                                          # no hook runs for cname
    if len(hooks) != 1 or not hooks[0].args.args:
        raise Unsupported("__init_subclass__ chaining across multiple bases is not modeled")
    clsname = hooks[0].args.args[0].arg
    seeds = []
    for st in hooks[0].body:
        if isinstance(st, ast.Pass):
            continue
        if (isinstance(st, ast.Expr) and isinstance(st.value, ast.Call)         # super().__init_subclass__(...)
                and isinstance(st.value.func, ast.Attribute) and st.value.func.attr == "__init_subclass__"):
            continue                                         # chains to the no-op default: ignored
        if (isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Attribute)
                and isinstance(st.targets[0].value, ast.Name) and st.targets[0].value.id == clsname
                and isinstance(st.value, ast.Constant)):
            seeds.append((st.targets[0].attr, st.value))
        else:
            raise Unsupported("__init_subclass__ body beyond simple constant cls.attr assignments is not modeled")
    return seeds


def _metaclass_seeds(classes, cname):
    """The constant class attributes a custom metaclass's __init__ sets on `cname` at its creation, or None
    when no metaclass is declared. A `class C(metaclass=M)` (inherited along the MRO) runs M.__init__(cls,
    name, bases, ns) with cls bound to the new class, so a metaclass can give every class it creates an
    attribute. Modeled for the resolvable case: a visible M whose __init__ body is `cls.attr = <constant>`
    assignments. Raises Unsupported when a metaclass is declared but cannot be resolved -- M not a visible
    class, a metaclass __new__ (custom class creation), or an __init__ body beyond constant cls.attr
    assignments -- so the instantiation abstains (UNKNOWN) rather than leaving a metaclass-set attribute
    unconstrained, which could refute a true property."""
    mkw = None
    for c in _class_mro(classes, cname):
        cnode = classes.get(c)
        mkw = cnode and next((k for k in cnode.keywords if k.arg == "metaclass"), None)
        if mkw is not None:
            break
    if mkw is None:
        return None                                          # no metaclass declared: nothing to seed
    mname = mkw.value.id if isinstance(mkw.value, ast.Name) else None
    mcls = classes.get(mname) if mname else None
    if mcls is None:
        raise Unsupported("custom metaclass is not a visible class; not modeled")
    if any(isinstance(s, ast.FunctionDef) and s.name == "__new__" for s in mcls.body):
        raise Unsupported("metaclass __new__ (custom class creation) is not modeled")
    init = next((s for s in mcls.body if isinstance(s, ast.FunctionDef) and s.name == "__init__"), None)
    if init is None or not init.args.args:
        return None                                          # a metaclass with no __init__ sets no class attrs here
    clsname = init.args.args[0].arg
    seeds = []
    for st in init.body:
        if isinstance(st, ast.Pass):
            continue
        if (isinstance(st, ast.Expr) and isinstance(st.value, ast.Call)         # super().__init__(...)
                and isinstance(st.value.func, ast.Attribute) and st.value.func.attr == "__init__"):
            continue                                         # chains to the type machinery: ignored
        if (isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Attribute)
                and isinstance(st.targets[0].value, ast.Name) and st.targets[0].value.id == clsname
                and isinstance(st.value, ast.Constant)):
            seeds.append((st.targets[0].attr, st.value))
        else:
            raise Unsupported("metaclass __init__ beyond simple constant cls.attr assignments is not modeled")
    return seeds


def _init_class_vars(addr, cname, heap, ctr, traps, pc, kinds):
    """Seed a fresh instance's attribute arrays from the class-level variables (k = value) declared along
    cname's MRO, base-first so a derived class overrides a base, then from a base's __init_subclass__ hook
    and a custom metaclass's __init__ (which run after the class body, so their constant attributes win). The heap model otherwise leaves an
    unset attribute unconstrained, so without this a read of a class variable (o.k where the class declares
    k) would be arbitrary rather than its value; __init__ runs after, so an instance attribute still
    overrides a class variable. A class-body value the heap engine cannot evaluate (a method, an unmodeled
    expression) is left unseeded; an unresolvable __init_subclass__ hook abstains (Unsupported -> UNKNOWN)."""
    classes = heap.get("@classes", {})
    def seed(name, val, strict=False):
        try:
            v = _as_int(_heap_eval(val, {}, heap, ctr, traps, pc, kinds))
        except Unsupported:
            if strict:
                raise                                        # a hook attribute must be seeded soundly or abstain
            return                                           # a non-scalar class-body value is left unseeded
        arr = heap.setdefault(name, z3.Array("_h_" + name, z3.IntSort(), z3.IntSort()))
        heap[name] = z3.Store(arr, addr, v)
        _heap_mark_present(heap, name, addr)                 # a seeded class variable is a present attribute
    for c in reversed(_class_mro(classes, cname)):           # base-first: a derived class's var wins
        cnode = classes.get(c)
        if cnode is None:
            continue
        for st in cnode.body:
            if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name):
                seed(st.targets[0].id, st.value)
            elif isinstance(st, ast.AnnAssign) and isinstance(st.target, ast.Name) and st.value is not None:
                seed(st.target.id, st.value)
    for name, val in (_init_subclass_seeds(classes, cname) or []):   # a base's __init_subclass__ wins over the body
        seed(name, val, strict=True)
    for name, val in (_metaclass_seeds(classes, cname) or []):       # a custom metaclass's __init__ runs last
        seed(name, val, strict=True)


def _heap_dict_key(node, env, heap, ctr, traps, pc, kinds):
    """Evaluate a dict key for the heap engine, declining a float. The engine encodes an int key by its
    value but a float (like a str) by an opaque distinct code, so a numerically-equal int and float would
    never match -- yet Python conflates 1, 1.0, and True as a single key. Emitting a KeyError there is a
    false counterexample (a spurious REFUTED), so abstain on a float key instead, exactly as the value
    engine's _map_get does for mixed numeric key types. A non-float key returns its canonical integer term."""
    if isinstance(node, ast.Constant) and isinstance(node.value, float):
        raise Unsupported("float dict key conflates with int and bool keys (1 == 1.0 == True); "
                          "not modeled in the heap engine")
    k = _heap_eval(node, env, heap, ctr, traps, pc, kinds)
    if z3.is_expr(k) and _is_fp(k):
        raise Unsupported("float dict key conflates with int and bool keys; not modeled in the heap engine")
    return _as_int(k)


def _heap_eval(node, env, heap, ctr, traps, pc, kinds):
    """Evaluate an expression in a heap state, threading index/key traps. References are
    addresses; lists, dicts, and sets are heap objects with array/length, key-value/present,
    and membership payloads. Subscripts and membership dispatch on the receiver name's kind;
    mutating methods update the passed heap dict in place (the current path's copy)."""
    if isinstance(node, ast.Constant) and isinstance(node.value, bool):
        return z3.BoolVal(node.value)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return z3.IntVal(node.value)
    if isinstance(node, ast.Constant) and isinstance(node.value, (str, float, bytes)):
        return z3.IntVal(_heap_const_code(node.value))       # opaque distinct identity; preserves ==/distinctness
    if isinstance(node, ast.Name):
        if node.id not in env:
            raise Unsupported(f"free variable {node.id}")
        return env[node.id]
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in (
            "getattr", "setattr", "hasattr"):                # reflection with a resolvable attribute name
        fn = node.func.id
        if len(node.args) < 2:
            raise Unsupported(f"{fn} with no attribute name")
        addr = _heap_eval(node.args[0], env, heap, ctr, traps, pc, kinds)
        namenode = node.args[1]
        if isinstance(namenode, ast.Constant) and isinstance(namenode.value, str):
            attr = namenode.value                            # a literal attribute name
        else:                                                # a resolvable one: a name bound to a string literal,
            attr = _heap_const_str(_heap_eval(namenode, env, heap, ctr, traps, pc, kinds))   # recovered to its text
        if attr is None:
            raise Unsupported(f"{fn} with a dynamic (non-constant) attribute name")
        arr = heap.setdefault(attr, z3.Array("_h_" + attr, z3.IntSort(), z3.IntSort()))
        present = z3.Select(_heap_present(heap, attr), addr)
        if fn == "hasattr":                                  # decided from attribute-presence tracking
            return present
        if fn == "getattr":
            if len(node.args) >= 3:                          # getattr(o, name, default): the value if present, else default
                default = _as_int(_heap_eval(node.args[2], env, heap, ctr, traps, pc, kinds))
                return z3.If(present, z3.Select(arr, addr), default)
            return z3.Select(arr, addr)
        heap[attr] = z3.Store(arr, addr, _as_int(_heap_eval(node.args[2], env, heap, ctr, traps, pc, kinds)))
        _heap_mark_present(heap, attr, addr)                 # setattr marks the attribute present
        return z3.IntVal(0)                                  # setattr returns None
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ("eval", "exec", "compile"):
        raise Unsupported(f"{node.func.id} runs dynamically constructed code and is not modeled")
    if isinstance(node, ast.List):                           # list literal -> fresh heap object
        ctr[0] += 1
        addr = z3.IntVal(ctr[0])
        backing = z3.K(z3.IntSort(), z3.IntVal(0))
        for j, el in enumerate(node.elts):
            backing = z3.Store(backing, z3.IntVal(j), _as_int(_heap_eval(el, env, heap, ctr, traps, pc, kinds)))
        heap["@arr"] = z3.Store(_heap_arr(heap), addr, backing)
        heap["@len"] = z3.Store(_heap_len(heap), addr, z3.IntVal(len(node.elts)))
        return addr
    if isinstance(node, ast.Dict):                           # dict literal -> fresh heap object
        ctr[0] += 1
        addr = z3.IntVal(ctr[0])
        dv = z3.K(z3.IntSort(), z3.IntVal(0)); dk = z3.K(z3.IntSort(), z3.BoolVal(False)); n = z3.IntVal(0)
        for kn, vn in zip(node.keys, node.values):
            k = _heap_dict_key(kn, env, heap, ctr, traps, pc, kinds)
            try:
                v = _as_int(_heap_eval(vn, env, heap, ctr, traps, pc, kinds))
            except Unsupported:
                v = z3.IntVal(_heap_const_code(("dval", ast.dump(vn))))   # an unencodable value (a function): opaque
            n = n + z3.If(z3.Select(dk, k), z3.IntVal(0), z3.IntVal(1))   # count distinct keys
            dv = z3.Store(dv, k, v); dk = z3.Store(dk, k, z3.BoolVal(True))
        heap["@dval"] = z3.Store(_heap_dval(heap), addr, dv)
        heap["@dkey"] = z3.Store(_heap_dkey(heap), addr, dk)
        heap["@dn"] = z3.Store(_heap_dn(heap), addr, n)
        return addr
    if isinstance(node, ast.Set):                            # set literal -> fresh heap object
        ctr[0] += 1
        addr = z3.IntVal(ctr[0])
        si = z3.K(z3.IntSort(), z3.BoolVal(False)); n = z3.IntVal(0)
        for el in node.elts:
            e = _as_int(_heap_eval(el, env, heap, ctr, traps, pc, kinds))
            n = n + z3.If(z3.Select(si, e), z3.IntVal(0), z3.IntVal(1))
            si = z3.Store(si, e, z3.BoolVal(True))
        heap["@sin"] = z3.Store(_heap_sin(heap), addr, si)
        heap["@sn"] = z3.Store(_heap_sn(heap), addr, n)
        return addr
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "frozenset":
        if node.args:                                        # frozenset(s) shares the source set's payload
            return _heap_eval(node.args[0], env, heap, ctr, traps, pc, kinds)
        ctr[0] += 1
        addr = z3.IntVal(ctr[0])
        heap["@sn"] = z3.Store(_heap_sn(heap), addr, z3.IntVal(0))
        return addr
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in heap.get("@classes", {}):
        cname = node.func.id                                 # instantiation: allocate, seed class vars, run __init__
        ctr[0] += 1
        addr = z3.IntVal(ctr[0])
        _init_class_vars(addr, cname, heap, ctr, traps, pc, kinds)
        init = _find_method(heap["@classes"], cname, "__init__")
        if init is not None:
            params = [a.arg for a in init.args.args]
            argvals = [_heap_eval(a, env, heap, ctr, traps, pc, kinds) for a in node.args]
            ienv = {params[0]: addr}
            ienv.update(dict(zip(params[1:], argvals)))
            _run_method(init.body, ienv, heap, ctr, traps, pc, kinds)
        return addr
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ("object", "new", "list", "dict", "set"):
        ctr[0] += 1
        addr = z3.IntVal(ctr[0])
        if node.func.id == "list":
            heap["@len"] = z3.Store(_heap_len(heap), addr, z3.IntVal(0))
        elif node.func.id == "dict":
            heap["@dn"] = z3.Store(_heap_dn(heap), addr, z3.IntVal(0))
        elif node.func.id == "set":
            heap["@sn"] = z3.Store(_heap_sn(heap), addr, z3.IntVal(0))
        return addr                                          # fresh, distinct identity (empty if a collection)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "len" and len(node.args) == 1:
        arg = node.args[0]
        cls = _instance_class(arg, heap, kinds)
        if cls is not None:                                  # len(obj) -> obj.__len__()
            mdef = _find_method(heap["@classes"], cls, "__len__")
            if mdef is not None:
                return _dispatch_method(mdef, _heap_eval(arg, env, heap, ctr, traps, pc, kinds), [],
                                        heap, ctr, traps, pc, kinds)
        addr = _heap_eval(arg, env, heap, ctr, traps, pc, kinds)
        k = _kind_of(arg, kinds)
        if k == "dict":
            return z3.Select(_heap_dn(heap), addr)
        if k in ("set", "frozenset"):
            return z3.Select(_heap_sn(heap), addr)
        return z3.Select(_heap_len(heap), addr)
    if isinstance(node, ast.Subscript) and (
            isinstance(node.value, ast.Name)                 # a local sequence/dict, or a container-valued
            or (_heap_recv_expr(node.value, env)             # self.<attr> with a tracked list/dict kind
                and _kind_of(node.value, kinds) in ("list", "dict"))):
        cls = _instance_class(node.value, heap, kinds)
        if cls is not None and not isinstance(node.slice, ast.Slice):   # obj[i] -> obj.__getitem__(i)
            mdef = _find_method(heap["@classes"], cls, "__getitem__")
            if mdef is not None:
                return _dispatch_method(mdef, _heap_eval(node.value, env, heap, ctr, traps, pc, kinds),
                                        [_heap_eval(node.slice, env, heap, ctr, traps, pc, kinds)],
                                        heap, ctr, traps, pc, kinds)
        addr = _heap_eval(node.value, env, heap, ctr, traps, pc, kinds)
        if _kind_of(node.value, kinds) == "dict":            # dict lookup: KeyError if absent
            key = _heap_dict_key(node.slice, env, heap, ctr, traps, pc, kinds)
            traps.append(z3.And(pc, z3.Not(z3.Select(z3.Select(_heap_dkey(heap), addr), key))))
            return z3.Select(z3.Select(_heap_dval(heap), addr), key)
        if isinstance(node.slice, ast.Slice):                # list slice a[i:j] -> a new list
            st = node.slice.step
            if st is not None and not (isinstance(st, ast.Constant) and st.value in (1, None)):
                raise Unsupported("list slice with a step")
            backing = z3.Select(_heap_arr(heap), addr)
            n = z3.Select(_heap_len(heap), addr)

            def _bnd(b, dflt):
                if b is None:
                    return dflt
                x = _as_int(_heap_eval(b, env, heap, ctr, traps, pc, kinds))
                return z3.If(x < 0, _zmax(n + x, z3.IntVal(0)), _zmin(x, n))

            lo = _bnd(node.slice.lower, z3.IntVal(0))
            hi = _bnd(node.slice.upper, n)
            kk = z3.FreshInt("sl")
            ctr[0] += 1
            na = z3.IntVal(ctr[0])
            heap["@arr"] = z3.Store(_heap_arr(heap), na, z3.Lambda([kk], z3.Select(backing, lo + kk)))
            heap["@len"] = z3.Store(_heap_len(heap), na, _zmax(hi - lo, z3.IntVal(0)))
            return na
        idx = _as_int(_heap_eval(node.slice, env, heap, ctr, traps, pc, kinds))   # list index
        n = z3.Select(_heap_len(heap), addr)
        real = z3.If(idx < 0, n + idx, idx)
        traps.append(z3.And(pc, z3.Or(real < 0, real >= n)))   # IndexError
        return z3.Select(z3.Select(_heap_arr(heap), addr), real)
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Call) and isinstance(node.func.value.func, ast.Name)
            and node.func.value.func.id in heap.get("@classes", {})):
        ctor = node.func.value.func.id                       # C(...).m(): construct the instance (exact type, so
        addr = _heap_eval(node.func.value, env, heap, ctr, traps, pc, kinds)   # sound), then dispatch on it
        mdef = _find_method(heap["@classes"], ctor, node.func.attr)
        if mdef is None:
            raise Unsupported(f"no method .{node.func.attr}() on class {ctor}")
        return _heap_dispatch(mdef, addr, ctor, node, env, heap, ctr, traps, pc, kinds)
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and _heap_recv_expr(node.func.value, env)):
        recv = node.func.value                               # a local name, or a self.<attr> container
        is_name = isinstance(recv, ast.Name)
        addr = env[recv.id] if is_name else _heap_eval(recv, env, heap, ctr, traps, pc, kinds)
        rkind = _kind_of(recv, kinds)                        # a local's tracked kind, or the attribute's
        meth = node.func.attr
        dcls = kinds.get(recv.id) if is_name else rkind      # the receiver's class: a local name, or a tracked
        if dcls in heap.get("@classes", {}):                 # instance attribute (self.child) -- dispatch along the MRO
            mdef = _find_method(heap["@classes"], dcls, meth)
            if mdef is None:
                raise Unsupported(f"no method .{meth}() on class {dcls}")
            return _heap_dispatch(mdef, addr, dcls, node, env, heap, ctr, traps, pc, kinds)
        # a self.<attr> receiver dispatches a collection method only with a tracked container kind (a local
        # name dispatches by method name as before); an attribute of unknown kind abstains rather than guess.
        _islist = is_name or rkind == "list"
        _isset = is_name or rkind == "set"
        if meth in ("add", "remove") and rkind == "frozenset":
            raise Unsupported("frozenset is immutable")
        if meth == "append" and len(node.args) == 1 and _islist:
            arr, ln = _heap_arr(heap), _heap_len(heap)
            n = z3.Select(ln, addr)
            x = _as_int(_heap_eval(node.args[0], env, heap, ctr, traps, pc, kinds))
            heap["@arr"] = z3.Store(arr, addr, z3.Store(z3.Select(arr, addr), n, x))
            heap["@len"] = z3.Store(ln, addr, n + 1)
            return z3.IntVal(0)                              # append returns None
        if meth == "pop" and not node.args and _islist:
            arr, ln = _heap_arr(heap), _heap_len(heap)
            n = z3.Select(ln, addr)
            traps.append(z3.And(pc, n <= 0))                 # pop from empty list -> IndexError
            heap["@len"] = z3.Store(ln, addr, n - 1)
            return z3.Select(z3.Select(arr, addr), n - 1)
        if meth == "add" and len(node.args) == 1 and _isset:
            si, sn = _heap_sin(heap), _heap_sn(heap)
            e = _as_int(_heap_eval(node.args[0], env, heap, ctr, traps, pc, kinds))
            before = z3.Select(z3.Select(si, addr), e)
            heap["@sin"] = z3.Store(si, addr, z3.Store(z3.Select(si, addr), e, z3.BoolVal(True)))
            heap["@sn"] = z3.Store(sn, addr, z3.Select(sn, addr) + z3.If(before, z3.IntVal(0), z3.IntVal(1)))
            return z3.IntVal(0)
        if meth == "remove" and len(node.args) == 1 and _isset:
            si, sn = _heap_sin(heap), _heap_sn(heap)
            e = _as_int(_heap_eval(node.args[0], env, heap, ctr, traps, pc, kinds))
            traps.append(z3.And(pc, z3.Not(z3.Select(z3.Select(si, addr), e))))   # KeyError
            heap["@sin"] = z3.Store(si, addr, z3.Store(z3.Select(si, addr), e, z3.BoolVal(False)))
            heap["@sn"] = z3.Store(sn, addr, z3.Select(sn, addr) - z3.IntVal(1))
            return z3.IntVal(0)
        raise Unsupported(f"collection method .{meth}()")
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
        if node.value.id not in env:
            raise Unsupported(f"free reference {node.value.id}")
        arr = heap.setdefault(node.attr, z3.Array("_h_" + node.attr, z3.IntSort(), z3.IntSort()))
        return z3.Select(arr, env[node.value.id])
    if isinstance(node, ast.BinOp):
        op = type(node.op)
        cls = _instance_class(node.left, heap, kinds)        # operator overloading: a + b -> a.__add__(b)
        if cls and op in _BINOP_DUNDER:
            mdef = _find_method(heap["@classes"], cls, _BINOP_DUNDER[op])
            if mdef is not None:
                return _dispatch_method(mdef, _heap_eval(node.left, env, heap, ctr, traps, pc, kinds),
                                        [_heap_eval(node.right, env, heap, ctr, traps, pc, kinds)],
                                        heap, ctr, traps, pc, kinds)
        lk, rk = _kind_of(node.left, kinds), _kind_of(node.right, kinds)
        if op is ast.Add and lk == "list" and rk == "list":  # list concatenation -> a new list
            a, b = _heap_eval(node.left, env, heap, ctr, traps, pc, kinds), _heap_eval(node.right, env, heap, ctr, traps, pc, kinds)
            arr, ln = _heap_arr(heap), _heap_len(heap)
            ba, na = z3.Select(arr, a), z3.Select(ln, a)
            bb, nb = z3.Select(arr, b), z3.Select(ln, b)
            kk = z3.FreshInt("cat")
            ctr[0] += 1
            addr = z3.IntVal(ctr[0])
            heap["@arr"] = z3.Store(_heap_arr(heap), addr,
                                    z3.Lambda([kk], z3.If(kk < na, z3.Select(ba, kk), z3.Select(bb, kk - na))))
            heap["@len"] = z3.Store(_heap_len(heap), addr, na + nb)
            return addr
        if op is ast.Mult and (lk == "list" or rk == "list"):   # list repetition -> a new list
            lnode, knode = (node.left, node.right) if lk == "list" else (node.right, node.left)
            a = _heap_eval(lnode, env, heap, ctr, traps, pc, kinds)
            mult = _as_int(_heap_eval(knode, env, heap, ctr, traps, pc, kinds))
            arr, ln = _heap_arr(heap), _heap_len(heap)
            ba, na = z3.Select(arr, a), z3.Select(ln, a)
            kk = z3.FreshInt("rep")
            ctr[0] += 1
            addr = z3.IntVal(ctr[0])
            heap["@arr"] = z3.Store(_heap_arr(heap), addr,
                                    z3.Lambda([kk], z3.Select(ba, z3.If(na > 0, kk % na, z3.IntVal(0)))))
            heap["@len"] = z3.Store(_heap_len(heap), addr, _zmax(na * mult, z3.IntVal(0)))
            return addr
        if op in (ast.FloorDiv, ast.Mod):
            li = _as_int(_heap_eval(node.left, env, heap, ctr, traps, pc, kinds))
            ri = _as_int(_heap_eval(node.right, env, heap, ctr, traps, pc, kinds))
            traps.append(z3.And(pc, ri == 0))               # ZeroDivisionError
            return py_floordiv(li, ri) if op is ast.FloorDiv else py_mod(li, ri)
        if op not in _BINOPS:
            raise Unsupported(f"heap binop {op.__name__}")
        return _BINOPS[op](_as_int(_heap_eval(node.left, env, heap, ctr, traps, pc, kinds)),
                           _as_int(_heap_eval(node.right, env, heap, ctr, traps, pc, kinds)))
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -_as_int(_heap_eval(node.operand, env, heap, ctr, traps, pc, kinds))
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        op = node.ops[0]
        if isinstance(op, (ast.In, ast.NotIn)) and isinstance(node.comparators[0], ast.Name):
            coll = node.comparators[0]
            addr = _heap_eval(coll, env, heap, ctr, traps, pc, kinds)
            k = _kind_of(coll, kinds)
            if k in ("set", "frozenset"):
                el = _as_int(_heap_eval(node.left, env, heap, ctr, traps, pc, kinds))
                present = z3.Select(z3.Select(_heap_sin(heap), addr), el)
            elif k == "dict":
                el = _heap_dict_key(node.left, env, heap, ctr, traps, pc, kinds)   # float key conflation: abstain
                present = z3.Select(z3.Select(_heap_dkey(heap), addr), el)
            else:
                raise Unsupported("membership over this collection")
            return present if isinstance(op, ast.In) else z3.Not(present)
        cls = _instance_class(node.left, heap, kinds)        # rich comparison: a < b -> a.__lt__(b)
        if cls and type(op) in _CMP_DUNDER:
            mdef = _find_method(heap["@classes"], cls, _CMP_DUNDER[type(op)])
            if mdef is not None:
                return _dispatch_method(mdef, _heap_eval(node.left, env, heap, ctr, traps, pc, kinds),
                                        [_heap_eval(node.comparators[0], env, heap, ctr, traps, pc, kinds)],
                                        heap, ctr, traps, pc, kinds)
        lv = _heap_eval(node.left, env, heap, ctr, traps, pc, kinds)
        rv = _heap_eval(node.comparators[0], env, heap, ctr, traps, pc, kinds)
        if isinstance(op, ast.Is):                           # object identity: same address
            return lv == rv
        if isinstance(op, ast.IsNot):
            return lv != rv
        if type(op) not in _CMP:                             # membership (in / not in) etc.: not modeled here, so
            raise Unsupported(f"heap comparison {type(op).__name__}")   # abstain cleanly rather than crash with KeyError
        return _CMP[type(op)](lv, rv)
    if isinstance(node, ast.Call):                           # callee not a modeled form (a subscript result):
        _heap_eval(node.func, env, heap, ctr, traps, pc, kinds)   # trap-check the callee (e.g. d[key] -> KeyError)
        for a in node.args:                                  # and the arguments; the call result is opaque
            _heap_eval(a, env, heap, ctr, traps, pc, kinds)
        return z3.FreshInt("opaque_call")
    if isinstance(node, ast.IfExp):                          # a ternary b if test else o: the test's truthiness is
        if any(isinstance(n, (ast.Call, ast.NamedExpr))      # collection-aware, and each branch is trap-checked under
               for br in (node.body, node.orelse) for n in ast.walk(br)):   # its path condition. A side-effecting
            raise Unsupported("ternary with a side-effecting branch")   # branch would mutate the heap on both paths
        t = _heap_truth(node.test, env, heap, ctr, traps, pc, kinds)
        b = _heap_eval(node.body, env, heap, ctr, traps, z3.And(pc, t), kinds)
        o = _heap_eval(node.orelse, env, heap, ctr, traps, z3.And(pc, z3.Not(t)), kinds)
        return z3.If(t, b, o) if z3.is_expr(b) and z3.is_expr(o) and b.sort() == o.sort() else z3.FreshInt("ifexp")
    raise Unsupported(f"heap expression {type(node).__name__}")


def _heap_dispatch(mdef, addr, dcls, node, env, heap, ctr, traps, pc, kinds):
    """Bind a dispatched method's parameters and run its body: self -> the receiver addr (carrying its class
    dcls so its own self.attr / self.method() resolve), the positional args, then any unfilled trailing
    parameter from its default."""
    params = [a.arg for a in mdef.args.args]
    argvals = [_heap_eval(a, env, heap, ctr, traps, pc, kinds) for a in node.args]
    menv = {params[0]: addr}; menv.update(dict(zip(params[1:], argvals)))
    mkinds = dict(kinds); mkinds[params[0]] = dcls
    defs = mdef.args.defaults
    for i, pn in enumerate(params):
        if pn not in menv:
            di = i - (len(params) - len(defs))
            if 0 <= di < len(defs):
                menv[pn] = _heap_eval(defs[di], menv, heap, ctr, traps, pc, mkinds)
    return _run_method(mdef.body, menv, heap, ctr, traps, pc, mkinds)


def _heap_truth(test, e, h, ctr, traps, p, kd):
    """Truthiness of a heap `if` / `while` test: a collection is truthy iff non-empty (its tracked length or
    count), NOT by its nonzero heap address -- so `if self.items: self.items[0]` ties the guard to the bounds
    and proves. Other values keep Python truthiness; `not` recurses."""
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return z3.Not(_heap_truth(test.operand, e, h, ctr, traps, p, kd))
    k = _kind_of(test, kd)
    if k in ("list", "set", "frozenset", "dict"):
        v = _heap_eval(test, e, h, ctr, traps, p, kd)
        cnt = _heap_len if k == "list" else _heap_sn if k in ("set", "frozenset") else _heap_dn
        return z3.Select(cnt(h), v) != 0
    return _as_bool(_heap_eval(test, e, h, ctr, traps, p, kd))


def _heap_walk(stmts, env, heap, pc, ctr, traps, rets, kinds):
    """Path-split a loop-free reference function, threading the heap (object attributes plus
    list / dict / set payloads), the per-name collection kinds, and index/key traps along each
    path. Returns the open (non-returning) paths."""
    falls = [(dict(env), dict(heap), dict(kinds), pc)]
    for s in stmts:
        nxt = []
        for e, h, kd, p in falls:
            if isinstance(s, ast.Return):
                if s.value is None:
                    raise Unsupported("heap function returns None")
                rets.append((p, _heap_eval(s.value, e, h, ctr, traps, p, kd), dict(h)))   # snapshot heap
            elif isinstance(s, ast.Expr):                    # bare call (e.g. lst.append(x)): for effect
                h2 = dict(h)
                _heap_eval(s.value, e, h2, ctr, traps, p, kd)
                nxt.append((dict(e), h2, dict(kd), p))
            elif isinstance(s, ast.Assign):
                if len(s.targets) != 1:
                    raise Unsupported("multiple assignment targets")
                tgt = s.targets[0]
                if isinstance(tgt, ast.Name) and _is_dynamic_class_call(s.value):
                    cls = _synthesize_class(tgt.id, s.value, h.get("@classes", {}))   # C = type('C', bases, ns)
                    h2 = dict(h); h2["@classes"] = dict(h2.get("@classes", {})); h2["@classes"][tgt.id] = cls
                    ctr[0] += 1
                    e2 = dict(e); e2[tgt.id] = z3.IntVal(ctr[0])     # the class object's identity
                    nxt.append((e2, h2, dict(kd), p)); continue
                if isinstance(tgt, ast.Name):
                    e2 = dict(e); h2 = dict(h); kd2 = dict(kd)
                    e2[tgt.id] = _heap_eval(s.value, e2, h2, ctr, traps, p, kd)
                    k = _kind_of(s.value, kd)
                    if k is None and isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Name) \
                            and s.value.func.id in h.get("@classes", {}):
                        k = s.value.func.id                  # an instance: tag it with its class
                    if k is not None:
                        kd2[tgt.id] = k
                    else:
                        kd2.pop(tgt.id, None)
                    nxt.append((e2, h2, kd2, p))
                elif isinstance(tgt, ast.Attribute) and isinstance(tgt.value, ast.Name):
                    if tgt.value.id not in e:
                        raise Unsupported(f"store to free reference {tgt.value.id}")
                    h2 = dict(h)
                    arr = h2.setdefault(tgt.attr, z3.Array("_h_" + tgt.attr, z3.IntSort(), z3.IntSort()))
                    h2[tgt.attr] = z3.Store(arr, e[tgt.value.id], _heap_eval(s.value, e, h2, ctr, traps, p, kd))
                    _heap_mark_present(h2, tgt.attr, e[tgt.value.id])
                    nxt.append((dict(e), h2, dict(kd), p))
                elif isinstance(tgt, ast.Subscript) and _heap_recv_expr(tgt.value, e):
                    is_nm = isinstance(tgt.value, ast.Name)   # d[k] = v on a local, or self.d[k] = v on an attribute
                    if is_nm and tgt.value.id not in e:
                        raise Unsupported(f"store to free reference {tgt.value.id}")
                    h2 = dict(h)
                    addr = e[tgt.value.id] if is_nm else _heap_eval(tgt.value, e, h2, ctr, traps, p, kd)
                    tkind = kd.get(tgt.value.id) if is_nm else _kind_of(tgt.value, kd)
                    if tkind == "dict":                      # dict store: d[k] = v / self.d[k] = v
                        dv, dk, dn = _heap_dval(h2), _heap_dkey(h2), _heap_dn(h2)
                        key = _heap_dict_key(tgt.slice, e, h2, ctr, traps, p, kd)
                        try:
                            val = _as_int(_heap_eval(s.value, e, h2, ctr, traps, p, kd))
                        except Unsupported:
                            val = z3.IntVal(_heap_const_code(("sval", ast.dump(s.value))))   # function/unencodable value: opaque
                        before = z3.Select(z3.Select(dk, addr), key)
                        h2["@dval"] = z3.Store(dv, addr, z3.Store(z3.Select(dv, addr), key, val))
                        h2["@dkey"] = z3.Store(dk, addr, z3.Store(z3.Select(dk, addr), key, z3.BoolVal(True)))
                        h2["@dn"] = z3.Store(dn, addr, z3.Select(dn, addr) + z3.If(before, z3.IntVal(0), z3.IntVal(1)))
                    elif tkind == "list" or is_nm:           # list store: a[i] = v / self.items[i] = v (an untyped local
                        arr, ln = _heap_arr(h2), _heap_len(h2)   # keeps the prior list default; an untracked attribute
                        idx = _as_int(_heap_eval(tgt.slice, e, h2, ctr, traps, p, kd))   # abstains rather than guess)
                        n = z3.Select(ln, addr)
                        real = z3.If(idx < 0, n + idx, idx)
                        traps.append(z3.And(p, z3.Or(real < 0, real >= n)))   # IndexError on store
                        try:
                            val = _as_int(_heap_eval(s.value, e, h2, ctr, traps, p, kd))
                        except Unsupported:
                            val = z3.IntVal(_heap_const_code(("sval", ast.dump(s.value))))   # function/unencodable value: opaque
                        h2["@arr"] = z3.Store(arr, addr, z3.Store(z3.Select(arr, addr), real, val))
                    else:
                        raise Unsupported("subscript store to an untracked attribute")
                    nxt.append((dict(e), h2, dict(kd), p))
                else:
                    raise Unsupported("heap assignment target")
            elif isinstance(s, ast.If):
                c = _heap_truth(s.test, e, h, ctr, traps, p, kd)
                nxt += _heap_walk(s.body, e, h, z3.And(p, c), ctr, traps, rets, kd)
                nxt += _heap_walk(s.orelse, e, h, z3.And(p, z3.Not(c)), ctr, traps, rets, kd)
            elif isinstance(s, ast.Try):                     # with-desugar: try/finally, no exceptions here
                if s.handlers:
                    raise Unsupported("except in heap-object code")
                for be, bh, bkd, bp in _heap_walk(s.body, e, h, p, ctr, traps, rets, kd):
                    nxt += _heap_walk(s.finalbody, be, bh, bp, ctr, traps, rets, bkd)
            elif isinstance(s, (ast.Pass, ast.Import, ast.ImportFrom)):
                nxt.append((dict(e), dict(h), dict(kd), p))   # import: a no-op
            else:
                raise Unsupported(f"heap statement {type(s).__name__}")
        falls = nxt
    return falls


# --------------------------------------------------------------------------- #
# User-defined classes over the heap. A class registry (heap["@classes"]) holds the   #
# parsed definitions; each instance's class is tracked in `kinds`. Instantiation runs   #
# __init__ (binding self.attributes), and a method call dispatches along the single-     #
# inheritance MRO, running the method body with self bound. Method bodies may branch:    #
# _run_method merges the per-attribute heap arrays across branches and folds the return. #
# --------------------------------------------------------------------------- #
def _c3_merge(seqs):
    """C3 merge: take a head in no other sequence's tail, drop it from all, repeat; inconsistent -> first head."""
    result = []
    seqs = [list(s) for s in seqs if s]
    while seqs:
        cand = None
        for s in seqs:
            if not any(s[0] in t[1:] for t in seqs):
                cand = s[0]
                break
        if cand is None:
            cand = seqs[0][0]
        result.append(cand)
        seqs = [s for s in ((x[1:] if x[0] == cand else x) for x in seqs) if s]
    return result


def _class_mro(classes, cname, _seen=None):
    """C3 linearization over the classes in `classes` (external bases and cycles dropped)."""
    if _seen is None:
        _seen = set()
    if cname not in classes or cname in _seen:
        return []
    bases = [b.id for b in classes[cname].bases if isinstance(b, ast.Name) and b.id in classes]
    if not bases:
        return [cname]
    seqs = [_class_mro(classes, b, _seen | {cname}) for b in bases] + [list(bases)]
    return [cname] + _c3_merge(seqs)


def _find_method(classes, cname, mname):
    for c in _class_mro(classes, cname):
        for s in classes[c].body:
            if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef)) and s.name == mname:
                return s
    return None


def _run_method(body, env, heap, ctr, traps, pc, kinds):
    """Execute a method/__init__ body, threading and merging the heap across branches, and
    return the folded return value (None paths return 0). Loop-free method bodies only."""
    rets = []

    def go(stmts, e, pc):
        e = dict(e)
        for s in stmts:
            if isinstance(s, ast.Return):
                rets.append((pc, _heap_eval(s.value, e, heap, ctr, traps, pc, kinds)
                             if s.value is not None else z3.IntVal(0)))
                return None
            elif isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name):
                e[s.targets[0].id] = _heap_eval(s.value, e, heap, ctr, traps, pc, kinds)
            elif isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Attribute) \
                    and isinstance(s.targets[0].value, ast.Name):
                tgt = s.targets[0]
                arr = heap.setdefault(tgt.attr, z3.Array("_h_" + tgt.attr, z3.IntSort(), z3.IntSort()))
                heap[tgt.attr] = z3.Store(arr, e[tgt.value.id],
                                          _as_int(_heap_eval(s.value, e, heap, ctr, traps, pc, kinds)))
                _heap_mark_present(heap, tgt.attr, e[tgt.value.id])
            elif isinstance(s, ast.Expr):
                _heap_eval(s.value, e, heap, ctr, traps, pc, kinds)
            elif isinstance(s, ast.Pass):
                pass
            elif isinstance(s, ast.If):
                c = _heap_truth(s.test, e, heap, ctr, traps, pc, kinds)
                before = {k: heap[k] for k in heap if z3.is_ast(heap[k])}
                et = go(s.body, e, z3.And(pc, c))
                then_h = {k: heap[k] for k in before}
                for k in before:                              # restore for the else branch
                    heap[k] = before[k]
                ee = go(s.orelse, e, z3.And(pc, z3.Not(c)))
                for k in set(then_h):                         # merge the two branch heaps
                    heap[k] = z3.If(c, then_h[k], heap.get(k, then_h[k]))
                for k in heap:
                    if z3.is_ast(heap[k]) and k not in before and k in then_h:
                        heap[k] = z3.If(c, then_h[k], heap[k])
                if et is None and ee is None:
                    return None
                if et is not None and ee is not None:
                    merged = dict(et)
                    for k in set(et) | set(ee):
                        a, b = et.get(k), ee.get(k)
                        if a is not None and b is not None and not (a is b):
                            merged[k] = z3.If(c, a, b)
                        elif b is not None:
                            merged[k] = b
                    return merged
                return et if et is not None else ee
            else:
                raise Unsupported(f"method statement {type(s).__name__}")
        return e

    fell = go(body, env, pc)
    if fell is not None:
        rets.append((pc, z3.IntVal(0)))                       # fell off the end -> None
    return fold(rets)


def _dispatch_method(mdef, self_addr, argvals, heap, ctr, traps, pc, kinds):
    """Run a resolved method/dunder with self bound to self_addr and the given argument values."""
    params = [a.arg for a in mdef.args.args]
    menv = {params[0]: self_addr}
    menv.update(dict(zip(params[1:], argvals)))
    return _run_method(mdef.body, menv, heap, ctr, traps, pc, kinds)


_BINOP_DUNDER = {ast.Add: "__add__", ast.Sub: "__sub__", ast.Mult: "__mul__",
                 ast.FloorDiv: "__floordiv__", ast.Mod: "__mod__", ast.Pow: "__pow__"}
_CMP_DUNDER = {ast.Eq: "__eq__", ast.NotEq: "__ne__", ast.Lt: "__lt__",
               ast.LtE: "__le__", ast.Gt: "__gt__", ast.GtE: "__ge__"}


def _instance_class(node, heap, kinds):
    """The class name if `node` denotes an instance of a user-defined class (a tracked name or
    an inline C(...) construction), else None."""
    classes = heap.get("@classes", {})
    k = _kind_of(node, kinds)
    if k in classes:
        return k
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in classes:
        return node.func.id
    return None


def _pyfn(src: str, repo: Dict[str, str]):
    """Compile a repo function (and its callees) to an executable Python callable."""
    ns: dict = {}
    for s in repo.values():
        exec(textwrap.dedent(s), ns)
    exec(textwrap.dedent(src), ns)
    return ns[_fndef(src).name]


# Builtins the modeled subset can legitimately call. Anything outside this set (open, eval, exec,
# compile, __import__, input, ...) is simply absent in the sandbox namespace, so a subject that
# reaches for it fails inside the isolated child rather than touching the host.
_SANDBOX_BUILTINS = {
    "abs": abs, "min": min, "max": max, "len": len, "range": range, "enumerate": enumerate,
    "zip": zip, "sorted": sorted, "sum": sum, "map": map, "filter": filter, "all": all, "any": any,
    "int": int, "float": float, "bool": bool, "str": str, "list": list, "dict": dict, "set": set,
    "tuple": tuple, "frozenset": frozenset, "divmod": divmod, "pow": pow, "round": round,
    "reversed": reversed, "isinstance": isinstance, "issubclass": issubclass, "type": type,
    "ord": ord, "chr": chr, "object": object, "True": True, "False": False, "None": None,
}
# Every builtin exception, so a subject that raises or catches a named exception runs as written: a
# `raise ValueError(...)` must produce ValueError, not a NameError from the name being absent. (Traps from
# an operation -- IndexError, ZeroDivisionError -- already fire from CPython's own code regardless.)
import builtins as _builtins
_SANDBOX_BUILTINS.update({_n: getattr(_builtins, _n) for _n in dir(_builtins)
                          if isinstance(getattr(_builtins, _n), type) and issubclass(getattr(_builtins, _n), BaseException)})
_SANDBOX_BUILTINS["__build_class__"] = _builtins.__build_class__   # the `class` statement needs it; a class subject
_SANDBOX_BUILTINS["property"] = property                           # (and a method confirmed on a real instance) execs


def _apply_rlimits(mem_mb):
    """In a sandbox child, cap address space (mem_mb), CPU seconds, and file size where the platform allows
    (POSIX rlimits). A no-op on Windows, which relies on process isolation and the parent's timeout."""
    try:
        import resource                                          # POSIX: hard resource limits
        soft = mem_mb * 1024 * 1024
        for lim, val in [(resource.RLIMIT_AS, soft), (resource.RLIMIT_CPU, 5),
                         (resource.RLIMIT_FSIZE, 0)]:            # 0-byte files: no writes to disk
            try:
                resource.setrlimit(lim, (val, val))
            except (ValueError, OSError):
                pass
    except Exception:
        pass                                                     # Windows: rely on process isolation + timeout


def _sandbox_compile(src, repo, fname):
    """In a sandbox child, build the restricted-builtins namespace, exec the repo modules then the subject
    into it, and return the named function -- or None if any of that raised (the caller reports its own
    setup_error to the parent, whose payload it owns)."""
    ns = {"__builtins__": dict(_SANDBOX_BUILTINS), "__name__": "__sandbox__"}   # __name__ so a class body resolves
    try:
        for s in repo.values():
            exec(textwrap.dedent(s), ns)
        exec(textwrap.dedent(src), ns)
        return ns[fname]
    except Exception:
        return None


def _sandbox_worker(q, src, repo, fname, inputs, mem_mb):
    """Run inside a separate process: cap memory / CPU / file size where the platform allows, compile
    the subject with a restricted builtins namespace, and evaluate it on each concrete input tuple.
    Reports per-input ('ok', value) / ('trap',) / ('nonint',) so the parent (which holds the
    unpicklable Z3 spec) decides the verdict. A crash or limit breach dies with the child, not the host."""
    _apply_rlimits(mem_mb)
    fn = _sandbox_compile(src, repo, fname)
    if fn is None:
        q.put(("setup_error",)); return
    out = []
    for tup in inputs:
        try:
            r = fn(*tup)
            out.append(("ok", r) if isinstance(r, int) and not isinstance(r, bool) else ("nonint",))
        except Exception:
            out.append(("trap",))                                # a raise is a trap, modeled separately
    q.put(("results", out))


class _TraceBudget(Exception):
    """Raised inside the trace worker when the recorded path exceeds its step budget."""


def _sandbox_trace_worker(q, src, repo, fname, argvals, mem_mb, max_steps):
    """Run fname(*argvals) in an isolated process under a line tracer, recording (lineno, integer
    locals) at each step, and report ('returned'|'raised', trace, detail). The trace makes a
    counterexample's path and intermediate values visible without trusting the subject in-process."""
    import sys as _sys
    _apply_rlimits(mem_mb)
    fn = _sandbox_compile(src, repo, fname)
    if fn is None:
        q.put(("setup_error", [], "")); return
    trace, steps = [], [0]

    def tracer(frame, event, arg):
        if event == "line" and frame.f_code.co_filename == "<string>":   # only the exec'd subject's lines,
            steps[0] += 1                                                # not the worker / library frames
            if steps[0] > max_steps:
                raise _TraceBudget()
            loc = {k: v for k, v in frame.f_locals.items() if isinstance(v, int) and not isinstance(v, bool)}
            trace.append((frame.f_lineno, loc))
        return tracer

    old = _sys.gettrace(); _sys.settrace(tracer)
    try:
        r = fn(*argvals)
        q.put(("returned", trace, repr(r)))
    except _TraceBudget:
        q.put(("diverged", trace, ""))
    except Exception as e:
        q.put(("raised", trace, type(e).__name__))
    finally:
        _sys.settrace(old)


def _spawn_worker(worker, args, timeout, extract, fallback):
    """Run a sandbox worker in a spawned child and return extract(its queued message), or None on a timeout,
    a spawn failure, or a worker death. When multiprocessing-spawn cannot re-import __main__ (a `python -c`
    or REPL launch), call fallback() instead -- the standalone-subprocess path -- so the oracle runs in every
    launch mode rather than abstaining. The child is always terminated and joined."""
    import multiprocessing as mp
    mainfile = getattr(sys.modules.get("__main__"), "__file__", None)
    if mainfile is None or mainfile.startswith("<"):             # REPL / stdin / -c: spawn cannot re-import
        return fallback()
    try:
        ctx = mp.get_context("spawn")                            # uniform across platforms; no fork inheritance
        q = ctx.Queue()
        p = ctx.Process(target=worker, args=(q,) + tuple(args))
        p.start()
    except Exception:
        return None
    try:
        try:
            msg = q.get(timeout=timeout)
        except Exception:
            return None                                          # timed out or worker died without a result
        return extract(msg)
    finally:
        if p.is_alive():
            p.terminate()
        p.join(timeout=1.0)


def sandbox_trace(src, repo, fname, argvals, timeout_s=4.0, mem_mb=512, max_steps=10000):
    """Trace fname(*argvals) in an isolated, resource-limited child process. Returns
    (outcome, [(lineno, {var: int}), ...], detail) or None if unavailable. outcome is 'returned'
    (detail = repr of the result), 'raised' (detail = exception name), 'diverged', or 'setup_error'."""
    return _spawn_worker(
        _sandbox_trace_worker, (src, repo, fname, list(argvals), mem_mb, max_steps), timeout_s,
        lambda msg: tuple(msg),
        lambda: _run_trace_in_subprocess(src, repo, fname, argvals, timeout_s, mem_mb, max_steps))


def _sandbox_child_path():
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), "_sandbox_child.py")


def _run_in_subprocess(mode, src, repo, fname, inputs, timeout_s, mem_mb):
    """Run the subject out of process via a standalone child script. Unlike multiprocessing-spawn this
    works in every launch mode (a file, -m, -c, the REPL), so the oracle is available wherever the
    verifier runs rather than silently abstaining under `python -c`. `mode` is 'value' (('ok', int) /
    ('nonint',) / ('trap',)) or 'typed' (('ok',) / ('raise', name)). Returns the per-input results list,
    or None if the child could not produce one (timeout, a resource-limit kill, or a serialization fault)."""
    import pickle, subprocess
    job = {"mode": mode, "src": src, "repo": repo or {}, "fname": fname,
           "inputs": [list(t) for t in inputs], "mem_mb": mem_mb}
    try:
        blob = pickle.dumps(job)
    except Exception:
        return None
    try:
        proc = subprocess.run([sys.executable, _sandbox_child_path()], input=blob,
                              capture_output=True, timeout=timeout_s)
    except Exception:
        return None
    try:
        tag, *rest = pickle.loads(proc.stdout)
    except Exception:
        return None
    return rest[0] if tag == "results" else None


def _run_trace_in_subprocess(src, repo, fname, argvals, timeout_s, mem_mb, max_steps):
    """Trace the subject out of process via the standalone child, so explain()'s execution trace is
    available in every launch mode (a file, -m, -c, the REPL) -- the sandbox_trace counterpart of
    _run_in_subprocess, used where multiprocessing-spawn cannot re-import __main__. Returns the
    (outcome, [(lineno, {var: int}), ...], detail) tuple, or None if the child could not produce one."""
    import pickle, subprocess
    job = {"mode": "trace", "src": src, "repo": repo or {}, "fname": fname,
           "argvals": list(argvals), "mem_mb": mem_mb, "max_steps": max_steps}
    try:
        blob = pickle.dumps(job)
    except Exception:
        return None
    try:
        proc = subprocess.run([sys.executable, _sandbox_child_path()], input=blob,
                              capture_output=True, timeout=timeout_s + 2)
    except Exception:
        return None
    try:
        tag, out = pickle.loads(proc.stdout)
    except Exception:
        return None
    return tuple(out) if tag == "trace" else None


def sandbox_run_batch(src, repo, fname, inputs, timeout_s=4.0, mem_mb=512):
    """Evaluate `fname` on each tuple in `inputs` inside an isolated, resource-limited child process. Returns a
    list aligned with `inputs` of ('ok', int) / ('trap',) / ('nonint',), or None if the sandbox could not
    produce a result (setup error, timeout, no multiprocessing). When multiprocessing-spawn is unavailable (a
    `python -c` / REPL __main__), falls back to a standalone subprocess child."""
    return _spawn_worker(
        _sandbox_worker, (src, repo, fname, list(inputs), mem_mb), timeout_s,
        lambda msg: msg[1] if msg[0] == "results" else None,
        lambda: _run_in_subprocess("value", src, repo, fname, inputs, timeout_s, mem_mb))


def _sandbox_worker_typed(q, src, repo, fname, inputs, mem_mb):
    """Like _sandbox_worker, but reports the exception class name per input: ('ok',) on a clean finish,
    ('raise', name) on an exception. Lets a caller distinguish the traps the verifier models (e.g.
    ZeroDivisionError) from ones it does not (e.g. RecursionError)."""
    _apply_rlimits(mem_mb)
    fn = _sandbox_compile(src, repo, fname)
    if fn is None:
        q.put(("setup_error",)); return
    out = []
    for tup in inputs:
        try:
            fn(*tup); out.append(("ok",))
        except Exception as e:
            out.append(("raise", type(e).__name__))
    q.put(("results", out))


def sandbox_run_batch_typed(src, repo, fname, inputs, timeout_s=4.0, mem_mb=512):
    """Evaluate `fname` on each input tuple in an isolated child process, reporting ('ok',) or
    ('raise', exception_name) per input, or None if the sandbox could not run. The exception name lets a
    caller count only the trap kinds the verifier models. Falls back to a standalone subprocess child
    when multiprocessing-spawn is unavailable (a `python -c` / REPL __main__), so the typed oracle runs
    in every launch mode rather than silently abstaining."""
    return _spawn_worker(
        _sandbox_worker_typed, (src, repo, fname, list(inputs), mem_mb), timeout_s,
        lambda msg: msg[1] if msg[0] == "results" else None,
        lambda: _run_in_subprocess("typed", src, repo, fname, inputs, timeout_s, mem_mb))


def soundness_probe(src, z3args, rets, args, repo, k=300):
    """Empirical regression test for the integer encoding (subordinate to the Rocq theorem
    pyfloordiv_correct / pymod_correct in touchstone_encoding.v): sample concrete inputs and check the Z3 term
    against Python, skipping inputs where Python traps. Runs the subject, so gated behind
    ALLOW_SUBJECT_EXECUTION. No-op unless every parameter is an integer term."""
    if any(not z3.is_int(z3args[a]) for a in args):
        return
    pyfn = _pyfn(src, repo)
    val = fold(rets)
    rng = random.Random(7)
    for _ in range(k):
        sample = {a: rng.randint(-500, 500) for a in args}
        try:
            py = pyfn(*[sample[a] for a in args])
        except ZeroDivisionError:
            continue
        sub = z3.substitute(val, *[(z3args[a], z3.IntVal(sample[a])) for a in args])
        z = z3.simplify(sub).as_long()
        if z != py:
            raise AssertionError(f"UNSOUND encoding of {src!r} at {sample}: z3={z} py={py}")


def _expr_has_fp(e) -> bool:
    """True if the term mentions any floating-point sort, so the solver should bit-blast it."""
    seen, stack = set(), [e]
    while stack:
        n = stack.pop()
        if not z3.is_ast(n):
            continue
        k = n.get_id()
        if k in seen:
            continue
        seen.add(k)
        try:
            if z3.is_fp(n) or z3.is_fp_value(n) or (z3.is_app(n) and n.sort().kind() == z3.Z3_FLOATING_POINT_SORT):
                return True
        except z3.Z3Exception:
            pass
        if z3.is_app(n):
            stack.extend(n.children())
    return False


def _fp_query(fp, *args, retry=0):
    """Run a z3 Fixedpoint (Spacer) query with the process's native stderr (fd 2) muted for the call. z3 4.16's
    Spacer prints an internal assertion-violation notice to its C-level stderr on some nonlinear-CHC queries
    before raising a catchable Z3Exception (which the engines convert to UNKNOWN); this silences that stream
    without touching the Python result. If fd 2 cannot be duplicated, the query runs unmuted. `retry` re-runs
    the query up to that many extra times on a Z3Exception (a transient wall-clock timeout); the seeded search
    is deterministic, so only completion under the budget varies with load. Default 0 is single-shot."""
    last = None
    for _ in range(retry + 1):
        try:
            sys.stderr.flush()
            saved = os.dup(2)
            devnull = os.open(os.devnull, os.O_WRONLY)
        except OSError:
            return fp.query(*args)
        try:
            os.dup2(devnull, 2)
            return fp.query(*args)
        except z3.Z3Exception as e:
            last = e
        finally:
            sys.stderr.flush()
            os.dup2(saved, 2)
            os.close(devnull)
            os.close(saved)
    raise last


def _solve(claim_false) -> Tuple[str, Optional[z3.ModelRef]]:
    """Return (PROVED|REFUTED|UNKNOWN, model). claim_false asserts a counterexample. A fixed random seed keeps
    the result reproducible. A floating-point claim is bit-blasted (fpa2bv), making the theory decidable, so the
    query returns a definite verdict rather than timing out."""
    if _expr_has_fp(claim_false):
        # bit-blasting makes the FP theory decidable; the rlimit is the sole, machine-independent cutoff. The
        # wall-clock timeout is not set while an rlimit is in force (a load-dependent cutoff could turn a
        # decidable query into a spurious UNKNOWN); it is the lone backstop only when no rlimit is configured.
        s = z3.Then("simplify", "fpa2bv", "bit-blast", "smt").solver()
        if FP_SOLVE_RLIMIT:
            s.set("rlimit", FP_SOLVE_RLIMIT)
        else:
            s.set("timeout", FP_SOLVE_TIMEOUT_MS)
    else:
        s = z3.Solver()
        if SOLVE_RLIMIT:
            s.set("rlimit", SOLVE_RLIMIT)        # deterministic cutoff, the sole bound: the verdict depends on
        else:                                    # the resource budget, not on how fast or loaded the machine is
            s.set("timeout", SOLVE_TIMEOUT_MS)   # no rlimit configured: wall-clock is the only backstop
    s.set("random_seed", 0)
    s.add(claim_false)
    r = s.check()
    if r == z3.unsat:
        if RECORD_OBLIGATIONS is not None:
            RECORD_OBLIGATIONS.append(claim_false)
        return PROVED, None
    if r == z3.sat:
        return REFUTED, s.model()
    return UNKNOWN, None


def minimize_witness(claim_false, z3args, args):
    """A model of claim_false with the smallest, simplest integer parameters -- lexicographically the
    fewest nonzero, then the least total magnitude -- or None when minimization does not apply (a
    non-integer parameter) or the optimizer is inconclusive. The result still satisfies claim_false, so
    it is a genuine counterexample, just the minimal one."""
    if not args or any(not z3.is_int(z3args[a]) for a in args):
        return None
    try:
        o = z3.Optimize()
        if SOLVE_RLIMIT:
            o.set("rlimit", SOLVE_RLIMIT)        # deterministic cutoff: the reported minimal counterexample is
        else:                                    # reproducible across runs and machine load (a wall clock is not);
            o.set("timeout", SOLVE_TIMEOUT_MS)   # on starvation check() is unknown -> None -> the caller keeps its cex
        o.add(claim_false)
        absv = []
        for a in args:
            av = z3.Int("_m_" + a)
            o.add(av >= z3args[a], av + z3args[a] >= 0)          # av >= |x_a|
            absv.append(av)
        o.minimize(z3.Sum([z3.If(z3args[a] != 0, 1, 0) for a in args]))   # 1st: fewest nonzero parameters
        o.minimize(z3.Sum(absv))                                          # 2nd: least total magnitude
        return o.model() if o.check() == z3.sat else None
    except z3.Z3Exception:
        return None


def _trap_or(traps, subs=None) -> z3.ExprRef:
    """Disjunction of trap conditions (optionally rewritten by `subs`)."""
    if not traps:
        return z3.BoolVal(False)
    t = z3.Or(*traps)
    return z3.substitute(t, *subs) if subs else t


def escalate(v: Verdict) -> Verdict:
    print(f"        -> escalate [{v.prop}]: UNKNOWN ({v.reason})")
    return v


def _is_noreturn_call(call, env):
    """Whether a call terminates the program -- sys.exit / os._exit / os.abort (module-qualified, the module not
    shadowed by a local) or a bare exit() / quit() -- so it raises SystemExit / ends the process rather than
    falling through. The path stops there (no modeled crash), exactly as a `raise` does."""
    f = call.func
    if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id not in env:
        return (f.value.id, f.attr) in {("sys", "exit"), ("os", "_exit"), ("os", "abort")}
    return isinstance(f, ast.Name) and f.id in ("exit", "quit") and f.id not in env


def _apply_assigns(stmts, state, ctx, raise_is_trap=False):
    """Apply a block of assignments to a symbolic state. Conditionals are merged
    with z3.If; divisions emit nonzero traps through ctx when ctx.traps is a list.
    With raise_is_trap (the witness-recovery path only), a reachable `raise` records its path condition as a
    trap and ends the block, so a guarded input-validation raise (`if n < 0: raise`) sitting before a loop
    yields a concrete witness instead of declining the whole function."""
    st = dict(state)
    for s in stmts:
        if raise_is_trap and isinstance(s, ast.Raise):
            if ctx.traps is not None:
                ctx.traps.append(ctx.pc)                      # the input reaching this raise is the witness
            break                                            # statements after a raise are unreachable on this path
        if isinstance(s, ast.Assign):
            tgt = s.targets[0]
            if isinstance(tgt, ast.Name):
                st = dict(st)
                st[tgt.id] = ev(s.value, st, ctx)
            elif isinstance(tgt, (ast.Tuple, ast.List)) and all(isinstance(t, ast.Name) for t in tgt.elts):
                val = ev(s.value, st, ctx)                    # tuple unpacking a, b = b, a + b (the loop-body swap)
                if not (isinstance(val, tuple) and len(val) == len(tgt.elts)):
                    raise Unsupported("complex assignment target")   # a non-tuple / wrong-arity RHS: decline
                st = dict(st)
                for nm, vv in zip(tgt.elts, val):
                    st[nm.id] = vv
            else:
                raise Unsupported("complex assignment target")
        elif isinstance(s, ast.If):
            cond = ev_bool(s.test, st, ctx)
            old = ctx.pc
            ctx.pc = z3.And(old, cond); then_st = _apply_assigns(s.body, st, ctx, raise_is_trap)
            ctx.pc = z3.And(old, z3.Not(cond)); else_st = _apply_assigns(s.orelse, st, ctx, raise_is_trap)
            ctx.pc = old
            merged = dict(st)
            for k in set(then_st) | set(else_st):
                tv, ev_ = then_st.get(k, st.get(k)), else_st.get(k, st.get(k))
                # A variable defined on only one branch (and not before the if) is
                # undefined on the other path. Model the undefined side as havoc (a
                # fresh unconstrained int) under the branch guard, so no obligation
                # about it can be discharged on the path where it was never assigned;
                # definite-assignment (verify_definite_assignment) rejects such reads.
                if tv is None and ev_ is None:
                    continue
                elif tv is None:
                    merged[k] = z3.If(cond, z3.FreshInt("undef"), ev_)
                elif ev_ is None:
                    merged[k] = z3.If(cond, tv, z3.FreshInt("undef"))
                elif tv is ev_ or z3.eq(tv, ev_):
                    merged[k] = tv
                else:
                    merged[k] = z3.If(cond, tv, ev_)
            st = merged
        elif isinstance(s, ast.Expr):
            ev(s.value, st, ctx)                             # bare expression statement: for its traps only
            c = s.value                                      # a method call on a name -- or a subscript / attribute
            rn = (_recv_root_name(c.func.value)              # of one -- may mutate the container, so forget the
                  if isinstance(c, ast.Call) and isinstance(c.func, ast.Attribute) else None)   # ROOT name (a fresh
            if rn is not None and rn in st:                  # value) so a later read is not a stale pre-mutation one
                st = dict(st); st[rn] = z3.FreshInt("mut_" + rn)
        elif BEST_EFFORT:                                    # an unmodeled statement: havoc the names it assigns (lower trust)
            _best_effort_assume()
            st = dict(st)
            for nm in _stmt_assigned_names([s]):
                st[nm] = z3.FreshInt("be_stmt")
        else:
            raise Unsupported(f"statement {type(s).__name__} at line {getattr(s, 'lineno', '?')}")
    return st


def _parse_single_loop(src):
    fn = _fndef(src)
    args = [a.arg for a in fn.args.args]
    init, loop, ret, bad = [], None, None, False
    for s in fn.body:
        if isinstance(s, ast.While):
            if loop is None:
                loop = s
            else:
                bad = True                 # a second loop is not single-loop
        elif isinstance(s, ast.Return):
            ret = s
        elif loop is None:
            init.append(s)
        else:
            bad = True                     # a statement after the loop is dropped otherwise
    if bad:
        loop = None                        # force callers to "not a single-loop function"
    return fn, args, init, loop, ret


def solve_portfolio(claim_false, timeout=4000):
    """Return (PROVED|REFUTED|UNKNOWN, model, who)."""
    configs = [("z3:default", {}), ("z3:arith.solver=2", {"arith.solver": 2}),
               ("z3:arith.random_initial_value", {"smt.arith.random_initial_value": True})]
    for who, opts in configs:
        s = z3.Solver()
        s.set("timeout", timeout)
        for k, val in opts.items():
            try: s.set(k, val)
            except z3.Z3Exception: pass
        s.add(claim_false)
        r = s.check()
        if r == z3.unsat: return PROVED, None, who
        if r == z3.sat: return REFUTED, s.model(), who
    cv = solve_with_cvc5(claim_false)                              # independent solver fallback
    if cv != UNKNOWN:
        return cv, None, "cvc5"
    return UNKNOWN, None, "portfolio"


# Operations cvc5's native bindings cannot re-decide through the SMT-LIB round-trip, so a claim using one
# is left to the primary solver rather than risking a process-killing fault. The find-from-end and
# replace-all sequence/string operators (str.last_indexof / seq.last_indexof / str.replace_all /
# seq.replace_all) print as operators cvc5's parser faults on -- a segfault, not a clean "unknown".
# (The plain str.indexof / str.replace family round-trips cleanly under cvc5 1.3.4 and is corroborated;
# only the find-from-end and replace-all forms still fault.) z3's bitvector multiplication-overflow
# predicates print as the non-standard bvsmul_noovfl / bvumul_noovfl / bvsmul_noudfl operators its parser
# also faults on; _rewrite_for_cvc5 rewrites those to standard QF_BV before serialization, so they appear
# here only as a safety net for a predicate that survives the rewrite (e.g. one nested under a quantifier).
# (Add/sub overflow rides portable bvslt/bvadd/bvneg form, so it round-trips cleanly and is not listed.)
_CVC5_FRAGILE_OPS = {"str.last_indexof", "seq.last_indexof", "str.replace_all", "seq.replace_all",
                     "bvsmul_noovfl", "bvumul_noovfl", "bvsmul_noudfl"}

# z3's non-standard bitvector multiplication-overflow predicates. _rewrite_for_cvc5 replaces each with
# its standard QF_BV equivalent (sign/zero extension, a double-width product, and a comparison -- proven
# equal to z3's predicate for every w-bit pair in the corroboration self-test), so a multiplication-overflow
# PROVED serializes to SMT-LIB cvc5 parses and is corroborated by two solvers instead of resting on z3.
_BV_MULOVF_PREDS = {"bvsmul_noovfl", "bvumul_noovfl", "bvsmul_noudfl"}


def _bv_mulovf_standard(name, a, b):
    """The standard QF_BV equivalent of one of z3's non-standard bitvector multiplication-overflow
    predicates over operands a, b of width w. Signed no-overflow / no-underflow compare the exact
    double-width signed product against the signed w-bit bounds (z3's `<=` / `>=` on bitvectors are the
    signed comparisons); unsigned no-overflow requires the high w bits of the double-width unsigned
    product to be zero. Each is verified equal to z3's predicate over every w-bit pair in the audit."""
    w = a.size()
    if name == "bvumul_noovfl":
        wide = z3.ZeroExt(w, a) * z3.ZeroExt(w, b)
        return z3.Extract(2 * w - 1, w, wide) == z3.BitVecVal(0, w)
    wide = z3.SignExt(w, a) * z3.SignExt(w, b)
    if name == "bvsmul_noovfl":
        return wide <= z3.BitVecVal(2 ** (w - 1) - 1, 2 * w)
    return wide >= z3.BitVecVal(-(2 ** (w - 1)), 2 * w)          # bvsmul_noudfl


def _rewrite_for_cvc5(e):
    """Replace each bitvector multiplication-overflow predicate in e with its standard QF_BV equivalent,
    so the term serializes to SMT-LIB cvc5 parses instead of z3's non-standard bvsmul_noovfl / bvumul_noovfl
    / bvsmul_noudfl operators. A no-op for the common term containing none: a node is rebuilt only when a
    child actually changed. Non-application nodes (quantifiers, bound variables) pass through unchanged,
    so an overflow predicate nested under a quantifier is left in place and _cvc5_can_handle declines it."""
    if not z3.is_app(e):
        return e
    decl = e.decl()
    try:
        name = decl.name()
    except z3.Z3Exception:
        name = ""
    kids = e.children()
    new_kids = [_rewrite_for_cvc5(c) for c in kids]
    if name in _BV_MULOVF_PREDS and len(new_kids) == 2:
        return _bv_mulovf_standard(name, new_kids[0], new_kids[1])
    if not kids:
        return e
    if all(a.get_id() == b.get_id() for a, b in zip(kids, new_kids)):
        return e
    try:
        return decl(*new_kids)
    except z3.Z3Exception:
        return e


def _has_quantifier(e) -> bool:
    """Whether the term contains a quantifier anywhere, descending through application children."""
    seen, stack = set(), [e]
    while stack:
        n = stack.pop()
        if not z3.is_ast(n):
            continue
        k = n.get_id()
        if k in seen:
            continue
        seen.add(k)
        if z3.is_quantifier(n):
            return True
        if z3.is_app(n):
            stack.extend(n.children())
    return False


def _smtlib_quiet(claim_false) -> str:
    """Serialize claim_false to SMT-LIB (the form fed to the second solver) with z3's C-level pretty-printer
    warnings silenced at the file-descriptor level for the duration of the print. z3 emits a 'Constructing a
    fresh variable' notice when a shared subterm appears under a quantifier; it then prints correctly, but
    the notice is stderr noise here, so descriptor 2 is redirected to the null device only across the print
    and restored after. Falls back to a plain print where the descriptor cannot be redirected."""
    s = z3.Solver(); s.add(claim_false)
    saved = None
    try:
        sys.stderr.flush()
        saved = os.dup(2)
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, 2)
        os.close(devnull)
    except OSError:
        saved = None
    try:
        return "(set-logic ALL)\n" + s.to_smt2()
    finally:
        if saved is not None:
            os.dup2(saved, 2)
            os.close(saved)


def _serialization_is_faithful(e, smt) -> bool:
    """Confirm z3's SMT-LIB serialization of e round-trips without changing meaning, so a quantified claim
    whose printer captured a nested bound variable is declined rather than trusted. Re-parse the text and
    require the single re-parsed assertion equivalent to e (their difference unsatisfiable under the same
    deterministic bound). Any failure to confirm (undecided at the bound, a parse error) declines. Not run for
    a quantifier-free term, whose round-trip is always faithful."""
    try:
        s2 = z3.Solver()
        s2.from_string(smt)
        cl = s2.assertions()
        if len(cl) != 1:
            return False
        chk = z3.Solver()
        chk.set("rlimit", SOLVE_RLIMIT)
        chk.add(cl[0] != e)
        return chk.check() == z3.unsat
    except Exception:
        return False


def _cvc5_can_handle(e) -> bool:
    """False if the term contains an operation cvc5's bindings cannot re-decide through the SMT-LIB
    round-trip, so solve_with_cvc5 declines (UNKNOWN) rather than faulting: a find-from-end or replace-all
    sequence/string operator (_CVC5_FRAGILE_OPS), or a bitvector multiplication-overflow predicate that
    survived _rewrite_for_cvc5. The walk descends through quantifier bodies so a fragile operation nested
    under a binder is still caught. Whether a quantified term's serialization is faithful (no captured
    bound variable) is a separate check, _serialization_is_faithful, run where the serialization exists."""
    seen, stack = set(), [e]
    while stack:
        n = stack.pop()
        if not z3.is_ast(n):
            continue
        k = n.get_id()
        if k in seen:
            continue
        seen.add(k)
        if z3.is_quantifier(n):
            stack.append(n.body())                    # descend so a fragile op under a binder is caught
            continue
        if z3.is_app(n):
            try:
                if n.decl().name() in _CVC5_FRAGILE_OPS:
                    return False
            except z3.Z3Exception:
                pass
            stack.extend(n.children())
    return True


def _is_nonlinear(e) -> bool:
    """Whether e multiplies two non-constant arithmetic terms or raises one to a power."""
    seen, stack = set(), [e]
    while stack:
        n = stack.pop()
        if not z3.is_ast(n) or n.get_id() in seen:
            continue
        seen.add(n.get_id())
        if z3.is_app(n):
            try:
                kind = n.decl().kind()
            except z3.Z3Exception:
                kind = None
            ch = n.children()
            if kind == z3.Z3_OP_POWER:
                return True
            if kind == z3.Z3_OP_MUL and sum(not (z3.is_int_value(c) or z3.is_rational_value(c)) for c in ch) >= 2:
                return True
            stack.extend(ch)
    return False


def _nl_squared_bases(e):
    """The distinct arithmetic terms t for which t*t (or t**2) occurs in e."""
    bases, seen, stack = {}, set(), [e]
    while stack:
        n = stack.pop()
        if not z3.is_ast(n) or n.get_id() in seen:
            continue
        seen.add(n.get_id())
        if z3.is_app(n):
            try:
                kind = n.decl().kind()
            except z3.Z3Exception:
                kind = None
            ch = n.children()
            if kind == z3.Z3_OP_MUL and len(ch) == 2 and ch[0].get_id() == ch[1].get_id() and not z3.is_int_value(ch[0]):
                bases[ch[0].get_id()] = ch[0]
            elif kind == z3.Z3_OP_POWER and len(ch) == 2 and z3.is_int_value(ch[1]) and ch[1].as_long() == 2:
                bases[ch[0].get_id()] = ch[0]
            stack.extend(ch)
    return list(bases.values())


def _nl_lemmas(e):
    """Tautological hints for e's squared subterms: t*t >= 0, and a*a + b*b >= 2*a*b per pair. Each holds for
    all integers/reals, so conjoining them leaves the query's models unchanged -- a solver guide, not a premise."""
    bases = _nl_squared_bases(e)
    lemmas = [t * t >= 0 for t in bases]
    for i in range(len(bases)):
        for j in range(i + 1, len(bases)):
            lemmas.append(bases[i] * bases[i] + bases[j] * bases[j] >= 2 * bases[i] * bases[j])
    return lemmas


def _relax_to_real(e, m):
    """Rebuild the polynomial/boolean term e over the reals, each integer variable mapped to a fresh real (in m);
    an operation outside the arithmetic/comparison/boolean fragment raises Unsupported."""
    if z3.is_int_value(e):
        return z3.RealVal(e.as_long())
    if z3.is_rational_value(e):
        return e
    if z3.is_const(e) and z3.is_int(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        m.setdefault(e.get_id(), z3.Real("_rr_" + e.decl().name()))
        return m[e.get_id()]
    if not z3.is_app(e):
        raise Unsupported("relax non-application")
    k, ch = e.decl().kind(), [_relax_to_real(c, m) for c in e.children()]
    if k == z3.Z3_OP_ADD:
        return z3.Sum(ch)
    if k == z3.Z3_OP_MUL:
        acc = ch[0]
        for c in ch[1:]:
            acc = acc * c
        return acc
    if k == z3.Z3_OP_SUB:
        acc = ch[0]
        for c in ch[1:]:
            acc = acc - c
        return acc
    if k == z3.Z3_OP_UMINUS:
        return -ch[0]
    if k == z3.Z3_OP_POWER and z3.is_int_value(e.children()[1]):
        return ch[0] ** e.children()[1].as_long()
    cmp = {z3.Z3_OP_LE: lambda l, r: l <= r, z3.Z3_OP_LT: lambda l, r: l < r, z3.Z3_OP_GE: lambda l, r: l >= r,
           z3.Z3_OP_GT: lambda l, r: l > r, z3.Z3_OP_EQ: lambda l, r: l == r, z3.Z3_OP_DISTINCT: lambda l, r: l != r}
    if k in cmp:
        return cmp[k](ch[0], ch[1])
    if k == z3.Z3_OP_AND:
        return z3.And(*ch)
    if k == z3.Z3_OP_OR:
        return z3.Or(*ch)
    if k == z3.Z3_OP_NOT:
        return z3.Not(ch[0])
    if k == z3.Z3_OP_ITE:
        return z3.If(ch[0], ch[1], ch[2])
    if k == z3.Z3_OP_TRUE:
        return z3.BoolVal(True)
    if k == z3.Z3_OP_FALSE:
        return z3.BoolVal(False)
    raise Unsupported("relax operator %s" % e.decl().name())


def _real_relaxation_proves(claim_false) -> bool:
    """Prove-only: claim_false unsatisfiable over the reals (z3 nlsat, rlimit-bounded) proves it over the integers.
    Only real-unsat is reported; a non-integral real-SAT model is no counterexample, so this lane never refutes."""
    try:
        m = {}
        real_claim = _relax_to_real(claim_false, m)
        if not m:
            return False
        s = z3.SolverFor("QF_NRA")
        if SOLVE_RLIMIT:
            s.set("rlimit", SOLVE_RLIMIT)
        s.add(real_claim, *_nl_lemmas(real_claim))
        return s.check() == z3.unsat
    except (Unsupported, z3.Z3Exception):
        return False


def _cvc5_prep(claim_false, allow_nonlinear=False):
    """The cvc5 serialization of a refutation query, computed where the z3 AST is read so the solve can then run
    on the string in a thread (z3 ASTs are not safe to touch from two threads). Returns (smt_string, nonlinear)
    or None when cvc5 cannot handle the fragment or a quantified serialization does not round-trip."""
    try:
        import cvc5  # noqa: F401
    except Exception:
        return None
    claim_false = _rewrite_for_cvc5(claim_false)
    if not _cvc5_can_handle(claim_false):
        return None
    nonlinear = allow_nonlinear and _is_nonlinear(claim_false)
    query = z3.And(claim_false, *_nl_lemmas(claim_false)) if nonlinear else claim_false
    try:
        smt = _smtlib_quiet(query)
    except Exception:
        return None
    if _has_quantifier(query) and not _serialization_is_faithful(query, smt):
        return None
    return smt, nonlinear


def _cvc5_run_smt(smt, nonlinear, timeout_s=8):
    """Decide a pre-serialized SMT-LIB query with cvc5 (no z3 AST access, so it runs safely in a thread alongside
    z3). nonlinear uses the rlimit-bounded CAD extension (deterministic), else a per-call wall-clock limit."""
    try:
        import cvc5
        solver = cvc5.Solver()
        if nonlinear:                                        # CAD nonlinear extension, deterministically rlimit-bounded
            solver.setOption("nl-ext", "full")
            solver.setOption("nl-cov", "true")
            solver.setOption("rlimit", str(CVC5_RLIMIT))
        else:
            solver.setOption("tlimit-per", str(timeout_s * 1000))
        parser = cvc5.InputParser(solver)
        parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, smt, "q")
        sm = parser.getSymbolManager()
        result = None
        while True:
            cmd = parser.nextCommand()
            if cmd.isNull():
                break
            out = cmd.invoke(solver, sm)
            if out and out.strip() in ("sat", "unsat", "unknown"):
                result = out.strip()
        return {"unsat": PROVED, "sat": REFUTED}.get(result, UNKNOWN)
    except Exception:
        return UNKNOWN


def solve_with_cvc5(claim_false, timeout_s=8, allow_nonlinear=False):
    """Decide claim_false with cvc5 via its native bindings. allow_nonlinear enables the CAD extension (nl-cov,
    rlimit-bounded) with squared-subterm hints for a nonlinear claim -- opt-in, since CAD is costly. UNKNOWN if
    cvc5 is unavailable, undecided, hits an unhandled operation, or a quantified serialization does not round-trip."""
    prep = _cvc5_prep(claim_false, allow_nonlinear)
    return _cvc5_run_smt(prep[0], prep[1], timeout_s) if prep is not None else UNKNOWN


def cvc5_available() -> bool:
    """Whether the independent second solver (cvc5) can be imported in this environment."""
    try:
        import cvc5  # noqa: F401
        return True
    except Exception:
        return False


# Nonlinear trust model: a PROVED is never left on a single unchecked solver. The second confirmation is one of
# cvc5's nonlinear coverings, a checked SOS/Positivstellensatz certificate (verify_sos_nonneg, routed from
# prove), or the independent real-relaxation nlsat procedure -- always one, recorded in the certificate.
_NL_UNCORROBORATED = ("nonlinear: z3 proved it but no independent corroborator "
                      "(cvc5 coverings / SOS certificate / real-relaxation) confirmed it")


def solve_corroborated(claim_false):
    """Confirm a PROVED with a second procedure; returns (status, model, corroborator). cvc5 runs SEQUENTIALLY,
    after z3 and only when z3 proves: the cvc5 binding holds the GIL through its native solve, so running it in a
    thread beside z3 is no real overlap -- it only starves the main thread -- and the linear cvc5 confirm is cheap
    anyway. A cvc5 SAT raises SoundnessError; on a nonlinear abstention the real-relaxation lane is tried. cvc5
    absent or corroboration disabled degrades to a labeled single-solver PROVED; an uncorroborated nonlinear PROVED
    becomes UNKNOWN."""
    if not cvc5_available() or not REQUIRE_CORROBORATION:
        st, model = _solve(claim_false)
        return (st, model, "z3 only") if st == PROVED else (st, model, None)   # cvc5 missing/off: labeled single-solver
    st, model = _solve(claim_false)
    if st != PROVED:
        return st, model, None                              # cvc5 is only needed to confirm a PROVED
    nonlinear = _is_nonlinear(claim_false)
    cv = solve_with_cvc5(claim_false, allow_nonlinear=True)
    if cv == REFUTED:
        raise SoundnessError("a PROVED verdict is refuted by the independent solver (cvc5)")
    if cv == PROVED:
        return st, model, "z3 + cvc5 (nonlinear)" if nonlinear else "z3 + cvc5"
    if nonlinear:
        if _real_relaxation_proves(claim_false):
            return st, model, "z3 + real-relaxation (nlsat over the reals)"
        return UNKNOWN, None, _NL_UNCORROBORATED              # z3 proved it; no independent confirmation
    return UNKNOWN, None, None


def _claim_is_cvc5_safe(e) -> bool:
    """True if cvc5 can soundly re-decide this refutation query through the SMT-LIB round-trip, so a PROVED over
    it is corroborated by two solvers. cvc5 handles the quantifier-free integer, real, bitvector, array,
    datatype, float, string, and sequence fragments (multiplication-overflow predicates first rewritten to
    standard QF_BV by _rewrite_for_cvc5); a quantified query qualifies only when z3's serialization provably
    round-trips. Declines the find-from-end / replace-all string operators and an overflow predicate surviving
    the rewrite; the linear-integer obligations among those carry an SMTCoq kernel certificate instead."""
    e = _rewrite_for_cvc5(e)
    if not _cvc5_can_handle(e):
        return False
    if _has_quantifier(e):
        return _serialization_is_faithful(e, _smtlib_quiet(e))
    return True


def _solve_corro(claim_false):
    """_solve with the PROVED corroborated by cvc5: it runs on the same refutation query, a SAT result raises
    SoundnessError, and cvc5 undecided keeps the PROVED. The gate (_claim_is_cvc5_safe) covers every fragment
    cvc5 re-decides, so a heap, separation-logic, overflow, optional, theory, or quantified-spec PROVED is no
    longer single-solver. REFUTED and UNKNOWN pass through."""
    st, model = _solve(claim_false)
    if st == PROVED and REQUIRE_CORROBORATION and _claim_is_cvc5_safe(claim_false):
        if solve_with_cvc5(claim_false, timeout_s=4) == REFUTED:
            raise SoundnessError("a PROVED verdict is refuted by the independent solver (cvc5)")
    return st, model


class SoundnessError(Exception):
    """A verifier verdict contradicts concrete execution or an independent solver -> a prover bug."""


def _horn_interps(answer):
    """Parse a Spacer answer (fp.get_answer) into a per-relation interpretation. The answer mixes
    bare equations (0-ary relations) and quantified ones (Rel(vars..) == def under their own ForAll),
    nested under And, so the parse descends through And and ForAll. Each relation maps to a callable
    that instantiates its def at given arguments, reading the De Bruijn positions off the left-hand
    side so any argument order is handled."""
    interps = {}

    def visit(t):
        if z3.is_quantifier(t):
            visit(t.body()); return          # the body's De Bruijn variables refer to this quantifier
        if z3.is_and(t):
            for c in t.children():
                visit(c)
            return
        if not (z3.is_eq(t) and z3.is_app(t.arg(0))):
            return
        lhs, rhs = t.arg(0), t.arg(1)
        order = []
        for p in range(lhs.num_args()):
            ap = lhs.arg(p)
            if not z3.is_var(ap):
                return                       # not a relation-interpretation equation
            order.append(z3.get_var_index(ap))

        def make(rhs=rhs, order=order):
            def f(*args):
                width = (max(order) + 1) if order else 0
                sv = [z3.IntVal(0)] * width
                for p, k in enumerate(order):
                    sv[k] = args[p]
                return z3.substitute_vars(rhs, *sv) if sv else rhs
            return f
        interps[lhs.decl()] = make()

    visit(answer)
    return interps


def _subst_rels(term, interps):
    """Replace every application of an interpreted relation in `term` with its interpretation,
    leaving the rest of the term intact."""
    if not z3.is_app(term):
        return term
    decl = term.decl()
    children = [_subst_rels(c, interps) for c in term.children()]
    if decl in interps:
        return interps[decl](*children)
    return decl(*children) if children else term


def _corroborate_horn(fp, rules, query) -> bool:
    """Corroborate a Spacer PROVED with the second solver by re-checking the invariant it found. The
    invariant (fp.get_answer) is substituted into every Horn rule and the bad query, turning each into a
    verification condition cvc5 must find unsatisfiable. A cvc5 SAT means the reported invariant fails a
    condition -- the PROVED is wrong -- and raises SoundnessError; cvc5 unable to confirm a condition, or
    an answer that cannot be parsed, leaves the PROVED uncorroborated (False); confirming every condition
    returns True. Spacer sometimes returns a quantified invariant, whose VC the gate (_claim_is_cvc5_safe)
    declines because z3's SMT-LIB printer can capture a nested bound variable and flip the verdict; such a
    VC leaves the PROVED uncorroborated rather than risking a spurious refutation. Fail-safe: an extraction
    hiccup never fabricates one."""
    if not (REQUIRE_CORROBORATION and cvc5_available()):
        return False
    try:
        interps = _horn_interps(fp.get_answer())
        if not interps:
            return False
        # the query may be a 0-ary error relation, proved unreachable, or a bad formula. For an error
        # relation, every rule that derives it must have an unreachable body; its own reachability set
        # is dropped (it is False by assumption), keeping the check quantifier-free.
        qrel = (query.decl() if z3.is_app(query) and query.num_args() == 0
                and query.decl() in interps else None)
        if qrel is not None:
            interps = {d: f for d, f in interps.items() if d != qrel}
        if not interps:
            return False
        vcs = []
        for head, body in rules:
            bs = [_subst_rels(b, interps) for b in body]
            if qrel is not None and z3.is_app(head) and head.decl() == qrel:
                vcs.append(z3.And(*bs) if bs else z3.BoolVal(True))   # error rule: body unreachable
            else:
                hs = _subst_rels(head, interps)
                vcs.append(z3.And(*bs, z3.Not(hs)) if bs else z3.Not(hs))
        if qrel is None:
            vcs.append(_subst_rels(query, interps))                  # formula query: must be unsatisfiable
        for vc in vcs:
            if not _claim_is_cvc5_safe(vc):
                return False
            r = solve_with_cvc5(vc, timeout_s=4)
            if r == REFUTED:
                raise SoundnessError(
                    "a CHC PROVED is refuted by the independent solver: the synthesized invariant "
                    "fails a verification condition under cvc5")
            if r != PROVED:
                return False
        return True
    except SoundnessError:
        raise
    except Exception:
        return False


def _argnames(src):
    return [a.arg for a in _fndef(src).args.args]


def _run(src, repo, inputs):
    """Concrete result as a sentinel: ('val', x) on return, ('trap', None) on a
    division by zero. Trap-vs-value and value-vs-value are both comparable.
    Executes the subject: gated behind ALLOW_SUBJECT_EXECUTION at every call site."""
    fn = _pyfn(src, repo)
    try:
        return ("val", fn(*[inputs[a] for a in _argnames(src)]))
    except ZeroDivisionError:
        return ("trap", None)


__all__ = [
    '_Desugar',
    '_parse',
    '_fndef',
    'PROVED',
    'REFUTED',
    'UNKNOWN',
    'Verdict',
    'Unsupported',
    'NonConvergence',
    'py_floordiv',
    'py_mod',
    '_fp_fmod',
    '_fp_divmod',
    '_transcendental',
    '_str_method',
    '_BINOPS',
    '_CMP',
    '_as_bool',
    '_as_int',
    '_is_fp',
    '_to_fp',
    '_F64',
    '_model_cex',
    '_param_term',
    '_term_eq',
    '_term_neq',
    '_subst',
    'Ctx',
    'ev',
    'ev_bool',
    'symexec',
    'fold',
    '_heap_eval',
    '_heap_walk',
    'heap_attr',
    'list_len',
    'list_get',
    'list_forall',
    '_pyfn',
    'soundness_probe',
    '_solve',
    '_solve_corro',
    '_corroborate_horn',
    '_trap_or',
    'escalate',
    '_apply_assigns',
    '_parse_single_loop',
    'solve_portfolio',
    'solve_with_cvc5',
    'solve_corroborated',
    '_is_nonlinear',
    '_nl_lemmas',
    '_real_relaxation_proves',
    '_NL_UNCORROBORATED',
    'cvc5_available',
    'minimize_witness',
    'configure',
    'proof_certificate',
    'find_extracted',
    'encoding_executable',
    'extracted_encoding_batch',
    'SoundnessError',
    '_argnames',
    '_run',
]
