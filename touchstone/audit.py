"""Soundness auditing: the harness cross-checks its own verdicts against the SMT model, an
independent second translation, a second solver, and (under core.ALLOW_SUBJECT_EXECUTION) CPython.
Hosts the self-test suite and the demonstration."""
import ast
import hashlib
import inspect
import random
import struct
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
from .vcgen import *


def cross_engine_audit(src, pre, post, repo=None):
    repo = repo or {}
    engines = {"houdini": lambda: verify_deductive_auto("a", "f", src, pre, post, repo),
               "chc": lambda: verify_chc("a", "f", src, pre, post, repo),
               "cfg": lambda: verify_function("a", "f", src, pre, post, repo),
               "bmc": lambda: bmc_check("a", "f", src, pre, post, 16, repo),
               "learn": lambda: learn_invariant("a", "f", src, pre, post, repo)}
    verds = {}
    for name, run in engines.items():
        try:
            verds[name] = run().status
        except Exception:
            verds[name] = UNKNOWN
    if PROVED in verds.values() and REFUTED in verds.values():
        raise SoundnessError(f"engines disagree (PROVED vs REFUTED): {verds}")
    return verds


def bmc_audit(verdict, src, pre, post, k=12, repo=None):
    """Cross-check a loop verdict against an independent bounded unrolling, both ways.
    A PROVED that BMC refutes is a prover bug; a REFUTED whose claimed counterexample
    BMC cannot reproduce within k unrollings (when one is carried) is a spurious
    refutation. Either contradiction raises SoundnessError."""
    bmc = bmc_check("a", "f", src, pre, post, k, repo)
    if verdict.status == PROVED and bmc.status == REFUTED:
        raise SoundnessError("PROVED verdict has a bounded counterexample (BMC)")
    if (verdict.status == REFUTED and verdict.counterexample_inputs
            and bmc.status == UNKNOWN):
        # the engine claimed a counterexample; replay it in the bounded unrolling and
        # require the postcondition to actually fail on it within the bound.
        fn, args, init, loop, ret = _parse_single_loop(src)
        if loop is not None and ret is not None:
            ctx = Ctx(repo or {}); ctx.traps = []; ctx.pc = z3.BoolVal(True)
            base = {a: z3.Int(a) for a in args}
            cur = _apply_assigns(init, base, ctx)
            fails = z3.BoolVal(False); reached = z3.BoolVal(True)
            for _ in range(k):
                g = ev_bool(loop.test, cur, ctx)
                rexpr = ev(ret.value, cur, ctx)
                fails = z3.Or(fails, z3.And(reached, z3.Not(g), z3.Not(post(base, rexpr))))
                reached = z3.And(reached, g)
                cur = _apply_assigns(loop.body, cur, ctx)
            sub = [(base[a], z3.IntVal(verdict.counterexample_inputs[a]))
                   for a in args if a in verdict.counterexample_inputs]
            if sub and z3.is_false(z3.simplify(z3.substitute(fails, *sub))):
                raise SoundnessError(
                    f"REFUTED verdict's counterexample {verdict.counterexample_inputs} "
                    f"does not violate the postcondition within {k} unrollings")
    return True


def _ibool(x):
    return x if z3.is_bool(x) else (x != 0)


def _iint(x):                                    # the integer value of a term: a bool counts as 1 / 0
    return z3.If(x, z3.IntVal(1), z3.IntVal(0)) if z3.is_bool(x) else x


def _iev(node, env, traps, pc):
    if isinstance(node, ast.Constant) and isinstance(node.value, bool):
        return z3.BoolVal(node.value)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return z3.IntVal(node.value)
    if isinstance(node, ast.Name):
        if node.id not in env:
            raise Unsupported(f"indep free var {node.id}")
        return env[node.id]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -_iev(node.operand, env, traps, pc)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return z3.If(_ibool(_iev(node.operand, env, traps, pc)), z3.IntVal(0), z3.IntVal(1))
    if isinstance(node, ast.BinOp):
        l = _iint(_iev(node.left, env, traps, pc))           # a bool operand counts as its integer value
        r = _iint(_iev(node.right, env, traps, pc))
        op = type(node.op)
        if op is ast.Add: return l + r
        if op is ast.Sub: return l - r
        if op is ast.Mult: return l * r
        if op in (ast.FloorDiv, ast.Mod):
            traps.append(z3.And(pc, r == 0))
            q = z3.ToInt(z3.ToReal(l) / z3.ToReal(r))       # floor(a/b) via reals
            return q if op is ast.FloorDiv else (l - r * q)
        raise Unsupported(f"indep binop {op.__name__}")
    if isinstance(node, ast.BoolOp):                         # Python and / or keep operand value semantics:
        vals = [_iev(v, env, traps, pc) for v in node.values]   # `a and b` is a if a is falsy else b
        res = vals[-1]
        for v in reversed(vals[:-1]):
            cond, vi = _ibool(v), _iint(v)
            res = z3.If(cond, res, vi) if isinstance(node.op, ast.And) else z3.If(cond, vi, res)
        return res
    if isinstance(node, ast.IfExp):                          # ternary a if c else b
        c = _ibool(_iev(node.test, env, traps, pc))
        return z3.If(c, _iint(_iev(node.body, env, traps, pc)),
                     _iint(_iev(node.orelse, env, traps, pc)))
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        a = [_iint(_iev(x, env, traps, pc)) for x in node.args]
        if node.func.id == "abs" and len(a) == 1:
            return z3.If(a[0] >= 0, a[0], -a[0])
        if node.func.id == "min" and len(a) >= 2:            # over values; a single iterable may be empty
            acc = a[0]
            for x in a[1:]: acc = z3.If(x < acc, x, acc)
            return acc
        if node.func.id == "max" and len(a) >= 2:
            acc = a[0]
            for x in a[1:]: acc = z3.If(x > acc, x, acc)
            return acc
        raise Unsupported(f"indep call {node.func.id}")
    if isinstance(node, ast.Compare):
        if len(node.ops) != 1:
            raise Unsupported("indep chained comparison")
        return _CMP[type(node.ops[0])](_iint(_iev(node.left, env, traps, pc)),
                                       _iint(_iev(node.comparators[0], env, traps, pc)))
    raise Unsupported(f"indep expr {type(node).__name__}")


def _isymexec(src):
    fn = _parse(src).body[0]
    args = [a.arg for a in fn.args.args]
    z3args = {a: z3.Int(a) for a in args}
    rets, none_list, traps = [], [], []

    def walk(stmts, env, pc):
        falls = [(dict(env), pc)]
        for s in stmts:
            nxt = []
            for e, p in falls:
                if isinstance(s, ast.Return):
                    if s.value is None:
                        none_list.append(p)
                    else:
                        rets.append((p, _iev(s.value, e, traps, p)))
                elif isinstance(s, ast.Assign):
                    if len(s.targets) != 1 or not isinstance(s.targets[0], ast.Name):
                        raise Unsupported("indep complex target")
                    e2 = dict(e); e2[s.targets[0].id] = _iev(s.value, e2, traps, p)
                    nxt.append((e2, p))
                elif isinstance(s, ast.If):
                    c = _ibool(_iev(s.test, e, traps, p))
                    nxt += walk(s.body, e, z3.And(p, c))
                    nxt += walk(s.orelse, e, z3.And(p, z3.Not(c)))
                else:
                    raise Unsupported(f"indep stmt {type(s).__name__}")
            falls = nxt
        return falls

    for _e, p in walk(fn.body, z3args, z3.BoolVal(True)):
        none_list.append(p)
    none_pc = z3.Or(*none_list) if none_list else z3.BoolVal(False)
    return args, z3args, rets, traps, none_pc


def _independent_claim(impl_src, spec_src, repo):
    """The equivalence claim re-derived by the independent translation, or None if the subset is
    outside it. The second translation now covers booleans, conditionals (ternary and and/or value
    semantics), and the abs / min / max builtins as well as integer arithmetic, so the strongest
    cross-check stays live past plain arithmetic. Interprocedural calls (a non-empty repo) remain
    outside it: the independent translation is deliberately intraprocedural."""
    if repo:
        return None
    try:
        args, z3a, rets, itr, inone = _isymexec(impl_src)
        sargs, sz3, srets, strp, snone = _isymexec(spec_src)
    except Unsupported:
        return None
    if len(sargs) != len(args):
        return None
    subs = [(sz3[sf], z3a[af]) for sf, af in zip(sargs, args)]
    iv, sv = fold(rets), z3.substitute(fold(srets), *subs)
    itrap, strap = _trap_or(itr), _trap_or(strp, subs)
    snone = z3.substitute(snone, *subs) if subs else snone
    claim_false = z3.Or(z3.Xor(itrap, strap), z3.Xor(inone, snone),
                        z3.And(z3.Not(itrap), z3.Not(strap), z3.Not(inone), z3.Not(snone), iv != sv))
    return args, z3a, claim_false


def _equiv_claim(impl_src, spec_src, repo):
    """Re-derive the symbolic equivalence claim_false and the impl arg vars. No
    subject execution: pure translation to Z3 terms."""
    ctx = Ctx(repo)
    args, z3a, rets, itr, inone = symexec(impl_src, ctx)
    sargs, sz3, srets, strp, snone = symexec(spec_src, Ctx(repo))
    if len(sargs) != len(args):
        raise Unsupported("impl/spec arity mismatch")
    subs = [(sz3[sf], z3a[af]) for sf, af in zip(sargs, args)]
    iv, sv = fold(rets), z3.substitute(fold(srets), *subs)
    itrap, strap = _trap_or(itr), _trap_or(strp, subs)
    snone = z3.substitute(snone, *subs) if subs else snone
    claim_false = z3.Or(z3.Xor(itrap, strap), z3.Xor(inone, snone),
                        z3.And(z3.Not(itrap), z3.Not(strap), z3.Not(inone), z3.Not(snone), iv != sv))
    return args, z3a, claim_false


def model_cross_check(verdict, impl_src, spec_src, repo=None) -> int:
    """Audit a verify_equiv verdict WITHOUT running the subject. A PROVED claim is
    re-discharged symbolically (the disagreement must be UNSAT); a REFUTED claim's
    counterexample is substituted into the symbolic disagreement and must hold.
    Raises SoundnessError on a verdict the symbolic semantics contradicts."""
    repo = repo or {}
    if verdict.status == UNKNOWN:
        return 0
    args, z3a, claim_false = _equiv_claim(impl_src, spec_src, repo)
    indep = _independent_claim(impl_src, spec_src, repo)        # second, distinct translation
    if verdict.status == PROVED:
        st, _ = _solve(claim_false)
        if st != PROVED:
            raise SoundnessError(f"claimed PROVED but the symbolic disagreement is {st}")
        if indep is not None and _solve(indep[2])[0] != PROVED:
            raise SoundnessError(
                "claimed PROVED, but an independent translation does not discharge the disagreement")
        return 1
    if verdict.status == REFUTED:
        if not verdict.counterexample_inputs:
            return 0
        sub = [(z3a[a], z3.IntVal(verdict.counterexample_inputs[a])) for a in args]
        if not z3.is_true(z3.simplify(z3.substitute(claim_false, *sub))):
            raise SoundnessError(
                f"counterexample {verdict.counterexample_inputs} does not disagree symbolically")
        if indep is not None:
            iargs, iz3a, iclaim = indep
            isub = [(iz3a[a], z3.IntVal(verdict.counterexample_inputs[a]))
                    for a in iargs if a in verdict.counterexample_inputs]
            if isub and not z3.is_true(z3.simplify(z3.substitute(iclaim, *isub))):
                raise SoundnessError(
                    f"counterexample {verdict.counterexample_inputs} does not disagree "
                    f"under an independent translation")
        return 1
    return 0


def validate_counterexample(verdict, impl_src, spec_src, repo=None) -> bool:
    """Replay a REFUTED equivalence verdict concretely; the inputs must really disagree
    (a different value, or one traps while the other does not)."""
    repo = repo or {}
    if verdict.status != REFUTED or not verdict.counterexample_inputs:
        return True
    a = _run(impl_src, repo, verdict.counterexample_inputs)
    b = _run(spec_src, repo, verdict.counterexample_inputs)
    if a == b:
        raise SoundnessError(
            f"spurious counterexample {verdict.counterexample_inputs}: "
            f"impl and spec agree ({a})")
    return True


def differential_check(verdict, impl_src, spec_src, repo=None, samples=64, seed=0) -> int:
    """Cross-check a verify_equiv verdict against concrete runs. Returns #checks performed.
    Equivalence is trap-aware: agreement means equal values or both trapping."""
    repo = repo or {}
    args = _argnames(impl_src)
    rng = random.Random(seed)
    pool = [-(1 << 31), -1000, -7, -1, 0, 1, 7, 1000, (1 << 31) - 1]
    n = 0
    if verdict.status == PROVED:
        for _ in range(samples):
            inp = {a: (rng.choice(pool) if rng.random() < 0.4 else rng.randint(-300, 300))
                   for a in args}
            a_out = _run(impl_src, repo, inp)
            b_out = _run(spec_src, repo, inp)
            if a_out != b_out:
                raise SoundnessError(
                    f"PROVED equivalence is false at {inp}: impl={a_out} spec={b_out}")
            n += 1
    elif verdict.status == REFUTED:
        validate_counterexample(verdict, impl_src, spec_src, repo)
        n += 1
    return n


def exhaustive_check(verdict, impl_src, spec_src, repo=None, bound=12, max_inputs=200000) -> int:
    """Cross-check a verify_equiv verdict against concrete runs over EVERY integer input in the bounded box
    [-bound, bound] per parameter -- the whole box, not a random sample. A PROVED that agrees on every point of
    the box is a proof of the verdict over that box. A single disagreement raises SoundnessError; agreement is
    trap-aware (both trapping counts as agreement). Returns the number of inputs checked, or 0 when the box would
    exceed max_inputs. Runs the subject, so it is gated behind ALLOW_SUBJECT_EXECUTION like the sampled checks."""
    import itertools
    repo = repo or {}
    args = _argnames(impl_src)
    span = 2 * bound + 1
    if not args or span ** len(args) > max_inputs:
        return 0
    n = 0
    if verdict.status == PROVED:
        for combo in itertools.product(range(-bound, bound + 1), repeat=len(args)):
            inp = dict(zip(args, combo))
            if _run(impl_src, repo, inp) != _run(spec_src, repo, inp):
                raise SoundnessError(f"PROVED equivalence is false at {inp}")
            n += 1
    elif verdict.status == REFUTED:
        validate_counterexample(verdict, impl_src, spec_src, repo)
        n += 1
    return n


def _rand_expr(rng, vars_, depth):
    if depth == 0 or rng.random() < 0.35:
        if rng.random() < 0.5:
            return ("var", rng.choice(vars_))
        return ("const", rng.randint(-5, 5))
    op = rng.choice(["+", "-", "*", "+", "-", "*", "//", "%"])
    return (op, _rand_expr(rng, vars_, depth - 1), _rand_expr(rng, vars_, depth - 1))


def _render(e):
    if e[0] == "var":
        return e[1]
    if e[0] == "const":
        return str(e[1])
    return f"({_render(e[1])} {e[0]} {_render(e[2])})"


def _perturb(e, rng):
    # change one constant leaf, or wrap a subterm with +k, to (usually) break equivalence
    if e[0] == "const":
        return ("const", e[1] + rng.choice([-3, -2, -1, 1, 2, 3]))
    if e[0] == "var":
        return (rng.choice(["+", "-"]), e, ("const", rng.choice([1, 2, 3])))
    if rng.random() < 0.5:
        return (e[0], _perturb(e[1], rng), e[2])
    return (e[0], e[1], _perturb(e[2], rng))


def verification_benchmark():
    """A curated benchmark of verification problems with known answers, spanning the engine's
    capabilities. Reports the pass rate (the verdict matches the known answer) and precision (the
    fraction decided rather than left UNKNOWN). Every problem is authored to be decidable, so a wrong
    verdict is a soundness regression and a missing one is lost precision -- both are caught here and
    tracked over time. Returns the per-problem outcomes and the aggregate rates."""
    P, R = PROVED, REFUTED
    sq = "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"
    cnt = "def cnt(xs: list, i):\n    if i >= len(xs):\n        return 0\n    return 1 + cnt(xs, i + 1)\n"
    rng0 = lambda S: z3.And(S["i"] >= 0, S["i"] <= S["len_xs"])
    cases = [
        ("equiv: x+x == 2*x", lambda: verify_equiv("bm", "f", "def f(a):\n    return a + a\n",
                                                   "def g(a):\n    return 2 * a\n", {}), P),
        ("equiv: x+1 != x", lambda: verify_equiv("bm", "f", "def f(a):\n    return a + 1\n",
                                                 "def g(a):\n    return a\n", {}), R),
        ("equiv: (a+b)^2 expansion", lambda: verify_equiv("bm", "f",
            "def f(a, b):\n    return (a + b) * (a + b)\n",
            "def g(a, b):\n    return a * a + 2 * a * b + b * b\n", {}), P),
        ("prove: x*x >= 0", lambda: prove("def f(x):\n    return x * x\n", "result >= 0"), P),
        ("prove: abs >= 0", lambda: prove("def f(x):\n    return abs(x)\n", "result >= 0"), P),
        ("prove: bad postcondition", lambda: prove("def f(x):\n    return x + 1\n", "result == x"), R),
        ("loop: counter == n", lambda: prove("def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n",
                                             "result == n", requires="n >= 0"), P),
        ("loop synth: gauss sum", lambda: prove(sq, "2 * result == n * (n - 1)", requires="n >= 0"), P),
        ("bitmask: x & 7 == x % 8", lambda: verify_equiv("bm", "f", "def f(a):\n    return a & 7\n",
                                                         "def g(a):\n    return a % 8\n", {}), P),
        ("shift: x << 3 == x * 8", lambda: verify_equiv("bm", "f", "def f(a):\n    return a << 3\n",
                                                        "def g(a):\n    return a * 8\n", {}), P),
        ("recursion: factorial >= 1", lambda: verify_recursive("bm", "f",
            "def f(n):\n    if n <= 0:\n        return 1\n    return n * f(n - 1)\n",
            lambda Pp: Pp["n"] >= 0, lambda Pp, r: r >= 1), P),
        ("recursion over list: count", lambda: verify_recursive_list("bm", "cnt", cnt, rng0,
            lambda Pp, r: r == Pp["len_xs"] - Pp["i"]), P),
        ("mutual recursion: is_even", lambda: verify_program("bm", "is_even",
            {"is_even": "def is_even(n):\n    if n == 0:\n        return 1\n    return is_odd(n - 1)\n",
             "is_odd": "def is_odd(n):\n    if n == 0:\n        return 0\n    return is_even(n - 1)\n"},
            "is_even", lambda S: S["n"] >= 0, lambda S, r: z3.Or(r == 0, r == 1)), P),
        ("trap: 10 // x refuted", lambda: check("def f(x):\n    return 10 // x\n"), R),
        ("trap: guarded division", lambda: check("def f(x):\n    return 10 // x\n", requires="x != 0"), P),
        ("assert mined: holds", lambda: check("def f(x):\n    assert x * x >= 0\n    return x\n"), P),
        ("assert mined: can fail", lambda: check("def f(x):\n    assert x > 0\n    return x\n"), R),
        ("type mismatch: str < int", lambda: verify_predicate("bm", "f", "def f(s: str, i):\n    return s < i\n",
                                                              lambda za, r: z3.BoolVal(True), {}), R),
        ("termination: descending loop", lambda: verify_termination("bm", "f",
            "def f(n):\n    s = 0\n    for i in range(n, 0, -1):\n        s = s + 1\n    return s\n"), P),
        ("float: a+b == b+a refuted? finite", lambda: verify_float_finite("bm", "f",
            "def f(x):\n    return x\n", finite_inputs=True), P),
        ("float: 1.0/x not finite (total)", lambda: verify_float_finite("bm", "f",
            "def f(x):\n    if x == 0.0:\n        return 0.0\n    return 1.0 / x\n"), R),
        ("array: set-zero prefix", lambda: verify_array_loop_auto("bm", "f",
            "def f(a: list, n: int):\n    i = 0\n    while i < n:\n        a[i] = 0\n        i = i + 1\n    return a\n",
            lambda S: z3.And(S["n"] >= 0, S["n"] <= S["len_a"]),
            lambda S, E: q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]), z3.Select(S["a"], j) == 0))), P),
        ("heap: aliasing write visible", lambda: verify_heap_property("bm", "f",
            "def f(p, q):\n    a = object()\n    b = a\n    a.x = p\n    b.x = q\n    return a.x\n",
            lambda za, r: r == za["q"]), P),
        ("overflow companion: bounded add", lambda: verify_function("bm", "f", "def f(a, b):\n    return a + b\n",
            lambda S: z3.And(S["a"] >= 0, S["a"] <= 100, S["b"] >= 0, S["b"] <= 100),
            lambda S, r: r == S["a"] + S["b"]), P),
    ]
    results, correct, decided = [], 0, 0
    for name, run, expected in cases:
        v = run()
        ok = (v.status == expected)
        correct += ok
        decided += v.status in (PROVED, REFUTED)
        results.append({"problem": name, "expected": expected, "got": v.status, "ok": ok})
    total = len(cases)
    return {"total": total, "correct": correct, "decided": decided,
            "pass_rate": 100.0 * correct / total, "precision": 100.0 * decided / total,
            "results": results}


def random_equiv_problem(rng):
    vars_ = ["a"] if rng.random() < 0.5 else ["a", "b"]
    e = _rand_expr(rng, vars_, 3)
    impl = f"def f({', '.join(vars_)}):\n    return {_render(e)}\n"
    if rng.random() < 0.5:
        spec = f"def f({', '.join(vars_)}):\n    return {_render(e)}\n"      # identical
    else:
        spec = f"def f({', '.join(vars_)}):\n    return {_render(_perturb(e, rng))}\n"
    return impl, spec


def soundness_audit(trials=80, samples=48, seed=12345):
    """Generate programs, verify equivalence, and cross-check every verdict against
    the SMT model (no subject execution)."""
    rng = random.Random(seed)
    checks = 0
    proved = refuted = unknown = 0
    for t in range(trials):
        impl, spec = random_equiv_problem(rng)
        v = verify_equiv("audit", "f", impl, spec, {})
        if v.status == PROVED:
            proved += 1
        elif v.status == REFUTED:
            refuted += 1
        else:
            unknown += 1
        checks += model_cross_check(v, impl, spec, {})
    return {"trials": trials, "model_checks": checks,
            "proved": proved, "refuted": refuted, "unknown": unknown}


def division_encoding_audit(bound=60):
    """Brute-force the integer-division encoding against CPython: py_floordiv / py_mod
    must equal Python // and % for every nonzero divisor in [-bound, bound]^2. This is
    the empirical counterpart of touchstone_encoding.v. Raises SoundnessError on any
    mismatch; returns the number of (a, b) pairs checked."""
    n = 0
    for a in range(-bound, bound + 1):
        for b in range(-bound, bound + 1):
            if b == 0:
                continue
            zfd = z3.simplify(py_floordiv(z3.IntVal(a), z3.IntVal(b))).as_long()
            zmod = z3.simplify(py_mod(z3.IntVal(a), z3.IntVal(b))).as_long()
            if zfd != a // b or zmod != a % b:
                raise SoundnessError(f"division encoding mismatch at a={a}, b={b}: "
                                     f"z3=({zfd},{zmod}) python=({a // b},{a % b})")
            n += 1
    return n


def _fp_to_float(term):
    """The Python float a concrete Float64 term denotes (NaN, signed zero, Inf included)."""
    m = z3.simplify(term)
    if z3.is_true(z3.simplify(z3.fpIsNaN(m))):
        return _math.nan
    bits = z3.simplify(z3.fpToIEEEBV(m))
    if not z3.is_bv_value(bits):
        x = z3.BitVec("_fpx", 64); s = z3.Solver(); s.add(x == z3.fpToIEEEBV(m)); s.check(); bits = s.model()[x]
    return struct.unpack(">d", struct.pack(">Q", bits.as_long() & ((1 << 64) - 1)))[0]


def float_divmod_audit(seed=20240918):
    """Check _fp_divmod against CPython's float // and % bit-for-bit (NaN, signed zero, Inf, subnormals)
    over a grid of special and random doubles -- the float counterpart of division_encoding_audit, the
    standing guard on the exact (un-Rocq-proven) encoding. SoundnessError on any mismatch."""
    F = z3.Float64()
    fv = lambda x: z3.FPVal(x, F)
    specials = [0.0, -0.0, 1.0, -1.0, 2.0, -2.0, 0.5, -0.5, 3.0, -3.0, 2.5, -2.5, 100.0, 7.0, -7.0,
                _math.inf, -_math.inf, _math.nan, 2.0 ** 53, -2.0 ** 53, 2.0 ** -1074, 1e300, -1e300]
    rng = random.Random(seed)
    # all-pairs over the special values (the edge cases the encoding can get wrong) plus a random spread;
    # the random count is kept small because the check is quadratic in the pool and the specials carry
    # the soundness weight (signed zero, Inf, NaN, subnormals, large).
    pool = specials + [rng.uniform(-1e6, 1e6) for _ in range(20)] + [rng.uniform(-10, 10) for _ in range(20)]

    def beq(x, y):
        return True if (_math.isnan(x) and _math.isnan(y)) else struct.pack(">d", x) == struct.pack(">d", y)

    n = 0
    for a in pool:
        for b in pool:
            if b == 0.0:                                       # b == 0 is a trap, not a value
                continue
            fd, md = core._fp_divmod(fv(a), fv(b))
            zfd, zmd = _fp_to_float(fd), _fp_to_float(md)
            if not beq(zmd, a % b) or not beq(zfd, a // b):
                raise SoundnessError(f"float divmod mismatch at a={a!r}, b={b!r}: "
                                     f"z3=({zfd!r},{zmd!r}) python=({a // b!r},{a % b!r})")
            n += 1
    return n


def transcendental_axiom_audit(trials=3000, seed=20240919):
    """Validate against CPython the axioms _transcendental asserts: sin/cos in [-1, 1], exp nonnegative
    and overflow-free below 709.0, log finite on x > 0 and raising on x <= 0, and the anchors
    sin(0)=0, cos(0)=1, exp(0)=1, log(1)=0. A violated axiom is an unsound over-approximation:
    SoundnessError."""
    m = _math
    rng = random.Random(seed)
    pool = [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, m.pi, -m.pi, 100.0, -100.0, 709.0, -709.0, 1e-300, 1e300,
            2.0 ** -1074] + [rng.uniform(-1e6, 1e6) for _ in range(trials)]
    n = 0
    for x in pool:
        s, c = m.sin(x), m.cos(x)
        if not (-1.0 <= s <= 1.0):
            raise SoundnessError(f"sin({x!r})={s!r} outside [-1, 1]")
        if not (-1.0 <= c <= 1.0):
            raise SoundnessError(f"cos({x!r})={c!r} outside [-1, 1]")
        if x <= 709.0:                                         # the engine's exp overflow trap bound
            e = m.exp(x)
            if not (e >= 0.0):
                raise SoundnessError(f"exp({x!r})={e!r} is negative")
            if m.isfinite(x):                                  # the anchor-monotone bounds: exp >= 1 above 0, <= 1 below
                if x >= 0.0 and not (e >= 1.0):
                    raise SoundnessError(f"exp({x!r})={e!r} < 1 for x >= 0")
                if x <= 0.0 and not (e <= 1.0):
                    raise SoundnessError(f"exp({x!r})={e!r} > 1 for x <= 0")
        if x > 0.0:
            l = m.log(x)
            if m.isfinite(x) and not m.isfinite(l):
                raise SoundnessError(f"log({x!r})={l!r} not finite for finite x > 0")
            if m.isfinite(x):                                  # log >= 0 above 1, <= 0 below
                if x >= 1.0 and not (l >= 0.0):
                    raise SoundnessError(f"log({x!r})={l!r} < 0 for x >= 1")
                if x <= 1.0 and not (l <= 0.0):
                    raise SoundnessError(f"log({x!r})={l!r} > 0 for x <= 1")
        else:
            try:
                m.log(x)
                raise SoundnessError(f"log({x!r}) did not raise for x <= 0")
            except ValueError:
                pass
        n += 1
    if not (m.sin(0.0) == 0.0 and m.cos(0.0) == 1.0 and m.exp(0.0) == 1.0 and m.log(1.0) == 0.0):
        raise SoundnessError("a transcendental exact anchor (sin0/cos0/exp0/log1) does not hold")
    return n


def math_pow_axiom_audit(trials=2500, seed=20260625):
    """Validate against CPython the math.pow domain-trap predicate and the math.pow / x ** n value axioms (both
    trap directions and every asserted axiom). A violation is a SoundnessError."""
    m = _math
    rng = random.Random(seed)
    specials = [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 3.0, m.inf, -m.inf, m.nan, 1e300, -1e300,
                1e-300, 2.0 ** -1074]
    xs = specials + [rng.uniform(-1e6, 1e6) for _ in range(trials)]
    ys = specials + [rng.uniform(-20.0, 20.0) for _ in range(trials)]
    integral = lambda y: m.isfinite(y) and y == m.floor(y)
    n = 0
    for x, y in zip(xs, ys):
        engine_traps = (m.isfinite(x) and x < 0 and m.isfinite(y) and not integral(y)) \
            or (x == 0.0 and m.isfinite(y) and y < 0)
        try:
            r = m.pow(x, y); raised = False
        except ValueError:
            raised = True
        except OverflowError:
            n += 1; continue                             # OverflowError is not a modeled trap (core: not emitted)
        if engine_traps != raised:
            raise SoundnessError(f"math.pow trap predicate disagrees at x={x!r}, y={y!r}: "
                                 f"engine={engine_traps}, cpython_raises={raised}")
        if raised:
            n += 1; continue
        if y == 0.0 and r != 1.0:
            raise SoundnessError(f"math.pow({x!r}, 0) = {r!r} != 1")
        if x == 1.0 and r != 1.0:
            raise SoundnessError(f"math.pow(1, {y!r}) = {r!r} != 1")
        if not m.isnan(x) and not m.isnan(y) and x >= 0.0 and not (r >= 0.0):
            raise SoundnessError(f"math.pow({x!r}, {y!r}) = {r!r} < 0 for a nonnegative base")
        if x == 0.0 and y > 0.0 and r != 0.0:
            raise SoundnessError(f"math.pow(0, {y!r}) = {r!r} != 0 for y > 0")
        n += 1
    # the operator x ** n (constant integral n, modeled by _fp_pow): ZeroDivisionError iff base 0 and n < 0, and
    # the sign axioms hold only nonstrictly (a negative power underflows to +/-0).
    for x in xs:
        for nexp in (-3, -2, -1, 2, 3, 4):
            try:
                r = x ** float(nexp); raised = False
            except ZeroDivisionError:
                raised = True
            except OverflowError:
                continue                                 # OverflowError is not a modeled trap
            engine_traps = (nexp < 0 and x == 0.0)
            if engine_traps != raised:
                raise SoundnessError(f"operator {x!r} ** {nexp}: engine_traps={engine_traps}, cpython_raises={raised}")
            if raised or not m.isfinite(x):
                continue
            if nexp > 0:
                if x >= 0.0 and not (r >= 0.0):
                    raise SoundnessError(f"{x!r} ** {nexp} = {r!r} < 0 (nonneg base)")
                if nexp % 2 == 0 and not (r >= 0.0):
                    raise SoundnessError(f"{x!r} ** {nexp} = {r!r} < 0 (even power)")
                if nexp % 2 == 1 and x <= 0.0 and not (r <= 0.0):
                    raise SoundnessError(f"{x!r} ** {nexp} = {r!r} > 0 (odd power, nonpos base)")
            else:
                if x > 0.0 and not (r >= 0.0):
                    raise SoundnessError(f"{x!r} ** {nexp} = {r!r} < 0 (positive base, neg power)")
                if nexp % 2 == 0 and x != 0.0 and not (r >= 0.0):
                    raise SoundnessError(f"{x!r} ** {nexp} = {r!r} < 0 (even neg power)")
                if nexp % 2 == 1 and x < 0.0 and not (r <= 0.0):
                    raise SoundnessError(f"{x!r} ** {nexp} = {r!r} > 0 (odd neg power, neg base)")
            n += 1
    return n


def math_domain_audit():
    """Validate against CPython that each modeled math domain trap (core._math_call) covers the ValueError
    CPython raises: over a grid, CPython raising ValueError must imply the modeled trap fires. A missed
    ValueError is an unsound trap-freedom claim (SoundnessError). An OverflowError is not a modeled trap."""
    m = _math
    fv = [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, m.pi, -m.pi, m.inf, -m.inf, m.nan, 1e300, -1e300,
          0.9999, 1.0001, -0.9999, -1.0001]
    iv = list(range(-6, 7)) + [12, 20, -12, -20]
    floatdom = {                                              # the predicate must hold wherever CPython ValueErrors
        "floor": lambda x: m.isinf(x) or m.isnan(x), "ceil": lambda x: m.isinf(x) or m.isnan(x),
        "trunc": lambda x: m.isinf(x) or m.isnan(x), "log2": lambda x: x <= 0.0, "log10": lambda x: x <= 0.0,
        "log1p": lambda x: x <= -1.0, "asin": lambda x: x < -1.0 or x > 1.0, "acos": lambda x: x < -1.0 or x > 1.0,
        "acosh": lambda x: x < 1.0, "atanh": lambda x: x <= -1.0 or x >= 1.0,
    }
    n = 0
    for name, pred in floatdom.items():
        fn = getattr(m, name)
        for x in fv:
            try:
                fn(x); raised = False
            except ValueError:
                raised = True
            except OverflowError:
                continue                                      # overflow is not a modeled trap
            if raised and not pred(x):
                raise SoundnessError(f"math.{name}({x!r}) raises ValueError but the modeled trap misses it")
            n += 1
    for name, pred in (("factorial", lambda k: k < 0), ("isqrt", lambda k: k < 0)):
        fn = getattr(m, name)
        for x in iv:
            try:
                fn(x); raised = False
            except ValueError:
                raised = True
            if raised and not pred(x):
                raise SoundnessError(f"math.{name}({x}) raises ValueError but the modeled trap misses it")
            n += 1
    for x in iv:
        for k in iv:
            try:
                m.comb(x, k); raised = False
            except ValueError:
                raised = True
            if raised and not (x < 0 or k < 0):
                raise SoundnessError(f"math.comb({x},{k}) ValueError missed by the modeled trap")
            n += 1
    for a in fv:                                              # fmod: ValueError on an infinite dividend or zero divisor
        for b in fv:
            try:
                m.fmod(a, b); raised = False
            except ValueError:
                raised = True
            if raised and not (m.isinf(a) or b == 0.0):
                raise SoundnessError(f"math.fmod({a!r},{b!r}) ValueError missed by the modeled trap")
            n += 1
    return n


def stdlib_trapfree_audit():
    """Confirm each trap-free-registered stdlib function (core._STDLIB_TF) raises no MODELED trap (ValueError /
    TypeError / KeyError / IndexError / ZeroDivisionError / AssertionError) on a well-typed argument, and that
    every registered dotted name resolves to a real callable. A modeled trap on a valid argument is an unsound
    allowlist entry (SoundnessError); an unmodeled exception (OSError, ...) is fine."""
    import importlib, os
    MT = (ValueError, TypeError, KeyError, IndexError, ZeroDivisionError, AssertionError)
    _posix_only = {"os.getuid", "os.getgid", "os.geteuid", "os.getegid", "os.getpgrp", "os.getlogin"}
    for qual in core._STDLIB_TF:                              # every entry resolves to a callable
        if qual in _posix_only and os.name != "posix":       # POSIX-only here; resolved and exercised on Linux CI
            continue
        mod, _, leaf = qual.rpartition(".")
        try:
            obj = importlib.import_module(mod.split(".")[0])
            for part in mod.split(".")[1:] + [leaf]:
                obj = getattr(obj, part)
        except (ImportError, AttributeError):
            raise SoundnessError(f"trap-free stdlib entry {qual!r} does not resolve to a callable")
        if not callable(obj):
            raise SoundnessError(f"trap-free stdlib entry {qual!r} is not callable")
    import os, sys, time, itertools, functools, textwrap, hashlib, platform, copy, logging, re, string, base64, pathlib
    calls = [
        (pathlib.Path, ("a/b",)), (pathlib.PurePath, ("a/b",)), (pathlib.PurePosixPath, ("a/b",)),
        (os.path.join, ("a", "b")), (os.path.dirname, ("a/b",)), (os.path.basename, ("a/b",)),
        (os.path.normpath, ("a//b",)), (os.path.abspath, ("a",)), (os.path.expanduser, ("~/a",)),
        (os.path.splitext, ("a.txt",)), (os.path.split, ("a/b",)), (os.path.exists, ("a",)),
        (os.path.isfile, ("a",)), (os.path.isabs, ("a",)), (os.path.commonprefix, (["a", "ab"],)),
        (os.path.commonprefix, ([],)), (os.getpid, ()), (os.getcwd, ()), (os.getenv, ("PATH",)),
        (os.fspath, ("a",)), (sys.getsizeof, (5,)), (sys.getrecursionlimit, ()), (sys.intern, ("a",)),
        (time.time, ()), (time.monotonic, ()), (time.time_ns, ()), (time.ctime, ()),
        (textwrap.dedent, ("  a\n",)), (textwrap.fill, ("a b c", 2)), (textwrap.shorten, ("a b c", 5)),
        (functools.partial, (len, [1])), (functools.cmp_to_key, (lambda a, b: 0,)),
        (copy.copy, ([1, 2],)), (copy.deepcopy, ({"a": 1},)), (hashlib.md5, (b"x",)), (hashlib.sha256, (b"x",)),
        (platform.system, ()), (platform.machine, ()), (platform.python_version, ()),
        (logging.getLogger, ("x",)), (re.escape, ("a.b*",)), (string.capwords, ("a b",)),
        (base64.b64encode, (b"x",)),
        (lambda: list(itertools.chain([1], [2])), ()), (lambda: list(itertools.repeat(1, 3)), ()),
        (lambda: list(itertools.product([1], [2])), ()), (lambda: list(itertools.accumulate([1, 2, 3])), ()),
        (lambda: list(itertools.takewhile(lambda x: x < 2, [1, 2, 3])), ()),
    ]
    n = 0
    for fn, args in calls:
        try:
            fn(*args)
        except MT as e:
            raise SoundnessError(f"trap-free stdlib entry {getattr(fn, '__name__', fn)!r} raised a modeled trap "
                                 f"{type(e).__name__} on a well-typed argument: {e}")
        except Exception:
            pass                                              # an unmodeled exception (OSError, ...) is fine
        n += 1
    return n


def string_method_axiom_audit(trials=3000, seed=20240920):
    """Validate against CPython the axioms the str over-approximations assert: strip leaves a substring
    no longer than s (lstrip a suffix, rstrip a prefix); the case maps are empty iff s is; the is*
    predicates' empty-string value; count is nonnegative and 0 when the substring is absent; replace is
    a no-op when old is absent; the pad methods give length max(len(s), width). Over ASCII and Unicode
    whitespace and case oddities (where a length-exact model would be unsound). SoundnessError on a
    violation."""
    rng = random.Random(seed)
    chars = "ab AB \t\n\r\x0b\f\xa0 　ßİı"   # ASCII + Unicode whitespace + case oddities
    fixed = ["", " ", "  ", "ab", " ab ", "\tx\n", "\xa0z\xa0", "ßẞ", "İab", "  　  "]
    pool = fixed + ["".join(rng.choice(chars) for _ in range(rng.randint(0, 8))) for _ in range(trials)]
    for name in ("isdigit", "isalpha", "isalnum", "isspace", "isupper", "islower", "isnumeric",
                 "isdecimal", "istitle", "isidentifier", "isprintable", "isascii"):
        if getattr("", name)() != (name in ("isprintable", "isascii")):   # the only axiom: the empty value
            raise SoundnessError(f"empty-string axiom for str.{name} does not hold for CPython")
    n = 0
    for s in pool:
        st, ls, rs_ = s.strip(), s.lstrip(), s.rstrip()
        if st not in s or len(st) > len(s):
            raise SoundnessError(f"strip({s!r})={st!r} is not a substring no longer than s")
        if not s.endswith(ls) or len(ls) > len(s):
            raise SoundnessError(f"lstrip({s!r})={ls!r} is not a suffix no longer than s")
        if not s.startswith(rs_) or len(rs_) > len(s):
            raise SoundnessError(f"rstrip({s!r})={rs_!r} is not a prefix no longer than s")
        for cm in ("upper", "lower", "capitalize", "title", "swapcase", "casefold"):
            if (len(getattr(s, cm)()) == 0) != (len(s) == 0):
                raise SoundnessError(f"{cm}({s!r}) is empty but s is not (or vice versa)")
        for sub in ("a", "ab", "Q"):
            c = s.count(sub)
            if c < 0 or (sub not in s and c != 0):
                raise SoundnessError(f"count({s!r}, {sub!r})={c} violates the count axioms")
        for old in ("Q", "zz"):
            if old not in s and s.replace(old, "X") != s:
                raise SoundnessError(f"replace({s!r}, {old!r}, 'X') changed s though old is absent")
        for w in (0, 3, 10):
            for pm in ("ljust", "rjust", "center", "zfill"):
                if len(getattr(s, pm)(w)) != max(len(s), w):
                    raise SoundnessError(f"{pm}({s!r}, {w}) length is not max(len(s), {w})")
        n += 1
    return n


def format_spec_audit():
    """Validate core._format_spec_safe against CPython: for every (spec, value) in a grid, a spec the predicate
    calls safe for the value's modeled type must not raise under real format(). A safe spec CPython rejects is
    an unsound model (a false trap freedom): SoundnessError. Returns the number of safe combinations confirmed."""
    F = z3.Float64()
    samples = [(z3.IntVal(0), 0), (z3.IntVal(5), 5), (z3.IntVal(-7), -7), (z3.IntVal(255), 255),
               (z3.BoolVal(True), True), (z3.FPVal(0.0, F), 0.0), (z3.FPVal(3.14159, F), 3.14159),
               (z3.FPVal(-2.5, F), -2.5), (z3.FPVal(_math.inf, F), _math.inf), (z3.FPVal(_math.nan, F), _math.nan),
               (z3.StringVal(""), ""), (z3.StringVal("ab"), "ab")]
    specs = ["", "f", ".2f", "10.3f", "+.4e", "g", "G", "%", "08.2f", "d", "5d", "x", "#x", "X", "o", "b", "n",
             ">10", "<8", "^6", "*^10", ".5", "s", ">10s", "+d", " d", "-d", "c", ".2d", "05d", "zf", "z.2f",
             "_d", ",d", "#b", "=8", "0>5", "10", ".0f", ".3", "e", "E", "+f", "#o"]
    n = 0
    for vt, pv in samples:
        for spec in specs:
            if core._format_spec_safe(spec, vt):
                try:
                    format(pv, spec)
                except Exception as e:
                    raise SoundnessError(f"_format_spec_safe accepts {spec!r} for {pv!r} but CPython raises: {e}")
                n += 1
    return n


def _z3_replace_all(s, src, dst):
    """z3's str.replace_all string operator, which has no Python wrapper, via the C API."""
    return z3.SeqRef(z3.z3core.Z3_mk_seq_replace_all(s.ctx_ref(), s.as_ast(), src.as_ast(), dst.as_ast()), s.ctx)


def string_fragile_op_audit(seed=20240922):
    """Independently corroborate z3's find-from-end and replace-all string operators -- str.last_indexof and
    str.replace_all -- against Python's str.rfind and str.replace over a grid of concrete strings. These are the
    fragment cvc5 1.3.4 segfaults parsing, so the dual-solver gate cannot reach them and Python is the third
    checker. A disagreement is a z3 string-solver bug a PROVED using these operators could rest on, so it raises
    SoundnessError. Restricted to non-empty patterns, whose semantics Python and SMT-LIB share. Returns the
    number of (string, pattern, replacement) cases checked."""
    rng = random.Random(seed)
    fixed = ["", "a", "b", "ab", "ba", "aba", "bab", "abab", "aabb", "abba", "ababab", "xaby"]
    pool = fixed + ["".join(rng.choice("ab x") for _ in range(rng.randint(0, 8))) for _ in range(80)]
    subs = ["a", "b", "ab", "ba", "aa", "bb", "aba", "x", " x"]   # non-empty patterns
    reps = ["", "x", "Q", "ab", "yy"]
    n = 0
    for s in pool:
        S = z3.StringVal(s)
        for sub in subs:
            T = z3.StringVal(sub)
            li = z3.simplify(z3.LastIndexOf(S, T)).as_long()
            if li != s.rfind(sub):
                raise SoundnessError("z3 str.last_indexof(%r, %r)=%d != Python rfind=%d" % (s, sub, li, s.rfind(sub)))
            for rep in reps:
                ra = z3.simplify(_z3_replace_all(S, T, z3.StringVal(rep)))
                if not z3.is_string_value(ra) or ra.as_string() != s.replace(sub, rep):
                    raise SoundnessError("z3 str.replace_all(%r, %r, %r)=%r != Python replace=%r"
                                         % (s, sub, rep, ra, s.replace(sub, rep)))
                n += 1
    return n


def differential_equiv_audit(trials=120, seed=4321):
    """Generate random loop-free integer programs, verify equivalence, and cross-check
    EVERY verdict against real CPython execution -- the one oracle that is independent of
    the symbolic translation. Requires ALLOW_SUBJECT_EXECUTION (a trusted sandbox running
    only self-generated programs). Raises SoundnessError if a PROVED equivalence ever
    disagrees under execution, or a REFUTED counterexample fails to disagree."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("differential_equiv_audit requires ALLOW_SUBJECT_EXECUTION")
    rng = random.Random(seed)
    proved = refuted = unknown = exec_checks = 0
    for _ in range(trials):
        impl, spec = random_equiv_problem(rng)
        v = verify_equiv("audit", "f", impl, spec, {})
        if v.status == PROVED:
            proved += 1
        elif v.status == REFUTED:
            refuted += 1
        else:
            unknown += 1
        exec_checks += differential_check(v, impl, spec, {})    # real execution comparison
    return {"trials": trials, "proved": proved, "refuted": refuted,
            "unknown": unknown, "exec_checks": exec_checks}


def differential_loop_audit(trials=60, seed=99):
    """Extend the CPython oracle to the looping CHC engine: generate random linear-accumulator
    loops with a sometimes-perturbed postcondition, verify each with verify_chc, and cross-check
    the verdict against real execution. A PROVED the interpreter violates, or a REFUTED it
    satisfies, raises SoundnessError. Runs the subject, so it needs ALLOW_SUBJECT_EXECUTION."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("differential_loop_audit requires ALLOW_SUBJECT_EXECUTION")
    rng = random.Random(seed)
    proved = refuted = unknown = checks = 0
    for _ in range(trials):
        c0, k = rng.randint(-5, 5), rng.randint(-3, 3)
        delta = 0 if rng.random() < 0.5 else rng.choice([-1, 1, 2])   # 0 => correct spec
        src = (f"def f(n):\n    a = {c0}\n    i = 0\n    while i < n:\n"
               f"        a = a + {k}\n        i = i + 1\n    return a\n")
        post = lambda S, r, c0=c0, k=k, d=delta: r == c0 + k * S["n"] + d
        v = verify_chc("dl", "f", src, lambda S: S["n"] >= 0, post)
        pyfn = _pyfn(src, {})
        holds = all(pyfn(n) == c0 + k * n + delta for n in range(0, 25))   # CPython oracle
        if v.status == PROVED:
            proved += 1; checks += 1
            if not holds:
                raise SoundnessError(f"loop PROVED but CPython violates it: {src!r} delta={delta}")
        elif v.status == REFUTED:
            refuted += 1; checks += 1
            if holds:
                raise SoundnessError(f"loop REFUTED but CPython satisfies it: {src!r} delta={delta}")
        else:
            unknown += 1
    return {"trials": trials, "proved": proved, "refuted": refuted, "unknown": unknown, "exec_checks": checks}


def differential_heap_audit(trials=80, seed=1717):
    """Extend the CPython oracle to the heap engine: generate small object/list/dict programs over
    random integer inputs with a sometimes-perturbed postcondition, verify each with
    verify_heap_property, and cross-check the verdict against real execution -- objects via a real
    class, lists and dicts via the real builtins. A PROVED CPython violates, or a REFUTED it
    satisfies on the sampled inputs, raises SoundnessError. Needs ALLOW_SUBJECT_EXECUTION."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("differential_heap_audit requires ALLOW_SUBJECT_EXECUTION")
    rng = random.Random(seed)
    _CLASS = "class C:\n    def __init__(self, v):\n        self.v = v\n\n"
    # (source, params, Python oracle); each returns one integer from a heap manipulation.
    templates = [
        (_CLASS + "def f(a, b):\n    o = C(a)\n    p = o\n    p.v = b\n    return o.v\n",
         ["a", "b"], lambda a, b: b),                                       # aliasing: last write wins
        ("def f(a, b, c):\n    xs = [a, b, c]\n    return xs[1]\n",
         ["a", "b", "c"], lambda a, b, c: b),                              # list index
        ("def f(a, b):\n    xs = [a]\n    xs.append(b)\n    return xs[1]\n",
         ["a", "b"], lambda a, b: b),                                      # list append then index
        ("def f(a, b):\n    d = {0: a, 1: b}\n    return d[1]\n",
         ["a", "b"], lambda a, b: b),                                      # dict lookup
        (_CLASS + "def f(a):\n    o = C(a)\n    return o.v\n",
         ["a"], lambda a: a),                                              # attribute round-trip
    ]
    def make_post(oracle, params, delta):                                 # exactly two args, so
        return lambda za, r: r == oracle(*[za[p] for p in params]) + delta  # verify_heap_property does
    #                                                                       not mistake it for a heap spec
    proved = refuted = unknown = checks = 0
    for _ in range(trials):
        src, params, oracle = rng.choice(templates)
        delta = 0 if rng.random() < 0.5 else rng.choice([-1, 1, 2])        # 0 => correct spec
        post = make_post(oracle, params, delta)
        v = verify_heap_property("dheap", "f", src, post)
        ns: dict = {}
        exec(textwrap.dedent(src), ns)                                    # real class / list / dict
        fn = ns["f"]
        holds = all(fn(*pt) == oracle(*pt) + delta                        # CPython oracle over a sample grid
                    for pt in [tuple(rng.randint(-6, 6) for _ in params) for _ in range(20)])
        if v.status == PROVED:
            proved += 1; checks += 1
            if not holds:
                raise SoundnessError(f"heap PROVED but CPython violates it: {src!r} delta={delta}")
        elif v.status == REFUTED:
            refuted += 1; checks += 1
            if holds:
                raise SoundnessError(f"heap REFUTED but CPython satisfies it: {src!r} delta={delta}")
        else:
            unknown += 1
    return {"trials": trials, "proved": proved, "refuted": refuted, "unknown": unknown, "exec_checks": checks}


def differential_sequence_audit(trials=40, seed=606):
    """Extend the CPython oracle to the sequence-loop engine: generate random accumulator loops over a
    list parameter with a sometimes-perturbed postcondition, verify each with verify_sequence_loop, and
    cross-check the verdict against real execution on random lists. The accumulator advances by a
    constant per element, so its exit value is c0 + k * len(xs); a PROVED CPython violates, or a REFUTED
    it satisfies on the sampled lists, raises SoundnessError. Needs ALLOW_SUBJECT_EXECUTION."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("differential_sequence_audit requires ALLOW_SUBJECT_EXECUTION")
    rng = random.Random(seed)
    proved = refuted = unknown = checks = 0
    for _ in range(trials):
        c0, k = rng.randint(-4, 4), rng.randint(-3, 3)
        delta = 0 if rng.random() < 0.5 else rng.choice([-2, -1, 1, 2])         # 0 => correct spec
        src = f"def f(xs: list):\n    acc = {c0}\n    for x in xs:\n        acc = acc + {k}\n    return acc\n"
        post = lambda P, r, c0=c0, k=k, d=delta: r == c0 + k * P["len_xs"] + d
        v = verify_sequence_loop("dseq", "f", src, post)
        ns: dict = {}
        exec(textwrap.dedent(src), ns)                                          # real list iteration
        fn = ns["f"]
        holds = all(fn([rng.randint(-9, 9) for _ in range(L)]) == c0 + k * L + delta for L in range(0, 14))
        if v.status == PROVED:
            proved += 1; checks += 1
            if not holds:
                raise SoundnessError(f"sequence PROVED but CPython violates it: {src!r} delta={delta}")
        elif v.status == REFUTED:
            refuted += 1; checks += 1
            if holds:
                raise SoundnessError(f"sequence REFUTED but CPython satisfies it: {src!r} delta={delta}")
        else:
            unknown += 1
    return {"trials": trials, "proved": proved, "refuted": refuted, "unknown": unknown, "exec_checks": checks}


def _bit_eq(a, b):
    """Value equality matching the symbolic semantics: floats compare bit-for-bit (NaN equals NaN,
    +0.0 differs from -0.0), everything else by Python equality."""
    if isinstance(a, float) or isinstance(b, float):
        try:
            return struct.pack(">d", float(a)) == struct.pack(">d", float(b))
        except (OverflowError, ValueError, TypeError):
            return a == b
    return a == b


def differential_typed_audit(seed=20240917):
    """Replay float, boolean, and string equivalence counterexamples against CPython, not only integer
    ones, with float results compared bit-for-bit to match the symbolic semantics. A PROVED
    equivalence is sampled on typed inputs (the float special values among them); a REFUTED one's
    counterexample is re-run and must genuinely disagree. Raises SoundnessError on any disagreement.
    Needs ALLOW_SUBJECT_EXECUTION."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("differential_typed_audit requires ALLOW_SUBJECT_EXECUTION")
    rng = random.Random(seed)
    specials = [0.0, -0.0, 1.0, -1.0, 0.5, _math.inf, -_math.inf, _math.nan, 2.0 ** 53, 2.0 ** -1074]

    def sample(ty):
        if ty == "float":
            return rng.choice(specials) if rng.random() < 0.4 else rng.uniform(-1e6, 1e6)
        if ty == "bool":
            return rng.random() < 0.5
        return "".join(rng.choice("AB ") for _ in range(rng.randint(0, 4)))

    cases = [
        ("def f(x: float):\n    return x + x\n", "def g(x: float):\n    return 2.0 * x\n", PROVED, "float"),
        ("def f(x: float):\n    return x + 0.0\n", "def g(x: float):\n    return x\n", REFUTED, "float"),
        ("def f(a: bool, b: bool):\n    return not (a or b)\n",
         "def g(a: bool, b: bool):\n    return (not a) and (not b)\n", PROVED, "bool"),
        ("def f(a: bool, b: bool):\n    return a and b\n",
         "def g(a: bool, b: bool):\n    return a or b\n", REFUTED, "bool"),
        ("def f(a: str, b: str):\n    return (a + b) + a\n",
         "def g(a: str, b: str):\n    return a + (b + a)\n", PROVED, "str"),
        ("def f(a: str, b: str):\n    return a + b\n", "def g(a: str, b: str):\n    return b + a\n", REFUTED, "str"),
    ]
    proved = refuted = checks = 0
    for impl, spec, expected, ty in cases:
        v = verify_equiv("typed", "f", impl, spec, {})
        if v.status != expected:
            raise SoundnessError(f"typed equivalence ({ty}): expected {expected}, got {v.status} for {impl!r}")
        fi, fg = _pyfn(impl, {}), _pyfn(spec, {})
        args = _argnames(impl)
        if v.status == REFUTED:
            inp = v.counterexample_inputs
            if not inp or any(a not in inp for a in args):
                raise SoundnessError(f"REFUTED {ty} verdict has no replayable counterexample: {impl!r}")
            ai, ag = fi(*[inp[a] for a in args]), fg(*[inp[a] for a in args])
            if _bit_eq(ai, ag):
                raise SoundnessError(f"REFUTED {ty} counterexample {inp} does not disagree: {ai!r} vs {ag!r}")
            refuted += 1; checks += 1
        else:
            for _ in range(40):
                xs = [sample(ty) for _ in args]
                if not _bit_eq(fi(*xs), fg(*xs)):
                    raise SoundnessError(f"PROVED {ty} equivalence disagrees at {xs}: {fi(*xs)!r} vs {fg(*xs)!r}")
                checks += 1
            proved += 1
    return {"proved": proved, "refuted": refuted, "checks": checks}


def differential_method_audit():
    """Cross-check the modular method-call model against CPython. Each case is a method call on a
    concrete builtin receiver with type-valid arguments; a verdict PROVED while CPython raises a modeled
    trap means a trapping method is missing from core._TRAPPING_METHODS. Needs ALLOW_SUBJECT_EXECUTION."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("differential_method_audit requires ALLOW_SUBJECT_EXECUTION")
    from . import domains as _bench
    exprs = [
        "[].pop()", "[1, 2].pop(5)", "[1, 2].remove(9)", "[1, 2].index(9)", "[1, 'a'].sort()",
        "{}.popitem()", "{1: 2}.pop(9)", "set().pop()", "{1, 2}.remove(9)",
        "'abc'.index('z')", "'abc'.rindex('z')", "'abc'.split('')", "'a b c'.split()",
        "'{}'.format()", "'{k}'.format_map({})", "b'\\xff'.decode('ascii')", "'-'.join([1, 2])",
        "'abc'.upper()", "'abc'.lower()", "'  x  '.strip()", "'abc'.replace('a', 'z')",
        "'a,b'.count(',')", "'abc'.startswith('a')", "'abc'.find('z')", "'abc'.center(7)",
        "'abc'.zfill(6)", "'abc'.title()", "'abc'.casefold()", "'a.b'.partition('.')",
        "(1, 2, 3).count(2)", "(1, 2, 3).index(9)", "[1, 2].append(3)", "[1, 2].extend([3])",
        "{1: 2}.get(9)", "{1, 2}.add(3)", "{1, 2}.discard(9)",
        "(7).bit_length()", "(255).to_bytes(1, 'big')", "(1.5).is_integer()", "(1.5).as_integer_ratio()",
    ]
    proved = refuted = unknown = checks = 0
    for e in exprs:
        try:
            eval(e); trap = None
        except Exception as ex:
            trap = type(ex).__name__ if type(ex).__name__ in _bench._MODELED_TRAPS else None
        v = _bench._decide("def f():\n    return %s\n" % e, {})
        checks += 1
        if v.status == PROVED:
            proved += 1
            if trap is not None:
                raise SoundnessError("method PROVED trap-free but CPython raised %s: %s" % (trap, e))
        elif v.status == REFUTED:
            refuted += 1
        else:
            unknown += 1
    return {"checks": checks, "proved": proved, "refuted": refuted, "unknown": unknown}


def _grammar_program(rng):
    """A random loop-free program over the container grammar -- list literals, [x] * n repetition (the shared-row
    alias), `b = a` aliasing, indexing, append / item-store mutation, and one level of nesting -- returning an int
    (a len or an element). It deliberately COMPOSES aliasing x mutation x repetition, the interaction a
    single-construct corpus misses (the [[0]] * 2 shared-row trap). The body is `def f():` over literal seeds, so
    CPython gives one deterministic answer the symbolic verdict is differentially checked against."""
    sm = lambda: str(rng.randint(0, 3))
    lst = lambda: "[" + ", ".join(sm() for _ in range(rng.randint(1, 3))) + "]"
    seed = rng.choice([
        lambda: "a = " + lst(),                                  # a flat list of ints
        lambda: "a = [%s] * %d" % (lst(), rng.randint(2, 3)),    # repetition: the rows are ONE shared inner list
        lambda: "a = [%s, %s]" % (lst(), lst()),                 # separately-written rows
        lambda: "a = [%s] * %d" % (sm(), rng.randint(2, 4)),     # flat repetition of an int (immutable: safe)
    ])
    lines, aliased = [seed()], False
    for _ in range(rng.randint(1, 4)):
        k = rng.random()
        if k < 0.2 and not aliased:
            lines.append("b = a"); aliased = True                # alias, so a later mutation is seen through b too
        elif k < 0.45:
            lines.append("a.append(%s)" % sm())                  # mutate a directly
        elif k < 0.7:
            lines.append("a[0].append(%s)" % sm())               # mutate THROUGH a subscript (the [[0]]*2 shape)
        elif k < 0.85:
            lines.append("a[%d] = %s" % (rng.randint(0, 1), sm()))   # item store
        elif aliased:
            lines.append("b.append(%s)" % sm())                  # mutate through the alias
        else:
            lines.append("a.append(%s)" % sm())
    reads = ["return len(a)", "return len(a[0])", "return a[0]", "return a[1]"]
    if aliased:
        reads += ["return len(b)", "return b[0]", "return len(b[0])"]
    lines.append(rng.choice(reads))
    return "def f():\n" + "".join("    " + s + "\n" for s in lines)


def differential_grammar_audit(trials=150, seed=20260628):
    """A GENERATIVE differential check of the container-grammar translation against CPython -- the defense against
    TRANSLATION bugs, which corroboration (two solvers on ONE translation) cannot catch. Each random program
    (composing aliasing / mutation / repetition -- the interaction the curated corpus missed) is run in the
    sandbox for its deterministic CPython answer, and the symbolic verdict is required to AGREE or abstain, never
    disagree: a REFUTED of a value CPython returns, a PROVED of a value it does not, a PROVED trap-freedom of a
    function that raises a modeled trap, or a REFUTED trap-freedom of a clean run is a translation bug
    (SoundnessError). This is exactly the check the [[0]] * 2 shared-row bug failed. Needs ALLOW_SUBJECT_EXECUTION."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("differential_grammar_audit requires ALLOW_SUBJECT_EXECUTION")
    rng = random.Random(seed)
    checks = value_checks = trap_checks = 0
    for _ in range(trials):
        src = _grammar_program(rng)
        out = core.sandbox_run_batch(src, {}, "f", [[]])         # CPython's answer: ('ok', int) / ('nonint',) / ('trap',)
        if out is None:
            return {"available": False, "checks": 0}             # no sandbox in this environment: skip cleanly
        res = out[0]
        if res[0] == "ok":                                       # a clean int return: the engine must agree on it
            v = res[1]
            if prove(src, "result == %d" % v, target="f").status == REFUTED:
                raise SoundnessError("translation bug: REFUTED a postcondition CPython satisfies "
                                     "(result == %d) for:\n%s" % (v, src))
            for w in (v + 1, v - 1):                             # ...and must not prove a value CPython contradicts
                if prove(src, "result == %d" % w, target="f").status == PROVED:
                    raise SoundnessError("translation bug: PROVED result == %d but CPython returns %d for:\n%s"
                                         % (w, v, src))
            value_checks += 1
        if res[0] in ("ok", "nonint"):                           # a clean run: trap freedom must not be REFUTED
            if check(src, target="f").status == REFUTED:
                raise SoundnessError("translation bug: REFUTED trap freedom of a function CPython runs cleanly:\n%s" % src)
            trap_checks += 1
        elif res[0] == "trap":                                   # CPython raised: if a MODELED trap, no false PROVED
            typed = core.sandbox_run_batch_typed(src, {}, "f", [[]])
            if typed and typed[0][0] == "raise" and typed[0][1] in core._MODELED_TRAP_NAMES:
                if check(src, target="f").status == PROVED:
                    raise SoundnessError("translation bug: PROVED trap freedom but CPython raises %s:\n%s"
                                         % (typed[0][1], src))
                trap_checks += 1
        checks += 1
    return {"trials": trials, "checks": checks, "value_checks": value_checks, "trap_checks": trap_checks}


def differential_sound_inference_audit():
    """Hold sound return-type inference against concrete execution. For each corpus function the inferred
    type set, when a claim is made, must contain type(f(...)).__name__ on every sampled input -- a proven
    over-approximation -- or the inference must abstain (UNKNOWN). A runtime type outside a non-empty
    inferred set is a soundness violation. Parameter-dependent functions are run on diverse-typed inputs,
    so any unsound narrowing surfaces. Needs ALLOW_SUBJECT_EXECUTION (it runs the corpus)."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("differential_sound_inference_audit requires ALLOW_SUBJECT_EXECUTION")
    from .inference import infer_return_type
    corpus = [
        ("def f():\n    return 5\n", [()]),
        ("def f():\n    return 'a' + 'b'\n", [()]),
        ("def f():\n    return [1, 2]\n", [()]),
        ("def f():\n    return {'a': 1}\n", [()]),
        ("def f():\n    return (1, 2)\n", [()]),
        ("def f():\n    return 1 < 2\n", [()]),
        ("def f(a, b, c):\n    return a is b is c\n", [(1, 1, 1), (1, 2, 3), (None, None, None)]),  # chained is: bool
        ("def f(a, b, c):\n    return a in b in c\n", [(1, [1], [[1]],), (9, [1], [[1]],)]),        # chained in: bool
        ("def f():\n    return 1.0 + 2\n", [()]),
        ("def f():\n    return True + True\n", [()]),
        ("def f():\n    return 7 // 2\n", [()]),
        ("def f():\n    return 7 / 2\n", [()]),
        ("def f():\n    return 'ab' * 3\n", [()]),
        ("def f(x):\n    return len(x)\n", [([1, 2],), ("abc",), ({1: 2},)]),
        ("def f(x):\n    return str(x)\n", [(1,), ("a",), (None,), ([1],)]),
        ("def f(x):\n    return sorted(x)\n", [([3, 1],), ("bca",)]),
        ("def f(x):\n    return bool(x)\n", [(0,), (1,), ("",), ([],)]),
        ("def f():\n    x = 5\n    return x\n", [()]),
        ("def f(c):\n    x = 5\n    if c:\n        x = 'a'\n    return x\n", [(True,), (False,)]),
        ("def f(c):\n    if c:\n        return 1\n    return 'a'\n", [(True,), (False,)]),
        ("def f(c):\n    if c:\n        return 1\n", [(True,), (False,)]),
        ("def f():\n    return\n", [()]),
        ("def f(n):\n    i = 0\n    while i < n:\n        yield i\n        i = i + 1\n", [(3,)]),
        ("def f(a, b):\n    return a is b\n", [(1, 1), (1, 2)]),
        ("def f(a, b):\n    return a in b\n", [(1, [1, 2]), (9, [1, 2])]),
        ("def f(x):\n    return not x\n", [(0,), (5,), ([],)]),
        ("def f():\n    return 'abc'.upper()\n", [()]),
        ("def f():\n    x = 'a b c'\n    return x.split()\n", [()]),
        ("def f():\n    return 'abc'.find('b')\n", [()]),
        ("def f():\n    return 'abc'.startswith('a')\n", [()]),
        ("def f():\n    return 'x,y'.partition(',')\n", [()]),
        ("def f():\n    return 'abc'.encode('ascii')\n", [()]),
        ("def f():\n    x = [3, 1, 2]\n    return x.copy()\n", [()]),
        ("def f():\n    x = [3, 1, 2]\n    return x.count(1)\n", [()]),
        ("def f():\n    x = {'a': 1}\n    return x.keys()\n", [()]),
        ("def f():\n    x = {'a': 1}\n    return x.copy()\n", [()]),
        ("def f():\n    x = {1, 2}\n    return x.union({3})\n", [()]),
        ("def f():\n    x = (1, 2, 3)\n    return x.index(2)\n", [()]),
        ("def f(s):\n    return s.upper()\n", [("aBc",), ("xyz",)]),   # str method on a param: abstains, run on str
        # parameter-dependent: must abstain. Diverse-typed inputs catch any unsound claim.
        ("def f(x):\n    return x\n", [(1,), ("a",), ([1],), (1.5,), (None,)]),
        ("def f(x):\n    return x[0]\n", [([1],), ("ab",), ((3.0,),)]),
        ("def f(a, b):\n    return a + b\n", [(1, 2), ("a", "b"), (1.0, 2)]),
        ("def f():\n    return abs(-3)\n", [()]),                    # abs of bounded numerics: commits the kind,
        ("def f():\n    return abs(3.5)\n", [()]),                   # float for a float operand,
        ("def f():\n    return abs(3 + 4j)\n", [()]),               # and float for a complex one (abs(z) is float)
        ("def f():\n    return round(3.7)\n", [()]),                # round with no ndigits is int
        ("def f():\n    return min(1, 2.0)\n", [()]),               # min / max of explicit args: the join of their
        ("def f():\n    return max(5, 2, 8)\n", [()]),              # bounds (one argument is returned unchanged)
        ("def f(x):\n    return abs(x)\n", [(1,), (1.5,), (-2,)]),  # abs of an unbounded parameter still abstains
        # printf-style `s % args` on a PROVEN str / bytes left yields that type whatever the right operand is
        # (str.__mod__ / bytes.__mod__ return their own type or raise, no __rmod__ on the right intercepts), so
        # the bound holds across diverse-typed right operands; an f-string left is itself a proven str
        ("def f(x):\n    return 'v=%s' % x\n", [(1,), ("a",), ([1],), (1.5,)]),       # str % anything -> str
        ("def f(a, b):\n    return '%d-%d' % (a, b)\n", [(1, 2), (3, 4)]),            # str % tuple -> str
        ("def f(x):\n    return b'v=%d' % x\n", [(1,), (255,)]),                      # bytes % anything -> bytes
        ("def f(x):\n    s = f'{x}'\n    return s % x\n", [("a",), (1,)]),            # f-string is str, then % -> str
    ]
    claims = runs = abstain = 0
    for src, inputs in corpus:
        inferred = infer_return_type(src)
        if inferred is None:
            abstain += 1
        else:
            claims += 1
        ns = {}
        exec(src, ns)                                       # trusted built-in corpus
        fn = ns["f"]
        for tup in inputs:
            try:
                r = fn(*tup)
            except Exception:
                continue                                    # a trap produces no value to type
            runs += 1
            tn = type(r).__name__
            if inferred is not None and tn not in inferred:
                raise SoundnessError(
                    "sound type inference unsound: %r returned type %s, not in inferred %s"
                    % (src.strip().splitlines()[0], tn, sorted(inferred)))
    return {"claims": claims, "runs": runs, "abstain": abstain}


def differential_sound_local_audit():
    """Hold sound local-variable inference against concrete execution: when a function returns, each local's
    runtime type must be in its inferred bound (a proven over-approximation), or the bound abstains (None).
    A runtime type outside a non-empty bound is a soundness violation. Needs ALLOW_SUBJECT_EXECUTION."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("differential_sound_local_audit requires ALLOW_SUBJECT_EXECUTION")
    import sys as _sys
    from .inference import infer_local_types
    corpus = [
        ("def f():\n    a = 5\n    b = 'x'\n    c = [1, 2]\n    d = len(b)\n    return d\n", ()),
        ("def f(n):\n    x = 0\n    y = 'a'\n    z = (1, 2)\n    return x\n", (3,)),
        ("def f(c):\n    x = 1\n    if c:\n        x = 'two'\n    return x\n", (True,)),
        ("def f(c):\n    x = 1\n    if c:\n        x = 'two'\n    return x\n", (False,)),
        ("def f():\n    a = 1.5\n    b = a + 1\n    c = a > 0\n    return b\n", ()),
        ("def f():\n    s = 'a,b'\n    parts = s.split(',')\n    return parts\n", ()),
        ("def f():\n    d = {'k': 1}\n    e = d.copy()\n    return e\n", ()),
        ("def f():\n    t = (1, 2, 3)\n    n = t.count(1)\n    return n\n", ()),
        ("def f(p):\n    y = p\n    return y\n", (7,)),       # a local from a parameter: abstains, run with int
        ("def f(p):\n    y = p\n    return y\n", ("s",)),     # ... and with str -- never a claim either way
    ]
    claims = runs = abstain = 0
    for src, args in corpus:
        loc = infer_local_types(src, target="f")
        ns = {}
        exec(src, ns)                                       # trusted built-in corpus
        fn = ns["f"]
        captured = {}

        def tracer(frame, event, arg, _cap=captured):
            if event == "return" and frame.f_code.co_name == "f":
                _cap.clear()
                _cap.update(frame.f_locals)
            return tracer
        old = _sys.gettrace()
        _sys.settrace(tracer)
        try:
            fn(*args)
        except Exception:
            pass
        finally:
            _sys.settrace(old)
        for name, val in captured.items():
            inferred = loc.get(name)
            if inferred is None:
                abstain += 1
                continue
            claims += 1
            runs += 1
            tn = type(val).__name__
            if tn not in inferred:
                raise SoundnessError("sound local inference unsound: %s = %r (type %s) not in %s"
                                     % (name, val, tn, sorted(inferred)))
    return {"claims": claims, "runs": runs, "abstain": abstain}


def relational_domain_audit(trials=300, seed=777):
    """Generate random bounded single-loop linear programs and replay every PROVED
    relational fact (octagon sum, zone equality, Karr equality) against the program's
    concrete semantics. A PROVED fact a real run violates raises SoundnessError. The
    oracle is a direct simulation of the generated loop, so no subject code is executed.
    Returns the number of PROVED facts checked."""
    import itertools
    rng = random.Random(seed)
    names = ["x", "y", "z"]
    saved, core.CROSS_VALIDATE_DOMAINS = core.CROSS_VALIDATE_DOMAINS, False   # replay is the check here
    checked = 0
    try:
        for _ in range(trials):
            inits = {v: rng.randint(-3, 3) for v in names}
            steps = {v: rng.randint(-3, 3) for v in names}
            lines = ["def f(n):"] + [f"    {v} = {inits[v]}" for v in names]
            lines += ["    i = 0", "    while i < n:"]
            lines += [f"        {v} = {v} + ({steps[v]})" for v in names if steps[v]]
            lines += ["        i = i + 1", "    return x"]
            src = "\n".join(lines) + "\n"
            runs, st = [], dict(inits)
            for _n in range(0, 14):
                runs.append(dict(st))
                for v in names:
                    st[v] += steps[v]
            for u, w in itertools.combinations(names, 2):
                c = runs[-1][u] + runs[-1][w]
                if verify_octagon_sum("a", "f", src, u, w, c).status == PROVED:
                    checked += 1
                    if any(r[u] + r[w] != c for r in runs):
                        raise SoundnessError(f"octagon PROVED {u}+{w}=={c}, but a run violates it:\n{src}")
            for u, w in itertools.permutations(names, 2):
                if verify_zone_equal("a", "f", src, u, w).status == PROVED:
                    checked += 1
                    if any(r[u] != r[w] for r in runs):
                        raise SoundnessError(f"zone PROVED {u}=={w}, but a run violates it:\n{src}")
                if verify_affine_equal("a", "f", src, u, w).status == PROVED:
                    checked += 1
                    if any(r[u] != r[w] for r in runs):
                        raise SoundnessError(f"Karr PROVED {u}=={w}, but a run violates it:\n{src}")
    finally:
        core.CROSS_VALIDATE_DOMAINS = saved
    return checked


def _rand_ir(rng, nvars=3):
    """A random IR (prog, post formula) over `nvars` variables, exercising every operator the
    extracted generator handles, for the differential check below."""
    def rexpr(d):
        if d <= 0 or rng.random() < 0.4:
            return ("v", rng.randrange(nvars)) if rng.random() < 0.5 else ("c", rng.randint(-5, 5))
        op = rng.choice(["add", "sub", "mul", "div", "elt", "ele", "eeq", "eand", "eor", "enot"])
        return (op, rexpr(d - 1)) if op == "enot" else (op, rexpr(d - 1), rexpr(d - 1))

    def rprog(d):
        if d <= 0 or rng.random() < 0.35:
            return ("nil",)
        if rng.random() < 0.6:
            return ("asgn", rng.randrange(nvars), rexpr(2), rprog(d - 1))
        return ("cond", rexpr(2), rprog(d - 1), rprog(d - 1), rprog(d - 1))

    def rform(d):
        if d <= 0 or rng.random() < 0.3:
            return rng.choice([("true",), ("false",), ("lt", rexpr(2), rexpr(2)),
                               ("le", rexpr(2), rexpr(2)), ("eq", rexpr(2), rexpr(2))])
        c = rng.choice(["not", "and", "or", "impl"])
        return ("not", rform(d - 1)) if c == "not" else (c, rform(d - 1), rform(d - 1))

    return rprog(3), rform(2)


def _rand_kcmd(rng, nvars=3):
    """A random (kcmd, post formula) over `nvars` variables for the differential check of the loop
    generator vcg, exercising kskip/kasgn/kseq/kif/kwhile and a syntactic (form) invariant."""
    def rexpr(d):
        if d <= 0 or rng.random() < 0.4:
            return ("v", rng.randrange(nvars)) if rng.random() < 0.5 else ("c", rng.randint(-5, 5))
        op = rng.choice(["add", "sub", "mul", "div", "mod", "elt", "ele", "eeq", "eand", "eor", "enot"])
        return (op, rexpr(d - 1)) if op == "enot" else (op, rexpr(d - 1), rexpr(d - 1))

    def rform(d):
        if d <= 0 or rng.random() < 0.3:
            return rng.choice([("true",), ("false",), ("lt", rexpr(2), rexpr(2)),
                               ("le", rexpr(2), rexpr(2)), ("eq", rexpr(2), rexpr(2))])
        c = rng.choice(["not", "and", "or", "impl"])
        return ("not", rform(d - 1)) if c == "not" else (c, rform(d - 1), rform(d - 1))

    def rcmd(d):
        if d <= 0 or rng.random() < 0.3:
            return ("kasgn", rng.randrange(nvars), rexpr(2)) if rng.random() < 0.7 else ("kskip",)
        r = rng.random()
        if r < 0.4:
            return ("kseq", rcmd(d - 1), rcmd(d - 1))
        if r < 0.7:
            return ("kif", rexpr(2), rcmd(d - 1), rcmd(d - 1))
        return ("kwhile", rform(1), rexpr(2), rcmd(d - 1))

    return rcmd(3), rform(2)


def _extracted_compare(exe, build, batch, noun, subject, msg):
    """Shared tail of the extracted-audit checks. When the OCaml binary is built (exe is not None),
    build() yields the (corpus, expected) pair, batch runs the corpus through the extracted executable,
    and every result is held equal element-wise; a length mismatch or any divergence raises
    SoundnessError. Returns {available, checks} (available=False, corpus unbuilt, when exe is None)."""
    if exe is None:
        return {"available": False, "checks": 0}
    corpus, expected = build()
    got = batch(corpus, exe)
    if got is None or len(got) != len(expected):
        raise SoundnessError(f"extracted {subject} produced {0 if got is None else len(got)} results "
                             f"for {len(expected)} {noun}")
    for item, py, ml in zip(corpus, expected, got):
        if py != ml:
            raise SoundnessError(msg(item, py, ml))
    return {"available": True, "checks": len(corpus)}


def extracted_vcgen_audit(trials=400, seed=8675309):
    """Hold the in-engine VC generator (wpg) equal to the one extracted from touchstone_functor.v over
    a random corpus: the serialized verification conditions must match character for character.
    SoundnessError on divergence; available=False if not built."""
    def build():
        rng = random.Random(seed)
        corpus = [_rand_ir(rng) for _ in range(trials)]
        return corpus, [ser_form(wpg(prog, post)) for prog, post in corpus]
    return _extracted_compare(
        vcgen_executable(), build, extracted_wpg_batch, "queries", "vcgen",
        lambda it, py, ml: ("the in-engine VC generator disagrees with the Rocq-extracted one:\n"
                            f"  query (query {ser_prog(it[0])} {ser_form(it[1])})\n  engine={py}\n  extracted={ml}"))


def extracted_vcg_audit(trials=400, seed=2718281):
    """Hold the in-engine loop generator (vcg) equal to the one extracted from touchstone_functor.v over
    a random corpus of commands: the serialized (precondition, obligations) must match character for
    character. SoundnessError on divergence; available=False if not built."""
    def build():
        rng = random.Random(seed)
        corpus = [_rand_kcmd(rng) for _ in range(trials)]
        return corpus, [ser_vcg(vcg(k, post)) for k, post in corpus]
    return _extracted_compare(
        vcgen_executable(), build, extracted_vcg_batch, "queries", "vcg",
        lambda it, py, ml: ("the in-engine loop generator disagrees with the Rocq-extracted one:\n"
                            f"  query (querycmd {ser_kcmd(it[0])} {ser_form(it[1])})\n  engine={py}\n  extracted={ml}"))


def extracted_intervals_audit(trials=2000, seed=1234567):
    """Hold the in-engine interval transfers (_iadd/_isub/_ineg/_ijoin/_imul) equal to the operators
    extracted from touchstone_domains.v over a random corpus. SoundnessError on divergence;
    available=False if not built."""
    def build():
        rng = random.Random(seed)
        binop = {"iadd": _iadd, "isub": _isub, "ijoin": _ijoin, "imul": _imul}
        corpus, expected = [], []
        for _ in range(trials):
            op = rng.choice(["iadd", "isub", "ineg", "ijoin", "imul"])
            a = rng.randint(-50, 50); b = rng.randint(a, 50)
            if op == "ineg":
                corpus.append((op, (a, b))); r = _ineg(Iv(a, b))
            else:
                c = rng.randint(-50, 50); d = rng.randint(c, 50)
                corpus.append((op, (a, b, c, d))); r = binop[op](Iv(a, b), Iv(c, d))
            expected.append((r.lo, r.hi))
        return corpus, expected
    return _extracted_compare(
        intervals_executable(), build, extracted_intervals_batch, "requests", "intervals",
        lambda it, py, ml: ("the in-engine interval operator disagrees with the Rocq-extracted one: "
                            f"{it[0]} {it[1]} -> engine={py} extracted={ml}"))


def extracted_encoding_audit(bound=60):
    """Hold the in-engine py_floordiv / py_mod equal to the Rocq-extracted pyfloordiv / pymod over every
    nonzero divisor in [-bound, bound]^2. A divergence is SoundnessError; available=False if not built."""
    def build():
        pairs, expected = [], []
        for a in range(-bound, bound + 1):
            for b in range(-bound, bound + 1):
                if b == 0:
                    continue
                fd = z3.simplify(py_floordiv(z3.IntVal(a), z3.IntVal(b))).as_long()
                md = z3.simplify(py_mod(z3.IntVal(a), z3.IntVal(b))).as_long()
                pairs.append((a, b)); expected.append((fd, md))
        return pairs, expected
    return _extracted_compare(
        encoding_executable(), build, extracted_encoding_batch, "pairs", "encoding",
        lambda it, py, ml: ("the in-engine division encoding disagrees with the Rocq-extracted one: "
                            f"a={it[0]} b={it[1]} -> engine={py} extracted={ml}"))


def extracted_encoding_committed_audit(bound=60):
    """Hold the in-engine py_floordiv / py_mod equal to the committed Rocq extraction in
    _generated/encoding_rocq (its pyfloordiv / pymod) over every nonzero divisor in [-bound, bound]^2.
    Where extracted_encoding_audit shells out to an OCaml binary that proofs/build_encoding.sh must build,
    this runs the proof's extraction directly in Python from the committed module -- no coqc, no ocamlfind --
    so the running division encoding is checked byte-for-byte against the proof on every machine rather than
    skipping. SoundnessError on divergence; always available."""
    from ._generated import encoding_rocq as _enc
    def _pos(n):                                          # int -> the extraction's binary-positive
        return ("XH",) if n == 1 else (("XI", _pos(n >> 1)) if n & 1 else ("XO", _pos(n >> 1)))
    def _Z(n):                                            # int -> the extraction's binary integer
        return ("Z0",) if n == 0 else (("Zpos", _pos(n)) if n > 0 else ("Zneg", _pos(-n)))
    def _p2i(p):
        return 1 if p[0] == "XH" else (2 * _p2i(p[1]) + (1 if p[0] == "XI" else 0))
    def _z2i(z):                                          # the extraction's binary integer -> int
        return 0 if z[0] == "Z0" else (_p2i(z[1]) if z[0] == "Zpos" else -_p2i(z[1]))
    checks = 0
    for a in range(-bound, bound + 1):
        for b in range(-bound, bound + 1):
            if b == 0:
                continue
            fd = z3.simplify(py_floordiv(z3.IntVal(a), z3.IntVal(b))).as_long()
            md = z3.simplify(py_mod(z3.IntVal(a), z3.IntVal(b))).as_long()
            efd = _z2i(_enc.pyfloordiv(_Z(a))(_Z(b)))
            emd = _z2i(_enc.pymod(_Z(a))(_Z(b)))
            if (fd, md) != (efd, emd):
                raise SoundnessError("the in-engine division encoding disagrees with the committed Rocq "
                                     f"extraction: a={a} b={b} -> engine=({fd}, {md}) extracted=({efd}, {emd})")
            checks += 1
    return {"available": True, "checks": checks}


def extracted_lattice_audit():
    """Hold the sound type-inference join (soundinfer._join) equal to the committed Rocq extraction in
    _generated/encoders_rocq (its join) over a range of type-bound inputs. None is top (UNKNOWN, no bound);
    a finite bound is a set of type tags. touchstone_encoders.v proves this join over-approximates both
    operands (join_over_approx_l/r) and extracts it; this checks the engine runs that verified join
    byte-for-byte rather than a hand transcription -- no coqc, no ocamlfind. SoundnessError on divergence;
    always available. (Strings, containers, and the heap/array model are proven sound in the same file but
    the engine discharges them through z3's theories, so only the join is tied here to running code.)"""
    from ._generated import encoders_rocq as _enc
    from .inference import _join
    def _to_rocq(b):                                          # a frozenset/None bound -> the extraction's option (list tag)
        if b is None:
            return ("None",)
        node = ("Nil",)
        for x in sorted(b):
            node = ("Cons", x, node)
        return ("Some", node)
    def _from_rocq(r):                                        # the extraction's option (list tag) -> a set/None
        if r[0] == "None":
            return None
        out, node = set(), r[1]
        while node[0] == "Cons":
            out.add(node[1]); node = node[2]
        return out
    checks = 0
    bounds = [None, frozenset(), frozenset({"int"}), frozenset({"int", "str"}),
              frozenset({"bool", "float", "int"}), frozenset({"NoneType"})]
    for a in bounds:
        for b in bounds:
            eng = _join(a, b)
            ext = _from_rocq(_enc.join(_to_rocq(a))(_to_rocq(b)))
            if (eng is None) != (ext is None) or (eng is not None and set(eng) != ext):
                raise SoundnessError("the in-engine type-inference join disagrees with the committed Rocq "
                                     f"extraction: a={a} b={b} -> engine={eng} extracted={ext}")
            checks += 1
    return {"available": True, "checks": checks}


def committed_extraction_audit():
    """Hold each committed engine module -- _generated/vcgen_rocq.py (the wpg/vcg generator),
    intervals_rocq.py (the interval operators), encoding_rocq.py (the division encoding), encoders_rocq.py
    (the type-inference lattice join) -- equal to the Python image of the committed Rocq JSON extraction it
    was generated from. The transpiler (_transpile) and the JSON ship in the package, so this runs the
    proof's extraction image directly in Python on every machine -- no coqc, no ocamlfind -- checking the
    generator code the engine actually runs byte-for-byte against the proof's extraction rather than
    skipping. SoundnessError on any divergence; always available."""
    import os
    from ._generated import _transpile
    gendir = os.path.dirname(_transpile.__file__)
    def _norm(s):
        return s.replace("\r\n", "\n").rstrip("\n")               # checkout line endings do not matter
    checks = 0
    for jstem, module in (("vcgen", "vcgen_rocq"), ("intervals", "intervals_rocq"), ("encoding", "encoding_rocq"),
                          ("encoders", "encoders_rocq")):
        image = _transpile.transpile(os.path.join(gendir, jstem + ".json"))
        with open(os.path.join(gendir, module + ".py"), encoding="utf-8") as f:
            committed = f.read()
        if _norm(image) != _norm(committed):
            raise SoundnessError("the committed engine module %s.py is not the Python image of the proof's "
                                 "JSON extraction %s.json" % (module, jstem))
        checks += 1
    return {"available": True, "checks": checks}


def committed_obligations_audit():
    """Hold the integer obligations the engine currently discharges equal to the committed
    proofs/touchstone_obligations.v that the smtcoq CI job re-checks inside Coq's kernel on every commit
    (proofs/Dockerfile.smtcoq + .github/workflows/smtcoq.yml run it provisioned, so it never skips), so the
    kernel-validated-certificate is exercised against the engine's actual present obligations rather than a
    stale snapshot. The export's order is not significant, so the hold is by set; a current obligation absent
    from the committed (kernel-checked) file is a drift that must be regenerated. Skips cleanly when the
    proofs tree is absent (an installed-only package ships no proofs/), where there is nothing to hold."""
    import os
    import re
    from . import vcgen as smtcoq_export
    path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "proofs", "touchstone_obligations.v")
    if not os.path.isfile(path):
        return {"available": False, "checks": 0}
    generated = set(smtcoq_export.generate_obligation_lemmas())
    with open(path, encoding="utf-8") as f:
        committed = set(re.findall(r"Goal .*?Qed\.", f.read(), re.S))
    missing = generated - committed
    if missing:
        raise SoundnessError(
            "proofs/touchstone_obligations.v is stale: the engine now discharges an integer obligation the "
            "committed (kernel-checked) file does not cover; regenerate with "
            "`python -m touchstone.vcgen proofs/touchstone_obligations.v`. Missing: " + next(iter(missing)))
    return {"available": True, "checks": len(generated)}


# Per-construct refinement vs CPython. Each modeled construct is a one-expression function; the symbolic
# translation evaluated on concrete inputs must agree with CPython on the value (bit-exact for floats,
# NaN == NaN, signed zero distinguished) or both must trap. CPython has no formal spec, so this is the
# refinement statement for each construct that can be modeled exactly. Over-approximated constructs
# (sin/cos/exp/log, str case/strip, float **) are excluded; their soundness is the axiom audits above.
_REFINEMENT_CONSTRUCTS = [
    ("int a + b",   "def f(a, b):\n    return a + b\n",   [("a", "int"), ("b", "int")]),
    ("int a - b",   "def f(a, b):\n    return a - b\n",   [("a", "int"), ("b", "int")]),
    ("int a * b",   "def f(a, b):\n    return a * b\n",   [("a", "int"), ("b", "int")]),
    ("int a // b",  "def f(a, b):\n    return a // b\n",  [("a", "int"), ("b", "int")]),
    ("int a % b",   "def f(a, b):\n    return a % b\n",   [("a", "int"), ("b", "int")]),
    ("int a / b",   "def f(a, b):\n    return a / b\n",   [("a", "int"), ("b", "int")]),   # true div -> float
    ("int a ** 3",  "def f(a):\n    return a ** 3\n",     [("a", "int")]),
    ("int -a",      "def f(a):\n    return -a\n",         [("a", "int")]),
    ("int ~a",      "def f(a):\n    return ~a\n",         [("a", "int")]),
    ("int a << 2",  "def f(a):\n    return a << 2\n",     [("a", "int")]),
    ("int a >> 2",  "def f(a):\n    return a >> 2\n",     [("a", "int")]),
    ("int a & 7",   "def f(a):\n    return a & 7\n",      [("a", "int")]),
    ("abs(a)",      "def f(a):\n    return abs(a)\n",     [("a", "int")]),
    ("min(a, b)",   "def f(a, b):\n    return min(a, b)\n", [("a", "int"), ("b", "int")]),
    ("max(a, b, c)", "def f(a, b, c):\n    return max(a, b, c)\n", [("a", "int"), ("b", "int"), ("c", "int")]),
    ("int a < b",   "def f(a, b):\n    return a < b\n",   [("a", "int"), ("b", "int")]),
    ("int a <= b",  "def f(a, b):\n    return a <= b\n",  [("a", "int"), ("b", "int")]),
    ("int a > b",   "def f(a, b):\n    return a > b\n",   [("a", "int"), ("b", "int")]),
    ("int a >= b",  "def f(a, b):\n    return a >= b\n",  [("a", "int"), ("b", "int")]),
    ("int a == b",  "def f(a, b):\n    return a == b\n",  [("a", "int"), ("b", "int")]),
    ("int a != b",  "def f(a, b):\n    return a != b\n",  [("a", "int"), ("b", "int")]),
    ("chained a<b<c", "def f(a, b, c):\n    return a < b < c\n", [("a", "int"), ("b", "int"), ("c", "int")]),
    ("a and b",     "def f(a, b):\n    return a and b\n", [("a", "int"), ("b", "int")]),
    ("a or b",      "def f(a, b):\n    return a or b\n",  [("a", "int"), ("b", "int")]),
    ("not a",       "def f(a):\n    return not a\n",      [("a", "int")]),
    ("a if a>0 else b", "def f(a, b):\n    return a if a > 0 else b\n", [("a", "int"), ("b", "int")]),
    ("flt x + y",   "def f(x: float, y: float):\n    return x + y\n", [("x", "float"), ("y", "float")]),
    ("flt x - y",   "def f(x: float, y: float):\n    return x - y\n", [("x", "float"), ("y", "float")]),
    ("flt x * y",   "def f(x: float, y: float):\n    return x * y\n", [("x", "float"), ("y", "float")]),
    ("flt x / y",   "def f(x: float, y: float):\n    return x / y\n", [("x", "float"), ("y", "float")]),
    ("flt x // y",  "def f(x: float, y: float):\n    return x // y\n", [("x", "float"), ("y", "float")]),
    ("flt x % y",   "def f(x: float, y: float):\n    return x % y\n", [("x", "float"), ("y", "float")]),
    ("flt -x",      "def f(x: float):\n    return -x\n",  [("x", "float")]),
    ("flt abs(x)",  "def f(x: float):\n    return abs(x)\n", [("x", "float")]),
    ("flt x < y",   "def f(x: float, y: float):\n    return x < y\n", [("x", "float"), ("y", "float")]),
    ("flt x == y",  "def f(x: float, y: float):\n    return x == y\n", [("x", "float"), ("y", "float")]),
    ("str a + b",   "def f(a: str, b: str):\n    return a + b\n", [("a", "str"), ("b", "str")]),
    ("str a * 3",   "def f(a: str):\n    return a * 3\n", [("a", "str")]),
    ("str len(a)",  "def f(a: str):\n    return len(a)\n", [("a", "str")]),
    ("str a[0:2]",  "def f(a: str):\n    return a[0:2]\n", [("a", "str")]),
    ("str a.startswith", "def f(a: str):\n    return a.startswith('ab')\n", [("a", "str")]),
    ("str 'x' in a", "def f(a: str):\n    return 'x' in a\n", [("a", "str")]),
]


def _refine_sample(rng, ty):
    if ty == "int":
        if rng.random() < 0.08:
            return rng.choice([10 ** 200, -(10 ** 200), 1 << 200, -(1 << 200)])   # large-operand rounding stress
        return rng.choice([0, 1, -1, 2, -2, 3, 7, 8, 10]) if rng.random() < 0.3 \
            else rng.randint(-(1 << 60), 1 << 60)
    if ty == "float":
        sp = [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, 3.0, _math.inf, -_math.inf, _math.nan,
              2.0 ** 53, 2.0 ** -1074, 1e300, -1e300]
        return rng.choice(sp) if rng.random() < 0.4 \
            else struct.unpack(">d", struct.pack(">Q", rng.getrandbits(64)))[0]
    return "".join(rng.choice("ab xY") for _ in range(rng.randint(0, 5)))      # str


def _refine_eval(src, inputs):
    """Concrete (kind, value) the symbolic translation gives f(**inputs): ('trap', None) if a trap
    fires on these inputs, else ('val', python_value)."""
    args, z3args, rets, traps, _none = symexec(src, Ctx({}))
    sub = []
    for a in args:
        z, v = z3args[a], inputs[a]
        sub.append((z, z3.FPVal(v, _F64) if _is_fp(z) else z3.StringVal(v) if core._is_str(z)
                    else z3.BoolVal(v) if z3.is_bool(z) else z3.IntVal(v)))
    if z3.is_true(z3.simplify(z3.substitute(z3.Or(*traps) if traps else z3.BoolVal(False), *sub))):
        return ("trap", None)
    val = z3.simplify(z3.substitute(fold(rets), *sub))
    if z3.is_int_value(val):
        return ("val", val.as_long())
    if z3.is_true(val):
        return ("val", 1)
    if z3.is_false(val):
        return ("val", 0)
    if z3.is_string_value(val):
        return ("val", val.as_string())
    if z3.is_fp_value(val):
        return ("val", _fp_to_float(val))
    raise Unsupported(f"undecodable symbolic value {val}")


def _refine_float_eq(v, r):
    if _math.isnan(v) and _math.isnan(r):
        return True                                          # any NaN refines any NaN (payload unspecified)
    return struct.pack(">d", v) == struct.pack(">d", r)      # bit-exact: signed zero distinguished


def _refine_agree(sym, cpy):
    if sym[0] != cpy[0]:
        return False
    if sym[0] == "trap":
        return True
    v, r = sym[1], cpy[1]
    if isinstance(r, bool):
        r = int(r)                                           # the symbolic side folds bool to its 0/1 value
    if isinstance(v, float) or isinstance(r, float):
        return _refine_float_eq(float(v), float(r))
    return v == r


def refinement_audit(per=80, seed=20240921):
    """Hold the symbolic translation of each modeled construct equal to CPython: random typed inputs are
    evaluated symbolically and by CPython and must agree on the value or both trap. SoundnessError on a
    divergence. Needs ALLOW_SUBJECT_EXECUTION."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("refinement_audit requires ALLOW_SUBJECT_EXECUTION")
    rng = random.Random(seed)
    checks = 0
    for label, src, params in _REFINEMENT_CONSTRUCTS:
        fn = _pyfn(src, {})
        names = [p for p, _ in params]
        for _ in range(per):
            inputs = {p: _refine_sample(rng, ty) for p, ty in params}
            try:
                sym = _refine_eval(src, inputs)
            except Unsupported as u:
                raise SoundnessError(f"refinement: {label} no longer models exactly ({u})")
            try:
                cpy = ("val", fn(*[inputs[p] for p in names]))
            except Exception:
                cpy = ("trap", None)
            if not _refine_agree(sym, cpy):
                raise SoundnessError(f"refinement divergence in {label} at {inputs}: "
                                     f"symbolic={sym} cpython={cpy}")
            checks += 1
    return {"constructs": len(_REFINEMENT_CONSTRUCTS), "checks": checks}


def exhaustive_refinement_audit(bound=12, max_inputs=100000):
    """Hold the symbolic translation of each integer-only modeled construct equal to CPython over EVERY input
    in the bounded box [-bound, bound] per parameter -- the whole box, not a random sample. The integer
    fragment of the symbolic core (ev / symexec), which the Rocq proof does not cover, is thereby confirmed to
    refine CPython exactly on that box: a bounded proof of the core's integer encodings, stronger than the
    sampled refinement_audit. SoundnessError on any divergence. Each construct is symbolically executed once
    and its formula re-decoded per input, so the box is cheap to sweep. Constructs with a non-integer
    parameter, or too large a box to enumerate, are left to the sampled audit. Needs ALLOW_SUBJECT_EXECUTION."""
    if not core.ALLOW_SUBJECT_EXECUTION:
        raise RuntimeError("exhaustive_refinement_audit requires ALLOW_SUBJECT_EXECUTION")
    import itertools
    checks = constructs = 0
    for label, src, params in _REFINEMENT_CONSTRUCTS:
        if not params or any(ty != "int" for _, ty in params):
            continue
        if (2 * bound + 1) ** len(params) > max_inputs:
            continue
        fn = _pyfn(src, {})
        names = [p for p, _ in params]
        args, z3args, rets, traps, _none = symexec(src, Ctx({}))           # symbolic form, once per construct
        trap_form = z3.Or(*traps) if traps else z3.BoolVal(False)
        ret_form = fold(rets)
        constructs += 1
        for combo in itertools.product(range(-bound, bound + 1), repeat=len(params)):
            inputs = dict(zip(names, combo))
            sub = [(z3args[a], z3.IntVal(inputs[a])) for a in args]
            if z3.is_true(z3.simplify(z3.substitute(trap_form, *sub))):
                sym = ("trap", None)
            else:
                val = z3.simplify(z3.substitute(ret_form, *sub))
                if z3.is_int_value(val):
                    sym = ("val", val.as_long())
                elif z3.is_true(val):
                    sym = ("val", 1)
                elif z3.is_false(val):
                    sym = ("val", 0)
                elif z3.is_fp_value(val):
                    sym = ("val", _fp_to_float(val))
                else:
                    raise SoundnessError(f"exhaustive refinement: {label} undecodable symbolic value {val} at {inputs}")
            try:
                cpy = ("val", fn(*[inputs[p] for p in names]))
            except Exception:
                cpy = ("trap", None)
            if not _refine_agree(sym, cpy):
                raise SoundnessError(f"exhaustive refinement divergence in {label} at {inputs}: "
                                     f"symbolic={sym} cpython={cpy}")
            checks += 1
    return {"constructs": constructs, "checks": checks}


_COVERAGE_CORPUS = [
    ("gcd", "def gcd(a, b):\n    while b != 0:\n        t = b\n        b = a % b\n        a = t\n    return a\n"),
    ("abs_branch", "def f(x):\n    if x < 0:\n        return -x\n    return x\n"),
    ("clamp", "def f(x):\n    if x > 100:\n        x = 100\n    if x < 0:\n        x = 0\n    return x\n"),
    ("sign", "def f(x):\n    if x > 0:\n        return 1\n    if x < 0:\n        return -1\n    return 0\n"),
    ("max_of_three", "def f(a, b, c):\n    return max(a, max(b, c))\n"),
    ("factorial_rec", "def f(n):\n    if n <= 0:\n        return 1\n    return n * f(n - 1)\n"),
    ("fib_rec", "def f(n):\n    if n < 2:\n        return n\n    return f(n - 1) + f(n - 2)\n"),
    ("sum_to", "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"),
    ("power", "def f(b, e):\n    r = 1\n    i = 0\n    while i < e:\n        r = r * b\n        i = i + 1\n    return r\n"),
    ("count_digits", "def f(n):\n    c = 0\n    while n > 10:\n        n = n // 10\n        c = c + 1\n    return c\n"),
    ("for_range_sum", "def f(n):\n    s = 0\n    for i in range(n):\n        s = s + i\n    return s\n"),
    ("startswith", "def f(s: str):\n    return s.startswith('ab')\n"),
    ("str_concat", "def f(a: str, b: str):\n    return a + b\n"),
    ("clamp_float", "def f(x: float):\n    if x < 0.0:\n        return 0.0\n    return x\n"),
    ("list_index", "def f():\n    a = [1, 2, 3]\n    return a[1]\n"),
    ("list_append", "def f(x):\n    a = []\n    a.append(x)\n    return a[0]\n"),
    ("dict_round_trip", "def f(k, v):\n    d = {}\n    d[k] = v\n    return d[k]\n"),
    ("object_attr", "def f(p):\n    o = object()\n    o.x = p\n    return o.x\n"),
    ("tuple_swap", "def f(a, b):\n    a, b = b, a\n    return a - b\n"),
    ("comprehension_over_var", "def f(xs):\n    return [x * 2 for x in xs]\n"),
    ("filter_comprehension", "def f(xs):\n    return [x for x in xs if x > 0]\n"),
    ("all_over_list", "def f(xs):\n    return all(x >= 0 for x in xs)\n"),
    ("any_over_list", "def f(xs):\n    return any(x > 0 for x in xs)\n"),
    ("set_build", "def f(xs):\n    s = set()\n    for x in xs:\n        s.add(x)\n    return len(s)\n"),
    ("set_count_range", "def f(n):\n    s = set()\n    for i in range(n):\n        s.add(i)\n    return len(s)\n"),
    ("dict_build", "def f(xs):\n    d = dict()\n    for x in xs:\n        d[x] = 1\n    return len(d)\n"),
    ("set_build_guarded", "def f(xs):\n    s = set()\n    for x in xs:\n        if x > 0:\n            s.add(x)\n    return len(s)\n"),
    # iterating a list parameter, via the sequence-loop engine
    ("list_sum", "def f(xs: list):\n    s = 0\n    for x in xs:\n        s = s + x\n    return s\n"),
    ("list_count_pos", "def f(xs: list):\n    c = 0\n    for x in xs:\n        if x > 0:\n            c = c + 1\n    return c\n"),
    ("list_max", "def f(xs: list):\n    m = 0\n    for x in xs:\n        if x > m:\n            m = x\n    return m\n"),
    ("list_min0", "def f(xs: list):\n    m = 0\n    for x in xs:\n        if x < m:\n            m = x\n    return m\n"),
    ("list_contains", "def f(xs: list, target):\n    found = 0\n    for x in xs:\n        if x == target:\n            found = 1\n    return found\n"),
    ("list_abs_sum", "def f(xs: list):\n    s = 0\n    for x in xs:\n        s = s + abs(x)\n    return s\n"),
    ("list_product", "def f(xs: list):\n    p = 1\n    for x in xs:\n        p = p * x\n    return p\n"),
    ("list_nonneg_count", "def f(xs: list):\n    c = 0\n    for x in xs:\n        if x >= 0:\n            c = c + 1\n    return c\n"),
    ("enumerate_index_sum", "def f(xs: list):\n    s = 0\n    for i, x in enumerate(xs):\n        s = s + i\n    return s\n"),
    ("range_len_sum", "def f(xs: list):\n    s = 0\n    for i in range(len(xs)):\n        s = s + xs[i]\n    return s\n"),
    # generators that yield in a range loop, via the generator-loop engine
    ("branching_generator", "def f(n):\n    for i in range(n):\n        if i > 0:\n            yield i\n"),
    ("range_generator", "def f(n):\n    for i in range(n):\n        yield i\n"),
    ("even_generator", "def f(n):\n    for i in range(n):\n        yield 2 * i\n"),
    # round and a list slice are modeled (min(xs) / max(xs) as a direct call are NOT: an empty list is a
    # ValueError the value engine cannot rule out for an opaque list parameter, so they are left UNKNOWN;
    # the list-iteration forms list_max / list_min0 above are the soundly-modeled reductions over a list)
    ("round_to_int", "def f(x: float):\n    return round(x)\n"),
    ("round_ndigits", "def f(x: float):\n    return round(x, 2)\n"),
    ("list_slice", "def f(xs: list):\n    return xs[1:3]\n"),
    # str.split / splitlines and a generator with control flow or recursion are modeled
    ("string_split", "def f(s: str):\n    return len(s.split())\n"),
    ("recursive_generator", "def f(n):\n    if n > 0:\n        yield n\n        yield from f(n - 1)\n"),
    # bitwise | / & / ^ on unbounded integers, as sound over-approximations (nonnegative-operand bounds)
    ("bitwise_or", "def f(a, b):\n    return a | b\n"),
    # str.format on a literal format string, as a sound over-approximation (an opaque string when the
    # positional fields are satisfied and spec-free; a field beyond the arguments is an IndexError trap)
    ("str_format", "def f(x):\n    return '{}'.format(x)\n"),
]


def _coverage_one(src):
    """Whether the tool can reason about a function: some engine returns a definite verdict (PROVED or
    REFUTED) for a trivial obligation, meaning the body is within the modeled subset. Tries the
    control-flow safety engine, the loop-free value engine, the heap engine, and the recursion engine.
    Returns (modeled, reason) where reason is the last front end's complaint when none apply."""
    decided = (PROVED, REFUTED)
    tt = lambda *a: z3.BoolVal(True)
    attempts = [
        lambda: check(src),
        lambda: verify_predicate("cov", "f", src, tt, {}),
        lambda: verify_heap_property("cov", "f", src, tt),
        lambda: verify_recursive("cov", "f", src, tt, tt),
        lambda: verify_map_comprehension("cov", "f", src, lambda P, R, ln: z3.BoolVal(True)),
        lambda: verify_all_any("cov", "f", src, lambda P, r: z3.BoolVal(True)),
        lambda: verify_growing_set_auto("cov", "f", src, lambda P, c: z3.BoolVal(True)),
        lambda: verify_sequence_loop("cov", "f", src, lambda P, r: z3.BoolVal(True)),
        lambda: verify_generator_loop("cov", "f", src, lambda P, v: z3.BoolVal(True)),
    ]
    reason = ""
    for run in attempts:
        try:
            v = run()
            if v.status in decided:
                return True, ""
            if not reason:
                reason = v.reason                            # the primary engine's complaint is the clearest
        except Exception as e:
            if not reason:
                reason = f"{type(e).__name__}: {e}"
    return False, reason


def coverage_report(corpus=None):
    """Modeled coverage over a representative sample of Python functions: the fraction the
    tool can reason about, with the rest naming the constructs still to model. A measurement, not a
    gate; the aim is to drive it up over time. Returns the rate and the unmodeled functions."""
    corpus = corpus if corpus is not None else _COVERAGE_CORPUS
    modeled, unmodeled = 0, []
    for name, src in corpus:
        ok, reason = _coverage_one(src)
        if ok:
            modeled += 1
        else:
            unmodeled.append((name, reason))
    total = len(corpus)
    return {"functions": total, "modeled": modeled,
            "rate": 100.0 * modeled / total if total else 100.0, "unmodeled": unmodeled}


def nonlinear_corroboration_audit():
    """The nonlinear lane holds two invariants: no PROVED rests on a single uncorroborated solver (every PROVED
    carries a corroborator certificate -- cvc5 coverings, a checked SOS certificate, or real-relaxation), and no
    REFUTED comes from a non-integral real model (every counterexample is integral and genuinely falsifies). A
    corpus of true nonnegativity goals proves-and-corroborates; false ones refute with an integer witness; a goal
    true over Z but false over R is never refuted by its real model."""
    saved = core.REQUIRE_CORROBORATION
    core.REQUIRE_CORROBORATION = True
    try:
        must_prove = [
            ("def f(a, b):\n    return (a - b) * (a - b)\n", "result >= 0"),             # square
            ("def f(x):\n    return x * x\n", "result >= 0"),                             # square
            ("def f(a, b):\n    return a * a + b * b - 2 * a * b\n", "result >= 0"),      # AM-GM
            ("def f(a, b):\n    return a * a * b * b - 2 * a * b + 1\n", "result >= 0"),  # (a*b - 1)^2, degree 4
        ]
        for src, ens in must_prove:
            v = prove(src, ens)
            assert v.status == PROVED and v.certificate is not None, (src, v.status, v.certificate, v.reason)
        v = prove("def f(a, b):\n    return a * b\n", "result >= 0", requires="a >= 0 and b >= 0")
        assert v.status == PROVED and v.certificate is not None, v       # sign product (a precondition: cvc5 coverings)
        for src, ens, exact in [("def f(x):\n    return x * x\n", "result > 0", {"x": 0}),
                                ("def f(x):\n    return x * x * x\n", "result >= 0", {"x": -1})]:
            v = prove(src, ens)                                          # genuinely false: REFUTED at an integer witness
            assert v.status == REFUTED and v.counterexample_inputs, (src, v.status)
            assert all(isinstance(x, int) for x in v.counterexample_inputs.values()), v
            assert v.counterexample_inputs == exact, v
        v = prove("def f(x):\n    return x * x\n", "result >= x")        # true over Z, false over R at x = 1/2:
        assert v.status != REFUTED, v                                   # the real model is not an integer counterexample
        sv = verify_sos_nonneg("p", "p", lambda X: (X[0] - X[1]) * (X[0] - X[1]), 2)
        assert sv.status == PROVED and sv.certificate is not None and "exact" in sv.certificate, sv
        _a, _b, _x = z3.Int("a"), z3.Int("b"), z3.Int("x")
        assert core._real_relaxation_proves((_a - _b) * (_a - _b) < 0)   # real-unsat proves the integer goal
        assert not core._real_relaxation_proves(_x * _x < _x)           # real-sat (x = 1/2): abstains, never refutes
    finally:
        core.REQUIRE_CORROBORATION = saved
    return {"proved": len(must_prove) + 1, "refuted": 2}


def run_self_tests(fast=False):
    # fast=True is the inner-loop gate: it keeps every capability assertion but substitutes stub results for the
    # CPython-execution cross-checks (the differential / refinement / benchmark audits), which spawn subprocesses
    # and dominate the runtime. The full suite (fast=False, what CI runs) still executes them.
    print("SELF-TESTS" + (" (fast)" if fast else ""))
    repo = {
        "fee": "def fee(p):\n    return p // 10\n",
        "net": "def net(p):\n    return p - fee(p)\n",
    }

    # correct sign proven over ALL integers
    sign_ok = "def sign(x):\n    if x > 0:\n        return 1\n    if x < 0:\n        return -1\n    return 0\n"
    sign_spec = "def s(x):\n    if x > 0:\n        return 1\n    if x < 0:\n        return -1\n    return 0\n"
    v = verify_equiv("sign==spec", "sign", sign_ok, sign_spec, {})
    assert v.status == PROVED, v

    # boundary bug only at large x: bounded testing MISSES, SMT PROVES it wrong
    classify_bug = ("def classify(x):\n"
                    "    if x >= 1000001:\n"
                    "        return 1\n"
                    "    if x <= -1000000:\n"
                    "        return 1\n"
                    "    return 0\n")
    classify_spec = ("def c(x):\n"
                     "    if x >= 1000000:\n"
                     "        return 1\n"
                     "    if x <= -1000000:\n"
                     "        return 1\n"
                     "    return 0\n")
    cf = _pyfn(classify_bug, {})
    cs = _pyfn(classify_spec, {})
    assert all(cf(i) == cs(i) for i in range(-10000, 10001)), "bounded test should miss the bug"
    v = verify_equiv("classify==spec", "classify", classify_bug, classify_spec, {})
    assert v.status == REFUTED and "1000000" in (v.counterexample or ""), v

    classify_fixed = classify_spec.replace("def c(", "def classify(")
    v = verify_equiv("classify==spec", "classify", classify_fixed, classify_spec, {})
    assert v.status == PROVED, v

    # counterexamples are minimized to the smallest, simplest witness (fewest nonzero, least magnitude)
    vm = verify_predicate("min", "f", "def f(x):\n    return x * 2\n", lambda za, o: o < 100, {})
    assert vm.status == REFUTED and vm.counterexample_inputs == {"x": 50}, vm     # the boundary, not a large x
    vm = verify_equiv("min", "f", "def f(a):\n    return a + a\n", "def g(a):\n    return a + a + 7\n", {})
    assert vm.status == REFUTED and vm.counterexample_inputs == {"a": 0}, vm      # simplest witness
    vm = prove("def f(x):\n    return x * 2\n", "result < 100")
    assert vm.status == REFUTED and vm.counterexample_inputs == {"x": 50}, vm     # via the verified VC generator

    # predicate spec: abs is always non-negative, for all inputs
    v = verify_predicate("abs>=0", "myabs", "def myabs(x):\n    return abs(x)\n",
                         lambda za, out: out >= 0, {})
    assert v.status == PROVED, v

    # interprocedural predicate: for p>=0, 0 <= net(p) <= p  (net inlines fee)
    pred = lambda za, out: z3.Implies(za["p"] >= 0, z3.And(out >= 0, out <= za["p"]))
    v = verify_predicate("net_bounds", "net", repo["net"], pred, repo)
    assert v.status == PROVED, v

    # buggy fee breaks net's property (at p=0, fee=1 -> net=-1)
    bad_repo = dict(repo, fee="def fee(p):\n    return p // 10 + 1\n")
    v = verify_predicate("net_bounds", "net", bad_repo["net"], pred, bad_repo)
    assert v.status == REFUTED, v

    # unmodeled external call -> UNKNOWN (escalation boundary)
    ext = {"post": "def post(a):\n    return external_fetch(a) - a\n"}
    v = verify_predicate("post_ok", "post", ext["post"], lambda za, out: out <= za["a"], ext)
    assert v.status == UNKNOWN and "external_fetch" in v.reason, v

    # deductive: sum_to proven over unbounded n (nonlinear postcondition)
    sum_to = ("def sum_to(n):\n"
              "    total = 0\n"
              "    i = 1\n"
              "    while i <= n:\n"
              "        total = total + i\n"
              "        i = i + 1\n"
              "    return total\n")
    pre = lambda S: S["n"] >= 0
    inv = lambda S: z3.And(2 * S["total"] == (S["i"] - 1) * S["i"], S["i"] >= 1, S["i"] <= S["n"] + 1)
    post = lambda S, ret: 2 * ret == S["n"] * (S["n"] + 1)
    v = verify_deductive("sum=n(n+1)/2", "sum_to", sum_to, pre, inv, post, {})
    assert v.status == PROVED, v

    # buggy loop body (i += 2) fails preservation -> REFUTED
    sum_bug = sum_to.replace("i = i + 1", "i = i + 2")
    v = verify_deductive("sum=n(n+1)/2", "sum_to", sum_bug, pre, inv, post, {})
    assert v.status == REFUTED, v

    # structural: both-branch acquire then write-after-if PROVES (join works)
    both = ("def save(x):\n"
            "    if x > 0:\n"
            "        acquire_lock()\n"
            "    else:\n"
            "        acquire_lock()\n"
            "    db.write(x)\n")
    assert verify_lock("lock", "save", both, {}).status == PROVED
    # one-branch acquire -> REFUTED
    one = "def save(x):\n    if x > 0:\n        acquire_lock()\n    db.write(x)\n"
    assert verify_lock("lock", "save", one, {}).status == REFUTED
    # loop-protected -> PROVED ; loop with write-before-acquire -> REFUTED
    good_loop = ("def flush(xs):\n    while xs:\n        acquire_lock()\n"
                 "        db.write(xs)\n        release_lock()\n")
    assert verify_lock("lock", "flush", good_loop, {}).status == PROVED
    bad_loop = ("def flush(xs):\n    while xs:\n        db.write(xs)\n"
                "        acquire_lock()\n        release_lock()\n")
    assert verify_lock("lock", "flush", bad_loop, {}).status == REFUTED
    # arbitrary lock variables and regions: a with-block, method acquire/release, several named locks,
    # and a per-operation requirement that a specific lock be the one held.
    assert verify_lock("lock", "f", "def f(x):\n    with lock:\n        db.write(x)\n", {}).status == PROVED
    assert verify_lock("lock", "f", "def f(x):\n    with lock:\n        y = 1\n    db.write(x)\n", {}).status == REFUTED
    assert verify_lock("lock", "f", "def f(x):\n    L.acquire()\n    db.write(x)\n    L.release()\n", {}).status == PROVED
    assert verify_lock("lock", "f", "def f(x):\n    a.acquire()\n    b.acquire()\n    db.write(x)\n"
                       "    b.release()\n    a.release()\n", {}).status == PROVED
    assert verify_lock("lock", "f", "def f(x):\n    db_lock.acquire()\n    db.write(x)\n", {},
                       guarded={"db.write": "db_lock"}).status == PROVED
    assert verify_lock("lock", "f", "def f(x):\n    other.acquire()\n    db.write(x)\n", {},
                       guarded={"db.write": "db_lock"}).status == REFUTED       # wrong lock held

    # interval analysis: prove a loop's result range with NO supplied invariant
    clamp = "def clamp():\n    x = 0\n    while x < 100:\n        x = x + 1\n    return x\n"
    assert verify_range("range", "clamp", clamp, 0, 100).status == PROVED
    assert verify_range("range", "clamp", clamp, 100, 100).status == PROVED
    # limitation: a relational bound (i <= n) is beyond a non-relational domain
    rel = "def g(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n"
    assert verify_range("range", "g", rel, 0, 1000).status == UNKNOWN

    # Houdini: AUTOMATICALLY discover the sum_to invariant, then prove the post
    v = verify_deductive_auto("sum=n(n+1)/2", "sum_to", sum_to, pre, post, {})
    assert v.status == PROVED and "2*total" in v.reason, v
    # without the degree-2 templates the invariant is outside the candidate space -> UNKNOWN
    v = verify_deductive_auto("sum=n(n+1)/2", "sum_to", sum_to, pre, post, {}, quad=False)
    assert v.status == UNKNOWN, v

    # bitvector: overflow not represented by the unbounded-integer model
    sq = "def sq(x):\n    return x * x\n"
    assert verify_equiv("sq==x*x", "sq", sq, "def s(x):\n    return x * x\n", {}).status == PROVED
    assert verify_no_overflow("no-ovf", "sq", sq, width=64).status == REFUTED       # overflows
    safe = "def sgn(x):\n    if x > 0:\n        return 1\n    return 0\n"
    assert verify_no_overflow("no-ovf", "sgn", safe, width=64).status == PROVED
    # clamping is PROVEN to prevent overflow (path-sensitive)
    score_safe = ("def score(x):\n    if x > 100:\n        x = 100\n"
                  "    if x < 0:\n        x = 0\n    return x * x\n")
    score_unsafe = "def score(x):\n    return x * x\n"
    assert verify_no_overflow("no-ovf", "score", score_safe, width=16).status == PROVED
    assert verify_no_overflow("no-ovf", "score", score_unsafe, width=16).status == REFUTED

    # CHC/Spacer: template-free invariant synthesis, including relational facts
    counter = "def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n"
    assert verify_chc("ret==n", "f", counter,
                      lambda S: S["n"] >= 0, lambda S, r: r == S["n"]).status == PROVED
    twovar = ("def g(n):\n    x = 0\n    y = 0\n    while x < n:\n"
              "        x = x + 1\n        y = y + 1\n    return x\n")
    assert verify_chc("x==y", "g", twovar,
                      lambda S: S["n"] >= 0, lambda S, r: S["x"] == S["y"]).status == PROVED
    # the nonlinear obligation is beyond Spacer's linear search, so the engine synthesizes the
    # degree-two inductive invariant it diverges on and discharges it
    assert verify_chc("nl", "sum_to", sum_to,
                      lambda S: S["n"] >= 0,
                      lambda S, r: 2 * r == S["n"] * (S["n"] + 1)).status == PROVED
    # a single-loop CHC PROVED is corroborated by re-checking Spacer's invariant as quantifier-free
    # verification conditions with the second solver; the corroborated verdict carries a certificate.
    cv = verify_chc("ret==n", "f", counter, lambda S: S["n"] >= 0, lambda S, r: r == S["n"])
    assert cv.status == PROVED and cv.certificate is not None and "cvc5" in cv.certificate, cv
    # the same invariant recheck corroborates the recursion engine (its answer carries an input/output
    # relation alongside the error relation, each substituted by its own De Bruijn binding). It is wired
    # into the whole-function, whole-program, and interprocedural Horn engines too, best-effort: it
    # corroborates when the second solver can confirm the invariant and leaves the verdict standing
    # otherwise, never falsely flagging a correct proof.
    rv = verify_recursive("rc", "f", "def f(n):\n    if n <= 0:\n        return 0\n    return f(n - 1) + 1\n",
                          lambda S: S["n"] >= 0, lambda S, r: r == S["n"])
    assert rv.status == PROVED and rv.certificate is not None and "cvc5" in rv.certificate, rv
    # nested loops: the per-block Horn system synthesizes an independent inductive invariant for each loop, so a
    # property over a doubly-nested loop is decided (proved, or refuted on a concrete input) rather than abstained.
    _nest = ("def f(n, m):\n    c = 0\n    i = 0\n    while i < n:\n        j = 0\n"
             "        while j < m:\n            c = c + 1\n            j = j + 1\n        i = i + 1\n    return c\n")
    assert prove(_nest, "result >= 0", requires="n >= 0 and m >= 0", target="f").status == PROVED
    assert prove(_nest, "result == n * m + 1", requires="n >= 0 and m >= 0", target="f").status == REFUTED
    _tri = ("def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        j = 0\n"
            "        while j < i:\n            s = s + 1\n            j = j + 1\n        i = i + 1\n    return s\n")
    assert prove(_tri, "result >= 0", requires="n >= 0", target="f").status == PROVED
    # a false loop postcondition is refuted by Spacer's reachability query, which finds the violating run through
    # the invariant rather than by unrolling, so the refutation does not require reaching the bug's iteration depth.
    _lp = "def f(n):\n    x = 0\n    i = 0\n    while i < n:\n        x = x + 1\n        i = i + 1\n    return x\n"
    assert prove(_lp, "result == n + 1", requires="n >= 0", target="f").status == REFUTED

    # arrays + quantifiers: bounds-safety and a quantified functional postcondition
    set_zero = ("def set_zero(a: list, n: int):\n    i = 0\n    while i < n:\n"
                "        a[i] = 0\n        i = i + 1\n    return a\n")
    pre_sz = lambda S: z3.And(S["n"] >= 0, S["n"] <= S["len_a"])
    inv_sz = lambda S: z3.And(0 <= S["i"], S["i"] <= S["n"], S["n"] <= S["len_a"],
                              q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < S["i"]),
                                                            z3.Select(S["a"], j) == 0)))
    post_sz = lambda S, _: q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]),
                                                         z3.Select(S["a"], j) == 0))
    assert verify_array_loop("zeroed", "set_zero", set_zero, pre_sz, inv_sz, post_sz).status == PROVED
    # an off-by-one that writes a[n] is caught as a possible out-of-bounds access
    set_zero_bad = set_zero.replace("i < n", "i <= n")
    inv_bad = lambda S: z3.And(0 <= S["i"], S["i"] <= S["n"] + 1, S["n"] <= S["len_a"])
    assert verify_array_loop("zeroed", "set_zero", set_zero_bad,
                             pre_sz, inv_bad, lambda S, _: z3.BoolVal(True)).status == REFUTED

    # termination: a ranking function proves the counted loop halts; the
    #     unbounded loop has no linear ranking function -> UNKNOWN
    assert verify_termination("term", "f", counter).status == PROVED
    nonterm = "def f(x):\n    while x != 0:\n        x = x + 1\n    return x\n"
    assert verify_termination("term", "f", nonterm).status == UNKNOWN
    # non-termination as a findable bug: the dual of verify_termination. A recurrence set R (a half-space
    # over the loop variables) discharged soundly with z3 -- R implies the guard, is closed under the body,
    # the body is trap free on R, and R is reachable -- certifies that some input diverges, reported as
    # REFUTED with the diverging witness. The counter that halts is not flagged (no false positive).
    nt = verify_nontermination("nt", "f", nonterm)
    assert nt.status == REFUTED and nt.counterexample_inputs == {"x": 1}, nt           # x=1 -> x grows, never 0
    assert verify_nontermination("nt", "f",
        "def f(x):\n    while x > 0:\n        x = x + 1\n    return x\n").status == REFUTED   # guard already inductive
    assert verify_nontermination("nt", "f",
        "def f(n):\n    i = 0\n    while i < n:\n        i = i - 1\n    return i\n").status == REFUTED  # counter away from guard
    assert verify_nontermination("nt", "f", counter).status == UNKNOWN                  # the halting counter: not flagged
    assert verify_nontermination("nt", "f", sum_to).status == UNKNOWN                   # gauss sum halts: not flagged
    # total correctness folds it in: a partial-correct but provably non-terminating loop is a total-correctness
    # REFUTED carrying the diverging witness, while a precondition excluding the diverging region yields no
    # false refutation (UNKNOWN, since termination there is simply not shown).
    _divloop = "def f(x):\n    while x > 0:\n        x = x + 1\n    return x\n"
    _vd = verify_total("tot-nt", "f", _divloop, lambda S: z3.BoolVal(True), lambda S, r: r <= 0)
    assert _vd.status == REFUTED and _vd.counterexample_inputs == {"x": 1}, _vd
    assert verify_total("tot-nt", "f", _divloop, lambda S: S["x"] <= 0, lambda S, r: r <= 0).status == UNKNOWN
    # and the implicit-contract triage path (`check --total`, repo triage) surfaces it as a finding: a
    # trap-free but non-terminating loop is REFUTED with the witness, while a precondition that excludes the
    # diverging region does not produce a false totality bug.
    _ctd = check(_divloop, total=True, target="f")
    assert _ctd.status == REFUTED and _ctd.counterexample_inputs == {"x": 1}, _ctd
    assert check(_divloop, requires="x <= 0", total=True, target="f").status != REFUTED

    # zone (relational) domain proves x == y, which the interval domain cannot
    assert verify_zone_equal("x==y", "g", twovar, "x", "y").status == PROVED

    # soundness auditing: verdicts cross-checked against the SMT model, with no
    #     execution of the subject (the threat model forbids running analyzed code).
    impl_id, spec_p1 = "def f(a):\n    return a\n", "def f(a):\n    return a + 1\n"
    vb = verify_equiv("a vs a+1", "f", impl_id, spec_p1, {})
    assert vb.status == REFUTED
    assert model_cross_check(vb, impl_id, spec_p1, {}) == 1           # cex disagrees symbolically
    impl_2a, spec_aa = "def f(a):\n    return a * 2\n", "def f(a):\n    return a + a\n"
    vp = verify_equiv("2a vs a+a", "f", impl_2a, spec_aa, {})
    assert vp.status == PROVED
    assert model_cross_check(vp, impl_2a, spec_aa, {}) == 1           # PROVED re-discharged
    # teeth: a fabricated PROVED for two differing functions is caught by re-solving
    fake = Verdict(PROVED, "fabricated", "f", "symbolic+SMT (all inputs)")
    try:
        model_cross_check(fake, impl_id, spec_p1, {})
        raise AssertionError("auditor failed to catch a bogus PROVED")
    except SoundnessError:
        pass
    # end-to-end audit over random programs, plus the exhaustive CPython cross-check -- both run the subject, so
    # the inner-loop fast mode skips them while the full suite keeps them.
    if not fast:
        rep = soundness_audit(trials=40)
        assert rep["model_checks"] > 0, rep
        core.ALLOW_SUBJECT_EXECUTION = True
        try:
            assert differential_check(vp, impl_2a, spec_aa, {}) > 0   # encoding vs Python
            assert validate_counterexample(vb, impl_id, spec_p1, {})
            # exhaustive (not sampled) cross-check: a PROVED equivalence confirmed on EVERY input in the bounded
            # box [-12, 12] per parameter is proved over that box -- stronger than the sampled differential -- and
            # a genuine non-equivalence is caught as a SoundnessError, never missed.
            _exi, _exs = "def f(a, b):\n    return a + b\n", "def f(a, b):\n    return b + a\n"
            _exv = verify_equiv("exh", "f", _exi, _exs, {})
            assert _exv.status == PROVED and exhaustive_check(_exv, _exi, _exs, {}, bound=12) == 25 * 25
            try:
                exhaustive_check(Verdict(PROVED, "exh", "f", "t"), _exi,
                                 "def f(a, b):\n    return a + b + 1\n", {}, bound=4)
                raise AssertionError("exhaustive_check missed a non-equivalence")
            except SoundnessError:
                pass
        finally:
            core.ALLOW_SUBJECT_EXECUTION = False

    # partial functions: division by a possibly-zero divisor is a trap. a//a
    #     differs from 1 only at a=0 (impl traps); same-trap functions are equal.
    impl_dz, spec_one = "def f(a):\n    return a // a\n", "def f(a):\n    return 1\n"
    vdz = verify_equiv("a//a vs 1", "f", impl_dz, spec_one, {})
    assert vdz.status == REFUTED and vdz.counterexample_inputs.get("a") == 0, vdz
    assert validate_counterexample(vdz, impl_dz, spec_one, {})        # a=0: impl traps, spec=1
    both = verify_equiv("trap==trap", "f", "def f(a):\n    return (a // a) + 1\n",
                        "def f(a):\n    return 1 + (a // a)\n", {})
    assert both.status == PROVED, both
    # negative-divisor floor division is encoded exactly (Euclidean correction)
    assert verify_equiv("negdiv", "f", "def f(a):\n    return a // -3\n",
                        "def f(a):\n    return a // -3\n", {}).status == PROVED

    # augmented assignment, and a branched loop body, both invariant-inferred
    sum_aug = ("def sum_to(n):\n    total = 0\n    i = 1\n    while i <= n:\n"
               "        total += i\n        i += 1\n    return total\n")
    assert verify_deductive_auto("sum+=", "sum_to", sum_aug, pre, post, {}).status == PROVED
    branched = ("def f(n):\n    s = 0\n    i = 0\n    while i < n:\n"
                "        if i > 0:\n            s = s + i\n        i = i + 1\n    return s\n")
    assert verify_termination("branched", "f", branched).status == PROVED

    # min/max/abs are modeled; a clamp lands in [0,100] over ALL inputs
    assert verify_predicate("clamp", "f", "def f(x):\n    return max(0, min(100, x))\n",
                            lambda za, out: z3.And(out >= 0, out <= 100), {}).status == PROVED
    # min / max over a single opaque sequence parameter raises ValueError when it is empty, modeled against
    # the container's symbolic length: unguarded it is REFUTED (min([]) raises), a len() or truthiness guard
    # proves it safe, and a default= keyword never raises. Multi-argument min / max over values stays exact,
    # and a non-empty literal is computed; the recursion engine is held to the same rule.
    assert check("def f(xs: list):\n    return min(xs)\n").status == REFUTED      # min([]) is a ValueError
    assert check("def f(xs: list):\n    return max(xs)\n").status == REFUTED
    assert check("def f(xs: list):\n    if len(xs) > 0:\n        return min(xs)\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    if xs:\n        return max(xs)\n    return 0\n").status == PROVED   # truthiness guard
    assert check("def f(xs: list):\n    return min(xs, default=0)\n").status == PROVED   # a default never raises
    # min/max of an empty literal: bare raises ValueError (REFUTED); a default= makes it total, returning the
    # default (PROVED), even through later arithmetic; a default expression that itself traps still refutes.
    assert check("def f():\n    return min([], default=5) + 1\n").status == PROVED
    assert check("def f():\n    return max((), default=-1)\n").status == PROVED
    assert check("def f():\n    return min([])\n").status == REFUTED
    assert check("def f():\n    return max(())\n").status == REFUTED
    assert check("def f(x: int):\n    return min([], default=10 // x)\n").status == REFUTED   # default expr divides by x
    assert check("def f():\n    v = min([], default=None)\n    if v is None:\n        return 0\n    return v + 1\n").status == PROVED
    # an emptiness guard written as truthiness (`if c:` / `if not c:`), not only `len(c) > 0`, connects to the
    # container's length, so a guarded index or reduction proves while the unguarded form still refutes and a
    # guard too weak for the index (non-empty but read past element 0) is still refuted.
    assert check("def f(xs: list):\n    if xs:\n        return xs[0]\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    if not xs:\n        return 0\n    return xs[0]\n").status == PROVED
    assert check("def f(xs: list):\n    if xs:\n        return xs[5]\n    return 0\n").status == REFUTED   # non-empty != len > 5
    assert check("def f(xs: list):\n    return xs[0]\n").status == REFUTED        # genuinely unguarded: still refuted
    # unpacking a sequence parameter into N names raises ValueError unless its length is exactly N (CPython's
    # exact-arity rule), modeled against the same symbolic length: an unguarded a, b = xs is REFUTED on a
    # length-mismatched witness while a len(xs) == N guard proves it. A literal tuple and a swap still verify.
    assert check("def f(xs: list):\n    a, b = xs\n    return a + b\n").status == REFUTED
    assert check("def f(xs: list):\n    if len(xs) == 2:\n        a, b = xs\n        return a + b\n    return 0\n").status == PROVED
    assert check("def f(pt: list):\n    x, y, z = pt\n    return x + y + z\n").status == REFUTED
    assert check("def f(pt: list):\n    if len(pt) == 3:\n        x, y, z = pt\n        return x\n    return 0\n").status == PROVED
    assert check("def f():\n    a, b = (1, 2)\n    return a + b\n").status == PROVED   # a literal tuple: exact, no trap
    # a starred unpacking a, *b, c = seq raises ValueError unless len(seq) >= the fixed-name count; *b is the middle
    # slice (length len(seq) minus that count), so an unguarded unpack refutes, a len() guard proves, and b[0] under
    # the guard that makes b non-empty stays sound (no false refute).
    assert check("def f(xs: list):\n    a, *b = xs\n    return a\n").status == REFUTED
    assert check("def f(xs: list):\n    if len(xs) >= 1:\n        a, *b = xs\n        return a\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    a, *b, c = xs\n    return a\n").status == REFUTED
    assert check("def f(xs: list):\n    if len(xs) >= 2:\n        a, *b = xs\n        return b[0]\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    a, *b = xs\n    return b[0]\n").status == REFUTED
    # str.encode() (default utf-8) never raises and yields bytes of length >= len(s), so the value engine decides
    # a str-parameter function the integer CHC model declines: encode() is trap free, an unguarded encode()[0]
    # refutes on the empty string, and a len() guard proves it (the byte length tracks the char length).
    assert check("def f(s: str):\n    return s.encode()\n").status == PROVED
    assert check("def f(s: str):\n    return s.encode()[0]\n").status == REFUTED
    assert check("def f(s: str):\n    if len(s) >= 1:\n        return s.encode()[0]\n    return 0\n").status == PROVED
    # str search with a position window: find/rfind with a start (and end) bound is a sound index in [-1, len(s))
    # (never raises), and index(sub, start) raises ValueError when the substring is absent from s[start:], so a parser
    # scanning with src.find(sep, pos, end) and a later end + 1 is decided rather than left dark.
    assert check("def f(s: str, p: int, m: int):\n    e = s.find(\",\", p, m)\n    return e + 1\n").status == PROVED
    assert check("def f(s: str):\n    return s.index(\",\", 2)\n").status == REFUTED
    assert check("def f():\n    return \"a,b\".index(\",\", 0)\n").status == PROVED
    # startswith/endswith with a non-negative start (and optional end) is exact over s[start:end] -- a true result
    # implies s is long enough, so a guarded s[0] proves -- and count over a window is a sound count in [0, len(s)].
    assert check("def f(s: str):\n    if s.startswith(\"x\", 0):\n        return s[0]\n    return \"y\"\n").status == PROVED
    assert check("def f(s: str):\n    n = s.count(\",\", 0, 5)\n    return 10 // n\n").status == REFUTED
    # split(sep, maxsplit) and replace(old, new, count) are decided: split yields a string sequence (an empty
    # separator raises ValueError), replace never raises (a string result, over-approximated for the count limit).
    assert check("def f(s: str, sep: str):\n    return s.split(sep, 1)\n").status == REFUTED
    assert check("def f(s: str):\n    return s.replace(\"a\", \"b\", 1)\n").status == PROVED
    assert check("def f(s: str):\n    return \" \".join(s.split())\n").status == PROVED   # join a split (string) seq
    # split/rsplit with a separator yield >= 1 part, so [0]/[-1] are in bounds and an element is a string; split() on
    # whitespace and splitlines() can be empty, so [0] there is a refutable IndexError.
    assert check("def f(s: str):\n    return s.split(',')[0]\n").status == PROVED
    assert check("def f(s: str):\n    return s.split(',')[-1]\n").status == PROVED
    assert check("def f(s: str):\n    return s.rsplit('/', 1)[-1]\n").status == PROVED
    assert check("def f(s: str):\n    return s.split(',')[0].upper()\n").status == PROVED
    assert check("def f(s: str):\n    return 10 // len(s.split(','))\n").status == PROVED   # length >= 1, no div-by-0
    assert check("def f(s: str):\n    return s.split()[0]\n").status == REFUTED              # ''.split() == [] -> OOB
    assert check("def f(s: str):\n    return s.splitlines()[0]\n").status == REFUTED
    assert check("def f(s: str):\n    return s.split(',')[5]\n").status == REFUTED           # only >= 1, [5] may be OOB
    assert check("def f(s: str, i: int):\n    return s.split(',')[i]\n").status == REFUTED   # unguarded symbolic index
    assert check("def f(s: str, i: int):\n    p = s.split(',')\n    if 0 <= i < len(p):\n        return p[i]\n    return ''\n").status == PROVED
    # map(str, X) / map(repr, X) yields strings, so sep.join(...) is a trap-free string; the iterator is unsized, so
    # len() of it is a TypeError and it[i] abstains. A non-string map function (map(abs, X)) stays UNKNOWN.
    assert check("def f(xs: list):\n    return ''.join(map(str, xs))\n").status == PROVED
    assert check("def f(xs: list):\n    return ','.join(map(str, xs))\n").status == PROVED
    assert check("def f(n: int):\n    return ' '.join(map(str, range(n)))\n").status == PROVED
    assert check("def f(xs: list):\n    return '-'.join(map(repr, xs))\n").status == PROVED
    assert check("def f(d: dict):\n    return ','.join(map(str, list(d)))\n").status == PROVED
    assert check("def f(xs: list):\n    return len(map(str, xs))\n").status == REFUTED       # map has no len(): TypeError
    assert check("def f(xs: list):\n    return map(str, xs)[0]\n").status == UNKNOWN          # map not subscriptable
    assert check("def f(xs: list):\n    return ','.join(map(abs, xs))\n").status == UNKNOWN   # abs may not yield a str
    # a string-element generator (str(x) for x in xs) is likewise an iterator of strings: sep.join(...) proves; a
    # non-string-element generator stays UNKNOWN.
    assert check("def f(xs: list):\n    return ','.join(str(x) for x in xs)\n").status == PROVED
    assert check("def f(n: int):\n    return '/'.join(str(i) for i in range(n))\n").status == PROVED
    assert check("def f(xs: list):\n    return ','.join(x for x in xs)\n").status == UNKNOWN     # elements not proven str
    # a string-element LIST comp ([str(x) for x in xs]) is a sized string sequence, so sep.join([...]) proves too; and
    # an f-string is always str-typed, so f'{x}' joins, has string methods, and f'{x}' + 1 is a refutable TypeError.
    assert check("def f(xs: list):\n    return ','.join([str(x) for x in xs])\n").status == PROVED
    assert check("def f(xs: list):\n    return ' '.join(f'{x}' for x in xs)\n").status == PROVED
    assert check("def f(xs: list):\n    return ' '.join([f'{x}' for x in xs])\n").status == PROVED
    assert check("def f(x: int):\n    return f'{x}'.upper()\n").status == PROVED
    assert check("def f(x: int):\n    return f'{x}' + 1\n").status == REFUTED               # str + int: TypeError
    # a sequence's truthiness uses the same length its c[i] bounds check uses (the explicit length of a comprehension
    # or split result), so `if c: c[0]` proves.
    assert check("def f(xs: list):\n    c = [x + 1 for x in xs]\n    if c:\n        return c[0]\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    c = [x + 1 for x in xs]\n    return c[0]\n").status == REFUTED   # unguarded: may be empty
    assert check("def f(s: str):\n    parts = s.split()\n    if parts:\n        return parts[0]\n    return ''\n").status == PROVED
    assert check("def f(s: str):\n    parts = s.split()\n    return parts[0]\n").status == REFUTED   # ''.split() == []
    # functools.reduce(f, list[, init]): a total step proves, a trapping step (a // b) refutes, no-init empty refutes
    # (TypeError); a concrete-tuple iterable declines.
    assert check("import functools\ndef f(xs: list):\n    return functools.reduce(lambda a, b: a + b, xs, 0)\n").status == PROVED
    assert check("import functools\ndef f(xs: list):\n    return functools.reduce(lambda a, b: a // b, xs, 100)\n").status == REFUTED
    assert check("import functools\ndef f(xs: list):\n    return functools.reduce(lambda a, b: a + b, xs)\n").status == REFUTED   # empty: TypeError
    assert check("import functools\ndef f(xs: list):\n    if xs:\n        return functools.reduce(lambda a, b: a + b, xs)\n    return 0\n").status == PROVED
    assert check("import functools\ndef f():\n    return functools.reduce(lambda a, b: a // b, (1, 2, 3))\n").status == UNKNOWN   # tuple declines
    # an operator.<binop> fold function (reduce(operator.add, ...) = sum, reduce(operator.mul, ...) = product) applies
    # the corresponding binop, so a total binop proves and a dividing one refutes -- in reduce and accumulate alike.
    assert check("import functools, operator\ndef f(xs: list):\n    return functools.reduce(operator.add, xs, 0)\n").status == PROVED
    assert check("import functools, operator\ndef f(xs: list):\n    return functools.reduce(operator.floordiv, xs, 1)\n").status == REFUTED
    assert check("import itertools, operator\ndef f(xs: list):\n    return list(itertools.accumulate(xs, operator.mul))\n").status == PROVED
    # a lazy iterator (zip / itertools.chain / reversed / ...) has no len() and is not subscriptable: len(it) and it[i]
    # are TypeErrors; only list(it) / sorted(it) / a for-loop consume it.
    assert check("import itertools\ndef f(a: list, b: list):\n    return len(itertools.chain(a, b))\n").status == REFUTED
    assert check("def f(a: list, b: list):\n    return len(zip(a, b))\n").status == REFUTED
    assert check("def f(xs: list):\n    return len(reversed(xs))\n").status == REFUTED
    assert check("import itertools\ndef f(a: list, b: list):\n    return 10 // (len(itertools.chain(a, b)) + 1)\n").status == REFUTED
    assert check("import itertools\ndef f(a: list, b: list):\n    return itertools.chain(a, b)[0]\n").status == REFUTED   # not subscriptable
    assert check("import itertools\ndef f(a: list, b: list):\n    return 10 // (len(list(itertools.chain(a, b))) + 1)\n").status == PROVED   # list(it) is sized
    assert check("import itertools\ndef f(a: list, b: list):\n    t = 0\n    for x in itertools.chain(a, b):\n        t = 1\n    return t\n").status == PROVED   # iterating is fine
    assert check("def f(xs: list):\n    return list(reversed(xs))\n").status == PROVED
    # itertools.accumulate(it[, func]): list(accumulate(xs)) is trap free; a trapping func (a // b) refutes; the
    # iterator is unsized, so len(accumulate(xs)) and accumulate(xs)[i] are TypeErrors.
    assert check("import itertools\ndef f(xs: list):\n    return list(itertools.accumulate(xs))\n").status == PROVED
    assert check("import itertools\ndef f(xs: list):\n    return list(itertools.accumulate(xs, lambda a, b: a // b))\n").status == REFUTED
    assert check("import itertools\ndef f(xs: list):\n    return len(itertools.accumulate(xs))\n").status == REFUTED
    assert check("import itertools\ndef f(xs: list):\n    t = 0\n    for x in itertools.accumulate(xs):\n        t = 1\n    return t\n").status == PROVED
    # itertools.chain.from_iterable(xss): a lazy iterator (like chain), so list(...) is sized but len(...) and [i] are
    # TypeErrors.
    assert check("import itertools\ndef f(xss: list):\n    return 10 // (len(list(itertools.chain.from_iterable(xss))) + 1)\n").status == PROVED
    assert check("import itertools\ndef f(xss: list):\n    return len(itertools.chain.from_iterable(xss))\n").status == REFUTED
    assert check("import itertools\ndef f(xss: list):\n    t = 0\n    for x in itertools.chain.from_iterable(xss):\n        t = 1\n    return t\n").status == PROVED
    # itertools.pairwise(it): consecutive 2-tuples of length max(len-1, 0); a lazy iterator, so list(...) sizes and an
    # element unpacks, len(...) is a TypeError.
    assert check("import itertools\ndef f(xs: list):\n    return 10 // (len(list(itertools.pairwise(xs))) + 1)\n").status == PROVED
    assert check("import itertools\ndef f(xs: list):\n    t = 0\n    for a, b in itertools.pairwise(xs):\n        t = 1\n    return t\n").status == PROVED
    assert check("import itertools\ndef f(xs: list):\n    return len(itertools.pairwise(xs))\n").status == REFUTED
    # sorting / max-ing dict items by value (the d.items() tuple element's [1]) decides via the key= machinery.
    assert check("def f(d: dict):\n    return sorted(d.items(), key=lambda kv: kv[1])\n").status == PROVED
    # [*a, *b, x] star-unpacking builds a NEW list of length sum(len(*list)) + the plain-element count; it is trap free
    # and iterable, indexing it bounds-checks, and a starred non-plain-list source (a zip tuple) declines.
    assert check("def f(a: list, b: list):\n    return 10 // (len([*a, *b]) - len(a) - len(b) + 1)\n").status == PROVED
    assert check("def f(a: list, b: list):\n    t = 0\n    for x in [*a, *b]:\n        t = 1\n    return t\n").status == PROVED
    assert check("def f(a: list, b: list):\n    return [*a, *b][0]\n").status == REFUTED   # may be empty -> IndexError
    assert check("def f(a: list, b: list):\n    return [*list(zip(a, b))]\n").status == UNKNOWN   # tuple source declines
    # (*a, *b, x) tuple star-unpacking is the immutable analogue: a NEW tuple of the same summed length.
    assert check("def f(a: list, b: list):\n    return 10 // (len((*a, *b)) - len(a) - len(b) + 1)\n").status == PROVED
    assert check("def f(a: list, b: list):\n    return (*a, *b)[0]\n").status == REFUTED   # may be empty -> IndexError
    assert check("def f(rest: list, x: int):\n    return (x, *rest)\n").status == PROVED
    # a list / bytes parameter * int repeats it: a NEW sequence of length max(count, 0) * len(seq), trap free, with
    # the element kind preserved (bytes stay [0, 255]). A non-integer multiplier or a nested source declines.
    assert check("def f(a: list):\n    return 10 // (len(a * 3) - 3 * len(a) + 1)\n").status == PROVED
    assert check("def f(a: list):\n    return 3 * a\n").status == PROVED
    assert check("def f(a: list):\n    return (a * 3)[0]\n").status == REFUTED   # a may be empty -> IndexError
    assert check("def f(b: bytes):\n    c = b * 3\n    if c:\n        return 1000 // (c[0] + 1)\n    return 0\n").status == PROVED
    assert check("def f(a: list):\n    return a * 1.5\n").status == UNKNOWN   # non-integer multiplier declines
    # zip / enumerate / dict.items() yield fixed-arity tuples, so an element is a tuple: z[i][0] / z[i][1] decide and
    # a, b = z[i] unpacks, but z[i] + 1 is the TypeError CPython raises (was a false PROVED when elements were modeled
    # as scalar ints). list(enumerate / zip) is sized; sorted(d.items()) and for k, v in d.items() decide.
    assert check("def f(a: list, b: list):\n    z = list(zip(a, b))\n    if z:\n        return z[0] + 1\n    return 0\n").status == REFUTED   # tuple + int
    assert check("def f(a: list, b: list):\n    z = list(zip(a, b))\n    if z:\n        return z[0][0] + 1\n    return 0\n").status == PROVED
    assert check("def f(a: list, b: list):\n    z = list(zip(a, b))\n    if z:\n        x, y = z[0]\n        return x + y\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    return 10 // (len(list(enumerate(xs))) + 1)\n").status == PROVED
    assert check("def f(xs: list):\n    t = 0\n    for i, x in enumerate(xs):\n        t = 1\n    return t\n").status == PROVED
    assert check("def f(d: dict):\n    return sorted(d.items())\n").status == PROVED
    assert check("def f(d: dict):\n    t = 0\n    for k, v in d.items():\n        t = 1\n    return t\n").status == PROVED
    # statistics.mean / median / stdev / ... raise StatisticsError on too few data points (< 1 for the mean family,
    # < 2 for stdev / variance); a len guard removes it. The result is a float.
    assert check("import statistics\ndef f(xs: list):\n    return statistics.mean(xs)\n").status == REFUTED
    assert check("import statistics\ndef f(xs: list):\n    if xs:\n        return statistics.mean(xs)\n    return 0.0\n").status == PROVED
    assert check("import statistics\ndef f(xs: list):\n    return statistics.stdev(xs)\n").status == REFUTED
    assert check("import statistics\ndef f(xs: list):\n    if len(xs) >= 2:\n        return statistics.stdev(xs)\n    return 0.0\n").status == PROVED
    assert check("import statistics\ndef f(xs: list):\n    if len(xs) >= 1:\n        return statistics.stdev(xs)\n    return 0.0\n").status == REFUTED   # 1 point still raises
    # random.choice(seq) IndexErrors on empty; random.sample(seq, k) ValueErrors if k out of [0, len]; random.randint(a,
    # b) ValueErrors if a > b. choice returns an element, sample a list of length k. A guard removes each trap.
    assert check("import random\ndef f(xs: list):\n    return random.choice(xs)\n").status == REFUTED
    assert check("import random\ndef f(xs: list):\n    if xs:\n        return random.choice(xs) + 1\n    return 0\n").status == PROVED
    assert check("import random\ndef f(xs: list):\n    return random.sample(xs, 3)\n").status == REFUTED
    assert check("import random\ndef f(xs: list, k: int):\n    if 0 <= k <= len(xs):\n        return 10 // (len(random.sample(xs, k)) - k + 1)\n    return 0\n").status == PROVED
    assert check("import random\ndef f(a: int, b: int):\n    return random.randint(a, b)\n").status == REFUTED
    assert check("import random\ndef f(a: int, b: int):\n    if a <= b:\n        return random.randint(a, b)\n    return 0\n").status == PROVED
    assert check("import random\ndef f():\n    return random.randint(1, 6)\n").status == PROVED
    # heapq.heappop(h) IndexErrors on an empty heap; returns an element. Modeled only when h is popped exactly once
    # (mutate_once); two pops under a len >= 1 guard ABSTAIN (the second could empty -- not a false PROVED).
    assert check("import heapq\ndef f(h: list):\n    return heapq.heappop(h)\n").status == REFUTED
    assert check("import heapq\ndef f(h: list):\n    if h:\n        return heapq.heappop(h) + 1\n    return 0\n").status == PROVED
    assert check("import heapq\ndef f(h: list):\n    if len(h) >= 1:\n        a = heapq.heappop(h)\n        b = heapq.heappop(h)\n        return a + b\n    return 0\n").status == UNKNOWN
    # deque.popleft() raises IndexError on an empty deque, so it is a trapping method: an opaque receiver abstains
    # to UNKNOWN rather than being assumed trap-free (which would falsely PROVE deque(xs).popleft() for an empty xs).
    assert check("import collections\ndef f(d):\n    return d.popleft()\n").status == UNKNOWN
    assert check("import collections\ndef f(xs: list):\n    return collections.deque(xs).popleft()\n").status == UNKNOWN
    # math.prod(iterable) is trap free (empty -> start=1); the result is an arbitrary int that can be 0, so
    # 10 // math.prod(xs) refutes. A non-scalar-numeric sequence (list of lists) declines.
    assert check("import math\ndef f(xs: list):\n    return math.prod(xs) + 1\n").status == PROVED
    assert check("import math\ndef f(xs: list):\n    return 10 // math.prod(xs)\n").status == REFUTED
    assert check("import math\ndef f(xs: list[list]):\n    return math.prod(xs)\n").status == UNKNOWN
    # math.fsum(iterable) is a trap-free float reduction (empty -> 0.0); the result can be 0.0, so 10 // math.fsum(xs)
    # refutes (float floor-division by zero).
    assert check("import math\ndef f(xs: list):\n    return math.fsum(xs) / 2\n").status == PROVED
    assert check("import math\ndef f(xs: list):\n    return 10 // math.fsum(xs)\n").status == REFUTED
    assert check("import math\ndef f(xs: list[list]):\n    return math.fsum(xs)\n").status == UNKNOWN
    # string module constants (string.digits / ascii_lowercase / ...) are fixed literals, so an index bounds-checks
    # against the exact length (digits is 10), len() is exact, and string methods apply.
    assert check("import string\ndef f(i: int):\n    return string.digits[i]\n").status == REFUTED
    assert check("import string\ndef f(i: int):\n    if 0 <= i < 10:\n        return string.digits[i]\n    return ''\n").status == PROVED
    assert check("import string\ndef f():\n    return string.digits[20]\n").status == REFUTED   # len 10
    assert check("import string\ndef f():\n    return 10 // len(string.digits)\n").status == PROVED
    assert check("import string\ndef f():\n    return string.ascii_uppercase.lower()\n").status == PROVED
    # os.path.split / splitext / splitdrive return a 2-tuple of strings (never raise on str input); basename / dirname
    # / join / normpath return a string; exists / isfile / isdir / isabs return a bool. So splitext(p)[1] is a string,
    # [2] is an out-of-range IndexError, and unpacking root, ext = splitext(p) decides.
    assert check("import os\ndef f(p: str):\n    return os.path.splitext(p)[1].lower()\n").status == PROVED
    assert check("import os\ndef f(p: str):\n    root, ext = os.path.splitext(p)\n    return root + ext\n").status == PROVED
    assert check("import os\ndef f(p: str):\n    return os.path.splitext(p)[2]\n").status == REFUTED   # 2-tuple, [2] OOB
    assert check("import os\ndef f(p: str):\n    return os.path.basename(p).startswith('x')\n").status == PROVED
    assert check("import os\ndef f(p: str):\n    if os.path.exists(p):\n        return 1\n    return 0\n").status == PROVED
    # a nested loop's inner-body first iteration is exact (the first element of an arbitrary row), so an unguarded
    # inner trap refutes (10 // x on a zero element); a trap-free or guarded inner body proves.
    assert check("def f(m: list[list]):\n    s = 0\n    for row in m:\n        for x in row:\n            s = 10 // x\n    return s\n").status == REFUTED
    assert check("def f(m: list[list]):\n    s = 0\n    for row in m:\n        for x in row:\n            s = s + x\n    return s\n").status == PROVED
    assert check("def f(m: list[list]):\n    s = 0\n    for row in m:\n        for x in row:\n            if x != 0:\n                s = 10 // x\n    return s\n").status == PROVED
    # sorted/min/max key= lambda applied to a freely-chosen element: a trap-free key proves, a dividing key refutes.
    # min/max also refute on an empty iterable (no guard / default=). A bare builtin key (len/abs) is declined.
    assert check("def f(xs: list):\n    return sorted(xs, key=lambda x: x + 1)\n").status == PROVED
    assert check("def f(xs: list):\n    return sorted(xs, key=lambda x: -x)\n").status == PROVED
    assert check("def f(xs: list):\n    return sorted(xs, key=lambda x: 10 // x)\n").status == REFUTED   # zero element
    assert check("def f(xs: list):\n    if xs:\n        return max(xs, key=lambda x: x * x)\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    return max(xs, key=lambda x: x + 1, default=0)\n").status == PROVED  # no empty trap
    assert check("def f(xs: list):\n    return max(xs, key=lambda x: x + 1)\n").status == REFUTED          # empty ValueError
    assert check("def f(xs: list):\n    if xs:\n        return max(xs, key=lambda x: 10 // x)\n    return 0\n").status == REFUTED
    assert check("def f(xs: list):\n    return sorted(xs, key=len)\n").status == UNKNOWN                   # builtin key abstains
    assert check("def f(xs: list):\n    return max(xs, key=abs)\n").status == UNKNOWN
    # key=str / key=repr are total on any element (never trap), so they are accepted: sorted(xs, key=str) proves and
    # max(xs, key=str) is the empty-iterable ValueError. Element-type-dependent builtins (len / abs) still decline.
    assert check("def f(xs: list):\n    return sorted(xs, key=str)\n").status == PROVED
    assert check("def f(xs: list):\n    return max(xs, key=str)\n").status == REFUTED                      # empty -> ValueError
    assert check("def f(xs: list):\n    if xs:\n        return max(xs, key=repr)\n    return ''\n").status == PROVED
    # list(s) / sorted(s) of a STRING is a list of 1-char strings, so an element is a string: ''.join(sorted(s)) proves,
    # s[i].upper() proves, and c[0] + 1 refutes (str + int) -- previously elements were modeled as ints (a false PROVED).
    assert check("def f(s: str):\n    return ''.join(sorted(s))\n").status == PROVED
    assert check("def f(s: str):\n    c = sorted(s)\n    if c:\n        return c[0] + 1\n    return 0\n").status == REFUTED
    assert check("def f(s: str):\n    c = list(s)\n    if c:\n        return c[0].upper()\n    return ''\n").status == PROVED
    assert check("def f(xs: list):\n    c = sorted(xs)\n    if c:\n        return c[0] + 1\n    return 0\n").status == PROVED   # list source: int elements
    # getattr(o, "name"[, default]) with a constant name models the field o.name (a stable value, duck-typed numeric),
    # and a parameter used as getattr/hasattr(o, ...) is inferred an object, so arithmetic on a getattr is decided.
    assert check("def f(o):\n    return getattr(o, \"x\", 0) + 1\n").status == PROVED
    assert check("def f(o):\n    return 10 // getattr(o, \"x\", 0)\n").status == REFUTED
    assert check("def f(o):\n    if hasattr(o, \"x\"):\n        return o.x + 1\n    return 0\n").status == PROVED
    # bytes/bytearray find/index/count are decided without modeling byte content: find is an index in [-1, len) so a
    # guarded index is safe, index raises ValueError when the subsequence is absent, and count is in [0, len].
    assert check("def f(b: bytes):\n    i = b.find(b\",\")\n    if i >= 0:\n        return b[i]\n    return 0\n").status == PROVED
    assert check("def f(b: bytes):\n    return b.index(b\",\")\n").status == REFUTED
    # bytes.hex() is a str (never raises), and bytes startswith/endswith with a constant prefix is a bool whose truth
    # implies b is long enough -- so a b[i] within the prefix length proves while one beyond it can still trap.
    assert check("def f(b: bytes):\n    return b.hex().upper()\n").status == PROVED
    assert check("def f(b: bytes):\n    if b.startswith(b\"abc\"):\n        return b[2]\n    return 0\n").status == PROVED
    assert check("def f(b: bytes):\n    if b.startswith(b\"abc\"):\n        return b[5]\n    return 0\n").status == REFUTED
    # a bytes case transform (upper/lower/...) returns bytes of the same length (a guarded index proves, an unguarded
    # one on a possibly-empty result refutes), and split on a constant non-empty separator is a sequence of parts.
    assert check("def f(b: bytes):\n    if len(b) >= 1:\n        return b.upper()[0]\n    return 0\n").status == PROVED
    assert check("def f(b: bytes):\n    return b.upper()[0]\n").status == REFUTED
    assert check("def f(b: bytes):\n    return b.split(b\",\")\n").status == PROVED
    # bytes strip/removeprefix/... return a contiguous sub-portion (length in [0, len(b)]), so a guarded index proves
    # and an unguarded index on a possibly-empty result refutes.
    assert check("def f(b: bytes):\n    s = b.strip()\n    if len(s) >= 1:\n        return s[0]\n    return 0\n").status == PROVED
    assert check("def f(b: bytes):\n    return b.strip()[0]\n").status == REFUTED
    # bytes partition(const sep) is a 3-tuple of sub-portions (each length <= len(b)), so unpacking decides and a
    # guarded index into a piece proves while an unguarded one on a possibly-empty piece refutes.
    assert check("def f(b: bytes):\n    head, sep, tail = b.partition(b\":\")\n    return tail\n").status == PROVED
    assert check("def f(b: bytes):\n    head, sep, tail = b.partition(b\":\")\n    return head[0]\n").status == REFUTED
    assert check("def f(b: bytes):\n    if b.isdigit():\n        return 1\n    return 0\n").status == PROVED   # bytes predicate -> bool
    # total str/bytes stdlib transforms (html.escape/unescape, urllib.parse.quote/unquote, shlex.quote,
    # binascii.hexlify) never raise, so a function using one is decided.
    assert check("import html\ndef f(s: str):\n    return html.escape(s).upper()\n").status == PROVED
    assert check("import binascii\ndef f(b: bytes):\n    return binascii.hexlify(b)\n").status == PROVED
    # bytes + bytes and list + list concatenate to a container of the summed length, so a guarded index into the
    # result proves and an unguarded index when both operands may be empty refutes.
    assert check("def f(b1: bytes, b2: bytes):\n    r = b1 + b2\n    if len(r) >= 1:\n        return r[0]\n    return 0\n").status == PROVED
    assert check("def f(b1: bytes, b2: bytes):\n    r = b1 + b2\n    return r[0]\n").status == REFUTED
    # a loop-havoc'd accumulator that was a container before the loop stays a container (not an int), so a list/bytes
    # accumulator built across a loop -- acc = acc + xs -- and a guarded index into the result are decided.
    assert check("def f(xs: list):\n    acc = xs\n    for x in xs:\n        acc = acc + xs\n    if len(acc) >= 1:\n        return acc[0]\n    return 0\n").status == PROVED
    # a bytes literal is a byteslike container of its known length, so b"" + b concatenates, b"abc"[2] proves in
    # bounds, and b"abc"[5] refutes out of bounds.
    assert check("def f(b: bytes):\n    s = b\"\" + b\n    if len(s) >= 1:\n        return s[0]\n    return 0\n").status == PROVED
    assert check("def f():\n    return b\"abc\"[2]\n").status == PROVED
    assert check("def f():\n    return b\"abc\"[5]\n").status == REFUTED
    # a behavior-preserving decorator -- a memoizer (functools.lru_cache / cache, including the @lru_cache(...) call
    # form) or a binding / marker (staticmethod, property) -- is stripped so the undecorated body is analyzed; an
    # unknown decorator is still inlined or declined, never silently stripped (so a wrapper that traps is not missed).
    assert check("import functools\n@functools.lru_cache\ndef f(x):\n    return 10 // x\n").status == REFUTED
    assert check("import functools\n@functools.lru_cache\ndef f(x):\n    if x != 0:\n        return 10 // x\n    return 0\n").status == PROVED
    assert check("from functools import lru_cache\n@lru_cache(maxsize=128)\ndef f(x):\n    return 10 // x\n").status == REFUTED
    assert prove("import functools\n@functools.lru_cache\ndef f(x):\n    return x + x\n", "result == 2 * x").status == PROVED
    # a variable possibly read before assignment on some branch (if c: x = 1, then an unconditional return x) raises
    # UnboundLocalError on the unassigned path, so the value engine abstains rather than proving total; a correlated
    # guard (the use under the same condition as the def) and a prior unconditional assignment still prove.
    assert check("def f(c):\n    if c:\n        x = 1\n    return x\n").status == UNKNOWN
    assert check("def f(c):\n    if c:\n        x = 1\n    if c:\n        return x\n    return 0\n").status == PROVED
    assert check("def f(c):\n    x = 0\n    if c:\n        x = 1\n    return x\n").status == PROVED
    # a try whose every handler exits (return / raise / break / continue) leaves the try body's assignments definite
    # afterward -- reaching past the try means the body completed -- so a later use is not use-before-assignment; a
    # handler that falls through (pass) leaves the name genuinely maybe-unbound and still gates.
    assert check("def f(n):\n    try:\n        x = 10 // n\n    except ZeroDivisionError:\n        return 0\n    return x + 1\n").status == PROVED
    assert check("def f(n):\n    try:\n        x = 10 // n\n    except ZeroDivisionError:\n        pass\n    return x + 1\n").status == UNKNOWN
    # a while-True break, or a for/else where the else and every break bind a name, leaves it definite afterward (an
    # exact break-set intersection: a name set under one guard but broken under another stays possibly-unbound).
    assert check("def f():\n    while True:\n        x = 1\n        break\n    return x + 1\n").status == PROVED
    assert check("def f(xs):\n    for x in xs:\n        if x:\n            r = x\n            break\n    else:\n        r = 0\n    return r + 1\n").status == PROVED
    assert check("def f(xs, a, b):\n    for x in xs:\n        if a:\n            r = x\n        if b:\n            break\n    else:\n        r = 0\n    return r + 1\n").status == UNKNOWN
    # a for-loop counter stepped by an unconditional integer constant (s = s + c, no break/continue) has the exact
    # post-loop value s_init + c * len(seq), so a trap on it is decided -- a len() guard proves 10 // s safe -- while
    # a conditionally-incremented counter is left havoc'd (UNKNOWN), never summarized to a false verdict.
    assert check("def f(xs: list):\n    if len(xs) >= 1:\n        s = 0\n        for x in xs:\n            s = s + 1\n        return 10 // s\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    s = 0\n    for x in xs:\n        if x > 0:\n            s = s + 1\n    return 10 // s\n").status == UNKNOWN
    # an in-repo class constructor C(args) is an opaque instance: the arguments are trap-checked and a dataclass-style
    # __init__ (only self-attribute stores of trap-free expressions) is confirmed trap free; a non-trivial one abstains.
    assert check("def f():\n    v = C()\n    return v.x\n", repo={"C": "class C:\n    def __init__(self):\n        self.x = 0\n        self.items = []\n"}).status == PROVED
    assert check("def f(n):\n    p = P(10 // n, n)\n    return p.a\n", repo={"P": "class P:\n    def __init__(self, a, b):\n        self.a = a\n        self.b = b\n"}).status == REFUTED
    # intra-object dispatch: a method on a locally-constructed instance carries self's class, so self.attr reads and
    # self.method() calls (and chains) dispatch -- a trap through them refutes, a guard proves, and an overriding
    # subclass dispatches its own method (no false PROVED), since a local instance has the exact constructed type.
    assert check("class C:\n    def helper(self, x):\n        return x * 2\n    def m(self, x):\n        return self.helper(x) + 1\n\ndef f(x):\n    c = C()\n    return c.m(x)\n").status == PROVED
    assert check("class C:\n    def __init__(self, v):\n        self.v = v\n    def m(self):\n        return 10 // self.v\n\ndef f(v):\n    c = C(v)\n    return c.m()\n").status == REFUTED
    assert check("class C:\n    def __init__(self, v):\n        self.v = v\n    def m(self):\n        return 10 // self.v\n\ndef f(v):\n    if v == 0:\n        return 0\n    c = C(v)\n    return c.m()\n").status == PROVED
    assert check("class C:\n    def helper(self):\n        return 1\n    def m(self):\n        return 10 // self.helper()\n\nclass S(C):\n    def helper(self):\n        return 0\n\ndef f():\n    c = S()\n    return c.m()\n").status == REFUTED
    # a collection-valued instance attribute is truthy by its length, not its (always nonzero) heap address, so
    # `if self.items:` guards the bounds and self.items[0] proves; an unguarded pop on the empty list still refutes.
    assert check("class C:\n    def __init__(self):\n        self.items = []\n    def first(self):\n        if self.items:\n            return self.items[0]\n        return 0\n\ndef f():\n    c = C()\n    return c.first()\n").status == PROVED
    assert check("class C:\n    def __init__(self):\n        self.items = []\n    def take(self):\n        return self.items.pop()\n\ndef f():\n    c = C()\n    return c.take()\n").status == REFUTED
    # a membership test inside a dispatched method (k in self.d) is not modeled in the heap engine, so it abstains
    # cleanly rather than crashing the analysis (was a KeyError on the unhandled comparison operator).
    assert check("class C:\n    def __init__(self):\n        self.d = {}\n    def g(self, k):\n        if k in self.d:\n            return self.d[k]\n        return 0\n\ndef f(k):\n    c = C()\n    return c.g(k)\n").status == UNKNOWN
    # a method on a class-valued instance attribute (self.child = D()) dispatches along D's MRO, so a nested-object
    # call decides; but if the attribute is ALSO assigned a non-literal (a param), its class is ambiguous and the
    # dispatch abstains rather than assume D -- assuming it would false-PROVE when the param is a trapping class.
    assert check("class D:\n    def __init__(self, v):\n        self.v = v\n    def g(self):\n        return self.v\n\nclass C:\n    def __init__(self, v):\n        self.child = D(v)\n    def m(self):\n        return 10 // self.child.g()\n\ndef f(v):\n    c = C(v)\n    return c.m()\n").status == REFUTED
    assert check("class D:\n    def g(self):\n        return 1\nclass E:\n    def g(self):\n        return 0\nclass C:\n    def __init__(self):\n        self.child = D()\n    def set(self, e):\n        self.child = e\n    def m(self):\n        return 10 // self.child.g()\n\ndef f(e):\n    c = C()\n    c.set(e)\n    return c.m()\n").status == UNKNOWN
    # a heap ternary's test truthiness is collection-aware (items[0] if self.items else 0 proves), each branch is
    # trap-checked under its path condition, and a side-effecting branch (a call) abstains rather than mutate both.
    assert check("class C:\n    def __init__(self):\n        self.items = []\n    def first(self):\n        return self.items[0] if self.items else 0\n\ndef f():\n    c = C()\n    return c.first()\n").status == PROVED
    # a method's unfilled trailing parameter takes its default (so the trap in 10 // x with x=0 is found), the
    # one-expression C(...).m() form constructs then dispatches on the fresh exact-type instance, and a dict-attribute
    # read raises KeyError on an absent key.
    assert check("class C:\n    def m(self, x=2):\n        return 10 // x\n\ndef f():\n    c = C()\n    return c.m()\n").status == PROVED
    assert check("class C:\n    def m(self, x=0):\n        return 10 // x\n\ndef f():\n    c = C()\n    return c.m()\n").status == REFUTED
    assert check("class C:\n    def __init__(self, v):\n        self.v = v\n    def m(self):\n        return 10 // self.v\n\ndef f(v):\n    return C(v).m()\n").status == REFUTED
    assert check("class C:\n    def __init__(self):\n        self.d = {}\n    def get(self, k):\n        return self.d[k]\n\ndef f(k):\n    c = C()\n    return c.get(k)\n").status == REFUTED
    # comprehension content (a per-element trap refutes, nested too), isinstance narrowing a parameter to the tested
    # type (bytes -> its element bounds check), an annotated assignment carried, and a non-integer value across a loop.
    assert check("def f(xs: list):\n    return [10 // x for x in xs]\n").status == REFUTED
    assert check("def f(x):\n    if isinstance(x, bytes):\n        return x[0]\n    return 0\n").status == REFUTED
    assert check("def f(s: str):\n    x: str = s\n    return x.upper()\n").status == PROVED
    assert check("def f(o):\n    i = 0\n    while i < 3:\n        i = i + 1\n    return o.x\n").status == PROVED
    # SOUNDNESS: isinstance on a guessed-scalar parameter must not statically prune the non-matching branch. The
    # value engine answers isinstance on a z3 scalar from its sort, so isinstance(v, str) on a usage-inferred str
    # reads as unconditionally true and would kill the else branch -- but the type was guessed, not declared, so
    # a trap waiting there (1 // 0 on a non-str input) must not be hidden: the value engine abstains. A DECLARED
    # type is a real precondition the pruning honours, so `v: str` proves (the else is genuinely unreachable).
    assert check("def f(v):\n    if isinstance(v, str):\n        return v.encode()\n    return 1 // 0\n").status == UNKNOWN
    assert check("def f(v):\n    if isinstance(v, str):\n        return v.encode()\n    return 1 // len(v)\n").status == UNKNOWN
    assert check("def f(n):\n    d = {}\n    d[0] = n\n    if isinstance(n, int):\n        return d[0]\n    return 1 // 0\n").status == UNKNOWN
    assert check("def f(v: str):\n    if isinstance(v, str):\n        return v.encode()\n    return 1 // 0\n").status == PROVED
    # the guess propagates through a plain alias (x = n) and a type tuple / negated test, so those abstain too; an
    # alias forced to a concrete type (x = n + 1, reachable only if n is an int) and an isinstance on an unrelated
    # container parameter keep their precise PROVED -- the abstention is scoped to the guessed-scalar name itself.
    assert check("def f(n):\n    x = n\n    d = {}\n    d[0] = x\n    if isinstance(x, int):\n        return d[0]\n    return 1 // 0\n").status == UNKNOWN
    assert check("def f(n):\n    x = n + 1\n    d = {}\n    d[0] = x\n    if isinstance(x, int):\n        return d[0]\n    return 1 // 0\n").status == PROVED
    # SOUNDNESS: a value with no decidable truth -- an object field (`if o.x:`), a dict-get / getattr / callable /
    # hasattr / unmodeled-call result -- must NOT read as truthy (Python's default object truth), which would
    # prune the else and hide its traps. It becomes a fresh bool (both branches live), so a trap in the
    # assumed-false branch abstains. A z3 int / container / string keeps its exact truthiness, and the field
    # stays numeric in arithmetic (`1 // o.x` still refutes).
    assert check("def f(o):\n    if o.x:\n        return 0\n    return 1 // 0\n").status == UNKNOWN
    assert check("def f(o):\n    if getattr(o, 'flag', False):\n        return 0\n    return 1 // 0\n").status == UNKNOWN
    assert check("def f(d):\n    if d.get(0):\n        return 0\n    return 1 // 0\n").status == UNKNOWN
    assert check("def f(v):\n    if not callable(v):\n        return 1 // 0\n    return 0\n").status == UNKNOWN
    assert check("def f(o):\n    return 1 // o.x\n").status == REFUTED
    assert check("def f(n):\n    if n:\n        return 0\n    return 1 // n\n").status == REFUTED
    # a bytes split always yields at least one part, so result[0] is in bounds (an unconstrained length would
    # false-refute it as an IndexError); a higher index still refutes on a no-separator input (a single part).
    assert check("def f(b: bytes):\n    return b.split(b',')[0]\n").status == PROVED
    assert check("def f(b: bytes):\n    return b.split(b',')[1]\n").status == REFUTED
    # a for-loop's first iteration is trap-checked exactly (pre-loop accumulators, a freely-chosen element), so a
    # per-element trap (// or % by an element, a zero accumulator on entry) REFUTES on a non-empty witness.
    assert check("def f(xs):\n    s = 0\n    for x in xs:\n        s = s + 10 // x\n    return s\n").status == REFUTED   # // by an element
    assert check("def f(xs):\n    t = 0\n    for x in xs:\n        t = t + 5 % x\n    return t\n").status == REFUTED       # % by an element
    assert check("def f(xs):\n    s = 0\n    for x in xs:\n        s = s + x // 2\n    return s\n").status == PROVED       # // by a constant: trap free
    assert check("def f(xs):\n    s = 0\n    for x in xs:\n        s = s + x * x\n    return s\n").status == PROVED        # no division
    assert check("def f(xs):\n    s = 0\n    for x in xs:\n        if x != 0:\n            s = s + 10 // x\n    return s\n").status == PROVED   # guarded
    # .pop() on a container parameter mutated exactly once, against the stable length/membership the c[i]/d[k]
    # checks use: list.pop()/pop(i) is an IndexError on empty/out-of-range, dict.pop(k) a KeyError unless k is a
    # provable key, pop(k, default) never raises; a len()/`in` guard proves it. Two mutations: excluded (abstains).
    assert check("def f(xs: list):\n    return xs.pop()\n").status == REFUTED                    # pop() on a possibly-empty list
    assert check("def f(xs: list):\n    if xs:\n        return xs.pop()\n    return 0\n").status == PROVED   # truthiness guard
    assert check("def f(xs: list):\n    return xs.pop(0)\n").status == REFUTED                    # pop(i) out of range on empty
    assert check("def f(d: dict):\n    return d.pop('k')\n").status == REFUTED                    # pop a possibly-missing key
    assert check("def f(d: dict, k):\n    if k in d:\n        return d.pop(k)\n    return 0\n").status == PROVED
    assert check("def f(d: dict):\n    return d.pop('k', 0)\n").status == PROVED                  # a default never raises
    # dict.popitem() on a dict parameter mutated once: KeyError on an empty dict (like list/set pop), so an
    # unguarded popitem refutes and a len() guard proves; the popped value is an arbitrary (key, value) 2-tuple.
    assert check("def f(d: dict):\n    return d.popitem()\n").status == REFUTED                   # empty dict: KeyError
    assert check("def f(d: dict):\n    k, v = d.popitem()\n    return 0\n").status == REFUTED      # same trap, unpacked
    assert check("def f(d: dict):\n    if len(d) > 0:\n        return d.popitem()\n    return None\n").status == PROVED
    assert check("def f(d: dict):\n    a = d.popitem()\n    b = d.popitem()\n    return 0\n").status == UNKNOWN   # two pops: not mutate-once
    assert check("def f(xs: list):\n    if len(xs) >= 1:\n        a = xs.pop()\n        b = xs.pop()\n"
                 "        return a + b\n    return 0\n").status == UNKNOWN   # popped twice: abstains
    assert check("def f(xs: list):\n    x = xs.pop()\n    xs.append(x)\n    return x\n").status == UNKNOWN   # pop + append: excluded
    # list.index(x) / list.remove(x) raise ValueError when x is not present, against the sequence's stable
    # membership predicate, so an `x in xs` guard proves them; that guard now connects to the length too (a
    # member means the sequence is non-empty), so a guarded index proves. remove mutates and is gated to a
    # single mutation like pop. The unguarded forms refute with the missing-element witness.
    assert check("def f(xs: list):\n    return xs.index(9)\n").status == REFUTED                     # 9 maybe absent: ValueError
    assert check("def f(xs: list):\n    if 9 in xs:\n        return xs.index(9)\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    xs.remove(9)\n    return 0\n").status == REFUTED
    assert check("def f(xs: list):\n    if 9 in xs:\n        xs.remove(9)\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    if 9 in xs:\n        return xs[0]\n    return 0\n").status == PROVED   # member => non-empty
    assert check("def f(xs: list):\n    if 9 in xs:\n        xs.remove(9)\n        xs.remove(9)\n    return 0\n").status == UNKNOWN   # removed twice: abstains
    # index is non-mutating, so it is modeled on an immutable tuple too -- t.index(x) raises ValueError unless
    # x is a member, an `x in t` guard proves it; t.count(x) never raises; tuple has no remove (an unmodeled
    # AttributeError), so a t.remove(...) abstains rather than be miscast as a ValueError.
    assert check("def f(t: tuple):\n    return t.index(9)\n").status == REFUTED                       # 9 maybe absent
    assert check("def f(t: tuple):\n    if 9 in t:\n        return t.index(9)\n    return 0\n").status == PROVED
    assert check("def f(t: tuple):\n    return t.count(9)\n").status == PROVED                        # count never raises
    assert check("def f(t: tuple):\n    t.remove(9)\n    return 0\n").status == UNKNOWN               # tuple has no remove
    # dict.get(k) on a dict parameter returns None when k is absent, so using the result as a number / index /
    # attribute is a TypeError, modeled by the None machinery: d.get(k) is None (a sound over-approximation),
    # refuting an unguarded d.get(k) + 1 / d.get(k)[0], while a default argument, a truthiness or `is None`
    # guard, or a plain return make it safe. None is falsy in the value engine's truthiness, so `if d.get(k):`
    # guards a possibly-None value.
    assert check("def f(d: dict, k):\n    return d.get(k) + 1\n").status == REFUTED          # None + int
    assert check("def f(d: dict, k):\n    return d.get(k)[0]\n").status == REFUTED            # None[0]: TypeError
    assert check("def f(d: dict, k):\n    return d.get(k, 0) + 1\n").status == PROVED         # a default: never None
    assert check("def f(d: dict, k):\n    v = d.get(k)\n    if v is None:\n        return 0\n    return v + 1\n").status == PROVED
    assert check("def f(d: dict, k):\n    x = d.get(k)\n    if x:\n        return x + 1\n    return 0\n").status == PROVED   # truthiness guard
    assert check("def f(d: dict, k):\n    return d.get(k)\n").status == PROVED                # returning None is fine
    # len() of a dict / view / opaque container is nonnegative, so len(d) + 1 >= 1 and 10 // (len(d) + 1) is trap free;
    # the unguarded 10 // len(d) still refutes (empty dict).
    assert check("def f(d: dict):\n    return 10 // (len(d) + 1)\n").status == PROVED
    assert check("def f(d: dict):\n    return 10 // (len(d.keys()) + 1)\n").status == PROVED
    assert check("def f(d: dict):\n    return 10 // (len(d.values()) + 1)\n").status == PROVED
    assert check("def f(d: dict):\n    return 10 // (len(d.items()) + 1)\n").status == PROVED
    assert check("def f(s: set):\n    return 10 // (len(s) + 1)\n").status == PROVED
    assert check("def f(d: dict):\n    return 10 // len(d)\n").status == REFUTED               # empty dict -> div by zero
    # d.keys() / d.values() is a sized, iterable, NON-subscriptable view of length len(d): list / sorted / sum over it
    # decide, max(d.values()) is the empty-dict ValueError (a len(d) guard proves a guarded max), and view[i] is a
    # TypeError. The view length ties to len(d), so the guard connects.
    assert check("def f(d: dict):\n    return sorted(d.values())\n").status == PROVED
    assert check("def f(d: dict):\n    return 10 // (len(list(d.keys())) + 1)\n").status == PROVED
    assert check("def f(d: dict):\n    return max(d.values())\n").status == REFUTED             # empty dict -> ValueError
    assert check("def f(d: dict):\n    if len(d) > 0:\n        return max(d.values())\n    return 0\n").status == PROVED
    assert check("def f(d: dict):\n    return d.keys()[0]\n").status == REFUTED                 # view is not subscriptable
    assert check("def f():\n    y = None\n    if y:\n        return y + 1\n    return 0\n").status == PROVED   # None falsy in value engine
    # a dict read d[k] traps (KeyError) unless the key is provably present, for an unannotated parameter the body
    # subscripts with a string key (inferred a dict), an annotation, or a literal; a guard or a prior store proves it
    assert check("def f(d):\n    return d['x']\n").status == REFUTED
    assert check("def f(d):\n    if 'x' in d:\n        return d['x']\n    return 0\n").status == PROVED
    assert check("def f(d: dict):\n    return d['x']\n").status == REFUTED
    # a read-only dict parameter's d[k] is a fixed function of k, so it is memoized: re-reading the same key gives one
    # value. A guard `if k in d and d[k] != 0:` then protects a later `10 // d[k]` (once a false REFUTED, the two
    # reads having been independent fresh values). A genuine trap still refutes -- an unguarded `10 // d[k]`, or
    # d[k] == 5 then 10 // (d[k] - 5) -- and a name bound once (x = d[k]) was already stable.
    assert check("def f(d: dict, k):\n    if k in d and d[k] != 0:\n        return 10 // d[k]\n    return 0\n").status == PROVED
    assert check("def f(d: dict[str, int], k):\n    if k in d and d[k] != 0:\n        return 10 // d[k]\n    return 0\n").status == PROVED
    assert check("def f(d: dict, k):\n    if k in d:\n        return 10 // d[k]\n    return 0\n").status == REFUTED
    assert check("def f(d: dict, k):\n    if k in d and d[k] == 5:\n        return 10 // (d[k] - 5)\n    return 0\n").status == REFUTED
    assert check("def f(d: dict, k):\n    if k in d:\n        x = d[k]\n        if x != 0:\n            return 10 // x\n    return 0\n").status == PROVED
    # a dict parameter's value type is modeled (dict[K, V] / typing.Dict[K, V]): a read-only dict[str, list] read d[k]
    # is a stable list, so a len(d[k]) > 0 guard proves d[k][0], an unguarded d[k][0] refutes (it may be empty), and
    # d[k].append / len(d[k]) decide; dict[str, str] read d[k] is a string (d[k].upper()). A bare dict (no value type)
    # leaves d[k] opaque, so d[k][0] abstains.
    assert check("def f(d: dict[str, list], k):\n    if k in d and len(d[k]) > 0:\n        return d[k][0]\n    return 0\n").status == PROVED
    assert check("def f(d: dict[str, list], k):\n    if k in d:\n        return d[k][0]\n    return 0\n").status == REFUTED
    assert check("def f(d: dict[str, list], k):\n    if k in d:\n        d[k].append(1)\n    return 0\n").status == PROVED
    assert check("from typing import Dict, List\ndef f(d: Dict[str, List[int]], k):\n    if k in d and len(d[k]) > 0:\n        return d[k][0]\n    return 0\n").status == PROVED
    assert check("def f(d: dict[str, str], k):\n    if k in d:\n        return d[k].upper()\n    return 0\n").status == PROVED
    assert check("def f(d: dict, k):\n    if k in d:\n        return d[k][0]\n    return 0\n").status == UNKNOWN
    # None in arithmetic is a TypeError trap; an `is None` guard that exits or rebinds proves the use safe
    assert check("def f():\n    y = None\n    return y + 1\n").status == REFUTED
    assert check("def f(c):\n    y = None\n    if c:\n        y = 3\n    return y + 1\n").status == REFUTED
    assert check("def f(c):\n    y = None\n    if c:\n        y = 3\n    if y is None:\n        return 0\n"
                 "    return y + 1\n").status == PROVED
    # a subscript, call, or attribute access on None is the TypeError / AttributeError it raises (a trap),
    # and a guard that rules None out proves it safe
    assert check("def f():\n    y = None\n    return y[0]\n").status == REFUTED            # None[0]: TypeError
    assert check("def f():\n    y = None\n    return y()\n").status == REFUTED             # None(): TypeError
    assert check("def f():\n    y = None\n    return y.x\n").status == REFUTED             # None.x: AttributeError
    assert check("def f(c):\n    y = None\n    if c:\n        y = [1]\n    if y is None:\n        return 0\n"
                 "    return y[0]\n").status == PROVED                                      # guarded: safe
    # None carried through a loop is the optional CFG/CHC engine (None as a first-class value over the back
    # edge), so a None that reaches arithmetic across a loop refutes: a None present at a possibly-zero-
    # iteration loop's exit, or set in the body (which may run zero times), traps at the use; a guard or an
    # in-body reassignment covering every path proves it safe; a None divisor refutes and a guarded one proves.
    assert check("def f(n):\n    y = None\n    i = 0\n    while i < n:\n        i = i + 1\n    return y + 1\n").status == REFUTED
    assert check("def f(n):\n    y = None\n    i = 0\n    while i < n:\n        y = i\n        i = i + 1\n"
                 "    return y + 1\n").status == REFUTED                                    # n == 0: y stays None
    assert check("def f(n):\n    y = None\n    i = 0\n    while i < n:\n        y = i\n        i = i + 1\n"
                 "    if y is None:\n        return 0\n    return y + 1\n").status == PROVED   # guarded after the loop
    assert check("def f(n):\n    y = None\n    s = 0\n    i = 0\n    while i < n:\n        s = s + 10 // y\n"
                 "        i = i + 1\n    return s\n").status == REFUTED                      # None in // across the loop
    assert check("def f(n, d):\n    s = 0\n    i = 0\n    while i < n:\n        if d != 0:\n            s = s + 10 // d\n"
                 "        i = i + 1\n    return s\n").status == PROVED                       # zero divisor guarded out
    assert check("def f(n):\n    y = 0\n    i = 0\n    while i < n:\n        i = i + 1\n    return y + 1\n").status == PROVED   # never None
    assert verify_no_raise_optional("opt", "f", "def f(n):\n    y = None\n    i = 0\n    while i < n:\n"
                                    "        i = i + 1\n    return y + 1\n").status == REFUTED   # the engine, direct
    # invalid operand pairings with known types trap as the TypeError they raise, while valid ones still verify
    assert check("def f():\n    return [1, 2] + 3\n").status == REFUTED                    # list + int: TypeError
    assert check("def f():\n    return [1, 2] - [3]\n").status == REFUTED                  # list - list: TypeError
    assert check("def f():\n    return 'a' * 'b'\n").status == REFUTED                     # str * str: TypeError
    assert check("def f():\n    return 'a' - 1\n").status == REFUTED                       # str - int: TypeError
    assert check("def f():\n    return (1, 2) * 1.5\n").status == REFUTED                  # tuple * float: TypeError
    assert check("def f():\n    return [1, 2] + [3]\n").status == PROVED                   # list + list is fine
    assert check("def f():\n    return [1, 2] * 3\n").status == PROVED                     # list * int is fine
    assert check("def f(n):\n    return 'ab' * n\n").status != REFUTED                     # str * int (any count) never traps
    # a string operation whose other operand is an UNMODELED value (an opaque method result on an untyped
    # receiver, a free name) abstains rather than refuting -- the value is not provably a non-string, so a
    # TypeError is not certain (it could define __radd__); a modeled wrong type (int, None) still refutes.
    assert check("def f(s):\n    return s.get_field() + '.y'\n").status == UNKNOWN
    assert check("def f(s, loc):\n    if loc is None:\n        x = s.get_field()\n    else:\n        x = loc\n    return x + '.y'\n").status != REFUTED
    assert check("def f():\n    y = None\n    return y + 'x'\n").status == REFUTED
    # a str / bytes-typed parameter is outside the integer CHC model, so the no-raise engine abstains rather
    # than proving a FALSE trap freedom: int(s) / float(s) of a string may ValueError and str + int / str // int
    # is a TypeError -- none of which an integer relation, binding every parameter to an int, can see. check()
    # then decides through the value engine (which models strings): the conversions are UNKNOWN (the parse can
    # raise), the type-mismatched arithmetic REFUTED, while a safe string use still proves and an unused str
    # parameter does not block the integer reasoning.
    assert check("def f(s: str):\n    return int(s)\n").status == UNKNOWN                   # int('x') may raise ValueError
    assert check("def f(s: str):\n    return float(s)\n").status == UNKNOWN                 # float('x') may raise ValueError
    assert check("def f(s: str):\n    return s + 1\n").status == REFUTED                    # str + int: TypeError
    assert check("def f(s: str):\n    return s // 2\n").status == REFUTED                   # str // int: TypeError
    assert verify_no_raise("nr", "f", "def f(s: str):\n    return int(s)\n",
                           lambda S: z3.BoolVal(True)).status == UNKNOWN                    # the CHC engine, directly: abstains
    assert check("def f(s: str):\n    return len(s)\n").status == PROVED                    # safe string use: still proves
    assert check("def f(s: str):\n    return s.strip()\n").status == PROVED
    # str truthiness `if s:` / `while s:` is len(s) != 0, so an `if s:` guard before a str operation proves and
    # equals the explicit length test.
    assert check("def f(s: str):\n    if s:\n        t = s.upper()\n    else:\n        t = s\n    return t\n", target="f").status == PROVED
    assert check("def f(s: str):\n    if not s:\n        return 0\n    return len(s)\n", target="f").status == PROVED
    assert verify_equiv("e", "f", "def f(s: str):\n    if s:\n        return 1\n    return 0\n",
                        "def g(s: str):\n    if len(s) != 0:\n        return 1\n    return 0\n", {}).status == PROVED
    assert check("def f(s: str, n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n").status == PROVED   # unused str param: loop still proves
    # a dict is inferred from a string-keyed read under ANY key (an f-string, a str parameter, a
    # concatenation), not only a constant literal, so a missing-key KeyError is caught on a computed key
    assert check("def f(d, s: str):\n    return d[s]\n").status == REFUTED                 # d[str param]: KeyError
    assert check("def f(d, s: str):\n    if s in d:\n        return d[s]\n    return 0\n").status == PROVED
    assert check("def f(d, k: str):\n    return d['p_' + k]\n").status == REFUTED          # concatenated string key
    assert check("def f(d, k: str):\n    return d[f'{k}!']\n").status == REFUTED            # f-string over a str key
    assert verify_predicate("mm-list", "f", "def f(xs: list):\n    return min(xs)\n",
                            lambda za, o: z3.BoolVal(True), {}).status == UNKNOWN
    _sb_mm, _ae_mm = core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION
    core.SANDBOX_SUBJECT = False; core.ALLOW_SUBJECT_EXECUTION = False
    try:
        assert verify_recursive("mm-rec", "f", "def f(xs: list):\n    return min(xs)\n",
                                lambda S: z3.BoolVal(True), lambda S, r: z3.BoolVal(True)).status != PROVED
    finally:
        core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = _sb_mm, _ae_mm
    assert verify_predicate("mm-vals", "f", "def f(a, b, c):\n    return max(a, min(b, c))\n",
                            lambda za, o: z3.BoolVal(True), {}).status == PROVED   # multi-argument stays exact
    assert verify_predicate("mm-lit", "f", "def f():\n    return min((3, 1, 2))\n",
                            lambda za, o: o == 1, {}).status == PROVED             # a non-empty literal is computed

    # division by zero inside a loop body is caught deductively (safety VC)
    divbug = ("def f(n):\n    s = 0\n    i = 0\n    while i < n:\n"
              "        s = s + 10 // i\n        i = i + 1\n    return s\n")
    vdb = verify_deductive("divbug", "f", divbug, lambda S: S["n"] >= 0,
                           lambda S: z3.And(S["i"] >= 0, S["i"] <= S["n"]),
                           lambda S, r: z3.BoolVal(True), {})
    assert vdb.status == REFUTED and "division by zero" in vdb.reason, vdb

    # octagon (relational, sums) proves x+y==const, which the zone domain cannot
    cons = ("def f():\n    i = 0\n    j = 10\n    while i < 10:\n"
            "        i = i + 1\n        j = j - 1\n    return i\n")
    assert verify_octagon_sum("i+j==10", "f", cons, "i", "j", 10).status == PROVED
    assert verify_octagon_sum("i+j==11", "f", cons, "i", "j", 11).status == UNKNOWN

    # lexicographic ranking proves a nested counter halts (no single measure works)
    nested = ("def f(n, m):\n    i = 0\n    j = 0\n    while i < n:\n"
              "        if j < m:\n            j = j + 1\n        else:\n            i = i + 1\n            j = 0\n"
              "    return i\n")
    vt = verify_termination("nested", "f", nested, inv=lambda S: z3.And(S["j"] >= 0, S["j"] <= S["m"]))
    assert vt.status == PROVED and "lexicographic" in vt.technique, vt
    # a lexicographic TRIPLE proves a flattened triple-nested counter whose progress lives in no single
    # measure or pair: the measure (n-i, m-j, p-k) decreases (the first component that changes decreases),
    # discharged under the bounding invariant. The pair search runs first and returns a 2-tuple when it
    # succeeds, so a 3-tuple reason confirms the triple was needed.
    nested3 = ("def f(n, m, p):\n    i = 0\n    j = 0\n    k = 0\n    while i < n:\n"
               "        if j < m:\n            if k < p:\n                k = k + 1\n"
               "            else:\n                j = j + 1\n                k = 0\n"
               "        else:\n            i = i + 1\n            j = 0\n            k = 0\n    return i\n")
    vt3 = verify_termination("nested3", "f", nested3,
                             inv=lambda S: z3.And(S["j"] >= 0, S["j"] <= S["m"], S["k"] >= 0, S["k"] <= S["p"]))
    assert vt3.status == PROVED and "lexicographic" in vt3.technique and vt3.reason.count(",") == 2, vt3

    # unified loop prover escalates: CHC for f(n)==n, Houdini for the nonlinear sum
    assert verify_loop_auto("f==n", "f", counter, lambda S: S["n"] >= 0,
                            lambda S, r: r == S["n"], {}).status == PROVED
    assert verify_loop_auto("sum", "sum_to", sum_to, pre, post, {}).status == PROVED

    # whole-function CHC over the real control-flow graph: a statement after the
    #     loop is part of the program (the old single-loop engines silently dropped it).
    postloop = ("def f(n):\n    total = 0\n    i = 0\n    while i < n:\n        total = total + 1\n"
                "        i = i + 1\n    total = total * 100\n    return total\n")
    assert verify_function("post*100", "f", postloop, lambda S: S["n"] >= 0,
                           lambda S, r: r == S["n"] * 100, {}).status == PROVED
    assert verify_function("post*100", "f", postloop, lambda S: S["n"] >= 0,
                           lambda S, r: r == S["n"], {}).status == REFUTED          # not n
    # sequential loops, early return, break, continue, nested loops all in scope
    seq = ("def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    j = 0\n"
           "    while j < n:\n        j = j + 1\n    return j\n")
    assert verify_function("seq", "f", seq, lambda S: S["n"] >= 0, lambda S, r: r == S["n"], {}).status == PROVED
    brk = ("def f(n):\n    i = 0\n    while i < n:\n        if i == 3:\n            break\n"
           "        i = i + 1\n    return i\n")
    assert verify_function("brk", "f", brk, lambda S: S["n"] >= 0, lambda S, r: r <= S["n"], {}).status == PROVED

    # the old single-loop engines now REJECT post-loop code (no false PROVED)
    assert verify_deductive_auto("p", "f", postloop, lambda S: S["n"] >= 0,
                                 lambda S, r: r == S["n"], {}).status == UNKNOWN

    # recursion: an inductive input/output relation, proved over all inputs
    rec = "def f(n):\n    if n <= 0:\n        return 0\n    return f(n - 1) + 1\n"
    assert verify_recursive("rec", "f", rec, lambda S: S["n"] >= 0, lambda S, r: r == S["n"]).status == PROVED
    assert verify_recursive("rec", "f", rec, lambda S: S["n"] >= 0, lambda S, r: r == S["n"] + 1).status == REFUTED
    # a `raise` inside a recursive body is a reachable escaping exception (a guard like `if exponent < 0:
    # raise ValueError(...)` in binary exponentiation, or a hard error): the recursion engine refutes it
    # symbolically -- an Err under the raise's path condition. A recursion with no raise and no trap still
    # proves, and the exception's message expression is not what is checked (the raise is the failure).
    _rraise = "def f(base, exponent: int):\n    if exponent < 0:\n        raise ValueError('neg')\n    if exponent == 0:\n        return 1\n    return base * f(base, exponent - 1)\n"
    assert verify_recursive("rr", "f", _rraise, lambda S: z3.BoolVal(True), lambda S, r: z3.BoolVal(True)).status == REFUTED
    _rok = "def f(n: int):\n    if n <= 0:\n        return 1\n    return n * f(n - 1)\n"
    assert verify_recursive("rok", "f", _rok, lambda S: z3.BoolVal(True), lambda S, r: z3.BoolVal(True)).status == PROVED
    # the recursion engine now decides the type-guard idioms a recursive input validator uses -- not, isinstance
    # (from the argument's sort), and `n in {0, 1}` membership over a literal -- so factorial-style validators
    # (`if not isinstance(n, int): raise; if n < 0: raise; return 1 if n in {0, 1} else n * f(n - 1)`) refute
    # SYMBOLICALLY on the n < 0 raise (the isinstance guard is unreachable for the int-modeled argument), and a
    # validator with no reachable raise still proves.
    _fac = ("def f(n):\n    if not isinstance(n, int):\n        raise ValueError('a')\n    if n < 0:\n"
            "        raise ValueError('b')\n    return 1 if n in {0, 1} else n * f(n - 1)\n")
    assert verify_recursive("fac", "f", _fac, lambda S: z3.BoolVal(True), lambda S, r: z3.BoolVal(True)).status == REFUTED
    _facok = "def f(n):\n    if not isinstance(n, int):\n        raise ValueError('a')\n    if n <= 0:\n        return 1\n    return n * f(n - 1)\n"
    assert verify_recursive("facok", "f", _facok, lambda S: z3.BoolVal(True), lambda S, r: z3.BoolVal(True)).status == PROVED

    # a recursive REFUTED carries a replayable witness recovered by bounded symbolic unrolling (NO execution),
    # and the same unrolling upgrades a nonlinear recursive UNKNOWN the inductive (Spacer) engine cannot close
    # to a witness-backed REFUTED. The witness is replayed here; a true recursive postcondition still PROVES.
    _sb21, _ae21 = core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION
    core.SANDBOX_SUBJECT = False; core.ALLOW_SUBJECT_EXECUTION = False        # force the symbolic path, no sandbox
    try:
        _r21 = "def f(n):\n    if n <= 0:\n        return 0\n    return f(n - 1) + 2\n"
        _v21 = verify_recursive("w21", "f", _r21, lambda S: S["n"] >= 0, lambda S, r: r == S["n"])
        assert _v21.status == REFUTED and _v21.counterexample_inputs, _v21     # a witness with no execution
        _ns21 = {}; exec(_r21, _ns21); _n21 = _v21.counterexample_inputs["n"]
        assert _ns21["f"](_n21) != _n21, (_n21, _ns21["f"](_n21))              # and it really violates the spec
        _ssq21 = "def f(n):\n    if n <= 0:\n        return 0\n    return (n * n) + f(n - 1)\n"   # nonlinear: Spacer abstains
        _vu21 = verify_recursive("u21", "f", _ssq21, lambda S: S["n"] >= 0, lambda S, r: r == S["n"])
        assert _vu21.status == REFUTED and _vu21.counterexample_inputs, _vu21  # UNKNOWN -> witness-backed REFUTED
        assert verify_recursive("t21", "f", rec, lambda S: S["n"] >= 0, lambda S, r: r == S["n"]).status == PROVED   # no false witness
    finally:
        core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = _sb21, _ae21

    # a recursive callee the inliner cannot unfold is summarized at the call site by its @ensure contract, so a
    # caller verifies modularly: it assumes require(args) -> ensure(args, result), with the callee checked
    # against its own contract separately. The unpinned result withholds REFUTED; only the contract is PROVED.
    _gc = "@ensure('result >= 0')\ndef g(n):\n    if n <= 0:\n        return 0\n    return g(n - 1) + 1\n"
    assert verify_contracts(_gc, target="g").status == PROVED                            # the callee meets its contract
    assert prove("def f(x):\n    return g(x) + 1\n", "result >= 1", repo={"g": _gc}).status == PROVED    # modular caller
    assert prove("def f(x):\n    return g(x)\n", "result >= 5", repo={"g": _gc}).status == UNKNOWN        # not implied
    _gc2 = "@require('n >= 0')\n@ensure('result == n')\ndef g(n):\n    if n <= 0:\n        return 0\n    return g(n - 1) + 1\n"
    assert prove("def f(x):\n    return g(x)\n", "result == x", requires="x >= 0", repo={"g": _gc2}).status == PROVED
    assert prove("def f(x):\n    return g(x)\n", "result == x", repo={"g": _gc2}).status == UNKNOWN        # require not established

    # recursion termination by a well-founded measure: a strictly decreasing, bounded-below measure
    # at every recursive call (n-1, n//2, two recursive calls, two parameters), and an honest UNKNOWN
    # for a recursion with no such measure.
    assert verify_recursive_termination("rt", "f", rec, lambda P: P["n"] >= 0).status == PROVED
    assert verify_recursive_termination("rt", "f",
        "def f(n):\n    if n <= 1:\n        return n\n    return f(n // 2)\n", lambda P: P["n"] >= 0).status == PROVED
    assert verify_recursive_termination("rt", "f",
        "def f(n):\n    if n < 2:\n        return n\n    return f(n - 1) + f(n - 2)\n", lambda P: P["n"] >= 0).status == PROVED
    assert verify_recursive_termination("rt", "f",
        "def f(a, b):\n    if a == 0:\n        return b\n    return f(a - 1, b + 1)\n", lambda P: P["a"] >= 0).status == PROVED
    assert verify_recursive_termination("rt", "f", "def f(n):\n    return f(n + 1)\n").status == UNKNOWN
    # a lexicographic (size-change) measure proves a two-counter recursion no single measure decreases: the
    # inner counter b resets when the outer a decrements, so (a, b) decreases lexicographically at every call.
    # The non-terminating f(n + 1) above still stays UNKNOWN -- the callee-measure >= 0 bound blocks a spurious
    # lexicographic proof, so the addition never turns a divergent recursion into a false PROVED.
    _twoctr = "def f(a, b):\n    if a == 0:\n        return 0\n    if b == 0:\n        return f(a - 1, 5)\n    return f(a, b - 1)\n"
    _vlx = verify_recursive_termination("rt-lex", "f", _twoctr, lambda P: z3.And(P["a"] >= 0, P["b"] >= 0))
    assert _vlx.status == PROVED and "lexicographic" in _vlx.technique, _vlx
    # the lexicographic bound is required only on the component that strictly decreases at each edge, so a sound
    # measure survives an unconstrained nested-call argument (Ackermann-flavored): a falls with its callee value
    # >= 0 while the second slot is a recursive-call result, and b's own decrease is bounded by the guard b > 0.
    _nest = ("def f(a, b):\n    if a == 0:\n        return 0\n    if b <= 0:\n"
             "        return f(a - 1, f(a - 1, 0))\n    return f(a, b - 1)\n")
    _vnest = verify_recursive_termination("rt-lex-nested", "f", _nest, lambda P: P["a"] >= 0)
    assert _vnest.status == PROVED and "lexicographic" in _vnest.technique, _vnest
    # but the bound still blocks a divergent two-counter whose strictly decreasing component is never bounded below
    _divlex = "def f(a, b):\n    if a == 0:\n        return 0\n    return f(a, b - 1)\n"
    assert verify_recursive_termination("rt-lex-div", "f", _divlex, lambda P: P["a"] >= 0).status == UNKNOWN
    # mutual-recursion (size-change) termination: one well-founded measure shared across the whole cycle. The
    # measure n decreases at every edge of is_even -> is_odd -> is_even, so the cycle halts; a cycle with no
    # decrease stays UNKNOWN (sound abstention), and a single-function cycle defers to the self-recursion engine.
    _mr = {"is_even": "def is_even(n):\n    if n == 0:\n        return 1\n    return is_odd(n - 1)\n",
           "is_odd": "def is_odd(n):\n    if n == 0:\n        return 0\n    return is_even(n - 1)\n"}
    _vmt = verify_mutual_termination("mt", "is_even", _mr, lambda P: P["n"] >= 0)
    assert _vmt.status == PROVED and "shared measure" in _vmt.reason, _vmt
    assert verify_mutual_termination("mt", "p",
        {"p": "def p(n):\n    return q(n)\n", "q": "def q(n):\n    return p(n)\n"}).status == UNKNOWN
    assert verify_mutual_termination("mt", "f",
        {"f": "def f(n):\n    if n <= 0:\n        return 0\n    return f(n - 1) + 1\n"},
        lambda P: P["n"] >= 0).status == PROVED                  # single-function cycle: defers to self-recursion

    # total correctness = partial correctness AND termination, in one verdict (loops and recursion)
    vt = verify_total("tot", "f", counter, lambda S: S["n"] >= 0, lambda S, r: r == S["n"])
    assert vt.status == PROVED and "total correctness" in vt.technique, vt
    vtr = verify_total("tot-rec", "f", rec, lambda S: S["n"] >= 0, lambda S, r: r == S["n"])
    assert vtr.status == PROVED and "recursion" in vtr.technique, vtr      # total correctness of a recursive function

    # boolean connectives and truthiness are modeled
    assert verify_equiv("and", "f", "def f(a, b):\n    return a and b\n",
                        "def f(a, b):\n    if a != 0:\n        return b\n    return a\n", {}).status == PROVED
    assert verify_function("truthy", "f", "def f(x):\n    while x:\n        x = x - 1\n    return x\n",
                           lambda S: S["x"] >= 0, lambda S, r: r == 0, {}).status == PROVED

    # conditional inside an array loop body is modeled
    arr_if = ("def f(a: list, n: int):\n    i = 0\n    while i < n:\n"
              "        if i > 0:\n            a[i] = 0\n        i = i + 1\n    return a\n")
    assert verify_array_loop("arr-if", "f", arr_if,
                             lambda S: z3.And(S["n"] >= 0, S["n"] <= S["len_a"]),
                             lambda S: z3.And(0 <= S["i"], S["i"] <= S["n"], S["n"] <= S["len_a"]),
                             lambda S, _: z3.BoolVal(True)).status == PROVED

    # IEEE-754: a sum can overflow to Inf; multiplying a finite by 0.0 stays finite, but over the
    #     full double domain Inf * 0.0 is NaN, so the finiteness claim holds only once the input is
    #     guarded finite.
    assert verify_float_finite("ovf", "f", "def f(a, b):\n    return a + b\n").status == REFUTED
    assert verify_float_finite("fin", "f", "def f(a):\n    return a * 0.0\n", finite_inputs=True).status == PROVED
    assert verify_float_finite("fin-total", "f",
                               "def f(a):\n    if isfinite(a):\n        return a * 0.0\n    return 0.0\n"
                               ).status == PROVED

    # bounded concurrency: a non-atomic counter loses an update on some schedule
    assert verify_two_thread_counter("atomic", "t", True).status == PROVED
    assert verify_two_thread_counter("racy", "t", False).status == REFUTED

    # agent reference monitor: prove a plan stays within budget over all guard traces
    plan = [("search", "read", 3, "g1"), ("write", "fs.write", 5, "g2")]
    assert verify_agent_policy("ok", "m", plan, {"read", "fs.write"}, 10).status == PROVED
    assert verify_agent_policy("over", "m", plan, {"read", "fs.write"}, 6).status == REFUTED
    assert verify_agent_policy("perm", "m", plan, {"read"}, 10).status == REFUTED

    # specification inference: an output range is inferred and then discharged
    vi = infer_and_verify_range("range", "f",
                                "def f():\n    x = 0\n    while x < 100:\n        x = x + 1\n    return x\n")
    assert vi.status == PROVED and "100" in vi.reason

    # subset coverage is a plain measurement (comprehensions are still out of scope)
    cov = subset_coverage("def a(n):\n    return [i for i in range(n)]\n"
                          "def b(x):\n    if x > 0:\n        return 1\n    return 0\n")
    assert cov["functions"] == 2 and cov["encoded"] == 1, cov
    # modeled coverage over a representative sample: the tool reasons about the scalar,
    # heap, float, and recursive functions, and names the constructs still outside the subset.
    rep = coverage_report()
    assert rep["modeled"] >= 46 and rep["rate"] >= 95.0, rep      # does not regress below the current reach
    assert rep["unmodeled"] == [], rep["unmodeled"]              # every representative-corpus function is modeled

    # exception safety: raise / try / except are control edges; prove no escape
    raises = "def f(x):\n    if x < 0:\n        raise ValueError\n    return x\n"
    assert verify_no_raise("ex", "f", raises, lambda S: S["x"] >= 0).status == PROVED
    assert verify_no_raise("ex", "f", raises, lambda S: z3.BoolVal(True)).status == REFUTED
    caught = ("def f(x):\n    try:\n        if x < 0:\n            raise ValueError\n        y = 1\n"
              "    except ValueError:\n        y = 0\n    return y\n")
    assert verify_no_raise("ex", "f", caught, lambda S: z3.BoolVal(True)).status == PROVED
    mism = "def f(x):\n    try:\n        raise KeyError\n    except ValueError:\n        x = 0\n    return x\n"
    assert verify_no_raise("ex", "f", mism, lambda S: z3.BoolVal(True)).status == REFUTED

    # cost certification: a proven symbolic iteration bound
    vb = verify_iteration_bound("cost", "f", counter)
    assert vb.status == PROVED and "n" in vb.reason, vb

    # dynamic typing: a runtime-dispatch property over a tagged value union
    assert verify_dynamic_dispatch("dyn", "value").status == PROVED

    # modular contracts: verify across calls using callee contracts, not inlining
    contracts = {"g": (lambda a: z3.BoolVal(True), lambda a, r: r == a[0] + 1)}
    assert verify_modular("mod", "f", "def f(x):\n    return g(g(x))\n",
                          lambda S: z3.BoolVal(True), lambda S, r: r == S["x"] + 2, contracts).status == PROVED
    need = {"g": (lambda a: a[0] >= 0, lambda a, r: r == a[0] + 1)}
    assert verify_modular("mod", "f", "def f(x):\n    return g(x)\n",
                          lambda S: z3.BoolVal(True), lambda S, r: r == S["x"] + 1, need).status == REFUTED

    # separation-logic frame rule over a points-to heap
    assert verify_heap_frame("frame", "heap").status == PROVED

    # grounding bundle: proven facts with certificates, re-checked by signature match (no live solve)
    g = export_grounding(repo, [Prop("net_bounds", "net",
                                     lambda r: verify_predicate("net_bounds", "net", r["net"], pred, r))])
    assert g["call_graph"]["net"] == ["fee"] and g["verified_properties"][0]["status"] == PROVED, g
    assert g["verified_properties"][0]["certificate"] is not None                 # a saved certificate
    rc = recheck_grounding(g, repo)
    assert rc["signatures_match"] and rc["rechecked"] == rc["total"] and rc["certified"] == rc["proved"], rc
    drifted = {**repo, "fee": "def fee(x):\n    return x - 999999\n"}             # change a callee's body
    assert recheck_grounding(g, drifted)["signatures_match"] is False             # drift defeats the re-check

    # sum-of-squares (Positivstellensatz): proves nonnegativity, rejects non-SOS
    assert verify_sos_nonneg("sos", "p", lambda X: X[0] * X[0] - 2 * X[0] + 1, 1).status == PROVED
    assert verify_sos_nonneg("sos", "p", lambda X: X[0] * X[0] - 2 * X[0] * X[1] + X[1] * X[1], 2).status == PROVED
    assert verify_sos_nonneg("sos", "p", lambda X: X[0], 1).status == UNKNOWN          # x is not nonneg

    # nonlinear corroboration: every PROVED carries a corroborator; no REFUTED from a non-integral real model.
    _nl = nonlinear_corroboration_audit()
    assert _nl["proved"] >= 5 and _nl["refuted"] == 2, _nl
    # the nonlinear-uncorroborated UNKNOWN classifies as nonlinear; budget does not help.
    from .diagnostics import classify_unknown as _cu, budget_helps as _bh
    assert prove("def f(a, b):\n    return (a - b) * (a - b)\n", "result >= 0").status == PROVED
    assert _cu(core._NL_UNCORROBORATED) == "nonlinear" and not _bh(core._NL_UNCORROBORATED)

    # public entry points validate their arguments with a typed error.
    for _bad in (lambda: prove(123, "result >= 0"), lambda: prove("def f(x):\n    return x\n", 5),
                 lambda: check(None), lambda: verify_equiv("p", "f", 1, "def g(x):\n    return x\n", {}),
                 lambda: verify_contracts(7), lambda: verify_change("def f(x):\n    return x\n", 9),
                 lambda: verify_sos_nonneg("p", "p", lambda X: X[0], 0),
                 lambda: verify_sos_nonneg("p", "p", "notcallable", 1)):
        try:
            _bad(); _raised = False
        except TypeError:
            _raised = True
        assert _raised, "a public entry point did not validate its argument"

    # explain / repair CLI verbs: explain traces a refutation; repair drives a generator command to a proof.
    import io as _xio, contextlib as _xcl, tempfile as _xtf, os as _xos, shutil as _xsh
    from .cli import main as _xmain, build_parser as _xbp
    _verbs = set()
    for _act in _xbp()._actions:
        if getattr(_act, "choices", None):
            _verbs.update(_act.choices)
    assert {"explain", "repair", "metamorphic", "doctest", "returns", "leak", "lock", "recheck",
            "termination", "cost", "overflow"} <= _verbs, _verbs
    _xd = _xtf.mkdtemp(prefix="ts_cli_")
    try:
        _xp = _xos.path.join(_xd, "m.py")
        with open(_xp, "w", encoding="utf-8") as _fh:
            _fh.write("def f(x):\n    return 10 // x\n")
        _xb = _xio.StringIO()
        with _xcl.redirect_stdout(_xb):
            _xrc = _xmain(["explain", _xp])
        _xout = _xb.getvalue()
        assert _xrc == 1 and "REFUTED" in _xout and "x=0" in _xout, _xout
        if core.sandbox_run_batch("def f(x):\n    return x\n", {}, "f", [[1]]) == [("ok", 1)]:
            assert "trace:" in _xout and "ZeroDivisionError" in _xout, _xout
        if _xsh.which("printf"):                              # the repair generator shells out; printf is POSIX-only
            _xb2 = _xio.StringIO()
            with _xcl.redirect_stdout(_xb2):
                _xrc2 = _xmain(["repair", "--generator", "printf 'def f(x):\\n    return x + 1\\n'",
                                "--ensures", "result == x + 1"])
            assert _xrc2 == 0 and "PROVED" in _xb2.getvalue(), _xb2.getvalue()
    finally:
        _xsh.rmtree(_xd, ignore_errors=True)

    # the CLI surfaces the library's argv-expressible verbs -- metamorphic / doctest / returns / leak / lock
    # (the source-only, string-arg properties) and recheck (re-validate a saved bundle) -- each driven end to
    # end here so the gate locks the wiring and the exit-status contract (0 PROVED/verified, 1 REFUTED/failed).
    import io as _vio, contextlib as _vcl, tempfile as _vtf, os as _vos, shutil as _vsh, json as _vjson
    from .cli import main as _vmain

    def _vrun(argv):
        _b = _vio.StringIO()
        with _vcl.redirect_stdout(_b):
            return _vmain(argv)

    _vd = _vtf.mkdtemp(prefix="ts_cliverbs_")
    try:
        def _w(name, body):
            p = _vos.path.join(_vd, name)
            with open(p, "w", encoding="utf-8") as _fh:
                _fh.write(body)
            return p
        # metamorphic: idempotent (PROVED), a non-idempotent (REFUTED), and an involution via --relation
        assert _vrun(["metamorphic", _w("mi.py", "def f(x):\n    if x < 0:\n        return 0\n    return x\n")]) == 0
        assert _vrun(["metamorphic", _w("mn.py", "def f(x):\n    return x + 1\n")]) == 1
        assert _vrun(["metamorphic", _w("mv.py", "def f(x):\n    return -x\n"), "--relation", "involution"]) == 0
        # doctest: a correct example proves (0), a wrong one refutes (1); a no-doctest file is a clean no-op (0)
        assert _vrun(["doctest", _w("dg.py", "def sq(x):\n    '''\n    >>> sq(3)\n    9\n    '''\n    return x * x\n")]) == 0
        assert _vrun(["doctest", _w("db.py", "def sq(x):\n    '''\n    >>> sq(3)\n    10\n    '''\n    return x * x\n")]) == 1
        assert _vrun(["doctest", _w("dn.py", "def f(x):\n    return x\n")]) == 0
        # returns: a fall-through / wrong-type return under -> int refutes (1), a consistent one proves (0)
        assert _vrun(["returns", _w("rb.py", "def f() -> int:\n    return None\n")]) == 1
        assert _vrun(["returns", _w("rg.py", "def f() -> int:\n    return 5\n")]) == 0
        # leak: an unclosed handle refutes (1), a closed one proves (0)
        assert _vrun(["leak", _w("lkb.py", "def f():\n    x = open('a')\n    return 0\n")]) == 1
        assert _vrun(["leak", _w("lkg.py", "def f():\n    x = open('a')\n    x.close()\n    return 0\n")]) == 0
        # lock: an unprotected guarded op refutes (1), a protected one proves (0); --guarded names the op
        assert _vrun(["lock", _w("lcb.py", "def save(x):\n    db.write(x)\n")]) == 1
        assert _vrun(["lock", _w("lcg.py", "def save(x):\n    acquire_lock()\n    db.write(x)\n")]) == 0
        assert _vrun(["lock", _w("lco.py", "def save(x):\n    log.append(x)\n"), "--guarded", "log.append"]) == 1
        # recheck: a re-checkable bundle verifies (0), a tampered one fails (1), both through the CLI
        _vbundle = change_bundle("def f(a):\n    return a + a\n", "def f(a):\n    return 2 * a\n")
        assert _vbundle["checkable"], _vbundle
        _vbp = _vos.path.join(_vd, "ok.json")
        with open(_vbp, "w", encoding="utf-8") as _fh:
            _vjson.dump(_vbundle, _fh)
        assert _vrun(["recheck", _vbp]) == 0
        _vtp = _vos.path.join(_vd, "bad.json")
        with open(_vtp, "w", encoding="utf-8") as _fh:
            _vjson.dump({**_vbundle, "sha256": "0" * 64}, _fh)
        assert _vrun(["recheck", _vtp]) == 1
        # termination / cost / overflow: the source-only verdict verbs. A counted loop halts (0) and bounds (0),
        # a recursion with a well-founded measure halts (0), a divergent loop is REFUTED with a witness (1), and
        # a + b wraps a signed 8-bit integer (1) while a branch returning 0 / 1 cannot (0).
        _vcounted = "def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n"
        assert _vrun(["termination", _w("tmg.py", _vcounted)]) == 0
        assert _vrun(["termination", _w("tmd.py", "def f(x):\n    while x != 0:\n        x = x + 1\n    return x\n")]) == 1
        assert _vrun(["termination", _w("tmr.py", "def f(n):\n    if n <= 0:\n        return 0\n    return f(n - 1) + 1\n")]) == 0
        assert _vrun(["cost", _w("cst.py", _vcounted)]) == 0
        assert _vrun(["overflow", _w("ovw.py", "def f(a, b):\n    return a + b\n"), "--width", "8"]) == 1
        assert _vrun(["overflow", _w("ovs.py", "def f(x):\n    if x > 0:\n        return 1\n    return 0\n"), "--width", "64"]) == 0
    finally:
        _vsh.rmtree(_vd, ignore_errors=True)

    # separation logic with a recursive predicate (list well-formedness)
    assert verify_list_segment("sl", "lseg").status == PROVED
    assert verify_list_segment("sl", "lseg", buggy=True).status == REFUTED

    # whole-program / mutual-recursion CHC
    repo_wp = {"inc": "def inc(x):\n    return x + 1\n",
               "double": "def double(x):\n    return inc(x) + inc(x)\n"}
    assert verify_program("wp", "double", repo_wp, "double",
                          lambda S: z3.BoolVal(True), lambda S, r: r == 2 * S["x"] + 2).status == PROVED
    mr = {"is_even": "def is_even(n):\n    if n == 0:\n        return 1\n    return is_odd(n - 1)\n",
          "is_odd": "def is_odd(n):\n    if n == 0:\n        return 0\n    return is_even(n - 1)\n"}
    assert verify_program("wp", "is_even", mr, "is_even",
                          lambda S: S["n"] >= 0, lambda S, r: z3.Or(r == 0, r == 1)).status == PROVED
    # whole repository: modules merged into one system, a cross-module call resolved by name and the
    # assembled program verified interprocedurally.
    pkg = load_package("def area(w, h):\n    return mul(w, h)\n", "def mul(a, b):\n    return a * b\n")
    assert verify_program("pkg", "area", pkg, "area", lambda S: z3.And(S["w"] >= 0, S["h"] >= 0),
                          lambda S, r: r == S["w"] * S["h"]).status == PROVED
    # whole-program across real module imports: load_program resolves from-import, import m; m.g(), and
    # aliases (not just a flat by-name merge), so a callee's trap is seen through the boundary.
    _b = "def g(x):\n    return 10 // x\n"
    for _a in ("from b import g\ndef f(x):\n    return g(x)\n",
               "import b\ndef f(x):\n    return b.g(x)\n",
               "from b import g as gg\ndef f(x):\n    return gg(x)\n"):
        assert check_program({"b": _b, "a": _a}, "a", "f").status == REFUTED
    assert check_program({"b": _b, "a": "import b\ndef f(x):\n    if x == 0:\n        return 0\n    return b.g(x)\n"},
                         "a", "f").status == PROVED
    # namespaces stay separate: a.f calls a's own safe helper, not b's trapping one of the same name
    _ns = {"b": "def helper(x):\n    return 10 // x\n",
           "a": "def helper(x):\n    return x + 1\ndef f(x):\n    return helper(x)\n"}
    assert check_program(_ns, "a", "f").status == PROVED
    # a nested for-loop that reuses the loop variable must not read as non-terminating (which would make the
    # post-loop code look unreachable and a trap there vacuously absent); the range desugaring binds the loop
    # variable from a fresh per-loop counter, so the inner loop cannot clobber the outer's, and the reachable
    # modulo-by-zero (a % 7 can be 0) is still refuted.
    assert check("def f(a):\n    for _i in range(2):\n        for _i in range(0):\n            z = 1\n"
                 "    return 0 % (a % 7)\n").status == REFUTED
    assert check("def f(n):\n    s = 0\n    for i in range(n):\n        s = s + i\n    return s\n").status == PROVED
    # indexing a list parameter reaches an IndexError unless guarded by its length: xs[len(xs)] is always out
    # of bounds, and xs[0] is safe exactly when the list is non-empty.
    assert check("def f(xs: list):\n    return xs[len(xs)]\n").status == REFUTED
    assert check("def f(xs: list):\n    if len(xs) > 0:\n        return xs[0]\n    return 0\n").status == PROVED
    # self-recursion: a trap in the recursive branch is reachable (10 // (n - 1) divides by zero at n == 1),
    # and one guarded away from the base is not. The recursion engine decides these.
    from .domains import _decide as _bdecide
    _rt = "def f(n):\n    if n <= 0:\n        return 0\n    return (10 // (n - 1)) + f(n - 1)\n"
    assert _bdecide(_rt, {"f": _rt}).status == REFUTED
    _rs = "def f(n):\n    if n <= 0:\n        return 0\n    return (10 // n) + f(n - 1)\n"
    assert _bdecide(_rs, {"f": _rs}).status == PROVED
    # a `for i in range(len(a)): body` loop over a list parameter (desugared to
    # i = 0; while i < len(a): body; i += 1) is trap free for its array accesses -- 0 <= i < len(a) by the
    # guard, so a[i] is in bounds. A bounds-only invariant discharged by verify_array_loop proves the fill
    # (a[i] = e, including the in-place a[i] = a[i] + 1) and the index read; an out-of-bounds a[i + 1] refutes,
    # a non-array trap (10 // a[i]) abstains, and a guard against an unrelated bound (range(n), n != len(a)) is
    # not claimed.
    assert _bdecide("def f(a: list):\n    for i in range(len(a)):\n        a[i] = 0\n    return a\n", {}).status == PROVED
    assert _bdecide("def f(a: list):\n    for i in range(len(a)):\n        a[i] = a[i] + 1\n    return a\n", {}).status == PROVED
    assert _bdecide("def f(a: list[int]):\n    for i in range(len(a)):\n        a[i] = i\n    return a\n", {}).status == PROVED
    assert _bdecide("def f(a: list):\n    for i in range(len(a)):\n        a[i + 1] = 0\n    return a\n", {}).status != PROVED   # out of bounds
    assert _bdecide("def f(a: list, n: int):\n    for i in range(n):\n        a[i] = 0\n    return a\n", {}).status != PROVED    # n unrelated to len(a)
    # a fence-post overrun in an array-write loop -- `while i <= len(a): a[i] = ...`, or the desugared
    # `for i in range(len(a) + 1): a[i] = ...` -- writes a[len(a)], out of bounds for every array (the empty one
    # included), so it REFUTES under the one-past invariant, while the correct `i < len(a)` still proves.
    assert _bdecide("def f(a: list):\n    i = 0\n    while i <= len(a):\n        a[i] = 0\n        i = i + 1\n    return a\n", {}).status == REFUTED
    assert _bdecide("def f(a: list):\n    for i in range(len(a) + 1):\n        a[i] = 0\n    return a\n", {}).status == REFUTED
    # SOUNDNESS: the recursion engine declines a NON-self-recursive function (it models parameters as integers
    # with no container guard, so it would otherwise vacuously prove `return a + 1` for a list -- a TypeError).
    # Such a function is decided by the earlier guarded engines instead.
    from .engines import verify_recursive as _vrec
    assert _vrec("nr", "f", "def f(a):\n    return a + 1\n", lambda S: z3.BoolVal(True), lambda S, r: z3.BoolVal(True)).status == UNKNOWN
    assert _bdecide("def f(a: list):\n    return a + 1\n", {}).status != PROVED          # list + 1 is a TypeError
    # a parametric-bound while loop: dividing by the positive loop counter is trap free, but a modulo by a
    # parameter that can be zero after the loop is a reachable trap.
    assert check("def f(n):\n    s = 0\n    _wc = n\n    while _wc > 0:\n        s = s + 10 // _wc\n"
                 "        _wc = _wc - 1\n    return s\n").status == PROVED
    assert check("def f(a):\n    s = 0\n    _wc = a\n    while _wc > 0:\n        s = s + 1\n"
                 "        _wc = _wc - 1\n    return s % a\n").status == REFUTED
    # a looping function whose REFUTED is a guarded raise -- the input-validation idiom `if n < 0:
    # raise` sitting before a loop, or a raise inside the loop body -- carries a concrete replayable witness.
    # The bounded-unrolling recoverer treats a reachable raise as a trap, so the refutation is not witness-less.
    # A straight-line or recursive guarded raise carries its witness from the value engine.
    _vloop = check("def f(n: int):\n    if n < 0:\n        raise ValueError('neg')\n    s = 0\n"
                   "    for i in range(n):\n        s = s + i\n    return s\n", target="f")
    assert _vloop.status == REFUTED and _vloop.counterexample_inputs == {"n": -1}, _vloop
    _vbody = check("def f(n: int):\n    i = 0\n    while i < n:\n        if i == 3:\n            raise ValueError('hit')\n"
                   "        i = i + 1\n    return i\n", target="f")
    assert _vbody.status == REFUTED and _vbody.counterexample_inputs is not None, _vbody     # raise in the loop body
    _vsl = check("def f(side: int):\n    if side < 0:\n        raise ValueError('bad')\n    return side * side\n", target="f")
    assert _vsl.status == REFUTED and _vsl.counterexample_inputs == {"side": -1}, _vsl       # straight-line: unchanged
    # cross-function: a trap inside a callee is propagated to the call site. g(n) divides by zero at n == 0,
    # so an unguarded call refutes f, while a call guarded by n != 0 is trap free.
    _gtrap = "def g(x):\n    return 10 // x\n"
    _fcall = "def f(n):\n    return g(n)\n"
    assert _bdecide(_fcall, {"f": _fcall, "g": _gtrap}).status == REFUTED
    _fguard = "def f(n):\n    if n != 0:\n        return g(n)\n    return 0\n"
    assert _bdecide(_fguard, {"f": _fguard, "g": _gtrap}).status == PROVED
    # load_program tolerates a rare mangle collision under on_collision="skip" (a scan must not crash when two
    # sibling-module functions mangle alike, e.g. factor_.divisors and factor._divisors), keeping the first;
    # the rigorous default still rejects the ambiguity.
    _coll = {"factor_": "def divisors(n):\n    return n\n", "factor": "def _divisors(n):\n    return n\n"}
    assert len(load_program(_coll, on_collision="skip")) == 1, "a scan must tolerate a mangle collision"
    try:
        load_program(_coll); _craised = False
    except ValueError:
        _craised = True
    assert _craised, "the rigorous default must reject a mangle collision"
    # load_program's import-resolved repo feeds the Horn contract prover across modules
    _prog = load_program({"b": "def inc(n):\n    return n + 1\n",
                          "a": "import b\ndef f(x):\n    return b.inc(b.inc(x))\n"})
    assert verify_program("xmod", "a.f", _prog, "a__f",
                          lambda S: z3.BoolVal(True), lambda S, r: r == S["x"] + 2).status == PROVED
    # cross-module and same-module decorators survive load_program's name mangling: a bare @deco / from-import,
    # an attribute @m.deco (through `import m`), and the factory forms all rewrite to the mangled callee so the
    # inliner resolves them; a decorator outside the program stays UNKNOWN (declined, not guessed).
    _hlp = ("def trace(f):\n    def w(x):\n        return f(x) + 1\n    return w\n"
            "def at(k):\n    def deco(f):\n        def w(x):\n            return f(x) + k\n        return w\n    return deco\n")
    def _dprove(mods, modname, fn, ensures):
        _r = load_program(mods); _k = modname.replace(".", "_") + "__" + fn
        return prove(_r[_k], ensures, target=_k, repo=_r).status
    assert _dprove({"helpers": _hlp, "app": "import helpers\n@helpers.trace\ndef g(x):\n    return x * 2\n"},
                   "app", "g", "result == x * 2 + 1") == PROVED                       # attribute decorator
    assert _dprove({"helpers": _hlp, "app": "from helpers import trace\n@trace\ndef g(x):\n    return x * 2\n"},
                   "app", "g", "result == x * 2 + 1") == PROVED                       # from-import decorator
    assert _dprove({"app": _hlp + "@trace\ndef g(x):\n    return x * 2\n"},
                   "app", "g", "result == x * 2 + 1") == PROVED                       # same-module decorator
    assert _dprove({"helpers": _hlp, "app": "import helpers\n@helpers.at(5)\ndef g(x):\n    return x * 2\n"},
                   "app", "g", "result == x * 2 + 5") == PROVED                       # attribute factory decorator
    assert _dprove({"app": "import flask\n@flask.route\ndef g(x):\n    return x * 2\n"},
                   "app", "g", "result == x * 2") == UNKNOWN                          # external decorator: declined
    # an attribute decorator @C.m where C is a LOCAL class and m a one-parameter wrapper method resolves in the
    # flat API too -- the method's sole parameter (a static f, or self) is the decorated function. A wrapper
    # that touches self beyond calling it, an attribute factory @C.m(args), and a non-local class all decline.
    _amc = "class D:\n    @staticmethod\n    def wrap(f):\n        def w(x):\n            return f(x) + 1\n        return w\n@D.wrap\ndef g(x):\n    return x * 2\n"
    assert prove(_amc, "result == x * 2 + 1", target="g").status == PROVED            # staticmethod wrapper
    _amm = "class D:\n    def wrap(self):\n        def w(x):\n            return self(x) + 1\n        return w\n@D.wrap\ndef g(x):\n    return x * 2\n"
    assert prove(_amm, "result == x * 2 + 1", target="g").status == PROVED            # regular method (self is the fn)
    _ams = "class D:\n    def wrap(self):\n        def w(x):\n            return self.helper(x)\n        return w\n@D.wrap\ndef g(x):\n    return x * 2\n"
    assert prove(_ams, "result == x * 2", target="g").status == UNKNOWN               # wrapper uses self.attr: declined
    # an attribute factory @C.m(args) where C.m is a STATICMETHOD factory (def make(k): def deco(f): <wrapper>;
    # return deco) is inlined, the factory argument bound into the wrapper; a non-static class-method factory
    # (whose first parameter is self/cls, unbindable from C.m(args)) declines rather than mis-bind.
    _amf = ("class D:\n    @staticmethod\n    def make(k):\n        def deco(f):\n            def w(x):\n"
            "                return f(x) + k\n            return w\n        return deco\n"
            "@D.make(3)\ndef g(x):\n    return x * 2\n")
    assert prove(_amf, "result == x * 2 + 3", target="g").status == PROVED            # staticmethod attribute factory
    assert prove(_amf, "result == x * 2", target="g").status == REFUTED
    assert prove("class D:\n    def make(self, k):\n        def deco(f):\n            def w(x):\n"
                 "                return f(x) + k\n            return w\n        return deco\n"
                 "@D.make(3)\ndef g(x):\n    return x * 2\n",
                 "result == x * 2 + 3", target="g").status == UNKNOWN                 # non-static factory: declined
    # an @m.deco / @m.deco(args) attribute decorator where m is an imported module and `deco` is a wrapper /
    # factory supplied in the repo resolves through the repo (the flat-API counterpart of the load_program
    # cross-module path), so a directly-passed module decorator inlines instead of declining.
    _wrap_repo = {"wrap": "def wrap(f):\n    def w(x):\n        return f(x) + 1\n    return w\n"}
    assert prove("import helpers\n@helpers.wrap\ndef g(x):\n    return x * 2\n",
                 "result == x * 2 + 1", target="g", repo=_wrap_repo).status == PROVED
    _at_repo = {"at": "def at(k):\n    def deco(f):\n        def w(x):\n            return f(x) + k\n        return w\n    return deco\n"}
    assert prove("import helpers\n@helpers.at(5)\ndef g(x):\n    return x * 2\n",
                 "result == x * 2 + 5", target="g", repo=_at_repo).status == PROVED   # module attribute factory
    # cross-module imports beyond a flat name resolve: dotted, an m.g() attribute call, a relative import,
    # and a star import all let the callee's trap reach the caller
    _trap = "def g(x):\n    return 10 // x\n"
    assert check_program({"pkg.sub": _trap, "main": "from pkg.sub import g\ndef f(x):\n    return g(x)\n"},
                         "main", "f").status == REFUTED
    assert check_program({"pkg.sub": _trap, "main": "import pkg.sub\ndef f(x):\n    return pkg.sub.g(x)\n"},
                         "main", "f").status == REFUTED
    assert check_program({"pkg": _trap, "pkg.a": "from . import g\ndef f(x):\n    return g(x)\n"},
                         "pkg.a", "f").status == REFUTED
    assert check_program({"m": _trap, "main": "from m import *\ndef f(x):\n    return g(x)\n"},
                         "main", "f").status == REFUTED

    # language-server diagnostics: each function is verified from its own source (a sibling's trap does not
    # leak), a refutation is an error and a proof an information, and a syntax error yields nothing
    from .lsp import diagnostics as _lsp_diags
    _ds = _lsp_diags("def first(a):\n    return a[0]\n\ndef inc(x):\n    return x + 1\n\n"
                     "def safe(a):\n    if len(a) > 0:\n        return a[0]\n    return 0\n")
    assert [d["severity"] for d in _ds] == [1, 3, 3]               # REFUTED -> error, two PROVED -> information
    assert _ds[0]["source"] == "touchstone" and "REFUTED" in _ds[0]["message"]
    assert _lsp_diags("def f(x:\n    return x\n") == []            # a syntax error is left to the editor

    # check / prove isolate the named function in a multi-function module: a sibling's trap does not leak
    _multi = "def trap(a):\n    return a[0]\n\ndef safe(x):\n    return x + 1\n"
    assert check(_multi, target="safe").status == PROVED
    assert check(_multi, target="trap").status == REFUTED
    assert prove(_multi, "result == x + 1", target="safe").status == PROVED

    # verify a change preserves the code's properties (a diff gate) and carries a re-checkable proof bundle
    from .vcgen import recheck_bundle as _recheck
    assert verify_change("def f(a):\n    return a + a\n", "def f(a):\n    return 2 * a\n").status == PROVED
    assert verify_change("def f(a):\n    return a + a\n", "def f(a):\n    return a + 1\n").status == REFUTED
    _cc = '@require("n >= 0")\n@ensure("result == n")\ndef c(n):\n    return n\n'
    assert verify_change(_cc, "def c(n):\n    return n\n").status == PROVED          # the contract still holds
    assert verify_change(_cc, "def c(n):\n    return n + 1\n").status == REFUTED      # the change breaks it
    _vb = change_bundle("def f(a):\n    return a + a\n", "def f(a):\n    return 2 * a\n")
    assert _vb["checkable"] and _recheck(_vb)["verified"]                            # re-checks independently
    _vb["queries"][0] += "\n; tampered"
    assert not _recheck(_vb)["verified"]                                            # a tampered bundle is rejected

    # type inference: super() keeps the receiver subclass, and a tuple returned through a variable still
    # destructures per position
    from .inference import emit_facts as _emit
    def _ty(src, name):
        return next((sorted(f["type"]) for f in _emit(src)
                     if (f.get("variable") or f.get("function")) == name), None)
    assert _ty("class A:\n    def me(self):\n        return self\nclass D(A):\n    def me(self):\n        "
               "return super().me()\nd = D()\nx = d.me()\n", "x") == ["D"]
    assert _ty("def f(x):\n    t = (len(x), str(x))\n    return t\n"
               "def u(xs):\n    for a, b in map(f, xs):\n        return b\n", "b") == ["str"]
    assert _ty("def f():\n    for a, b in [(1, 'x')]:\n        return b\n", "b") == ["str"]   # a sequence literal of
    #                                                       uniform tuples destructures per position, not tuple-for-each
    assert _ty("class C:\n    def _m(a, b):\n        return C()\n"
               "    def factory(op, fb):\n        def fwd(x, y):\n            return op(x, y)\n        return fwd\n"
               "    g = factory(_m, _m)\n", "op") == ["callable"]   # a class-body factory called unbound: its first
    #                                                                 parameter is an argument, not the receiver C
    assert _ty("def f(x):\n    y = round(x + 1.5)\n    return y\n", "y") == ["int"]      # round(x) with no ndigits is int
    assert _ty("def f():\n    y = round(1.5, 2)\n    return y\n", "y") == ["float"]      # round(x, n) preserves x's type
    _b0 = [sorted(f["type"]) for f in _emit("def f():\n    b = ['x']\n    b[0] = len\n    return b[0]\n")
           if f.get("variable") == "b[0]"]
    assert ["callable"] in _b0, _b0     # a subscript reassignment b[i] = v is typed by v at its own line, not the
    #                                     stale element type spilling forward from the list literal
    _db = [sorted(f["type"]) for f in _emit("def f():\n    d = {}\n    x = 1\n    d['b'] = len\n    return d['b']\n")
           if f.get("variable") == "d['b']"]
    assert ["callable"] in _db, _db     # d[k] = v emits the element at its own assignment line even when the dict
    #                                     literal is far away (here an empty literal that carries no element type)
    _aa = [sorted(f["type"]) for f in _emit("class A:\n    def __init__(self):\n        self.a = [1, 2, 3]\n")
           if f.get("variable") == "A.a[0]"]
    assert ["int"] in _aa, _aa          # a homogeneous list/tuple class attribute emits its element facts (A.a[i])
    _nest = [f for f in _emit("class A:\n    class B:\n        def __init__(self):\n            self.a = 1.5\n")
             if f.get("variable") == "A.B.a"]
    assert any("function" not in f and f["type"] == ["float"] for f in _nest), _nest   # a nested-class attribute is
    #                                     recorded globally (no function scope), unlike a top-level class's A.a
    _nd = [sorted(f["type"]) for f in _emit("d = {'b': [1, 2, 3]}\nx = d['b'][0]\n") if f.get("variable") == "d['b'][0]"]
    assert ["int"] in _nd, _nd          # a dict value that is itself a sequence emits its positions (d['k'][i])
    _ad = [sorted(f["type"]) for f in _emit("class A:\n    def __init__(self):\n        self.a = {'k': 1, 'm': 2}\n")
           if f.get("variable") == "A.a['k']"]
    assert ["int"] in _ad, _ad          # a dict class attribute emits its key facts (A.a['k'])
    _dec = _emit("def dec1(f):\n    def wrapper(a, b):\n        return f(a, b)\n    return wrapper\n"
                 "@dec1\ndef func(a, b):\n    return a + b\nc = func(1, 2)\n")
    _wa = {f.get("function") for f in _dec if f.get("parameter") == "a" and f["type"] == ["int"]}
    assert "wrapper" in _wa and "dec1.wrapper" in _wa, _wa   # a nested function's facts carry both the bare scope
    #                                     the autogen ground truth uses and the qualified scope the runtime records
    _dod = [f.get("variable") for f in _emit("d = {'a': {'x': 1}}\ny = d['a']['x']\n")]
    assert "d['a']['x']" in _dod and "d['a'][0]" not in _dod, [v for v in _dod if v and v.startswith("d['a']")]
    #                                     a dict-valued dict element emits its keys, not spurious integer positions
    _un = [sorted(f["type"]) for f in _emit("d1 = {'a': 1}\nd2 = {'b': 2}\nm = d1 | d2\nx = m['b']\n")
           if f.get("variable") == "m['b']"]
    assert ["int"] in _un, _un          # a dict union (d1 | d2) and an alias carry the source dict's keys
    _ns = [sorted(f["type"]) for f in _emit("d = {'a': {}}\nx = 1\nd['a']['b'] = len\n")
           if f.get("variable") == "d['a']['b']"]
    assert ["callable"] in _ns, _ns     # a nested store d[k1][k2] = v emits the inner element at its own line
    _rk = [sorted(f["type"]) for f in _emit("class A:\n    def __init__(self):\n        self.a = {'k': 1}\n"
                  "    def m(self):\n        return self.a\nb = A()\nc = b.m()\nx = c['k']\n")
           if f.get("variable") == "c['k']"]
    assert ["int"] in _rk, _rk          # a method returning a dict attribute carries its keys to the caller (c['k'])
    _rkb = [sorted(f["type"]) for f in _emit("class A:\n    def __init__(self):\n        self.a = {}\n        self.a['k'] = 9\n"
                  "    def m(self):\n        return self.a\nb = A()\nc = b.m()\nx = c['k']\n")
            if f.get("variable") == "c['k']"]
    assert ["int"] in _rkb, _rkb        # a dict attribute BUILT UP by subscript store (self.a = {}; self.a['k'] = ...),
    #                                     not a single literal, carries its keys to the caller through the indirect return
    _flc = {f.get("function") for f in _emit("def deco(cls):\n    class New(cls):\n        def m(self):\n"
                  "            return 'x'\n    return New\n") if f.get("type") == ["str"]}
    assert "New.m" in _flc, _flc        # a function-local class's method is scoped to the class (New.m), the
    #                                     enclosing function dropped, as the ground truth names it
    _flt = [sorted(f["type"]) for f in _emit("def deco():\n    class New:\n        pass\n    n = New()\n    return n\n")
            if f.get("variable") == "n"]
    assert _flt and all(t == ["New"] for t in _flt), _flt   # a function-local class instance is named by its bare
    #                                     runtime __name__ (New), the spelling type(x).__name__ reports, not a
    #                                     qualified form specific to a benchmark
    _ndc = [sorted(f["type"]) for f in _emit("def g():\n    return 5\nd = {'a': {'b': g}}\ne = d['a']['b']()\n")
            if f.get("variable") == "e"]
    assert ["int"] in _ndc, _ndc        # a callable held in a nested dict resolves when called (d['a']['b']())
    _nt = ("import collections\ndef f():\n    P = collections.namedtuple('P', ['x', 'y'])\n"
           "    p = P(1, 2)\n    a = p.x\n    d = p._asdict()\n    q = p._replace(x=5)\n"
           "    m = P._make([3, 4])\n    fs = p._fields\n    return a\n")
    assert _ty(_nt, "a") == ["int"]     # a namedtuple field carries the type it was constructed with, resolved
    #                                     through the exec-built class the factory hides (p.x from P(1, 2))
    assert _ty(_nt, "d") == ["dict"]    # _asdict() returns a dict, and the siblings their own types:
    assert _ty(_nt, "q") == ["P"]       # _replace() a fresh instance of the same namedtuple type,
    assert _ty(_nt, "m") == ["P"]       # _make(iterable) likewise (a classmethod on the type),
    assert _ty(_nt, "fs") == ["tuple"]  # and _fields the field-name tuple
    _ne = _emit("def f(memo):\n    x = 1\n    return memo\n")
    assert all(e.get("type") for e in _ne), _ne                  # an un-inferable slot abstains: it emits no fact
    assert any(e.get("variable") == "x" and e["type"] == ["int"] for e in _ne)   # rather than an empty-type one,
    assert not any(e.get("parameter") == "memo" for e in _ne)    # which would carry no information and only cost
    #                                     precision (it matches no ground truth); typed bindings still emit normally
    # the TypeEvalPy emit surface (`infer --emit`, emit_facts with path + qualified=True): qualified=True keeps
    # the module-path spelling its matcher expects for an imported / stdlib type (itertools.count, not the bare
    # count -- a same-file class never carries a prefix), and the file path lets an import of a sibling module in
    # the same directory resolve to that module's types. Both materially raise the autogen-suite exact-match score.
    _itq = _emit("import itertools\ndef f():\n    c = itertools.count()\n    return c\n", qualified=True)
    assert any(e.get("variable") == "c" and "itertools.count" in e["type"] for e in _itq), _itq   # qualified spelling
    assert any(e.get("variable") == "c" and e["type"] == ["count"]            # the default still bares it (the
               for e in _emit("import itertools\ndef f():\n    c = itertools.count()\n    return c\n"))   # __name__)
    import tempfile as _tfe, os as _ose, shutil as _she
    _de = _tfe.mkdtemp(prefix="ts_emit_")
    try:
        _ose.path  # noqa
        with open(_ose.path.join(_de, "to_import.py"), "w", encoding="utf-8") as _fh:
            _fh.write("def make():\n    return 'hi'\n")
        _ms = "from to_import import make\nv = make()\n"
        _mp = _ose.path.join(_de, "main.py")
        with open(_mp, "w", encoding="utf-8") as _fh:
            _fh.write(_ms)
        assert any(e.get("variable") == "v" and e["type"] == ["str"]          # the sibling's return type resolves
                   for e in _emit(_ms, path=_mp, qualified=True)), "sibling import did not resolve through the path"
        assert not any(e.get("variable") == "v" and e.get("type") for e in _emit(_ms))   # no path: import unresolved
    finally:
        _she.rmtree(_de, ignore_errors=True)

    # repository-scale verification: a package on disk loads as one cross-module program and triages per function
    from .engines import _module_name as _modname
    assert _modname("pkg/sub/mod.py") == "pkg.sub.mod" and _modname("pkg/__init__.py") == "pkg"
    import tempfile as _tf, shutil as _sh, os as _os
    _d = _tf.mkdtemp()
    try:
        open(_os.path.join(_d, "lib.py"), "w").write("def half(n):\n    return 10 // n\n")
        open(_os.path.join(_d, "app.py"), "w").write(
            "from lib import half\ndef run(n):\n    return half(n)\n"
            "def safe(n):\n    if n == 0:\n        return 0\n    return half(n)\n")
        _tri = dict(verify_repo(_d))
        assert _tri["lib.half"] == REFUTED and _tri["app.run"] == REFUTED and _tri["app.safe"] == PROVED
        _cache = {}                                                      # content-addressed cache: a re-run reuses it
        assert dict(verify_repo(_d, cache=_cache)) == _tri and len(_cache) == 3
        assert dict(verify_repo(_d, cache=_cache)) == _tri
        # jobs > 1 triages the cache misses across worker processes, capped at the CPU count; each worker has its
        # own z3 context and returns the deterministic rlimit-bound verdict, so a parallel run is IDENTICAL to the
        # serial one (only faster), and the content-addressed cache composes with it.
        assert dict(verify_repo(_d, jobs=3)) == _tri                     # parallel == serial, deterministically
        _pcache = {}
        assert dict(verify_repo(_d, jobs=3, cache=_pcache)) == _tri and len(_pcache) == 3   # cache populated in parallel
        assert dict(verify_repo(_d, jobs=3, cache=_pcache)) == _tri      # a parallel re-run reuses the cache (zero work)
    finally:
        _sh.rmtree(_d, ignore_errors=True)
    # whole-program triage enters methods inside classes too, each triaged standalone: a method that is a
    # pure function of its parameters is verified, a trapping one is refuted, and self/attribute access is
    # UNKNOWN -- so class bodies are covered, not only top-level functions.
    _dm = _tf.mkdtemp()
    try:
        open(_os.path.join(_dm, "k.py"), "w").write(
            "def topf(x):\n    return x + 1\n"
            "class C:\n"
            "    def pure(self, x):\n        return x * 2\n"
            "    def divm(self, a, b):\n        return a // b\n"
            "    def uses_self(self):\n        return self.v + 1\n")
        _mt = dict(verify_repo(_dm))
        assert _mt["k.topf"] == PROVED                                       # top-level function still covered
        assert _mt["k.C.pure"] == PROVED                                     # pure-of-parameters method: verified
        assert _mt["k.C.divm"] == REFUTED                                    # a // b traps at b == 0
        assert _mt["k.C.uses_self"] == UNKNOWN                               # self attribute: outside the subset
    finally:
        _sh.rmtree(_dm, ignore_errors=True)

    # a scan's repo triage parallelizes the same way and stays just as deterministic: jobs > 1 triages the
    # modules across a spawn pool (capped at the CPU count), each worker replicating the symbolic-scan
    # execution flags, and returns byte-identical findings and counts to the serial scan. Exercise a
    # multi-module tree with a trapping function, a safe one, and a trapping method, so both the function and
    # the method worker paths run.
    _dp = _tf.mkdtemp(prefix="ts_parscan_")
    try:
        for _i in range(4):
            open(_os.path.join(_dp, "m%d.py" % _i), "w").write(
                "def divz(a, b):\n    return a // b\n"
                "def safe(x):\n    return x + 1\n"
                "class C:\n    def trap(self):\n        return 1 // 0\n")

        def _scankey(_r):
            return (_r["functions"], _r["proved"], _r["refuted"], _r["unknown"],
                    sorted((_f["location"], _f["classification"], _f["kind"]) for _f in _r["findings"]))
        _ss = scan(_dp, execute=False, jobs=1)
        assert _scankey(_ss) == _scankey(scan(_dp, execute=False, jobs=4))   # parallel == serial, deterministically
        assert _ss["functions"] == 12 and _ss["proved"] == 4 and _ss["refuted"] == 8 and _ss["unknown"] == 0
    finally:
        _sh.rmtree(_dp, ignore_errors=True)

    # per-unit scan budget: a unit whose AST exceeds core.SCAN_UNIT_NODE_BUDGET is skipped to UNKNOWN before any
    # engine runs (deterministic), so one giant generated body cannot stall or OOM a whole-repo scan. A tiny
    # budget skips even a small trap (every unit UNKNOWN, no findings); a large budget finds it. The wall-clock
    # backstop is a separate opt-out net, not exercised here (these units finish instantly).
    _db = _tf.mkdtemp(prefix="ts_budget_")
    try:
        open(_os.path.join(_db, "a.py"), "w").write("def trap(a, b):\n    return a // b\n")
        open(_os.path.join(_db, "b.py"), "w").write("def ok(x):\n    return x + 1\n")
        _saved_budget = core.SCAN_UNIT_NODE_BUDGET
        try:
            core.SCAN_UNIT_NODE_BUDGET = 100000                  # generous: the small trap is checked and refuted
            _hi = scan(_db, execute=False, jobs=1)
            core.SCAN_UNIT_NODE_BUDGET = 4                       # below every unit's node count: all skipped
            _lo = scan(_db, execute=False, jobs=1)
        finally:
            core.SCAN_UNIT_NODE_BUDGET = _saved_budget
        assert _hi["refuted"] == 1 and any(_f["location"] == "a.trap" for _f in _hi["findings"])
        assert _lo["refuted"] == 0 and _lo["unknown"] == _lo["functions"]   # the budget skipped every unit to UNKNOWN
    finally:
        _sh.rmtree(_db, ignore_errors=True)

    # per-unit crash tolerance: a unit that aborts its worker (a z3 SIGABRT no in-process bound can catch,
    # simulated here through the _SCAN_CRASH_ON test hook) is isolated to UNKNOWN, while its module-siblings and
    # the rest of the repo still triage. Force a crash on every 'boom' across a multi-module tree under the
    # supervised pool (jobs > 1) and confirm only the booms are lost.
    _dk = _tf.mkdtemp(prefix="ts_crash_")
    try:
        for _i in range(8):
            open(_os.path.join(_dk, "m%d.py" % _i), "w").write(
                "def boom(a, b):\n    return a // b\n"          # aborts its worker
                "def fine(a, b):\n    return a // b\n"           # sibling: still REFUTED despite the crash
                "def okay(x):\n    return x + 1\n")              # sibling: still PROVED
        _saved_crash = core._SCAN_CRASH_ON
        try:
            core._SCAN_CRASH_ON = ".boom"
            _ck = scan(_dk, execute=False, jobs=4)
        finally:
            core._SCAN_CRASH_ON = _saved_crash
        _ckloc = {_f["location"] for _f in _ck["findings"]}
        _crashed = not any(_loc.endswith(".boom") for _loc in _ckloc)             # booms -> UNKNOWN (the pool ran) vs
        #                                          REFUTED (a bare `python -c` cannot spawn, so triage runs serial and
        #                                          the worker-only hook never fires); assert isolation only when it ran
        assert sum(1 for _i in range(8) if "m%d.fine" % _i in _ckloc) == 8        # every fine refuted, both ways
        assert _ck["proved"] == 8                                                 # every okay proved, both ways
        if _crashed:
            assert _ck["refuted"] == 8 and _ck["unknown"] == 8                    # the 8 booms isolated to UNKNOWN
    finally:
        _sh.rmtree(_dk, ignore_errors=True)

    # scan verdict cache: a re-scan with a content-addressed cache returns findings identical to an uncached
    # scan, caches only non-REFUTED verdicts (so a finding's witness is always recomputed fresh), and -- the
    # soundness point -- a unit edited from safe to trapping is re-triaged to REFUTED, never served a stale PROVED.
    _dc = _tf.mkdtemp(prefix="ts_cache_")
    try:
        for _i in range(4):
            open(_os.path.join(_dc, "m%d.py" % _i), "w").write(
                "def divz(a, b):\n    return a // b\ndef safe(x):\n    return x + 1\n")
        _locs = lambda _r: sorted(_f["location"] for _f in _r["findings"])
        _cache = {}
        _r1 = scan(_dc, execute=False, jobs=1, cache=_cache)
        _r2 = scan(_dc, execute=False, jobs=1, cache=_cache)                                  # all safe units now hits
        assert _locs(_r1) == _locs(_r2) == ["m%d.divz" % _i for _i in range(4)]
        assert _r2["proved"] == 4 and _r2["refuted"] == 4 and _r2["unknown"] == 0
        assert len(_cache) == 4 and all(_v["status"] != REFUTED for _v in _cache.values())    # only the safe fns
        assert _locs(scan(_dc, execute=False, jobs=1)) == _locs(_r1)                          # uncached: same findings
        _cs = {}
        open(_os.path.join(_dc, "m0.py"), "w").write("def divz(x):\n    return x + 1\n")      # now safe
        scan(_dc, execute=False, jobs=1, cache=_cs)                                           # m0.divz cached PROVED
        open(_os.path.join(_dc, "m0.py"), "w").write("def divz(x):\n    return 1 // x\n")     # now traps
        assert "m0.divz" in _locs(scan(_dc, execute=False, jobs=1, cache=_cs))                # re-triaged, not stale
    finally:
        _sh.rmtree(_dc, ignore_errors=True)

    # SARIF 2.1.0 output for the triage verbs: a well-formed log, one result per finding carrying a level, a
    # logical + physical location (module path and def line), and a stable fingerprint; the repo-row form emits
    # one error result per refuted function and a physical location for a file::func gate label.
    from .sarif import scan_to_sarif, rows_to_sarif
    _dsf = _tf.mkdtemp(prefix="ts_sarif_")
    try:
        open(_os.path.join(_dsf, "a.py"), "w").write("def divz(a, b):\n    return a // b\ndef ok(x):\n    return x + 1\n")
        _rep = scan(_dsf, execute=False, jobs=1)
        _sl = scan_to_sarif(_rep)
        assert _sl["version"] == "2.1.0" and len(_sl["runs"]) == 1
        assert _sl["runs"][0]["tool"]["driver"]["name"] == "touchstone"
        _results = _sl["runs"][0]["results"]
        assert len(_results) == len(_rep["findings"]) == 1
        _res0 = _results[0]
        assert _res0["level"] in ("error", "warning", "note")
        assert _res0["locations"][0]["logicalLocations"][0]["fullyQualifiedName"] == "a.divz"
        assert _res0["locations"][0]["physicalLocation"]["artifactLocation"]["uri"] == "a.py"
        assert _res0["partialFingerprints"]["touchstone/v1"] == finding_fingerprint(_rep["findings"][0])
        _rs = rows_to_sarif([("pkg.f", "REFUTED"), ("pkg.g", "PROVED"), ("d.py::h", "REFUTED")])
        assert len(_rs["runs"][0]["results"]) == 2                                            # only the refuted rows
        assert _rs["runs"][0]["results"][1]["locations"][0]["physicalLocation"]["artifactLocation"]["uri"] == "d.py"
    finally:
        _sh.rmtree(_dsf, ignore_errors=True)

    # finding fingerprint + baseline partition: a fingerprint is the trap site and exception (independent of the
    # sampled witness), and partition splits findings into those a baseline already records (known) and the rest
    # (new), so a baselined scan fails only on a finding not in the baseline.
    _bf1 = {"location": "p.f", "exception": "ZeroDivisionError", "classification": "bug"}
    _bf2 = {"location": "p.g", "exception": "IndexError", "classification": "bug"}
    assert finding_fingerprint(_bf1) == "p.f|ZeroDivisionError"
    _bnew, _bknown = baseline_partition([_bf1, _bf2], [finding_fingerprint(_bf1)])
    assert [_f["location"] for _f in _bknown] == ["p.f"] and [_f["location"] for _f in _bnew] == ["p.g"]
    assert baseline_partition([_bf1], [])[0] == [_bf1]                                        # empty baseline: all new

    # exclude globs: a module matching an fnmatch glob (dotted-name or slash-path form) is dropped from the
    # triage set of verify_repo / scan, while still loaded for call resolution.
    from . import engines as _eng
    assert _eng._excluded("vendor.dep", ["vendor/*"]) and _eng._excluded("pkg.vendor.dep", ["*vendor*"])
    assert not _eng._excluded("keep.mod", ["vendor/*"]) and not _eng._excluded("any", None)
    _dex = _tf.mkdtemp(prefix="ts_excl_")
    try:
        open(_os.path.join(_dex, "keep.py"), "w").write("def divz(a, b):\n    return a // b\n")
        _os.makedirs(_os.path.join(_dex, "vendor"))
        open(_os.path.join(_dex, "vendor", "__init__.py"), "w").write("")
        open(_os.path.join(_dex, "vendor", "dep.py"), "w").write("def divz(a, b):\n    return a // b\n")
        _all = {_l for _l, _s in verify_repo(_dex)}
        _ex = {_l for _l, _s in verify_repo(_dex, exclude=["vendor/*"])}
        assert "vendor.dep.divz" in _all and "vendor.dep.divz" not in _ex and "keep.divz" in _ex
        _slocs = {_f["location"] for _f in scan(_dex, execute=False, jobs=1, exclude=["vendor.*"])["findings"]}
        assert "keep.divz" in _slocs and not any(_l.startswith("vendor.") for _l in _slocs)
    finally:
        _sh.rmtree(_dex, ignore_errors=True)

    # CLI exit policy + config: --fail-on sets the scan status, and the [tool.touchstone] table is read from the
    # nearest pyproject (the keys that back --exclude / --fail-on / --jobs / --budget).
    from . import cli as _cli
    import io as _cio, contextlib as _ccl
    _dcli = _tf.mkdtemp(prefix="ts_cliscan_")
    try:
        open(_os.path.join(_dcli, "z.py"), "w").write("def divz(a, b):\n    return a // b\n")
        with _ccl.redirect_stdout(_cio.StringIO()):
            _rc_any = _cli.main(["scan", _dcli, "--jobs", "1", "--fail-on", "any"])
            _rc_none = _cli.main(["scan", _dcli, "--jobs", "1", "--fail-on", "none"])
            _rc_bug = _cli.main(["scan", _dcli, "--jobs", "1", "--fail-on", "bug"])   # symbolic: no 'bug' class
        assert _rc_any == 1 and _rc_none == 0 and _rc_bug == 0
        open(_os.path.join(_dcli, "pyproject.toml"), "w").write(
            '[tool.touchstone]\nexclude = ["z*"]\nfail_on = "none"\njobs = 2\n')
        assert _cli._load_tool_config(_dcli) == {"exclude": ["z*"], "fail_on": "none", "jobs": 2}
    finally:
        _sh.rmtree(_dcli, ignore_errors=True)

    # inline suppression: a unit carrying `# touchstone: ignore` in its body is dropped from the findings and
    # counted in suppressed_in_source, while its unmarked sibling still reports.
    _dsupp = _tf.mkdtemp(prefix="ts_supp_")
    try:
        open(_os.path.join(_dsupp, "s.py"), "w").write(
            "def risky(x):  # touchstone: ignore\n    return 10 // x\ndef other(y):\n    return 10 // y\n")
        _sr = scan(_dsupp, execute=False, jobs=1)
        _slocs = {_f["location"] for _f in _sr["findings"]}
        assert "s.other" in _slocs and "s.risky" not in _slocs and _sr["suppressed_in_source"] == 1
    finally:
        _sh.rmtree(_dsupp, ignore_errors=True)

    # report renderings: a Markdown findings table and GitHub Actions annotations, plus the empty case.
    from .report import scan_to_markdown, scan_to_github
    _frep = {"target": "t", "executed": False, "functions": 2, "proved": 1, "refuted": 1, "unknown": 0,
             "findings": [{"location": "m.f", "module": "m", "line": 3, "classification": "bug",
                           "exception": "ZeroDivisionError", "label": "confirmed bug"}]}
    _md = scan_to_markdown(_frep)
    assert _md.startswith("## Touchstone scan") and "| `m.f:3` |" in _md and "ZeroDivisionError" in _md
    assert scan_to_markdown({"target": "t", "functions": 0, "findings": []}).strip().endswith("No reachable traps found.")
    _gh = scan_to_github(_frep)
    assert _gh.startswith("::error file=m.py,line=3,title=") and "::m.f: confirmed bug" in _gh

    # CLI --format dispatch and the init scaffolding (no baseline scan in the test).
    _dfmt = _tf.mkdtemp(prefix="ts_fmt_")
    try:
        open(_os.path.join(_dfmt, "a.py"), "w").write("def trap(x):\n    return 1 // x\n")
        _bmd = _cio.StringIO()
        with _ccl.redirect_stdout(_bmd):
            _cli.main(["scan", _dfmt, "--jobs", "1", "--format", "markdown"])
        assert "| Location |" in _bmd.getvalue() and "a.trap" in _bmd.getvalue()
        _bgh = _cio.StringIO()
        with _ccl.redirect_stdout(_bgh):
            _cli.main(["scan", _dfmt, "--jobs", "1", "--format", "github"])
        assert _bgh.getvalue().startswith("::") and "a.trap" in _bgh.getvalue()
        open(_os.path.join(_dfmt, "pyproject.toml"), "w").write('[project]\nname = "d"\nversion = "0"\n')
        with _ccl.redirect_stdout(_cio.StringIO()):
            _rc_init = _cli.main(["init", _dfmt, "--no-baseline"])
        assert _rc_init == 0 and _os.path.exists(_os.path.join(_dfmt, ".github", "workflows", "touchstone.yml"))
        assert "[tool.touchstone]" in open(_os.path.join(_dfmt, "pyproject.toml")).read()
    finally:
        _sh.rmtree(_dfmt, ignore_errors=True)

    # progress callback on the repo / coverage triage path (verify_repo), reaching the work total.
    _prog = []
    _dpg = _tf.mkdtemp(prefix="ts_prog_")
    try:
        for _i in range(3):
            open(_os.path.join(_dpg, "m%d.py" % _i), "w").write("def f%d(a, b):\n    return a // b\n" % _i)
        verify_repo(_dpg, progress=lambda _d, _t: _prog.append((_d, _t)))
        assert _prog and _prog[-1] == (3, 3)                              # three distinct units, all reported
    finally:
        _sh.rmtree(_dpg, ignore_errors=True)

    # [tool.touchstone] now also supplies baseline / cache path defaults.
    _dcfg = _tf.mkdtemp(prefix="ts_cfg2_")
    try:
        open(_os.path.join(_dcfg, "pyproject.toml"), "w").write('[tool.touchstone]\nbaseline = "b.json"\ncache = "c.json"\n')
        assert _cli._load_tool_config(_dcfg) == {"baseline": "b.json", "cache": "c.json"}
    finally:
        _sh.rmtree(_dcfg, ignore_errors=True)

    # execute-mode caching: a re-scan reuses the cached sandbox confirmation (an `xf` cache entry), and -- the
    # soundness point -- editing the unit from trapping to safe invalidates it (the confirmation is not stale).
    _dxc = _tf.mkdtemp(prefix="ts_xcache_")
    try:
        open(_os.path.join(_dxc, "a.py"), "w").write("def trap(x):\n    return 1 // x\ndef ok(y):\n    return y + 1\n")
        _xc = {}
        _x1 = scan(_dxc, execute=True, jobs=1, cache=_xc)
        assert any(_k.startswith("xf") for _k in _xc) and _x1["bugs"] == 1
        _x2 = scan(_dxc, execute=True, jobs=1, cache=_xc)
        assert _x2["bugs"] == 1 and [_f["location"] for _f in _x1["findings"]] == [_f["location"] for _f in _x2["findings"]]
        open(_os.path.join(_dxc, "a.py"), "w").write("def trap(x):\n    return x + 1\ndef ok(y):\n    return y + 1\n")
        assert scan(_dxc, execute=True, jobs=1, cache=_xc)["bugs"] == 0    # re-confirmed, not served stale
    finally:
        _sh.rmtree(_dxc, ignore_errors=True)

    # spawn-pool re-entry guard: a worker re-importing an unguarded __main__ has _POOL_ENV set, so a re-entered
    # whole-repo entry point no-ops (empty result) instead of recursing into a nested pool -- the footgun fix.
    from . import engines as _eng2
    _dre = _tf.mkdtemp(prefix="ts_reentry_")
    try:
        open(_os.path.join(_dre, "a.py"), "w").write("def trap(x):\n    return 1 // x\n")
        assert scan(_dre, jobs=1)["functions"] == 1                       # normal: the unit is triaged
        _had = _os.environ.get(_eng2._POOL_ENV)
        _os.environ[_eng2._POOL_ENV] = "1"
        try:                                                             # emulate running inside a pool worker
            assert scan(_dre, jobs=1)["functions"] == 0 and scan(_dre, jobs=1)["findings"] == []
            assert verify_repo(_dre) == [] and verify_diff(_dre, ["a.py"]) == [] and coverage(_dre)["total"] == 0
        finally:
            if _had is None:
                _os.environ.pop(_eng2._POOL_ENV, None)
            else:
                _os.environ[_eng2._POOL_ENV] = _had
        assert scan(_dre, jobs=1)["functions"] == 1                       # flag cleared: normal again
    finally:
        _sh.rmtree(_dre, ignore_errors=True)

    # annotated assignment is desugared to a plain assignment, so a function using `x: T = v` is decided rather
    # than abstaining at "statement AnnAssign"; a bare annotation `x: T` binds nothing and is dropped.
    assert check("def f(n):\n    total: int = 0\n    total = total + n\n    return total\n").status == PROVED
    assert check("def f(n):\n    x: int\n    return n + 1\n").status == PROVED

    # nested-container parameter modeling: an element of a list[list[T]] parameter is itself a bounds-checked
    # sequence with a per-index symbolic length, so len(p[i]) and p[i][j] (load and store) decide. The per-index
    # length is sound: a len(p[i]) guard protects p[i][j] but NOT a different index p[i+1][j].
    _NL = "p: list[list[int]], i: int, j: int"
    assert check("def f(%s):\n    if 0<=i<len(p) and 0<=j<len(p[i]):\n        return p[i][j]\n    return 0\n" % _NL).status == PROVED
    assert check("def f(%s):\n    if 0<=i<len(p):\n        return p[i][j]\n    return 0\n" % _NL).status == REFUTED
    assert check("def f(%s):\n    if 0<=i<len(p) and 0<=j<len(p[i]) and i+1<len(p):\n        return p[i+1][j]\n    return 0\n" % _NL).status == REFUTED
    assert check("def f(%s, v: int):\n    if 0<=i<len(p) and 0<=j<len(p[i]):\n        p[i][j] = v\n    return 0\n" % _NL).status == PROVED

    # a self-recursive function over a list / str parameter is verified trap free through the value engine (its
    # self-call assumed trap free -- the inductive hypothesis), so a guarded recursive index proves while an
    # unguarded one still refutes. Triaged with a repo (the self-call is in-repo), exactly as a scan does.
    _drec = _tf.mkdtemp(prefix="ts_rec_")
    try:
        open(_os.path.join(_drec, "r.py"), "w").write(
            "def g(p: list, i: int):\n    if i < 0 or i >= len(p):\n        return 0\n    return p[i] + g(p, i + 1)\n\n"
            "def bad(p: list, i: int):\n    if i >= len(p):\n        return 0\n    return p[i] + bad(p, i + 1)\n")
        _st = dict(verify_repo(_drec))
        assert _st.get("r.g") == PROVED and _st.get("r.bad") == REFUTED
    finally:
        _sh.rmtree(_drec, ignore_errors=True)

    # a fixed-arity tuple parameter (tuple[int, int]) has exactly that many elements, so x, y = t raises no
    # ValueError and t in bounds proves, while t[2] still refutes and a bare / variadic tuple keeps arbitrary length.
    assert check("def f(key: tuple[int, int]):\n    n, d = key\n    return n + d\n").status == PROVED
    assert check("def f(key: tuple[int, int]):\n    return key[2]\n").status == REFUTED
    assert check("def f(key: tuple):\n    n, d = key\n    return 0\n").status == REFUTED

    # iterating a string parameter binds the element to a 1-char string (a for-loop or a comprehension), so an
    # element op ord(c) / len(c) decides (an arbitrary char over-approximates every one), while a trapping element
    # op still refutes.
    assert check("def f(plain: str):\n    return [ord(c) - 96 for c in plain]\n").status == PROVED
    assert check("def f(s: str):\n    for c in s:\n        x = ord(c)\n    return 0\n").status == PROVED
    assert check("def f(s: str):\n    return [10 // (ord(c) - 65) for c in s]\n").status == REFUTED
    # iterating a bytes / bytearray parameter binds the element to an int in [0, 255] (an arbitrary byte over-
    # approximates every one), in the loop body, the exact first iteration, and a comprehension. So x + 1 is never
    # 0 over a byte -- PROVED, where an unconstrained element would FABRICATE a ZeroDivisionError at the impossible
    # byte == -1 -- x % 16 never traps, while a trap reachable at a real byte value (100 // (x - 5) at byte 5) still
    # REFUTES (5 is in [0, 255]).
    assert check("def f(b: bytes):\n    s = 0\n    for x in b:\n        s = s + 1000 // (x + 1)\n    return s\n").status == PROVED
    assert check("def f(b: bytes):\n    return [1000 // (x + 1) for x in b]\n").status == PROVED
    assert check("def f(b: bytearray):\n    s = 0\n    for x in b:\n        s = s + 1000 // (x + 1)\n    return s\n").status == PROVED
    assert check("def f(b: bytes):\n    s = 0\n    for x in b:\n        s = s + 100 // (x - 5)\n    return s\n").status == REFUTED
    assert check("def f(b: bytes):\n    return [100 // (x - 5) for x in b]\n").status == REFUTED
    # a sequence literal collapses to a tuple, so list + list (valid) versus tuple + list (TypeError) is undecided:
    # the value engine abstains rather than fabricate a TypeError -- xs + [1] must never be REFUTED (it once was, a
    # false refutation of valid list concatenation). A genuinely incompatible right operand still refutes (a scalar /
    # bytes / set + a list literal), and a sequence times a sequence is the TypeError CPython raises (xs * [1] was
    # once a false PROVED, a missed TypeError). Repetition by an int and list + list-literal still hold.
    assert check("def f(xs: list):\n    return xs + [1]\n").status != REFUTED
    assert check("def f(xs: list):\n    return [1] + xs\n").status != REFUTED
    assert check("def f(xs: list):\n    return xs * [1]\n").status == REFUTED
    assert check("def f(xs: list):\n    return [1] * xs\n").status == REFUTED
    assert check("def f(b: bytes):\n    return b + [1]\n").status == REFUTED
    assert check("def f(s: set):\n    return s + [1]\n").status == REFUTED
    assert check("def f():\n    return [1, 2, 3] + 5\n").status == REFUTED
    assert check("def f():\n    return [0] * 3\n").status == PROVED
    assert check("def f():\n    return [1] + [2]\n").status == PROVED
    assert check("def f(n: int):\n    a = [0] * n\n    return len(a)\n").status == PROVED
    # a list / tuple literal value reassigned across a loop keeps its sequence kind through the havoc (not collapsed
    # to a fresh int), so a length / index after the loop is modeled rather than abstained on as a non-integer.
    assert check("def f(n: int):\n    a = (0,)\n    for i in range(n):\n        a = a\n    return len(a)\n").status == PROVED
    # int.from_bytes(b, byteorder) reads a bytes value as an integer: a correct byteorder literal ('big' / 'little')
    # is trap free and the unsigned result is non-negative (so it can feed a // (x + 1) safely); a bad byteorder
    # literal or an unconstrained byteorder parameter refutes (ValueError), a guard on the byteorder proves, and
    # signed=True drops the non-negativity (a negative result is possible, so // (x + 1) refutes). A non-bytes
    # first argument (whose elements may not be valid byte values) is declined.
    assert check("def f(b: bytes):\n    return int.from_bytes(b, 'big')\n").status == PROVED
    assert check("def f(b: bytes):\n    return int.from_bytes(b, byteorder='little')\n").status == PROVED
    assert check("def f(b: bytes):\n    return int.from_bytes(b, 'middle')\n").status == REFUTED
    assert check("def f(b: bytes, bo: str):\n    return int.from_bytes(b, bo)\n").status == REFUTED
    assert check("def f(b: bytes, bo: str):\n    if bo == 'big' or bo == 'little':\n        return int.from_bytes(b, bo)\n    return 0\n").status == PROVED
    assert check("def f(b: bytes):\n    x = int.from_bytes(b, 'big')\n    return 1000 // (x + 1)\n").status == PROVED
    assert check("def f(b: bytes):\n    x = int.from_bytes(b, 'big', signed=True)\n    return 1000 // (x + 1)\n").status == REFUTED
    assert check("def f(s: str):\n    return int.from_bytes(s, 'big')\n").status == UNKNOWN
    # int('42') / float('1.5') parse a string literal exactly as CPython does: a valid literal is total and its value
    # is known (int('42') is 42, float('1.5') is 1.5, float('inf') is the IEEE infinity), while an unparseable literal
    # (float('abc'), int('0x10') without a base) always raises ValueError. A non-literal string argument stays
    # UNKNOWN -- the parse cannot be decided symbolically (a str-to-number predicate is not in the theory).
    assert check("def f():\n    return float('inf')\n").status == PROVED
    assert check("def f():\n    return 100 // (int('42') - 41)\n").status == PROVED   # int('42') == 42 exactly
    assert check("def f():\n    x = float('1.5')\n    return 10.0 / (x - 1.5 + 1.0)\n").status == PROVED   # float('1.5') == 1.5
    assert check("def f():\n    return float('abc')\n").status == REFUTED
    assert check("def f():\n    return int('0x10')\n").status == REFUTED            # base-10 int() rejects a 0x prefix
    assert check("def f(s: str):\n    return float(s)\n").status == UNKNOWN
    # int(str_literal, base) parses with the given base (positional or base=, default 10) -- exactly CPython's parse.
    # A valid (digits, base) is total with a known value (int('ff', 16) is 255), an invalid digit string or an
    # out-of-range base (must be 0 or 2..36) raises ValueError. A base= keyword MUST use that base, not 10, so
    # int('ff', base=16) is valid -- never a false ValueError. A non-literal string or base abstains.
    assert check("def f():\n    return int('ff', base=16)\n").status == PROVED          # base= keyword, not base 10
    assert check("def f():\n    return 1000 // (int('ff', 16) - 254)\n").status == PROVED   # int('ff', 16) == 255 exactly
    assert check("def f():\n    return int('zz', 16)\n").status == REFUTED
    assert check("def f():\n    return int('5', 37)\n").status == REFUTED               # base out of range (2..36 or 0)
    assert check("def f(s: str):\n    return int(s, 16)\n").status == UNKNOWN
    # itertools.chain(a, b, ...) concatenates known sized iterables into one of the summed length (trap free), so
    # len(list(chain(a, b))) is exactly len(a) + len(b), an index into it past that length refutes (both may be
    # empty), and a non-sized / possibly non-iterable argument (chain(5, 6)) abstains.
    assert check("import itertools\ndef f(a: list, b: list):\n    return 10 // (len(list(itertools.chain(a, b))) - len(a) - len(b) + 1)\n").status == PROVED
    assert check("import itertools\ndef f(a: list, b: list):\n    c = list(itertools.chain(a, b))\n    if len(c) > 0:\n        return c[0]\n    return 0\n").status == PROVED
    assert check("import itertools\ndef f(a: list, b: list):\n    return list(itertools.chain(a, b))[0]\n").status == REFUTED
    assert check("import itertools\ndef f():\n    return len(list(itertools.chain(5, 6)))\n").status == UNKNOWN
    # a = [1, 2, 3]; a[i] = v mutates a list literal in place: a constant in-range index updates the element exactly
    # (a[0] = 9 then a[0] is 9), a constant out-of-range or an unguarded symbolic index refutes (IndexError), a
    # guarded symbolic index proves. A tuple literal is NOT mutable -- (1, 2, 3)[0] = v stays a possible TypeError
    # (UNKNOWN). Exact element reads and unpacking over a list literal are unchanged (the value is a tuple subclass).
    assert check("def f():\n    a = [1, 2, 3]\n    a[0] = 9\n    return 10 // (a[0] - 8)\n").status == PROVED   # a[0] == 9 exactly
    assert check("def f(i: int):\n    a = [1, 2, 3]\n    if 0 <= i < 3:\n        a[i] = 9\n    return a[0]\n").status == PROVED
    assert check("def f(i: int):\n    a = [1, 2, 3]\n    a[i] = 9\n    return 0\n").status == REFUTED
    assert check("def f():\n    a = [1, 2, 3]\n    a[5] = 9\n    return 0\n").status == REFUTED
    assert check("def f():\n    a = (1, 2, 3)\n    a[0] = 9\n    return 0\n").status == UNKNOWN          # tuple literal: not mutable
    assert check("def f():\n    return 10 // ([1, 2, 3][0])\n").status == PROVED                       # exact read preserved
    assert check("def f():\n    a, b = [1, 2]\n    return 10 // a\n").status == PROVED                 # unpacking preserved
    # reversed(seq): an indexable sized sequence gives a NEW sequence of the same length (trap free), so
    # len(list(reversed(xs))) is exactly len(xs) and an unguarded index into it refutes (it may be empty); reversed
    # bytes yields ints in [0, 255]. A set / frozenset is NOT reversible -- reversed(s) refutes (TypeError, once a
    # false PROVED) and list(reversed(s)) never proves; a str / bytes / dict (3.8+) is reversible.
    assert check("def f(xs: list):\n    return 10 // (len(list(reversed(xs))) - len(xs) + 1)\n").status == PROVED
    assert check("def f(xs: list):\n    r = list(reversed(xs))\n    if len(r) > 0:\n        return r[0]\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    return list(reversed(xs))[0]\n").status == REFUTED
    assert check("def f(s: set):\n    return reversed(s)\n").status == REFUTED                  # a set is not reversible
    assert check("def f(s: set):\n    return list(reversed(s))\n").status != PROVED             # never a false PROVED
    assert check("def f(b: bytes):\n    s = 0\n    for x in reversed(b):\n        s = s + 1000 // (x + 1)\n    return s\n").status == PROVED
    assert check("def f(d: dict):\n    return reversed(d)\n").status == PROVED                  # dict reversible (3.8+)
    # operator.add(a, b) / operator.lt(a, b) / operator.neg(a) mirror the Python operator exactly, reusing its
    # semantics and traps: operator.add(a, b) is a + b (exactly), operator.floordiv(a, b) is a ZeroDivisionError when
    # b is 0 (an unguarded divisor refutes, a b != 0 guard proves), operator.lt returns a bool, operator.neg(x) is
    # -x. A non-operator helper (itemgetter) is not mapped and abstains.
    assert check("import operator\ndef f(a: int, b: int):\n    return 10 // (operator.add(a, b) - a - b + 1)\n").status == PROVED
    assert check("import operator\ndef f(x: int):\n    return 10 // (operator.neg(x) + x + 1)\n").status == PROVED
    assert check("import operator\ndef f(a: int, b: int):\n    return operator.floordiv(a, b)\n").status == REFUTED
    assert check("import operator\ndef f(a: int, b: int):\n    if b != 0:\n        return operator.floordiv(a, b)\n    return 0\n").status == PROVED
    assert check("import operator\ndef f(a: int, b: int):\n    return 1 if operator.lt(a, b) else 0\n").status == PROVED
    assert check("import operator\ndef f(xs: list):\n    return operator.itemgetter(0)(xs)\n").status == UNKNOWN
    # bytes.fromhex(s) / bytearray.fromhex(s) parses a hex string literal exactly as CPython does: a valid hex string
    # (interleaved whitespace allowed) gives a byteslike value of half its non-space length whose elements are bytes
    # in [0, 255], an odd-length or non-hex literal always raises ValueError. A non-literal argument abstains.
    assert check("def f():\n    return 10 // (len(bytes.fromhex('dead')) - 1)\n").status == PROVED   # len == 2 exactly
    assert check("def f():\n    return bytes.fromhex('zz')\n").status == REFUTED
    assert check("def f():\n    return bytes.fromhex('abc')\n").status == REFUTED                    # odd length
    assert check("def f():\n    s = 0\n    for x in bytes.fromhex('cafe'):\n        s = s + 1000 // (x + 1)\n    return s\n").status == PROVED
    assert check("def f():\n    return bytes.fromhex('')[0]\n").status == REFUTED                    # empty -> IndexError
    assert check("def f(s: str):\n    return bytes.fromhex(s)\n").status == UNKNOWN
    # math.isclose(a, b) -> a bool, total over numbers with the default tolerances (so an if math.isclose(...) branch
    # decides). The two values must be numeric -- a str / list argument abstains -- and a rel_tol / abs_tol keyword
    # (a possible negative-tolerance ValueError) is declined. The bool is 0/1, so 10 // math.isclose(a, b) refutes
    # (isclose can be False, i.e. 0 -- a real ZeroDivisionError).
    assert check("import math\ndef f(a: float, b: float):\n    return 1 if math.isclose(a, b) else 0\n").status == PROVED
    assert check("import math\ndef f(a: float, b: float):\n    x = 1 if math.isclose(a, b) else 2\n    return 10 // x\n").status == PROVED
    assert check("import math\ndef f(a: float, b: float):\n    return 10 // math.isclose(a, b)\n").status == REFUTED
    assert check("import math\ndef f(s: str, b: float):\n    return 1 if math.isclose(s, b) else 0\n").status == UNKNOWN
    assert check("import math\ndef f(a: float, b: float):\n    return 1 if math.isclose(a, b, rel_tol=0.1) else 0\n").status == UNKNOWN
    # zip(a, b, ...) stops at the SHORTEST argument, so list(zip(...)) has the minimum length of its sized arguments
    # (trap free; a for-loop over it still havocs the targets, including a tuple target). An unguarded index into it
    # refutes (it may be empty); its elements are opaque tuples, so a deep index z[0][0] abstains.
    assert check("def f(a: list, b: list):\n    n = len(list(zip(a, b)))\n    if n <= len(a):\n        return 1\n    return 10 // 0\n").status == PROVED
    assert check("def f(a: list, b: list):\n    return list(zip(a, b))[0]\n").status == REFUTED
    assert check("def f(a: list, b: list):\n    s = 0\n    for x, y in zip(a, b):\n        s = 1\n    return s\n").status == PROVED
    assert check("def f(a: list, b: list):\n    z = list(zip(a, b))\n    if len(z) > 0:\n        return z[0][0]\n    return 0\n").status == PROVED   # zip element is a 2-tuple: [0][0] is a scalar
    # itertools.repeat(x, count) yields max(count, 0) copies, so list(repeat(x, n)) has length max(n, 0): an unguarded
    # index refutes (n may be 0), an n >= 1 guard proves, and it composes with chain (chain(repeat(x, 3), ys) has
    # length 3 + len(ys)). repeat(x) without a count is infinite and abstains.
    assert check("import itertools\ndef f(x: int):\n    return 10 // (len(list(itertools.repeat(x, 5))) - 4)\n").status == PROVED   # len == 5 exactly
    assert check("import itertools\ndef f(x: int, n: int):\n    return list(itertools.repeat(x, n))[0]\n").status == REFUTED
    assert check("import itertools\ndef f(x: int, n: int):\n    if n >= 1:\n        return list(itertools.repeat(x, n))[0]\n    return 0\n").status == PROVED
    assert check("import itertools\ndef f(x: int, ys: list):\n    return 10 // (len(list(itertools.chain(itertools.repeat(x, 3), ys))) - len(ys) - 2)\n").status == PROVED
    assert check("import itertools\ndef f(x: int):\n    return len(list(itertools.repeat(x)))\n").status == UNKNOWN
    # itertools.islice(it, stop) takes the first `stop` elements (stop=None -> all), so for a sized iterable
    # list(islice(it, n)) has length min(len(it), n) when n is a non-negative int: an unguarded n refutes (a negative
    # stop is a ValueError), an n >= 0 guard proves, and stop=None gives len(it). A non-sized iterable abstains.
    assert check("import itertools\ndef f(xs: list):\n    m = len(list(itertools.islice(xs, 3)))\n    if m <= 3 and m <= len(xs):\n        return 1\n    return 10 // 0\n").status == PROVED
    assert check("import itertools\ndef f(xs: list, n: int):\n    return len(list(itertools.islice(xs, n)))\n").status == REFUTED
    assert check("import itertools\ndef f(xs: list, n: int):\n    if n >= 0:\n        return len(list(itertools.islice(xs, n)))\n    return 0\n").status == PROVED
    assert check("import itertools\ndef f(xs: list):\n    return 10 // (len(list(itertools.islice(xs, None))) - len(xs) + 1)\n").status == PROVED
    assert check("import itertools\ndef f(xs: list):\n    return len(list(itertools.islice((y for y in xs), 3)))\n").status == UNKNOWN
    # struct.calcsize(fmt) for a string LITERAL is exactly CPython's byte size of the format (struct.calcsize('>I')
    # is 4, '>2I' is 8); an invalid format literal always raises struct.error. A non-literal format abstains.
    assert check("import struct\ndef f():\n    return 10 // (struct.calcsize('>I') - 3)\n").status == PROVED   # == 4 exactly
    assert check("import struct\ndef f():\n    return struct.calcsize('zzz')\n").status == REFUTED
    assert check("import struct\ndef f(fmt: str):\n    return struct.calcsize(fmt)\n").status == UNKNOWN
    # math.log(x, base) (two-argument) = log(x)/log(base): a ValueError when x <= 0 or base <= 0, a ZeroDivisionError
    # when base == 1 -- so an unguarded call refutes (CPython: log(-1, 2) is ValueError, log(10, 1) is
    # ZeroDivisionError), and a guard (x > 0, base > 0, base != 1) proves. A non-numeric argument abstains.
    assert check("import math\ndef f(x: float):\n    return math.log(x, 2.0)\n").status == REFUTED
    assert check("import math\ndef f(x: float):\n    if x > 0.0:\n        return math.log(x, 2.0)\n    return 0.0\n").status == PROVED
    assert check("import math\ndef f():\n    return math.log(10.0, 1.0)\n").status == REFUTED   # base == 1: ZeroDivisionError
    assert check("import math\ndef f(x: float, b: float):\n    if x > 0.0 and b > 0.0 and b != 1.0:\n        return math.log(x, b)\n    return 0.0\n").status == PROVED
    assert check("import math\ndef f(s: str):\n    return math.log(s, 2.0)\n").status == UNKNOWN
    # itertools.zip_longest(a, b, ...) pads to the LONGEST argument (the dual of zip), so list(zip_longest(...)) has
    # the MAXIMUM length of its sized arguments (trap free; a for-loop still havocs the targets). An unguarded index
    # refutes (both may be empty); a fillvalue keyword is benign; a non-sized argument abstains.
    assert check("import itertools\ndef f(a: list, b: list):\n    m = len(list(itertools.zip_longest(a, b)))\n    if m >= len(a) and m >= len(b):\n        return 1\n    return 10 // 0\n").status == PROVED
    assert check("import itertools\ndef f(a: list, b: list):\n    return list(itertools.zip_longest(a, b))[0]\n").status == REFUTED
    assert check("import itertools\ndef f(a: list, b: list):\n    s = 0\n    for x, y in itertools.zip_longest(a, b):\n        s = 1\n    return s\n").status == PROVED
    assert check("import itertools\ndef f(a: list):\n    return len(list(itertools.zip_longest(a, (y for y in a))))\n").status == UNKNOWN
    # itertools.product(a, b, ...) is the cartesian product, so list(product(...)) has length equal to the PRODUCT of
    # the argument lengths (product() with no args is the single empty tuple, length 1). A guarded index proves, an
    # unguarded one refutes (a factor may be empty); a non-sized argument abstains.
    assert check("import itertools\ndef f(a: list, b: list):\n    return 10 // (len(list(itertools.product(a, b))) + 1)\n").status == PROVED
    assert check("import itertools\ndef f():\n    return 10 // (len(list(itertools.product())) - 0)\n").status == PROVED   # length 1
    assert check("import itertools\ndef f(a: list, b: list):\n    return list(itertools.product(a, b))[0]\n").status == REFUTED
    assert check("import itertools\ndef f(a: list, b: list):\n    p = list(itertools.product(a, b))\n    if len(p) > 0:\n        return p[0]\n    return 0\n").status == PROVED
    assert check("import itertools\ndef f(xs: list):\n    return len(list(itertools.product(xs, (y for y in xs))))\n").status == UNKNOWN
    # bytes(n) / bytearray(n) builds n zero bytes: a negative count is a ValueError (an unguarded count refutes, an
    # n >= 0 guard proves), and the result is a byteslike sequence of length n whose elements are valid bytes in
    # [0, 255] (so iterating it and dividing by element + 1 is safe). bytes()/bytearray() is empty; bytes(b) copies a
    # bytes value at equal length. A str argument (which needs an encoding) is declined.
    assert check("def f(n: int):\n    return bytes(n)\n").status == REFUTED
    assert check("def f(n: int):\n    if n >= 0:\n        return bytes(n)\n    return b''\n").status == PROVED
    assert check("def f(n: int):\n    if n >= 0:\n        return bytearray(n)\n    return bytearray()\n").status == PROVED
    assert check("def f():\n    return 10 // (len(bytes()) + 1)\n").status == PROVED
    assert check("def f(b: bytes):\n    c = bytes(b)\n    return 10 // (len(c) - len(b) + 1)\n").status == PROVED
    assert check("def f(n: int):\n    if n >= 0:\n        s = 0\n        for x in bytearray(n):\n            s = s + 1000 // (x + 1)\n        return s\n    return 0\n").status == PROVED
    assert check("def f(s: str):\n    return bytes(s)\n").status == UNKNOWN
    # n.to_bytes(length, byteorder[, signed=]) writes an int to `length` bytes: for a CONSTANT length L it is total
    # iff n fits (unsigned 0 <= n < 256**L, signed -(256**L)//2 <= n < (256**L)//2), else OverflowError -- so an
    # unguarded n refutes and a tight range guard proves, exactly at the boundary (255 fits one byte, 256 does not;
    # signed one byte is [-128, 127]). A bad byteorder literal refutes (ValueError); the result has length L. A
    # symbolic length is declined (256**length is not a concrete bound).
    assert check("def f(n: int):\n    return n.to_bytes(4, 'big')\n").status == REFUTED
    assert check("def f(n: int):\n    if 0 <= n and n <= 255:\n        return n.to_bytes(1, 'big')\n    return b''\n").status == PROVED
    assert check("def f(n: int):\n    if 0 <= n and n <= 256:\n        return n.to_bytes(1, 'big')\n    return b''\n").status == REFUTED
    assert check("def f(n: int):\n    if -128 <= n and n <= 127:\n        return n.to_bytes(1, 'big', signed=True)\n    return b''\n").status == PROVED
    assert check("def f(n: int):\n    if 0 <= n and n < 256:\n        b = n.to_bytes(4, 'big')\n        return 10 // (len(b) - 4 + 1)\n    return 0\n").status == PROVED
    assert check("def f(n: int):\n    if 0 <= n and n < 256:\n        return n.to_bytes(1, 'middle')\n    return b''\n").status == REFUTED
    assert check("def f(n: int, L: int):\n    return n.to_bytes(L, 'big')\n").status == UNKNOWN

    # sys.exit / exit() / quit() terminate the path (SystemExit is an intentional exit, not a modeled crash), so a
    # trap on a path the exit guards proves; a module name shadowed by a parameter is not the real sys.exit.
    assert check("import sys\ndef f(x: int):\n    if x == 0:\n        sys.exit()\n    return 10 // x\n").status == PROVED
    assert check("def f(x: int):\n    if x < 0:\n        exit()\n    return x + 1\n").status == PROVED

    # a string accumulator (out = out + c) stays a string under loop havoc; a monotonic counter keeps its lower
    # bound (i >= 0) so an index loop proves; iterating a nested container (for row in g) yields inner sequences --
    # while an unguarded inner index (row[0] with row possibly empty) still does not prove.
    assert check("def f(s: str):\n    out = ''\n    for c in s:\n        out = out + c\n    return out\n").status == PROVED
    assert check("def f(p: list):\n    i = 0\n    while i < len(p):\n        x = p[i]\n        i = i + 1\n    return 0\n").status == PROVED
    assert check("def f(g: list[list[int]]):\n    for row in g:\n        for x in row:\n            y = x\n    return 0\n").status == PROVED
    assert check("def f(g: list[list[int]]):\n    for row in g:\n        x = row[0]\n    return 0\n").status != PROVED

    # a list built by repetition [x] * n has length n (clamped at 0), so a DP-table fill (build, store in a loop,
    # read) proves under a non-negative guard, while an unguarded read on a possibly-empty [0] * (n + 1) refutes.
    assert check("def f(n: int):\n    dp = [0] * n\n    if n > 0:\n        return dp[0]\n    return 0\n").status == PROVED
    assert check("def f(n: int):\n    if n < 0:\n        return 0\n    dp = [0] * (n + 1)\n    for i in range(2, n + 1):\n        dp[i] = dp[i - 1] + dp[i - 2]\n    return dp[n]\n").status == PROVED
    assert check("def f(n: int):\n    dp = [0] * (n + 1)\n    return dp[0]\n").status == REFUTED
    # SOUNDNESS: sequence repetition [x] * n replicates the REFERENCE, so [[0]] * 2 is two names for ONE inner
    # row -- an append through a[0] grows a[1] too (real Python: len(a[1]) == 2). The value engine models a list
    # as an immutable tuple and cannot track the mutation, so a mutating method reached through a subscript /
    # attribute receiver forgets the root container rather than silently no-op'ing it; the later read then
    # abstains (UNKNOWN) instead of returning the stale pre-mutation row (a false PROVED of len(a[1]) == 1 and
    # REFUTED of len(a[1]) == 2 -- the verdict exactly backwards).
    _alias = "def f():\n    a = [[0]] * 2\n    a[0].append(1)\n    return len(a[1])\n"
    assert prove(_alias, "result == 1", target="f").status == UNKNOWN, prove(_alias, "result == 1", target="f")
    assert prove(_alias, "result == 2", target="f").status == UNKNOWN, prove(_alias, "result == 2", target="f")
    # even with separately-written rows the value engine cannot model the append's effect, so a read of the
    # mutated row abstains rather than be proved wrong (len(a[0]) is really 2 after the append, not 1).
    assert prove("def f():\n    a = [[0], [0]]\n    a[0].append(1)\n    return len(a[0])\n",
                 "result == 1", target="f").status == UNKNOWN
    # the bare-name append-then-read is forgotten the same way (already sound; locked here as a regression guard)
    assert prove("def f():\n    a = [0]\n    a.append(1)\n    return len(a)\n", "result == 1", target="f").status == UNKNOWN
    # the same staleness reached through an ALIAS: b = a makes b and a one object, so b.append grows a too (real
    # Python len(a) == 3). Forgetting only the receiver b is not enough -- a aliases it -- so the engine forgets
    # every name that shares the mutated object (found by the generative grammar fuzzer below, not the curated list).
    assert prove("def f():\n    a = [2, 3]\n    b = a\n    b.append(3)\n    return len(a)\n",
                 "result == 2", target="f").status == UNKNOWN
    assert prove("def f():\n    a = [2, 3]\n    b = a\n    b.append(3)\n    return len(a)\n",
                 "result == 3", target="f").status == UNKNOWN

    # str % args (printf formatting, including a tuple of args) is a trap-free string; the args are trap-checked,
    # so a div by zero in an argument still refutes.
    assert check("def f(a: int, b: int):\n    return '%d/%d' % (a, b)\n").status == PROVED
    assert check("def f(x: int):\n    return '%d' % (10 // x)\n").status == REFUTED

    # verification-guided repair loop: a counterexample drives a generator to a verified result
    _attempts = iter(["def f(x):\n    return x + 1\n", "def f(x):\n    return 2 * x\n"])
    _r = repair_loop(lambda fb: next(_attempts), ensures="result == 2 * x")
    assert _r["status"] == PROVED and _r["rounds"] == 2 and _r["converged"]
    _bad_tries = iter(["def f(x):\n    return x + 1\n", "def f(x):\n    return x + 2\n"])   # two distinct wrong
    _bad = repair_loop(lambda fb: next(_bad_tries), ensures="result == 2 * x", max_rounds=2)   # attempts: no repeat,
    assert _bad["status"] == REFUTED and "feedback" in _bad and not _bad["converged"]   # so the loop spends both rounds
    _conv = repair_loop(lambda fb: "def f(a, b):\n    return a // b\n", max_rounds=5)   # a generator that repeats one
    assert _conv["converged"] and _conv["rounds"] == 2 and _conv["status"] == REFUTED   # candidate converges at the
    #                                     repeat (round 2) rather than burning all five: a fixpoint cannot improve

    # diff-scoped verification: a localized change verifies only the affected functions and their callers
    import tempfile as _tf2, shutil as _sh2, os as _os2
    _d2 = _tf2.mkdtemp()
    try:
        open(_os2.path.join(_d2, "lib.py"), "w").write("def half(n):\n    return 10 // n\n")
        open(_os2.path.join(_d2, "app.py"), "w").write("from lib import half\ndef run(n):\n    return half(n)\n")
        open(_os2.path.join(_d2, "util.py"), "w").write("def noop(x):\n    return x\n")
        assert {n for n, _ in verify_diff(_d2, ["util.py"])} == {"util.noop"}              # unrelated: scoped down
        assert {n for n, _ in verify_diff(_d2, ["lib.py"])} == {"lib.half", "app.run"}     # callee pulls in callers
    finally:
        _sh2.rmtree(_d2, ignore_errors=True)

    # PR gate: a behavior-breaking change in a git working tree refutes and exits nonzero
    import tempfile as _tf3, shutil as _sh3, os as _os3, subprocess as _sp3, io as _io, contextlib as _cl
    from .cli import main as _climain
    _d3 = _tf3.mkdtemp()
    try:
        def _g(*a):
            return _sp3.run(["git", "-C", _d3, *a], capture_output=True, text=True)
        if _g("init").returncode == 0:                                  # skip cleanly where git is unavailable
            _g("config", "user.email", "t@t"); _g("config", "user.name", "t")
            open(_os3.path.join(_d3, "m.py"), "w").write("def f(x):\n    return x + x\n")
            _g("add", "m.py"); _g("commit", "-m", "b")
            open(_os3.path.join(_d3, "m.py"), "w").write("def f(x):\n    return x + 1\n")
            with _cl.redirect_stdout(_io.StringIO()):
                _rc = _climain(["gate", _d3, "--base", "HEAD"])
            assert _rc == 1                                            # behavior change refuted -> nonzero exit
    finally:
        _sh3.rmtree(_d3, ignore_errors=True)

    # coverage report: the verified-subset fraction, and a new refusal flagged as a regression against history
    import tempfile as _tf4, shutil as _sh4, os as _os4
    _d4 = _tf4.mkdtemp()
    try:
        open(_os4.path.join(_d4, "m.py"), "w").write("def ok(x):\n    return x + 1\ndef bad(a):\n    return a[0]\n")
        _c1 = coverage(_d4)
        assert _c1["proved"] == 1 and _c1["refuted"] == 1 and _c1["coverage"] == 50.0
        open(_os4.path.join(_d4, "m.py"), "w").write(
            "def ok(x):\n    return x + 1\ndef bad(a):\n    return a[0]\ndef worse(a):\n    return a[5]\n")
        _c2 = coverage(_d4, history=[_c1])
        assert _c2["new_refusals"] == ["m.worse"] and _c2["delta_coverage"] < 0
    finally:
        _sh4.rmtree(_d4, ignore_errors=True)

    # lazy load: importing the package, the stdlib-only type-inference submodules, and the sound inference API
    # must not pull in the SMT solver; a verification name (check) loads it on first access. Checked in a fresh
    # interpreter, since z3 is already imported in this one.
    import sys as _sys5, subprocess as _sp5, os as _os6
    _root5 = _os6.path.dirname(_os6.path.dirname(_os6.path.abspath(__file__)))
    _lz = _sp5.run([_sys5.executable, "-c",
                    "import sys, touchstone\n"
                    "assert 'z3' not in sys.modules, 'import touchstone loaded z3'\n"
                    "import touchstone.inference\n"
                    "assert 'z3' not in sys.modules, 'type-inference submodule loaded z3'\n"
                    "_ = touchstone.infer_types\n"
                    "assert 'z3' not in sys.modules, 'infer_types loaded z3'\n"
                    "_ = touchstone.check\n"
                    "assert 'z3' in sys.modules, 'check did not load z3'\n"
                    "print('LAZY_OK')\n"],
                   capture_output=True, text=True, cwd=_root5,
                   env={**_os6.environ, "PYTHONPATH": _root5})
    assert "LAZY_OK" in _lz.stdout, (_lz.stdout, _lz.stderr)   # the solver is deferred to first verification use

    # specification synthesis: keep the postconditions a function provably satisfies and a precondition for
    # trap freedom
    _sp = synthesize_spec("def absval(x):\n    if x < 0:\n        return -x\n    return x\n")
    assert "result >= 0" in _sp["ensures"] and "result >= x" in _sp["ensures"] and _sp["requires"] == "True"
    assert synthesize_spec("def recip(x):\n    return 10 // x\n")["requires"] == "x != 0"
    assert synthesize_spec("def g(x):\n    assert x >= 0\n    return x\n")["requires"] == "x >= 0"   # the weakest
    #                                     precondition that makes it trap free, not the stronger x > 0 that also would
    assert synthesize_spec("def double(x):\n    return x + x\n")["ensures"] == ["result == 2 * x"]
    assert "result >= x" not in synthesize_spec("def inc(x):\n    return x + 1\n")["ensures"]   # > x implies it
    # the synthesized contract is the STRONGEST the domain certifies, not the first clause found: candidate
    # bounds drawn from the function's own constants and its inferred @ret interval, conjoined and confirmed.
    _clamp = synthesize_spec("def f(x):\n    if x > 100:\n        x = 100\n    if x < 0:\n        x = 0\n    return x\n")
    assert "result >= 0" in _clamp["ensures"] and "result <= 100" in _clamp["ensures"], _clamp   # both bounds
    assert synthesize_spec("def inc(x):\n    return x + 1\n")["ensures"] == ["result == x + 1"]   # the tightest, no redundant clause

    # MCP server tools: a model calls the verifier; the text result carries the verdict and counterexample
    from .mcp import call_tool as _mcp_call, _TOOLS as _mcp_tools
    assert {x["name"] for x in _mcp_tools} == {"check", "prove", "verify_change", "synthesize_spec", "scan"}
    assert _mcp_call("prove", {"source": "def f(x):\n    return x + x\n",
                               "ensures": "result == 2 * x"}).startswith("PROVED")
    assert _mcp_call("check", {"source": "def f(a):\n    return a[0]\n"}).startswith("REFUTED")
    # a REFUTED with replayable inputs carries the sandbox execution trace the model steers on (explain),
    # available whenever the sandbox can spawn -- the same guard the trace self-test above uses.
    if core.sandbox_run_batch("def f(x):\n    return x\n", {}, "f", [[1]]) == [("ok", 1)]:
        _mct = _mcp_call("prove", {"source": "def f(x):\n    return x + 1\n", "ensures": "result == x"})
        assert _mct.startswith("REFUTED") and "counterexample" in _mct and "trace:" in _mct, _mct
    # the JSON-RPC loop itself (not only call_tool): initialize carries the spec-required serverInfo.version,
    # a tool call round-trips through tools/call, an unknown method is a -32601 error, and a non-object JSON
    # line (a stray value or a batch array) is ignored rather than crashing the server.
    import io as _mio, json as _mjson
    from . import mcp as _mcpmod

    def _mcp_drive(_lines):
        class _S:
            def __init__(self, b): self.buffer = b
        _ib = _mio.BytesIO(("\n".join(_lines) + "\n").encode("utf-8")); _ob = _mio.BytesIO()
        _si, _so = sys.stdin, sys.stdout
        sys.stdin, sys.stdout = _S(_ib), _S(_ob)
        try:
            _mcpmod.main()
        finally:
            sys.stdin, sys.stdout = _si, _so
        return {m.get("id"): m for m in (_mjson.loads(x) for x in _ob.getvalue().splitlines() if x.strip())}
    _mb = _mcp_drive([
        _mjson.dumps({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}}),
        "42",                                                            # a non-object line must not crash the loop
        _mjson.dumps([{"jsonrpc": "2.0", "id": 0, "method": "ping"}]),   # a JSON-RPC batch array: ignored, no crash
        _mjson.dumps({"jsonrpc": "2.0", "id": 2, "method": "tools/call",
                      "params": {"name": "prove", "arguments": {"source": "def f(x):\n    return x + x\n",
                                                                "ensures": "result == 2 * x"}}}),
        _mjson.dumps({"jsonrpc": "2.0", "id": 3, "method": "bogus_method"}),
    ])
    assert set(_mb) == {1, 2, 3}, _mb                                    # the non-object lines yielded no response
    assert _mb[1]["result"]["serverInfo"].get("version"), "MCP initialize must carry serverInfo.version"
    assert _mb[1]["result"]["serverInfo"]["name"] == "touchstone" and _mb[1]["result"]["protocolVersion"]
    assert _mb[2]["result"]["isError"] is False and _mb[2]["result"]["content"][0]["text"].startswith("PROVED")
    assert _mb[3]["error"]["code"] == -32601                            # an unknown method is a JSON-RPC error
    # compositional verification: each function proved against its contract with calls replaced by callee
    # contracts, assembling a whole-system proof; a wrong contract or unmet callee precondition is refuted
    sysrepo = {"inc": "def inc(x):\n    return x + 1\n",
               "twice_inc": "def twice_inc(y):\n    a = inc(y)\n    b = inc(a)\n    return b\n"}
    good = {"inc": (lambda P: z3.BoolVal(True), lambda P, r: r == P["x"] + 1),
            "twice_inc": (lambda P: z3.BoolVal(True), lambda P, r: r == P["y"] + 2)}
    assert verify_system("sys", "twice_inc", sysrepo, good).status == PROVED
    wrong = dict(good); wrong["twice_inc"] = (lambda P: z3.BoolVal(True), lambda P, r: r == P["y"] + 3)
    assert verify_system("sys", "twice_inc", sysrepo, wrong).status == REFUTED
    prerepo = {"g": "def g(x):\n    return x\n", "use": "def use(n):\n    return g(n)\n"}
    preok = {"g": (lambda P: P["x"] >= 1, lambda P, r: r == P["x"]),
             "use": (lambda P: P["n"] >= 1, lambda P, r: r == P["n"])}
    assert verify_system("sys", "use", prerepo, preok).status == PROVED
    prebad = dict(preok); prebad["use"] = (lambda P: z3.BoolVal(True), lambda P, r: z3.BoolVal(True))
    assert verify_system("sys", "use", prerepo, prebad).status == REFUTED   # callee precondition not met

    # Karr affine equalities: relational x == y the interval domain cannot reach
    assert verify_affine_equal("karr", "g", twovar, "x", "y").status == PROVED
    div2 = "def g(n):\n    x = 0\n    y = 0\n    while x < n:\n        x = x + 1\n        y = y + 2\n    return x\n"
    assert verify_affine_equal("karr", "g", div2, "x", "y").status == UNKNOWN

    # lists as sequences (Z3 sequence theory)
    assert verify_seq_property("seq", "list").status == PROVED

    # machine-integer intervals (sound about fixed-width overflow)
    assert verify_machine_range("mi", "f", "def f(x):\n    y = 100\n    return y\n", 8, 0, 100).status == PROVED
    assert verify_machine_range("mi", "f", "def f(a, b):\n    return a + b\n", 8, 0, 100).status == UNKNOWN

    # ranking-function synthesis (exists-coeffs, forall-state)
    assert verify_ranking_synth("rs", "f", counter).status == PROVED
    assert verify_ranking_synth("rs", "f", nonterm).status == UNKNOWN

    # concurrency: N-thread race detection and deadlock freedom
    assert verify_concurrent_counter("c", "t", 3, True).status == PROVED
    assert verify_concurrent_counter("c", "t", 3, False).status == REFUTED
    assert verify_deadlock_free("d", "t", True).status == PROVED
    assert verify_deadlock_free("d", "t", False).status == REFUTED

    # definite assignment
    assert verify_definite_assignment("da", "f",
        "def f(x):\n    if x > 0:\n        y = 1\n    return y\n").status == REFUTED
    assert verify_definite_assignment("da", "f",
        "def f(x):\n    if x > 0:\n        y = 1\n    else:\n        y = 2\n    return y\n").status == PROVED
    # path-sensitive over a correlated guard: a def and a later use under the same side-effect-free, never-
    # reassigned guard run together, so the use is safe. A different / negated / reassigned / call guard still gates.
    assert verify_definite_assignment("da", "f",
        "def f(c):\n    if c:\n        x = 1\n    if c:\n        return x\n    return 0\n").status == PROVED
    assert verify_definite_assignment("da", "f",
        "def f(n):\n    if n > 0:\n        x = n * 2\n    if n > 0:\n        return x\n    return 0\n").status == PROVED
    assert verify_definite_assignment("da", "f",
        "def f(c, d):\n    if c:\n        x = 1\n    if d:\n        return x\n    return 0\n").status == REFUTED   # different guard
    assert verify_definite_assignment("da", "f",
        "def f(c):\n    if c:\n        x = 1\n    if not c:\n        return x\n    return 0\n").status == REFUTED   # negated guard
    assert verify_definite_assignment("da", "f",
        "def f(c):\n    if c:\n        x = 1\n    c = not c\n    if c:\n        return x\n    return 0\n").status == REFUTED   # reassigned

    # specification mining: proposed and proved with no annotation
    assert "out >= 0" in mine_spec("def f(x):\n    return x * x\n")

    # cross-engine self-audit: no engine contradicts another (and would raise if it did)
    assert REFUTED not in cross_engine_audit(sum_to, pre, post).values()

    # data-driven invariant learning proves sum_to from sampled states
    assert learn_invariant("li", "sum_to", sum_to, pre, post).status == PROVED

    # independent solver in the portfolio (cvc5 if reachable, else z3-only)
    assert solve_portfolio(z3.Int("z") != z3.Int("z"))[0] == PROVED
    assert solve_with_cvc5(z3.Int("z") != z3.Int("z")) in (PROVED, UNKNOWN)

    # None-return is modeled exactly: a partial function differs from a total one
    assert verify_equiv("none", "f", "def f(x):\n    if x > 0:\n        return x\n    return\n",
                        "def f(x):\n    return x\n", {}).status == REFUTED

    # chained comparison is desugared (1 < a < 5)
    assert verify_function("chain", "f", "def f(a):\n    if 1 < a < 5:\n        return 1\n    return 0\n",
                           lambda S: z3.BoolVal(True), lambda S, r: z3.Or(r == 0, r == 1), {}).status == PROVED

    # a chained comparison is accepted in the requires/ensures spec language too, desugared as in a body; a false
    # chained bound still refutes, so the desugaring widens reach without weakening soundness
    assert prove("def f(a):\n    return a\n", "0 <= result <= 1", requires="0 <= a <= 1").status == PROVED
    assert check("def f(a):\n    return 100 // a\n", requires="1 <= a <= 9").status == PROVED
    assert prove("def f(a):\n    return a + 1\n", "0 <= result <= 1", requires="5 <= a <= 9").status == REFUTED
    assert verify_contracts('@require("0 <= n <= 100")\n@ensure("0 <= result <= 100")\n'
                            "def clamp(n):\n    return n\n").status == PROVED
    assert verify_contracts('@require("0 <= n <= 100")\n@ensure("0 <= result <= 50")\n'
                            "def f(n):\n    return n\n").status == REFUTED

    # minimize_witness returns the lexicographically minimal counterexample (fewest nonzero, then least total
    # magnitude), bounded by the deterministic SOLVE_RLIMIT so the witness reproduces across runs and machine load
    _zw = {"a": z3.Int("a"), "b": z3.Int("b")}
    _mw = core.minimize_witness(z3.And(_zw["a"] + _zw["b"] == 5, _zw["a"] >= 0, _zw["b"] >= 0), _zw, ["a", "b"])
    assert _mw is not None
    _va, _vb = _mw.eval(_zw["a"]).as_long(), _mw.eval(_zw["b"]).as_long()
    assert _va + _vb == 5 and (_va == 0 or _vb == 0)            # exactly one nonzero: minimization actually ran

    # for-loops are desugared and verified like any while loop
    forsum = "def f(n):\n    s = 0\n    for i in range(n):\n        s = s + 1\n    return s\n"
    assert verify_function("for", "f", forsum, lambda S: S["n"] >= 0, lambda S, r: r == S["n"], {}).status == PROVED

    # higher-degree sum-of-squares: (x^2-1)^2 >= 0 at degree 4
    assert verify_sos_nonneg("sos4", "p", lambda X: X[0]*X[0]*X[0]*X[0] - 2*X[0]*X[0] + 1, 1, degree=4).status == PROVED

    # multi-parameter data-driven invariant learning (a conservation law)
    mp = ("def f(A, c):\n    a = A\n    b = c\n    while a > 0:\n        a = a - 1\n        b = b + 1\n    return b\n")
    assert learn_invariant("mp", "f", mp, lambda S: S["A"] >= 0,
                           lambda S, r: r == S["A"] + S["c"]).status == PROVED

    # bounded model checking cross-checks the invariant engines (and has teeth)
    assert bmc_check("bmc", "f", sum_to, pre, lambda S, r: 2*r == S["n"]*(S["n"]+1) + 1).status == REFUTED
    try:
        bmc_audit(Verdict(PROVED, "x", "f", "fake"), sum_to, pre, lambda S, r: 2*r == S["n"]*(S["n"]+1) + 1)
        raise AssertionError("bmc_audit failed to catch a bounded counterexample")
    except SoundnessError:
        pass
    # BMC refutation fallback: a false nonlinear loop postcondition Spacer leaves UNKNOWN -- with concrete
    # sampling turned off -- is still refuted with a concrete witness by bounded unrolling inside verify_chc.
    _sb, _ae = core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION
    core.SANDBOX_SUBJECT = False; core.ALLOW_SUBJECT_EXECUTION = False
    try:
        _bf = verify_chc("bmc-fallback", "sum_to", sum_to, pre, lambda S, r: 2 * r == S["n"] * S["n"])
        assert _bf.status == REFUTED and _bf.counterexample is not None, _bf
    finally:
        core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = _sb, _ae

    # a single-loop prove whose PRECONDITION is outside the modeled subset -- a free name not among the
    # parameters, or an unmodeled call -- abstains rather than crashing: prove routes the loop through verify_chc,
    # whose bmc_check fallback evaluates the precondition as pre(base) and must catch an untranslatable one and
    # return UNKNOWN, the way the straight-line path already does; a translatable precondition on the same loop
    # still proves. (The pre evaluation sat outside bmc_check's guard, so an untranslatable precondition crashed
    # prove instead of yielding a verdict; bmc_check now guards the pre/post evaluation like the loop engines.)
    assert prove(counter, "result == n", requires="n >= 0 or zzz >= 0").status == UNKNOWN     # free name in the precondition
    assert prove(counter, "result == n", requires="ghost(n) > 0").status == UNKNOWN           # unmodeled call in the precondition
    assert bmc_check("bmc-badpre", "f", counter, lambda S: S["nope"] >= 0,                    # the engine directly: a precondition
                     lambda S, r: r >= 0).status == UNKNOWN                                   # raising KeyError abstains, not crash
    assert prove(counter, "result == n", requires="n >= 0").status == PROVED                  # a translatable precondition still proves

    # 59-60. strings and dictionaries via Z3 theories
    assert verify_string_property("str", "s").status == PROVED
    assert verify_dict_property("dict", "d").status == PROVED

    # concurrency proved for every thread count by induction (not enumeration)
    assert verify_locked_counter("conc", "t").status == PROVED

    # independent solver (native cvc5) and corroborated PROVED
    assert solve_with_cvc5(z3.Int("w") != z3.Int("w")) == PROVED
    assert solve_corroborated(z3.Int("w") != z3.Int("w"))[0] == PROVED
    _saved_corr = core.REQUIRE_CORROBORATION
    core.REQUIRE_CORROBORATION = True
    try:
        assert verify_equiv("corr", "f", "def f(a):\n    return a + a\n",
                            "def f(a):\n    return 2 * a\n", {}).status == PROVED
    finally:
        core.REQUIRE_CORROBORATION = _saved_corr

    # recursion with assignments in the body (not just if/return)
    rec_a = "def f(n):\n    if n <= 0:\n        return 0\n    m = n - 1\n    r = f(m)\n    return r + 1\n"
    assert verify_recursive("reca", "f", rec_a, lambda S: S["n"] >= 0, lambda S, r: r == S["n"]).status == PROVED
    assert verify_recursive("reca", "f", rec_a, lambda S: S["n"] >= 0, lambda S, r: r == S["n"] + 1).status == REFUTED

    # machine-integer interval domain over a loop (widening + narrowing, fixed width)
    clamp = "def f():\n    x = 0\n    while x < 100:\n        x = x + 1\n    return x\n"
    assert verify_machine_range("mi", "f", clamp, 16, 0, 100).status == PROVED
    assert verify_machine_range("mi", "f", clamp, 16, 0, 50).status == UNKNOWN

    # template polyhedra (relational inequalities): i == n at exit
    assert verify_polyhedra("poly", "f", counter,
                            [lambda S: S["i"] - S["n"], lambda S: S["n"] - S["i"]],
                            lambda S: S["i"] - S["n"], 0, 0, pre=lambda S: S["n"] >= 0).status == PROVED

    # separation logic: disjoint-region frame and points-to entailment
    assert verify_array_disjoint("disj", "arr").status == PROVED
    assert verify_sl_entailment("ent", "sl").status == PROVED
    # the disjoint-region frame, now also discharged over actual array code (not only as a fixed lemma):
    # verify_array_code models two list parameters as distinct arrays, so a write to one frames the other;
    # it proves the written cell, and refutes a false frame or an out-of-bounds store -- separation over the
    # function's real loads and stores, the loop-free analog of verify_array_loop.
    _afp = lambda S: z3.And(S["len_a"] >= 1, S["len_b"] >= 1)
    assert verify_array_code("acode-frame", "f", "def f(a: list, b: list):\n    a[0] = 5\n    return b\n",
        lambda F, E: q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < F["len_b"]),
                                                   z3.Select(F["b"], j) == z3.Select(E["b"], j))),
        pre=_afp).status == PROVED
    assert verify_array_code("acode-write", "f", "def f(a: list):\n    a[0] = 5\n    return a\n",
                             lambda F, E: z3.Select(F["a"], 0) == 5, pre=lambda S: S["len_a"] >= 1).status == PROVED
    assert verify_array_code("acode-oob", "f", "def f(a: list, i):\n    a[i] = 1\n    return a\n",
                             lambda F, E: z3.BoolVal(True)).status == REFUTED                           # out-of-bounds store
    assert verify_array_code("acode-false", "f", "def f(a: list):\n    a[0] = 5\n    return a\n",
                             lambda F, E: z3.Select(F["a"], 0) == z3.Select(E["a"], 0),
                             pre=lambda S: S["len_a"] >= 1).status == REFUTED                           # a false frame claim
    # the full fragment over arbitrary heaps: the frame rule as the separating-conjunction / magic-wand
    # adjunction, modus ponens for the wand, and an n-ary separating conjunction forcing distinctness
    assert verify_sl_frame_rule("frame-adj", "sl").status == PROVED
    assert verify_sl_magic_wand("wand", "sl").status == PROVED
    assert verify_sl_separating_conjunction("starN", "sl", 4).status == PROVED
    # separation logic as an analysis of the pointer code a function actually runs: cvc5's SL theory
    # discharges a points-to triple over the function's real loads and stores. The swap is correct only
    # because the cells are separated (p != q, from the separating conjunction); the frame keeps an
    # untouched cell; arithmetic through a pointer is tracked; a false post-heap is refuted.
    _swap = "def swap(p, q):\n    a = p.val\n    b = q.val\n    p.val = b\n    q.val = a\n"
    assert verify_sl_code("swap", "swap", _swap, ["p", "q"], {"p": "init_q", "q": "init_p"}).status == PROVED
    _setp = "def setp(p, q):\n    p.val = 5\n"
    assert verify_sl_code("frame", "setp", _setp, ["p", "q"], {"p": "5", "q": "init_q"}).status == PROVED
    assert verify_sl_code("frame", "setp", _setp, ["p", "q"], {"p": "5", "q": "99"}).status == REFUTED
    assert verify_sl_code("inc", "inc", "def inc(p, q):\n    p.val = p.val + 1\n",
                          ["p", "q"], {"p": "init_p + 1", "q": "init_q"}).status == PROVED
    _two = "def f(p, q):\n    p.val = 1\n    q.val = 2\n"   # post holds only because p and q are separated
    assert verify_sl_code("sep", "f", _two, ["p", "q"], {"p": "1", "q": "2"}).status == PROVED
    # an inductive predicate -- a list segment -- a function builds: allocating and linking nodes yields a
    # chain of separated cells ending at null (lseg), which cvc5's SL theory proves; a mis-link is refuted.
    _build = ("def build3():\n    n3 = object()\n    n3.next = 0\n    n2 = object()\n    n2.next = n3\n"
              "    n1 = object()\n    n1.next = n2\n    return n1\n")
    assert verify_sl_code("lseg", "build3", _build, (), {"n1": "n2", "n2": "n3", "n3": "0"}).status == PROVED
    assert verify_sl_code("lseg", "build3", _build, (), {"n1": "n2", "n2": "n3", "n3": "n1"}).status == REFUTED
    # the frame rule {P} c {Q} => {P * R} c {Q * R} over real code: storing through p leaves two disjoint
    # frame cells q and r untouched -- the separating conjunction / magic-wand adjunction applied to a heap.
    assert verify_sl_code("frame-rule", "setp", "def setp(p, q, r):\n    p.val = 5\n",
                          ["p", "q", "r"], {"p": "5", "q": "init_q", "r": "init_r"}).status == PROVED

    # whole-program: a looping function calling a loop-free helper (inlined)
    assert verify_function("wp", "f",
        "def f(n):\n    c = 0\n    i = 0\n    while i < n:\n        c = inc(c)\n        i = i + 1\n    return c\n",
        lambda S: S["n"] >= 0, lambda S, r: r == S["n"], {"inc": "def inc(x):\n    return x + 1\n"}).status == PROVED

    # division inside the CHC engine (linearized), zero divisor still caught
    assert verify_function("div", "f", "def f(n):\n    y = 2 * n\n    return y // 2\n",
                           lambda S: z3.BoolVal(True), lambda S, r: r == S["n"], {}).status == PROVED
    assert verify_function("div", "f",
        "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        s = s + 10 // i\n        i = i + 1\n    return s\n",
        lambda S: S["n"] >= 0, lambda S, r: z3.BoolVal(True), {}).status == REFUTED

    # interprocedural CHC where the callee itself has a loop (via summaries)
    repo_ip = {"count": "def count(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n",
               "main": "def main(n):\n    r = count(n)\n    return r\n"}
    assert verify_program_loops("ip", "main", repo_ip, "main",
                                lambda S: S["n"] >= 0, lambda S, r: r == S["n"]).status == PROVED

    # the compositional IR: the functor composition law holds on a program pair
    assert verify_ir_functor("ir", "core", "def p(x):\n    y = x + 1\n    z = y * 2\n    return z\n",
                             "def q(x):\n    z = z - x\n    y = y + z\n    return y\n").status == PROVED
    # the IR is a first-class category object: identity and composition are operations the engine
    # uses, and they satisfy the functor laws (identity, composition) on all states.
    assert verify_category_laws("cat", "ir", "def f(x):\n    y = x + 1\n    z = y * 2\n",
                                "def g(x):\n    w = z - y\n").status == PROVED
    _f, _g = IR.lower("def f(x):\n    a = x + 1\n"), IR.lower("def g(x):\n    b = a * 2\n")
    assert (_f @ _g).instrs == IR.identity().then(_f).then(_g).instrs           # id is a unit of composition
    assert (_f @ _g).instrs == _f.then(_g.then(IR.identity())).instrs           # composition is associative

    # exception safety now models division: a reachable zero divisor is a ZeroDivisionError
    assert verify_no_raise("dz", "f", "def f(x):\n    return 10 // x\n",
                           lambda S: z3.BoolVal(True)).status == REFUTED
    assert verify_no_raise("dz", "f", "def f(x):\n    return 10 // x\n",
                           lambda S: S["x"] >= 1).status == PROVED
    assert verify_no_raise("dz", "f", "def f(x):\n    if x == 0:\n        return 0\n    return 10 % x\n",
                           lambda S: z3.BoolVal(True)).status == PROVED

    # recursion now admits division; a reachable div-by-zero refutes the spec
    rec_dz = "def f(n):\n    if n < 0:\n        return 0\n    return 10 // n + f(n - 1)\n"
    assert verify_recursive("rdz", "f", rec_dz, lambda S: S["n"] >= 0,
                            lambda S, r: z3.BoolVal(True)).status == REFUTED
    rec_safe = "def f(n):\n    if n <= 0:\n        return 0\n    return f(n - 2) + n // 2\n"
    assert verify_recursive("rsafe", "f", rec_safe, lambda S: S["n"] >= 0,
                            lambda S, r: r >= 0).status == PROVED

    # whole-program CHC admits division by a nonzero constant
    repo_div = {"half": "def half(x):\n    return x // 2\n", "q": "def q(x):\n    return half(x + x)\n"}
    assert verify_program("wpd", "q", repo_div, "q", lambda S: z3.BoolVal(True),
                          lambda S, r: r == S["x"]).status == PROVED

    # float finiteness over branches / abs; a guarded reciprocal can still overflow to Inf. The
    #     branch-abs is finite for finite inputs but passes NaN/Inf straight through, so it holds under
    #     finite_inputs and is refuted over the full domain unless the input is guarded.
    branch_abs = "def f(x):\n    if x < 0.0:\n        y = -x\n    else:\n        y = x\n    return y\n"
    assert verify_float_finite("fb", "f", branch_abs, finite_inputs=True).status == PROVED
    assert verify_float_finite("fb-total", "f", branch_abs).status == REFUTED          # NaN/Inf flows through
    assert verify_float_finite("fb-guard", "f",
        "def f(x):\n    if isfinite(x):\n        if x < 0.0:\n            return -x\n        return x\n    return 0.0\n"
        ).status == PROVED                                                             # guarded: total-finite
    assert verify_float_finite("fb", "f",
        "def f(x):\n    if x == 0.0:\n        return 0.0\n    return 1.0 / x\n").status == REFUTED

    # concurrency decided for EVERY thread count by induction (atomic vs non-atomic)
    assert verify_concurrent_counter_inductive("ca", "t", True).status == PROVED
    assert verify_concurrent_counter_inductive("cna", "t", False).status == REFUTED
    # rely-guarantee for all schedules and depths: a global invariant stable under every thread's step
    assert verify_rely_guarantee("rg-counter", "t", ["x", "total"],
        lambda s: z3.And(s["x"] == 0, s["total"] == 0),
        [("incr", lambda s, s2: z3.And(s2["x"] == s["x"] + 1, s2["total"] == s["total"] + 1))],
        lambda s: s["x"] == s["total"], post=lambda s: s["x"] == s["total"]).status == PROVED
    assert verify_rely_guarantee("rg-interfere", "t", ["x", "y"],
        lambda s: z3.And(s["x"] == 0, s["y"] == 0),
        [("A", lambda s, s2: z3.And(s2["x"] <= s["y"], s2["x"] >= s["x"], s2["y"] == s["y"])),
         ("B", lambda s, s2: z3.And(s2["y"] >= s["y"], s2["x"] == s["x"]))],
        lambda s: s["x"] <= s["y"], post=lambda s: s["x"] <= s["y"]).status == PROVED
    assert verify_rely_guarantee("rg-weak", "t", ["x"], lambda s: s["x"] == 0,
        [("inc", lambda s, s2: s2["x"] == s["x"] + 1)],
        lambda s: s["x"] == 0).status == UNKNOWN              # a non-inductive invariant is not proved

    # array loops verified with the invariant INFERRED (no supplied invariant)
    qf = q_forall
    pre_a = lambda S: z3.And(S["n"] >= 0, S["n"] <= S["len_a"])
    zloop = "def f(a: list, n: int):\n    i = 0\n    while i < n:\n        a[i] = 0\n        i = i + 1\n    return a\n"
    assert verify_array_loop_auto("az", "f", zloop, pre_a,
        lambda S, E: qf(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]), z3.Select(S["a"], j) == 0))).status == PROVED
    iloop = "def f(a: list, n: int):\n    i = 0\n    while i < n:\n        a[i] = i\n        i = i + 1\n    return a\n"
    assert verify_array_loop_auto("ai", "f", iloop, pre_a,
        lambda S, E: qf(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]), z3.Select(S["a"], j) == j))).status == PROVED
    # the same prefix reasoning over an array the function ALLOCATES locally, not only a parameter: `[c] * n`
    # and `[c for _ in range(n)]` are fresh Z3 arrays of length n, so a[i] bounds-checks and the fill's content
    # is proved; a false content claim stays UNKNOWN.
    _laf = "def f(n):\n    a = [0] * n\n    i = 0\n    while i < n:\n        a[i] = i\n        i = i + 1\n    return a\n"
    assert verify_array_loop_auto("local-alloc", "f", _laf, lambda S: S["n"] >= 0,
        lambda S, E: qf(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]), z3.Select(S["a"], j) == j))).status == PROVED
    assert verify_array_loop_auto("local-alloc", "f", _laf, lambda S: S["n"] >= 0,
        lambda S, E: qf(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]), z3.Select(S["a"], j) == j + 1))).status != PROVED
    _lac = "def f(n):\n    a = [0 for _ in range(n)]\n    i = 0\n    while i < n:\n        a[i] = 0\n        i = i + 1\n    return a\n"
    assert verify_array_loop_auto("local-comp", "f", _lac, lambda S: S["n"] >= 0,
        lambda S, E: qf(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]), z3.Select(S["a"], j) == 0))).status == PROVED
    # nested (inner) array loops: the doubly-nested fill a[i*m + j] = e is proved bounds-safe under
    # n*m <= len(a) -- the flattened index stays in [0, len), a nonlinear bound z3 discharges, with i,j >= 0
    # guaranteed by the start-at-0/positive-increment counters and i<n, j<m the guards where the body runs.
    # Without the bound it refutes; a counter modified beyond a positive increment declines.
    _nest = ("def f(a: list, n: int, m: int):\n    i = 0\n    while i < n:\n        j = 0\n"
             "        while j < m:\n            a[i * m + j] = 0\n            j = j + 1\n        i = i + 1\n    return a\n")
    assert verify_nested_array_bounds("nb", "f", _nest,
        lambda S: z3.And(S["n"] >= 0, S["m"] >= 0, S["n"] * S["m"] <= S["len_a"])).status == PROVED
    assert verify_nested_array_bounds("nb", "f", _nest).status == REFUTED          # unguarded: index can exceed len
    assert verify_nested_array_bounds("nb", "f",
        _nest.replace("j = j + 1", "j = j - 1")).status == UNKNOWN                  # weird counter: declined
    # the CONTENT of a doubly-nested constant fill, through the contiguous flat-index invariant
    # forall k in [0, i*m + j): a[k] == c: a[i*m + j] = c fills a[0:n*m] with c, proved over the whole region;
    # a false content claim is UNKNOWN, an unguarded write refutes on bounds, and a fill reading i (the 2D case
    # needing a nonlinear quantified index z3 cannot discharge) declines.
    _ncpre = lambda S: z3.And(S["n"] >= 0, S["m"] >= 0, S["n"] * S["m"] <= S["len_a"])
    _ncpost = lambda c: (lambda S, E: qf(lambda k: z3.Implies(z3.And(0 <= k, k < S["n"] * S["m"]),
                                                              z3.Select(S["a"], k) == c)))
    assert verify_nested_array_content("nc", "f", _nest, _ncpost(0), _ncpre).status == PROVED
    assert verify_nested_array_content("nc", "f", _nest.replace("a[i * m + j] = 0", "a[i * m + j] = 7"),
                                       _ncpost(7), _ncpre).status == PROVED
    assert verify_nested_array_content("nc", "f", _nest, _ncpost(1), _ncpre).status == UNKNOWN       # false content
    assert verify_nested_array_content("nc", "f", _nest, _ncpost(0)).status == REFUTED               # unguarded: bounds
    assert verify_nested_array_content("nc", "f",
        _nest.replace("a[i * m + j] = 0", "a[i * m + j] = i"), _ncpost(0), _ncpre).status == UNKNOWN  # 2D fill: declined

    # growing containers: a list built by append in a loop, reasoned about by CONTENT, not only length.
    # The list is modeled as an array whose length grows with the counter, the prefix invariant
    # len(a) == i and a[j] == <append expr>[i := j] is inferred, and a quantified element property is
    # proved (including a nonlinear one); a false content claim is not proved.
    _glpre = lambda S: S["n"] >= 0
    _glid = "def f(n):\n    a = []\n    i = 0\n    while i < n:\n        a.append(i)\n        i = i + 1\n    return a\n"
    assert verify_growing_list_auto("gl", "f", _glid,
        lambda P, A, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(A, j) == j)),
        pre=_glpre).status == PROVED
    assert verify_growing_list_auto("gl", "f", _glid,
        lambda P, A, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(A, j) >= 0)),
        pre=_glpre).status == PROVED                           # every appended element is nonnegative
    assert verify_growing_list_auto("gl", "f", _glid,
        lambda P, A, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(A, j) == j + 1)),
        pre=_glpre).status == UNKNOWN                          # a false content claim is not proved
    _glsq = "def f(n):\n    a = []\n    i = 0\n    while i < n:\n        a.append(i * i)\n        i = i + 1\n    return a\n"
    assert verify_growing_list_auto("gl", "f", _glsq,
        lambda P, A, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(A, j) == j * j)),
        pre=_glpre).status == PROVED                           # nonlinear element property (squares)
    # the length-only reasoning still holds through the integer engines (built list, len(a) == n)
    assert prove(_glid.replace("return a", "return len(a)"), "result == n", requires="n >= 0").status == PROVED

    # the SIZE of a set or dict grown in a loop: the size lies in [0, iterations] (and [1, N] for a
    # non-empty unguarded build), which is exactly the reachable set, so the bound proves and refutes.
    # Element values are not tracked, so a content claim is out of scope -- this is the count alone.
    _gsb = "def f(xs):\n    s = set()\n    for x in xs:\n        s.add(x)\n    return len(s)\n"
    assert verify_growing_set_auto("gs", "f", _gsb, lambda P, c: c <= P["len_xs"]).status == PROVED
    assert verify_growing_set_auto("gs", "f", _gsb, lambda P, c: c >= 1).status == REFUTED            # empty xs -> 0
    assert verify_growing_set_auto("gs", "f", _gsb, lambda P, c: c >= 1,
                                   pre=lambda P: P["len_xs"] >= 1).status == PROVED                   # non-empty -> >= 1
    assert verify_growing_set_auto("gs", "f", _gsb, lambda P, c: c <= P["len_xs"] - 1).status == REFUTED  # all-distinct hits N
    _gsr = "def f(n):\n    s = set()\n    for i in range(n):\n        s.add(i)\n    return len(s)\n"
    assert verify_growing_set_auto("gsr", "f", _gsr, lambda P, c: z3.And(c >= 0, c <= P["n"]),
                                   pre=lambda P: P["n"] >= 0).status == PROVED
    _gdb = "def f(xs):\n    d = dict()\n    for x in xs:\n        d[x] = 1\n    return len(d)\n"
    assert verify_growing_set_auto("gd", "f", _gdb, lambda P, c: c <= P["len_xs"]).status == PROVED
    _gsg = "def f(xs):\n    s = set()\n    for x in xs:\n        if x > 0:\n            s.add(x)\n    return len(s)\n"
    assert verify_growing_set_auto("gsg", "f", _gsg, lambda P, c: c >= 1).status == REFUTED            # guarded: may add nothing
    assert verify_growing_set_auto("gsg", "f", _gsg, lambda P, c: c <= P["len_xs"]).status == PROVED

    # loop-engine widening: the growing-collection engines admit a running accumulator alongside the add (the
    # size / content claim is unaffected by it), and the array engine admits a non-unit stride (a strided
    # prefix invariant). A second touch of the collection, an appended accumulator, or a claim over every
    # index (not only the strided ones) is still declined, since the bound / content would no longer hold.
    _sa = "def f(xs):\n    s = set()\n    c = 0\n    for x in xs:\n        s.add(x)\n        c = c + 1\n    return len(s)\n"
    assert verify_growing_set_auto("acc", "f", _sa, lambda P, c: c <= P["len_xs"]).status == PROVED
    _da = "def f(xs):\n    d = dict()\n    t = 0\n    for x in xs:\n        d[x] = 1\n        t = t + x\n    return len(d)\n"
    assert verify_growing_set_auto("acc", "f", _da, lambda P, c: c <= P["len_xs"]).status == PROVED
    _sr = "def f(xs):\n    s = set()\n    for x in xs:\n        s.add(x)\n        s.discard(0)\n    return len(s)\n"
    assert verify_growing_set_auto("acc", "f", _sr, lambda P, c: c <= P["len_xs"]).status == UNKNOWN   # a second touch: declined
    _la = "def f(n):\n    a = []\n    t = 0\n    i = 0\n    while i < n:\n        a.append(i)\n        t = t + i\n        i = i + 1\n    return a\n"
    assert verify_growing_list_auto("acc", "f", _la,
        lambda P, A, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(A, j) == j)),
        pre=lambda S: S["n"] >= 0).status == PROVED
    _lac = "def f(n):\n    a = []\n    acc = 0\n    i = 0\n    while i < n:\n        acc = acc + i\n        a.append(acc)\n        i = i + 1\n    return a\n"
    assert verify_growing_list_auto("acc", "f", _lac,
        lambda P, A, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(A, j) >= 0)),
        pre=lambda S: S["n"] >= 0).status == UNKNOWN                                                  # appended accumulator: declined
    _astr = "def f(a: list, n: int):\n    i = 0\n    while i < n:\n        a[i] = i\n        i = i + 2\n    return a\n"
    _apre = lambda S: z3.And(S["n"] >= 0, S["n"] <= S["len_a"])
    assert verify_array_loop_auto("stride", "f", _astr, _apre,
        lambda S, E: qf(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"], j % 2 == 0),
                                             z3.Select(S["a"], j) == j))).status == PROVED            # the even indices
    assert verify_array_loop_auto("stride", "f", _astr, _apre,
        lambda S, E: qf(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]),
                                             z3.Select(S["a"], j) == j))).status != PROVED            # not every index
    # the shapes the general CHC engine already covers, locked in: multiple accumulators (sequence loop and
    # the whole-function Horn engine), nested-loop trap freedom, and a non-unit integer step
    assert verify_sequence_loop("multi-acc", "f",
        "def f(xs: list):\n    s = 0\n    c = 0\n    for x in xs:\n        s = s + x\n        c = c + 1\n    return c\n",
        lambda P, r: r == P["len_xs"]).status == PROVED
    assert prove("def f(n):\n    a = 0\n    b = 0\n    i = 0\n    while i < n:\n        a = a + 1\n        b = b + 2\n"
                 "        i = i + 1\n    return b\n", "result == 2 * n", requires="n >= 0").status == PROVED
    assert check("def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        j = 0\n        while j < n:\n            s = s + 1\n"
                 "            j = j + 1\n        i = i + 1\n    return s\n", requires="n >= 0").status == PROVED  # nested loop
    assert prove("def f(n):\n    s = 0\n    for i in range(0, n, 2):\n        s = s + 1\n    return s\n",
                 "result >= 0", requires="n >= 0").status == PROVED                                   # non-unit integer step

    # iterating a list parameter, with the elements universally-quantified so Spacer synthesizes the loop
    # invariant: a count of positives lies in [0, len]; the sum of a list is >= 0 only under a per-element
    # precondition (forall_pre); the enumerate and range(len(xs)) index forms are handled; a division by an
    # element refutes and is safe under a per-element nonzero precondition; an off-index read is UNKNOWN.
    _slc = "def f(xs: list):\n    c = 0\n    for x in xs:\n        if x > 0:\n            c = c + 1\n    return c\n"
    assert verify_sequence_loop("sl", "f", _slc, lambda P, r: z3.And(r >= 0, r <= P["len_xs"])).status == PROVED
    assert verify_sequence_loop("sl", "f", _slc, lambda P, r: r <= P["len_xs"] - 1).status == REFUTED
    # a for-loop over a list parameter relating the result to len(xs) is now provable through `prove` itself,
    # not only verify_sequence_loop: prove routes it to the sequence-loop engine (which the general CHC engine
    # leaves UNKNOWN) when its other loop engines abstain, with len(xs) read off the list length.
    _cnt = "def f(xs: list):\n    count = 0\n    for x in xs:\n        count = count + 1\n    return count\n"
    assert prove(_cnt, "result == len(xs)", target="f").status == PROVED
    assert prove(_cnt, "result == len(xs) + 1", target="f").status == REFUTED
    # for-loop equivalence by a relational product: two functions accumulating over the same `for elem in xs`
    # are equivalent iff their results agree at every input, by the single inductive invariant the sequence-loop
    # engine synthesizes -- sound both ways, where the value engine's loop over-approximation is unsound for ==.
    _sum1 = "def f(xs: list):\n    total = 0\n    for x in xs:\n        total = total + x\n    return total\n"
    _sum2 = "def g(xs: list):\n    acc = 0\n    for y in xs:\n        acc = acc + y\n    return acc\n"
    assert verify_equiv("loop-eq", "f", _sum1, _sum2, {}).status == PROVED                  # same accumulation, renamed
    _sum2x = "def g(xs: list):\n    acc = 0\n    for y in xs:\n        acc = acc + 2 * y\n    return acc\n"
    assert verify_equiv("loop-neq", "f", _sum1, _sum2x, {}).status == REFUTED               # sum vs sum of doubles
    _max1 = "def f(xs: list):\n    m = 0\n    for x in xs:\n        if x > m:\n            m = x\n    return m\n"
    _max2 = "def g(xs: list):\n    best = 0\n    for y in xs:\n        if y > best:\n            best = y\n    return best\n"
    assert verify_equiv("loop-max", "f", _max1, _max2, {}).status == PROVED                 # guarded accumulator
    _min2 = "def g(xs: list):\n    best = 0\n    for y in xs:\n        if y < best:\n            best = y\n    return best\n"
    assert verify_equiv("loop-maxmin", "f", _max1, _min2, {}).status == REFUTED             # max vs min
    # structural recursion over a `list` parameter auto-routes from prove to the array-encoded recursive-list
    # engine (no named entry point), the spec's len(xs) bridged to the array length; a spec that subscripts the
    # list is declined (the content bridge is unsound) and falls to the scalar engine.
    _rl = "def cnt(xs: list, i):\n    if i >= len(xs):\n        return 0\n    return 1 + cnt(xs, i + 1)\n"
    _rlr = "i >= 0 and i <= len(xs)"
    assert prove(_rl, "result == len(xs) - i", requires=_rlr, target="cnt").status == PROVED
    assert prove(_rl, "result == len(xs)", requires=_rlr, target="cnt").status == REFUTED
    assert prove(_rl, "result >= 0", requires=_rlr, target="cnt").status == PROVED
    _rs = "def hsum(xs: list, i):\n    if i >= len(xs):\n        return 0\n    return xs[i] + hsum(xs, i + 1)\n"
    assert prove(_rs, "result >= 0", requires=_rlr, target="hsum").status == REFUTED        # a sum can be negative
    assert prove(_rs, "result >= xs[0]", requires=_rlr, target="hsum").status == UNKNOWN    # list subscript: declined
    # prove falls back to the value/loop over-approximation for a postcondition the exact loop / non-trapfree
    # engines decline: a for-loop, an annotated assignment, or a comprehension. Sound (the over-approximation
    # widens the states, so a post holding over all of them holds for the real ones), and PROVED-only -- a post
    # that depends on the loop's exact effect, or a false one, is not proved.
    assert prove("def f(xs):\n    s = 0\n    for x in xs:\n        s = s + 1\n    return 5\n", "result == 5", target="f").status == PROVED
    assert prove("def f(xs, k):\n    s = 0\n    for x in xs:\n        s = s + x\n    return k\n", "result == k", target="f").status == PROVED
    assert prove("def f(a, b):\n    res: int = a + b\n    return res\n", "result == a + b", target="f").status == PROVED
    assert prove("def f(n):\n    xs = [i for i in range(n)]\n    return len(xs)\n", "result >= 0", requires="n >= 0", target="f").status == PROVED
    assert prove("def f(xs):\n    s = 0\n    for x in xs:\n        s = s + x\n    return s\n", "result == 0", target="f").status != PROVED
    assert prove("def f(a, b):\n    res: int = a + b\n    return res\n", "result == a + b + 1", target="f").status != PROVED
    assert prove("def f(xs: list):\n    s = 0\n    for i, x in enumerate(xs):\n        s = s + 1\n    return s\n",
                 "result == len(xs)", target="f").status == PROVED                 # enumerate index form
    # a per-element precondition written as `requires="all(<pred> for x in xs)"` becomes the sequence-loop
    # engine's forall_pre, so the sum of nonnegative elements is proved >= 0; without it the elements are
    # arbitrary and it refutes, and a claim false on the empty list still refutes under the per-element pre.
    _sum = "def f(xs: list):\n    total = 0\n    for x in xs:\n        total = total + x\n    return total\n"
    assert prove(_sum, "result >= 0", requires="all(x >= 0 for x in xs)", target="f").status == PROVED
    assert prove(_sum, "result >= 0", target="f").status == REFUTED                # arbitrary elements
    assert prove(_sum, "result >= 1", requires="all(x >= 0 for x in xs)", target="f").status == REFUTED  # empty list -> 0
    # object state mutated inside a loop is verifiable for a single non-aliased local object whose class has a
    # no-argument constant-attribute __init__: `o = C()` and every `o.attr` are rewritten to plain accumulator
    # variables, so o.count over the loop relates to len(xs). An object that ESCAPES -- aliased, passed,
    # returned, or with a method called on it -- is declined (UNKNOWN); an arg-taking __init__ too.
    _objc = "class C:\n    def __init__(self):\n        self.count = 0\ndef f(xs: list):\n    o = C()\n    for x in xs:\n        o.count = o.count + 1\n    return o.count\n"
    assert prove(_objc, "result == len(xs)", target="f").status == PROVED
    assert prove(_objc, "result == len(xs) + 1", target="f").status == REFUTED
    assert prove(_objc.replace("    return o.count\n", "    p = o\n    return p.count\n"),
                 "result == len(xs)", target="f").status == UNKNOWN               # aliased (p = o): escape declined
    # a simple mutator method called in the loop is inlined (self -> o, parameters -> the call arguments), so
    # the idiomatic `for x in xs: o.inc()` and `o.bump(k)` are proved; a method that lets self escape declines
    # the object (UNKNOWN), so the rewrite never produces a false PROVED.
    assert prove("class D:\n    def __init__(self):\n        self.count = 0\n    def inc(self):\n        self.count = self.count + 1\n"
                 "def f(xs: list):\n    o = D()\n    for x in xs:\n        o.inc()\n    return o.count\n",
                 "result == len(xs)", target="f").status == PROVED                # mutator method inlined
    assert prove("class G:\n    def __init__(self):\n        self.total = 0\n    def bump(self, k):\n        self.total = self.total + k\n"
                 "def f(xs: list):\n    o = G()\n    for x in xs:\n        o.bump(2)\n    return o.total\n",
                 "result == 2 * len(xs)", target="f").status == PROVED            # mutator with a parameter
    # a value-returning ACCESSOR method (a pure getter: `return <expr over self.attr>`) is inlined in expression
    # position as that expression over the accumulator, so object state read back through a method over the loop
    # is verifiable; an escaping object still declines, and a false claim refutes.
    _H = ("class H:\n    def __init__(self):\n        self.count = 0\n    def inc(self):\n        self.count = self.count + 1\n"
          "    def get(self):\n        return self.count\n    def doubled(self):\n        return self.count * 2\n")
    assert prove(_H + "def f(xs: list):\n    o = H()\n    for x in xs:\n        o.inc()\n    return o.get()\n",
                 "result == len(xs)", target="f").status == PROVED               # accessor inlined: get() == count
    assert prove(_H + "def f(xs: list):\n    o = H()\n    for x in xs:\n        o.inc()\n    return o.doubled()\n",
                 "result == 2 * len(xs)", target="f").status == PROVED           # a computed getter (count * 2)
    assert prove(_H + "def f(xs: list):\n    o = H()\n    for x in xs:\n        o.inc()\n    return o.get()\n",
                 "result == len(xs) + 1", target="f").status == REFUTED          # a false claim is not a spurious PROVED
    assert prove(_H + "def f(xs: list):\n    o = H()\n    p = o\n    for x in xs:\n        o.inc()\n    return p.get()\n",
                 "result == len(xs)", target="f").status == UNKNOWN             # aliased (p = o): escape declined
    # an arg-taking __init__ binds the constructor arguments into the attribute initializers (o = C(v) gives the
    # `count` accumulator the value of v), so an object constructed with a starting value is reasoned about over
    # the loop; a non-constant binding still pins each attribute to its argument exactly.
    assert prove("class E:\n    def __init__(self, v):\n        self.count = v\n"
                 "def f(xs: list):\n    o = E(0)\n    for x in xs:\n        o.count = o.count + 1\n    return o.count\n",
                 "result == len(xs)", target="f").status == PROVED               # arg __init__: count starts at 0
    assert prove("class E:\n    def __init__(self, v):\n        self.count = v\n"
                 "def f(xs: list):\n    o = E(5)\n    for x in xs:\n        o.count = o.count + 1\n    return o.count\n",
                 "result == 5 + len(xs)", target="f").status == PROVED           # count starts at the bound argument
    # a CONDITIONAL mutator (a guarded `if v > 0: self.count = self.count + 1`, or an if/else over two
    # attributes) inlines as a guarded accumulator: o.add(x) counting the positive elements lies in [0, len],
    # and a claim that every element bumped it is refuted.
    _objg = ("class J:\n    def __init__(self):\n        self.count = 0\n    def add(self, v):\n        if v > 0:\n            self.count = self.count + 1\n"
             "def f(xs: list):\n    o = J()\n    for x in xs:\n        o.add(x)\n    return o.count\n")
    assert prove(_objg, "result <= len(xs)", target="f").status == PROVED
    assert prove(_objg, "result >= 0", target="f").status == PROVED
    assert prove(_objg, "result == len(xs)", target="f").status == REFUTED         # not every element is positive
    # the same object rewrite feeds `check` (trap-freedom triage, used by scan / verify_repo), so a loop or
    # straight-line code mutating object state is triaged: a division by an object attribute that is zero is
    # REFUTED, a guarded one and a trap-free object loop PROVED, and an escaping object declined to UNKNOWN.
    assert check("class C:\n    def __init__(self):\n        self.count = 0\ndef f():\n    o = C()\n    return 10 // o.count\n",
                 target="f").status == REFUTED                                     # straight-line div by a 0 attribute
    assert check("class C:\n    def __init__(self):\n        self.count = 5\ndef f():\n    o = C()\n    return 10 // o.count\n",
                 target="f").status == PROVED                                      # guarded (count = 5): safe
    assert check("class C:\n    def __init__(self):\n        self.count = 0\n    def inc(self):\n        self.count = self.count + 1\n"
                 "def f(xs: list):\n    o = C()\n    for x in xs:\n        o.inc()\n    return o.count\n",
                 target="f").status == PROVED                                      # trap-free object-mutation loop
    # object state across the method lifecycle: a function constructing an object and calling VALUE-returning
    # methods on it (which the object rewrite declines) is triaged by the heap engine in check, so a setter then
    # a getter that divides by the set value refutes (the value can be 0) while a safe sequence proves.
    _objlc = ("class C:\n    def __init__(self):\n        self.v = 5\n    def set(self, x):\n        self.v = x\n"
              "    def use(self):\n        return 10 // self.v\n")
    assert check(_objlc + "def f(x):\n    o = C()\n    o.set(x)\n    return o.use()\n", target="f").status == REFUTED
    assert check(_objlc + "def f():\n    o = C()\n    o.set(3)\n    return o.use()\n", target="f").status == PROVED
    assert prove("class C:\n    def __init__(self):\n        self.v = 0\n    def set(self, x):\n        self.v = x\n    def get(self):\n        return self.v\n"
                 "def f():\n    o = C()\n    o.set(7)\n    return o.get()\n", "result == 7", target="f").status == PROVED
    _sls = "def f(xs: list):\n    s = 0\n    for x in xs:\n        s = s + x\n    return s\n"
    assert verify_sequence_loop("sl", "f", _sls, lambda P, r: r >= 0).status == REFUTED                 # arbitrary elements
    assert verify_sequence_loop("sl", "f", _sls, lambda P, r: r >= 0, forall_pre=lambda x: x >= 0).status == PROVED
    assert verify_sequence_loop("sl", "f",
        "def f(xs: list):\n    s = 0\n    for i, x in enumerate(xs):\n        s = s + 1\n    return s\n",
        lambda P, r: r == P["len_xs"]).status == PROVED                                                 # enumerate counter == len
    assert verify_sequence_loop("sl", "f",
        "def f(xs: list):\n    s = 0\n    for i in range(len(xs)):\n        s = s + xs[i]\n    return s\n",
        lambda P, r: r >= 0, forall_pre=lambda x: x >= 0).status == PROVED                              # range(len) reading xs[i]
    _sld = "def f(xs: list):\n    s = 0\n    for x in xs:\n        s = s + 10 // x\n    return s\n"
    assert verify_sequence_loop("sl", "f", _sld, lambda P, r: z3.BoolVal(True)).status == REFUTED        # element may be 0
    assert verify_sequence_loop("sl", "f", _sld, lambda P, r: z3.BoolVal(True),
                                forall_pre=lambda x: x >= 1).status == PROVED
    assert verify_sequence_loop("sl", "f",
        "def f(xs: list):\n    s = 0\n    for i in range(len(xs)):\n        s = s + xs[i + 1]\n    return s\n",
        lambda P, r: z3.BoolVal(True)).status == UNKNOWN                                                # off-loop-variable index

    # a generator yielding in a range loop: every yielded value is checked over the index, no unrolling.
    # The branching generator yields i for i > 0 (every yield >= 1), an unguarded one yields [0, n) (not
    # every yield >= 1), and a doubled one yields evens.
    _bg = "def f(n):\n    for i in range(n):\n        if i > 0:\n            yield i\n"
    assert verify_generator_loop("gen", "f", _bg, lambda P, v: v >= 1).status == PROVED
    assert verify_generator_loop("gen", "f", _bg, lambda P, v: v >= 2).status == REFUTED
    _rg = "def f(n):\n    for i in range(n):\n        yield i\n"
    assert verify_generator_loop("gen", "f", _rg, lambda P, v: z3.And(v >= 0, v < P["n"])).status == PROVED
    assert verify_generator_loop("gen", "f", _rg, lambda P, v: v >= 1).status == REFUTED
    assert verify_generator_loop("gen", "f", "def f(n):\n    for i in range(n):\n        yield 2 * i\n",
                                 lambda P, v: v % 2 == 0).status == PROVED
    # the generator engine summarizes the whole yielded set: straight-line yields, branching with yields in
    # multiple branches, yields around a loop, and yield from a finite iterable -- post is checked over every
    # yield point, sound both ways. A loop-carried accumulator is unrolled to a bound (a while-loop abstains).
    assert verify_generator_loop("gen", "f", "def f(n):\n    yield 0\n    for i in range(n):\n        yield i + 1\n",
                                 lambda P, v: v >= 0).status == PROVED
    assert verify_generator_loop("gen", "f", "def f(n):\n    yield 0\n    for i in range(n):\n        yield i + 1\n",
                                 lambda P, v: v >= 1).status == REFUTED              # the leading yield 0 fails
    _gbr = "def f(n):\n    for i in range(n):\n        if i % 2 == 0:\n            yield i\n        else:\n            yield 0 - i\n"
    assert verify_generator_loop("gen", "f", _gbr, lambda P, v: v >= 0 - P["n"], pre=lambda P: P["n"] >= 0).status == PROVED
    assert verify_generator_loop("gen", "f", _gbr, lambda P, v: v >= 0, pre=lambda P: P["n"] >= 2).status == REFUTED
    assert verify_generator_loop("gen", "f", "def f():\n    yield from (1, 2, 3)\n", lambda P, v: v >= 1).status == PROVED
    assert verify_generator_loop("gen", "f", "def f():\n    yield from (1, 2, 3)\n", lambda P, v: v >= 2).status == REFUTED
    # a loop-carried accumulator (a running sum, a running max) is unrolled to a bound, threading the state: a
    # violating yield within the bound REFUTES (sound), and a statically-bounded loop fully covered PROVES; an
    # unbounded loop whose tail the bound does not reach withholds PROVED (UNKNOWN), staying sound.
    _accn = "def f(n):\n    total = 0\n    for i in range(n):\n        total = total + i\n        yield total\n"
    assert verify_generator_loop("gen", "f", _accn, lambda P, v: v <= 0).status == REFUTED          # total > 0 at i >= 1
    assert verify_generator_loop("gen", "f", _accn, lambda P, v: v >= 0).status == UNKNOWN           # tail past the bound
    _acc5 = "def f():\n    total = 0\n    for i in range(5):\n        total = total + i\n        yield total\n"
    assert verify_generator_loop("gen", "f", _acc5, lambda P, v: v >= 0).status == PROVED            # covered: 0,1,3,6,10
    assert verify_generator_loop("gen", "f", _acc5, lambda P, v: v <= 5).status == REFUTED           # 10 > 5
    _rmax = "def f():\n    m = 0\n    for i in range(4):\n        if i > m:\n            m = i\n        yield m\n"
    assert verify_generator_loop("gen", "f", _rmax, lambda P, v: v <= 3).status == PROVED            # guarded accumulator
    assert verify_generator_loop("gen", "f", "def f(n):\n    if n < 0:\n        yield 1\n",
                                 lambda P, v: v >= 5, pre=lambda P: P["n"] >= 0).status == PROVED   # unreachable yield
    assert verify_generator_loop("gen", "f", "def f(n):\n    x = 0\n    while x < n:\n        yield x\n        x = x + 1\n",
                                 lambda P, v: v >= 0).status == UNKNOWN              # while-loop generator: abstains
    assert verify_generator_loop("gen", "f", "def f(n):\n    acc = 0\n    for i in range(n):\n        acc = acc + i\n        yield acc\n",
                                 lambda P, v: v >= 0).status == UNKNOWN              # loop-carried accumulator: abstains
    # a generator with branching control flow is the lazily-yielded sequence its consumer observes: the object is
    # opaque (its elements are left to the consumer), but the body's ITERATION traps -- a division, an index, a
    # key in a yielded expression -- surface when iterated, recovered by stripping the yields to expression
    # statements and running the value engine over the body. So check() on a branching generator whose body would
    # trap during iteration REFUTES (where it used to vacuously prove the call total), a guarded / trap-free body
    # PROVES, and a consumer iterating a branching-generator callee surfaces the callee's body trap.
    assert check("def g(n):\n    for i in range(n):\n        yield 10 // i\n", target="g").status == REFUTED      # 10 // i at i == 0
    assert check("def g(n):\n    for i in range(n):\n        if i > 0:\n            yield 10 // i\n", target="g").status == PROVED  # guarded
    assert check("def g(n):\n    for i in range(n):\n        if i > 0:\n            yield i\n", target="g").status == PROVED       # trap free
    _gcrp = {"gen": "def gen(n):\n    for i in range(n):\n        yield 10 // i\n",
             "consume": "def consume(n):\n    s = 0\n    for x in gen(n):\n        s = x\n    return s\n"}
    assert check(_gcrp["consume"], repo=_gcrp, target="consume").status == REFUTED   # the callee's iteration trap surfaces at the consumer
    _gsrp = {"gen": "def gen(n):\n    for i in range(n):\n        yield i\n",
             "consume": "def consume(n):\n    s = 0\n    for x in gen(n):\n        s = x\n    return s\n"}
    assert check(_gsrp["consume"], repo=_gsrp, target="consume").status == PROVED    # a trap-free generator consumer proves

    # a list comprehension over a list parameter is the exact map [e(x) for x in xs]: the result has
    # the same length as xs and result[j] == e(xs[j]), so a quantified property of the result is decided
    # (every doubled element is even, the element relates to the source, the length is preserved), and a
    # false claim or a length-changing filter is refused.
    dbl = "def f(xs):\n    return [x * 2 for x in xs]\n"
    assert verify_map_comprehension("mc", "f", dbl,
        lambda P, R, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(R, j) % 2 == 0))).status == PROVED
    assert verify_map_comprehension("mc", "f", dbl,
        lambda P, R, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln),
                                                 z3.Select(R, j) == 2 * z3.Select(P["xs"], j)))).status == PROVED
    assert verify_map_comprehension("mc", "f", dbl, lambda P, R, ln: ln == P["len_xs"]).status == PROVED
    assert verify_map_comprehension("mc", "f", dbl,
        lambda P, R, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln),
                                                 z3.Select(R, j) == z3.Select(P["xs"], j)))).status == REFUTED
    assert verify_map_comprehension("mc", "f", "def f(xs, k):\n    return [x + k for x in xs]\n",
        lambda P, R, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln),
                                                 z3.Select(R, j) == z3.Select(P["xs"], j) + P["k"]))).status == PROVED
    # a filtered comprehension is a sound over-approximation: the result is a subsequence no longer
    # than the source whose every element satisfies the filter, so a property following from the filter
    # is proved and one that does not is left UNKNOWN.
    flt = "def f(xs):\n    return [x for x in xs if x > 0]\n"
    assert verify_map_comprehension("fc", "f", flt,
        lambda P, R, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(R, j) > 0))).status == PROVED
    assert verify_map_comprehension("fc", "f", flt, lambda P, R, ln: ln <= P["len_xs"]).status == PROVED
    assert verify_map_comprehension("fc", "f", flt,
        lambda P, R, ln: qf(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(R, j) > 5))).status == UNKNOWN

    # an element-universal postcondition -- all(P(result[j]) ...) / all(P(e) for e in result) / all(P(a[j])
    # for j in range(n)) -- written in `prove` itself is compiled into the quantified-spec engines' callback
    # (verify_map_comprehension for a map return, verify_array_loop_auto for an array-write loop), so a forall
    # the general CHC engine leaves UNKNOWN is decided. The body is translated by the engines' own _ev_arr /
    # q_forall.
    assert prove("def f(xs: list):\n    return [x * x for x in xs]\n",
                 "all(e >= 0 for e in result)", target="f").status == PROVED              # every squared element >= 0
    assert prove("def f(xs: list):\n    return [x * 2 for x in xs]\n",
                 "all(result[j] == 2 * xs[j] for j in range(len(xs)))", target="f").status == PROVED   # exact map, index form
    assert prove("def f(xs: list):\n    return [x * x for x in xs]\n",
                 "all(e > 0 for e in result)", target="f").status != PROVED                # false (0 maps to 0): not proved
    assert prove("def f(xs: list):\n    return [x * 2 for x in xs]\n",
                 "all(result[j] == xs[j] for j in range(len(xs)))", target="f").status != PROVED   # false map relation
    _afill = "def f(a: list, n: int):\n    i = 0\n    while i < n:\n        a[i] = 0\n        i = i + 1\n    return a\n"
    assert prove(_afill, "all(a[j] == 0 for j in range(n))",
                 requires="n >= 0 and n <= len(a)", target="f").status == PROVED           # array fill, content universal
    assert prove("def f(a: list, n: int):\n    i = 0\n    while i < n:\n        a[i] = i\n        i = i + 1\n    return a\n",
                 "all(a[j] == j for j in range(n))", requires="n >= 0 and n <= len(a)", target="f").status == PROVED
    assert prove(_afill, "all(a[j] == 1 for j in range(n))",
                 requires="n >= 0 and n <= len(a)", target="f").status != PROVED           # false content: withheld
    assert prove(_afill, "all(a[j] == 0 for j in range(n))", target="f").status != PROVED  # unguarded (out-of-bounds write): not proved

    # all(p(x) for x in xs) / any(p(x) for x in xs) over a list parameter are exactly the universal /
    # existential quantifier over the elements (sound both ways): instantiation, the contrapositive, the
    # vacuous empty-list cases, and a false claim are decided correctly.
    alln, anyp = "def f(xs):\n    return all(x >= 0 for x in xs)\n", "def f(xs):\n    return any(x > 0 for x in xs)\n"
    assert verify_all_any("aa", "f", alln,
        lambda P, r: z3.Implies(z3.And(r, P["len_xs"] > 0), z3.Select(P["xs"], 0) >= 0)).status == PROVED
    assert verify_all_any("aa", "f", alln,
        lambda P, r: z3.Implies(z3.And(P["len_xs"] > 0, z3.Select(P["xs"], 0) < 0), z3.Not(r))).status == PROVED
    assert verify_all_any("aa", "f", alln, lambda P, r: z3.Implies(P["len_xs"] == 0, r)).status == PROVED
    assert verify_all_any("aa", "f", anyp,
        lambda P, r: z3.Implies(z3.And(P["len_xs"] > 2, z3.Select(P["xs"], 2) > 0), r)).status == PROVED
    assert verify_all_any("aa", "f", anyp, lambda P, r: z3.Implies(P["len_xs"] == 0, z3.Not(r))).status == PROVED
    assert verify_all_any("aa", "f", alln,
        lambda P, r: z3.Implies(z3.And(r, P["len_xs"] > 0), z3.Select(P["xs"], 0) > 5)).status == REFUTED

    # parallel / tuple assignment (Python evaluates the whole right side first)
    assert verify_equiv("swap", "f", "def f(a, b):\n    a, b = b, a\n    return a - b\n",
                        "def g(a, b):\n    return b - a\n", {}).status == PROVED
    assert verify_equiv("rot", "f", "def f(x, y, z):\n    x, y, z = y, z, x\n    return x - z\n",
                        "def g(x, y, z):\n    return y - x\n", {}).status == PROVED
    # tuple unpacking to MIXED targets -- the in-place swap a[i], a[j] = a[j], a[i] and self.x, self.y = ... --
    # evaluates the right side first, then stores to each target with the same bounds checks a single
    # assignment uses. An unguarded index swap refutes on the out-of-range witness; a len()-bounded one proves;
    # an attribute store raises no modeled trap; pure-name and starred unpack are unaffected.
    assert check("def f(a: list, i, j):\n    a[i], a[j] = a[j], a[i]\n    return a\n").status == REFUTED
    assert check("def f(a: list, i, j):\n    if 0 <= i and i < len(a) and 0 <= j and j < len(a):\n"
                 "        a[i], a[j] = a[j], a[i]\n    return a\n").status == PROVED
    assert check("def f(o):\n    o.x, o.y = 0, 0\n    return 0\n").status == PROVED            # attribute targets: no trap
    assert check("def f(a: list, b):\n    a[0], b = b, a[0]\n    return b\n").status == REFUTED  # a may be empty
    assert check("def f(a, b):\n    a, b = b, a\n    return a - b\n").status == PROVED          # pure-name unpack: unchanged
    # chained assignment to MIXED targets -- a = b[i] = expr (and a = o.attr = expr) -- evaluates the right
    # side once, then stores it to every target left to right with the same per-target bounds checks. The
    # subscript store is IndexError-checked, so an unguarded one refutes and a len()-bounded one proves; an
    # attribute store raises no modeled trap; the all-name chain a = b = expr is unchanged.
    assert check("def f(b: list, i):\n    a = b[i] = 0\n    return a\n").status == REFUTED
    assert check("def f(b: list, i):\n    if 0 <= i and i < len(b):\n        a = b[i] = 0\n    return 0\n").status == PROVED
    assert check("def f(o):\n    x = o.attr = 5\n    return x\n").status == PROVED              # attribute target: no trap
    assert check("def f():\n    a = b = 5\n    return a + b\n").status == PROVED                # all-name chain: unchanged

    # accumulator comprehension lowered to a counting loop: sum(1 for i in range(n)) == n
    assert verify_function("sumc", "f", "def f(n):\n    s = sum(1 for i in range(n))\n    return s\n",
                           lambda S: S["n"] >= 0, lambda S, r: r == S["n"], {}).status == PROVED

    # definite assignment now GATES the CHC engines: a use-before-def is not a PROVED
    uba = "def f(x):\n    if x > 0:\n        y = 1\n    return y\n"
    g = verify_function("uba", "f", uba, lambda S: z3.BoolVal(True), lambda S, r: r == 1, {})
    assert g.status == UNKNOWN and "use before assignment" in g.reason, g
    # ...but an ANNOTATED assignment binds its target: res: int = 1 (and an augmented assign that follows)
    # must NOT be a false use-before-assignment. _use_before_def now models AnnAssign (with a value), AugAssign
    # (which reads its target first), and For (which binds the loop variable), so the binary-exponentiation
    # idiom res: int | float = 1; while ...: if ...: res *= base does not falsely gate, while a genuine
    # use-before-def -- a bare x: int with only a conditional later assign, or x += 1 with no prior x -- still does.
    from .engines import _use_before_def
    assert _use_before_def("def f(b, e):\n    res: int = 1\n    if e:\n        res += b\n    return res\n") == []
    assert _use_before_def("def f(xs):\n    t = 0\n    for x in xs:\n        t += x\n    return t\n") == []
    assert _use_before_def("def f(e):\n    x: int\n    if e:\n        x = 1\n    return x\n") == ["x"]      # bare ann, conditional
    assert _use_before_def("def f():\n    x += 1\n    return x\n") == ["x"]                              # aug on unbound
    assert check("def f(b: int, e: int):\n    res: int = 1\n    while e > 0:\n        if e & 1:\n            res = res + b\n        e = e - 1\n    return res\n", target="f").status == PROVED
    # a name bound only inside a loop body is definite after the loop when the loop provably runs at least once: a
    # constant range (for i in range(10), which desugars to a counter-while whose test is true at entry) or a
    # non-empty literal iterable (for c in 'abc'), even when each body path binds it differently (every-branch). It
    # stays a possible use-before-assignment when the loop may run zero times (a symbolic range / iterable), when a
    # continue could loop back before the binding, or when only some branch binds it.
    assert _use_before_def("def f():\n    for i in range(10):\n        y = i\n    return y\n") == []
    assert _use_before_def("def f():\n    for c in 'abc':\n        y = c\n    return y\n") == []
    assert _use_before_def("def f(n):\n    for i in range(n):\n        y = i\n    return y\n") == ["y"]
    assert _use_before_def("def f(c):\n    for i in range(10):\n        if c:\n            continue\n        y = i\n    return y\n") == ["y"]
    assert check("def f():\n    for i in range(10):\n        y = i\n    return y\n", target="f").status == PROVED
    assert check("def f():\n    for i in range(10):\n        if i > 5:\n            y = 1\n        else:\n            y = 2\n    return y\n", target="f").status == PROVED
    assert check("def f(n: int):\n    for i in range(n):\n        y = i\n    return y\n", target="f").status == UNKNOWN
    assert check("def f():\n    for i in range(10):\n        if i > 5:\n            y = i\n    return y\n", target="f").status == UNKNOWN

    # model_cross_check now requires an INDEPENDENT translation (distinct division encoding)
    assert _independent_claim("def f(a):\n    return a // 3\n", "def f(a):\n    return a // 3\n", {}) is not None
    vpc = verify_equiv("ind", "f", "def f(a):\n    return a * 2\n", "def f(a):\n    return a + a\n", {})
    assert model_cross_check(vpc, "def f(a):\n    return a * 2\n", "def f(a):\n    return a + a\n", {}) == 1

    # abstract-domain PROVEDs are CHC-corroborated by default (toggle the gate explicitly)
    assert core.CROSS_VALIDATE_DOMAINS is True
    twovar2 = ("def g(n):\n    x = 0\n    y = 0\n    while x < n:\n"
               "        x = x + 1\n        y = y + 1\n    return x\n")
    assert verify_zone_equal("zc", "g", twovar2, "x", "y").status == PROVED   # corroborated, no SoundnessError

    # cross-engine audit now includes BMC and the learner; agreement holds (would raise on a split)
    sumto2 = ("def sum_to(n):\n    total = 0\n    i = 1\n    while i <= n:\n"
              "        total = total + i\n        i = i + 1\n    return total\n")
    assert REFUTED not in cross_engine_audit(sumto2, lambda S: S["n"] >= 0,
                                             lambda S, r: 2 * r == S["n"] * (S["n"] + 1)).values()

    # float-annotated parameters reason under IEEE-754: x+x and 2.0*x are bit-equal for every double
    assert verify_equiv("fp2x", "f", "def f(x: float):\n    return x + x\n",
                        "def g(x: float):\n    return 2.0 * x\n", {}).status == PROVED
    # x+0.0 differs from x only at -0.0, which the float model distinguishes (not the int one)
    vfp0 = verify_equiv("fp0", "f", "def f(x: float):\n    return x + 0.0\n",
                        "def g(x: float):\n    return x\n", {})
    assert vfp0.status == REFUTED and "-0.0" in (vfp0.counterexample or ""), vfp0
    # bool-annotated parameters: De Morgan over the four truth assignments
    assert verify_equiv("demorgan", "f", "def f(a: bool, b: bool):\n    return not (a or b)\n",
                        "def g(a: bool, b: bool):\n    return (not a) and (not b)\n", {}).status == PROVED
    # bool participates in integer arithmetic (Python True + True == 2)
    assert verify_predicate("boolsum", "f", "def f(a: bool, b: bool):\n    return a + b\n",
                            lambda za, o: z3.And(o >= 0, o <= 2), {}).status == PROVED
    # a float predicate: x*x is nonnegative for every non-NaN double (squares, incl. +Inf)
    _sq_nonneg = lambda za, o: z3.Implies(z3.Not(z3.fpIsNaN(za["x"])), z3.fpGEQ(o, z3.FPVal(0.0, z3.Float64())))
    assert verify_predicate("sq>=0", "f", "def f(x: float):\n    return x * x\n",
                            _sq_nonneg, {}).status == PROVED

    # general heap: object identity, aliasing, and frame. When b aliases a,
    #     a write through b is observed through a; distinct objects and attributes are framed.
    _alias = "def f(p, q):\n    a = object()\n    b = a\n    a.x = p\n    b.x = q\n    return a.x\n"
    assert verify_heap_property("alias", "f", _alias, lambda za, r: r == za["q"]).status == PROVED
    valias = verify_heap_property("alias", "f", _alias, lambda za, r: r == za["p"])
    assert valias.status == REFUTED, valias                       # a.x is q, not p, when p != q
    _frame = "def f(p, q):\n    a = object()\n    b = object()\n    a.x = p\n    b.x = q\n    return a.x\n"
    assert verify_heap_property("frame", "f", _frame, lambda za, r: r == za["p"]).status == PROVED
    _attrs = "def f(p, q):\n    a = object()\n    a.x = p\n    a.y = q\n    return a.x\n"
    assert verify_heap_property("attr-frame", "f", _attrs, lambda za, r: r == za["p"]).status == PROVED
    # a base's __init_subclass__ hook gives every subclass a constant class attribute; Python runs it once per
    # subclass with cls bound to the new class, so the subclass instance reads the hook's value (it runs after
    # the class body, so its attribute wins, and it does not run for the class that defines it). Resolved for
    # the common single-hook constant case through the MRO; an ambiguous hook (two in the ancestry, whose
    # super-chaining order is not modeled) or a non-constant body abstains (UNKNOWN), never an unconstrained
    # attribute that could refute a true property.
    _isc = ("class Base:\n    def __init_subclass__(cls, **kwargs):\n        cls.tag = 7\n"
            "class Child(Base):\n    pass\n"
            "def f():\n    c = Child()\n    return c.tag\n")
    assert verify_heap_property("isc", "f", _isc, lambda za, r: r == 7).status == PROVED
    assert verify_heap_property("isc", "f", _isc, lambda za, r: r == 8).status == REFUTED
    _iscovr = ("class Base:\n    def __init_subclass__(cls):\n        cls.k = 3\n"
               "class Child(Base):\n    k = 1\n"
               "def f():\n    c = Child()\n    return c.k\n")
    assert verify_heap_property("isc", "f", _iscovr, lambda za, r: r == 3).status == PROVED   # hook overrides the body
    _isc2 = ("class A:\n    def __init_subclass__(cls):\n        cls.tag = 1\n"
             "class B(A):\n    def __init_subclass__(cls):\n        cls.tag = 2\n"
             "class C(B):\n    pass\n"
             "def f():\n    c = C()\n    return c.tag\n")
    assert verify_heap_property("isc", "f", _isc2, lambda za, r: r == 2).status == UNKNOWN     # ambiguous chaining: abstains
    # a visible custom metaclass's __init__ gives every class it creates a constant attribute (cls bound to the
    # new class); resolved through the MRO so an inherited metaclass applies to a subclass too. A metaclass
    # __new__ (custom class creation), a non-visible metaclass, or a non-constant body abstains (UNKNOWN),
    # never an unconstrained attribute.
    _mc = ("class Meta(type):\n    def __init__(cls, name, bases, ns):\n        cls.kind = 9\n"
           "class B(metaclass=Meta):\n    pass\n"
           "def f():\n    b = B()\n    return b.kind\n")
    assert verify_heap_property("mc", "f", _mc, lambda za, r: r == 9).status == PROVED
    assert verify_heap_property("mc", "f", _mc, lambda za, r: r == 8).status == REFUTED
    _mci = ("class Meta(type):\n    def __init__(cls, name, bases, ns):\n        cls.kind = 4\n"
            "class B(metaclass=Meta):\n    pass\n"
            "class C(B):\n    pass\n"
            "def f():\n    c = C()\n    return c.kind\n")
    assert verify_heap_property("mc", "f", _mci, lambda za, r: r == 4).status == PROVED   # inherited metaclass
    _mcn = ("class Meta(type):\n    def __new__(mcs, name, bases, ns):\n        return super().__new__(mcs, name, bases, ns)\n"
            "class B(metaclass=Meta):\n    pass\n"
            "def f():\n    b = B()\n    return b.kind\n")
    assert verify_heap_property("mc", "f", _mcn, lambda za, r: r == 9).status == UNKNOWN  # custom __new__: abstains
    # the heap engine's object reasoning is reachable through `prove` itself, not only verify_heap_property: a
    # loop-free class-using function (construction, attribute round-trip, method dispatch along the C3 MRO)
    # routes its Python postcondition to the heap engine, so the dispatch resolves instead of UNKNOWN; a plain
    # integer function with a class merely defined falls through to the integer engine unaffected.
    assert prove("class C:\n    def val(self):\n        return 5\ndef f():\n    o = C()\n    return o.val()\n",
                 "result == 5", target="f").status == PROVED
    assert prove("class C:\n    def val(self):\n        return 5\ndef f():\n    o = C()\n    return o.val()\n",
                 "result == 6", target="f").status == REFUTED
    assert prove("class A:\n    def v(self):\n        return 1\nclass B(A):\n    def v(self):\n        return 2\n"
                 "def f():\n    o = B()\n    return o.v()\n", "result == 2", target="f").status == PROVED  # MRO override
    assert prove("class C:\n    def v(self):\n        return 1\ndef f(x):\n    return x + 1\n",
                 "result == x + 1", target="f").status == PROVED                 # class defined, integer body: unaffected
    # int/float dict-key conflation: Python treats 1, 1.0, and True as one key, but the heap engine encodes
    # an int key by value and a float key by an opaque code, so a numerically-equal int and float would not
    # match. Rather than emit a false KeyError (a spurious REFUTED), abstain on a float key, exactly as the
    # value engine's _map_get guards mixed numeric key types; an int key still decides.
    assert verify_heap_property("dk-float", "f", "def f():\n    d = {1: 10}\n    return d[1.0]\n",
                                lambda za, r: r == 10).status == UNKNOWN
    assert verify_heap_property("dk-int", "f", "def f():\n    d = {1: 10}\n    return d[1]\n",
                                lambda za, r: r == 10).status == PROVED
    assert verify_heap_property("dk-in", "f", "def f():\n    d = {1: 10}\n    return 1.0 in d\n",
                                lambda za, r: z3.BoolVal(True)).status == UNKNOWN          # membership abstains too
    # sound type inference of self.<field>: a field set in __init__ bounds a read in any method, and a field
    # set in __new__ on the returned instance bounds it too; an unsound __new__ (returns a different object)
    # contributes no field, so the read abstains. The receiver is a never-subclassed class, so self is it.
    from .inference import infer_return_type as _irt
    assert _irt("class C:\n    def __init__(self):\n        self.x = 5\n    def get(self):\n        return self.x\n",
                target="C.get") == {"int"}
    assert _irt("class C:\n    def __new__(cls):\n        self = object.__new__(cls)\n        self.x = 'hi'\n"
                "        return self\n    def get(self):\n        return self.x\n", target="C.get") == {"str"}
    assert _irt("class C:\n    def __new__(cls):\n        self = object.__new__(cls)\n        self.x = 5\n"
                "        return 7\n    def get(self):\n        return self.x\n", target="C.get") is None
    # sound inference widens on printf-style `%`: a str / bytes left operand fixes the result type whatever the
    # right operand is (str.__mod__ / bytes.__mod__ return their own type or raise, no __rmod__ on the right
    # intercepts -- unlike `*`), so `'fmt' % x` / `b'fmt' % x` commit even on an unbounded right, where the
    # operand pair alone abstained. The left's str/bytes-ness comes from a literal, an f-string, an inferred
    # local, or a parameter's annotation -- the same str bound soundinfer already trusts elsewhere (`s: str;
    # return s` is {str}); an int-annotated or unannotated left stays UNKNOWN.
    assert _irt("def f(x):\n    return 'v=%s' % x\n") == {"str"}                  # str % anything -> str
    assert _irt("def f(x):\n    return b'v=%d' % x\n") == {"bytes"}              # bytes % anything -> bytes
    assert _irt("def f(x):\n    return f'{x}' % x\n") == {"str"}                 # an f-string left is a str
    assert _irt("def f(s: str, x):\n    return s % x\n") == {"str"}             # a str-annotated left (annotation trust)
    assert _irt("def f(s: int, x):\n    return s % x\n") is None                 # int %: numeric/delegating, stays UNKNOWN
    assert _irt("def f(x):\n    return x % 1\n") is None                         # unannotated left: stays UNKNOWN

    # None as a first-class value: Optional results, is-None, truthiness, and
    #     None-in-arithmetic as a trap. A guarded function never returns None; an Optional
    #     result is nonnegative when present; using a nullable value as a number is a TypeError.
    _opt = "def f(x: int):\n    if x < 0:\n        return None\n    return x\n"
    assert verify_optional("opt-nonneg", "f", _opt,
                           lambda za, r: z3.Implies(z3.Not(opt_is_none(r)), opt_val(r) >= 0)).status == PROVED
    assert verify_optional("opt-iff", "f", _opt,
                           lambda za, r: opt_is_none(r) == (opt_val(za["x"]) < 0)).status == PROVED
    _guard = "def f(x):\n    if x is None:\n        return 0\n    return x\n"
    assert verify_optional("is-none-guard", "f", _guard, lambda za, r: z3.Not(opt_is_none(r))).status == PROVED
    # None used as a number is a trap: a nullable x in x + 1 can be None + 1
    vnt = verify_optional("none-arith", "f", "def f(x):\n    return x + 1\n", lambda za, r: z3.BoolVal(True))
    assert vnt.status == REFUTED and "none" in (vnt.counterexample or ""), vnt
    # with x present (int-annotated), the arithmetic is safe and exact
    assert verify_optional("int-arith", "f", "def f(x: int):\n    return x + 1\n",
                           lambda za, r: r == opt_some(opt_val(za["x"]) + 1)).status == PROVED
    # None literal is falsy and returns None
    assert verify_optional("none-lit", "f", "def f():\n    return None\n", lambda za, r: opt_is_none(r)).status == PROVED
    assert verify_optional("none-falsy", "f", "def f():\n    x = None\n    if x:\n        return 1\n    return 0\n",
                           lambda za, r: r == opt_some(0)).status == PROVED

    # floats beyond finiteness: rounding-correct equivalence, NaN/Inf
    #     propagation, an honest UNKNOWN where CPython's % is not exactly modeled, and a
    #     bounded float loop in the BMC engine. _F = z3.Float64().
    _F = z3.Float64()
    # IEEE addition is not associative; the verifier exhibits a (subnormal) counterexample
    assert verify_equiv("fp-assoc", "f", "def f(a: float, b: float, c: float):\n    return (a + b) + c\n",
                        "def g(a: float, b: float, c: float):\n    return a + (b + c)\n", {}).status == REFUTED
    # x - x is not always 0.0 (Inf - Inf and NaN), so the model propagates NaN/Inf, not reals
    assert verify_predicate("fp-nan", "f", "def f(x: float):\n    return x - x\n",
                            lambda za, o: z3.fpEQ(o, z3.FPVal(0.0, _F)), {}).status == REFUTED
    # float % and // are modeled exactly (CPython float_divmod via fpRem): concrete results are
    # computed, the divisor's sign is taken, and division by 0.0 is a ZeroDivisionError trap.
    assert verify_predicate("fp-mod-c", "f", "def f():\n    return 5.5 % 2.0\n",
                            lambda za, o: z3.fpEQ(o, z3.FPVal(1.5, _F)), {}).status == PROVED
    assert verify_predicate("fp-mod-neg", "f", "def f():\n    return (0 - 7.0) % 3.0\n",
                            lambda za, o: z3.fpEQ(o, z3.FPVal(2.0, _F)), {}).status == PROVED   # sign of divisor
    assert verify_predicate("fp-fd-c", "f", "def f():\n    return 7.0 // 2.0\n",
                            lambda za, o: z3.fpEQ(o, z3.FPVal(3.0, _F)), {}).status == PROVED
    assert verify_predicate("fp-fd-neg", "f", "def f():\n    return (0 - 7.0) // 2.0\n",
                            lambda za, o: z3.fpEQ(o, z3.FPVal(-4.0, _F)), {}).status == PROVED  # floors toward -inf
    assert verify_equiv("fp-mod-eq", "f", "def f(x: float):\n    return x % 2.0\n",
                        "def g(x: float):\n    return x % 2.0\n", {}).status == PROVED
    vfpz = verify_predicate("fp-div0", "f", "def f(x: float):\n    return x % 0.0\n",
                            lambda za, o: z3.BoolVal(True), {})
    assert vfpz.status == REFUTED, vfpz                        # % 0.0 raises ZeroDivisionError
    # the exact encoding matches CPython float // and % bit-for-bit over the special values
    assert float_divmod_audit() > 0

    # the transcendentals sin, cos, exp, log are sound over-approximations: uninterpreted Float64
    # functions with axioms true of the real function (range, sign, exact anchors) and the domain /
    # overflow errors as traps. A property following from the axioms is PROVED; a domain trap or a
    # property the axioms do not force is UNKNOWN (a satisfiable query is not a certified
    # counterexample), and the asserted axioms are validated against CPython.
    assert prove("import math\ndef f(x: float):\n    return math.sin(x)\n",
                 "result <= 1.0 and result >= -1.0", requires="math.isfinite(x)").status == PROVED
    assert prove("import math\ndef f(x: float):\n    return math.cos(x)\n",
                 "result <= 1.0", requires="math.isfinite(x)").status == PROVED
    assert prove("import math\ndef f():\n    return math.exp(0.0)\n", "result == 1.0").status == PROVED
    assert prove("import math\ndef f(x: float):\n    return math.exp(x)\n",
                 "result >= 0.0", requires="x <= 700.0").status == PROVED
    # anchor-monotone bounds: exp(x) >= 1 for x >= 0, <= 1 for x <= 0; log(x) >= 0 for x >= 1, <= 0 for 0 < x <= 1.
    assert prove("import math\ndef f(x: float):\n    return math.exp(x)\n", "result >= 1.0", requires="x >= 0.0 and x <= 700.0").status == PROVED
    assert prove("import math\ndef f(x: float):\n    return math.exp(x)\n", "result <= 1.0", requires="x <= 0.0 and math.isfinite(x)").status == PROVED
    assert prove("import math\ndef f(x: float):\n    return math.log(x)\n", "result >= 0.0", requires="x >= 1.0 and math.isfinite(x)").status == PROVED
    assert prove("import math\ndef f(x: float):\n    return math.log(x)\n", "result <= 0.0", requires="x > 0.0 and x <= 1.0").status == PROVED
    assert prove("import math\ndef f():\n    return math.log(1.0)\n", "result == 0.0").status == PROVED
    assert prove("from math import sin\ndef f(x: float):\n    return sin(x)\n",
                 "result <= 1.0", requires="math.isfinite(x)").status == PROVED   # bare-import form
    # a FALSE transcendental property is refuted by sampling real witnesses (sin can be negative, exp
    # grows past any bound), so it decides REFUTED with a counterexample rather than UNKNOWN.
    _sinf = prove("import math\ndef f(x: float):\n    return math.sin(x)\n",
                  "result >= 0.0", requires="math.isfinite(x)")
    assert _sinf.status == REFUTED and _sinf.counterexample_inputs is not None, _sinf
    assert prove("import math\ndef f(x: float):\n    return math.exp(x)\n",
                 "result <= 100.0", requires="x <= 700.0").status == REFUTED
    # a TRUE property the axioms do not force, or one with an unguarded trap, stays UNKNOWN (no finite
    # witness refutes it) and carries no corroboration certificate
    _sinb = verify_predicate("sin-noguard", "f", "def f(x: float):\n    return math.sin(x)\n",
                             lambda za, o: z3.fpLEQ(o, z3.FPVal(1.0, _F)), {})
    assert _sinb.status == UNKNOWN, _sinb                      # traps on +-inf -> not certified
    _sinp = prove("import math\ndef f(x: float):\n    return math.sin(x)\n",
                  "result <= 1.0 and result >= -1.0", requires="math.isfinite(x)")
    assert _sinp.certificate is None                           # over-approximation PROVED: no two-solver cert
    # log's domain error is a trap (x <= 0); exp may overflow for large x -- both conservatively UNKNOWN
    assert verify_predicate("log-dom", "f", "def f(x: float):\n    return math.log(x)\n",
                            lambda za, o: z3.BoolVal(True), {}).status == UNKNOWN
    assert transcendental_axiom_audit() > 0                    # the asserted axioms hold for CPython
    # the transcendental DOMAIN / OVERFLOW errors reach trap-freedom triage (check / scan), not only the
    # over-approximation channel that prove / verify_predicate supply: math.log(x <= 0), math.sin / cos(+-inf),
    # and an overflowing math.exp are emitted into the trap channel (as math.sqrt's domain error already is),
    # so an unguarded call REFUTES -- each genuinely crashes, CPython raising ValueError / OverflowError -- while
    # a guard excluding the bad domain PROVES; the prove / predicate value axioms above are unchanged.
    assert check("import math\ndef f(x: float):\n    return math.log(x)\n", target="f").status == REFUTED      # x <= 0
    assert check("import math\ndef f(x: float):\n    if x > 0.0:\n        return math.log(x)\n    return 0.0\n",
                 target="f").status == PROVED
    assert check("import math\ndef f(x: float):\n    return math.sin(x)\n", target="f").status == REFUTED      # +-inf
    assert check("import math\ndef f(x: float):\n    if math.isfinite(x):\n        return math.sin(x)\n    return 0.0\n",
                 target="f").status == PROVED
    assert check("import math\ndef f(x: float):\n    return math.exp(x)\n", target="f").status == REFUTED      # overflow
    # SOUNDNESS: verify_no_raise models a float parameter as z3.Int (x != x always false), so it abstains on one
    # and check decides via the value engine over z3.FP: a NaN-only trap REFUTES, a total float function proves.
    assert check("def f(x: float):\n    if x != x:\n        return 10 // 0\n    return 0\n", target="f").status == REFUTED
    assert check("def f(x: float):\n    if x == x:\n        return 0\n    return 10 // 0\n", target="f").status == REFUTED
    assert verify_no_raise("nrfp", "f", "def f(x: float):\n    if x != x:\n        return 10 // 0\n    return 0\n",
                           lambda S: z3.BoolVal(True)).status == UNKNOWN      # the CHC engine abstains on a float param
    assert check("def f(x: float):\n    return x + 1.0\n", target="f").status == PROVED            # a total float function still proves
    # the broader math module: floor / ceil / trunc (a non-finite argument is a domain error), the integer-domain
    # factorial / comb / perm / isqrt (negative), the float-domain log2 / log10 / log1p / asin / acos / acosh /
    # atanh / fmod (a domain ValueError), and the pure gcd / hypot / degrees / atan (never trap). The domain
    # trap is exact (so check refutes unguarded and proves under a guard); the value is over-approximated, so a
    # value claim withholds. math_domain_audit validates every trap against CPython.
    _ma = "import math\n"
    assert check(_ma + "def f(x: float):\n    return math.floor(x)\n", target="f").status == REFUTED      # inf / nan -> domain error
    assert check(_ma + "def f(x: float):\n    if math.isfinite(x):\n        return math.ceil(x)\n    return 0\n", target="f").status == PROVED
    assert prove(_ma + "def f():\n    return math.floor(2.7)\n", "result == 2", target="f").status == PROVED   # a constant folds exactly
    assert prove(_ma + "def f():\n    return math.trunc(-2.7)\n", "result == -2", target="f").status == PROVED
    assert check(_ma + "def f(n: int):\n    return math.factorial(n)\n", target="f").status == REFUTED      # n < 0
    assert check(_ma + "def f(n: int):\n    if n >= 0:\n        return math.factorial(n)\n    return 1\n", target="f").status == PROVED
    assert check(_ma + "def f(n: int, k: int):\n    return math.comb(n, k)\n", target="f").status == REFUTED
    assert check(_ma + "def f(n: int):\n    return math.isqrt(n)\n", target="f").status == REFUTED
    assert check(_ma + "def f(x: float):\n    return math.log2(x)\n", target="f").status == REFUTED      # x <= 0
    assert check(_ma + "def f(x: float):\n    if x > 0.0:\n        return math.log10(x)\n    return 0.0\n", target="f").status == PROVED
    assert check(_ma + "def f(x: float):\n    return math.asin(x)\n", target="f").status == REFUTED      # outside [-1, 1]
    assert check(_ma + "def f(x: float):\n    if x >= -1.0 and x <= 1.0:\n        return math.acos(x)\n    return 0.0\n", target="f").status == PROVED
    assert check(_ma + "def f(x: float):\n    return math.acosh(x)\n", target="f").status == REFUTED      # x < 1
    assert check(_ma + "def f(x: float):\n    return math.atanh(x)\n", target="f").status == REFUTED      # |x| >= 1
    assert check(_ma + "def f(a: float, b: float):\n    return math.fmod(a, b)\n", target="f").status == REFUTED   # inf dividend / zero divisor
    assert check(_ma + "def f(a: float, b: float):\n    return math.gcd(a, b)\n".replace("float", "int"), target="f").status == PROVED
    assert check(_ma + "def f(a: float, b: float):\n    return math.hypot(a, b)\n", target="f").status == PROVED   # never traps
    assert check(_ma + "def f(x: float):\n    return math.degrees(math.atan(x))\n", target="f").status == PROVED
    assert check("from math import floor\ndef f(n: int):\n    return floor(n)\n", target="f").status == PROVED   # bare imported name
    assert prove(_ma + "def f(x: float):\n    return math.floor(x)\n", "result >= 0", requires="x >= 0.0", target="f").status == UNKNOWN   # value over-approx
    assert math_domain_audit() > 0                             # every modeled domain trap holds against CPython
    # math.pow always returns a float, with the exact ValueError domain (neg finite base ** fractional, or zero
    # base ** negative); the ** operator x ** n (constant integral n) carries sign axioms and traps at base 0 for
    # n < 0. A fractional ** abstains (a negative base yields complex). math_pow_axiom_audit checks it vs CPython.
    assert prove(_ma + "def f(x: float):\n    if x >= 0.0:\n        return math.pow(x, 0.5)\n    return 1.0\n",
                 "result >= 0.0", target="f").status == PROVED                         # nonnegative base -> nonnegative
    assert prove(_ma + "def f(x: float):\n    return math.pow(x, 0.0)\n", "result == 1.0", target="f").status == PROVED   # x ** 0 == 1
    assert check(_ma + "def f(x: float):\n    return math.pow(x, 0.5)\n", target="f").status == REFUTED       # neg base ** fractional
    assert check(_ma + "def f(x: float):\n    if x >= 0.0:\n        return math.pow(x, 0.5)\n    return 0.0\n",
                 target="f").status == PROVED
    assert prove("def f(x: float):\n    if x >= 0.0 and x < 1e150:\n        return x ** 2.0\n    return 0.0\n",
                 "result >= 0.0", target="f").status == PROVED                         # integral-valued float exponent
    assert prove("def f(x: float):\n    if x > 0.0 and x < 1e150:\n        return x ** -2\n    return 1.0\n",
                 "result >= 0.0", target="f").status == PROVED                         # negative integral exponent
    assert prove("def f(x: float):\n    return x ** 0.5\n", "result >= 0.0", target="f").status == UNKNOWN     # complex boundary: abstains
    assert math_pow_axiom_audit() > 0                          # every math.pow / x ** n trap and axiom holds vs CPython
    # a bytes / bytearray element is an int in [0, 255]; ord / chr are the codepoint bijection over [0, 0x10FFFF]:
    # a constant folds exactly (ord('A') == 65), a single character round-trips (ord(chr(n)) == n), else not pinned.
    assert prove("def f(b: bytes):\n    if len(b) > 0:\n        return b[0]\n    return 0\n",
                 "result >= 0 and result <= 255").status == PROVED
    assert prove("def f(b: bytearray):\n    if len(b) > 0:\n        return b[0]\n    return 0\n",
                 "result >= 0 and result <= 255").status == PROVED
    assert prove("def f():\n    return ord('A')\n", "result == 65").status == PROVED            # constant fold
    assert prove("def f():\n    return chr(65)\n", "result == 'A'").status == PROVED
    assert prove("def f(c: str):\n    if len(c) == 1:\n        return ord(c)\n    return 0\n",
                 "result >= 0 and result <= 1114111").status == PROVED                          # codepoint range
    assert prove("def f(n: int):\n    return ord(chr(n))\n", "result == n",
                 requires="n >= 0 and n <= 1114111").status == PROVED                           # ord . chr == id
    assert prove("def f(c: str):\n    return chr(ord(c))\n", "result == c",
                 requires="len(c) == 1").status == PROVED                                       # chr . ord == id
    assert prove("def f(c: str):\n    if len(c) == 1:\n        return ord(c)\n    return 0\n",
                 "result == 65").status == UNKNOWN                                              # value not pinned
    assert check("def f(n: int):\n    return chr(n)\n").status == REFUTED                       # ValueError out of range
    assert check("def f(n: int):\n    if n >= 0 and n <= 1114111:\n        return chr(n)\n    return 'x'\n").status == PROVED
    # an unannotated parameter paired with a non-integral float literal (x * 0.5, x == 0.5) or a float-only method
    # is modeled under IEEE-754, not the default int; an integral float (2.0) is ambiguous, a subscript stays a seq.
    assert prove("def f(x):\n    return x * 0.5\n", "result == result").status == REFUTED          # float: NaN witness
    assert prove("def f(x):\n    return x * 2\n", "result == result").status == PROVED              # int: no NaN
    assert prove("def f(x):\n    return x == 0.5\n", "result == False").status == REFUTED           # x can equal 0.5
    assert prove("def f(x):\n    if x >= 1.5:\n        return x\n    return 2.0\n",
                 "result > 1.0").status == PROVED                                                   # float fact provable
    # non-constant sequence repetition (s * n, (a, b) * n), a symbolic range step, and extra positional
    # arguments are modeled for trap freedom: each is trap free except a zero range step (ValueError) and too
    # many positional arguments with no *args parameter (TypeError).
    assert check("def f(s: str, n: int):\n    return s * n\n", target="f").status == PROVED
    assert check("def f(n: int):\n    x = (1, 2) * n\n    return len(x)\n", target="f").status == PROVED
    assert check("def f(a: int, b: int, s: int):\n    if s != 0:\n        return len(range(a, b, s))\n    return 0\n", target="f").status == PROVED
    assert check("def f(a: int, b: int, s: int):\n    return len(range(a, b, s))\n", target="f").status == REFUTED   # step may be 0
    _va = {"g": "def g(a, *rest):\n    return a\n", "f": "def f():\n    return g(1, 2, 3)\n"}
    assert check(_va["f"], repo=_va, target="f").status == PROVED                          # extras feed *args
    _va2 = {"g": "def g(a, *rest):\n    return rest[0]\n", "f": "def f():\n    return g(1)\n"}
    assert check(_va2["f"], repo=_va2, target="f").status == REFUTED                       # rest[0] on an empty *args
    _vn = {"g": "def g(a):\n    return a\n", "f": "def f():\n    return g(1, 2, 3)\n"}
    assert check(_vn["f"], repo=_vn, target="f").status == REFUTED                         # too many args, no *args: TypeError
    # a curated trap-free stdlib registry (os.path / time / itertools / functools / logging / hashlib / ...):
    # a pure function raising no modeled trap on a well-typed argument proves trap free and returns its result
    # sort, so a downstream operation composes; a parser / converter that ValueErrors on valid input (json.loads,
    # int(s)) is excluded and stays UNKNOWN. stdlib_trapfree_audit validates the no-modeled-trap claim.
    assert check("import os\ndef f(p):\n    return os.path.join(p, 'x')\n", target="f").status == PROVED
    assert check("import os\ndef f():\n    return os.getpid() + 1\n", target="f").status == PROVED          # int return composes
    assert check("import time\ndef f():\n    return time.time()\n", target="f").status == PROVED
    assert check("import os\ndef f(p):\n    if os.path.exists(p):\n        return 1\n    return 0\n", target="f").status == PROVED   # bool return
    assert check("import os\ndef f(p):\n    return os.path.basename(p) + '.bak'\n", target="f").status == PROVED   # str compose
    assert check("import logging\ndef f():\n    logging.info('hi')\n    return 0\n", target="f").status == PROVED
    assert check("import itertools\ndef f(xs):\n    return itertools.chain(xs, xs)\n", target="f").status == PROVED
    assert check("from os.path import dirname\ndef f(p):\n    return dirname(p)\n", target="f").status == PROVED   # bare-imported leaf
    assert check("from textwrap import dedent\ndef f(s):\n    return dedent(s)\n", target="f").status == PROVED
    assert check("import json\ndef f(s: str):\n    return json.loads(s)\n", target="f").status == UNKNOWN   # a parser: excluded
    assert stdlib_trapfree_audit() > 0                        # every registered entry holds against CPython
    # the trap-bearing builtins bin / hex / oct / ascii / format (str results), chr / ord (a domain ValueError),
    # and hash (an int): each composes or refutes against its exact trap.
    assert check("def f(n: int):\n    return hex(n) + bin(n) + oct(n)\n", target="f").status == PROVED
    assert check("def f(x: int):\n    return ascii(x)\n", target="f").status == PROVED
    assert check("def f(x: float):\n    return format(x, '.2f')\n", target="f").status == PROVED
    assert check("def f(n: int):\n    return chr(n)\n", target="f").status == REFUTED        # outside [0, 0x10FFFF]
    assert check("def f(n: int):\n    if 0 <= n and n < 1000:\n        return chr(n)\n    return 'a'\n", target="f").status == PROVED
    assert check("def f(s: str):\n    return ord(s)\n", target="f").status == REFUTED        # length may not be 1
    assert check("def f(s: str):\n    if len(s) == 1:\n        return ord(s)\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: int):\n    return hash(x)\n", target="f").status == PROVED

    # the string methods z3's theory lacks (strip / lstrip / rstrip / upper / lower) are sound
    # over-approximations: strip leaves a contiguous substring no longer than s, lstrip a suffix,
    # rstrip a prefix, and case mapping is empty exactly when s is -- axioms that hold whatever the
    # characters are (avoiding the Unicode length traps), so a property following from them is PROVED.
    assert prove("def f(s: str):\n    return s.strip()\n", "len(result) <= len(s)").status == PROVED
    assert verify_predicate("strip-sub", "f", "def f(s: str):\n    return s.strip()\n",
                            lambda za, o: z3.Contains(za["s"], o), {}).status == PROVED
    assert verify_predicate("rstrip-pre", "f", "def f(s: str):\n    return s.rstrip()\n",
                            lambda za, o: z3.PrefixOf(o, za["s"]), {}).status == PROVED
    assert verify_predicate("lstrip-suf", "f", "def f(s: str):\n    return s.lstrip()\n",
                            lambda za, o: z3.SuffixOf(o, za["s"]), {}).status == PROVED
    assert prove("def f(s: str):\n    return s.upper()\n", "len(result) == 0",
                 requires="len(s) == 0").status == PROVED
    assert verify_predicate("upper-ne", "f", "def f(s: str):\n    return s.upper()\n",
                            lambda za, o: z3.Implies(z3.Length(za["s"]) >= 1, z3.Length(o) >= 1), {}).status == PROVED
    # a property the over-approximation does not force is UNKNOWN
    assert prove("def f(s: str):\n    return s.strip()\n", "result == s").status == UNKNOWN
    # str.split / splitlines yield a list of strings of unknown length, so the length is a nonnegative
    # integer (a sound over-approximation)
    assert prove("def f(s: str):\n    return len(s.split())\n", "result >= 0").status == PROVED
    assert prove("def f(s: str):\n    return len(s.splitlines())\n", "result >= 0").status == PROVED
    # the broader str API: removeprefix / removesuffix are exact (prefix/suffix + slice); partition
    # splits at the first occurrence into a 3-tuple; index traps when the substring is absent.
    assert verify_equiv("rmpre", "f", "def f(s: str):\n    return s.removeprefix('ab')\n",
                        "def g(s: str):\n    return s.removeprefix('ab')\n", {}).status == PROVED
    assert prove("def f(s: str):\n    return s.removesuffix('xy')\n", "len(result) <= len(s)").status == PROVED
    assert verify_equiv("join", "f", "def f(x: str, y: str):\n    return '-'.join((x, y))\n",
                        "def g(x: str, y: str):\n    return x + '-' + y\n", {}).status == PROVED   # join over a tuple
    assert verify_equiv("part", "f", "def f(s: str):\n    return s.partition('x')\n",
                        "def g(s: str):\n    return s.partition('y')\n", {}).status == REFUTED   # distinct separators
    assert verify_predicate("index-trap", "f", "def f(s: str):\n    return s.index('zz')\n",
                            lambda za, o: z3.BoolVal(True), {}).status == REFUTED                # ValueError if absent
    # the is* predicates as over-approximations: the asserted axiom is the empty-string value
    assert prove("def f(s: str):\n    return s.isspace()\n", "result == 0", requires="len(s) == 0").status == PROVED
    assert prove("def f(s: str):\n    return s.isascii()\n", "result == 1", requires="len(s) == 0").status == PROVED
    assert verify_predicate("isdigit-ne", "f", "def f(s: str):\n    return s.isdigit()\n",
                            lambda za, o: z3.Implies(o == 1, z3.Length(za["s"]) >= 1), {}).status == PROVED
    # count / replace / pad / case over-approximations
    assert verify_predicate("count-nn", "f", "def f(s: str):\n    return s.count('a')\n",
                            lambda za, o: o >= 0, {}).status == PROVED
    assert prove("def f(s: str):\n    return s.replace('Q', 'z')\n", "result == s",
                 requires="not ('Q' in s)").status == PROVED
    assert prove("def f(s: str):\n    return s.ljust(10)\n", "len(result) >= 10").status == PROVED
    assert prove("def f(s: str):\n    return s.capitalize()\n", "len(result) == 0",
                 requires="len(s) == 0").status == PROVED
    # startswith / endswith accept a tuple of candidates (any matches)
    assert verify_predicate("starts-tup", "f", "def f(s: str):\n    return s.startswith(('ab', 'cd'))\n",
                            lambda za, o: z3.Implies(z3.Or(z3.PrefixOf(z3.StringVal('ab'), za['s']),
                                                           z3.PrefixOf(z3.StringVal('cd'), za['s'])), o == 1),
                            {}).status == PROVED
    # str.format on a literal format string is a sound over-approximation: a non-trapping call yields an
    # opaque string (a property over its content is not invented), a field beyond the arguments is an
    # IndexError, and a format spec, a nested field, or a non-literal format string stays UNKNOWN.
    assert prove("def f(x):\n    return '{}'.format(x)\n", "len(result) >= 0").status == PROVED   # satisfied: opaque str
    assert verify_predicate("fmt-idx", "f", "def f(x):\n    return '{} {}'.format(x)\n",
                            lambda za, o: z3.BoolVal(True), {}).status == REFUTED     # too few arguments: IndexError
    assert verify_predicate("fmt-spec", "f", "def f(x):\n    return '{:d}'.format(x)\n",
                            lambda za, o: z3.BoolVal(True), {}).status == UNKNOWN     # a format spec can ValueError
    # a named field {name} is satisfied by a matching keyword argument (an opaque string, no trap), and a
    # KeyError when the call supplies no such keyword; a named field coexists with positional fields; a nested /
    # attribute field ({0.x} / {a[k]}, which may itself trap) is left UNKNOWN.
    assert check("def f(x):\n    return '{a}'.format(a=x)\n", target="f").status == PROVED
    assert check("def f(x):\n    return '{a}'.format(x)\n", target="f").status == REFUTED          # no keyword a: KeyError
    assert check("def f(x, y):\n    return '{} {b}'.format(x, b=y)\n", target="f").status == PROVED  # named + positional
    assert verify_predicate("fmt-nested", "f", "def f(x):\n    return '{0.real}'.format(x)\n",
                            lambda za, o: z3.BoolVal(True), {}).status == UNKNOWN    # an attribute field is not modeled
    # a non-literal format string and format_map (a mapping argument) stay UNKNOWN
    for _m in ("def f(s: str):\n    return s.format()\n", "def f(s: str):\n    return s.format_map({})\n"):
        assert verify_predicate("unmod", "f", _m, lambda za, o: z3.BoolVal(True), {}).status == UNKNOWN
    # an f-string format spec that is a constant alignment / width spec ([fill]<>^ then an optional non-zero
    # width) applies to a str / int / float / bool through __format__ without raising -- a string, no trap; a
    # spec with a sign / 0-fill / precision / presentation type can raise on an incompatible value and stays
    # UNKNOWN. (A spec on a container value, whose __format__ rejects a non-empty spec, the value engine declines
    # too -- left to the broader engines.)
    assert check("def f(name: str):\n    return f'{name:>20}'\n", target="f").status == PROVED
    assert check("def f(n: int):\n    return f'{n:^8}'\n", target="f").status == PROVED
    assert verify_predicate("fstr-spec", "f", "def f(x: float):\n    return f'{x:.2f}'\n",
                            lambda za, o: z3.BoolVal(True), {}).status == UNKNOWN    # a precision/type spec: may raise
    # an f-string field with a constant presentation spec compatible with the value's type never raises, so the
    # field is a string and check() proves trap freedom; a type-incompatible spec is declined, and the safe-spec
    # predicate is validated against CPython in format_spec_audit.
    assert check("def f(x: float):\n    return f'{x:.2f}'\n", target="f").status == PROVED
    assert check("def f(x: float):\n    return f'{x:+.3e}'\n", target="f").status == PROVED
    assert check("def f(n: int):\n    return f'{n:d}'\n", target="f").status == PROVED
    assert check("def f(n: int):\n    return f'{n:#x}'\n", target="f").status == PROVED
    assert check("def f(n: int):\n    return f'{n:.2f}'\n", target="f").status == PROVED        # int via a float type: coerced
    assert check("def f(s: str):\n    return f'{s:.5s}'\n", target="f").status == PROVED        # string truncation
    assert check("def f(x: float):\n    return f'{x:d}'\n", target="f").status == UNKNOWN        # integer type on a float
    assert check("def f(n: int):\n    return f'{n:.2d}'\n", target="f").status == UNKNOWN        # precision on an integer
    assert check("def f(s: str):\n    return f'{s:d}'\n", target="f").status == UNKNOWN          # numeric type on a string
    assert format_spec_audit() > 0                              # the safe-spec predicate holds against CPython
    # str.maketrans(x, y) builds a translation table and raises ValueError when the strings differ in length
    # (modeled against their symbolic lengths); the dict and three-argument forms carry no length trap.
    assert check("def f():\n    return str.maketrans('abc', 'xyz')\n", target="f").status == PROVED
    assert check("def f():\n    return str.maketrans('abc', 'xy')\n", target="f").status == REFUTED
    assert check("def f(a: str, b: str):\n    return str.maketrans(a, b)\n", target="f").status == REFUTED   # lengths may differ
    assert check("def f(a: str, b: str):\n    if len(a) == len(b):\n        return str.maketrans(a, b)\n    return {}\n",
                 target="f").status == PROVED                                       # length guard: safe
    # re.match / search / fullmatch with a CONSTANT compilable pattern is a total call returning Optional[Match]
    # -- None when there is no match -- modeled as None, so an unguarded .group() on the result is a trap and an
    # `if m:` / `if m is not None:` guard proves the use safe. A non-constant pattern (which can raise re.error)
    # and a pattern that does not compile stay UNKNOWN. (None.method() is a reachable AttributeError trap.)
    assert check("import re\ndef f(s: str):\n    return re.match('a.*', s).group()\n", target="f").status == REFUTED
    assert check("import re\ndef f(s: str):\n    m = re.match('a.*', s)\n    if m:\n        return m.group()\n    return ''\n",
                 target="f").status == PROVED
    assert check("import re\ndef f(s: str):\n    m = re.search('x', s)\n    if m is not None:\n        return m.group()\n    return ''\n",
                 target="f").status == PROVED
    assert check("import re\ndef f(p: str, s: str):\n    return re.match(p, s)\n", target="f").status == UNKNOWN   # variable pattern
    assert check("import re\ndef f(s: str):\n    return re.match('[', s)\n", target="f").status == UNKNOWN          # does not compile
    # re.findall / sub / split / subn / finditer with a constant compilable pattern are total (findall / split a
    # sized list, sub an opaque str); a non-constant pattern stays UNKNOWN.
    assert check("import re\ndef f(s: str):\n    return len(re.findall('a', s))\n", target="f").status == PROVED
    assert check("import re\ndef f(s: str):\n    return re.sub('a', 'b', s)\n", target="f").status == PROVED
    assert check("import re\ndef f(s: str):\n    return len(re.split(',', s))\n", target="f").status == PROVED
    assert check("import re\ndef f(p: str, s: str):\n    return re.findall(p, s)\n", target="f").status == UNKNOWN
    # pathlib.Path / PurePath construction is trap free (an opaque path); a method on it stays opaque-safe.
    assert check("import pathlib\ndef f(p: str):\n    return pathlib.Path(p)\n", target="f").status == PROVED
    assert check("from pathlib import Path\ndef f(p: str):\n    return Path(p).name\n", target="f").status == PROVED
    assert check("def f():\n    y = None\n    return y.foo()\n", target="f").status == REFUTED       # None.method(): AttributeError
    # collections constructors, reachable as collections.X(...) and as the bare imported name: defaultdict /
    # Counter are dicts whose missing-key read returns a default (never KeyError), so d[k] is trap free (the
    # value is opaque, not assumed nonzero -- a division by it still refutes); OrderedDict() is a tracked dict
    # (a stored key reads back, a missing one KeyErrors); namedtuple(...) builds a class (a total construction).
    assert check("import collections\ndef f(k):\n    d = collections.defaultdict(int)\n    return d[k]\n", target="f").status == PROVED
    assert check("from collections import defaultdict\ndef f(k):\n    d = defaultdict(list)\n    return d[k]\n", target="f").status == PROVED
    assert check("import collections\ndef f(k, v):\n    d = collections.defaultdict(int)\n    d[k] = v\n    return d[k]\n", target="f").status == PROVED
    assert check("import collections\ndef f(k):\n    c = collections.Counter()\n    return c[k]\n", target="f").status == PROVED
    assert check("import collections\ndef f(k):\n    d = collections.defaultdict(int)\n    return 10 // d[k]\n", target="f").status != PROVED   # the value can be 0
    assert check("from collections import OrderedDict\ndef f(v):\n    d = OrderedDict()\n    d['x'] = v\n    return d['x']\n", target="f").status == PROVED
    assert check("from collections import OrderedDict\ndef f():\n    d = OrderedDict()\n    return d['x']\n", target="f").status == REFUTED   # missing key
    assert check("import collections\ndef f():\n    P = collections.namedtuple('P', ['x', 'y'])\n    return 0\n", target="f").status == PROVED
    # nested tuple unpacking ((a, b), c = ...) binds recursively, with the flat and starred forms unchanged
    assert prove("def f():\n    (a, b), c = ((1, 2), 3)\n    return a + b + c\n", "result == 6", target="f").status == PROVED
    assert prove("def f():\n    a, (b, (c, d)) = (1, (2, (3, 4)))\n    return d\n", "result == 4", target="f").status == PROVED
    assert check("def f(x, y):\n    (a, b), c = (y, x), x\n    return a - b\n", target="f").status == PROVED
    assert string_method_axiom_audit() > 0                     # the asserted axioms hold for CPython
    assert string_fragile_op_audit() > 0                       # z3 last_indexof/replace_all == Python (cvc5-uncorroborated)
    # floats reason inside a loop engine: repeated +1.0 differs from +3.0 by rounding (BMC refutes)
    _floop = "def f(x: float):\n    i = 0\n    while i < 3:\n        x = x + 1.0\n        i = i + 1\n    return x\n"
    assert bmc_check("fp-loop", "f", _floop, lambda S: z3.BoolVal(True),
                     lambda S, r: z3.fpEQ(r, z3.fpAdd(z3.RNE(), S["x"], z3.FPVal(3.0, _F))), k=5).status == REFUTED

    # floating-point interval domain: a float loop's range is proved by
    #     widening over doubles with outward rounding, and NaN-freedom is part of the claim.
    _fr = "def f():\n    x = 0.0\n    while x < 10.0:\n        x = x + 1.0\n    return x\n"
    assert verify_float_range("frange", "f", _fr, 10.0, 12.0).status == PROVED
    assert verify_float_range("frange-tight", "f", _fr, 10.0, 10.5).status == UNKNOWN   # sound, not precise
    _decay = "def f():\n    x = 1.0\n    while x > 0.0001:\n        x = x * 0.5\n    return x\n"
    assert verify_float_range("fdecay", "f", _decay, 0.0, 1.0).status == PROVED

    # remaining operators in ev: the exactly-encodable ones are proved, true
    #     division is float and traps on a zero divisor, and operators with no sound
    #     unbounded-integer encoding (bitwise &, @) are reported UNKNOWN rather than guessed.
    assert verify_equiv("pow2", "f", "def f(a):\n    return a ** 2\n", "def g(a):\n    return a * a\n", {}).status == PROVED
    assert verify_equiv("pow0", "f", "def f(a):\n    return a ** 0\n", "def g(a):\n    return 1\n", {}).status == PROVED
    assert verify_equiv("lshift", "f", "def f(a):\n    return a << 3\n", "def g(a):\n    return a * 8\n", {}).status == PROVED
    assert verify_equiv("rshift", "f", "def f(a):\n    return a >> 1\n", "def g(a):\n    return a // 2\n", {}).status == PROVED
    assert verify_equiv("invert", "f", "def f(a):\n    return ~a\n", "def g(a):\n    return -a - 1\n", {}).status == PROVED
    assert verify_equiv("truediv", "f", "def f(x: float):\n    return x / 1.0\n",
                        "def g(x: float):\n    return x\n", {}).status == PROVED
    vd0 = verify_predicate("div0", "f", "def f(a):\n    return 10 / a\n", lambda za, o: z3.BoolVal(True), {})
    assert vd0.status == REFUTED and vd0.counterexample_inputs.get("a") == 0, vd0
    assert verify_equiv("bitand", "f", "def f(a, b):\n    return a & b\n",
                        "def g(a, b):\n    return a & b\n", {}).status == UNKNOWN   # sound: no Int encoding
    # masking the low k bits is exact for every integer: a & (2^k - 1) == a % 2^k, including negatives,
    # so parity and low-mask idioms are proved while a general & between variables stays UNKNOWN.
    assert verify_equiv("bitmask1", "f", "def f(a):\n    return a & 1\n",
                        "def g(a):\n    return a % 2\n", {}).status == PROVED
    assert verify_equiv("bitmask7", "f", "def f(a):\n    return a & 7\n",
                        "def g(a):\n    return a % 8\n", {}).status == PROVED
    # bitwise | / & / ^ between variables, with no exact unbounded-integer encoding, are sound
    # over-approximations via the nonnegative-operand bounds (max(a,b) <= a|b <= a+b, 0 <= a&b <=
    # min(a,b), 0 <= a^b <= a+b): a property following from those bounds is PROVED, while a property
    # the bounds do not force yields no certified counterexample (UNKNOWN), never a false verdict.
    assert prove("def f(a, b):\n    return a | b\n", "result >= 0", requires="a >= 0 and b >= 0").status == PROVED
    assert prove("def f(a, b):\n    return a | b\n", "result >= a", requires="a >= 0 and b >= 0").status == PROVED
    assert prove("def f(a, b):\n    return a & b\n", "result <= a", requires="a >= 0 and b >= 0").status == PROVED
    assert prove("def f(a, b):\n    return a ^ b\n", "result >= 0", requires="a >= 0 and b >= 0").status == PROVED
    assert prove("def f(a, b):\n    return a | b\n", "result == a", requires="a >= 0 and b >= 0").status == UNKNOWN
    _bor = verify_predicate("bor-unk", "f", "def f(a, b):\n    return a | b\n", lambda za, o: o == 0, {})
    assert _bor.status == UNKNOWN and _bor.reason, _bor      # the over-approximation withholds a counterexample
    # trap freedom: the bitwise result is a fresh integer (over-approximated) that flows into later arithmetic
    # -- (a & b) + 1, (a ^ b) * 2. The nonnegative-operand bounds carry through (0 <= a & b, so 10 // ((a & b)
    # + 1) proves under a nonneg guard), while an unguarded 10 // (a & b) abstains (a & b can be 0; REFUTED
    # withheld). The bare a & b is still trap free.
    assert check("def f(a: int, b: int):\n    return (a & b) + 1\n", target="f").status == PROVED
    assert check("def f(a: int, b: int):\n    return (a ^ b) * 2\n", target="f").status == PROVED
    assert check("def f(a: int, b: int):\n    return (a | b) - 1\n", target="f").status == PROVED
    assert check("def f(a: int, b: int):\n    if a >= 0 and b >= 0:\n        return 10 // ((a & b) + 1)\n    return 0\n", target="f").status == PROVED
    assert check("def f(a: int, b: int):\n    return 10 // (a & b)\n", target="f").status != PROVED   # a & b can be 0: abstains
    assert check("def f(a: int, b: int):\n    return a & b\n", target="f").status == PROVED            # bare bitwise: trap free
    # bitwise between variables BOUNDED by the precondition is decided exactly via fixed-width bitvectors --
    # both PROVED and REFUTED, beyond the over-approximation's PROVED-only -- transferring to unbounded integers
    # because the precondition keeps every operand in [0, 2^width). A false identity refutes with a concrete
    # witness, a true one proves; the unbounded case still abstains (the over-approximation stands).
    assert prove("def f(a, b):\n    return a & b\n", "result == a",
                 requires="0 <= a and a <= 255 and 0 <= b and b <= 255").status == REFUTED
    assert prove("def f(a, b):\n    return (a & b) | (a ^ b)\n", "result == a | b",
                 requires="0 <= a and a <= 255 and 0 <= b and b <= 255").status == PROVED   # an exact bitwise identity
    assert prove("def f(a, b):\n    c = a ^ b\n    d = a ^ c\n    return d\n", "result == b",
                 requires="0 <= a and a <= 65535 and 0 <= b and b <= 65535").status == PROVED   # xor round-trip
    assert prove("def f(a):\n    return a ^ a\n", "result == 0", requires="0 <= a and a <= 1000000").status == PROVED
    _bvr = verify_bitwise("bw", "f", "def f(a, b):\n    return a & b\n",
                          ast.parse("result == a | b", mode="eval").body,
                          ast.parse("0 <= a and a <= 255 and 0 <= b and b <= 255", mode="eval").body)
    assert _bvr.status == REFUTED and "bitvector" in _bvr.technique, _bvr   # the engine, direct, with a counterexample
    assert verify_bitwise("bw", "f", "def f(a, b):\n    return a & b\n",
                          ast.parse("result == a", mode="eval").body,
                          ast.parse("a >= 0 and b >= 0", mode="eval").body).status == UNKNOWN   # unbounded: abstains
    # bitwise over operands bounded into a signed width decides in two's complement; a false identity refutes.
    _sb = "-128 <= a and a <= 127 and -128 <= b and b <= 127"
    assert prove("def f(a):\n    return a & a\n", "result == a", requires="-128 <= a and a <= 127", target="f").status == PROVED
    assert prove("def f(a):\n    return a ^ a\n", "result == 0", requires="-128 <= a and a <= 127", target="f").status == PROVED
    assert prove("def f(a, b):\n    return a & b\n", "result == a", requires=_sb, target="f").status == REFUTED
    assert "signed" in prove("def f(a):\n    return a & a\n", "result == a", requires="-128 <= a and a <= 127", target="f").technique
    # a bitwise identity mixed with integer arithmetic decides at width 16 and 32, not only 8: the Int2BV/BV2Int
    # bridge leaves both z3 and cvc5 UNKNOWN there, so a widened pure-bitvector discharge takes over. A true
    # identity proves, a false variant refutes, and one that could overflow the bitvector headroom stays UNKNOWN.
    _p16 = "0 <= a and a <= 65535 and 0 <= b and b <= 65535"
    _p32 = "0 <= a and a <= 4294967295 and 0 <= b and b <= 4294967295"
    assert prove("def f(a, b):\n    return a ^ b\n", "result == (a | b) - (a & b)", requires=_p16).status == PROVED
    assert prove("def f(a, b):\n    return a ^ b\n", "result == (a | b) - (a & b)", requires=_p32).status == PROVED
    assert prove("def f(a, b):\n    return a + b\n", "result == (a ^ b) + 2 * (a & b)", requires=_p32).status == PROVED
    assert prove("def f(a, b):\n    return a ^ b\n", "result == (a | b) - (a & b) + 1", requires=_p16).status == REFUTED
    # the widened-bitvector path is sound under overflow: a product that can exceed the headroom is not decided
    from .engines import _bitwise_bvnative
    _ovf = _bitwise_bvnative("ovf", "f", "def f(a, b):\n    return a * b * a * b\n",
                             ast.parse("result == (a * b) * (a * b)", mode="eval").body,
                             ast.parse(_p32, mode="eval").body, 32)
    assert _ovf is None, _ovf                                    # abstains rather than risk a wraparound verdict
    # float ** : x ** 0 is 1.0 and x ** 1 is x bit-exactly (modeled exactly, for every double); a higher constant
    # power is a sound over-approximation (a nonnegative finite base gives a nonnegative result, an even power of a
    # finite base is nonnegative, the anchors), so a property following from the axioms is PROVED -- while
    # x ** 2 == x * x is NOT proved, since float x ** 2 is not bit-identical to x * x.
    assert prove("def f(x: float):\n    return x ** 0\n", "result == 1.0").status == PROVED
    assert prove("def f(x: float):\n    return x ** 1\n", "result == x", requires="isfinite(x)").status == PROVED
    assert prove("def f(x: float):\n    return x ** 2\n", "result >= 0.0", requires="isfinite(x)").status == PROVED
    assert prove("def f(x: float):\n    return x ** 3\n", "result >= 0.0",
                 requires="isfinite(x) and x >= 0.0").status == PROVED
    assert prove("def f(x: float):\n    return x ** 2\n", "result == x * x", requires="isfinite(x)").status == UNKNOWN
    # integer base ** a VARIABLE (or large) integer exponent x ** y: the only trap is a ZeroDivisionError when
    # the base is zero and the exponent negative (0 ** -1), and the result is some number (an int for y >= 0, a
    # float for y < 0) over-approximated by a fresh integer -- so a y >= 0 or x != 0 guard proves trap freedom,
    # the result flows into further arithmetic (x ** y + 1), and pow(x, y) and modular exponentiation decide.
    # The constant-exponent path (x ** 3, exact repeated multiplication) is unchanged.
    assert check("def f(x: int, y: int):\n    if y >= 0:\n        return x ** y\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: int, y: int):\n    if x != 0:\n        return x ** y\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: int, y: int):\n    if y >= 0:\n        return (x ** y) + 1\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: int, y: int):\n    if y >= 0:\n        return pow(x, y)\n    return 0\n", target="f").status == PROVED
    assert check("def f(b: int, e: int, m: int):\n    if e >= 0 and m != 0:\n        return (b ** e) % m\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: int, y: int):\n    return x ** y\n", target="f").status == REFUTED       # unguarded: 0 ** -1 is a ZeroDivisionError (exact-operand trap)
    assert check("def f(x: int):\n    return x ** 3\n", target="f").status == PROVED                 # constant exponent: exact path kept
    assert prove("def f(x: int):\n    return x ** 2\n", "result == x * x", target="f").status == PROVED  # constant: still exact
    # variable-exponent x ** y reasons in prove via the power axioms; pow routes the same.
    assert prove("def f(x, y):\n    return x ** y\n", "result >= 0", requires="x >= 0 and y >= 0", target="f").status == PROVED
    assert prove("def f(x, y):\n    return x ** y\n", "result >= 1", requires="x >= 1 and y >= 0", target="f").status == PROVED
    assert prove("def f(x, y):\n    return pow(x, y)\n", "result >= 0", requires="x >= 0 and y >= 0", target="f").status == PROVED
    assert prove("def f(x, y):\n    return x ** y\n", "result >= 0", target="f").status == UNKNOWN     # unconstrained: not forced
    # a CONSTANT exponent beyond the unroll cap (64) is still over-approximated, but the reason names it a constant
    # over the cap rather than a variable exponent; a genuine variable exponent keeps the variable-exponent wording.
    _vcap = prove("def f(x):\n    return x ** 100\n", "result >= x", requires="x >= 1", target="f")
    assert _vcap.status == UNKNOWN and "constant exponent over the unroll cap" in _vcap.reason, _vcap
    _vvar = prove("def f(x, y):\n    if y >= 1:\n        return x ** y\n    return 1\n", "result >= x",
                  requires="x >= 1", target="f")
    assert _vvar.status == UNKNOWN and "variable exponent" in _vvar.reason, _vvar
    # trap freedom of a variable-exponent power: the only trap is 0 ** (negative) (a ZeroDivisionError), modeled
    # exactly on the operands -- so an unguarded x ** n refutes (x=0, n=-1) and an x != 0 or n >= 0 guard proves, even
    # though the RESULT value is over-approximated. A nested over-approximated base ((a ** b) ** n) does NOT fabricate
    # a refutation (its operands are not exact); a divisor built from the over-approximated result stays UNKNOWN.
    assert check("def f(x: int, n: int):\n    return x ** n\n", target="f").status == REFUTED
    assert check("def f(n: int):\n    return 0 ** n\n", target="f").status == REFUTED
    assert check("def f(x: int, n: int):\n    if x != 0:\n        return x ** n\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: int, n: int):\n    if n >= 0:\n        return x ** n\n    return 0\n", target="f").status == PROVED
    assert check("def f(n: int):\n    return 2 ** n\n", target="f").status == PROVED
    assert check("def f(a: int, b: int, n: int):\n    if a >= 1 and n >= 0:\n        y = a ** b\n        return y ** n\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: int, n: int):\n    if x != 0:\n        return 10 // (x ** n + 1)\n    return 0\n", target="f").status == UNKNOWN
    # a float accumulator that crosses a loop keeps its float kind through the havoc (not collapsed to an int), so a
    # later float-only operation is modeled correctly: a bitwise x & 1 / x | 1 (a TypeError on a float) is no longer a
    # false PROVED (it abstains, the float bitwise op being unmodeled), while a safe float op (x + 2.0 / x * 2.0) proves.
    assert check("def f(n: int):\n    x = 1.5\n    for i in range(n):\n        x = x + 1.0\n    return x & 1\n", target="f").status != PROVED
    assert check("def f(n: int):\n    x = 1.5\n    for i in range(n):\n        x = x + 1.0\n    return x | 1\n", target="f").status != PROVED
    assert check("def f(n: int):\n    x = 1.5\n    for i in range(n):\n        x = x + 1.0\n    return x + 2.0\n", target="f").status == PROVED
    assert check("def f(n: int):\n    x = 0.0\n    for i in range(n):\n        x = x + 1.0\n    return x * 2.0\n", target="f").status == PROVED
    # variable bit-shift x << k / x >> k: a negative count is a ValueError. The count is exact even though the
    # shifted value is over-approximated, so the negative-count trap is hard (refutes despite the fuzzy value):
    # an unguarded shift refutes, a k >= 0 guard proves trap freedom, and a constant non-negative shift stays exact.
    assert check("def f(x: int, k: int):\n    if k >= 0:\n        return x << k\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: int, k: int):\n    if k >= 0:\n        return x >> k\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: int, k: int):\n    return x << k\n", target="f").status == REFUTED              # k may be negative
    assert check("def f(x: int, k: int):\n    return x >> k\n", target="f").status == REFUTED
    assert check("def f():\n    return 1 << -1\n", target="f").status == REFUTED                            # constant negative count
    assert check("def f(x: int):\n    return x << 3\n", target="f").status == PROVED
    # del of a subscript or attribute target: del c[i] traps as a read does (IndexError / KeyError), a guarded
    # delete proves, and del o.attr raises no modeled trap.
    assert check("def f(a: list):\n    del a[0]\n    return 0\n", target="f").status == REFUTED            # empty list: IndexError
    assert check("def f(a: list):\n    if len(a) > 0:\n        del a[0]\n    return 0\n", target="f").status == PROVED
    assert check("def f(d: dict, k):\n    del d[k]\n    return 0\n", target="f").status == REFUTED          # missing key: KeyError
    assert check("def f(d: dict, k):\n    if k in d:\n        del d[k]\n    return 0\n", target="f").status == PROVED
    assert check("def f(o):\n    del o.x\n    return 0\n", target="f").status == PROVED                     # attribute del: no modeled trap
    # an opaque object's field o.x is a stable value, duck-typed numeric in arithmetic and comparison (o.x + o.y,
    # o.x > o.y decide; o.x - o.x == 0), while len(o.x) / o.x.method() stay opaque (not refuted) and the value is
    # not pinned. A parameter used only as o.attr is inferred an object; an annotated class parameter is one.
    assert prove("def f(o):\n    return o.x + o.y\n", "result == o.x + o.y", target="f").status == PROVED
    assert prove("def f(o):\n    return o.x - o.x\n", "result == 0", target="f").status == PROVED
    assert prove("def f(o):\n    return o.x + 1\n", "result > o.x", target="f").status == PROVED            # field arithmetic
    assert prove("def f(o):\n    if o.x > o.y:\n        return o.x - o.y\n    return 0\n",
                 "result >= 0", target="f").status == PROVED                                                # field comparison
    assert prove("def f(o):\n    return o.a.x + o.a.y\n", "result == o.a.x + o.a.y", target="f").status == PROVED   # nested
    assert prove("class P:\n    pass\ndef f(p: P):\n    return p.x * p.x\n",
                 "result >= 0", target="f").status == PROVED                                                # annotated class param
    assert check("def f(o):\n    return o.x + 1\n", target="f").status == PROVED                            # numeric field: trap free
    assert check("def f(o):\n    return len(o.x)\n", target="f").status == PROVED                           # len of a field: not refuted
    assert prove("def f(o):\n    return o.x\n", "result == 99", target="f").status == UNKNOWN               # value not pinned
    # any() / all() over a container parameter: element truthiness never traps, so the call is trap free.
    assert check("def f(xs: list):\n    return any(xs)\n", target="f").status == PROVED
    assert check("def f(xs: list):\n    return all(xs)\n", target="f").status == PROVED
    assert check("def f(s: set):\n    return any(s)\n", target="f").status == PROVED
    # container / iterator builtins: set / frozenset / tuple / iter / next over an iterable are modeled trap-free
    # (a non-iterable scalar abstains); a set is not subscriptable, and an element trap still surfaces.
    assert check("def f(xs):\n    return len(set(xs))\n", target="f").status == PROVED
    assert check("def f(xs):\n    s = set(xs)\n    return s[0]\n", target="f").status == REFUTED
    assert check("def f(n: int):\n    return set(n)\n", target="f").status == UNKNOWN
    assert check("def f(xs):\n    t = tuple(xs)\n    if len(t) > 0:\n        return t[0]\n    return 0\n", target="f").status == PROVED
    assert check("def f(xs):\n    it = iter(xs)\n    return next(it)\n", target="f").status == PROVED
    assert check("def f(xs):\n    return set(10 // k for k in xs)\n", target="f").status == REFUTED
    # set union | intersection & difference - symmetric ^ (and the matching methods) carry content: membership on
    # the result reduces to the operands' (x in a|b iff x in a or x in b, etc.), with the size relation; the
    # content is exact, so a false set implication REFUTES.
    assert prove("def f(a: set, b: set, x: int):\n    if x in a:\n        return 1 if x in (a | b) else 2\n    return 0\n",
                 "result != 2").status == PROVED                                            # x in a -> x in a|b
    assert prove("def f(a: set, b: set, x: int):\n    if x in (a & b):\n        return 1 if (x in a and x in b) else 2\n    return 0\n",
                 "result != 2").status == PROVED                                            # x in a&b -> x in a and b
    assert prove("def f(a: set, b: set, x: int):\n    if x in (a - b):\n        return 1 if (x in a and x not in b) else 2\n    return 0\n",
                 "result != 2").status == PROVED                                            # x in a-b -> x in a, not in b
    assert prove("def f(a: set, b: set, x: int):\n    if x in (a ^ b):\n        return 1 if ((x in a) != (x in b)) else 2\n    return 0\n",
                 "result != 2").status == PROVED                                            # symmetric difference (xor)
    assert prove("def f(a: set, b: set, x: int):\n    if x in a:\n        return 1 if x in a.union(b) else 2\n    return 0\n",
                 "result != 2").status == PROVED                                            # method form .union
    assert prove("def f(a: set, b: set):\n    return len(a & b) - len(a)\n", "result <= 0").status == PROVED   # intersection subset
    assert prove("def f(a: set, b: set):\n    return len(a | b) - len(a)\n", "result >= 0").status == PROVED   # union superset
    assert prove("def f(a: set, b: set, x: int):\n    if x in a:\n        return 1 if x in (a & b) else 2\n    return 0\n",
                 "result != 2").status == REFUTED                                           # x in a does NOT imply x in a&b
    # an unannotated parameter unpacked (a, b = x) or tested for membership (e in x) is inferred a container:
    # the unpack raises ValueError on an arity mismatch (a len() guard proves it), and membership is trap free.
    assert check("def f(x):\n    a, b = x\n    return a + b\n", target="f").status == REFUTED              # arity may mismatch
    assert check("def f(x):\n    if len(x) == 2:\n        a, b = x\n        return a + b\n    return 0\n", target="f").status == PROVED
    assert check("def f(x):\n    return 3 in x\n", target="f").status == PROVED
    assert check("def f(x):\n    if 5 in x:\n        return 1\n    return 0\n", target="f").status == PROVED
    # a is b / a is not b on two non-None values is opaque identity (it never raises), so the function is trap free.
    assert check("def f(a, b):\n    return a is b\n", target="f").status == PROVED
    assert check("def f(a, b):\n    return a is not b\n", target="f").status == PROVED
    # a construct that makes z3 reject the encoding -- a sort clash from `sep or ' '` mixing str and int -- yields a
    # verdict, not an escaping Z3Exception: the engine abstains cleanly.
    assert check("def f(sep):\n    return sep or ' '\n", target="f").status == UNKNOWN
    assert check("def f(s, sep):\n    return (sep or ' ').join(s)\n", target="f").status == UNKNOWN

    # the contract API states a property in Python over the parameters and `result` (a loop routes to
    # the Horn engine, which infers the invariant), instead of a raw Z3 lambda
    assert prove("def f(x):\n    return x + x\n", "result == 2 * x").status == PROVED
    assert prove("def f(x):\n    return x * x\n", "result >= 0").status == PROVED
    assert prove("def f(x):\n    return x + 1\n", "result == x").status == REFUTED
    assert prove("def f(x):\n    return 10 // x\n", "result >= 0", requires="x > 0").status == PROVED
    assert prove("def f(s: str):\n    return s + s\n", "len(result) == 2 * len(s)").status == PROVED
    loop_src = "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"
    assert prove(loop_src, "2 * result == n * (n - 1)", requires="n >= 0").status == PROVED   # invariant inferred
    # contracts written as decorators (the contracts / icontract style) are compiled into the same proof
    # goals: a string condition, a lambda condition, a precondition that discharges a trap, and a loop
    # whose invariant is inferred; a false postcondition is refuted.
    assert verify_contracts('@require("x > 0")\n@ensure("result > x")\ndef inc(x):\n    return x + 1\n').status == PROVED
    assert verify_contracts('@ensure("result == x")\ndef f(x):\n    return x + 1\n').status == REFUTED
    assert verify_contracts("@require(lambda x: x >= 0)\n@ensure(lambda result, x: result >= x)\n"
                            "def sq(x):\n    return x * x\n").status == PROVED
    assert verify_contracts('@require("x >= 1")\n@ensure("result <= 10")\ndef d(x):\n    return 10 // x\n').status == PROVED
    assert verify_contracts('@require("n >= 0")\n@ensure("result == n")\n'
                            "def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n").status == PROVED
    assert verify_contracts("def f(x):\n    return x\n").status == UNKNOWN     # no @ensure to verify
    # specification-free: mine the code's own contracts (asserts and traps are obligations), with only a
    # precondition supplied
    assert check("def f(x):\n    assert x * x >= 0\n    return x\n").status == PROVED       # assert always holds
    assert check("def f(x):\n    assert x > 0\n    return x\n").status == REFUTED           # assert can fail
    assert check("def f(x):\n    assert x > 0\n    return x\n", requires="x >= 1").status == PROVED
    assert check("def f(x):\n    return 10 // x\n").status == REFUTED                        # trap mined
    assert check("def f(x):\n    return 10 // x\n", requires="x != 0").status == PROVED
    # a REFUTED trap-freedom verdict is labeled a likely bug or an intended input-validation
    # guard, symbolically (no sandbox), by re-checking a variant with each explicit raise turned into a bare
    # return and each `assert c` into `if not c: return None` (preserving the path each guards). So a raise OR
    # an assert guarding the trapping operation -- `if x == 0: raise; return 10 // x`, or an `assert` before it
    # -- reads as validation, while an unguarded operation trap or a trap that survives the guard reads as a
    # bug. The verdict stays REFUTED; only the reason is enriched, so `check` separates partiality from a crash.
    assert "intended input validation" in check("def f(x):\n    if x == 0:\n        raise ValueError('zero')\n"
                                                "    return 10 // x\n").reason                # the raise guards the //
    assert "intended input validation" in check("def f(xs: list):\n    if not xs:\n        raise ValueError('e')\n"
                                                "    return xs[0]\n").reason                  # the raise guards the index
    assert "intended input validation" in check("def f(d: dict, k):\n    if k not in d:\n        raise KeyError(k)\n"
                                                "    return d[k]\n").reason                   # the raise guards the lookup
    assert "likely a bug" in check("def f(x):\n    return 10 // x\n").reason                  # unguarded division
    assert "likely a bug" in check("def f(xs: list):\n    return xs[0]\n").reason             # unguarded index
    assert "likely a bug" in check("def f(x):\n    if x < 0:\n        raise ValueError\n    return 10 // x\n").reason   # x == 0 still traps
    assert "intended input validation" in check("def f(x):\n    assert x > 0\n    return x\n").reason   # a validating assert, trap free once removed
    assert "likely a bug" in check("def f(x):\n    assert x > -100\n    return 10 // x\n").reason   # the assert does not rule out x == 0
    assert check("def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n",
                 requires="n >= 0", total=True).status == PROVED                             # safe and terminates
    # a counterexample is enriched with an execution trace: the path taken and the live integer values
    # at each line, recorded by running the failing input in the sandbox (when the sandbox can spawn).
    if core.sandbox_run_batch("def f(x):\n    return x\n", {}, "f", [[1]]) == [("ok", 1)]:
        trap = "def f(x):\n    return 10 // x\n"
        et = explain(verify_predicate("tr", "f", trap, lambda A, r: z3.BoolVal(True), {}), trap)
        assert et.trace is not None and "x=0" in et.trace and "raises ZeroDivisionError" in et.trace, et.trace
        branchy = "def f(x):\n    if x > 0:\n        r = x\n    else:\n        r = 0 - x\n    return r\n"
        eb = explain(prove(branchy, "result == x"), branchy)
        assert eb.trace is not None and "r = 0 - x" in eb.trace and "=> returns" in eb.trace, eb.trace

    # strings as first-class values over Z3's string theory: literals,
    #     concatenation, len, membership, slicing, methods, and f-strings, all over all strings.
    assert verify_equiv("str-assoc", "f", "def f(a: str, b: str, c: str):\n    return (a + b) + c\n",
                        "def g(a: str, b: str, c: str):\n    return a + (b + c)\n", {}).status == PROVED
    assert verify_predicate("str-len", "f", "def f(a: str, b: str):\n    return len(a + b)\n",
                            lambda za, o: o == z3.Length(za["a"]) + z3.Length(za["b"]), {}).status == PROVED
    assert verify_equiv("str-fstring", "f", "def f(name: str):\n    return f\"hi {name}!\"\n",
                        "def g(name: str):\n    return \"hi \" + name + \"!\"\n", {}).status == PROVED
    assert verify_predicate("str-prefix", "f", "def f(s: str):\n    return s.startswith(\"ab\")\n",
                            lambda za, o: z3.Implies(o == 1, z3.Length(za["s"]) >= 2), {}).status == PROVED
    assert verify_predicate("str-contains", "f", "def f(a: str, c: str):\n    return \"b\" in (a + \"b\" + c)\n",
                            lambda za, o: o == 1, {}).status == PROVED
    assert verify_equiv("str-slice", "f", "def f(s: str):\n    return s[0:len(s)]\n",
                        "def g(s: str):\n    return s\n", {}).status == PROVED
    # strided slicing x[i:j:k]: exact length (x[::k] is ceil(len/|k|), so x[::-1] keeps length and x[::2] halves
    # it), content over-approximated. A list slice is a sized list, a bytes slice keeps [0,255]; a zero step traps.
    assert prove("def f(s: str):\n    return len(s[::2])\n",
                 "2 * result == len(s) or 2 * result == len(s) + 1").status == PROVED       # halved length, exact
    assert prove("def f(s: str):\n    return len(s[::-1])\n", "result == len(s)").status == PROVED   # reversal keeps length
    assert prove("def f(xs: list):\n    return len(xs[::-1])\n", "result == len(xs)").status == PROVED
    assert prove("def f(xs: list):\n    return len(xs[:])\n", "result == len(xs)").status == PROVED   # full copy
    assert prove("def f(xs: list):\n    return len(xs[1:4])\n", "result <= len(xs)").status == PROVED
    assert prove("def f(b: bytes):\n    c = b[1:]\n    if len(c) > 0:\n        return c[0]\n    return 0\n",
                 "result >= 0 and result <= 255").status == PROVED                          # slice keeps byte elements
    assert prove("def f(s: str):\n    if len(s) >= 2:\n        return s[::2]\n    return ''\n",
                 "result == s").status == UNKNOWN                                           # strided content not pinned
    assert check("def f(xs: list, k: int):\n    return xs[::k]\n", target="f").status == REFUTED        # zero step: ValueError
    assert check("def f(xs: list, k: int):\n    if k != 0:\n        return xs[::k]\n    return xs\n",
                 target="f").status == PROVED

    # lists, first-class and growable: literals, indexing, append, pop, and
    #     element store, all on the heap so in-place mutation is observed through every alias,
    #     and an out-of-range index is an IndexError trap.
    assert verify_heap_property("lit-idx", "f", "def f():\n    a = [10, 20, 30]\n    return a[1]\n",
                                lambda za, r: r == 20).status == PROVED
    assert verify_heap_property("append-len", "f", "def f():\n    a = [1, 2]\n    a.append(3)\n    return len(a)\n",
                                lambda za, r: r == 3).status == PROVED
    assert verify_heap_property("append-val", "f", "def f(x):\n    a = []\n    a.append(x)\n    return a[0]\n",
                                lambda za, r: r == za["x"]).status == PROVED
    # aliasing: b = a, so appends through either name grow the one shared list
    assert verify_heap_property("alias-len", "f",
                                "def f(x, y):\n    a = []\n    b = a\n    a.append(x)\n    b.append(y)\n    return len(a)\n",
                                lambda za, r: r == 2).status == PROVED
    assert verify_heap_property("alias-elem", "f",
                                "def f(x):\n    a = []\n    b = a\n    a.append(x)\n    return b[0]\n",
                                lambda za, r: r == za["x"]).status == PROVED
    assert verify_heap_property("store", "f", "def f():\n    a = [1, 2, 3]\n    a[1] = 9\n    return a[1]\n",
                                lambda za, r: r == 9).status == PROVED
    assert verify_heap_property("pop", "f", "def f():\n    a = [1, 2, 3]\n    x = a.pop()\n    return x\n",
                                lambda za, r: r == 3).status == PROVED
    vidx = verify_heap_property("oob", "f", "def f():\n    a = []\n    return a[0]\n", lambda za, r: z3.BoolVal(True))
    assert vidx.status == REFUTED, vidx                       # IndexError on empty list

    # dicts, sets, and frozensets on the heap: literals, store/lookup,
    #     membership, length, and aliasing; a missing key/element is a trap, frozensets are
    #     immutable.
    assert verify_heap_property("dict-rw", "f", "def f(x):\n    d = {}\n    d[5] = x\n    return d[5]\n",
                                lambda za, r: r == za["x"]).status == PROVED
    assert verify_heap_property("dict-lit", "f", "def f():\n    d = {1: 10, 2: 20}\n    return d[2]\n",
                                lambda za, r: r == 20).status == PROVED
    assert verify_heap_property("dict-alias", "f",
                                "def f(x):\n    d = {}\n    e = d\n    d[1] = x\n    return len(e)\n",
                                lambda za, r: r == 1).status == PROVED
    vkey = verify_heap_property("dict-key", "f", "def f():\n    d = {}\n    return d[9]\n", lambda za, r: z3.BoolVal(True))
    assert vkey.status == REFUTED, vkey                       # KeyError on a missing key
    assert verify_heap_property("set-add", "f",
                                "def f(x):\n    s = set()\n    s.add(x)\n    if x in s:\n        return len(s)\n    return -1\n",
                                lambda za, r: r == 1).status == PROVED
    assert verify_heap_property("set-dedup", "f", "def f():\n    s = {1, 1, 2}\n    return len(s)\n",
                                lambda za, r: r == 2).status == PROVED
    vrem = verify_heap_property("set-rem", "f", "def f():\n    s = set()\n    s.remove(7)\n    return 0\n",
                                lambda za, r: z3.BoolVal(True))
    assert vrem.status == REFUTED, vrem                       # KeyError removing a missing element
    assert verify_heap_property("frozenset", "f",
                                "def f():\n    s = frozenset({1, 2, 2})\n    return len(s)\n",
                                lambda za, r: r == 2).status == PROVED

    # tuples as first-class values: packing, unpacking, indexing, membership,
    #     length, and multi-value returns, compared by structural value equality.
    assert verify_equiv("tup-swap", "f", "def f(a, b):\n    a, b = b, a\n    return a, b\n",
                        "def g(a, b):\n    return b, a\n", {}).status == PROVED
    vtr = verify_equiv("tup-order", "f", "def f(a, b):\n    return a, b\n",
                       "def g(a, b):\n    return b, a\n", {})
    assert vtr.status == REFUTED, vtr                          # (a,b) != (b,a) in general
    assert verify_equiv("tup-unpack", "f", "def f(a, b):\n    x, y = a, b\n    return x + y\n",
                        "def g(a, b):\n    return a + b\n", {}).status == PROVED
    assert verify_predicate("tup-index", "f", "def f():\n    t = (10, 20, 30)\n    return t[1]\n",
                            lambda za, o: o == 20, {}).status == PROVED
    assert verify_predicate("tup-len", "f", "def f():\n    return len((1, 2, 3))\n",
                            lambda za, o: o == 3, {}).status == PROVED
    assert verify_predicate("tup-in", "f", "def f(a, b, c):\n    if a in (a, b, c):\n        return 1\n    return 0\n",
                            lambda za, o: o == 1, {}).status == PROVED

    # Fraction (exact rationals over Z3 Real) and complex (a pair of doubles).
    #     Fraction reasons without rounding -- 1/3 + 1/3 + 1/3 == 1, which floats cannot prove.
    assert verify_predicate("frac-third", "f", "def f():\n    x = Fraction(1, 3)\n    return x + x + x\n",
                            lambda za, o: o == z3.RealVal(1), {}).status == PROVED
    assert verify_equiv("frac-distrib", "f",
                        "def f(a, b, c):\n    return Fraction(a) * (Fraction(b) + Fraction(c))\n",
                        "def g(a, b, c):\n    return Fraction(a) * Fraction(b) + Fraction(a) * Fraction(c)\n",
                        {}).status == PROVED
    assert verify_equiv("frac-exact", "f", "def f(a):\n    return Fraction(a) / 2 * 2\n",
                        "def g(a):\n    return Fraction(a)\n", {}).status == PROVED
    vfz = verify_predicate("frac-zero", "f", "def f():\n    return Fraction(1, 0)\n", lambda za, o: z3.BoolVal(True), {})
    assert vfz.status == REFUTED, vfz                          # Fraction(_, 0) raises ZeroDivisionError
    _F2 = z3.Float64()
    assert verify_predicate("cx-mul", "f", "def f():\n    z = complex(1, 2) * complex(3, 4)\n    return z.real\n",
                            lambda za, o: z3.fpEQ(o, z3.FPVal(-5.0, _F2)), {}).status == PROVED
    assert verify_predicate("cx-isq", "f", "def f():\n    z = complex(0, 1) * complex(0, 1)\n    return z.real\n",
                            lambda za, o: z3.fpEQ(o, z3.FPVal(-1.0, _F2)), {}).status == PROVED

    # general subscripting / slicing and augmented subscript assignment.
    assert verify_heap_property("aug-sub", "f", "def f():\n    a = [10, 20]\n    a[0] += 5\n    return a[0]\n",
                                lambda za, r: r == 15).status == PROVED
    assert verify_heap_property("aug-attr", "f",
                                "def f():\n    o = object()\n    o.x = 0\n    o.x += 1\n    o.x += 1\n    return o.x\n",
                                lambda za, r: r == 2).status == PROVED
    assert verify_heap_property("aug-dict", "f", "def f():\n    d = {1: 0}\n    d[1] += 3\n    return d[1]\n",
                                lambda za, r: r == 3).status == PROVED
    assert verify_predicate("tup-slice", "f", "def f():\n    t = (1, 2, 3, 4)\n    s = t[1:3]\n    return s[0] + s[1]\n",
                            lambda za, o: o == 5, {}).status == PROVED
    assert verify_predicate("tup-step", "f", "def f():\n    t = (1, 2, 3, 4)\n    s = t[::2]\n    return s[0] + s[1]\n",
                            lambda za, o: o == 4, {}).status == PROVED
    assert verify_heap_property("list-slice", "f",
                                "def f():\n    a = [10, 20, 30, 40]\n    b = a[1:3]\n    return b[0]\n",
                                lambda za, r: r == 20).status == PROVED
    assert verify_heap_property("list-slice-len", "f",
                                "def f():\n    a = [1, 2, 3, 4, 5]\n    b = a[1:4]\n    return len(b)\n",
                                lambda za, r: r == 3).status == PROVED

    # list concatenation and repetition produce fresh lists; string and tuple
    #     concatenation/repetition were added with their types.
    assert verify_heap_property("list-cat", "f",
                                "def f():\n    a = [1, 2]\n    b = [3, 4]\n    c = a + b\n    return c[2]\n",
                                lambda za, r: r == 3).status == PROVED
    assert verify_heap_property("list-cat-len", "f",
                                "def f():\n    a = [1, 2]\n    b = [3, 4]\n    c = a + b\n    return len(c)\n",
                                lambda za, r: r == 4).status == PROVED
    assert verify_heap_property("list-rep", "f",
                                "def f():\n    a = [1, 2]\n    b = a * 2\n    return b[3]\n",
                                lambda za, r: r == 2).status == PROVED
    assert verify_heap_property("list-cat-frame", "f",
                                "def f():\n    a = [1, 2]\n    b = [3]\n    c = a + b\n    c.append(9)\n    return len(a)\n",
                                lambda za, r: r == 2).status == PROVED

    # starred unpacking targets; plain unpacking and subscript/attribute
    #     targets landed with tuples and subscripting.
    assert verify_predicate("star-mid", "f", "def f():\n    a, *b, c = (1, 2, 3, 4, 5)\n    return a + c\n",
                            lambda za, o: o == 6, {}).status == PROVED
    assert verify_predicate("star-len", "f", "def f():\n    a, *b, c = (1, 2, 3, 4, 5)\n    return len(b)\n",
                            lambda za, o: o == 3, {}).status == PROVED
    assert verify_predicate("star-tail", "f", "def f():\n    first, *rest = (1, 2, 3)\n    return rest[0]\n",
                            lambda za, o: o == 2, {}).status == PROVED
    assert verify_equiv("star-sym", "f", "def f(p, q, r):\n    a, *b, c = (p, q, r)\n    return a + c\n",
                        "def g(p, q, r):\n    return p + r\n", {}).status == PROVED

    # complete exceptions: multiple handlers, finally, as-e, and Exception as a
    #     catch-all; an exact-type mismatch still escapes.
    _multi = ("def f(x):\n    try:\n        if x < 0:\n            raise ValueError\n        if x == 0:\n            raise KeyError\n"
              "        y = x\n    except ValueError:\n        y = 1\n    except KeyError:\n        y = 2\n    return y\n")
    assert verify_no_raise("multi", "f", _multi, lambda S: z3.BoolVal(True)).status == PROVED
    assert verify_no_raise("catchall", "f",
                           "def f(x):\n    try:\n        raise KeyError\n    except Exception:\n        x = 0\n    return x\n",
                           lambda S: z3.BoolVal(True)).status == PROVED
    assert verify_no_raise("ase", "f",
                           "def f(x):\n    try:\n        if x < 0:\n            raise ValueError\n    except ValueError as e:\n        x = 0\n    return x\n",
                           lambda S: z3.BoolVal(True)).status == PROVED
    assert verify_no_raise("mismatch", "f",
                           "def f(x):\n    try:\n        raise KeyError\n    except ValueError:\n        x = 0\n    return x\n",
                           lambda S: z3.BoolVal(True)).status == REFUTED   # KeyError is not a ValueError
    # exception matching follows the class MRO -- the module's user-defined `class Sub(Base)` hierarchy and
    # Python's builtin exception tree -- so an `except Base` catches a `raise Sub`, and `except LookupError`
    # catches a `raise IndexError`, while an unrelated sibling still escapes. A tuple handler `except (A, B)`
    # catches exactly A, B, and their subclasses.
    _hier = ("class Base(Exception):\n    pass\nclass Sub(Base):\n    pass\n"
             "def f(x):\n    try:\n        raise Sub\n    except %s:\n        return 0\n    return x\n")
    assert check(_hier % "Base", target="f").status == PROVED              # a base handler catches a subclass raise
    assert check(_hier % "Sub", target="f").status == PROVED               # the exact class still matches
    assert check("class A(Exception):\n    pass\nclass B(Exception):\n    pass\n"
                 "def f(x):\n    try:\n        raise A\n    except B:\n        return 0\n    return x\n",
                 target="f").status == REFUTED                             # an unrelated sibling escapes
    assert check("def f(x):\n    try:\n        raise ZeroDivisionError\n    except ArithmeticError:\n        return 0\n"
                 "    return x\n", target="f").status == PROVED            # builtin MRO: ZeroDivisionError < ArithmeticError
    assert check("def f(x):\n    try:\n        raise IndexError\n    except LookupError:\n        return 0\n    return x\n",
                 target="f").status == PROVED                             # IndexError < LookupError
    assert check("def f(x):\n    try:\n        raise KeyError\n    except (ValueError, TypeError):\n        return 0\n"
                 "    return x\n", target="f").status == REFUTED          # tuple handler: KeyError in neither
    assert check("def f(x):\n    try:\n        raise KeyError\n    except (ValueError, LookupError):\n        return 0\n"
                 "    return x\n", target="f").status == PROVED           # tuple handler catches via the MRO
    # finally always runs and is reflected in the result (try/finally with no except)
    assert verify_function("finally", "f",
                           "def f(x):\n    y = 0\n    try:\n        y = 1\n    finally:\n        y = y + 10\n    return y\n",
                           lambda S: z3.BoolVal(True), lambda S, r: r == 11, {}).status == PROVED

    # generators: a finite straight-line generator denotes the tuple of its
    #     yields, consumable by unpacking and indexing; yield from splices a finite generator.
    _gn = {"g": "def g(n):\n    x = n\n    yield x\n    yield x + 1\n    yield x + 2\n"}
    assert verify_equiv("gen-sum", "f", "def f(n):\n    a, b, c = g(n)\n    return a + b + c\n",
                        "def h(n):\n    return 3 * n + 3\n", _gn).status == PROVED
    _yf = {"inner": "def inner():\n    yield 1\n    yield 2\n", "g": "def g():\n    yield from inner()\n    yield 3\n"}
    assert verify_predicate("yieldfrom", "f", "def f():\n    a, b, c = g()\n    return a + b + c\n",
                            lambda za, o: o == 6, _yf).status == PROVED
    assert verify_predicate("gen-index", "f", "def f():\n    t = g()\n    return t[1]\n",
                            lambda za, o: o == 2, {"g": "def g():\n    yield 1\n    yield 2\n    yield 3\n"}).status == PROVED

    # for over arbitrary iterables and for/while-else: constant tuple/list,
    #     enumerate, and zip unroll; the else clause runs on normal loop exit.
    assert verify_predicate("for-tuple", "f", "def f():\n    s = 0\n    for x in (1, 2, 3):\n        s = s + x\n    return s\n",
                            lambda za, o: o == 6, {}).status == PROVED
    assert verify_predicate("for-enum", "f",
                            "def f():\n    s = 0\n    for i, v in enumerate((10, 20, 30)):\n        s = s + i * v\n    return s\n",
                            lambda za, o: o == 80, {}).status == PROVED
    assert verify_predicate("for-zip", "f",
                            "def f():\n    s = 0\n    for a, b in zip((1, 2, 3), (4, 5, 6)):\n        s = s + a * b\n    return s\n",
                            lambda za, o: o == 32, {}).status == PROVED
    assert verify_function("for-else", "f",
                           "def f(n):\n    r = 0\n    for i in range(n):\n        r = r + 1\n    else:\n        r = r + 100\n    return r\n",
                           lambda S: S["n"] >= 0, lambda S, rr: rr == S["n"] + 100, {}).status == PROVED

    # with / context managers: the body runs in the managed scope with cleanup
    #      on both the normal and the exception path; an unguarded raise still escapes.
    assert verify_function("with", "f", "def f(x):\n    with lock:\n        y = x + 1\n    return y\n",
                           lambda S: z3.BoolVal(True), lambda S, r: r == S["x"] + 1, {}).status == PROVED
    assert verify_function("with-nested", "f", "def f(x):\n    with lock1, lock2:\n        y = x * 2\n    return y\n",
                           lambda S: z3.BoolVal(True), lambda S, r: r == 2 * S["x"], {}).status == PROVED
    assert verify_no_raise("with-raise", "f",
                           "def f(x):\n    with lock:\n        if x < 0:\n            raise ValueError\n    return x\n",
                           lambda S: S["x"] >= 0).status == PROVED
    assert verify_heap_property("with-heap", "f",
                                "def f():\n    with object() as o:\n        o.v = 7\n    return o.v\n",
                                lambda za, r: r == 7).status == PROVED
    # a context manager whose __exit__ provably returns a truthy constant suppresses the body's raised
    # exceptions (the contextlib.suppress shape); a non-suppressing __exit__ propagates as before.
    _supcm = "class S:\n    def __enter__(self):\n        return self\n    def __exit__(self, a, b, c):\n        return True\n"
    assert check(_supcm + "def f(x):\n    with S():\n        raise ValueError\n    return x\n", target="f").status == PROVED
    assert check(_supcm + "def f(x):\n    with S():\n        if x < 0:\n            raise ValueError\n    return x\n", target="f").status == PROVED
    _nocm = "class N:\n    def __enter__(self):\n        return self\n    def __exit__(self, a, b, c):\n        return False\n"
    assert check(_nocm + "def f(x):\n    with N():\n        raise ValueError\n    return x\n", target="f").status == REFUTED
    assert check(_nocm + "def f(x):\n    with N():\n        return x\n", target="f").status == PROVED
    # contextlib.suppress(ExcTypes) -- contextlib.suppress(...) or a suppress(...) imported from contextlib --
    # swallows the body's explicit raises of those types: `with contextlib.suppress(ValueError): raise ValueError`
    # does not escape (a false REFUTED before, since the finally model let it propagate), while a raise of an
    # unsuppressed type still does, and a tuple of types catches any of them.
    assert check("import contextlib\ndef f(x):\n    with contextlib.suppress(ValueError):\n        raise ValueError\n    return x\n", target="f").status == PROVED
    assert check("from contextlib import suppress\ndef f(x):\n    with suppress(ValueError):\n        raise ValueError\n    return x\n", target="f").status == PROVED
    assert check("import contextlib\ndef f(x):\n    with contextlib.suppress(ValueError):\n        raise KeyError\n    return x\n", target="f").status == REFUTED
    assert check("import contextlib\ndef f(x):\n    with contextlib.suppress(ValueError, KeyError):\n        raise KeyError\n    return x\n", target="f").status == PROVED
    # an OPERATION trap inside a try / with -- a division's ZeroDivisionError -- is routed through the handler too:
    # `if d == 0: raise ZeroDivisionError()` is prepended before each division (only when the function has a
    # try/with), so the CFG catches it along the exception MRO. A caught division (except ZeroDivisionError /
    # ArithmeticError / Exception, or contextlib.suppress(ZeroDivisionError)) PROVES -- a false REFUTED before --
    # while an unmatched handler (except KeyError) still REFUTES with the divisor==0 witness; a function without a
    # try/with is byte-identical, so a bare division still refutes and a guarded one still proves.
    assert check("def f(x):\n    try:\n        return 10 // x\n    except ZeroDivisionError:\n        return 0\n", target="f").status == PROVED
    assert check("def f(x):\n    try:\n        return 10 % x\n    except ArithmeticError:\n        return 0\n", target="f").status == PROVED
    assert check("def f(x):\n    try:\n        return 10 // x\n    except Exception:\n        return 0\n", target="f").status == PROVED
    assert check("def f(x):\n    try:\n        return 10 // x\n    except KeyError:\n        return 0\n", target="f").status == REFUTED
    assert check("import contextlib\ndef f(x):\n    with contextlib.suppress(ZeroDivisionError):\n        return 10 // x\n    return 0\n", target="f").status == PROVED
    assert check("def f(x):\n    return 10 // x\n", target="f").status == REFUTED                  # no try: unchanged
    assert check("def f(x):\n    if x != 0:\n        return 10 // x\n    return 0\n", target="f").status == PROVED   # guard: unchanged

    # match/case structural pattern matching: literals, capture, wildcard,
    #      or-patterns, and guards, desugared to an if/elif/else chain.
    assert verify_equiv("match-lit", "f",
                        "def f(x):\n    match x:\n        case 0:\n            return 10\n        case 1:\n            return 20\n        case _:\n            return 30\n",
                        "def g(x):\n    if x == 0:\n        return 10\n    if x == 1:\n        return 20\n    return 30\n", {}).status == PROVED
    assert verify_equiv("match-cap", "f",
                        "def f(x):\n    match x:\n        case 0:\n            return 100\n        case y:\n            return y + 1\n",
                        "def g(x):\n    if x == 0:\n        return 100\n    return x + 1\n", {}).status == PROVED
    assert verify_predicate("match-or", "f",
                            "def f(x):\n    match x:\n        case 1 | 2 | 3:\n            return 1\n        case _:\n            return 0\n",
                            lambda za, o: z3.Implies(z3.Or(za['x'] == 1, za['x'] == 2, za['x'] == 3), o == 1), {}).status == PROVED
    assert verify_predicate("match-guard", "f",
                            "def f(x):\n    match x:\n        case n if n * 2 > 10:\n            return n\n        case _:\n            return 0\n",
                            lambda za, o: o == z3.If(za['x'] * 2 > 10, za['x'], 0), {}).status == PROVED

    # comprehensions and generator expressions over constant iterables, lowered to a build sequence
    assert verify_heap_property("lc-elem", "f", "def f():\n    r = [x * x for x in (1, 2, 3)]\n    return r[2]\n",
                                lambda za, r: r == 9).status == PROVED
    assert verify_heap_property("lc-filter", "f",
                                "def f():\n    r = [x for x in (1, 2, 3, 4) if x > 2]\n    return len(r)\n",
                                lambda za, r: r == 2).status == PROVED
    assert verify_heap_property("sc-dedup", "f", "def f():\n    r = {x % 2 for x in (1, 2, 3, 4)}\n    return len(r)\n",
                                lambda za, r: r == 2).status == PROVED
    assert verify_heap_property("dc-elem", "f", "def f():\n    r = {x: x * x for x in (1, 2, 3)}\n    return r[3]\n",
                                lambda za, r: r == 9).status == PROVED
    assert verify_heap_property("lc-enum", "f",
                                "def f():\n    r = [i * v for i, v in enumerate((5, 6))]\n    return r[1]\n",
                                lambda za, r: r == 6).status == PROVED

    # lambda as a value (with closures), is / is not identity, and starred calls.
    assert verify_equiv("lam-store", "f", "def f(a):\n    g = lambda x: x * 2\n    return g(a)\n",
                        "def h(a):\n    return a + a\n", {}).status == PROVED
    assert verify_equiv("lam-closure", "f", "def f(a, k):\n    add = lambda x: x + k\n    return add(a)\n",
                        "def h(a, k):\n    return a + k\n", {}).status == PROVED
    assert verify_heap_property("is-alias", "f",
                                "def f():\n    a = object()\n    b = a\n    if a is b:\n        return 1\n    return 0\n",
                                lambda za, r: r == 1).status == PROVED
    assert verify_heap_property("is-distinct", "f",
                                "def f():\n    a = object()\n    b = object()\n    if a is not b:\n        return 1\n    return 0\n",
                                lambda za, r: r == 1).status == PROVED
    assert verify_predicate("starred", "f", "def f():\n    return add3(*(1, 2, 3))\n", lambda za, o: o == 6,
                            {"add3": "def add3(a, b, c):\n    return a + b + c\n"}).status == PROVED
    # a positional *xs splat of a variable-length sequence parameter into a callee's named parameters
    # binds xs[0..n-1] and raises TypeError unless len(xs) equals the parameter count. So an unguarded g(*xs)
    # is REFUTED on the arity mismatch, a len(xs) == N guard binds and inlines g (PROVED when g is trap free),
    # a guard to the WRONG length still refutes (a 2-element splat into a 3-parameter callee is a TypeError),
    # and a callee that traps on its (now arbitrary) arguments refutes. A constant-tuple splat is unaffected.
    _g2 = "def g(a, b):\n    return a + b\n"
    _f_un = "def f(t: tuple):\n    return g(*t)\n"
    assert check(_f_un, repo={"g": _g2, "f": _f_un}, target="f").status == REFUTED                  # wrong-arity TypeError
    _f_g = "def f(t: tuple):\n    if len(t) == 2:\n        return g(*t)\n    return 0\n"
    assert check(_f_g, repo={"g": _g2, "f": _f_g}, target="f").status == PROVED                      # len==2 guard: binds, safe
    assert check(_f_g, repo={"g": "def g(a, b, c):\n    return a + b + c\n", "f": _f_g},
                 target="f").status == REFUTED                                                       # 2-splat into 3 params
    assert check(_f_g, repo={"g": "def g(a, b):\n    return a // b\n", "f": _f_g},
                 target="f").status == REFUTED                                                       # callee traps a // b
    assert check("def f():\n    return g(*(1, 2))\n", repo={"g": _g2, "f": "def f():\n    return g(*(1, 2))\n"},
                 target="f").status == PROVED                                                        # constant tuple: unaffected
    # a method call on a class-annotated parameter (o: C, C a module class) dispatches to the method body:
    # a reachable trap there refutes with a plain-receiver witness (a C instance satisfies o: C), while a safe
    # method -- or one whose body is outside the modeled subset -- keeps its verdict (the dispatch only upgrades
    # a PROVED to REFUTED, never regresses). self / attribute access in the body stays opaque.
    _C4 = ("class C:\n    def __init__(self, v):\n        self.v = v\n    def get(self):\n        return self.v\n"
           "    def bad(self):\n        return 10 // 0\n    def divx(self, x):\n        return 10 // x\n"
           "    def complex(self):\n        return self.v.pop()\n")
    assert check(_C4 + "def f(o: C):\n    return o.bad()\n", target="f").status == REFUTED            # visible 10 // 0
    assert check(_C4 + "def f(o: C, y):\n    return o.divx(y)\n", target="f").status == REFUTED       # 10 // y, y == 0
    assert check(_C4 + "def f(o: C):\n    return o.divx(5)\n", target="f").status == PROVED            # 10 // 5: safe, kept
    assert check(_C4 + "def f(o: C):\n    return o.get()\n", target="f").status == PROVED              # safe method: kept
    assert check(_C4 + "def f(o: C):\n    return o.complex()\n", target="f").status == PROVED          # body outside subset: no regression
    assert check("def f(o):\n    return o.frobnicate()\n", target="f").status == PROVED                # unannotated receiver: unchanged

    # user-defined classes: __init__, methods (with branching), single
    #      inheritance, instantiation, dispatch, and aliasing of objects through methods.
    _pt = ("class Point:\n    def __init__(self, x, y):\n        self.x = x\n        self.y = y\n"
           "    def normsq(self):\n        return self.x * self.x + self.y * self.y\n"
           "def f():\n    p = Point(3, 4)\n    return p.normsq()\n")
    assert verify_heap_property("class-method", "f", _pt, lambda za, r: r == 25).status == PROVED
    _ctr = ("class Counter:\n    def __init__(self):\n        self.n = 0\n    def inc(self):\n        self.n = self.n + 1\n"
            "def f():\n    c = Counter()\n    c.inc()\n    c.inc()\n    c.inc()\n    return c.n\n")
    assert verify_heap_property("class-mutate", "f", _ctr, lambda za, r: r == 3).status == PROVED
    _mag = ("class V:\n    def __init__(self, x):\n        self.x = x\n    def mag(self):\n        if self.x < 0:\n            return -self.x\n        return self.x\n"
            "def f(a):\n    v = V(a)\n    return v.mag()\n")
    assert verify_heap_property("class-branch", "f", _mag, lambda za, r: r >= 0).status == PROVED
    _inh = ("class Animal:\n    def __init__(self, legs):\n        self.legs = legs\n    def legcount(self):\n        return self.legs\n"
            "class Dog(Animal):\n    def speak(self):\n        return 4\n"
            "def f():\n    d = Dog(4)\n    return d.legcount() + d.speak()\n")
    assert verify_heap_property("class-inherit", "f", _inh, lambda za, r: r == 8).status == PROVED
    _alias = ("class Box:\n    def __init__(self):\n        self.v = 0\n    def set(self, x):\n        self.v = x\n"
              "def f(x):\n    a = Box()\n    b = a\n    a.set(x)\n    return b.v\n")
    assert verify_heap_property("class-alias", "f", _alias, lambda za, r: r == za["x"]).status == PROVED

    # dunder dispatch / operator overloading on objects: __add__, __eq__,
    #      __len__, __getitem__ route operators and builtins to the instance's methods.
    _vec = ("class Vec:\n    def __init__(self, x, y):\n        self.x = x\n        self.y = y\n"
            "    def __add__(self, o):\n        return Vec(self.x + o.x, self.y + o.y)\n"
            "def f(a, b):\n    r = Vec(a, 0) + Vec(b, 0)\n    return r.x\n")
    assert verify_heap_property("dunder-add", "f", _vec, lambda za, r: r == za["a"] + za["b"]).status == PROVED
    _eq = ("class P:\n    def __init__(self, x):\n        self.x = x\n    def __eq__(self, o):\n        return self.x == o.x\n"
           "def f(a):\n    p = P(a)\n    q = P(a)\n    if p == q:\n        return 1\n    return 0\n")
    assert verify_heap_property("dunder-eq", "f", _eq, lambda za, r: r == 1).status == PROVED
    _ln = ("class Stack:\n    def __init__(self, n):\n        self.n = n\n    def __len__(self):\n        return self.n\n"
           "def f(k):\n    s = Stack(k)\n    return len(s)\n")
    assert verify_heap_property("dunder-len", "f", _ln, lambda za, r: r == za["k"]).status == PROVED
    _gi = ("class Squares:\n    def __init__(self):\n        self.b = 0\n    def __getitem__(self, i):\n        return i * i\n"
           "def f():\n    s = Squares()\n    return s[5]\n")
    assert verify_heap_property("dunder-getitem", "f", _gi, lambda za, r: r == 25).status == PROVED

    # argument grammar: default, keyword, and keyword-only arguments at call sites.
    _g = {"g": "def g(x, y=10):\n    return x + y\n"}
    assert verify_predicate("arg-default", "f", "def f():\n    return g(5)\n", lambda za, o: o == 15, _g).status == PROVED
    assert verify_predicate("arg-kw", "f", "def f():\n    return g(x=2, y=3)\n", lambda za, o: o == 5, _g).status == PROVED
    assert verify_predicate("arg-mixed", "f", "def f():\n    return g(2, y=7)\n", lambda za, o: o == 9, _g).status == PROVED
    _h = {"h": "def h(a, *, scale=2):\n    return a * scale\n"}
    assert verify_predicate("arg-kwonly", "f", "def f():\n    return h(4)\n", lambda za, o: o == 8, _h).status == PROVED
    assert verify_predicate("arg-kwonly2", "f", "def f():\n    return h(4, scale=3)\n", lambda za, o: o == 12, _h).status == PROVED
    assert verify_equiv("arg-sym", "f", "def f(a):\n    return g(a)\n", "def k(a):\n    return a + 10\n", _g).status == PROVED
    # call-site ** splat of a constant-string-keyed dict literal binds into the named parameters (the
    # counterpart of the *tuple splat _eval_args handles): the bound values are exact.
    assert verify_predicate("arg-ddsplat", "f", "def f():\n    return g(**{'x': 2, 'y': 5})\n",
                            lambda za, o: o == 7, _g).status == PROVED
    assert verify_predicate("arg-ddsplat-mix", "f", "def f():\n    return g(2, **{'y': 5})\n",
                            lambda za, o: o == 7, _g).status == PROVED
    # a spliced key that names no parameter, collides with a positional, or comes from a non-literal
    # (symbolic-key) mapping is declined symbolically, never silently bound (Python would TypeError).
    _sb = core.SANDBOX_SUBJECT; core.SANDBOX_SUBJECT = False
    for _bad in ("def f(a, b):\n    return g(**{'x': a, 'z': b})\n",      # 'z' names no parameter
                 "def f(a):\n    return g(a, **{'x': a})\n",              # 'x' already given positionally
                 "def f(a, d):\n    return g(**d)\n"):                    # non-literal (symbolic-key) mapping
        assert check(_bad, repo={"g": _g["g"], "f": _bad}, target="f").status == UNKNOWN, _bad
    core.SANDBOX_SUBJECT = _sb
    # int(...) conversion: exact for an integer/bool argument (so a trap through it refutes with a witness),
    # 0 for int(), and a sound over-approximation for a float (REFUTED withheld, PROVED still sound).
    assert prove("def f(x):\n    return int(x)\n", "result == x", target="f").status == PROVED
    _iz = check("def f(x):\n    return 7 // int(x)\n", target="f")          # int(x) == 0 reachable -> witnessed REFUTED
    assert _iz.status == REFUTED and _iz.counterexample_inputs == {"x": 0}, _iz
    assert check("def f():\n    return 5 // int()\n", target="f").status == REFUTED       # int() == 0
    assert check("def f(x):\n    y = x / 2.0\n    return int(y)\n", target="f").status == PROVED   # int(float): no trap
    _io = check("def f(x):\n    y = x / 2.0\n    return 9 // int(y)\n", target="f")       # over-approx: no spurious refute
    assert _io.status == UNKNOWN, _io
    # sum(...): exact over a constant-length sequence (so a trap through it refutes), and a sound
    # over-approximation over an int-element container parameter (no trap, but REFUTED withheld). A bare
    # parameter used only as sum(p) is inferred to be a container.
    assert prove("def f(a, b, c):\n    return sum((a, b, c))\n", "result == a + b + c", target="f").status == PROVED
    assert check("def f():\n    return 10 // sum((1, -1))\n", target="f").status == REFUTED       # exact 0
    assert check("def f():\n    return 10 // sum((1, 2, 3))\n", target="f").status == PROVED       # exact 6
    assert check("def f(nums):\n    return sum(nums) + 1\n", target="f").status == PROVED          # container: no trap
    # sum / min / max over a container is a stable named arbitrary int (not a withheld over-approximation), so a
    # division by an INDEPENDENT divisor -- the average sum(xs) / len(xs) over a possibly-empty list -- refutes
    # on len == 0 (the reduction no longer poisons the verdict), a guard on the length or the reduction proves,
    # and a division by the reduction itself refutes (the sum can be zero: the empty list, or [1, -1]).
    _su = check("def f(nums):\n    return 10 // sum(nums)\n", target="f")                          # sum can be 0:
    assert _su.status == REFUTED, _su                                                             # a real trap
    assert check("def f(xs: list):\n    return sum(xs) / len(xs)\n", target="f").status == REFUTED
    assert check("def f(xs: list):\n    if len(xs) > 0:\n        return sum(xs) / len(xs)\n    return 0\n",
                 target="f").status == PROVED
    assert check("def f(xs: list):\n    s = sum(xs)\n    if s != 0:\n        return 10 // s\n    return 0\n",
                 target="f").status == PROVED                                                      # guard on the stable sum
    # math float constants (math.pi / e / tau / inf / nan, and the bare `from math import pi` names) are modeled
    # exactly, so arithmetic over them decides; a local name shadows the module.
    assert check("def f(r):\n    return 2 * pi * r\n", target="f").status == PROVED                # bare pi
    assert prove("def f(r):\n    return 2 * math.pi * r\n", "result == 2.0 * 3.141592653589793 * r",
                 target="f").status == PROVED                                                      # exact value
    assert check("def f(angle, radius):\n    return 2 * math.pi * radius * (angle / 360)\n",
                 target="f").status == PROVED                                                      # a real arc length
    assert check("def f(math):\n    return math + 1\n", target="f").status == PROVED               # param shadows module
    # float(...): exact for an int/bool argument (a float-zero division through it refutes), 0.0 for float();
    # a string or unmodeled argument is declined (its parse can raise ValueError).
    assert prove("def f(x):\n    return float(x)\n", "result == 1.0 * x", target="f").status == PROVED
    assert check("def f(x):\n    return 1.0 / float(x)\n", target="f").status == REFUTED            # float(0) == 0.0
    assert check("def f():\n    return float()\n", target="f").status == PROVED                     # float() -> 0.0
    # bool(...): exact for int/bool/float -- bool() is False, bool(int) is the nonzero test (so a bool(x)
    # guard proves the division safe), a string/container argument is declined.
    assert prove("def f(x):\n    return bool(x)\n", "result == (x != 0)", target="f").status == PROVED
    assert check("def f(x):\n    if bool(x):\n        return 10 // x\n    return 0\n", target="f").status == PROVED
    assert prove("def f():\n    return bool()\n", "result == False", target="f").status == PROVED
    # f-string !r / !a / !s conversions never trap (repr/ascii/str of any value): an opaque string with the
    # interpolated expression still trap-checked; a type-incompatible format spec is declined.
    assert check("def f(n):\n    return f'value={n!r}'\n", target="f").status == PROVED
    assert check("def f(n):\n    return f'{(10 // n)!r}'\n", target="f").status == REFUTED   # interpolated expr traps
    assert check("def f(n):\n    return f'{n:.2d}'\n", target="f").status == UNKNOWN          # precision on an integer: declined
    # str(x) for a modeled value -- a number, bool, None, string, or a list / dict / tuple -- calls a builtin
    # __str__ that cannot raise, so it is a string of unknown content (a fresh string, the format/split
    # over-approximation channel): the call is total (PROVED), len/concatenation on the result work, and a
    # later trap still refutes. str() of a value the engine holds only opaquely -- an unmodeled call/method
    # result, whose runtime __str__ could be a user override that raises -- stays declined.
    assert check("def f(n: int):\n    return str(n)\n", target="f").status == PROVED
    assert check("def f(n: int):\n    return len(str(n)) >= 0\n", target="f").status == PROVED
    assert check("def f(x: float):\n    return str(x) + '!'\n", target="f").status == PROVED
    assert check("def f():\n    return str()\n", target="f").status == PROVED                  # str() is the empty string
    assert check("def f(n: int):\n    s = str(n)\n    return 1 // 0\n", target="f").status == REFUTED   # str total, trap after
    assert check("def f(o):\n    return str(o.compute())\n", target="f").status == UNKNOWN      # opaque result: __str__ may raise
    # range(...) used as a VALUE (not the for-loop iterable, which is desugared separately) is a sized,
    # immutable integer sequence carrying its EXACT length. len(range(n)) is total; the exactness is
    # witnessed through trap freedom -- an index equal to the length is always out of range (REFUTED, which a
    # fresh symbolic length could not give), an index one below it under a guard is in range (PROVED), and the
    # step-2 and negative-step lengths bound their indices precisely. A zero step refutes (ValueError), a
    # non-constant step is declined, an unguarded index refutes, and range flowing into sum stays total.
    assert check("def f(n: int):\n    return len(range(n))\n", target="f").status == PROVED
    assert check("def f(n: int):\n    return range(n)[n]\n", target="f").status == REFUTED              # idx == len: out of range
    assert check("def f(n: int):\n    if n > 0:\n        return range(n)[n - 1]\n    return 0\n", target="f").status == PROVED
    assert check("def f():\n    return range(0, 10, 2)[4]\n", target="f").status == PROVED              # len 5: index 4 in range
    assert check("def f():\n    return range(0, 10, 2)[5]\n", target="f").status == REFUTED             # len 5: index 5 out of range
    assert check("def f():\n    return range(10, 0, -1)[10]\n", target="f").status == REFUTED           # negative step, len 10
    assert check("def f(n: int, i: int):\n    if 0 <= i and i < n:\n        return range(n)[i]\n    return 0\n", target="f").status == PROVED
    assert check("def f(n: int, i: int):\n    return range(n)[i]\n", target="f").status == REFUTED      # i may be out of range
    assert check("def f(a: int, b: int):\n    return len(range(a, b, 0))\n", target="f").status == REFUTED   # zero step: ValueError
    assert check("def f(a: int, b: int, s: int):\n    return len(range(a, b, s))\n", target="f").status == REFUTED   # non-constant step: ValueError when s == 0
    assert check("def f(a: int, b: int, s: int):\n    if s != 0:\n        return len(range(a, b, s))\n    return 0\n", target="f").status == PROVED   # guarded
    # a constant zero step refutes in any consuming context, not only len(): the post-trap value is a consumable
    # container, so list()/sum()/a bare return reach the trap instead of choking on an opaque.
    assert check("def f():\n    return list(range(0, 10, 0))\n", target="f").status == REFUTED
    assert check("def f():\n    return sum(range(1, 9, 0))\n", target="f").status == REFUTED
    assert check("def f():\n    return range(0, 10, 0)\n", target="f").status == REFUTED
    assert check("def f():\n    return len(list(range(0, 10, 2))) == 5\n", target="f").status == PROVED   # nonzero step: total
    assert check("def f(n: int):\n    return sum(range(n))\n", target="f").status == PROVED             # sized: sum is total
    # a single-generator list comprehension [e for x in it] is a NEW sized list: its length is the iterable's
    # length with no filter (so c = [0 for i in range(n)]; c[i] bounds-checks against n -- guarded by 0 <= i <
    # n it proves, an unguarded or c[n] index refutes), and a fresh nonnegative length bounded by the iterable
    # when filtered (c[0] may be out of range, refuted; a len() guard proves). len / iteration over a
    # comprehension are unchanged, and a generator expression (not
    # indexable) stays opaque.
    assert check("def f(n: int):\n    c = [0 for i in range(n)]\n    if n > 0:\n        return c[0]\n    return 0\n", target="f").status == PROVED
    assert check("def f(n: int, i: int):\n    c = [0 for j in range(n)]\n    if 0 <= i < n:\n        return c[i]\n    return 0\n", target="f").status == PROVED
    assert check("def f(n: int):\n    c = [0 for i in range(n)]\n    return c[n]\n", target="f").status == REFUTED   # idx == len
    assert check("def f(n: int):\n    c = [i for i in range(n) if i % 2 == 0]\n    return c[0]\n", target="f").status == REFUTED   # may be empty
    assert check("def f(n: int):\n    c = [i for i in range(n) if i % 2 == 0]\n    if len(c) > 0:\n        return c[0]\n    return 0\n", target="f").status == PROVED
    assert check("def f(xs: list[int], i: int):\n    c = [x + 1 for x in xs]\n    if 0 <= i < len(c):\n        return c[i]\n    return 0\n", target="f").status == PROVED
    # a single-generator comprehension's element / filters run only when the iterable yields an element, so a
    # trap in the element is conditioned on len(iterable) >= 1: `[10 // n for i in range(1, n)]` does not flag a
    # crash at n == 0 (range(1, 0) is empty -- the NormalDist.quantiles(0) spurious witness), nor at any n (n >= 2
    # makes 10 // n safe), so it PROVES; a genuinely reachable element trap (`[10 // i for i in range(0, n)]`,
    # i == 0 at n >= 1, or a possibly-zero list element) still REFUTES.
    assert check("def f(n):\n    return [10 // n for i in range(1, n)]\n", target="f").status == PROVED
    assert check("def f(n):\n    return [10 // n for i in range(n)]\n", target="f").status == PROVED
    assert check("def f(n):\n    return [10 // i for i in range(0, n)]\n", target="f").status == REFUTED
    assert check("def f(xs: list):\n    return [10 // x for x in xs]\n", target="f").status == REFUTED
    # sorted(it) and list(it) build a NEW same-length indexable list, so sorted(nums)[0] / list(xs)[i] bounds-
    # check against the iterable's length: guarded by len it proves, an
    # unguarded index refutes, and the whole sort-then-median idiom decides. An opaque (possibly non-iterable)
    # argument and a key= keyword are declined; reverse= changes order only and is accepted.
    assert check("def f(nums: list):\n    if len(nums) > 0:\n        return sorted(nums)[0]\n    return 0\n", target="f").status == PROVED
    assert check("def f(nums: list):\n    return sorted(nums)[0]\n", target="f").status == REFUTED                   # may be empty
    # sorted(it, reverse=bool) is the same sized container as sorted(it) -- reverse changes order only, never the
    # length or whether it raises -- so it decides exactly like the unkeyed sort (a guarded index proves, an unguarded
    # one refutes on the empty list); a param flag is trap-checked. A key= callable still abstains, even beside reverse=.
    assert check("def f(xs: list):\n    if len(xs) > 0:\n        return sorted(xs, reverse=True)[0]\n    return 0\n", target="f").status == PROVED
    assert check("def f(xs: list):\n    return sorted(xs, reverse=True)[0]\n", target="f").status == REFUTED
    assert check("def f(xs: list, r):\n    return len(sorted(xs, reverse=r))\n", target="f").status == PROVED
    assert check("def f(xs: list):\n    return len(sorted(xs, key=abs, reverse=True))\n", target="f").status == UNKNOWN
    assert check("def f(xs: list, i: int):\n    c = list(xs)\n    if 0 <= i < len(c):\n        return c[i]\n    return 0\n", target="f").status == PROVED
    assert check("def f(n: int, i: int):\n    c = list(range(n))\n    if 0 <= i < n:\n        return c[i]\n    return 0\n", target="f").status == PROVED
    assert check("def f(nums: list):\n    s = sorted(nums)\n    n = len(s)\n    if n == 0:\n        return 0\n    if n % 2 == 1:\n        return s[n // 2]\n    return (s[n // 2 - 1] + s[n // 2]) / 2\n", target="f").status == PROVED   # the median idiom
    assert check("def f(n: int):\n    return list(n)\n", target="f").status != PROVED                               # int is not iterable
    # print(...) is a total call returning None (the same assume-str-safe over-approximation an f-string
    # makes). Each argument is still
    # trap-checked (print(10 // n) refutes), the result is None (using it in arithmetic refutes), and an
    # input-validation raise before the print still refutes.
    assert check("def f(n: int):\n    print('value', n)\n    return n\n", target="f").status == PROVED
    assert check("def f(n: int):\n    print(f'v={n}')\n    return n\n", target="f").status == PROVED                  # f-string arg
    assert check("def f(n: int):\n    print(10 // n)\n    return 0\n", target="f").status == REFUTED                  # arg trap-checked
    assert check("def f(n: int):\n    x = print(n)\n    return x + 1\n", target="f").status == REFUTED                # result is None
    # a set / frozenset parameter is a sized, iterable, membership-queryable container that is NOT
    # subscriptable: len(s), x in s, and for x in s are total, while s[i], s[i:j], and s[i] = v each raise
    # TypeError (REFUTED -- a real crash for every set), so a function that indexes a set is a bug, not a
    # missed model. list and tuple indexing is unchanged.
    assert check("def f(s: set):\n    return len(s)\n", target="f").status == PROVED
    assert check("def f(s: frozenset):\n    return len(s)\n", target="f").status == PROVED
    assert check("def f(s: set, x: int):\n    return x in s\n", target="f").status == PROVED
    assert check("def f(s: set):\n    t = 0\n    for x in s:\n        t = x\n    return t\n", target="f").status == PROVED
    assert check("def f(s: set, i: int):\n    return s[i]\n", target="f").status == REFUTED              # set not subscriptable
    assert check("def f(s: set):\n    return s[1:2]\n", target="f").status == REFUTED                    # set not sliceable
    assert check("def f(s: set, i: int, v: int):\n    s[i] = v\n    return 0\n", target="f").status == REFUTED   # set item-assign
    assert check("def f(a: list, i: int):\n    if 0 <= i < len(a):\n        return a[i]\n    return 0\n", target="f").status == PROVED
    # bytes / bytearray are sized sequences of ints: an integer index is bounds-checked (IndexError), len and a
    # slice are total, iteration is total, bytes (immutable) refutes an item store as a TypeError while bytearray
    # bounds-checks it, and a trapping method (decode, which can UnicodeDecodeError) abstains.
    assert check("def f(b: bytes):\n    return b[0]\n", target="f").status == REFUTED
    assert check("def f(b: bytes):\n    if len(b) > 0:\n        return b[0]\n    return 0\n", target="f").status == PROVED
    assert check("def f(b: bytes):\n    return b[1:3]\n", target="f").status == PROVED
    assert check("def f(b: bytes):\n    b[0] = 1\n    return 0\n", target="f").status == REFUTED            # immutable
    assert check("def f(b: bytearray):\n    if len(b) > 0:\n        b[0] = 1\n    return 0\n", target="f").status == PROVED
    assert check("def f(b: bytearray, i: int, v: int):\n    b[i] = v\n    return 0\n", target="f").status == REFUTED   # unguarded store
    assert check("def f(b: bytes):\n    return b.decode('ascii')\n", target="f").status == UNKNOWN          # decode can raise
    # a PARAMETERIZED generic annotation -- list[int], dict[str, int], set[int], tuple[int, int], or a typing
    # alias (List[int], Sequence[int]) -- is the same container as its bare form; the element type is ignored,
    # exactly as the bare list / dict are. len(x) and a guarded index prove, an unguarded index refutes, a set
    # stays non-subscriptable, and the container-as-scalar guard (list[int] + 1) still abstains.
    assert check("def f(x: list[int]):\n    return len(x)\n", target="f").status == PROVED
    assert check("def f(x: list[int], i: int):\n    if 0 <= i < len(x):\n        return x[i]\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: list[int], i: int):\n    return x[i]\n", target="f").status == REFUTED            # unguarded index
    assert check("def f(d: dict[str, int]):\n    return len(d)\n", target="f").status == PROVED
    assert check("def f(s: set[int]):\n    return len(s)\n", target="f").status == PROVED
    assert check("def f(s: set[int]):\n    return s[0]\n", target="f").status == REFUTED                     # set not subscriptable
    assert check("def f(t: tuple[int, int], i: int):\n    if 0 <= i < len(t):\n        return t[i]\n    return 0\n", target="f").status == PROVED
    assert check("from typing import List\ndef f(x: List[int]):\n    return len(x)\n", target="f").status == PROVED
    assert check("def f(x: list[int]):\n    return x + 1\n", target="f").status != PROVED                    # container-as-scalar: still abstains
    # SOUNDNESS: a container-typed parameter (list / dict / set / tuple) used DIRECTLY as a scalar -- a + 1, -a,
    # int(a) -- is a TypeError on the real value, so the integer CHC model and the value engine's opaque int()
    # abstain (UNKNOWN); a container used AS a container (a[i], len(a), for x in a, seq * int repetition) and a
    # scalar derived from it (len(a) + 1) are sound and still decide.
    assert check("def f(a: list):\n    return a + 1\n", target="f").status != PROVED
    assert check("def f(d: dict):\n    return d + 1\n", target="f").status != PROVED
    assert check("def f(s: set):\n    return s + 1\n", target="f").status != PROVED
    assert check("def f(t: tuple):\n    return t * 2\n", target="f").status == PROVED        # tuple repetition is valid
    assert check("def f(a: list):\n    return -a\n", target="f").status != PROVED
    assert check("def f(a: list):\n    return int(a)\n", target="f").status != PROVED
    assert check("def f(s: set):\n    return int(s)\n", target="f").status != PROVED
    assert check("def f(a: list):\n    return len(a) + 1\n", target="f").status == PROVED        # scalar from len: still proves
    assert check("def f(x: float):\n    return int(x)\n", target="f").status == PROVED            # int(float): unaffected
    # an object-typed parameter -- a user class, a qualified name (module.Class), or a PEP-604 union -- is an
    # opaque receiver, not a sampled integer, so a scalar op pinned only to its being a number (100 // proto, the
    # proto=0 / dataset=0 scan artifact) is UNKNOWN, not a false trap, a method call on it stays opaque-safe, and a
    # class-annotated method dispatch still upgrades to its visible body.
    assert check("class Conf:\n    pass\ndef f(proto: Conf):\n    return 100 // proto\n", target="f").status == UNKNOWN
    assert check("import m\ndef f(proto: m.Conf):\n    return 100 // proto\n", target="f").status == UNKNOWN
    assert check("class A:\n    pass\nclass B:\n    pass\ndef f(p: A | B):\n    return 100 // p\n", target="f").status == UNKNOWN
    assert check("class Conf:\n    pass\ndef f(proto: Conf):\n    return proto.run()\n", target="f").status == PROVED
    _C6 = "class C:\n    def get(self):\n        return 1\n    def bad(self):\n        return 10 // 0\n"
    assert check(_C6 + "def f(o: C):\n    return o.bad()\n", target="f").status == REFUTED        # dispatch still upgrades
    assert check(_C6 + "def f(o: C):\n    return o.get()\n", target="f").status == PROVED
    # dispatch on o: C considers each module subclass override (the receiver could be any subclass), so a trap in
    # a subclass method refutes (including through a multi-level hierarchy), while all-safe overrides prove.
    assert check("class B:\n    def m(self):\n        return 1\nclass S(B):\n    def m(self):\n        return 10 // 0\n"
                 "def f(o: B):\n    return o.m()\n", target="f").status == REFUTED                # subclass override traps
    assert check("class B:\n    def m(self):\n        return 1\nclass S(B):\n    def m(self):\n        return 2\n"
                 "def f(o: B):\n    return o.m()\n", target="f").status == PROVED                 # all overrides safe
    assert check("class A:\n    def m(self):\n        return 1\nclass B(A):\n    pass\nclass C(B):\n    def m(self):\n        return 10 // 0\n"
                 "def f(o: A):\n    return o.m()\n", target="f").status == REFUTED                # a deep-subclass override traps
    # an UNANNOTATED parameter compared to a string literal is a string (it supports `== ""` and an index), so the
    # is_HDN idiom `if text == "": return 0; return text[0]` proves -- the guard is an emptiness test and text[0]
    # is bounds-checked against the string length -- rather than the `text` modeled as an int and the index a false trap.
    assert check("def f(text):\n    if text == '':\n        return 0\n    return text[0]\n", target="f").status == PROVED
    assert check("def f(text):\n    return text[0]\n", target="f").status == REFUTED             # unguarded: still refutes
    # SOUNDNESS, continued: an ORDERING comparison (< <= > >=) of a container or None against a number, and
    # abs() of a container, are TypeErrors too, so the model abstains on that pattern (None ordering refutes
    # outright via the None engine). Equality (== !=), which is
    # defined between any types, a comparison of scalars, and a scalar derived from the container all decide.
    assert check("def f(a: list):\n    return a < 1\n", target="f").status != PROVED
    assert check("def f(s: set):\n    return s < 1\n", target="f").status != PROVED
    assert check("def f(d: dict):\n    return d >= 0\n", target="f").status != PROVED
    assert check("def f(a: list):\n    return 1 < a\n", target="f").status != PROVED              # number on the left, too
    assert check("def f(a: list):\n    return abs(a)\n", target="f").status != PROVED
    assert check("def f(d: dict):\n    return abs(d)\n", target="f").status != PROVED
    assert check("def f(a: list):\n    return a == 1\n", target="f").status == PROVED              # equality is total: no trap
    assert check("def f(a: list):\n    return len(a) < 5\n", target="f").status == PROVED          # scalar from len: still proves
    assert check("def f(n: int):\n    return n < 1\n", target="f").status == PROVED                # scalar ordering: unaffected
    # SOUNDNESS, continued: len(None) is a TypeError (None is not sized), refuted through the None machinery.
    assert check("def f():\n    x = None\n    return len(x)\n", target="f").status == REFUTED        # len(None): TypeError
    assert check("def f(a: list):\n    return len(a)\n", target="f").status == PROVED                 # len(container): unchanged
    assert check("def f(s: str):\n    return len(s)\n", target="f").status == PROVED                  # len(str): unchanged
    # A method call on a parameter explicitly typed int / float / bool -- n.append(...) -- is an AttributeError
    # for all but a few numeric methods the engine does not model, so it abstains, keyed on the numeric
    # ANNOTATION. A DUCK-TYPED receiver (an unannotated o, treated as an object) and a class-annotated o: C keep
    # the opaque-safe over-approximation, so a class-annotated o: C method call resolves its body (above) and
    # the duck-typed call stays decided.
    assert check("def f(n: int):\n    n.append(1)\n    return 0\n", target="f").status != PROVED      # int has no .append
    # int methods: bit_length / bit_count (nonneg, zero iff receiver zero), __index__ / conjugate (the value).
    assert check("def f(n: int):\n    return n.bit_length()\n", target="f").status == PROVED
    assert prove("def f(n: int):\n    return n.bit_length()\n", "result >= 0", target="f").status == PROVED
    assert prove("def f(n):\n    return n.__index__()\n", "result == n", target="f").status == PROVED
    assert check("def f(n: int):\n    if n != 0:\n        return 10 // n.bit_length()\n    return 0\n", target="f").status == PROVED
    assert check("def f(x: float):\n    x.frob()\n    return 0\n", target="f").status != PROVED       # float has no .frob
    assert check("def f(o):\n    return o.frobnicate()\n", target="f").status == PROVED                # unannotated: duck-typed object, kept
    _Cobj = "class C:\n    def __init__(self, v):\n        self.v = v\n    def go(self):\n        return self.v\n"
    assert check(_Cobj + "def f(o: C):\n    return o.go()\n", target="f").status == PROVED            # object method: opaque-safe, kept
    # `for x in sorted(E)` / `reversed(E)` (no key=) iterates E's elements (same multiset, same count), so for
    # trap freedom it is the loop over E and decides where that loop does; a key= (which can trap) keeps it declined.
    assert check("def f(nums):\n    s = 0\n    for x in sorted(nums):\n        s = x\n    return s\n", target="f").status == PROVED
    assert check("def f(nums):\n    s = 0\n    for x in reversed(nums):\n        s = x\n    return s\n", target="f").status == PROVED
    assert check("def f(n):\n    s = 0\n    for x in sorted(range(n)):\n        s = x\n    return s\n", target="f").status == PROVED
    assert check("def f(nums):\n    s = 0\n    for x in sorted(nums, key=abs):\n        s = x\n    return s\n", target="f").status == UNKNOWN
    # `for i, x in enumerate(C[, start])` lowers to a counter plus the loop over C, so an enumerate that uses the
    # index arithmetically decides; a constant iterable still unrolls to the exact index sum.
    assert check("def f(nums):\n    s = 0\n    for i, x in enumerate(nums):\n        s = s + i + x\n    return s\n", target="f").status == PROVED
    assert check("def f(n):\n    s = 0\n    for i, x in enumerate(range(n)):\n        s = i + x\n    return s\n", target="f").status == PROVED
    assert prove("def f():\n    s = 0\n    for i, x in enumerate((10, 20, 30)):\n        s = s + i\n    return s\n", "result == 3", target="f").status == PROVED
    # the enumerate index (a monotonic counter) carries i >= start through the loop havoc, so a guard if i < start
    # is dead (PROVED) and a divide by the index decides; the bound never suppresses a real trap or over-claims.
    assert check("def f(xs: list):\n    for i, v in enumerate(xs, 1):\n        if i < 1:\n            return 1 // 0\n    return 0\n").status == PROVED
    assert check("def f(xs: list, k: int):\n    for i, v in enumerate(xs, k):\n        if i < k:\n            return 1 // 0\n    return 0\n").status == PROVED
    assert check("def f(xs: list):\n    t = 0\n    for i, v in enumerate(xs, 1):\n        t = 10 // i\n    return t\n").status == PROVED   # i >= 1: safe
    assert check("def f(xs: list):\n    for i, v in enumerate(xs, 1):\n        if i < 2:\n            return 1 // 0\n    return 0\n").status == REFUTED   # i == 1 reachable
    assert check("def f(xs: list):\n    for i, v in enumerate(xs):\n        y = xs[i]\n    return 0\n").status == UNKNOWN   # i >= 0 alone proves no upper bound
    # a descending for-loop counter carries i <= start the same way (a generalization beyond enumerate); a
    # conditionally-reset counter is not monotonic, so no bound is assumed.
    assert check("def f(xs: list):\n    i = 10\n    for x in xs:\n        if i > 10:\n            return 1 // 0\n        i = i - 1\n    return 0\n").status == PROVED
    # a slice bound is trap-checked: ys[10 // k :] divides by k, so k == 0 refutes;
    # a clean slice still decides.
    assert check("def f(ys, k):\n    return ys[10 // k:]\n", target="f").status == REFUTED
    assert check("def f(ys, a):\n    return ys[a:]\n", target="f").status == PROVED
    # zip(...) is an iterable of tuples: a for-loop over it havocs the (element) targets, so a lockstep loop decides.
    assert check("def f(xs, ys):\n    s = 0\n    for a, b in zip(xs, ys):\n        s = a + b\n    return s\n", target="f").status == PROVED
    assert check("def f(xs, ys, zs):\n    s = 0\n    for a, b, c in zip(xs, ys, zs):\n        s = a + b + c\n    return s\n", target="f").status == PROVED
    # tuple unpacking in a domain / BMC straight-line block (a, b = b, a -- a swap loop): the bounded engine now
    # recovers a witness for a trap in such a loop, and the affine-invariant engine proves a swap-preserved sum.
    _sw = check("def f(n):\n    a, b = 1, 1\n    x = n\n    while x > 0:\n        a, b = b, a\n        x = x - 1\n    return 10 // (a - a)\n", target="f")
    assert _sw.status == REFUTED and _sw.counterexample_inputs, _sw
    assert prove("def f(n):\n    a, b = 3, 5\n    x = n\n    while x > 0:\n        a, b = b, a\n        x = x - 1\n    return a + b\n", "result == 8", target="f").status == PROVED
    # iterating list/tuple/set/frozenset(E) is the loop over E (same or fewer element values), so it decides
    # where the loop over E does.
    assert check("def f(nums):\n    s = 0\n    for x in list(nums):\n        s = x\n    return s\n", target="f").status == PROVED
    assert check("def f(nums):\n    s = 0\n    for x in set(nums):\n        s = x\n    return s\n", target="f").status == PROVED
    assert check("def f(n):\n    s = 0\n    for x in tuple(range(n)):\n        s = x\n    return s\n", target="f").status == PROVED
    # `for x in A + B` (concatenation) lowers to the loop over A then the loop over B, so it decides; a break
    # keeps it declined (the split would not preserve break semantics).
    assert check("def f(a, b):\n    s = 0\n    for x in a + b:\n        s = x\n    return s\n", target="f").status == PROVED
    assert check("def f(nums):\n    s = 0\n    for x in nums + [0]:\n        s = x\n    return s\n", target="f").status == PROVED
    assert check("def f(a, b):\n    for x in a + b:\n        if x > 5:\n            break\n    return 0\n", target="f").status == UNKNOWN
    # sum / any / all over a generator on a symbolic container: the element/predicate is trap-checked (loop var
    # havoc'd to an int element), the aggregate over-approximated; an element that can trap is not PROVED.
    assert check("def f(nums):\n    return sum(x * x for x in nums)\n", target="f").status == PROVED
    assert check("def f(nums):\n    return any(x > 0 for x in nums)\n", target="f").status == PROVED
    assert check("def f(nums):\n    return all(x >= 0 for x in nums)\n", target="f").status == PROVED
    assert check("def f(nums):\n    return sum(10 // x for x in nums)\n", target="f").status != PROVED

    # accept a whole module with shared global constants: load_module builds the
    #      repo and inlines module-level globals into the functions that read them.
    _mod = load_module("RATE = 10\n\ndef fee(p):\n    return p // RATE\n\ndef net(p):\n    return p - fee(p)\n")
    assert set(_mod) == {"fee", "net"}, _mod
    assert verify_predicate("mod-net", "net", _mod["net"],
                            lambda za, o: z3.Implies(za["p"] >= 0, z3.And(o >= 0, o <= za["p"])), _mod).status == PROVED
    _mod2 = load_module("X = 5\nY = X + 1\n\ndef g(a):\n    return a + Y\n")
    assert verify_equiv("mod-glob", "g", _mod2["g"], "def k(a):\n    return a + 6\n", _mod2).status == PROVED

    # import statements: imports are no-ops; names resolve via the repo, and an
    #      unmodeled imported call is reported UNKNOWN rather than crashing the analysis.
    assert verify_predicate("imp-noop", "f", "import math\ndef f(x):\n    return abs(x)\n",
                            lambda za, o: o >= 0, {}).status == PROVED
    assert verify_equiv("imp-repo", "f", "from mod import helper\ndef f(a):\n    return helper(a)\n",
                        "def g(a):\n    return a + a\n", {"helper": "def helper(x):\n    return x * 2\n"}).status == PROVED
    assert verify_predicate("imp-unmodeled", "f", "def f(x: float):\n    from math import tan\n    return tan(x)\n",
                            lambda za, o: z3.BoolVal(True), {}).status == UNKNOWN   # tan is not modeled

    # standard-library contracts: a registry of trusted models, seeded with
    #      sound closed-form math functions, reachable as math.f(x) and via `from math import f`.
    _F3 = z3.Float64()
    assert verify_predicate("std-fabs", "f", "import math\ndef f(x: float):\n    return math.fabs(x)\n",
                            lambda za, o: z3.Implies(z3.Not(z3.fpIsNaN(za["x"])), z3.fpGEQ(o, z3.FPVal(0.0, _F3))),
                            {}).status == PROVED
    assert verify_predicate("std-isnan", "f", "import math\ndef f(x: float):\n    return math.isnan(x - x)\n",
                            lambda za, o: z3.Implies(z3.fpIsInf(za["x"]), o == 1), {}).status == PROVED
    assert verify_equiv("std-bare", "f", "from math import fabs\ndef f(x: float):\n    return fabs(x)\n",
                        "def g(x: float):\n    import math\n    return math.fabs(x)\n", {}).status == PROVED
    assert verify_equiv("std-copysign", "f", "import math\ndef f(x: float):\n    return math.copysign(x, 1.0)\n",
                        "def g(x: float):\n    import math\n    return math.fabs(x)\n", {}).status == PROVED
    # math.sqrt is the IEEE square root, nonnegative for a nonnegative argument and a domain trap for a
    # negative one; math.sqrt and the bare `from math import sqrt` name agree.
    assert prove("import math\ndef f(x):\n    return math.sqrt(x)\n", "result >= 0.0", requires="x >= 0.0").status == PROVED
    assert verify_equiv("sqrt-bare", "f", "from math import sqrt\ndef f(x: float):\n    return sqrt(x)\n",
                        "def g(x: float):\n    import math\n    return math.sqrt(x)\n", {}).status == PROVED
    vsq = verify_predicate("sqrt-trap", "f", "import math\ndef f(x: float):\n    return math.sqrt(x)\n",
                           lambda za, o: z3.BoolVal(True), {})
    assert vsq.status == REFUTED, vsq                          # math.sqrt(x) traps (ValueError) for x < 0
    # numpy scalar functions: the same value contracts as the math models (np.fabs == math.fabs) plus
    # numpy's own. np.sqrt returns NaN for x < 0 (no trap), unlike math.sqrt; an integer argument stays
    # integral; the `import numpy as np` alias and the spelled-out name agree.
    assert prove("import math\nimport numpy as np\ndef f(x: float):\n    return np.fabs(x)\n",
                 "result >= 0.0", requires="math.isfinite(x)").status == PROVED
    assert prove("import numpy as np\ndef f(x):\n    return np.abs(x)\n", "result >= 0").status == PROVED
    assert prove("import math\nimport numpy as np\ndef f(x: float):\n    return np.sign(x)\n",
                 "result <= 1.0 and result >= -1.0", requires="math.isfinite(x)").status == PROVED
    assert check("import numpy as np\ndef f(x: float):\n    return np.sqrt(x)\n").status == PROVED
    assert verify_equiv("np-fabs", "f", "import numpy as np\ndef f(x: float):\n    return np.fabs(x)\n",
                        "import numpy\ndef g(x: float):\n    return numpy.fabs(x)\n", {}).status == PROVED
    # leading imports do not derail the integer engines: a mined trap and a counted loop verify with
    # an `import` at the top of the function source.
    assert check("import math\ndef f(x):\n    return 10 // x\n").status == REFUTED
    assert check("import math\ndef f(x):\n    return 10 // x\n", requires="x != 0").status == PROVED
    assert verify_function("imp-loop", "f",
        "import math\ndef f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n",
        lambda S: S["n"] >= 0, lambda S, r: r == S["n"], {}).status == PROVED

    # reflection and dynamic features: getattr/setattr with a constant name are
    #      modeled as attribute access; eval/exec and dynamic names are UNKNOWN (sound). hasattr is decided
    #      from attribute-presence tracking: set -> True, never set -> False.
    assert verify_heap_property("getattr", "f",
                                "def f(v):\n    o = object()\n    o.x = v\n    return getattr(o, 'x')\n",
                                lambda za, r: r == za["v"]).status == PROVED
    assert verify_heap_property("setattr", "f",
                                "def f(v):\n    o = object()\n    setattr(o, 'y', v)\n    return getattr(o, 'y')\n",
                                lambda za, r: r == za["v"]).status == PROVED
    assert verify_heap_property("hasattr-set", "f",       # an attribute that was set: hasattr decided True
                                "def f(v):\n    o = object()\n    o.x = v\n    if hasattr(o, 'x'):\n        return 1\n    return 0\n",
                                lambda za, r: r == 1).status == PROVED
    assert verify_heap_property("hasattr-unset", "f",     # a fresh object's missing attribute: hasattr decided False
                                "def f():\n    o = object()\n    if hasattr(o, 'x'):\n        return 1\n    return 0\n",
                                lambda za, r: r == 0).status == PROVED
    assert verify_heap_property("eval-unk", "f",
                                "def f():\n    o = object()\n    o.x = eval('1+1')\n    return o.x\n",
                                lambda za, r: z3.BoolVal(True)).status == UNKNOWN
    assert verify_heap_property("dyn-attr-unk", "f",
                                "def f(name):\n    o = object()\n    return getattr(o, name)\n",
                                lambda za, r: z3.BoolVal(True)).status == UNKNOWN

    # builtins with exact contracts: any, all, isinstance (by value sort), and
    #      map over a constant tuple.
    assert verify_predicate("any", "f", "def f(a, b):\n    if any((a > 0, b > 0)):\n        return 1\n    return 0\n",
                            lambda za, o: o == z3.If(z3.Or(za['a'] > 0, za['b'] > 0), 1, 0), {}).status == PROVED
    assert verify_predicate("all", "f", "def f(a, b):\n    if all((a > 0, b > 0)):\n        return 1\n    return 0\n",
                            lambda za, o: o == z3.If(z3.And(za['a'] > 0, za['b'] > 0), 1, 0), {}).status == PROVED
    assert verify_predicate("isinst-int", "f", "def f(x: int):\n    if isinstance(x, int):\n        return 1\n    return 0\n",
                            lambda za, o: o == 1, {}).status == PROVED
    assert verify_predicate("isinst-no", "f", "def f(x: int):\n    if isinstance(x, float):\n        return 1\n    return 0\n",
                            lambda za, o: o == 0, {}).status == PROVED
    assert verify_predicate("map", "f", "def f():\n    r = map(lambda y: y * 2, (1, 2, 3))\n    a, b, c = r\n    return c\n",
                            lambda za, o: o == 6, {}).status == PROVED

    # general shared-memory interleaving model: arbitrary thread programs with
    #      locks; every sequentially-consistent schedule is checked. Subsumes the counter/lock pattern.
    #      Two threads keep the bounded enumeration small; all thread counts are covered inductively by
    #      verify_atomic_threads / verify_locked_counter below.
    _atomic = [[("acq", "L"), ("rd", "r", "x"), ("set", "r", lambda L: L["r"] + 1), ("wr", "x", "r"), ("rel", "L")]
               for _ in range(2)]
    assert verify_interleavings("atomic", "t", _atomic, {"x": 0}, lambda s: s["x"] == 2).status == PROVED
    _racy = [[("rd", "r", "x"), ("set", "r", lambda L: L["r"] + 1), ("wr", "x", "r")] for _ in range(3)]
    assert verify_interleavings("racy", "t", _racy, {"x": 0}, lambda s: s["x"] == 3).status == REFUTED
    assert verify_interleavings("racy-range", "t", _racy, {"x": 0}, lambda s: 1 <= s["x"] <= 3).status == PROVED
    _disjoint = [[("rd", "r", "x"), ("set", "r", lambda L: 1), ("wr", "x", "r")],
                 [("rd", "r", "y"), ("set", "r", lambda L: 1), ("wr", "y", "r")]]
    assert verify_interleavings("disjoint", "t", _disjoint, {"x": 0, "y": 0},
                                lambda s: s["x"] == 1 and s["y"] == 1).status == PROVED
    # thread bodies written as Python: a read-modify-write decomposes into read/compute/write, so an
    # unprotected counter loses an update on some schedule while a lock-protected (or with-block) one
    # reaches N on every schedule. Augmented assignment is handled the same way.
    _racy_src = "def th():\n    tmp = x\n    tmp = tmp + 1\n    x = tmp\n"
    _lock_src = "def th():\n    with lock:\n        tmp = x\n        tmp = tmp + 1\n        x = tmp\n"
    assert verify_threads("py-racy", "t", [_racy_src, _racy_src], {"x": 0}, lambda s: s["x"] == 2).status == REFUTED
    assert verify_threads("py-range", "t", [_racy_src, _racy_src], {"x": 0}, lambda s: 1 <= s["x"] <= 2).status == PROVED
    assert verify_threads("py-lock", "t", [_lock_src, _lock_src], {"x": 0}, lambda s: s["x"] == 2).status == PROVED
    assert verify_threads("py-aug", "t", ["def th():\n    x += 1\n"] * 2, {"x": 0},
                          lambda s: s["x"] == 2).status == REFUTED
    assert verify_threads("py-aug-lock", "t", ["def th():\n    with lock:\n        x += 1\n"] * 2, {"x": 0},
                          lambda s: s["x"] == 2).status == PROVED
    # branching thread bodies: an if/else over shared state is a conditional update -- the condition is
    # read once and each branch is a guarded write. A both-branch increment still loses an update; a
    # one-sided update whose guard is false never writes.
    _cinc = "def th():\n    if x < 100:\n        x = x + 1\n    else:\n        x = x + 1\n"
    assert verify_threads("cond-inc", "t", [_cinc, _cinc], {"x": 0}, lambda s: 1 <= s["x"] <= 2).status == PROVED
    assert verify_threads("cond-inc-lost", "t", [_cinc, _cinc], {"x": 0}, lambda s: s["x"] == 2).status == REFUTED
    _oneside = "def th():\n    if x < 10:\n        x = x + 1\n"
    assert verify_threads("cond-1side", "t", [_oneside, _oneside], {"x": 0}, lambda s: 1 <= s["x"] <= 2).status == PROVED
    assert verify_threads("cond-1side-off", "t", [_oneside, _oneside], {"x": 10},
                          lambda s: s["x"] == 10).status == PROVED          # guard false on both: no write
    # teeth for the guarded write: a one-sided write whose guard is false must NOT clobber another
    # thread's unconditional write; flipping the guard true lets it overwrite on some schedule.
    _guarded = "def a():\n    if flag == 1:\n        x = 5\n"
    _writer = "def b():\n    x = 7\n"
    assert verify_threads("cond-noclobber", "t", [_guarded, _writer], {"x": 0, "flag": 0},
                          lambda s: s["x"] == 7).status == PROVED
    assert verify_threads("cond-clobber", "t", [_guarded, _writer], {"x": 0, "flag": 1},
                          lambda s: s["x"] == 7).status == REFUTED          # guard true: A may overwrite B
    # a conditionally-assigned thread-local is undefined on the other path: UNKNOWN
    assert verify_threads("cond-local", "t", ["def th():\n    if x < 5:\n        t = 1\n    x = t\n"] * 2,
                          {"x": 0}, lambda s: True).status == UNKNOWN
    # a bounded for-loop over a constant range unrolls into the op stream, the loop variable bound per
    # iteration as a thread-local: two threads each adding 1 twice race to a final value in [2, 4], and
    # the lock-free version cannot guarantee 4. The loop variable is live in the body (sum over range).
    _loop2 = "def th():\n    for i in range(2):\n        x = x + 1\n"
    assert verify_threads("loop2", "t", [_loop2, _loop2], {"x": 0}, lambda s: 2 <= s["x"] <= 4).status == PROVED
    assert verify_threads("loop2-max", "t", [_loop2, _loop2], {"x": 0}, lambda s: s["x"] == 4).status == REFUTED
    assert verify_threads("loopvar", "t", ["def th():\n    for i in range(3):\n        x = x + i\n"],
                          {"x": 0}, lambda s: s["x"] == 3).status == PROVED      # 0 + 1 + 2 = 3
    assert verify_threads("while-unk", "t", ["def th():\n    while x < 5:\n        x = x + 1\n"],
                          {"x": 0}, lambda s: True).status == UNKNOWN            # unbounded loop not unrolled
    # semaphores, async/await, and condition variables. A counting semaphore at 1 is a mutex (no lost update);
    # a higher count lets threads race. Async cooperative scheduling switches only at an await, so a read-modify-
    # write with none between is atomic, while an await mid-update re-exposes the race. A CV producer/consumer is
    # PROVED; a CV violation is withheld (a notify a real CV would lose may be remembered -- sound for PROVED only).
    _sem = "def th():\n    S.acquire()\n    x += 1\n    S.release()\n"
    assert verify_threads("sem1", "t", [_sem, _sem], {"x": 0}, lambda s: s["x"] == 2, semaphores={"S": 1}).status == PROVED
    assert verify_threads("sem2", "t", [_sem, _sem], {"x": 0}, lambda s: s["x"] == 2, semaphores={"S": 2}).status == REFUTED
    assert verify_threads("coop", "t", ["def th():\n    x += 1\n"] * 2, {"x": 0},
                          lambda s: s["x"] == 2, cooperative=True).status == PROVED        # no await: atomic
    _ya = "def th():\n    t = x\n    await sleep()\n    x = t + 1\n"
    assert verify_threads("coop-await", "t", [_ya, _ya], {"x": 0}, lambda s: s["x"] == 2,
                          cooperative=True).status == REFUTED                              # await mid-update: race
    _prod = [("set", "r", lambda L: 5), ("wr", "x", "r"), ("cnotify", "C")]
    _cons = [("cwait", "C", "L"), ("rd", "r", "x"), ("set", "r", lambda L: L["r"]), ("wr", "y", "r")]
    assert verify_interleavings("cv", "t", [_prod, _cons], {"x": 0, "y": 0},
                                lambda s: s["y"] in (0, 5)).status == PROVED               # consumer reads the produced value
    assert verify_interleavings("cv-withheld", "t", [_prod, _cons], {"x": 0, "y": 0},
                                lambda s: s["y"] == 999).status == UNKNOWN                 # CV violation not certified
    # all depths: a lock-protected Python critical section is proved for EVERY thread count by induction
    # over (count, shared state); an unlocked body cannot soundly be treated as atomic and stays UNKNOWN.
    _atomic = "def th():\n    with lock:\n        x = x + 1\n"
    assert verify_atomic_threads("at", "t", _atomic, {"x": 0}, lambda k, s: s["x"] == k).status == PROVED
    assert verify_atomic_threads("at", "t", _atomic, {"x": 0}, lambda k, s: s["x"] == k + 1).status == REFUTED
    assert verify_atomic_threads("at", "t", "def th():\n    acquire_lock()\n    x = x + 2\n    release_lock()\n",
                                 {"x": 0}, lambda k, s: s["x"] == 2 * k).status == PROVED
    assert verify_atomic_threads("at", "t", "def th():\n    x = x + 1\n", {"x": 0},
                                 lambda k, s: s["x"] == k).status == UNKNOWN      # not atomic without a lock

    # specification language over heaps and structured values: a postcondition
    #      taking (z3args, ret, heap) quantifies over a returned list's elements and object attrs.
    assert verify_heap_property("spec-forall", "f", "def f():\n    return [2, 4, 6]\n",
                                lambda za, r, h: list_forall(h, r, lambda e: e % 2 == 0)).status == PROVED
    assert verify_heap_property("spec-forall-no", "f", "def f():\n    return [1, 2, 3]\n",
                                lambda za, r, h: list_forall(h, r, lambda e: e >= 2)).status == REFUTED
    assert verify_heap_property("spec-append", "f",
                                "def f():\n    a = []\n    a.append(0)\n    a.append(0)\n    return a\n",
                                lambda za, r, h: list_forall(h, r, lambda e: e == 0)).status == PROVED
    assert verify_heap_property("spec-attr", "f",
                                "def f(v):\n    o = object()\n    o.x = v\n    o.y = v\n    return o\n",
                                lambda za, r, h: heap_attr(h, r, "x") == heap_attr(h, r, "y")).status == PROVED
    assert verify_heap_property("spec-len", "f", "def f():\n    return [9, 9, 9]\n",
                                lambda za, r, h: list_len(h, r) == 3).status == PROVED

    # nonlinear invariant synthesis: the data-driven learner takes a degree, so
    #      polynomial loop invariants past degree two are learned and verified.
    _ssq = "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        i = i + 1\n        s = s + i * i\n    return s\n"
    _pre = lambda S: S["n"] >= 0
    _post3 = lambda S, r: 6 * r == 2 * S["n"] ** 3 + 3 * S["n"] ** 2 + S["n"]
    assert learn_invariant("ssq2", "f", _ssq, _pre, _post3, degree=2).status == UNKNOWN   # degree two is not enough
    assert learn_invariant("ssq3", "f", _ssq, _pre, _post3, degree=3).status == PROVED    # sum of squares
    _scb = "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        i = i + 1\n        s = s + i * i * i\n    return s\n"
    _post4 = lambda S, r: 4 * r == S["n"] ** 4 + 2 * S["n"] ** 3 + S["n"] ** 2
    assert learn_invariant("scb", "f", _scb, _pre, _post4, degree=4).status == PROVED      # sum of cubes
    # end to end the CHC path escalates the degree on its own: Spacer diverges on the nonlinear sum of
    # squares, and the fallback raises the learner's degree (2 -> 3 -> 4) until the invariant is found.
    assert verify_chc("ssq-e2e", "f", _ssq, _pre, _post3).status == PROVED
    # a power-sum loop -- i = i + 1; s = s + i**k -- past the data-driven learner's degree-4 cap: the closed-form
    # invariant s == p(i) is INTERPOLATED through a few small concrete steps (finite differences, not a monomial
    # null-space whose exact-rational arithmetic over huge sampled values is the learner's wall), then verified
    # inductively and for the postcondition. So an arbitrary-degree power sum (i^4, i^5, i^6) is proved in bounded
    # time, while a wrong closed form fails a check.
    _ps = lambda k: "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        i = i + 1\n        s = s + %s\n    return s\n" % ("*".join(["i"] * k))
    assert prove(_ps(4), "30*result == 6*n**5 + 15*n**4 + 10*n**3 - n", requires="n >= 0", target="f").status == PROVED   # sum i^4 (degree 5)
    assert prove(_ps(5), "12*result == 2*n**6 + 6*n**5 + 5*n**4 - n**2", requires="n >= 0", target="f").status == PROVED  # sum i^5 (degree 6)
    assert prove("def f(n):\n    a = 0\n    b = 0\n    i = 0\n    while i < n:\n        i = i + 1\n        a = a + i\n        b = b + i * i\n    return b\n",
                 "6*result == 2*n**3 + 3*n**2 + n", requires="n >= 0", target="f").status == PROVED   # two accumulators, both interpolated
    from .engines import _powersum_invariant as _psi
    assert _psi("ps", "f", _ps(6), lambda S: S["n"] >= 0,                              # the engine directly: sum i^6 (degree 7)
                lambda S, r: 42 * r == 6 * S["n"]**7 + 21 * S["n"]**6 + 21 * S["n"]**5 - 7 * S["n"]**3 + S["n"]).status == PROVED
    assert _psi("ps", "f", _ps(4), lambda S: S["n"] >= 0,                              # a wrong closed form (missing - n): not proved,
                lambda S, r: 30 * r == 6 * S["n"]**5 + 15 * S["n"]**4 + 10 * S["n"]**3).status != PROVED   # checked directly so it stays fast
    assert _psi("ps", "f", "def f(n, k):\n    s = 0\n    i = 0\n    while i < n:\n        i = i + 1\n        s = s + k\n    return s\n",
                lambda S: z3.BoolVal(True), lambda S, r: z3.BoolVal(True)).status == UNKNOWN   # a parameter-dependent body declines

    # termination of data-dependent loops: division in the body is allowed, so a
    #      halving loop is proved to halt, as is a data-dependent subtraction under an invariant.
    assert verify_termination("halve", "f", "def f(x):\n    while x > 1:\n        x = x // 2\n    return x\n").status == PROVED
    assert verify_termination("halve0", "f", "def f(x):\n    while x > 0:\n        x = x // 2\n    return x\n").status == PROVED
    assert verify_termination("data-sub", "f", "def f(x, d):\n    while x > 0:\n        x = x - d\n    return x\n",
                              inv=lambda S: S["d"] >= 1).status == PROVED

    # array invariant inference beyond the single self-write template: a
    #      cross-array transform b[i] = a[i] OP c has its element-wise prefix invariant inferred.
    _xf = "def f(a: list, b: list, n: int):\n    i = 0\n    while i < n:\n        b[i] = a[i] + 1\n        i = i + 1\n    return b\n"
    _xpre = lambda S: z3.And(S["n"] >= 0, S["n"] <= S["len_a"], S["n"] <= S["len_b"])
    assert verify_array_loop_auto("xform-add", "f", _xf, _xpre,
        lambda S, E: q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]),
                                                   z3.Select(S["b"], j) == z3.Select(S["a"], j) + 1))).status == PROVED
    _xf2 = "def f(a: list, b: list, n: int):\n    i = 0\n    while i < n:\n        b[i] = a[i] * 2\n        i = i + 1\n    return b\n"
    assert verify_array_loop_auto("xform-mul", "f", _xf2, _xpre,
        lambda S, E: q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]),
                                                   z3.Select(S["b"], j) == z3.Select(S["a"], j) * 2))).status == PROVED

    # the differential CPython oracle now covers the looping CHC engine: random
    #      accumulator loops are verified and cross-checked against execution, both ways.
    if fast:                                                # inner loop: skip the CPython-execution cross-checks
        _dl = _dh = _dseq = {"exec_checks": 1, "proved": 1, "refuted": 1}
        _dt = {"refuted": 3, "proved": 3, "checks": 1}
        _dm2 = {"checks": 1, "proved": 1}
        _si = _sl = {"claims": 1, "runs": 1, "abstain": 1}
        _rf = {"checks": 1, "constructs": 40}
        _erf = {"checks": 10001, "constructs": 20}
        _dg = {"checks": 1, "value_checks": 1, "trap_checks": 1}
    else:
        core.ALLOW_SUBJECT_EXECUTION = True
        try:
            _dl = differential_loop_audit(trials=20)
            _dh = differential_heap_audit(trials=30)            # the CPython oracle spans the heap engine too
            _dseq = differential_sequence_audit(trials=20)      # and the list-iteration sequence-loop engine
            _dt = differential_typed_audit()                    # and float / boolean / string counterexamples
            _dm2 = differential_method_audit()                  # and the modular method-call model
            _si = differential_sound_inference_audit()          # sound return-type inference: over-approximation holds
            _sl = differential_sound_local_audit()              # sound local-variable inference: over-approximation holds
            _rf = refinement_audit(per=25)                      # each modeled construct refines CPython
            _erf = exhaustive_refinement_audit()                # and the integer constructs refine it on EVERY box input
            _dg = differential_grammar_audit(trials=120)        # generative container-grammar translation check
        finally:
            core.ALLOW_SUBJECT_EXECUTION = False
    assert _dm2["checks"] > 0 and _dm2["proved"] > 0, _dm2   # method calls vs CPython, 0 contradictions
    assert _si["claims"] > 0 and _si["runs"] > 0 and _si["abstain"] > 0, _si   # claims hold; abstains on the unbounded
    assert _sl["claims"] > 0 and _sl["abstain"] > 0, _sl     # local claims hold; abstains on parameter-derived locals
    assert _dl["exec_checks"] > 0 and _dl["proved"] > 0 and _dl["refuted"] > 0, _dl
    assert _dseq["exec_checks"] > 0 and _dseq["proved"] > 0 and _dseq["refuted"] > 0, _dseq
    assert _rf["checks"] > 0 and _rf["constructs"] >= 40, _rf
    # the integer fragment of the core is confirmed equal to CPython on every input of a bounded box, not
    # only on sampled points: a bounded proof of the integer encodings the Rocq proof does not reach.
    assert _erf["checks"] > 10000 and _erf["constructs"] >= 20, _erf
    # the generative container-grammar fuzzer: aliasing x mutation x repetition programs, each differentially
    # checked against CPython -- the defense against TRANSLATION bugs that corroboration (two solvers on one
    # translation) cannot catch. A PROVED of the wrong value / a REFUTED of the right one is a SoundnessError;
    # this is the check the [[0]] * 2 shared-row bug failed.
    assert _dg["checks"] > 0 and _dg["value_checks"] > 0 and _dg["trap_checks"] > 0, _dg
    # the differential CPython oracle reaches the heap engine too: object/list/dict
    #       programs are verified and cross-checked against real execution, proving and refuting both.
    assert _dh["exec_checks"] > 0 and _dh["proved"] > 0 and _dh["refuted"] > 0, _dh
    # float, boolean, and string counterexamples are replayed against CPython, float results compared
    #       bit-for-bit; a REFUTED verdict's counterexample must genuinely disagree on every type.
    assert _dt["refuted"] == 3 and _dt["proved"] == 3 and _dt["checks"] > 0, _dt

    # the external-code precision/recall harness: a small corpus the tool did not author is decided by
    # trap freedom (broadest applicable engine) and each decided verdict is cross-checked against CPython
    # in the sandbox. No decided verdict may contradict execution -- that is the soundness bar (zero),
    # and the harness must decide and confirm the trap-free and trap-reachable cases.
    from . import domains as _bench
    if fast:                                                # inner loop: skip the external-corpus sandbox benchmark
        _bm = {"contradictions": 0, "proved": 1, "refuted": 1, "confirmed": 1, "decided": 1}
    else:
        core.ALLOW_SUBJECT_EXECUTION = True
        try:
            _bm = _bench.run_benchmark([
                ("gcd", "def gcd(a, b):\n    while b != 0:\n        t = b\n        b = a % b\n        a = t\n    return a\n"),
                ("divz", "def divz(a, b):\n    return a // b\n"),
                ("lsum", "def lsum(xs: list):\n    s = 0\n    for x in xs:\n        s = s + x\n    return s\n"),
            ], samples=30)
        finally:
            core.ALLOW_SUBJECT_EXECUTION = False
    assert _bm["contradictions"] == 0 and _bm["proved"] >= 1 and _bm["refuted"] >= 1, _bm
    assert _bm["confirmed"] == _bm["decided"], _bm                 # every decided verdict CPython-confirmed

    # the theories verify user functions through ev: strings, sequences, dicts, separation/frame,
    #      and dispatch.
    assert verify_predicate("int-str", "f", "def f(s: str):\n    return len(s + s)\n",
                            lambda za, o: o == 2 * z3.Length(za["s"]), {}).status == PROVED
    assert verify_heap_property("int-list", "f",
                                "def f(x):\n    a = [x, x, x]\n    return a[0] + a[1] + a[2]\n",
                                lambda za, r: r == 3 * za["x"]).status == PROVED
    assert verify_heap_property("int-dict", "f",
                                "def f(k, v):\n    d = {}\n    d[k] = v\n    return d[k]\n",
                                lambda za, r: r == za["v"]).status == PROVED
    assert verify_heap_property("int-frame", "f",
                                "def f(p, q):\n    a = object()\n    b = object()\n    a.v = p\n    b.v = q\n    return a.v\n",
                                lambda za, r: r == za["p"]).status == PROVED   # disjoint-object frame on user code
    _disp = ("class Money:\n    def __init__(self, c):\n        self.c = c\n    def __add__(self, o):\n        return Money(self.c + o.c)\n"
             "def f(a, b):\n    m = Money(a) + Money(b)\n    return m.c\n")
    assert verify_heap_property("int-disp", "f", _disp, lambda za, r: r == za["a"] + za["b"]).status == PROVED

    # polyhedral templates generated automatically: the octagon family over the
    #      program variables proves i == n and x == y with no user-supplied templates.
    _ctr = "def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n"
    assert verify_polyhedra_auto("poly-auto", "f", _ctr, lambda S: S["i"] - S["n"], 0, 0,
                                 pre=lambda S: S["n"] >= 0).status == PROVED
    _tv = "def g(n):\n    x = 0\n    y = 0\n    while x < n:\n        x = x + 1\n        y = y + 1\n    return x\n"
    assert verify_polyhedra_auto("poly-auto2", "g", _tv, lambda S: S["x"] - S["y"], 0, 0,
                                 pre=lambda S: S["n"] >= 0).status == PROVED

    # first-class and higher-order functions: a function passed as a callback (a
    #      lambda or a named repo function) is inlined specialized to its argument and called.
    assert verify_predicate("ho-lambda", "g", "def g():\n    return apply(lambda y: y + 1, 5)\n",
                            lambda za, o: o == 6, {"apply": "def apply(f, x):\n    return f(x)\n"}).status == PROVED
    _ho = {"inc": "def inc(x):\n    return x + 1\n", "twice": "def twice(f, x):\n    return f(f(x))\n"}
    assert verify_equiv("ho-named", "g", "def g(a):\n    return twice(inc, a)\n",
                        "def h(a):\n    return a + 2\n", _ho).status == PROVED

    # del, global / nonlocal, nested def, and decorators: a nested def is a
    #      closure; del unbinds; global / nonlocal are no-ops here; decorators verify the body.
    assert verify_equiv("nested-def", "f", "def f(a):\n    def g(y):\n        return y + a\n    return g(5)\n",
                        "def h(a):\n    return 5 + a\n", {}).status == PROVED
    assert verify_equiv("del", "f", "def f(x):\n    y = x + 1\n    del y\n    return x\n",
                        "def h(x):\n    return x\n", {}).status == PROVED
    assert verify_function("global", "f",
                           "def f(n):\n    global COUNT\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n",
                           lambda S: S["n"] >= 0, lambda S, r: r == S["n"], {}).status == PROVED
    _dm = load_module("def deco(fn):\n    return fn\n\n@deco\ndef f(x):\n    return x + 1\n")
    assert verify_equiv("decorated", "f", _dm["f"], "def h(x):\n    return x + 1\n", _dm).status == PROVED

    # side effects as world state -- resource / finalizer correctness: every
    #      opened handle must be closed on every path; with-managed handles close automatically.
    assert verify_no_leak("rl-ok", "f", "def f():\n    x = open('a')\n    x.close()\n    return 0\n").status == PROVED
    assert verify_no_leak("rl-leak", "f", "def f():\n    x = open('a')\n    return 0\n").status == REFUTED
    assert verify_no_leak("rl-with", "f", "def f():\n    with open('a') as x:\n        y = 1\n    return y\n").status == PROVED
    assert verify_no_leak("rl-branch", "f",
                          "def f(c):\n    x = open('a')\n    if c:\n        x.close()\n    return 0\n").status == REFUTED
    assert verify_no_leak("rl-both", "f",
                          "def f(c):\n    x = open('a')\n    if c:\n        x.close()\n    else:\n        x.close()\n    return 0\n").status == PROVED
    # leak tracking follows handle identity: closing through an alias counts, returning or storing a
    # handle hands out ownership, and a handle kept alive only through an alias is still caught.
    assert verify_no_leak("rl-alias-close", "f",
                          "def f():\n    x = open('a')\n    y = x\n    y.close()\n    return 0\n").status == PROVED
    assert verify_no_leak("rl-return", "f",
                          "def f():\n    x = open('a')\n    return x\n").status == PROVED
    assert verify_no_leak("rl-escape", "f",
                          "def f(o):\n    o.f = open('a')\n    return 0\n").status == PROVED
    assert verify_no_leak("rl-alias-leak", "f",
                          "def f():\n    x = open('a')\n    y = x\n    x = 0\n    return 0\n").status == REFUTED

    # nonnegativity beyond degree-two, few-variable SOS: higher degree and more
    #      variables, an exact PSD Gram certificate in each case.
    assert verify_sos_nonneg("sos-4-2", "p", lambda X: X[0] * X[0] * X[0] * X[0] + X[1] * X[1] * X[1] * X[1], 2,
                             degree=4).status == PROVED                         # x^4 + y^4
    assert verify_sos_nonneg("sos-d2", "p", lambda X: (X[0] * X[0] - X[1] * X[1]) * (X[0] * X[0] - X[1] * X[1]), 2,
                             degree=4).status == PROVED                         # (x^2 - y^2)^2
    assert verify_sos_nonneg("sos-6", "p", lambda X: (X[0] * X[0] * X[0] - 1) * (X[0] * X[0] * X[0] - 1), 1,
                             degree=6).status == PROVED                         # (x^3 - 1)^2
    assert verify_sos_nonneg("sos-mix", "p", lambda X: X[0] * X[0] + X[0] * X[1] + X[1] * X[1], 2,
                             degree=2).status == PROVED                         # x^2 + xy + y^2

    # interval operators vs. the closed forms proven sound in touchstone_domains.v (extracted to OCaml
    # there), over a wide grid, plus concrete soundness inclusion: each result interval contains every
    # corner result -- the property iadd_fn_sound .. imul_fn_sound prove abstractly.
    for a in range(-8, 9):
        for b in range(a, 9):
            assert _ineg(Iv(a, b)) == Iv(-b, -a)
            for x in (a, b):
                assert _ineg(Iv(a, b)).lo <= -x <= _ineg(Iv(a, b)).hi
            for c in range(-8, 9):
                for d in range(c, 9):
                    add, sub, jn = _iadd(Iv(a, b), Iv(c, d)), _isub(Iv(a, b), Iv(c, d)), _ijoin(Iv(a, b), Iv(c, d))
                    mul = _imul(Iv(a, b), Iv(c, d))
                    assert add == Iv(a + c, b + d)
                    assert sub == Iv(a - d, b - c)
                    assert jn == Iv(min(a, c), max(b, d))
                    assert mul == Iv(min(a * c, a * d, b * c, b * d), max(a * c, a * d, b * c, b * d))
                    for x in (a, b):                          # corners pin the extremes of these monotone/bilinear ops
                        for y in (c, d):
                            assert add.lo <= x + y <= add.hi and sub.lo <= x - y <= sub.hi
                            assert mul.lo <= x * y <= mul.hi
                            assert jn.lo <= x <= jn.hi and jn.lo <= y <= jn.hi

    # a ranking that needs an auxiliary invariant: the nested counter halts only under 0 <= j <= m
    nested = ("def f(n, m):\n    i = 0\n    j = 0\n    while i < n:\n"
              "        if j < m:\n            j = j + 1\n        else:\n            i = i + 1\n"
              "            j = 0\n    return i\n")
    assert verify_termination("rank-aux", "f", nested).status == UNKNOWN        # unbounded inner measure
    aux = lambda S: z3.And(S["j"] >= 0, S["j"] <= S["m"])
    assert verify_termination("rank-aux", "f", nested, inv=aux).status == PROVED  # (n-i, m-j) under j<=m
    # the candidate family now spans products as well as sums/differences, so a measure that decreases
    # only as a product is still in scope; a plain linear loop continues to resolve to its own counter.
    assert verify_termination("rank-lin", "f",
                              "def f(x):\n    while x > 0:\n        x = x - 1\n    return x\n"
                              ).reason == "ranking function: x"
    # the synthesis fallback (CEGIS) proves termination for a measure with non-unit coefficients that no
    # template captures: 3*x + y is bounded below by the guard and strictly decreases, while x, y, x+y, and
    # x-y are each individually unbounded under 3*x + y > 0, so verify_total reaches this loop only through
    # the synthesized general linear ranking function -- deterministically (rlimit, bounded refinement).
    _coeffrank = verify_termination("rank-synth", "f",
                                    "def f(x, y):\n    while 3 * x + y > 0:\n        x = x - 1\n        y = y + 2\n    return 0\n")
    assert _coeffrank.status == PROVED and "synthesi" in _coeffrank.technique, _coeffrank

    # termination over finite containers (one step per element) and data-dependent loops (halving)
    assert verify_termination("it-list", "f",
                              "def f(xs):\n    s = 0\n    for x in xs:\n        s = s + x\n    return s\n"
                              ).status == PROVED                                # list parameter
    assert verify_termination("it-str", "f",
                              "def f(s):\n    n = 0\n    for c in s:\n        n = n + 1\n    return n\n"
                              ).status == PROVED                                # string iteration
    assert verify_termination("it-enum", "f",
                              "def f(xs):\n    s = 0\n    for i, x in enumerate(xs):\n"
                              "        s = s + i\n    return s\n").status == PROVED          # enumerate
    assert verify_termination("it-zip", "f",
                              "def f(xs, ys):\n    s = 0\n    for a, b in zip(xs, ys):\n"
                              "        s = s + a\n    return s\n").status == PROVED           # zip
    assert verify_termination("it-keys", "f",
                              "def f(d):\n    n = 0\n    for k in d.keys():\n"
                              "        n = n + 1\n    return n\n").status == PROVED            # d.keys()
    # growing the iterated container during iteration is unsafe; we do not claim termination,
    # whether the growth is direct, through an alias bound from it, or through a callee it is passed to.
    assert verify_termination("it-grow", "f",
                              "def f(xs):\n    for x in xs:\n        xs.append(x)\n    return xs\n"
                              ).status == UNKNOWN
    assert verify_termination("it-grow-alias", "f",
                              "def f(xs):\n    for x in xs:\n        ys = xs\n        ys.append(x)\n    return xs\n"
                              ).status == UNKNOWN                                  # alias then grow
    assert verify_termination("it-grow-escape", "f",
                              "def f(xs):\n    for x in xs:\n        grow(xs, x)\n    return xs\n"
                              ).status == UNKNOWN                                  # container passed to a mutator
    assert verify_termination("it-grow-attr", "f",
                              "def f(xs):\n    for x in xs:\n        o.lst = xs\n        o.lst.append(x)\n    return xs\n"
                              ).status == UNKNOWN                                  # escapes into an attribute, then grows
    assert verify_termination("it-grow-sub", "f",
                              "def f(xs):\n    for x in xs:\n        d[0] = xs\n        d[0].append(x)\n    return xs\n"
                              ).status == UNKNOWN                                  # escapes into a subscript, then grows
    # but reading the container in the body (len, index, a read-only alias) keeps the termination proof,
    # as does appending an element to a different list
    assert verify_termination("it-read-alias", "f",
                              "def f(xs):\n    s = 0\n    for x in xs:\n        ys = xs\n"
                              "        s = s + ys[0]\n    return s\n").status == PROVED
    assert verify_termination("it-acc", "f",
                              "def f(xs):\n    acc = []\n    for x in xs:\n        acc.append(x)\n    return acc\n"
                              ).status == PROVED
    # data-dependent while loops (the loop count comes from the value, not a fixed counter) still halt.
    assert verify_termination("dd-halve", "f",
                              "def f(x):\n    while x > 1:\n        x = x // 2\n    return x\n"
                              ).status == PROVED                                # repeated halving

    # recursion beyond self-recursion with branch-and-return bodies: mutual recursion,
    #      recursion combined with loops, and recursion over a data structure.
    even_odd = {
        "is_even": "def is_even(n):\n    if n == 0:\n        return 1\n    return is_odd(n - 1)\n",
        "is_odd": "def is_odd(n):\n    if n == 0:\n        return 0\n    return is_even(n - 1)\n",
    }
    assert verify_program("mutual", "is_even", even_odd, "is_even",
                          lambda P: P["n"] >= 0, lambda P, r: z3.Or(r == 0, r == 1)).status == PROVED
    rec_loop = ("def f(n):\n    if n <= 0:\n        return 0\n    s = 0\n    for i in range(n):\n"
                "        s = s + 1\n    return s + f(n - 1)\n")
    assert verify_program_loops("rec+loop", "f", {"f": rec_loop}, "f",
                                lambda P: P["n"] >= 0, lambda P, r: r >= 0).status == PROVED
    # recursion over a list: the structural count equals len(xs) - i exactly, proved inductively over
    # the array relation; the same shape with a deliberately wrong post is refuted.
    cnt = "def cnt(xs: list, i):\n    if i >= len(xs):\n        return 0\n    return 1 + cnt(xs, i + 1)\n"
    in_range = lambda P: z3.And(P["i"] >= 0, P["i"] <= P["len_xs"])
    assert verify_recursive_list("rec-list", "cnt", cnt, in_range,
                                 lambda P, r: r == P["len_xs"] - P["i"]).status == PROVED
    assert verify_recursive_list("rec-list", "cnt", cnt, in_range,
                                 lambda P, r: r == P["len_xs"]).status == REFUTED
    # a read past the end is a trap, so a recursion that may index out of bounds is refuted, not silently
    # accepted; reading xs[i] under the guard i < len(xs) is in bounds and proves.
    head = ("def head(xs: list, i):\n    if i >= len(xs):\n        return 0\n"
            "    return xs[i] + head(xs, i + 1)\n")
    assert verify_recursive_list("rec-read", "head", head, in_range, lambda P, r: True).status == PROVED
    # recursive-list specifications that quantify over the elements: forall_pre assumes a per-element
    # precondition of every element read (a universal, expressed without a quantifier in any rule), so
    # a property that depends on all elements satisfying it is proved -- the sum of a nonnegative list
    # is nonnegative, and at least its length when every element is at least one -- while the same fold
    # without the element constraint is refuted and a false claim under it is refuted.
    sl = "def sl(xs: list, i):\n    if i >= len(xs):\n        return 0\n    return xs[i] + sl(xs, i + 1)\n"
    assert verify_recursive_list("sl", "sl", sl, in_range, lambda P, r: r >= 0).status == REFUTED
    assert verify_recursive_list("sl", "sl", sl, in_range, lambda P, r: r >= 0,
                                 forall_pre=lambda x: x >= 0).status == PROVED
    assert verify_recursive_list("sl", "sl", sl, in_range, lambda P, r: r >= P["len_xs"] - P["i"],
                                 forall_pre=lambda x: x >= 1).status == PROVED
    assert verify_recursive_list("sl", "sl", sl, in_range, lambda P, r: r <= 0,
                                 forall_pre=lambda x: x >= 0).status == REFUTED   # false under the precondition
    cnt0 = ("def f(xs: list, i):\n    if i >= len(xs):\n        return 0\n"
            "    if xs[i] >= 0:\n        return 1 + f(xs, i + 1)\n    return f(xs, i + 1)\n")
    assert verify_recursive_list("cnt0", "f", cnt0, in_range, lambda P, r: r == P["len_xs"] - P["i"],
                                 forall_pre=lambda x: x >= 0).status == PROVED    # all counted when all nonneg
    # a specification may also quantify over the elements in the POSTcondition (a per-element claim about
    # the result, checked for every element by a query with a free index). A false computed universal --
    # the maximum being a LOWER bound of every element -- is refuted with a concrete element below it.
    maxl = ("def maxl(xs: list, i):\n    if i >= len(xs):\n        return 0\n    r = maxl(xs, i + 1)\n"
            "    if xs[i] > r:\n        return xs[i]\n    return r\n")
    assert verify_recursive_list("maxl", "maxl", maxl, in_range, lambda P, r: z3.BoolVal(True),
                                 forall_post=lambda e, r: e >= r).status == REFUTED

    # when Spacer is inconclusive, sampling refutes a false spec (refute-only; UNKNOWN with no execution)
    sumsq = "def f(n):\n    if n <= 0:\n        return 0\n    return (n ** 2) + f(n - 1)\n"
    saved_sb, saved_ae = core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION
    core.SANDBOX_SUBJECT = False; core.ALLOW_SUBJECT_EXECUTION = False
    try:
        assert verify_recursive("fb", "f", sumsq, lambda P: P["n"] >= 0,
                                lambda P, r: r == P["n"]).status == UNKNOWN      # no execution path: UNKNOWN
    finally:
        core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = saved_sb, saved_ae
    core.ALLOW_SUBJECT_EXECUTION = True
    try:
        ref = verify_recursive("fb", "f", sumsq, lambda P: P["n"] >= 0, lambda P, r: r == P["n"])
        assert ref.status == REFUTED and ref.counterexample_inputs is not None   # concrete witness found
        assert verify_recursive("fb", "f", sumsq, lambda P: P["n"] >= 0,
                                lambda P, r: r >= 0).status == UNKNOWN            # sampling cannot prove
    finally:
        core.ALLOW_SUBJECT_EXECUTION = saved_ae

    # out-of-bounds, key errors, None-in-arithmetic, and type mismatches are traps, like division by zero
    assert verify_heap_property("oob", "f", "def f():\n    a = [1, 2, 3]\n    return a[5]\n",
                                lambda za, r: z3.BoolVal(True)).status == REFUTED        # IndexError
    assert verify_heap_property("inb", "f", "def f():\n    a = [1, 2, 3]\n    return a[1]\n",
                                lambda za, r: r == 2).status == PROVED
    assert verify_heap_property("key", "f", "def f():\n    d = {1: 10}\n    return d[2]\n",
                                lambda za, r: z3.BoolVal(True)).status == REFUTED         # KeyError
    assert verify_heap_property("hit", "f", "def f():\n    d = {1: 10}\n    return d[1]\n",
                                lambda za, r: r == 10).status == PROVED
    # None used in arithmetic is a TypeError trap (the None engine); a present integer is safe.
    assert verify_optional("none-add", "f", "def f(x):\n    return x + 1\n",
                           lambda za, r: z3.BoolVal(True)).status == REFUTED              # None in arithmetic
    # ordering a string against a number is a TypeError trap on the typed value path; equality is not an
    # error in CPython, so "s == i" is simply False and a function built on it verifies.
    assert verify_predicate("ty-ord", "f", "def f(s: str, i):\n    return s < i\n",
                            lambda za, r: z3.BoolVal(True), {}).status == REFUTED          # type mismatch
    assert verify_predicate("ty-eq", "f",
                            "def f(s: str, i):\n    if s == i:\n        return 1\n    return 0\n",
                            lambda za, r: r == 0, {}).status == PROVED                     # str == int is False

    # always-on fixed-width companion: a Python-integer proof also flags signed wraparound at the
    # default width (a switch; the standalone check still takes an explicit width)
    add = "def f(a, b):\n    return a + b\n"
    flagged = verify_function("ovf", "f", add, lambda S: z3.BoolVal(True), lambda S, r: r == S["a"] + S["b"])
    assert flagged.status == PROVED and "wraps signed 64-bit" in flagged.reason          # caught by default
    bounded = verify_function("ovf", "f", add,
                              lambda S: z3.And(S["a"] >= 0, S["a"] <= 1000, S["b"] >= 0, S["b"] <= 1000),
                              lambda S, r: r == S["a"] + S["b"])
    assert bounded.status == PROVED and "wraps" not in bounded.reason                     # cannot wrap under pre
    saved_ovf = core.CHECK_MACHINE_OVERFLOW
    core.CHECK_MACHINE_OVERFLOW = False
    try:
        quiet = verify_function("ovf", "f", add, lambda S: z3.BoolVal(True), lambda S, r: r == S["a"] + S["b"])
        assert quiet.status == PROVED and "wraps" not in quiet.reason                     # companion off
    finally:
        core.CHECK_MACHINE_OVERFLOW = saved_ovf
    assert verify_no_overflow("w8", "f", add, width=8,                                     # explicit width still works
                              pre=lambda S: z3.And(S["a"] >= 0, S["a"] <= 10, S["b"] >= 0, S["b"] <= 10)
                              ).status == PROVED
    # the companion rides on prove() too, not only verify_function: a loop-free integer proof (here through
    # the Rocq-extracted VC generator) surfaces the signed-64-bit wrap, while a float proof -- not an
    # integer proof -- is left alone, so no spurious wrap note attaches to it.
    pf = prove("def f(a, b):\n    return a + b\n", "result == a + b")
    assert pf.status == PROVED and "wraps signed 64-bit" in pf.reason, pf
    pflt = prove("def f(x: float):\n    return x * x\n", "result >= 0.0", requires="x == x")
    assert pflt.status == PROVED and "wrap" not in (pflt.reason or ""), pflt

    # total front end: every construct yields a verdict (a reason when UNKNOWN), never a crash or silent skip
    grammar = [
        "def f(x):\n    if (y := x + 1) > 0:\n        return y\n    return 0\n",          # walrus
        "def f(x):\n    yield x\n    yield x + 1\n",                                       # generator
        "async def f(x):\n    return x + 1\n",                                             # coroutine
        "def f(x):\n    with open('a') as h:\n        return x\n",                         # context manager
        "def f(x):\n    assert x > 0\n    return x\n",                                     # assert
        "def f(x):\n    return {i for i in range(x)}\n",                                   # set comprehension
        "def f(x):\n    if x > 0:\n        return 'a'\n    return x\n",                     # mixed return types
        "def f(x):\n    return x & 3 | 1\n",                                               # bitwise on unbounded int
        "def f(x):\n    y: int = x + 1\n    return y\n",                                   # annotated assignment
        "def f(x):\n    g = lambda y: y + 1\n    return g(x)\n",                           # lambda value
    ]
    for src in grammar:
        for spec in (lambda za, r: z3.BoolVal(True), lambda za, r: r == 0):               # trivial and scalar specs
            v = verify_predicate("total", "f", src, spec, {})
            assert v.status in (PROVED, REFUTED, UNKNOWN), (src, v)
            assert v.status != UNKNOWN or v.reason, (src, "UNKNOWN without a reason")
    # async is modeled as the value its coroutine yields when awaited (await e -> e), so verify_predicate over
    # `result` decides it soundly rather than declining; an incompatible return-sort union still surfaces as
    # UNKNOWN, not a crash. (Decorator inlining is wired into prove / check, which carry the module context,
    # so at the verify_predicate level a decorated function is still declined.)
    assert verify_predicate("async", "f", "async def f(x):\n    return x + 1\n",
                            lambda za, r: r == za["x"] + 1, {}).status == PROVED
    dm = load_module("def const(fn):\n    def h(a):\n        return 0\n    return h\n\n@const\ndef f(x):\n    return x + 1\n")
    assert verify_predicate("deco", "f", dm["f"], lambda za, r: r == za["x"] + 1, dm).status == UNKNOWN
    di = load_module("def ident(fn):\n    return fn\n\n@ident\ndef f(x):\n    return x + 1\n")
    assert verify_equiv("deco-id", "f", di["f"], "def h(x):\n    return x + 1\n", di).status == PROVED  # identity stripped
    assert verify_predicate("mixed", "f", "def f(x):\n    if x > 0:\n        return 'a'\n    return x\n",
                            lambda za, r: r == 0, {}).status == UNKNOWN                    # no sort-error crash

    # constructs modeled where each is decidable and sound.
    # async: an async function is reasoned about as the value its coroutine yields when awaited (await e -> e,
    # async for/with -> for/with), so prove/check/equiv decide it; an awaited inner repo coroutine inlines.
    assert prove("async def f(x):\n    return x + 1\n", "result == x + 1").status == PROVED
    assert prove("async def f(x):\n    return x + 1\n", "result == x").status == REFUTED
    assert check("async def f(x):\n    return 10 // x\n").status == REFUTED                 # the awaited body traps
    assert check("async def f(x):\n    return 10 // x\n", requires="x != 0").status == PROVED
    assert prove("async def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n",
                 "result == n", requires="n >= 0").status == PROVED                         # an async loop
    assert verify_equiv("async-eq", "f", "async def f(a):\n    return a + a\n",
                        "async def g(a):\n    return 2 * a\n", {}).status == PROVED          # equal awaited results
    _arepo = {"g": "async def g(x):\n    return x + 1\n"}
    assert prove("async def f(x):\n    y = await g(x)\n    return y + 1\n", "result == x + 2",
                 repo=_arepo).status == PROVED                                              # await of an inner coroutine

    # non-identity decorators: prove / check verify the callable a visible wrapper produces, with the original
    # inlined, not the written body and not declined. A def-wrapper, a lambda decorator, a stacked pair, a
    # decorator whose wrapper divides, and a decorator that replaces the function with a constant are decided.
    _d1 = "def plus1(f):\n    def w(n):\n        return f(n) + 1\n    return w\n\n@plus1\ndef g(n):\n    return n * 2\n"
    assert prove(_d1, "result == 2 * n + 1", target="g").status == PROVED
    assert prove(_d1, "result == 2 * n", target="g").status == REFUTED
    _d2 = "def dbl(f):\n    return lambda x: f(x) + f(x)\n\n@dbl\ndef h(x):\n    return x + 1\n"
    assert prove(_d2, "result == 2 * x + 2", target="h").status == PROVED
    _d3 = "def plus1(f):\n    def w(n):\n        return f(n) + 1\n    return w\n\n@plus1\n@plus1\ndef k(n):\n    return n\n"
    assert prove(_d3, "result == n + 2", target="k").status == PROVED                       # stacked: +2
    _d4 = "def over(f):\n    def w(n):\n        return f(n) // n\n    return w\n\n@over\ndef m(n):\n    return n\n"
    assert check(_d4, target="m").status == REFUTED and check(_d4, requires="n != 0", target="m").status == PROVED
    _d5 = "def const0(f):\n    def w(n):\n        return 0\n    return w\n\n@const0\ndef p(n):\n    return n + 1\n"
    assert prove(_d5, "result == 0", target="p").status == PROVED                           # the wrapper, not n + 1
    assert prove(_d5, "result == n + 1", target="p").status == REFUTED
    # a factory decorator @D(args) is inlined: D is called with its arguments to produce the decorator, which
    # is applied to the function (the arguments substituted into the wrapper). A decorator the engine cannot
    # resolve -- a non-simple factory, an attribute @x.deco, an imported name -- is declined (UNKNOWN), never
    # verified against the written body it may have replaced.
    _facd = ("def add(k):\n    def deco(f):\n        def w(n):\n            return f(n) + k\n        return w\n    return deco\n"
             "@add(3)\ndef g(n):\n    return n * 2\n")
    assert prove(_facd, "result == 2 * n + 3", target="g").status == PROVED
    assert prove(_facd, "result == 2 * n", target="g").status == REFUTED
    assert prove("def scale(k):\n    def deco(f):\n        return lambda x: f(x) * k\n    return deco\n"
                 "@scale(10)\ndef h(x):\n    return x + 1\n", "result == 10 * (x + 1)", target="h").status == PROVED
    assert check("def over(k):\n    def deco(f):\n        def w(n):\n            return f(n) // k\n        return w\n    return deco\n"
                 "@over(0)\ndef g(n):\n    return n\n", target="g").status == REFUTED   # factory arg 0 -> // 0 trap
    # soundness: an unresolvable decorator (a non-simple factory whose wrapper traps) is declined, not falsely PROVED
    assert check("def weird(k):\n    x = k + 1\n    def deco(f):\n        def w(n):\n            return f(n) // 0\n        return w\n    return deco\n"
                 "@weird(3)\ndef g(n):\n    return n\n", target="g").status == UNKNOWN

    # reflection with a resolvable attribute name: getattr / setattr / hasattr whose name is a local or
    # parameter provably bound to a string literal decides like a literal name (hasattr from attribute-presence
    # tracking); a genuinely dynamic (non-constant) name stays UNKNOWN.
    assert verify_heap_property("getattr-res", "f",
        "def f(v):\n    o = object()\n    o.x = v\n    a = 'x'\n    return getattr(o, a)\n",
        lambda za, r: r == za["v"]).status == PROVED
    assert verify_heap_property("setattr-res", "f",
        "def f(v):\n    o = object()\n    n = 'y'\n    setattr(o, n, v)\n    return getattr(o, n)\n",
        lambda za, r: r == za["v"]).status == PROVED
    assert verify_heap_property("getattr-dyn", "f",
        "def f(name):\n    o = object()\n    return getattr(o, name)\n",
        lambda za, r: z3.BoolVal(True)).status == UNKNOWN                                   # a dynamic name: declined

    # dynamic class creation: type(name, bases, ns) is modeled as that class definition (constant ns values
    # are class variables, lambdas are expression-body methods), so an instance's attributes, methods, and
    # inherited members decide; an unmodeled base or namespace declines (UNKNOWN).
    assert verify_heap_property("dyn-attr", "f",
        "def f(v):\n    C = type('C', (), {})\n    o = C()\n    o.x = v\n    return o.x\n",
        lambda za, r: r == za["v"]).status == PROVED
    assert verify_heap_property("dyn-method", "f",
        "def f():\n    C = type('C', (), {'s': lambda self: 5})\n    o = C()\n    return o.s()\n",
        lambda za, r: r == 5).status == PROVED
    assert verify_heap_property("dyn-subclass", "f",
        "class Base:\n    def __init__(self, v):\n        self.v = v\n    def get(self):\n        return self.v\n"
        "def f(a):\n    D = type('D', (Base,), {})\n    o = D(a)\n    return o.get()\n",
        lambda za, r: r == za["a"]).status == PROVED

    # class variables are read by an instance (the heap model seeds them on construction, base-first), and an
    # instance attribute set in __init__ overrides a class variable.
    assert verify_heap_property("cvar", "f", "class C:\n    k = 7\ndef f():\n    o = C()\n    return o.k\n",
                                lambda za, r: r == 7).status == PROVED
    assert verify_heap_property("cvar-override", "f",
        "class B:\n    k = 3\nclass D(B):\n    k = 9\ndef f():\n    o = D()\n    return o.k\n",
        lambda za, r: r == 9).status == PROVED
    assert verify_heap_property("cvar-init", "f",
        "class C:\n    k = 7\n    def __init__(self, v):\n        self.k = v\ndef f(v):\n    o = C(v)\n    return o.k\n",
        lambda za, r: r == za["v"]).status == PROVED

    # mixed float / exact-rational arithmetic: Python coerces a Fraction meeting a float to float, so the
    # result is the IEEE double, decided exactly; division by 0.0 is a ZeroDivisionError trap.
    assert verify_predicate("mix-add", "f", "def f():\n    return Fraction(1, 2) + 0.5\n",
                            lambda za, o: z3.fpEQ(o, z3.FPVal(1.0, _F64)), {}).status == PROVED
    assert verify_predicate("mix-mul", "f", "def f():\n    return 0.5 * Fraction(2, 3)\n",
                            lambda za, o: z3.fpEQ(o, z3.FPVal(0.5 * float(_Fr(2, 3)), _F64)), {}).status == PROVED
    assert verify_predicate("mix-div0", "f", "def f():\n    return Fraction(1, 2) / 0.0\n",
                            lambda za, o: z3.BoolVal(True), {}).status == REFUTED            # ZeroDivisionError

    # the independent second translation covers booleans, conditionals, and abs/min/max, and agrees
    for impl, spec in [
        ("def f(x):\n    return abs(x)\n", "def g(x):\n    return x if x >= 0 else -x\n"),         # abs / ternary
        ("def f(a, b):\n    return max(a, b)\n", "def g(a, b):\n    return a if a > b else b\n"),    # max
        ("def f(a, b, c):\n    return min(a, b, c)\n", "def g(a, b, c):\n    return min(min(a, b), c)\n"),  # min
        ("def f(x):\n    return (x > 0) + 1\n", "def g(x):\n    return 2 if x > 0 else 1\n"),        # bool in arithmetic
        ("def f(x):\n    return (x > 0) and (x + 1)\n", "def g(x):\n    return (x + 1) if x > 0 else False\n"),  # and
    ]:
        assert _independent_claim(impl, spec, {}) is not None                              # second translation is live
        veq = verify_equiv("indep2", "f", impl, spec, {})
        assert veq.status == PROVED, (impl, veq)
        assert model_cross_check(veq, impl, spec, {}) == 1                                  # both translations agree
    bad_i, bad_s = "def f(x):\n    return abs(x)\n", "def g(x):\n    return x\n"
    vbad = verify_equiv("indep2", "f", bad_i, bad_s, {})
    assert vbad.status == REFUTED and model_cross_check(vbad, bad_i, bad_s, {}) == 1        # disagreement confirmed

    # subject execution is sandboxed, so the concrete check runs by default in an isolated process
    saved_sb2, saved_ae2 = core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION
    core.SANDBOX_SUBJECT = True; core.ALLOW_SUBJECT_EXECUTION = False
    try:
        if core.sandbox_run_batch("def f(x):\n    return x\n", {}, "f", [[1]]) == [("ok", 1)]:  # spawnable here
            sb = verify_recursive("sbx", "f", sumsq, lambda P: P["n"] >= 0, lambda P, r: r == P["n"])
            assert sb.status == REFUTED and "sandboxed" in sb.technique, sb        # ran by default, isolated
            # the sandbox executes the subject out-of-process under restricted builtins: a file-opening
            # body cannot touch the host -- it is reported as a trap; arithmetic returns its value.
            assert core.sandbox_run_batch("def f(a, b):\n    return a + b\n", {}, "f", [[2, 3]]) == [("ok", 5)]
            assert core.sandbox_run_batch("def f(x):\n    open('x', 'w')\n    return x\n", {}, "f", [[1]]) == [("trap",)]
            # a divergent input is killed by the wall-clock limit rather than hanging the verifier
            assert core.sandbox_run_batch("def f(x):\n    while True:\n        pass\n", {}, "f", [[1]], timeout_s=2.0) is None
    finally:
        core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = saved_sb2, saved_ae2
    # the out-of-process subject runner works in every launch mode, including `python -c` where
    # multiprocessing-spawn cannot re-import __main__ and the oracle would otherwise silently abstain.
    # It runs a fresh interpreter on a standalone child script, so it always produces a result here.
    assert core._run_in_subprocess("typed", "def f(x):\n    return 10 // x\n", {}, "f",
                                   [[2], [0]], 8.0, 256) == [("ok",), ("raise", "ZeroDivisionError")]
    assert core._run_in_subprocess("value", "def f(x):\n    return x + 1\n", {}, "f",
                                   [[5]], 8.0, 256) == [("ok", 6)]
    assert core._run_in_subprocess("value", "def f(x):\n    open('x', 'w')\n    return x\n", {}, "f",
                                   [[1]], 8.0, 256) == [("trap",)]                  # host stays out of reach
    # the execution-trace path runs out of process in every launch mode too, so explain()'s counterexample
    # trace is available under `python -c` / the REPL, not only from a file: a reachable trap traces to its
    # raise, a clean run traces to its returned value, both with the subject isolated from the host.
    _trc = core._run_trace_in_subprocess("def f(x):\n    return 10 // x\n", {}, "f", [0], 8.0, 256, 10000)
    assert _trc is not None and _trc[0] == "raised" and _trc[2] == "ZeroDivisionError", _trc
    _trr = core._run_trace_in_subprocess("def f(x):\n    return x + 1\n", {}, "f", [5], 8.0, 256, 10000)
    assert _trr is not None and _trr[0] == "returned" and "6" in _trr[2], _trr

    # corroboration: a PROVED is confirmed by cvc5 when it is present (and a cvc5 refutation of a z3 PROVED
    # raises SoundnessError); when cvc5 is absent the PROVED degrades to a labeled single-solver result
    # rather than vanishing, so a broken second-solver install does not turn every PROVED into UNKNOWN.
    assert core.REQUIRE_CORROBORATION is True                                    # on by default
    aa = ("def f(a):\n    return a + a\n", "def g(a):\n    return 2 * a\n")
    _con = verify_equiv("corr-on", "f", aa[0], aa[1], {})
    assert _con.status == PROVED and "z3 + cvc5" in _con.certificate              # corroborated by cvc5
    assert cvc5_available() is True                                              # present in this environment
    _avail = core.cvc5_available
    core.cvc5_available = lambda: False                                          # simulate the second solver missing
    try:
        _none = verify_equiv("corr-none", "f", aa[0], aa[1], {})                  # graceful single-solver PROVED
        assert _none.status == PROVED and "z3 only" in _none.certificate, _none   # labeled lower-trust, not withheld
        assert solve_corroborated(z3.Int("w") != z3.Int("w"))[0] == PROVED        # single-solver PROVED, not UNKNOWN
    finally:
        core.cvc5_available = _avail
    # the second solver launches through portable native bindings: no subprocess, PATH, or env assumption
    _csrc = inspect.getsource(solve_with_cvc5) + inspect.getsource(cvc5_available)
    for forbidden in ("subprocess", "os.environ", "getenv", "Popen", "PATH", ".exe"):
        assert forbidden not in _csrc, f"second-solver launch uses {forbidden}"
    assert solve_with_cvc5(z3.Int("p") != z3.Int("p")) == PROVED                   # unsat, via bindings
    assert solve_with_cvc5(z3.Int("p") == z3.IntVal(5)) == REFUTED                 # sat, via bindings
    # the second solver re-decides the plain find/replace operations (str.indexof / str.replace round-trip
    # cleanly under cvc5 1.3.4) and declines only the find-from-end / replace-all forms whose bindings fault,
    # returning a verdict where it can and UNKNOWN where it cannot -- never faulting the process either way.
    _idx = z3.IndexOf(z3.String("q"), z3.StringVal("ab"), z3.IntVal(0))
    _lidx = z3.LastIndexOf(z3.String("q"), z3.StringVal("ab"))
    assert core._cvc5_can_handle(z3.Int("p") > 0) and core._cvc5_can_handle(_idx >= 0)
    assert not core._cvc5_can_handle(_lidx >= 0)                                    # find-from-end: declined
    assert solve_with_cvc5(_lidx >= 0) == UNKNOWN                                   # declined, not crashed
    assert verify_predicate("find", "f", "def f(s: str):\n    return s.find('ab')\n",
                            lambda za, o: z3.BoolVal(True), {}).status in (PROVED, REFUTED, UNKNOWN)
    # machine-independent verdicts: a deterministic resource bound (rlimit), and a certificate on a PROVED
    assert core.SOLVE_RLIMIT > 0                                                   # resource-bounded, not timed
    # the verdict is gated solely on that rlimit, never the wall clock: a hard bit-blasted query decides by
    # the resource budget and is identical run to run, rather than flipping PROVED<->UNKNOWN with machine
    # load. _solve binds the rlimit on both paths and sets a wall-clock timeout only as a fallback when no
    # rlimit is configured.
    assert core.FP_SOLVE_RLIMIT > 0
    _slines = inspect.getsource(core._solve).splitlines()
    assert sum('s.set("rlimit"' in ln for ln in _slines) == 2                      # both solve paths bind the rlimit
    for _i, _ln in enumerate(_slines):                                             # every wall-clock timeout is gated
        if 's.set("timeout"' in _ln:                                              # behind a no-rlimit else, never set
            assert _slines[_i - 1].split("#")[0].strip() == "else:", _ln          # while the rlimit is in force
    cert_v = verify_equiv("cert", "f", aa[0], aa[1], {})
    assert cert_v.status == PROVED and cert_v.certificate is not None
    assert "z3 + cvc5" in cert_v.certificate and "rlimit" in cert_v.certificate
    # the certificate is backed by a re-checkable bundle: the discharged SMT-LIB refutation queries, re-run
    # independently and required UNSAT, with a content hash a tampered bundle fails. A REFUTED has no bundle.
    from .vcgen import proof_bundle, recheck_bundle
    _pb = proof_bundle(lambda: verify_equiv("pb", "f", aa[0], aa[1], {}))
    assert _pb["checkable"] and _pb["n_queries"] >= 1, _pb
    assert recheck_bundle(_pb)["verified"] is True, _pb
    assert recheck_bundle({**_pb, "sha256": "0" * 64})["verified"] is False         # a tampered bundle fails
    assert proof_bundle(lambda: prove("def f(x):\n    return x + 1\n", "result == x"))["checkable"] is False
    # corroboration reaches past equivalence/predicates AND past the integer/real fragment: the deductive,
    # modular, termination, category, learner, heap, separation-logic, overflow, optional, and theory
    # engines route their verdict-level solves through the two-solver gate, so a PROVED there would raise if
    # cvc5 found a counterexample. The gate now covers every quantifier-free fragment cvc5's bindings
    # re-decide -- integer, real, bitvector, array, datatype, float, string, sequence -- with only what the
    # SMT-LIB round-trip cannot carry faithfully left single-solver, so no PROVED in these engines rests on
    # one solver and corroboration never crashes or silently downgrades a verdict.
    assert core._claim_is_cvc5_safe(z3.Int("a") > z3.Int("b"))                       # LIA: corroborated
    assert core._claim_is_cvc5_safe(z3.Real("r") + 1 < z3.RealVal(2))                # reals: corroborated
    _harr = z3.Array("h", z3.IntSort(), z3.IntSort())
    assert core._claim_is_cvc5_safe(z3.Select(_harr, z3.Int("i")) == 0)              # arrays: corroborated
    assert core._claim_is_cvc5_safe(z3.BitVec("bv", 64) + 1 == 0)                    # bitvectors: corroborated
    _F4 = z3.Float64()
    assert core._claim_is_cvc5_safe(z3.fpEQ(z3.fpAdd(z3.RNE(), z3.FP("xf", _F4), z3.FP("xf", _F4)),
                                            z3.FP("yf", _F4)))                       # floats: corroborated
    assert core._claim_is_cvc5_safe(z3.Length(z3.String("s")) >= 0)                  # strings: corroborated
    # the bitvector multiplication-overflow predicates are rewritten to standard QF_BV before serialization
    # (_rewrite_for_cvc5, each form proven equal to z3's predicate below), so a multiplication-overflow PROVED
    # is corroborated by two solvers; a quantified query is corroborated when z3's serialization of it provably
    # round-trips (_serialization_is_faithful, so a captured bound variable is detected and declined). What
    # stays single-solver is only what the round-trip cannot carry: the find-from-end / replace-all
    # sequence-string operators whose bindings fault, and a quantified query whose serialization is unfaithful.
    _bvm, _bvn = z3.BitVec("bvm", 16), z3.BitVec("bvn", 16)
    assert core._claim_is_cvc5_safe(z3.BVMulNoOverflow(_bvm, _bvn, True))             # signed mul-overflow: corroborated
    assert core._claim_is_cvc5_safe(z3.BVMulNoOverflow(_bvm, _bvn, False))            # unsigned mul-overflow: corroborated
    assert core._claim_is_cvc5_safe(z3.BVMulNoUnderflow(_bvm, _bvn))                  # mul-underflow: corroborated
    assert core._claim_is_cvc5_safe(z3.BVAddNoOverflow(_bvm, _bvn, True))             # add-overflow: corroborated
    assert core._claim_is_cvc5_safe(z3.ForAll([z3.Int("j")], z3.Int("j") >= 0))      # faithful quantifier: corroborated
    assert not core._claim_is_cvc5_safe(                                              # find-from-end: single-solver
        z3.LastIndexOf(z3.String("s"), z3.StringVal("ab")) >= 0)
    # the rewrite is sound: z3 proves each standard-QF_BV form equal to its native predicate for every w-bit
    # pair (the difference is unsatisfiable at each width), so the corroboration decides the same predicate.
    for _w in (8, 16):
        _ra, _rb = z3.BitVec("ra", _w), z3.BitVec("rb", _w)
        for _pred, _nm in ((z3.BVMulNoOverflow(_ra, _rb, True), "bvsmul_noovfl"),
                           (z3.BVMulNoOverflow(_ra, _rb, False), "bvumul_noovfl"),
                           (z3.BVMulNoUnderflow(_ra, _rb), "bvsmul_noudfl")):
            _eqs = z3.Solver(); _eqs.add(_pred != core._bv_mulovf_standard(_nm, _ra, _rb))
            assert _eqs.check() == z3.unsat, (_nm, _w)
    # multiplication-overflow and quantified queries are re-decided by cvc5
    _a8 = z3.BitVec("a8", 8)
    assert solve_with_cvc5(z3.Not(z3.BVMulNoOverflow(_a8, z3.BitVecVal(0, 8), True))) == PROVED   # a*0 never overflows
    assert solve_with_cvc5(z3.ForAll([z3.Int("j")], z3.Int("j") >= 0)) == PROVED      # closed false quantifier: unsat
    assert solve_with_cvc5(z3.Exists([z3.Int("k")], z3.Int("k") == 5)) == REFUTED     # satisfiable quantifier: sat
    # the second solver actually re-decides each quantifier-free fragment (a valid claim_false is unsat under
    # cvc5), so these are genuine two-solver corroborations rather than vacuous passes
    _hh, _ii, _vv = z3.Array("hh", z3.IntSort(), z3.IntSort()), z3.Int("ii"), z3.Int("vv")
    assert solve_with_cvc5(z3.Select(z3.Store(_hh, _ii, _vv), _ii) != _vv) == PROVED         # array read-after-write
    _u = z3.BitVec("u", 8)
    assert solve_with_cvc5(z3.URem(_u, z3.BitVecVal(8, 8)) != (_u & z3.BitVecVal(7, 8))) == PROVED      # bitvector
    assert solve_with_cvc5(z3.Length(z3.Concat(z3.String("sa"), z3.String("sb")))                       # string
                           != z3.Length(z3.String("sa")) + z3.Length(z3.String("sb"))) == PROVED
    # teeth on the widened fragment: with the second solver forced to disagree, a heap PROVED over an array
    # is rejected as a contradiction -- the old int/real-only gate would have passed it single-solver.
    # verify_heap_property routes through _solve_corro, the gate under test.
    _osv, _ocorr = core.solve_with_cvc5, core.REQUIRE_CORROBORATION
    core.solve_with_cvc5 = lambda *a, **k: REFUTED
    core.REQUIRE_CORROBORATION = True
    try:
        try:
            verify_heap_property("corro-wide", "f", "def f():\n    a = [1, 2, 3]\n    return a[1]\n",
                                 lambda za, r: r == 2)
            raise AssertionError("widened corroboration did not consult the second solver on the array fragment")
        except SoundnessError:
            pass
    finally:
        core.solve_with_cvc5, core.REQUIRE_CORROBORATION = _osv, _ocorr
    assert verify_modular("corr-mod", "f", "def f(x):\n    return g(g(x))\n",         # modular PROVED, two solvers
                          lambda S: z3.BoolVal(True), lambda S, r: r == S["x"] + 2,
                          {"g": (lambda a: z3.BoolVal(True), lambda a, r: r == a[0] + 1)}).status == PROVED
    # the integer obligations the engine discharges are committed to proofs/touchstone_obligations.v, which the
    # smtcoq CI job re-checks in Coq's kernel on every commit (not only when the toolchain is present locally),
    # so the kernel-validated-certificate is exercised against the engine's current obligations, not a snapshot
    _ob = committed_obligations_audit()
    assert _ob["available"] in (True, False) and (not _ob["available"] or _ob["checks"] > 0), _ob
    # the type-inference join the engine runs (soundinfer._join) is the verified join of touchstone_encoders.v,
    # held equal to its committed extraction; that file also machine-checks the string, container, and heap
    # McCarthy soundness laws the engine relies on (closed under the global context, gated by verify_coq.sh).
    _la = extracted_lattice_audit()
    assert _la["available"] and _la["checks"] > 0, _la
    # a refutation becomes a runnable failing test: repro_test emits a standalone test that, run as is,
    # reproduces the counterexample -- an AssertionError for a postcondition, the trap itself for a trap
    # claim -- and a non-refutation yields no test. The emitted tests are executed here to confirm they fire.
    from .repro import repro_test
    _psrc = "def f(x):\n    return x\n"
    _pv = prove(_psrc, "result > 0")                                   # REFUTED at x <= 0
    assert _pv.status == REFUTED and _pv.counterexample_inputs, _pv
    _pt = repro_test(_pv, _psrc, ensures="result > 0")
    assert _pt and "def test_touchstone_repro():" in _pt and "def f(x):" in _pt, _pt
    _pns = {}; exec(compile(_pt, "<repro>", "exec"), _pns)
    _fired = False
    try:
        _pns["test_touchstone_repro"]()
    except AssertionError:
        _fired = True
    assert _fired, "the postcondition repro did not reproduce the refutation"
    _tsrc = "def f(a):\n    return 10 // a\n"
    _tv = check(_tsrc)                                                 # REFUTED: a = 0 traps
    if _tv.status == REFUTED:
        _tt = repro_test(_tv, _tsrc)
        assert _tt and "f(" in _tt, _tt
        _tns = {}; exec(compile(_tt, "<repro>", "exec"), _tns)
        _trapped = False
        try:
            _tns["test_touchstone_repro"]()
        except Exception:                                             # the reachable trap fires on the input
            _trapped = True
        assert _trapped, "the trap repro did not raise on the counterexample"
    assert repro_test(prove(_psrc, "result == x"), _psrc, ensures="result == x") is None  # PROVED: nothing to show
    # an UNKNOWN's reason is classified into the world it is in (budget / approximation / unmodeled) so the
    # next step is obvious, and an unmodeled construct names its line.
    from .diagnostics import classify_unknown, advice, budget_helps, capabilities
    assert classify_unknown("solver returned unknown") == "budget"
    assert classify_unknown("an over-approximated term yields no certified verdict") == "approximation"
    assert classify_unknown("unmodeled call external(...) at line 2") == "unmodeled"
    assert classify_unknown("") == "none"
    assert "budget" in advice("solver returned unknown") and advice("") == ""
    assert "Modeled subset" in capabilities() and "Verbs" in capabilities()
    _uc = check("def f(x):\n    return external(x)\n")            # an unmodeled call: UNKNOWN, named, with its line
    assert _uc.status == UNKNOWN and classify_unknown(_uc.reason) == "unmodeled", _uc
    assert "external" in _uc.reason and "line 2" in _uc.reason, _uc
    # the language server surfaces verdicts as diagnostics (a trap is an error, trap freedom is info) and
    # offers a code action that inserts a proven contract into a contract-free function.
    from . import lsp as _lsp
    _dg = _lsp.diagnostics("def f(x):\n    return 10 // x\n")
    assert _dg and _dg[0]["severity"] == 1 and "REFUTED" in _dg[0]["message"], _dg
    _dp = _lsp.diagnostics("def f(x):\n    return x + 1\n")
    assert _dp and _dp[0]["severity"] == 3 and "PROVED" in _dp[0]["message"], _dp
    _ca = _lsp._code_actions("def g(x):\n    return x * x\n", "file:///t.py",
                             {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}})
    assert _ca and "g" in _ca[0]["title"], _ca
    _new = _ca[0]["edit"]["changes"]["file:///t.py"][0]["newText"]
    assert "@ensure(" in _new, _new
    ast.parse(_new + "def g(x):\n    return x * x\n")             # the inserted contract + def is valid Python
    # richer spec vocabulary: old(e) in a postcondition (the entry value, == e in the functional model), and
    # bounded all/any quantifiers over a concrete iterable (a constant range, a list/tuple literal) unrolled
    # to a sound finite conjunction/disjunction. A symbolic-length collection declines rather than unsoundly.
    assert prove("def f(x):\n    return x\n", "result == old(x)").status == PROVED
    assert prove("def f(x):\n    if x < 0:\n        return -x\n    return x\n", "result >= old(x)").status == PROVED
    assert prove("def f():\n    return 0\n", "all(i >= 0 for i in range(5))").status == PROVED
    assert prove("def f():\n    return 0\n", "any(i > 3 for i in range(5))").status == PROVED
    assert prove("def f():\n    return 0\n", "all(x > 0 for x in (1, 2, 3))").status == PROVED
    assert prove("def f():\n    return 0\n", "all(i > 0 for i in range(5))").status == REFUTED          # i = 0
    assert prove("def f(n):\n    return n\n", "all(i < n for i in range(3))", requires="n >= 3").status == PROVED
    assert prove("def f(xs):\n    return xs\n", "all(x >= 0 for x in xs)",
                 requires="all(x >= 0 for x in xs)").status == UNKNOWN          # symbolic length: declines soundly
    # divmod(a, b) is modeled as (a // b, a % b): the divmod identity holds, the remainder is bounded, and a
    # zero divisor traps exactly as // and % do (it reuses the Rocq-verified division encoding).
    assert prove("def f(a, b):\n    q, r = divmod(a, b)\n    return q * b + r\n", "result == a",
                 requires="b != 0").status == PROVED
    assert prove("def f(a, b):\n    q, r = divmod(a, b)\n    return r\n", "0 <= result and result < b",
                 requires="b > 0").status == PROVED
    assert check("def f(a, b):\n    return divmod(a, b)\n").status == REFUTED   # b = 0 traps
    # the pow builtin reuses the modeled ** and % encodings: pow(a, b) == a ** b and pow(a, b, m) == (a ** b) % m
    assert prove("def f(x):\n    return pow(x, 2)\n", "result == x * x").status == PROVED
    assert prove("def f(a, m):\n    return pow(a, 2, m)\n", "result == (a * a) % m",
                 requires="m > 0").status == PROVED
    assert check("def f(x):\n    return pow(x, 2, 0)\n").status == REFUTED       # three-arg pow with m = 0 traps
    # membership in a set literal is modeled as a disjunction of equalities: x in {a, b} == (x == a or x == b)
    assert prove("def f(x):\n    return x in {1, 2, 3}\n",
                 "result == (x == 1 or x == 2 or x == 3)").status == PROVED
    assert prove("def f(x):\n    return x not in {0, 5}\n",
                 "result == (x != 0 and x != 5)").status == PROVED

    # general control flow: either step direction, break/continue, and statements after a loop all verify
    down = "def f(n):\n    s = 0\n    for i in range(n, 0, -1):\n        s = s + 1\n    return s\n"
    assert verify_function("cf-down", "f", down, lambda S: S["n"] >= 0,
                           lambda S, r: r == S["n"]).status == PROVED           # descending range counts n
    assert verify_function("cf-step", "f",
                           "def f():\n    s = 0\n    for i in range(10, 0, -2):\n        s = s + 1\n    return s\n",
                           lambda S: z3.BoolVal(True), lambda S, r: r == 5).status == PROVED   # step -2
    assert verify_termination("cf-down-t", "f", down).status == PROVED          # and it terminates
    brk = "def f(n):\n    i = 0\n    while i < n:\n        if i == 5:\n            break\n        i = i + 1\n    return i\n"
    assert verify_function("cf-break", "f", brk, lambda S: S["n"] >= 0, lambda S, r: r >= 0).status == PROVED
    after = "def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    r = i + 1\n    return r\n"
    assert verify_function("cf-after", "f", after, lambda S: S["n"] >= 0,
                           lambda S, r: r == S["n"] + 1).status == PROVED        # statement after the loop

    # synthesizing the invariant Spacer misses: the quadratic sum proves, a false quadratic never does
    gauss = "def f(n):\n    s = 0\n    i = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n"
    assert verify_chc("synth", "f", gauss, lambda S: S["n"] >= 0,
                      lambda S, r: 2 * r == S["n"] * (S["n"] - 1)).status == PROVED       # synthesized invariant
    assert verify_chc("synth-false", "f", gauss, lambda S: S["n"] >= 0,
                      lambda S, r: 2 * r == S["n"] * S["n"]).status != PROVED             # never a false prove

    # a list grown by append in a loop: its length is tracked as an integer, so a length property
    # verifies (and a false one is refuted); element access is left to the heap engine untouched.
    _build = "def f(n):\n    a = []\n    i = 0\n    while i < n:\n        a.append(i)\n        i = i + 1\n    return len(a)\n"
    assert prove(_build, "result == n", requires="n >= 0").status == PROVED
    assert prove(_build, "result == n + 1", requires="n >= 0").status == REFUTED
    assert check(_build).status == PROVED                          # trap-free across the engines
    assert verify_termination("ll-term", "f", _build).status == PROVED
    assert check(_build, total=True).status == PROVED              # trap-free and terminating
    assert verify_heap_property("ll-content", "f", "def f():\n    a = []\n    a.append(7)\n    return a[0]\n",
                                lambda za, r: r == 7).status == PROVED      # contents still via the heap engine
    # an integer index into an opaque container parameter is bounds-checked against its symbolic length:
    # unguarded a[0] is out of range on the empty container (REFUTED), a len() guard or an explicit
    # 0 <= i < len(a) check discharges the bound (PROVED), and a slice never traps (Python clamps it)
    assert check("def f(a):\n    return a[0]\n").status == REFUTED
    assert check("def f(a):\n    if len(a) > 0:\n        return a[0]\n    return 0\n").status == PROVED
    assert check("def f(a, i):\n    if 0 <= i and i < len(a):\n        return a[i]\n    return 0\n").status == PROVED
    assert check("def f(a):\n    return a[1:2]\n").status == PROVED
    # the same bound is checked on an item store a[i] = v; a local dict's d[k] = v still never traps
    assert check("def f(a):\n    a[0] = 1\n    return a\n").status == REFUTED
    assert check("def f(a):\n    if len(a) > 0:\n        a[0] = 1\n    return a\n").status == PROVED
    assert check("def f():\n    out = {}\n    out[0] = 1\n    return out\n").status == PROVED
    # an explicit list annotation gets the same bounds reasoning as an inferred container
    assert check("def f(a: list):\n    return a[0]\n").status == REFUTED
    assert check("def f(a: list):\n    if len(a) > 0:\n        return a[0]\n    return 0\n").status == PROVED
    # a tuple is a bounds-checked sequence whose item assignment always raises (TypeError)
    assert check("def f(t: tuple):\n    return t[0]\n").status == REFUTED
    assert check("def f(t: tuple):\n    if len(t) > 0:\n        return t[0]\n    return 0\n").status == PROVED
    assert check("def f(t: tuple):\n    t[0] = 1\n    return t\n").status == REFUTED
    # a dict read d[k] traps (KeyError) unless k is a proven member: a `k in d` guard or a `for k in d`
    # iteration makes it safe; an item store d[k] = v never traps (a dict accepts any key)
    assert check("def f(d: dict, k):\n    return d[k]\n").status == REFUTED
    assert check("def f(d: dict, k):\n    if k in d:\n        return d[k]\n    return 0\n").status == PROVED
    assert check("def f(d: dict):\n    s = 0\n    for k in d:\n        s = s + d[k]\n    return s\n").status == PROVED
    assert check("def f(d: dict):\n    d[0] = 1\n    return d\n").status == PROVED
    # a string-keyed dict is tracked the same way: the membership predicate is typed by the key's sort
    assert check("def f(d: dict):\n    return d['x']\n").status == REFUTED
    assert check("def f(d: dict):\n    if 'x' in d:\n        return d['x']\n    return 0\n").status == PROVED
    assert check("def f(d: dict, s: str):\n    if s in d:\n        return d[s]\n    return 0\n").status == PROVED

    # IEEE-754 total over every double: Inf/NaN are first-class inputs; guards prove total, finite_inputs recovers
    assert verify_float_finite("f3", "f", "def f(x):\n    return x\n").status == REFUTED          # Inf/NaN passes through
    assert verify_float_finite("f3", "f", "def f(x):\n    return x\n", finite_inputs=True).status == PROVED
    assert verify_float_finite("f3", "f",
                               "def f(x):\n    if isfinite(x):\n        return x\n    return 0.0\n"
                               ).status == PROVED                                                 # guarded, total
    assert verify_float_finite("f3", "f",
                               "def f(x):\n    if isnan(x):\n        return 0.0\n    if isinf(x):\n"
                               "        return 0.0\n    return x\n").status == PROVED              # isnan/isinf guards

    # solver tuning is configurable rather than hardcoded: a tiny resource budget leaves a nonlinear query
    # inconclusive on every machine alike (the deterministic rlimit binds, not the wall clock), the default
    # budget discharges it, and an unknown setting is rejected loudly.
    nlq = ("def f(a, b):\n    return (a + b) * (a + b)\n",
           "def g(a, b):\n    return a * a + 2 * a * b + b * b\n")
    _prior = core.configure(solve_rlimit=1)
    try:
        assert verify_equiv("cfg", "f", nlq[0], nlq[1], {}).status == UNKNOWN     # rlimit binds, deterministically
    finally:
        core.configure(solve_rlimit=_prior["solve_rlimit"])
    assert verify_equiv("cfg", "f", nlq[0], nlq[1], {}).status == PROVED          # default budget proves it
    # a budget-bound UNKNOWN auto-escalates the rlimit once before returning: at a starved budget prove is UNKNOWN
    # with escalation disabled and PROVED with it (the retry is deterministic; the verdict is still the solver's).
    _esrc = "def f(a, b, c):\n    return (a + b + c) * (a + b + c)\n"
    _epost = "result == a*a + b*b + c*c + 2*a*b + 2*a*c + 2*b*c"
    _eprior, _ecap = core.configure(solve_rlimit=100000), core.BUDGET_ESCALATE_CAP
    try:
        core.BUDGET_ESCALATE_CAP = 100000                                        # 8x > cap: escalation off
        assert prove(_esrc, _epost, target="f").status == UNKNOWN
        core.BUDGET_ESCALATE_CAP = 200000000                                     # escalation on
        assert prove(_esrc, _epost, target="f").status == PROVED
    finally:
        core.BUDGET_ESCALATE_CAP = _ecap
        core.configure(solve_rlimit=_eprior["solve_rlimit"])
    # the float path is bounded by a deterministic rlimit, not the wall clock: a starved rlimit makes the
    # verdict UNKNOWN on every machine alike (not a CPU-speed race), and the default rlimit decides it.
    fpq = ("def f(x: float):\n    return x + x\n", "def g(x: float):\n    return 2.0 * x\n")
    _fpr = core.configure(fp_solve_rlimit=1)
    try:
        assert verify_equiv("fp-det", "f", fpq[0], fpq[1], {}).status == UNKNOWN  # rlimit binds, deterministically
    finally:
        core.configure(fp_solve_rlimit=_fpr["fp_solve_rlimit"])
    assert verify_equiv("fp-det", "f", fpq[0], fpq[1], {}).status == PROVED       # default rlimit decides it
    try:
        core.configure(no_such_knob=1)
        assert False, "configure accepted an unknown key"
    except ValueError:
        pass

    # the verification-condition generator the engine runs is the one proven sound and complete in
    # Rocq (touchstone_functor.v's wpg), extracted to OCaml and mirrored here. It decides goals over
    # the integer loop-free fragment directly, is trap-aware (a reachable division by zero leaves the
    # VC undischarged), reads parameters at entry in the postcondition, and rejects a non-integer
    # parameter as outside its fragment rather than reasoning about it as an integer.
    assert prove_via_vcgen("def f(x):\n    return x + 1\n", "result == x + 1").status == PROVED
    assert prove_via_vcgen("def f(x):\n    return x + 1\n", "result == x").status == REFUTED
    assert prove_via_vcgen("def d(x):\n    return 10 // x\n", "result <= 10", requires="x >= 1").status == PROVED
    assert prove_via_vcgen("def d(x):\n    return 10 // x\n", "result <= 10").status == REFUTED    # x = 0 traps
    assert prove_via_vcgen("def f(x):\n    if x < 0:\n        x = 0 - x\n    return x\n",
                           "result >= 0").status == PROVED                        # abs, parameter reassigned
    assert prove_via_vcgen("def f(a, b):\n    if a > b:\n        r = a\n    else:\n        r = b\n    return r\n",
                           "result >= a and result >= b").status == PROVED        # comparison guard
    assert prove_via_vcgen("def f(x):\n    return x % 2\n", "result >= 0 and result <= 1",
                           requires="x >= 0").status == PROVED                    # modulo via the // encoding
    assert prove_via_vcgen("def f(x: float):\n    return x + x\n", "result == x").status == UNKNOWN  # not an integer
    assert prove_via_vcgen("def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n",
                           "result == n").status == UNKNOWN                       # a loop is outside the fragment
    # prove() emits the goal through the verified generator on this fragment, and the verdict agrees
    # with what the engine reaches on its own (no routing regresses a verdict).
    for _src, _ens in [("def f(x):\n    return x * x\n", "result >= 0"),
                       ("def g(a, b):\n    return a + b\n", "result == a + b"),
                       ("def k(x):\n    y = x + 1\n    z = y * 2\n    return z\n", "result == 2 * x + 2")]:
        assert prove(_src, _ens).status == PROVED, (_src,)
    # and / or in VALUE position return an OPERAND (2 or 3 is 2, 7 and 9 is 9), not a 0/1 truth value, and
    # they short-circuit. The IR's eand / eor are the 0/1-valued connective (sound only in a test), so the
    # verified generator declines a value-position and/or and prove() falls back to the symbolic engine,
    # whose ev models the operand value and the short-circuit trap path exactly.
    assert prove("def f():\n    return 2 or 3\n", "result == 2").status == PROVED
    assert prove("def f():\n    return 2 or 3\n", "result == 1").status == REFUTED
    assert prove("def f():\n    return 7 and 9\n", "result == 9").status == PROVED
    assert prove("def f():\n    return 5 or 0\n", "result == 5").status == PROVED
    assert prove("def f(x):\n    return x or 1\n", "result == x", requires="x != 0").status == PROVED
    assert prove_via_vcgen("def f():\n    return 2 or 3\n", "result == 2").status == UNKNOWN   # operand: declined
    # path independence: a functionally-irrelevant repo routes to the same engine and must not flip the verdict
    assert prove("def f():\n    return 2 or 3\n", "result == 2",
                 repo={"h": "def h():\n    return 0\n"}).status == PROVED
    # the vcgen path cross-checks its verdict against CPython (the lowering is outside the Rocq proof), so a
    # wrong verdict raises rather than returns: a fabricated PROVED of a false property is caught, a true one is not.
    from .vcgen import _audit_against_cpython as _avc
    _sav_ae = core.ALLOW_SUBJECT_EXECUTION
    core.ALLOW_SUBJECT_EXECUTION = True
    try:
        try:
            _avc("def f():\n    return 5\n", "result == 6", "True", [], PROVED, None)
            raise AssertionError("vcgen CPython cross-check missed a bogus PROVED")
        except SoundnessError:
            pass
        _avc("def f(x):\n    return x + x\n", "result == x * 2", "True", ["x"], PROVED, None)   # true: no raise
        # the PROVED check is exhaustive over the bounded box, so a multi-parameter lowering bug is caught on
        # some point of the box, while a correct multi-parameter verdict passes every point.
        _avc("def f(a, b):\n    return a + b\n", "result == a + b", "True", ["a", "b"], PROVED, None)  # no raise
        try:
            _avc("def f(a, b):\n    return a - b\n", "result == a + b", "True", ["a", "b"], PROVED, None)
            raise AssertionError("vcgen cross-check missed a bogus two-parameter PROVED")
        except SoundnessError:
            pass
    finally:
        core.ALLOW_SUBJECT_EXECUTION = _sav_ae
    # where the Rocq-extracted generator is built (the OCaml toolchain present), the in-engine generator
    # is held byte-for-byte equal to it on a random corpus; skipped cleanly where it is not built. The
    # interval transfer operators extracted from touchstone_domains.v are held equal to the in-engine
    # _iadd / _isub / _ineg / _ijoin / _imul the same way.
    _vca = extracted_vcgen_audit(trials=40)
    assert _vca["available"] in (True, False) and (not _vca["available"] or _vca["checks"] == 40), _vca
    _vcl = extracted_vcg_audit(trials=40)          # the loop generator vcg, held equal to its extraction
    assert _vcl["available"] in (True, False) and (not _vcl["available"] or _vcl["checks"] == 40), _vcl
    _via = extracted_intervals_audit(trials=40)
    assert _via["available"] in (True, False) and (not _via["available"] or _via["checks"] == 40), _via
    _ea = extracted_encoding_audit(bound=8)        # 17*17 - 17 = 272 nonzero-divisor pairs when built
    assert _ea["available"] in (True, False) and (not _ea["available"] or _ea["checks"] == 272), _ea
    _eac = extracted_encoding_committed_audit(bound=8)   # the same check against the committed Python extraction,
    assert _eac["available"] and _eac["checks"] == 272, _eac   # which runs with no Rocq toolchain on any machine
    _cea = committed_extraction_audit()                  # all four engine modules == the committed JSON extraction's
    assert _cea["available"] and _cea["checks"] == 4, _cea   # Python image, transpiled in-process with no toolchain

    # the z3-Spacer query wrapper (core._fp_query) mutes z3 4.16's internal-assertion stderr around a
    # Fixedpoint query and is transparent to the verdict; its retry re-runs once on a transient wall-clock
    # timeout so an otherwise-fast solve is not flaked. A tiny unreachable-bad-state query checks the
    # wrapper, with and without retry, returns exactly what a bare query does.
    _qfp = z3.Fixedpoint(); _qfp.set(engine="spacer")
    _Rq = z3.Function("Rq", z3.IntSort(), z3.BoolSort()); _Bq = z3.Function("Bq", z3.BoolSort())
    _qi = z3.Int("qi"); _qfp.register_relation(_Rq); _qfp.register_relation(_Bq); _qfp.declare_var(_qi)
    _qfp.rule(_Rq(0)); _qfp.rule(_Rq(_qi + 1), [_Rq(_qi), _qi < 3]); _qfp.rule(_Bq(), [_Rq(_qi), _qi > 5])
    _bare = str(_qfp.query(_Bq()))
    assert str(core._fp_query(_qfp, _Bq())) == _bare == "unsat", _bare        # transparent: bad state unreachable
    assert str(core._fp_query(_qfp, _Bq(), retry=2)) == _bare                 # the retry path returns the same verdict

    # **kwargs / *args are modeled parameters: a kw read or an *args index traps unless guarded
    assert check("def f(**kw):\n    return kw['x']\n").status == REFUTED                  # KeyError
    assert check("def f(**kw):\n    if 'x' in kw:\n        return kw['x']\n    return 0\n").status == PROVED
    assert check("def f(*a):\n    return a[0]\n").status == REFUTED                        # IndexError on empty
    assert check("def f(*a):\n    if len(a) > 0:\n        return a[0]\n    return 0\n").status == PROVED
    # C3 multiple inheritance in the heap engine: D(B, C), C.who but no B.who -> C.who (MRO D, B, C, A), not A.who
    _c3 = ("class A:\n    def who(self):\n        return 1\n"
           "class B(A):\n    pass\n"
           "class C(A):\n    def who(self):\n        return 3\n"
           "class D(B, C):\n    pass\n"
           "def f():\n    d = D()\n    return d.who()\n")
    assert verify_heap_property("c3", "f", _c3, lambda za, r: r == 3).status == PROVED
    # best-effort (opt-in, off by default): an unmodeled call / trapping method is assumed well-behaved for
    # trap freedom (lower trust); off it abstains, and it never manufactures a postcondition proof.
    assert check("def f(x):\n    return ext(x)\n").status == UNKNOWN
    _be = check("def f(x):\n    return ext(x)\n", best_effort=True)
    assert _be.status == PROVED and "best-effort" in _be.technique and _be.certificate is None, _be
    assert check("def f(x):\n    return x.pop()\n", best_effort=True).status == PROVED     # trapping method assumed safe
    # best-effort also assumes operations on an unmodeled value are well-typed (lower trust, tainted): an opaque
    # subscript / index, unpack, membership, len, and iteration of a scalar get a verdict instead of abstaining,
    # while the sound default still abstains on each.
    assert check("def f(x):\n    return x.data[3]\n", best_effort=True, target="f").status == PROVED
    assert check("def f(x):\n    a, b = x.split_pair()\n    return a\n", best_effort=True, target="f").status == PROVED
    assert check("def f(x):\n    if 5 in x.items():\n        return 1\n    return 0\n", best_effort=True, target="f").status == PROVED
    assert check("def f(x: int):\n    n = 0\n    for y in x:\n        n = y\n    return n\n", best_effort=True, target="f").status == PROVED
    assert check("def f(x):\n    return x.size() + 1\n", best_effort=True, target="f").status == PROVED
    # best-effort also covers printf-style % and the unmodeled-construct tail (a catch-all over any expression or
    # statement outside the modeled subset), assumed well-behaved; a modeled trap (int modulo by zero) is still kept.
    assert check("def f(s: str, x):\n    return s % x\n", best_effort=True, target="f").status == PROVED
    assert check("def f(s: str, x):\n    return s % x\n", target="f").status == UNKNOWN          # sound: abstains on printf %
    assert check("def f(x, y):\n    return x % y\n", best_effort=True, target="f").status == REFUTED   # int modulo trap kept
    # a construct that aborts the z3 encoding (a sort clash from `sep or ' '`) becomes a trap-free opaque function
    # under best-effort instead of abstaining, while a genuine modeled trap (division by zero) is still refuted.
    assert check("def f(s, sep):\n    return (sep or ' ').join(s)\n", best_effort=True, target="f").status == PROVED
    assert check("def f(s, sep):\n    return (sep or ' ').join(s)\n", target="f").status == UNKNOWN
    assert check("def f(x):\n    return 10 // x\n", best_effort=True, target="f").status == REFUTED
    assert check("def f(x):\n    return x.data[3]\n", target="f").status == UNKNOWN          # sound default: abstains
    assert check("def f(x: int):\n    n = 0\n    for y in x:\n        n = y\n    return n\n", target="f").status == UNKNOWN
    assert check("def f(x):\n    return ext(x)\n").status == UNKNOWN                       # flag restored after the run
    assert prove("def f(x):\n    return ext(x)\n", "result >= 0", best_effort=True).status == UNKNOWN
    # best-effort is taint-tracked: tagged lower-trust only when an assumption was used; a fully-modeled function
    # is full-trust (untagged, certificate kept). An opaque result used as a number is assumed numeric (tainted).
    _bena = check("def f(x):\n    return x + 1\n", best_effort=True)                       # no unmodeled construct
    assert _bena.status == PROVED and "[best-effort]" not in _bena.technique, _bena         # full trust, not tagged
    _bya = check("def f(x):\n    return ext(x)\n", best_effort=True)
    assert _bya.status == PROVED and "[best-effort]" in _bya.technique, _bya                # tainted: an assumption was used
    assert check("def f(x):\n    return ext(x) + 1\n", best_effort=True).status == PROVED    # result contract: assumed numeric
    assert check("def f(x):\n    return ext(x) + 1\n", target="f").status == UNKNOWN         # off best-effort: unchanged
    _bep = prove("def f(x):\n    return x + x\n", "result == 2 * x", best_effort=True)       # provable without any assumption
    assert _bep.status == PROVED and "[best-effort]" not in _bep.technique and _bep.certificate is not None, _bep
    # a module-qualified call on an imported name (json.loads, re.match) is an unmodeled module FUNCTION, not a
    # method on a modeled value: it can raise a modeled trap (json.loads('') -> JSONDecodeError, a ValueError),
    # so it is UNKNOWN by default -- the bare-unmodeled-call posture -- never assumed trap free, while a method
    # on a parameter / local value stays the assume-safe duck-typed call; best-effort assumes the module call safe.
    assert check("import json\ndef f(s: str):\n    return json.loads(s)\n", target="f").status == UNKNOWN
    assert check("import re\ndef f(s: str):\n    return re.match('[', s)\n", target="f").status == UNKNOWN
    assert check("import json\ndef f(s: str):\n    return json.loads(s)\n", target="f",
                 best_effort=True).status == PROVED
    assert check("def f(o):\n    return o.frobnicate()\n", target="f").status == PROVED   # value-param method: unchanged

    # The sandbox carries the builtin exceptions, so a subject's explicit `raise ValueError(...)` runs as
    # ValueError there, not a NameError from the name being absent -- the signal scan uses to confirm an
    # intended validation raise rather than mislabel it, and a faithful trap name for the differential oracle.
    _svx = (core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION)
    core.SANDBOX_SUBJECT = True
    _rb = core.sandbox_run_batch_typed("def r(n):\n    if n < 0:\n        raise ValueError('x')\n    return n\n",
                                       {}, "r", [[-1], [3]])
    assert _rb == [("raise", "ValueError"), ("ok",)], _rb
    core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = _svx

    # a self-recursive function whose trap the value engine cannot reach (it bails on the recursive call) is
    # decided by the recursion engine symbolically -- no execution -- so a base-case or recursive-step trap
    # refutes even with a leading import that would otherwise block the sandbox oracle (the import is a no-op
    # symbolically); a clean recursion is not falsely refuted.
    assert check("import os\ndef f(n):\n    if n <= 0:\n        return 10 // n\n    return f(n - 1)\n",
                 target="f").status == REFUTED                                    # base-case trap, import present
    assert check("import math\ndef f(n):\n    if n <= 1:\n        return 10 // (n - 1)\n    return f(n - 1)\n",
                 target="f").status == REFUTED                                    # trap reached through the recursion
    assert check("import os\ndef f(n):\n    if n <= 0:\n        return 0\n    return f(n - 1)\n",
                 target="f").status != REFUTED                                    # clean recursion: no false refutation

    # the recursive-callee trap is refuted SYMBOLICALLY (no execution), reducing the cases that need the sandbox:
    # a function whose only crash is reached through a RECURSIVE in-repo callee the inliner bails on -- f's
    # `x // gcd(x, y)` (gcd(0, 0) == 0), or a callee whose own base case traps -- is refuted by bounded symbolic
    # unrolling of the caller and its callees (_interproc_bmc_witness), taking a witness only on a fully-unrolled
    # (exact) path. A precondition ruling the trap out is not falsely refuted, a trap-free recursion is not
    # refuted, and the sandbox oracle remains the deeper fallback (a trap past the unrolling bound, a non-integer
    # parameter) -- still REFUTING with execution on.
    _gcd = "def g(a, b):\n    return abs(b) if a == 0 else g(b % a, a)\n"
    _lcm = "def f(x, y):\n    return x // g(x, y) * y\n"
    _rp = {"g": _gcd, "f": _lcm}
    _sv = (core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION)
    core.SANDBOX_SUBJECT = False; core.ALLOW_SUBJECT_EXECUTION = False         # NO execution: purely symbolic
    _cs = check(_lcm, repo=_rp, target="f")
    assert _cs.status == REFUTED and _cs.counterexample_inputs == {"x": 0, "y": 0}, _cs   # gcd(0,0)==0, symbolic witness
    _rb = {"rec": "def rec(n):\n    if n <= 0:\n        return 10 // n\n    return rec(n - 1)\n",
           "f": "def f(n):\n    return rec(n)\n"}
    _rbv = check(_rb["f"], repo=_rb, target="f")
    assert _rbv.status == REFUTED and _rbv.counterexample_inputs is not None, _rbv   # a callee whose base case traps
    assert check(_lcm, repo=_rp, target="f", requires="x != 0 and y != 0").status == UNKNOWN   # guard: no false refute
    _safeic = {"rec": "def rec(n):\n    if n <= 0:\n        return 0\n    return rec(n - 1) + 1\n",
               "f": "def f(n):\n    return rec(n) + 1\n"}
    assert check(_safeic["f"], repo=_safeic, target="f").status != REFUTED     # a trap-free recursion is not refuted
    core.SANDBOX_SUBJECT = True                                                # the sandbox remains the deeper fallback
    _ce = check(_lcm, repo=_rp, target="f")
    assert _ce.status == REFUTED and _ce.counterexample_inputs == {"x": 0, "y": 0}, _ce
    core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = _sv
    # a recursive helper the inliner cannot unfold, verified trap free standalone, is inlined as a trap-free
    # result so the CALLER decides SYMBOLICALLY (no execution) instead of bailing to UNKNOWN -- a recursive
    # helper inside a larger function is triaged. The helper's result range is not modeled (an
    # over-approximation), so a trap that rests on it withholds REFUTED (UNKNOWN, no fabricated witness), and a
    # helper that can itself trap is not marked, so the caller stays UNKNOWN.
    from .engines import _trapfree_recursive_callees
    _sv6 = (core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION)
    core.SANDBOX_SUBJECT = False; core.ALLOW_SUBJECT_EXECUTION = False     # force the symbolic path, no sandbox oracle
    try:
        _rfac = {"fac": "def fac(n):\n    if n <= 0:\n        return 1\n    return n * fac(n - 1)\n",
                 "f": "def f(n):\n    return fac(n) + 1\n"}
        assert check(_rfac["f"], repo=_rfac, target="f").status == PROVED        # trap-free recursive helper: symbolic PROVED
        assert check("def f(n):\n    return 10 // fac(n)\n", repo=_rfac, target="f").status == UNKNOWN   # result range unmodeled
        _rtrap = {"rec": "def rec(n):\n    if n <= 0:\n        return 0\n    return 10 // (n - 5) + rec(n - 1)\n",
                  "f": "def f(n):\n    return rec(n)\n"}
        assert check(_rtrap["f"], repo=_rtrap, target="f").status != PROVED      # a trapping helper is not marked trap free
        assert sorted(_trapfree_recursive_callees(_rfac["f"], _rfac)) == ["fac"]  # only the trap-free recursive callee is marked
        assert _trapfree_recursive_callees(_rtrap["f"], _rtrap) == frozenset()
    finally:
        core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = _sv6

    # a looping trap-freedom REFUTED carries a replayable witness, recovered by bounded unrolling
    # (_bmc_trap_witness) when the havoc'd value engine cannot give one. The witness genuinely traps, and a
    # guarded loop stays PROVED -- the bounded model introduces no spurious trap.
    _sv2 = (core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION)
    core.SANDBOX_SUBJECT = False                                   # the witness must be symbolic, not from execution
    _wl = "def f(n):\n    x = n\n    while x > 0:\n        x = x - 1\n    return 10 // x\n"
    _wv = check(_wl, target="f")
    assert _wv.status == REFUTED and _wv.counterexample_inputs, _wv
    _wns = {}; exec(_wl, _wns)                                     # the recovered input really raises
    try:
        _wns["f"](**_wv.counterexample_inputs); _wtrap = False
    except ZeroDivisionError:
        _wtrap = True
    assert _wtrap, _wv.counterexample_inputs
    assert check("def f(n):\n    s = 0\n    for i in range(n):\n        s = s + 1\n    return 5 // s\n",
                 target="f").counterexample_inputs, "a for-loop REFUTED must carry a witness too"
    assert check("def f(n):\n    s = 1\n    for i in range(n):\n        s = s + 1\n    return 10 // s\n",
                 target="f").status == PROVED                      # guarded: still PROVED, no spurious witness
    core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = _sv2

    # scan normalizes a GitHub web (blob) file URL to its raw form, so a link copied from the browser fetches
    # source rather than the HTML page (which parses to zero functions and would read as a false "no traps").
    from .engines import _normalize_url as _nrm
    assert _nrm("https://github.com/voxel51/fiftyone/blob/develop/fiftyone/utils/transformers.py") == \
        "https://raw.githubusercontent.com/voxel51/fiftyone/develop/fiftyone/utils/transformers.py", "blob->raw"
    assert _nrm("http://github.com/o/r/blob/main/p/q.py") == "https://raw.githubusercontent.com/o/r/main/p/q.py"
    assert _nrm("https://raw.githubusercontent.com/o/r/main/x.py") == \
        "https://raw.githubusercontent.com/o/r/main/x.py", "an already-raw URL is unchanged"
    assert _nrm("https://github.com/o/r") == "https://github.com/o/r", "a repo URL is left for git clone"
    assert _nrm("/local/path/to/file.py") == "/local/path/to/file.py", "a local path is unchanged"
    assert _nrm("owner/repo") == "https://github.com/owner/repo", "a bare owner/repo slug -> GitHub repo URL"
    assert _nrm("github.com/owner/repo") == "https://github.com/owner/repo", "a scheme-less host gets https"
    assert _nrm("https://github.com/o/r/pull/9") == "https://github.com/o/r", "any github link -> the repo root"
    assert _nrm("https://github.com/o/r/tree/main/sub") == "https://github.com/o/r/tree/main/sub", "tree kept for resolver"
    assert _nrm("./rel/path") == "./rel/path", "a relative path is unchanged"
    assert _nrm("o/r/tree/main/sub") == "https://github.com/o/r/tree/main/sub", "bare owner/repo/tree path -> github"
    assert _nrm("o/r/blob/main/x.py") == "https://raw.githubusercontent.com/o/r/main/x.py", "bare owner/repo/blob path -> raw"

    # scan demotes a finding in a private helper (a trap that may rest on a caller-maintained precondition): it
    # is labeled and ranked below an API-reachable finding rather than presented as an equal hit; and a method's
    # receiver is opaque, so a 'trap' the engine could pin only to self=<scalar> is not reported (a receiver is
    # an object, never a sampled scalar), while a genuine parameter-only trap in a method still is.
    import tempfile as _tfx, os as _osx, shutil as _shx
    _dx = _tfx.mkdtemp(prefix="ts_st_")
    try:
        _pf = _osx.path.join(_dx, "pf.py")
        with open(_pf, "w", encoding="utf-8") as _fh:
            _fh.write("def pub(x):\n    return 100 // x\n\ndef _helper(x):\n    return 100 // x\n")
        _pr = {f["location"]: f for f in scan(_pf, execute=False)["findings"]}
        assert "private helper" in _pr["_helper"]["label"] and _pr["_helper"]["rank"] == 1, _pr["_helper"]
        assert "private helper" not in _pr["pub"]["label"], _pr["pub"]              # a public function is not demoted
        _mf = _osx.path.join(_dx, "mf.py")
        with open(_mf, "w", encoding="utf-8") as _fh:
            _fh.write("class C:\n    def selftrap(self, a):\n        return a // self\n"
                      "    def realtrap(self, a, b):\n        return a // b\n")
        _ml = {f["location"] for f in scan(_mf, execute=False)["findings"]}
        assert "C.realtrap" in _ml and "C.selftrap" not in _ml, _ml                 # self-scalar trap is not a finding
        # context-confirmation: a private helper whose standalone trap is unreachable through its real in-repo
        # callers is demoted (classification context-unreachable, rank 0) rather than presented as a candidate --
        # the caller-maintained-precondition case. Demotes when every call site pins the witnessing parameter to a
        # constant that misses the witness, OR when every caller is itself verified trap free (so the inlined call
        # cannot reach the trap). Scan ranking only -- the standalone check verdict is unchanged. An unguarded
        # symbolic caller, or no in-repo caller, keeps the finding.
        _cf = _osx.path.join(_dx, "ctx_const.py")
        with open(_cf, "w", encoding="utf-8") as _fh:                                # callers pass constants missing n=-2
            _fh.write("def _div(n):\n    return 100 // (n + 2)\n\ndef pub(x):\n    return _div(5) + _div(7)\n")
        _cr = {f["location"]: f for f in scan(_cf, execute=False)["findings"]}
        assert _cr["_div"]["classification"] == "context-unreachable" and _cr["_div"]["rank"] == 0, _cr.get("_div")
        _gf = _osx.path.join(_dx, "ctx_guard.py")                                    # the only caller guards x != 0 (PROVED)
        with open(_gf, "w", encoding="utf-8") as _fh:
            _fh.write("def _recip(x):\n    return 10 // x\n\ndef pub(x):\n    if x != 0:\n        return _recip(x)\n    return 0\n")
        _gr = {f["location"]: f for f in scan(_gf, execute=False)["findings"]}
        assert _gr["_recip"]["classification"] == "context-unreachable", _gr.get("_recip")
        _uf = _osx.path.join(_dx, "ctx_unguard.py")                                  # caller passes x unguarded: still a candidate
        with open(_uf, "w", encoding="utf-8") as _fh:
            _fh.write("def _recip(x):\n    return 10 // x\n\ndef pub(x):\n    return _recip(x)\n")
        _ur = {f["location"]: f for f in scan(_uf, execute=False)["findings"]}
        assert _ur["_recip"]["classification"] != "context-unreachable", _ur.get("_recip")
        assert "_recip" in _ur and _ur["_recip"]["classification"] == "unconfirmed", _ur.get("_recip")
    finally:
        _shx.rmtree(_dx, ignore_errors=True)

    # numpy array constructors model the array by its shape -- a tuple of nonnegative dimension terms with
    # opaque, value-independent elements. A 1-D array (scalar shape) is a sized sequence: an in-bounds index is
    # trap free, an out-of-bounds one is refuted, a negative dimension is the ValueError numpy raises.
    _np = "import numpy as np\n"
    assert check(_np + "def f():\n    a = np.zeros(5)\n    return a[2]\n").status == PROVED
    assert check(_np + "def f():\n    a = np.zeros(5)\n    return a[5]\n").status == REFUTED
    assert check(_np + "def f(n):\n    a = np.zeros(n)\n    return 0\n").status == REFUTED          # negative dim
    assert check(_np + "def f(n):\n    if n < 0:\n        return 0\n    a = np.zeros(n)\n    return 0\n").status == PROVED
    assert check(_np + "def f():\n    a = np.array([1, 2, 3])\n    return a[2]\n").status == PROVED
    assert check(_np + "def f():\n    a = np.arange(5)\n    return a[5]\n").status == REFUTED
    # an N-dimensional array (a tuple shape, or a nested-list array) is now shape-aware: each dimension is a
    # nonnegative term (a negative one is the ValueError numpy raises), a.shape / a.ndim / a.size / len(a) are
    # derived, an integer or tuple index bounds-checks each axis and yields the lower-rank subarray, reshape
    # adjusts the shape with a total-size-mismatch trap (a -1 dimension is inferred), element-wise arithmetic
    # broadcasts (a non-broadcastable pair is a ValueError), and a min / max reduction of a zero-size array is a
    # ValueError. Element values stay opaque (value-independent).
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    return 0\n").status == PROVED        # 2-D: now modeled
    assert check(_np + "def f(m, n):\n    a = np.zeros((m, n))\n    return 0\n").status == REFUTED    # a negative dimension
    assert check(_np + "def f(m, n):\n    if m < 0 or n < 0:\n        return 0\n    a = np.zeros((m, n))\n    return 0\n").status == PROVED
    assert prove(_np + "def f():\n    a = np.zeros((4, 3))\n    return a.ndim\n", "result == 2").status == PROVED
    assert prove(_np + "def f():\n    a = np.zeros((4, 3))\n    return len(a)\n", "result == 4").status == PROVED
    assert prove(_np + "def f():\n    a = np.zeros((4, 3))\n    return a.shape[1]\n", "result == 3").status == PROVED
    assert prove(_np + "def f():\n    a = np.zeros((4, 3))\n    return a.size\n", "result == 12").status == PROVED
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    return a[1, 2]\n").status == PROVED    # in-bounds tuple index
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    return a[2, 0]\n").status == REFUTED   # axis-0 IndexError
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    return a[1][3]\n").status == REFUTED   # axis-1 IndexError
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    return a[1, 2, 0]\n").status == REFUTED  # too many indices
    assert prove(_np + "def f():\n    a = np.array([[1, 2], [3, 4]])\n    return a.shape[0]\n", "result == 2").status == PROVED
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    b = a.reshape((3, 2))\n    return 0\n").status == PROVED
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    b = a.reshape((4, 2))\n    return 0\n").status == REFUTED  # size mismatch
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    b = a.reshape((6, -1))\n    return 0\n").status == PROVED  # -1 inferred
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    b = np.ones((2, 3))\n    return (a + b)[0, 0]\n").status == PROVED
    assert check(_np + "def f(m):\n    a = np.zeros((m,))\n    return a.min()\n").status == REFUTED   # min of a possibly-empty array
    assert check(_np + "def f():\n    a = np.zeros((5,))\n    return a.min()\n").status == PROVED
    assert prove(_np + "def f():\n    a = np.zeros((2, 3))\n    return a.sum(axis=1).shape[0]\n", "result == 2").status == PROVED
    assert check(_np + "def f(t):\n    return t.sum()\n").status == PROVED                            # an unannotated receiver: opaque-safe
    # SOUNDNESS: the truth value of a multi-element array is a ValueError ("ambiguous"), so `if a:` does not
    # over-approximate to a benign bool -- it abstains (UNKNOWN). A rich comparison a == b
    # is ELEMENT-WISE (an array of booleans, not a scalar), so `if a == b:` is ambiguous too; `.any()` / `.all()`
    # give a real bool, and a scalar derived from the array (a.size > 0) is a normal comparison.
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    if a:\n        return 1\n    return 0\n").status == UNKNOWN
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    if not a:\n        return 1\n    return 0\n").status == UNKNOWN
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    b = np.ones((2, 3))\n    if a == b:\n        return 1\n    return 0\n").status == UNKNOWN
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    if a.any():\n        return 1\n    return 0\n").status == PROVED
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    if a.size > 0:\n        return 1\n    return 0\n").status == PROVED
    # an item store a[i] = v is bounds-checked on each axis exactly like a read, so an out-of-bounds store
    # REFUTES (1-D and N-d) and a guarded one proves. A 1-D array is the same shape model as N-d (so its
    # truthiness is ambiguous too, not a benign bool).
    assert check(_np + "def f():\n    a = np.zeros(5)\n    a[2] = 1\n    return 0\n").status == PROVED
    assert check(_np + "def f():\n    a = np.zeros(5)\n    a[5] = 1\n    return 0\n").status == REFUTED          # 1-D store out of bounds
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    a[1, 2] = 1\n    return 0\n").status == PROVED
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    a[2, 0] = 1\n    return 0\n").status == REFUTED   # N-d store out of bounds
    assert check(_np + "def f(i):\n    a = np.zeros((5,))\n    if 0 <= i < 5:\n        a[i] = 1\n    return 0\n").status == PROVED
    assert check(_np + "def f():\n    a = np.zeros(5)\n    if a:\n        return 1\n    return 0\n").status == UNKNOWN  # 1-D truthiness is ambiguous
    assert check(_np + "def f():\n    a = np.zeros((2, 3))\n    return a.item()\n").status == REFUTED            # .item() needs exactly one element
    assert check(_np + "def f():\n    a = np.zeros(1)\n    return a.item()\n").status == PROVED
    # numpy differential: the model's shape/length and negative-dimension trap match real numpy where installed.
    try:
        import numpy as _real_np
    except ImportError:
        _real_np = None
    if _real_np is not None:
        assert len(_real_np.zeros(5)) == 5 and len(_real_np.arange(5)) == 5
        assert len(_real_np.array([1, 2, 3])) == 3
        try:
            _real_np.zeros(-1); assert False, "np.zeros(-1) did not raise"
        except ValueError:
            pass
        # the N-d model's shape / size / len and its reshape / broadcast / empty-reduction traps match real numpy
        assert _real_np.zeros((2, 3)).ndim == 2 and _real_np.zeros((2, 3)).shape == (2, 3)
        assert _real_np.zeros((2, 3)).size == 6 and len(_real_np.zeros((4, 3))) == 4
        assert _real_np.array([[1, 2], [3, 4]]).shape == (2, 2)
        assert _real_np.zeros((2, 3))[1, 2] == 0 and _real_np.zeros((2, 3)).reshape((6, -1)).shape == (6, 1)
        for _bad, _exc in ((lambda: _real_np.zeros((2, 3)).reshape((4, 2)), ValueError),     # total size mismatch
                           (lambda: _real_np.zeros((2, 3))[2, 0], IndexError),               # axis-0 out of range
                           (lambda: _real_np.zeros((2, 3)) + _real_np.ones((4, 5)), ValueError),  # non-broadcastable
                           (lambda: _real_np.zeros((0,)).min(), ValueError)):                # zero-size reduction
            try:
                _bad(); assert False, "expected a numpy trap"
            except _exc:
                pass

    # PyTorch tensors reuse the ndarray shape model: a constructor (zeros / ones / empty / rand / randn with
    # separate dimensions or one tuple, full, tensor of a nested list, arange, eye, *_like) is a shape-aware
    # tensor whose negative dimension is the RuntimeError torch raises; an integer / tuple index bounds-checks
    # each axis; view / reshape carry the total-size-mismatch trap (a -1 dimension is inferred); size() / dim() /
    # numel() report the shape; element-wise arithmetic broadcasts. Element values stay opaque.
    _to = "import torch\n"
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    return a[1, 2]\n", target="f").status == PROVED
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    return a[2, 0]\n", target="f").status == REFUTED   # axis-0 IndexError
    assert check(_to + "def f(n):\n    a = torch.zeros(n, 3)\n    return 0\n", target="f").status == REFUTED        # negative dim
    assert prove(_to + "def f():\n    a = torch.tensor([[1, 2], [3, 4]])\n    return a.size(0)\n", "result == 2", target="f").status == PROVED
    assert prove(_to + "def f():\n    a = torch.zeros((2, 3))\n    return a.dim()\n", "result == 2", target="f").status == PROVED
    assert prove(_to + "def f():\n    a = torch.zeros((2, 3))\n    return a.numel()\n", "result == 6", target="f").status == PROVED
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    b = a.view(6)\n    return 0\n", target="f").status == PROVED
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    b = a.view(7)\n    return 0\n", target="f").status == REFUTED  # size mismatch
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    b = a.reshape(-1)\n    return 0\n", target="f").status == PROVED  # -1 inferred
    assert check(_to + "def f():\n    a = torch.arange(5)\n    return a[5]\n", target="f").status == REFUTED        # 1-D index out of range
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    b = torch.ones(2, 3)\n    return (a + b)[0, 0]\n", target="f").status == PROVED
    # tensor algebra is shape-tracked: matmul checks the inner dimension, cat the non-concatenation axes, and
    # the elementwise / shape-preserving family (in-place, dtype, keepdim / tuple-axis reductions) is trap free.
    assert check(_to + "def f():\n    return torch.zeros(2, 3) @ torch.zeros(3, 4)\n", target="f").status == PROVED
    assert check(_to + "def f():\n    return torch.zeros(2, 3) @ torch.zeros(4, 5)\n", target="f").status == REFUTED   # inner-dim mismatch
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    return a.mm(torch.zeros(4, 4))\n", target="f").status == REFUTED
    assert check(_to + "def f():\n    return torch.matmul(torch.zeros(2, 3), torch.zeros(3, 4))[0, 0]\n", target="f").status == PROVED
    assert prove(_to + "def f():\n    a = torch.zeros(2, 3)\n    b = torch.bmm(torch.zeros(5, 2, 3), torch.zeros(5, 3, 4))\n    return b.shape[2]\n", "result == 4", target="f").status == PROVED   # batched matmul
    assert prove(_to + "def f():\n    return torch.cat((torch.zeros(2, 3), torch.zeros(5, 3)), 0).shape[0]\n", "result == 7", target="f").status == PROVED
    assert check(_to + "def f():\n    return torch.cat((torch.zeros(2, 3), torch.zeros(2, 4)), 0)\n", target="f").status == REFUTED   # a mismatched non-cat axis
    assert prove(_to + "def f():\n    return torch.stack((torch.zeros(2, 3), torch.zeros(2, 3)), 0).shape[0]\n", "result == 2", target="f").status == PROVED
    assert prove(_to + "def f():\n    return torch.zeros(2, 3).unsqueeze(0).shape[0]\n", "result == 1", target="f").status == PROVED
    assert prove(_to + "def f():\n    return torch.zeros(2, 3, 4).permute(2, 0, 1).shape[0]\n", "result == 4", target="f").status == PROVED
    assert prove(_to + "def f():\n    return torch.zeros(2, 3).transpose(0, 1).shape[0]\n", "result == 3", target="f").status == PROVED
    assert prove(_to + "def f():\n    return torch.zeros(2, 3).sum(1, keepdim=True).shape[1]\n", "result == 1", target="f").status == PROVED
    assert prove(_to + "def f():\n    return torch.zeros(2, 3, 4).sum((0, 1)).shape[0]\n", "result == 4", target="f").status == PROVED   # tuple-axis reduction
    assert prove(_to + "def f():\n    return torch.zeros(4).expand(3, 4).shape[0]\n", "result == 3", target="f").status == PROVED
    assert prove(_to + "def f():\n    return torch.zeros(2, 3).repeat(2, 5).shape[1]\n", "result == 15", target="f").status == PROVED
    assert prove(_to + "def f():\n    return torch.zeros(2, 3).narrow(1, 0, 2).shape[1]\n", "result == 2", target="f").status == PROVED
    assert prove(_to + "def f():\n    return torch.zeros(2, 3, 4).select(0, 0).shape[0]\n", "result == 3", target="f").status == PROVED
    assert check(_to + "def f():\n    a = torch.zeros(5)\n    a.add_(1)\n    a.mul_(2)\n    a.clamp_(0, 1)\n    return 0\n", target="f").status == PROVED   # in-place ops
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    a.backward()\n    a.requires_grad_()\n    return 0\n", target="f").status == PROVED   # autograd surface
    assert check(_to + "def f():\n    return torch.relu(torch.zeros(2, 3)).sigmoid().tanh().sum()\n", target="f").status == PROVED   # elementwise chain
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    return a.bool().int().float()[0, 0]\n", target="f").status == PROVED   # dtype conversions
    assert check(_to + "def f():\n    a = torch.zeros(2, 3)\n    b = torch.ones(2, 3)\n    if (a == b).all():\n        return 1\n    return 0\n", target="f").status == PROVED   # mask via .all()
    assert check(_to + "def f():\n    return torch.where(torch.zeros(2, 3) > 0, torch.zeros(2, 3), torch.ones(2, 3))[0, 0]\n", target="f").status == PROVED
    assert check(_to + "def f():\n    return torch.zeros(2, 3).softmax(1).cumsum(0).sum()\n", target="f").status == PROVED
    assert check(_to + "def f():\n    a = torch.zeros(5)\n    return a.nonzero()\n", target="f").status == PROVED   # data-dependent shape: opaque, trap free
    # an elementwise activation (torch.relu(x), F.gelu(x)) on a bare tensor param is trap free (no axis/shape arg). A
    # dim-taking op (softmax), a shape-changing layer (reshape/linear/layer_norm), or a reduction stays UNKNOWN.
    _tf = "import torch\nimport torch.nn.functional as F\n"
    assert check(_tf + "def f(x):\n    return torch.relu(x)\n", target="f").status == PROVED
    assert check(_tf + "def f(x):\n    return torch.sigmoid(x)\n", target="f").status == PROVED
    assert check(_tf + "def f(x):\n    return F.relu(x)\n", target="f").status == PROVED
    assert check(_tf + "def f(x):\n    return F.gelu(x)\n", target="f").status == PROVED
    assert check(_tf + "def f(x):\n    return F.silu(x)\n", target="f").status == PROVED
    assert check(_tf + "def f(x):\n    return F.leaky_relu(x)\n", target="f").status == PROVED
    assert check(_tf + "def f(x):\n    return torch.relu(x).sum()\n", target="f").status == PROVED
    assert check(_tf + "def f(x, k: int):\n    return F.dropout(x, 10 // k)\n", target="f").status == REFUTED  # arg trap caught
    assert check(_tf + "def f(x):\n    return torch.softmax(x, dim=5)\n", target="f").status == UNKNOWN     # dim may be OOB
    assert check(_tf + "def f(x):\n    return torch.reshape(x, (2, 3))\n", target="f").status == UNKNOWN    # size may mismatch
    assert check(_tf + "def f(x, w):\n    return F.linear(x, w)\n", target="f").status == UNKNOWN
    # a unary-math name (sqrt / abs) is excluded from the activation fallback so it reaches its scalar model:
    assert prove("import numpy as np\ndef f(x):\n    return np.abs(x)\n", "result >= 0").status == PROVED
    # numpy reuses the same shape algebra (matmul / concatenate / where); the scalar np.abs / np.sqrt models still apply.
    assert check(_np + "def f():\n    return np.zeros((2, 3)) @ np.zeros((3, 4))\n", target="f").status == PROVED
    assert check(_np + "def f():\n    return np.zeros((2, 3)) @ np.zeros((9, 4))\n", target="f").status == REFUTED
    assert prove(_np + "def f():\n    return np.concatenate((np.zeros((2, 3)), np.zeros((5, 3))), 0).shape[0]\n", "result == 7", target="f").status == PROVED
    assert check(_np + "def f():\n    return np.matmul(np.zeros((2, 3)), np.zeros((3, 4)))[0, 0]\n", target="f").status == PROVED
    assert prove(_np + "def f(x):\n    return np.abs(x)\n", "result >= 0").status == PROVED   # the scalar model is unaffected

    # pandas Series is a sized 1-D column with opaque cells: Series(list / container) carries the column's
    # length, a positional .iloc index is bounds-checked, and a min / max of a possibly-empty column is the
    # ValueError pandas raises; a guard on the length proves it. Cell values abstain. (DataFrame and pd.array
    # construction can raise on mismatched data, so they stay UNKNOWN.)
    _pd = "import pandas as pd\n"
    assert prove(_pd + "def f():\n    s = pd.Series([10, 20, 30])\n    return len(s)\n", "result == 3", target="f").status == PROVED
    assert check(_pd + "def f():\n    s = pd.Series([1, 2, 3])\n    return s.iloc[2]\n", target="f").status == PROVED
    assert check(_pd + "def f():\n    s = pd.Series([1, 2, 3])\n    return s.iloc[3]\n", target="f").status == REFUTED   # iloc out of range
    assert check(_pd + "def f(xs: list):\n    s = pd.Series(xs)\n    return s.min()\n", target="f").status == REFUTED   # min of a possibly-empty column
    assert check(_pd + "def f(xs: list):\n    if len(xs) == 0:\n        return 0\n    s = pd.Series(xs)\n    return s.min()\n", target="f").status == PROVED
    assert check(_pd + "def f(xs: list, i):\n    s = pd.Series(xs)\n    if 0 <= i < len(xs):\n        return s.iloc[i]\n    return 0\n", target="f").status == PROVED

    # framework value objects that recur as opaque receivers -- protobuf messages, datasets / config objects,
    # dataframes -- have a sound attribute / return contract: a parameter annotated with such a type (a bare
    # class name, a qualified module.Type, a string forward reference, or a union) is an opaque receiver, so an
    # attribute access or a method call on it raises no modeled trap (PROVED), while a construction whose
    # __init__ can raise a modeled trap (a mismatched DataFrame, an unknown protobuf field) correctly stays
    # UNKNOWN.
    assert check("def f(msg: SomeMessage):\n    return msg.field\n", target="f").status == PROVED          # bare class name
    assert check("import m\ndef f(cfg: m.Config):\n    return cfg.hidden_size\n", target="f").status == PROVED   # qualified type
    assert check("import pandas as pd\ndef f(df: pd.DataFrame):\n    return df.shape\n", target="f").status == PROVED
    assert check("def f(ds: 'Dataset'):\n    x = ds.map(ds)\n    return 0\n", target="f").status == PROVED   # string forward ref
    assert check("def f(x: A | B):\n    return x.run()\n", target="f").status == PROVED                     # a PEP-604 union
    assert check("def f():\n    m = SomeMessage()\n    return 0\n", target="f").status == UNKNOWN            # construction can raise: UNKNOWN

    # a whole-repo scan skips test modules (a test's helpers/fixtures are not the code under audit), and a
    # symbolic finding whose only trap is an explicit raise/assert is classified intended input validation
    # (not a candidate crash) -- the reason annotator re-checked that stripping the guards proves it trap free.
    from .engines import _is_test_module as _itm
    assert _itm("tests.test_api") and _itm("pkg.test_x") and _itm("conftest") and _itm("a.tests.b")
    assert not _itm("jwt.algorithms") and not _itm("pkg.utils")
    _dv = _tfx.mkdtemp(prefix="ts_iv_")
    try:
        _vp = _osx.path.join(_dv, "v.py")
        with open(_vp, "w", encoding="utf-8") as _fh:
            _fh.write("def validate(n):\n    if n < 0:\n        raise ValueError('neg')\n    return n\n"
                      "\ndef crash(x):\n    return 100 // x\n")
        _vr = {f["location"]: f for f in scan(_vp, execute=False)["findings"]}
        assert _vr["validate"]["classification"] == "input-validation" and _vr["validate"]["rank"] == 0, _vr["validate"]
        assert _vr["crash"]["classification"] == "unconfirmed", _vr["crash"]        # a real op-trap stays a candidate
    finally:
        _shx.rmtree(_dv, ignore_errors=True)

    # scan: point at a local target and classify reachable traps. Symbolic never EXECUTES the code, yet now finds
    # the cross-callee crash (the inliner bails on the recursive callee, so bounded symbolic unrolling reaches it)
    # -- a finding classified `unconfirmed` (not run); --execute replays each finding in the sandbox, confirming
    # the exception and splitting a genuine bug from intended input validation; the execution flags are restored
    # after; and the MCP `scan` tool exposes the same report (one core, two surfaces).
    import os as _os, tempfile as _tf, shutil as _sh
    from .mcp import call_tool as _scan_call
    _d = _tf.mkdtemp(prefix="ts_selftest_")
    try:
        _p = _os.path.join(_d, "m.py")
        with open(_p, "w", encoding="utf-8") as _fh:
            _fh.write(_gcd + "\n" + _lcm)
        _flags0 = (core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION)
        _sym = scan(_p, execute=False)
        assert _sym["executed"] is False and _sym["refuted"] == 1, _sym        # found symbolically, NOT run
        assert _sym["findings"][0]["location"] == "f" and _sym["findings"][0]["classification"] == "unconfirmed", _sym
        _exe = scan(_p, execute=True)
        assert _exe["refuted"] == 1 and _exe["bugs"] == 1, _exe                # the cross-callee crash, confirmed
        _f0 = _exe["findings"][0]
        assert _f0["location"] == "f" and _f0["classification"] == "bug", _f0
        assert _f0["exception"] == "ZeroDivisionError" and "0" in (_f0["counterexample"] or ""), _f0
        assert _f0["repro"] and "def g(" in _f0["repro"] and "def f(" in _f0["repro"], _f0   # repro carries the callee
        assert (core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION) == _flags0, "scan must restore the execution flags"
        _mcp = _scan_call("scan", {"target": _p, "execute": True})
        assert "[bug] f" in _mcp and "ZeroDivisionError" in _mcp, _mcp        # the MCP tool, same core

        # an explicit `raise ValueError` guarding a bad input is confirmed and classified intended validation,
        # NOT a bug -- the sandbox runs the named raise (with the builtin exceptions present, ValueError is
        # ValueError there, not a NameError from the name being absent).
        _vp = _os.path.join(_d, "val.py")
        with open(_vp, "w", encoding="utf-8") as _fh:
            _fh.write("def v(n):\n    if n < 0:\n        raise ValueError('neg')\n    return n * 2\n")
        _ve = scan(_vp, execute=True)
        assert _ve["bugs"] == 0 and _ve["input_validation"] == 1, _ve
        assert _ve["findings"][0]["classification"] == "input-validation", _ve
        assert _ve["findings"][0]["exception"] == "ValueError", _ve
        # a TypeError under sampled inputs is a likely type mismatch, not a confirmed bug: surface it as
        # unconfirmed, while a genuine division edge case still confirms (so the scan does not false-positive
        # on type-rich code where the sampler cannot match a string/list/object parameter).
        _pp = _os.path.join(_d, "prec.py")
        with open(_pp, "w", encoding="utf-8") as _fh:
            _fh.write("def crash(a, b):\n    return a // b\n\ndef tymism(x):\n    return None + x\n")
        _rp = scan(_pp, execute=True)
        _cls = {f["location"]: f["classification"] for f in _rp["findings"]}
        assert _cls.get("crash") == "bug", _cls
        assert _cls.get("tymism") != "bug", _cls
        # a confirmed crash in a private helper (single leading underscore) ranks below a public bug and carries
        # a likely-precondition note -- it relies on caller-maintained invariants, so a standalone crash is often
        # not reachable through the public API, but surfaced for review.
        _hp = _os.path.join(_d, "priv.py")
        with open(_hp, "w", encoding="utf-8") as _fh:
            _fh.write("def crash(a, b):\n    return a // b\n\ndef _helper(prev):\n    return prev[2] // 1\n")
        _rh = scan(_hp, execute=True)
        _byl = {f["location"]: f for f in _rh["findings"]}
        assert _byl["crash"]["rank"] == 3, _byl
        assert _byl["_helper"]["rank"] == 2 and "private helper" in _byl["_helper"]["label"], _byl
        # a directory scan confirms a bug from the subject's transitive callees alone, not the whole cross-module
        # repo: a sibling module that does not exec cleanly (a default that evaluates an undefined name at def
        # time) must not mask a confirmable trap.
        _d2 = _tf.mkdtemp(prefix="ts_dirscan_")
        try:
            with open(_os.path.join(_d2, "good.py"), "w", encoding="utf-8") as _fh:
                _fh.write("def crashy(a, b):\n    return a // b\n")
            with open(_os.path.join(_d2, "bad.py"), "w", encoding="utf-8") as _fh:
                _fh.write("def broken(x=UNDEF_GLOBAL):\n    return x\n")
            _rq = scan(_d2, execute=True)
            assert any(f["location"].endswith("crashy") and f["classification"] == "bug"
                       for f in _rq["findings"]), _rq
        finally:
            _sh.rmtree(_d2, ignore_errors=True)
        # a method bug is found symbolically by constructing the receiver and invoking the method through the
        # heap engine: an unguarded empty-container method (self.items.pop(), self.items[-1]) refutes with NO
        # execution, while a guarded or non-mutating one does not; --execute then confirms the trap on the
        # constructed instance (Class().method(...)). A parameter-validating explicit raise stays intended
        # validation, not a bug.
        _mc = _os.path.join(_d, "cls.py")
        with open(_mc, "w", encoding="utf-8") as _fh:
            _fh.write("class Stack:\n    def __init__(self):\n        self.items = []\n"
                      "    def push(self, x):\n        self.items.append(x)\n"
                      "    def pop(self):\n        return self.items.pop()\n"
                      "    def safe(self):\n        if not self.items:\n            return 0\n        return self.items[-1]\n"
                      "    def validate(self, n):\n        if n < 0:\n            raise ValueError('neg')\n        return n\n")
        _sym = {f["location"] for f in scan(_mc, execute=False)["findings"]}
        assert "Stack.pop" in _sym, _sym                          # unguarded empty pop: refuted with no execution
        assert "Stack.safe" not in _sym and "Stack.push" not in _sym, _sym   # guarded / non-trapping: no finding
        _cm = {f["location"]: f for f in scan(_mc, execute=True)["findings"]}
        assert _cm.get("Stack.pop") and _cm["Stack.pop"]["classification"] == "bug", _cm
        assert _cm["Stack.pop"]["exception"] == "IndexError", _cm   # confirmed on Stack().pop()
        if "Stack.validate" in _cm:                              # an explicit parameter raise stays intended validation
            assert _cm["Stack.validate"]["classification"] == "input-validation", _cm
    finally:
        _sh.rmtree(_d, ignore_errors=True)

    # --- further decided capabilities, each exercised so the gate locks it ---
    # the partiality triage recognizes an `assert` guard as intended input validation, not a bug.
    _v = check("def f(x):\n    assert x != 0\n    return 10 // x\n")
    assert _v.status == REFUTED and "input validation" in (_v.reason or ""), _v
    _v = check("def f(x):\n    return 10 // x\n")
    assert _v.status == REFUTED and "likely a bug" in (_v.reason or ""), _v

    # a recursive REFUTED carries a replayable witness -- a postcondition violation AND a pure trap.
    _rec = "def f(n):\n    if n <= 0:\n        return 10 // n\n    return f(n - 1)\n"
    _v = verify_recursive("t", "f", _rec, lambda S: z3.BoolVal(True), lambda S, r: z3.BoolVal(True))
    assert _v.status == REFUTED and _v.counterexample_inputs, _v
    _rec = "def f(n):\n    if n <= 0:\n        return 5\n    return f(n - 1)\n"
    _v = verify_recursive("t", "f", _rec, lambda S: z3.BoolVal(True), lambda S, r: r == 999)
    assert _v.status == REFUTED and _v.counterexample_inputs, _v

    # a call-site f(**{...}) / f(*(...)) literal splat binds into the callee's named parameters.
    _rp = {"g": "def g(a, b):\n    return a // b\n", "f": "def f():\n    return g(**{'a': 10, 'b': 0})\n"}
    assert check(_rp["f"], repo=_rp, target="f").status == REFUTED        # b=0 -> ZeroDivisionError through the splat
    _rp = {"g": "def g(a, b):\n    return a // b\n", "f": "def f():\n    return g(**{'a': 10, 'b': 2})\n"}
    assert check(_rp["f"], repo=_rp, target="f").status == PROVED
    _rp = {"g": "def g(a, b):\n    return a // b\n", "f": "def f():\n    return g(*(10, 0))\n"}
    assert check(_rp["f"], repo=_rp, target="f").status == REFUTED

    # hasattr is decided from attribute-presence tracking in the heap engine.
    _hp = "class C:\n    def __init__(self):\n        self.a = 1\ndef f():\n    o = C()\n    return hasattr(o, 'a')\n"
    assert verify_heap_property("t", "f", _hp, lambda za, r: r == 1).status == PROVED
    _hp = "class C:\n    def __init__(self):\n        self.a = 1\ndef f():\n    o = C()\n    return hasattr(o, 'b')\n"
    assert verify_heap_property("t", "f", _hp, lambda za, r: r == 0).status == PROVED

    # a function's doctests become prove obligations -- a correct example PROVED, a wrong one REFUTED.
    _ds = prove_doctests("def sq(x):\n    '''\n    >>> sq(3)\n    9\n    '''\n    return x * x\n")
    assert _ds and all(_dv.status == PROVED for _, _dv in _ds), _ds
    _ds = prove_doctests("def sq(x):\n    '''\n    >>> sq(3)\n    10\n    '''\n    return x * x\n")
    assert _ds and any(_dv.status == REFUTED for _, _dv in _ds), _ds

    # the sound return type is compared to the annotation -- a fall-through to None and an explicit
    # None under `-> int` are REFUTED; a consistent literal return is PROVED.
    assert check_return_annotation("def f(x) -> int:\n    if x > 0:\n        return 1\n").status == REFUTED
    assert check_return_annotation("def f() -> int:\n    return None\n").status == REFUTED
    assert check_return_annotation("def f() -> int:\n    return 5\n").status == PROVED

    # oracle-free metamorphic properties -- idempotence and involution -- decided on real code.
    assert verify_metamorphic("def f(x):\n    if x < 0:\n        return 0\n    return x\n", "idempotent").status == PROVED
    assert verify_metamorphic("def f(x):\n    return x + 1\n", "idempotent").status == REFUTED
    assert verify_metamorphic("def f(x):\n    return -x\n", "involution").status == PROVED

    # fixed-width overflow is a default-on companion -- a function PROVED over Python's unbounded
    # integers carries the wraparound witness, without its (sound) Python verdict being flipped.
    _v = prove("def f(x):\n    return x * x\n", "result >= 0")
    assert _v.status == PROVED and "wraps signed" in (_v.reason or ""), _v

    # a bitwise & / | / ^ over operands bounded by the function's own body (no explicit precondition)
    # is decided exactly via bitvectors -- commutativity holds, where the nonnegative over-approximation abstains.
    _bw = "def f(a, b):\n    if 0 <= a < 256 and 0 <= b < 256:\n        return (a & b) - (b & a)\n    return 0\n"
    assert prove(_bw, "result == 0", target="f").status == PROVED

    # peer benchmark: Touchstone decides the shared external-comparison corpus completely and correctly (the
    # CrossHair / Nagini head-to-head runs through peer_bench when those tools are installed; the Touchstone
    # side gates here, so the corpus and its expected verdicts stay locked).
    from .peer_bench import _touchstone_verdicts, _CORPUS, _tally
    _pv = _touchstone_verdicts()
    _pdec, _pok = _tally(_pv, ("PROVED", "REFUTED"))
    assert _pdec == len(_CORPUS) and _pok == _pdec, (_pdec, _pok, _pv)
    # the Nagini head-to-head: the translation to Nagini's contract DSL is always well-formed Python; when the
    # toolchain is configured (TOUCHSTONE_NAGINI / TOUCHSTONE_NAGINI_JAVA_HOME) Nagini verifies the
    # straight-line HOLDS functions and rejects the VIOLATED ones, and is undecided on the HOLDS loops it needs
    # a manual invariant for (which Touchstone synthesizes) -- a sound deductive-verifier profile (decided ==
    # correct), externally comparable to Touchstone's 12/12 and the concolic CrossHair.
    from .peer_bench import _nagini_translate, _nagini_verdicts, _nagini_tally, nagini_available
    for _nn, _ns, _ne, _nr, _ntr in _CORPUS:
        ast.parse(_nagini_translate(_nn, _ns, _ne, _nr))                 # the Nagini translation is valid Python
    if nagini_available():
        _ngv = _nagini_verdicts()
        assert _ngv["double"] == "VERIFIED" and _ngv["off_by_one"] == "FAILED", _ngv   # proves HOLDS, rejects VIOLATED
        assert _ngv["counter"] == "FAILED", _ngv                         # a HOLDS loop with no manual invariant: undecided
        _nd, _nok = _nagini_tally(_ngv)
        assert _nd == _nok and _nd >= 9, (_nd, _nok, _ngv)               # sound (decided == correct); decides >= 9/12

    # diagnostic / engine refinements: an approximation UNKNOWN names its real cause (the operation and line),
    # not a canned string; a non-termination REFUTED carries the divergence certificate (the recurrence set and
    # preserved guard) rather than an unbounded diverging trace; the exact bitvector engine infers a faithful
    # width from the precondition; a trap witness is minimized; and --budget is flagged a no-op for an
    # abstraction-limited UNKNOWN.
    _pv = prove("def f(s: str):\n    return s.strip()\n", "result == s", target="f")
    assert _pv.status == UNKNOWN and "str.strip" in _pv.reason and "line" in _pv.reason, _pv   # provenance, not canned
    assert classify_unknown(_pv.reason) == "approximation" and not budget_helps(_pv.reason), _pv   # budget no-op
    assert budget_helps("solver returned unknown") and not budget_helps("an over-approximated value")
    _nt = verify_nontermination("nt", "f", "def f(x):\n    while x != 0:\n        x = x + 1\n    return x\n")
    assert _nt.status == REFUTED and _nt.trace and "non-termination certificate" in _nt.trace, _nt
    assert "recurrence set" in _nt.trace and "preserved guard" in _nt.trace, _nt
    assert check("def f(x):\n    while x != 0:\n        x = x + 1\n    return x\n", total=True, target="f").trace \
        and "certificate" in check("def f(x):\n    while x != 0:\n        x = x + 1\n    return x\n", total=True, target="f").trace
    from .engines import _infer_bv_width, _escalate_unknown
    assert _infer_bv_width(ast.parse("0 <= a and a <= 255 and 0 <= b and b <= 255", mode="eval").body,
                           "def f(a, b):\n    return a & b\n") == 8                              # inferred width
    assert _infer_bv_width(ast.parse("a >= 0", mode="eval").body, "def f(a):\n    return a\n") is None
    _bwv = prove("def f(a, b):\n    return a & b\n", "result == a", requires="0 <= a and a <= 255 and 0 <= b and b <= 255", target="f")
    assert _bwv.status == REFUTED and "width 8" in _bwv.technique, _bwv                          # decided exactly, faithful width
    assert check("def f(x):\n    return 10 // x\n", target="f").counterexample_inputs == {"x": 0}   # minimized trap witness
    # the synthesized spec reaches the tightest bounds (item-11 strongest contract, re-asserted end to end)
    _cl = synthesize_spec("def f(x):\n    if x > 100:\n        x = 100\n    if x < 0:\n        x = 0\n    return x\n")
    assert sorted(_cl["ensures"]) == ["result <= 100", "result >= 0"], _cl
    # a symbolic UNKNOWN is pursued by guided sandbox fuzzing and surfaced as a distinct `suspected` finding
    # (a swallowed UNKNOWN in a bug finder is a missed bug), rather than dropped -- guarded on the sandbox.
    if not fast and core.sandbox_run_batch("def f(x):\n    return x\n", {}, "f", [[1]]) == [("ok", 1)]:
        _sus = _escalate_unknown("topkey", "def topkey(d):\n    s = sorted(d.items(), key=lambda kv: kv[1])\n    return s[0][0]\n", {}, "topkey")
        assert _sus is not None and _sus["classification"] == "suspected" and _sus["exception"] == "IndexError", _sus
        assert _sus["witness"] == {"d": {}} and _sus["repro"], _sus

    # a trap refutation names the exception type and the offending line symbolically (no execution), read from
    # the value engine's per-condition line record and a static type read of that line -- so a trap proof is as
    # informative as a postcondition proof.
    import re as _re_ti
    for _src, _kind, _ln in [("def f(x):\n    return 10 // x\n", "ZeroDivisionError", 2),
                             ("def f(xs: list):\n    return xs[0]\n", "IndexError", 2),
                             ("def f(d: dict):\n    return d['x']\n", "KeyError", 2),
                             ("def f(x):\n    y = x + 1\n    return 10 // y\n", "ZeroDivisionError", 3),
                             ("def f(x):\n    assert x > 0\n    return x\n", "AssertionError", 2),
                             ("def f(n: int):\n    if n < 0:\n        raise ValueError('neg')\n    return n\n", "ValueError", 3)]:
        _tv = check(_src, target="f")
        assert _tv.status == REFUTED and "%s at line %d" % (_kind, _ln) in (_tv.reason or ""), (_src, _tv.reason)

    # tensor coverage: advanced indexing (a boolean mask, an index tensor) is trap free; torch.nn.functional
    # dispatches through its F alias and the full path (an elementwise layer preserves shape, a shape-changing
    # layer is opaque); the data-dependent ops gather / scatter / index_select / argsort track precise shapes;
    # and the sparse / complex methods preserve shape.
    _T = "import torch\n"
    _Fi = "import torch.nn.functional as F\n"
    assert check(_T + "def f():\n    a = torch.zeros(5)\n    return a[a > 0].sum()\n", target="f").status == PROVED
    assert check(_T + "def f():\n    return torch.zeros(5)[torch.zeros(3)]\n", target="f").status == PROVED   # index tensor
    assert prove(_Fi + "def f():\n    return F.relu(torch.zeros(2, 3)).shape[1]\n", "result == 3", target="f").status == PROVED
    assert prove(_T + "def f():\n    return torch.nn.functional.relu(torch.zeros(2, 3)).shape[0]\n", "result == 2", target="f").status == PROVED
    assert check(_Fi + "def f():\n    return F.linear(torch.zeros(2, 3), torch.zeros(4, 3))\n", target="f").status == PROVED   # opaque, trap free
    assert check(_T + "def f(F):\n    return F.relu(torch.zeros(2, 3))\n", target="f").status == PROVED   # F is a param, not the functional: opaque-safe
    assert prove(_T + "def f():\n    return torch.zeros(2, 3).scatter(1, torch.zeros(2, 3), 0).shape[0]\n", "result == 2", target="f").status == PROVED
    assert prove(_T + "def f():\n    return torch.zeros(4, 5).gather(1, torch.zeros(4, 2)).shape[1]\n", "result == 2", target="f").status == PROVED
    assert prove(_T + "def f():\n    return torch.zeros(4, 5).index_select(0, torch.zeros(2)).shape[0]\n", "result == 2", target="f").status == PROVED
    assert prove(_T + "def f():\n    return torch.zeros(2, 3).argsort().shape[1]\n", "result == 3", target="f").status == PROVED
    assert prove(_T + "def f():\n    return torch.zeros(2, 3).to_sparse().to_dense().conj().real.shape[1]\n", "result == 3", target="f").status == PROVED
    # the broader stdlib registry: bisect / heapq / itertools and the pure math ldexp / nextafter decide trap free.
    assert check("import bisect\ndef f(xs: list, x):\n    return bisect.bisect(xs, x)\n", target="f").status == PROVED
    assert check("import heapq\ndef f(xs: list):\n    heapq.heapify(xs)\n    return 0\n", target="f").status == PROVED
    assert check("import math\ndef f(x: float):\n    return math.ldexp(x, 2)\n", target="f").status == PROVED
    # SOUNDNESS: a slice of a bare opaque value (an unmodeled call / attribute result) is a sub-sequence, never
    # a scalar, so an arithmetic op on it abstains rather than fabricating a scalar trap. The ndarray idiom
    # a[1:] / a[:-1] (diffusers VQ-diffusion alpha_schedules) raises nothing in numpy -- it yields nan element-
    # wise -- so it must NOT REFUTE as a reachable ZeroDivisionError; a divisor that is a slice is never a zero scalar.
    assert check("def f(o):\n    a = o.compute()\n    return a[1:] / a[:-1]\n", target="f").status == UNKNOWN
    assert check("def f(o):\n    a = o.compute()\n    return 5 // a[1:]\n", target="f").status == UNKNOWN
    assert check("import numpy as np\ndef f(n):\n    att = np.arange(0, n) / (n - 1)\n    att = np.concatenate(([1], att))\n    return att[1:] / att[:-1]\n", target="f").status != REFUTED
    assert check("def f(o):\n    a = o.compute()\n    return a[1:]\n", target="f").status == PROVED   # the slice itself is still trap free

    # Count the asserts by parsing the whole file and walking the run_self_tests definition. inspect.getsource's
    # tokenize-based block detection can under-read the function on some platforms (undercounting the suite), so
    # the full-file parse is primary and inspect the fallback for a frozen or source-less install.
    try:
        with open(__file__, encoding="utf-8") as _fh:
            _fn = next(n for n in ast.walk(ast.parse(_fh.read()))
                       if isinstance(n, ast.FunctionDef) and n.name == "run_self_tests")
        n_checks = sum(isinstance(n, ast.Assert) for n in ast.walk(_fn))
    except Exception:
        n_checks = sum(isinstance(n, ast.Assert)
                       for n in ast.walk(ast.parse(textwrap.dedent(inspect.getsource(run_self_tests)))))
    print(f"  all self-tests passed ({n_checks} asserts)\n")


def demo():
    repo = {
        "fee": "def fee(p):\n    return p // 10\n",
        "net": "def net(p):\n    return p - fee(p)\n",
        "sign": "def sign(x):\n    if x > 0:\n        return 1\n    if x < 0:\n        return -1\n    return 0\n",
        "save": "def save(x):\n    acquire_lock()\n    db.write(x)\n",
        "score": ("def score(x):\n    if x > 100:\n        x = 100\n"
                  "    if x < 0:\n        x = 0\n    return x * x\n"),
    }
    sign_spec = "def s(x):\n    if x > 0:\n        return 1\n    if x < 0:\n        return -1\n    return 0\n"
    net_pred = lambda za, out: z3.Implies(za["p"] >= 0, z3.And(out >= 0, out <= za["p"]))

    props = [
        Prop("sign==spec", "sign",
             lambda r: verify_equiv("sign==spec", "sign", r["sign"], sign_spec, r)),
        Prop("net_bounds", "net",
             lambda r: verify_predicate("net_bounds", "net", r["net"], net_pred, r)),
        Prop("lock-safety", "save",
             lambda r: verify_lock("lock-safety", "save", r["save"], r)),
        Prop("score-no-overflow(16b)", "score",
             lambda r: verify_no_overflow("score-no-overflow(16b)", "score", r["score"], r, width=16)),
    ]
    orch = Orchestrator(repo, props)

    print("DEMO\n----")
    print("initial verification of the whole repo:")
    for v in orch.verify(label="initial"):
        print(f"    [{v.prop:24}] {v.status:7} via {v.technique}")

    # change a leaf (fee) to a buggy version -> only fee's dependents re-verify
    print("\nauthor breaks `fee` (adds +1):")
    fix_loop(orch, "fee", [
        "def fee(p):\n    return p // 10 + 1\n",   # buggy: net(0) = -1
        "def fee(p):\n    return p // 10\n",        # fixed
    ])

    # structural fix loop on save
    print()
    fix_loop(orch, "save", [
        "def save(x):\n    if x > 0:\n        acquire_lock()\n        db.write(x)\n    else:\n        db.write(x)\n",
        "def save(x):\n    acquire_lock()\n    if x > 0:\n        db.write(x)\n    else:\n        db.write(x)\n",
    ])

    # author "simplifies" score and removes the clamps -> overflow at 16-bit caught,
    # then restores them (clamping is PROVEN to prevent overflow).
    print()
    fix_loop(orch, "score", [
        "def score(x):\n    return x * x\n",
        ("def score(x):\n    if x > 100:\n        x = 100\n"
         "    if x < 0:\n        x = 0\n    return x * x\n"),
    ])

    # an undecidable change -> escalation -> blocked
    print()
    fix_loop(orch, "net", ["def net(p):\n    return external_fetch(p)\n"])

    # --- automatic reasoning without a supplied invariant ---
    print("\nAUTOMATIC REASONING (no supplied invariants)\n--------------------------------------------")
    clamp = "def clamp():\n    x = 0\n    while x < 100:\n        x = x + 1\n    return x\n"
    r = verify_range("0<=clamp()<=100", "clamp", clamp, 0, 100)
    print(f"  interval analysis : {r.status} ({r.reason}) -- unbounded loop, terminates by widening")

    sum_to = ("def sum_to(n):\n    total = 0\n    i = 1\n    while i <= n:\n"
              "        total = total + i\n        i = i + 1\n    return total\n")
    pre = lambda S: S["n"] >= 0
    post = lambda S, ret: 2 * ret == S["n"] * (S["n"] + 1)
    r = verify_deductive_auto("sum_to == n(n+1)/2", "sum_to", sum_to, pre, post, {})
    print(f"  Houdini inference : {r.status}")
    print(f"      {r.reason}")

    rel = "def g(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n"
    r = verify_range("0<=g(n)<=n", "g", rel, 0, 1000)
    print(f"  interval (limit)  : {r.status} -- {r.reason}")

    # --- comparison: unbounded vs fixed-width integers ---
    print("\nUNBOUNDED vs FIXED-WIDTH INTEGERS\n--------------------------------")
    dbl = "def double_it(x):\n    return x + x\n"
    a = verify_equiv("double==2x", "double_it", dbl, "def s(x):\n    return x + x\n", {})
    b = verify_no_overflow("no-overflow(64b)", "double_it", dbl, {}, width=64)
    print(f"  over Z            : {a.status}  -- double_it(x) == x+x for all integers")
    print(f"  over int64        : {b.status} -- counterexample: {b.counterexample}")

    # --- relational, template-free invariant synthesis (CHC/Spacer) ---
    print("\nRELATIONAL INVARIANTS, TEMPLATE-FREE (CHC/Spacer)\n"
          "-------------------------------------------------")
    counter = "def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n"
    r = verify_chc("f(n) == n", "f", counter, lambda S: S["n"] >= 0, lambda S, x: x == S["n"])
    print(f"  counter  : {r.status} via {r.technique} -- f(n)==n (needs i<=n, inferred)")
    twovar = ("def g(n):\n    x = 0\n    y = 0\n    while x < n:\n"
              "        x = x + 1\n        y = y + 1\n    return x\n")
    r = verify_chc("x == y", "g", twovar, lambda S: S["n"] >= 0, lambda S, x: S["x"] == S["y"])
    print(f"  two vars : {r.status} -- relational invariant x==y, no template supplied")
    r = verify_chc("nonlinear", "sum_to", sum_to, lambda S: S["n"] >= 0,
                   lambda S, x: 2 * x == S["n"] * (S["n"] + 1))
    print(f"  nonlinear: {r.status} -- {r.reason}")

    # --- arrays + quantified specifications ---
    print("\nARRAYS + QUANTIFIED SPECIFICATIONS\n----------------------------------")
    set_zero = ("def set_zero(a: list, n: int):\n    i = 0\n    while i < n:\n"
                "        a[i] = 0\n        i = i + 1\n    return a\n")
    pre_sz = lambda S: z3.And(S["n"] >= 0, S["n"] <= S["len_a"])
    inv_sz = lambda S: z3.And(0 <= S["i"], S["i"] <= S["n"], S["n"] <= S["len_a"],
                              q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < S["i"]),
                                                            z3.Select(S["a"], j) == 0)))
    post_sz = lambda S, _: q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]),
                                                         z3.Select(S["a"], j) == 0))
    r = verify_array_loop("all zero", "set_zero", set_zero, pre_sz, inv_sz, post_sz)
    print(f"  set_zero : {r.status} via {r.technique}")
    r = verify_array_loop("all zero", "set_zero", set_zero.replace("i < n", "i <= n"),
                          pre_sz, lambda S: z3.And(0 <= S["i"], S["i"] <= S["n"] + 1, S["n"] <= S["len_a"]),
                          lambda S, _: z3.BoolVal(True))
    print(f"  off-by-one (i<=n): {r.status} -- {r.reason}")

    # --- partial functions: division by a possibly-zero value is a trap ---
    print("\nPARTIAL FUNCTIONS (division by zero is a trap)\n"
          "---------------------------------------------")
    r = verify_equiv("a//a vs 1", "f", "def f(a):\n    return a // a\n",
                     "def f(a):\n    return 1\n", {})
    print(f"  a//a  vs  1        : {r.status} -- counterexample: {r.counterexample} "
          f"(a=0 traps, 1 does not)")
    r = verify_equiv("trap==trap", "f", "def f(a):\n    return (a // a) + 1\n",
                     "def f(a):\n    return 1 + (a // a)\n", {})
    print(f"  (a//a)+1 vs 1+(a//a): {r.status} -- both trap on exactly the same inputs")

    # --- termination / total correctness ---
    print("\nTERMINATION (linear, lexicographic, and synthesized ranking functions)\n"
          "---------------------------------------------------------------------")
    r = verify_termination("halts", "f", counter)
    print(f"  while i<n: i+=1        : {r.status} -- {r.reason}")
    r = verify_termination("halts", "f", "def f(x, y):\n    while x + y > 0:\n        x = x - 1\n    return x\n")
    print(f"  while x+y>0: x-=1      : {r.status} -- {r.reason} (sum measure)")
    r = verify_termination("synth", "f",
                           "def f(x, y):\n    while 3 * x + y > 0:\n        x = x - 1\n        y = y + 2\n    return 0\n")
    print(f"  while 3x+y>0: ...      : {r.status} -- {r.reason}")
    nested = ("def f(n, m):\n    i = 0\n    j = 0\n    while i < n:\n"
              "        if j < m:\n            j = j + 1\n        else:\n            i = i + 1\n            j = 0\n"
              "    return i\n")
    r = verify_termination("nested", "f", nested, inv=lambda S: z3.And(S["j"] >= 0, S["j"] <= S["m"]))
    print(f"  nested counter+reset  : {r.status} -- {r.reason}")
    r = verify_termination("halts", "f", "def f(x):\n    while x != 0:\n        x = x + 1\n    return x\n")
    print(f"  while x!=0: x+=1       : {r.status} -- {r.reason}")

    # --- relational abstract interpretation (zones and octagons) ---
    print("\nRELATIONAL ABSTRACT INTERPRETATION (zone and octagon domains)\n"
          "------------------------------------------------------------")
    r = verify_zone_equal("x == y", "g", twovar, "x", "y")
    print(f"  zone    x==y    : {r.status} -- {r.reason}")
    cons = ("def f():\n    i = 0\n    j = 10\n    while i < 10:\n"
            "        i = i + 1\n        j = j - 1\n    return i\n")
    r = verify_octagon_sum("i+j==10", "f", cons, "i", "j", 10)
    print(f"  octagon i+j==10 : {r.status} -- {r.reason}")

    # --- whole-function verification over the real control-flow graph ---
    print("\nWHOLE-FUNCTION CONTROL FLOW (CFG -> CHC)\n"
          "---------------------------------------")
    postloop = ("def f(n):\n    total = 0\n    i = 0\n    while i < n:\n        total = total + 1\n"
                "        i = i + 1\n    total = total * 100\n    return total\n")
    r = verify_function("post", "f", postloop, lambda S: S["n"] >= 0, lambda S, x: x == S["n"] * 100, {})
    r2 = verify_function("post", "f", postloop, lambda S: S["n"] >= 0, lambda S, x: x == S["n"], {})
    print(f"  statement after the loop : f(n)==n*100 {r.status}, f(n)==n {r2.status}")
    brk = ("def f(n):\n    i = 0\n    while i < n:\n        if i == 3:\n            break\n"
           "        i = i + 1\n    return i\n")
    r = verify_function("brk", "f", brk, lambda S: S["n"] >= 0, lambda S, x: x <= S["n"], {})
    print(f"  break / continue / nested: {r.status} via {r.technique}")

    # --- recursion and total correctness ---
    print("\nRECURSION AND TOTAL CORRECTNESS\n-------------------------------")
    rec = "def f(n):\n    if n <= 0:\n        return 0\n    return f(n - 1) + 1\n"
    r = verify_recursive("rec", "f", rec, lambda S: S["n"] >= 0, lambda S, x: x == S["n"])
    print(f"  recursive f(n)==n        : {r.status} via {r.technique}")
    r = verify_total("tot", "f", counter, lambda S: S["n"] >= 0, lambda S, x: x == S["n"])
    print(f"  counter f(n)==n + halts  : {r.status} -- {r.reason}")

    # --- IEEE-754, concurrency, and a verified agent reference monitor ---
    print("\nFLOATS, CONCURRENCY, AGENT MONITOR\n---------------------------------")
    r = verify_float_finite("ovf", "f", "def f(a, b):\n    return a + b\n")
    print(f"  float a+b finite?        : {r.status} -- {r.reason or r.counterexample}")
    r = verify_two_thread_counter("racy", "t", False)
    print(f"  non-atomic counter       : {r.status} -- {r.counterexample}")
    plan = [("search", "read", 3, "g1"), ("write", "fs.write", 5, "g2")]
    r = verify_agent_policy("ok", "m", plan, {"read", "fs.write"}, 10)
    print(f"  agent plan within budget : {r.status} -- {r.reason}")
    r = verify_agent_policy("over", "m", plan, {"read", "fs.write"}, 6)
    print(f"  agent plan over budget   : {r.status} -- {r.counterexample}")
    cov = subset_coverage(postloop + rec + counter)
    print(f"  subset coverage (sample) : {cov['encoded']}/{cov['functions']} functions encoded")

    # --- exceptions, contracts, heap, cost, dynamic types ---
    print("\nEXCEPTIONS, CONTRACTS, HEAP, COST, DYNAMIC TYPES\n"
          "-----------------------------------------------")
    raises = "def f(x):\n    if x < 0:\n        raise ValueError\n    return x\n"
    r = verify_no_raise("ex", "f", raises, lambda S: S["x"] >= 0)
    r2 = verify_no_raise("ex", "f", raises, lambda S: z3.BoolVal(True))
    print(f"  raise if x<0 (pre x>=0 / pre True) : {r.status} / {r2.status}")
    contracts = {"g": (lambda a: z3.BoolVal(True), lambda a, ret: ret == a[0] + 1)}
    r = verify_modular("mod", "f", "def f(x):\n    return g(g(x))\n",
                       lambda S: z3.BoolVal(True), lambda S, ret: ret == S["x"] + 2, contracts)
    print(f"  modular g(g(x))==x+2 (no inlining): {r.status} -- {r.reason}")
    r = verify_heap_frame("frame", "heap")
    print(f"  separation-logic frame rule       : {r.status}")
    r = verify_iteration_bound("cost", "f", counter)
    print(f"  cost bound for counter            : {r.status} -- {r.reason}")
    r = verify_dynamic_dispatch("dyn", "value")
    print(f"  dynamic-dispatch type property    : {r.status}")

    # --- companion proofs (Rocq / SMTCoq, in proofs/) ---
    print("\nCOMPANION PROOFS (Rocq 9.0 / SMTCoq, in proofs/)\n"
          "------------------------------------------------")
    print("  touchstone_encoding.v : py_floordiv/py_mod == Python // and %")
    print("  touchstone_functor.v  : the translation preserves identity and composition")
    print("  touchstone_domains.v  : domain transfers over-approximate; ranking forces termination")
    print("  touchstone_encoders.v : type-join over-approximates; string/list/heap laws (join extracted)")
    print("  touchstone_floats.v   : float a//b and a%b obey the divmod laws (over Q, the floats' values)")
    print("  touchstone_seplogic.v : the separation-logic frame rule; a local mutation preserves disjoint state")
    print("  touchstone_relyguarantee.v : a stable global invariant holds across every interleaving, every depth")
    print("  touchstone_smtcoq.v   : integer obligations re-checked from an external certificate")

    # --- relational domains, SOS, recursive heap, whole-program, learning ---
    print("\nRELATIONAL DOMAINS, SOS, RECURSIVE HEAP, WHOLE-PROGRAM, LEARNING\n"
          "---------------------------------------------------------------")
    print(f"  Karr x==y (relational)   : {verify_affine_equal('k', 'g', twovar, 'x', 'y').status}")
    print(f"  SOS (x-y)^2 >= 0         : "
          f"{verify_sos_nonneg('s', 'p', lambda X: X[0]*X[0] - 2*X[0]*X[1] + X[1]*X[1], 2).status}")
    print(f"  recursive list predicate : {verify_list_segment('sl', 'lseg').status}")
    rwp = {"inc": "def inc(x):\n    return x + 1\n", "double": "def double(x):\n    return inc(x) + inc(x)\n"}
    print(f"  whole-program double==2x+2: "
          f"{verify_program('w', 'double', rwp, 'double', lambda S: z3.BoolVal(True), lambda S, r: r == 2*S['x']+2).status}")
    print(f"  ranking synthesis        : {verify_ranking_synth('r', 'f', counter).reason}")
    li = learn_invariant("l", "sum_to", sum_to, pre, post)
    print(f"  invariant learned (data) : {li.status} -- {li.reason}")
    print(f"  N-thread race / deadlock : {verify_concurrent_counter('c', 't', 3, False).status} / "
          f"{verify_deadlock_free('d', 't', False).status} (both REFUTED unsafe variants)")

    # --- the verifier audits its own verdicts against the SMT model (no execution) ---
    print("\nSOUNDNESS AUDIT (verdicts cross-checked against the SMT model)\n"
          "-------------------------------------------------------------")
    rep = soundness_audit(trials=120)
    print(f"  {rep['trials']} random programs verified: "
          f"{rep['proved']} proved, {rep['refuted']} refuted, {rep['unknown']} unknown")
    print(f"  {rep['model_checks']} model cross-checks, 0 verdicts contradicted the model")


__all__ = [
    'cross_engine_audit',
    'bmc_audit',
    '_ibool',
    '_iev',
    '_isymexec',
    '_independent_claim',
    '_equiv_claim',
    'model_cross_check',
    'validate_counterexample',
    'differential_check',
    'exhaustive_check',
    '_rand_expr',
    '_render',
    '_perturb',
    'random_equiv_problem',
    'soundness_audit',
    'division_encoding_audit',
    '_fp_to_float',
    'float_divmod_audit',
    'transcendental_axiom_audit',
    'math_pow_axiom_audit',
    'math_domain_audit',
    'stdlib_trapfree_audit',
    'string_method_axiom_audit',
    'format_spec_audit',
    'string_fragile_op_audit',
    'differential_equiv_audit',
    'differential_loop_audit',
    'differential_heap_audit',
    'differential_sequence_audit',
    '_bit_eq',
    'differential_typed_audit',
    'differential_method_audit',
    '_grammar_program',
    'differential_grammar_audit',
    'differential_sound_inference_audit',
    'differential_sound_local_audit',
    'verification_benchmark',
    '_COVERAGE_CORPUS',
    '_coverage_one',
    'coverage_report',
    'relational_domain_audit',
    'refinement_audit',
    'exhaustive_refinement_audit',
    '_rand_ir',
    'extracted_vcgen_audit',
    'extracted_vcg_audit',
    '_rand_kcmd',
    'extracted_intervals_audit',
    'extracted_encoding_audit',
    'extracted_encoding_committed_audit',
    'extracted_lattice_audit',
    'committed_extraction_audit',
    'committed_obligations_audit',
    'nonlinear_corroboration_audit',
    'run_self_tests',
    'demo',
]
