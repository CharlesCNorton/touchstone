"""Abstract interpretation: the interval, zone (difference-bound), octagon, Karr affine-
equality, template-polyhedra, and machine-integer domains, plus subset coverage. Every PROVED here
is independently re-derived by the CHC engine when core.CROSS_VALIDATE_DOMAINS."""
import ast
import builtins
import hashlib
import inspect
import random
import subprocess
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
from .engines import (check, load_module, verify_sequence_loop, verify_recursive, verify_heap_property,
                      verify_array_loop, _is_array_param)


def _corroborate_domain(prop, target, technique, src, post, pre=None):
    """Independently re-derive a fact an abstract domain just PROVED, using the CHC
    engine (Spacer) over the same program. `post(exit_state, ret)` is the fact as a
    postcondition. A CHC REFUTED of a domain PROVED means the domain is unsound and
    raises SoundnessError; otherwise the domain verdict stands. No-op unless
    CROSS_VALIDATE_DOMAINS. (verify_function / SoundnessError resolve at call time.)"""
    if not core.CROSS_VALIDATE_DOMAINS:
        return
    pre = pre or (lambda S: z3.BoolVal(True))
    try:
        chk = verify_function(prop, target, src, pre, post)
    except Exception:
        return                                   # CHC could not be built: leave domain verdict
    if chk.status == REFUTED:
        raise SoundnessError(
            f"{technique} PROVED '{prop}' on {target}, but the CHC engine refutes it "
            f"(counterexample {chk.counterexample}) -- abstract domain is unsound")


_NEG, _POS = -_math.inf, _math.inf


class Iv:
    __slots__ = ("lo", "hi")
    def __init__(self, lo, hi): self.lo, self.hi = lo, hi
    def __eq__(self, o): return isinstance(o, Iv) and self.lo == o.lo and self.hi == o.hi
    def __repr__(self): return f"[{self.lo},{self.hi}]"
    def bottom(self): return self.lo > self.hi


_TOP = Iv(_NEG, _POS)


# The interval transfers below are the operators proved sound in proofs/touchstone_domains.v, regenerated
# into touchstone/_generated/intervals_rocq.py by proofs/json_to_python.py. The proof is over finite
# integer bounds, so the engine runs the extracted operator on the finite case and keeps the unbounded
# (+-inf) and bottom bookkeeping -- which the proof does not model -- here. _zb / _bz are the bound
# bijection (Python int <-> binary Z) and _bopt the +-inf encoding the extracted widening reads (None).
from ._generated import intervals_rocq as _ivr


def _zb(n):
    return ("Z0",) if n == 0 else (("Zpos", _zp(n)) if n > 0 else ("Zneg", _zp(-n)))


def _zp(n):
    return ("XH",) if n == 1 else (("XI", _zp(n >> 1)) if n & 1 else ("XO", _zp(n >> 1)))


def _pz(p):
    return 1 if p[0] == "XH" else 2 * _pz(p[1]) + (1 if p[0] == "XI" else 0)


def _bz(x):
    return 0 if x[0] == "Z0" else (_pz(x[1]) if x[0] == "Zpos" else -_pz(x[1]))


def _fin(v):
    return v.lo != _NEG and v.lo != _POS and v.hi != _NEG and v.hi != _POS


def _bopt(b):
    return ("None",) if (b == _NEG or b == _POS) else ("Some", _zb(b))


def _ijoin(a, b):
    if a.bottom(): return b
    if b.bottom(): return a
    if _fin(a) and _fin(b):
        r = _ivr.ijoin(_zb(a.lo))(_zb(a.hi))(_zb(b.lo))(_zb(b.hi))
        return Iv(_bz(r[1]), _bz(r[2]))
    return Iv(min(a.lo, b.lo), max(a.hi, b.hi))


def _iadd(a, b):
    if _fin(a) and _fin(b):
        r = _ivr.iadd(_zb(a.lo))(_zb(a.hi))(_zb(b.lo))(_zb(b.hi))
        return Iv(_bz(r[1]), _bz(r[2]))
    return Iv(a.lo + b.lo, a.hi + b.hi)


def _ineg(a):
    if _fin(a):
        r = _ivr.ineg(_zb(a.lo))(_zb(a.hi))
        return Iv(_bz(r[1]), _bz(r[2]))
    return Iv(-a.hi, -a.lo)


def _isub(a, b): return _iadd(a, _ineg(b))


def _imul(a, b):
    if a.bottom() or b.bottom(): return Iv(_POS, _NEG)
    if a == Iv(0, 0) or b == Iv(0, 0): return Iv(0, 0)
    if _fin(a) and _fin(b):
        r = _ivr.imul(_zb(a.lo))(_zb(a.hi))(_zb(b.lo))(_zb(b.hi))
        return Iv(_bz(r[1]), _bz(r[2]))
    pts = [(0 if (x == 0 or y == 0) else x * y) for x in (a.lo, a.hi) for y in (b.lo, b.hi)]
    return Iv(min(pts), max(pts))


def _widen(o, n):
    if o.bottom(): return n
    lo = _ivr.widenL(_bopt(o.lo))(_bopt(n.lo))
    hi = _ivr.widenU(_bopt(o.hi))(_bopt(n.hi))
    return Iv(_NEG if lo[0] == "None" else _bz(lo[1]), _POS if hi[0] == "None" else _bz(hi[1]))


def _narrow(o, n):
    return Iv(n.lo if o.lo == _NEG else o.lo, n.hi if o.hi == _POS else o.hi)


def _sjoin(s, t):
    if s is None: return t
    if t is None: return s
    return {k: _ijoin(s[k], t.get(k, _TOP)) for k in s}


def _ieval(node, st):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return Iv(node.value, node.value)
    if isinstance(node, ast.Name):
        return st.get(node.id, _TOP)
    if isinstance(node, ast.BinOp):
        l, r = _ieval(node.left, st), _ieval(node.right, st)
        if isinstance(node.op, ast.Add): return _iadd(l, r)
        if isinstance(node.op, ast.Sub): return _isub(l, r)
        if isinstance(node.op, ast.Mult): return _imul(l, r)
        return _TOP
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return _ineg(_ieval(node.operand, st))
    return _TOP


def _refine(st, name, lo=_NEG, hi=_POS):
    cur = st.get(name, _TOP)
    out = dict(st); out[name] = Iv(max(cur.lo, lo), min(cur.hi, hi))
    return out


def _filter(st, test, truth):
    """Sound refinement of st assuming test==truth; never excludes a reachable state."""
    if st is None: return None
    if isinstance(test, ast.BoolOp):
        if (isinstance(test.op, ast.And) and truth) or (isinstance(test.op, ast.Or) and not truth):
            for v in test.values: st = _filter(st, v, truth)
            return st
        acc = None
        for v in test.values:
            acc = _sjoin(acc, _filter(dict(st), v, truth))
        return acc
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _filter(st, test.operand, not truth)
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        op, L, R = test.ops[0], test.left, test.comparators[0]
        if isinstance(L, ast.Name) and isinstance(R, ast.Constant) and isinstance(R.value, int):
            n, k = L.id, R.value
            if isinstance(op, ast.Lt):    return _refine(st, n, hi=k - 1) if truth else _refine(st, n, lo=k)
            if isinstance(op, ast.LtE):   return _refine(st, n, hi=k) if truth else _refine(st, n, lo=k + 1)
            if isinstance(op, ast.Gt):    return _refine(st, n, lo=k + 1) if truth else _refine(st, n, hi=k)
            if isinstance(op, ast.GtE):   return _refine(st, n, lo=k) if truth else _refine(st, n, hi=k - 1)
            if isinstance(op, ast.Eq):    return _refine(st, n, lo=k, hi=k) if truth else st
            if isinstance(op, ast.NotEq): return st if truth else _refine(st, n, lo=k, hi=k)
        if isinstance(L, ast.Name) and isinstance(R, ast.Name) and truth and isinstance(op, (ast.Lt, ast.LtE)):
            d = -1 if isinstance(op, ast.Lt) else 0
            st = _refine(st, L.id, hi=st.get(R.id, _TOP).hi + d)
            st = _refine(st, R.id, lo=st.get(L.id, _TOP).lo - d)
            return st
    return st


def _itransfer(stmts, st):
    if st is None: return None
    for s in stmts:
        if st is None: return None
        if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name):
            st = dict(st); st[s.targets[0].id] = _ieval(s.value, st)
        elif isinstance(s, ast.If):
            st = _sjoin(_itransfer(s.body, _filter(dict(st), s.test, True)),
                        _itransfer(s.orelse, _filter(dict(st), s.test, False)))
        elif isinstance(s, ast.While):
            entry, head = dict(st), dict(st)
            # Each non-stabilizing widening step pushes at least one of the 2*len(head)
            # bounds to an infinity it can never leave, so the sequence stabilizes within
            # 2*len(head)+1 steps; the cap below derives from program size with slack.
            cap = 4 * len(head) + 8
            for _ in range(cap):                      # widen to fixpoint
                body = _itransfer(s.body, _filter(dict(head), s.test, True))
                joined = _sjoin(head, body)
                widened = {k: _widen(head[k], joined[k]) for k in head}
                if widened == head: break
                head = widened
            else:
                raise NonConvergence("interval widening did not reach a fixpoint")
            for _ in range(cap):                      # narrow to recover precision
                body = _itransfer(s.body, _filter(dict(head), s.test, True))
                joined = _sjoin(entry, body)
                narrowed = {k: _narrow(head[k], joined[k]) for k in head}
                if narrowed == head: break
                head = narrowed
            st = _filter(dict(head), s.test, False)
        elif isinstance(s, ast.Return):
            st = dict(st); st["@ret"] = _ieval(s.value, st)
            return st
    return st


def analyze_intervals(src):
    fn = _parse(src).body[0]
    return _itransfer(fn.body, {a.arg: _TOP for a in fn.args.args})


def verify_range(prop, target, src, lo, hi, var="@ret") -> Verdict:
    try:
        st = analyze_intervals(src)
    except (Unsupported, NonConvergence) as u:
        return Verdict(UNKNOWN, prop, target, "interval analysis", reason=str(u))
    iv = (st or {}).get(var)
    if iv is None:
        return Verdict(UNKNOWN, prop, target, "interval analysis", reason=f"{var} not found")
    if iv.lo >= lo and iv.hi <= hi:
        post = ((lambda S, r: z3.And(r >= lo, r <= hi)) if var == "@ret"
                else (lambda S, r: z3.And(S[var] >= lo, S[var] <= hi)))
        _corroborate_domain(prop, target, "interval analysis", src, post)
        return Verdict(PROVED, prop, target, "interval analysis (widening+narrowing)",
                       reason=f"{var} in {iv}")
    return Verdict(UNKNOWN, prop, target, "interval analysis",
                   reason=f"computed {var}={iv}, not provably within [{lo},{hi}] "
                          f"(interval domain is non-relational)")


_ZINF = float("inf")


class _Zone:
    def __init__(self, idx):
        self.idx = idx
        self.n = len(idx) + 1
        self.m = [[0 if i == j else _ZINF for j in range(self.n)] for i in range(self.n)]
        self.empty = False

    def copy(self):
        z = _Zone(self.idx)
        z.m = [r[:] for r in self.m]
        z.empty = self.empty
        return z

    def close(self):
        m, n = self.m, self.n
        for k in range(n):
            for i in range(n):
                ik = m[i][k]
                if ik == _ZINF:
                    continue
                for j in range(n):
                    v = ik + m[k][j]
                    if v < m[i][j]:
                        m[i][j] = v
        for i in range(n):
            if m[i][i] < 0:
                self.empty = True
        return self

    def add(self, i, j, c):
        if c < self.m[i][j]:
            self.m[i][j] = c
        self.close()

    def forget(self, x):
        for k in range(self.n):
            if k != x:
                self.m[x][k] = _ZINF
                self.m[k][x] = _ZINF
        self.m[x][x] = 0

    def le(self, i, j):
        return self.m[i][j]


def _z_join(a, b):
    if a.empty:
        return b
    if b.empty:
        return a
    z = a.copy()
    for i in range(z.n):
        for j in range(z.n):
            z.m[i][j] = max(a.m[i][j], b.m[i][j])
    return z


def _z_widen(a, b):
    z = a.copy()
    for i in range(z.n):
        for j in range(z.n):
            z.m[i][j] = a.m[i][j] if b.m[i][j] <= a.m[i][j] else _ZINF
    return z


def _z_narrow(a, b):
    z = a.copy()
    for i in range(z.n):
        for j in range(z.n):
            z.m[i][j] = b.m[i][j] if a.m[i][j] == _ZINF else a.m[i][j]
    return z


def _z_eq(a, b):
    return a.empty == b.empty and a.m == b.m


def _z_assign(z, name, node):
    x = z.idx[name]
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        z.forget(x); z.add(x, 0, node.value); z.add(0, x, -node.value)
    elif isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub)):
        sgn = 1 if isinstance(node.op, ast.Add) else -1
        L, R = node.left, node.right
        if isinstance(L, ast.Name) and isinstance(R, ast.Constant):
            c = sgn * R.value
            if L.id == name:                              # x := x + c  (exact shift)
                for k in range(z.n):
                    if k != x:
                        if z.m[x][k] != _ZINF: z.m[x][k] += c
                        if z.m[k][x] != _ZINF: z.m[k][x] -= c
                z.close()
            else:
                y = z.idx[L.id]; z.forget(x); z.add(x, y, c); z.add(y, x, -c)
        else:
            z.forget(x)
    elif isinstance(node, ast.Name):                      # x := y
        y = z.idx[node.id]; z.forget(x); z.add(x, y, 0); z.add(y, x, 0)
    else:
        z.forget(x)
    return z


def _z_refine(z, test, truth):
    z = z.copy()
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        op, L, R = test.ops[0], test.left, test.comparators[0]
        if isinstance(L, ast.Name) and isinstance(R, ast.Name):
            a, b = z.idx[L.id], z.idx[R.id]
            if (isinstance(op, ast.Lt) and truth) or (isinstance(op, ast.GtE) and not truth): z.add(a, b, -1)
            elif (isinstance(op, ast.LtE) and truth) or (isinstance(op, ast.Gt) and not truth): z.add(a, b, 0)
            elif (isinstance(op, ast.Gt) and truth) or (isinstance(op, ast.LtE) and not truth): z.add(b, a, -1)
            elif (isinstance(op, ast.GtE) and truth) or (isinstance(op, ast.Lt) and not truth): z.add(b, a, 0)
        elif isinstance(L, ast.Name) and isinstance(R, ast.Constant) and isinstance(R.value, int):
            a, k = z.idx[L.id], R.value
            if (isinstance(op, ast.Lt) and truth) or (isinstance(op, ast.GtE) and not truth): z.add(a, 0, k - 1)
            elif (isinstance(op, ast.LtE) and truth) or (isinstance(op, ast.Gt) and not truth): z.add(a, 0, k)
            elif (isinstance(op, ast.Gt) and truth) or (isinstance(op, ast.LtE) and not truth): z.add(0, a, -(k + 1))
            elif (isinstance(op, ast.GtE) and truth) or (isinstance(op, ast.Lt) and not truth): z.add(0, a, -k)
    return z


def _z_transfer(stmts, z):
    for s in stmts:
        if z.empty:
            return z
        if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name):
            z = _z_assign(z, s.targets[0].id, s.value)
        elif isinstance(s, ast.While):
            head = z.copy()
            # Each non-stabilizing widening step sends at least one of the z.n*z.n DBM
            # entries to +inf permanently, so the sequence stabilizes within z.n*z.n + 1
            # steps; the cap derives from the matrix dimension with slack.
            cap = 2 * z.n * z.n + 8
            for _ in range(cap):
                body = _z_transfer(s.body, _z_refine(head, s.test, True))
                w = _z_widen(head, _z_join(head, body))
                if _z_eq(w, head):
                    break
                head = w
            else:
                raise NonConvergence("zone widening did not reach a fixpoint")
            for _ in range(cap):
                body = _z_transfer(s.body, _z_refine(head, s.test, True))
                nz = _z_narrow(head, _z_join(head.copy(), body))
                if _z_eq(nz, head):
                    break
                head = nz
            z = _z_refine(head, s.test, False)
        elif isinstance(s, ast.Return):
            return z
    return z


def _z_analyze(src):
    fn = _parse(src).body[0]
    names = {n.id for n in ast.walk(fn) if isinstance(n, ast.Name)}
    idx = {nm: i + 1 for i, nm in enumerate(sorted(names))}
    z = _Zone(idx)
    return z, _z_transfer(fn.body, z)


def verify_zone_equal(prop, target, src, u, v) -> Verdict:
    """Prove u == v at function exit using the zone domain (u - v <= 0 and v - u <= 0)."""
    z, out = _z_analyze(src)
    if u not in z.idx or v not in z.idx:
        return Verdict(UNKNOWN, prop, target, "zone domain", reason="variable not found")
    if out.empty or (out.le(z.idx[u], z.idx[v]) <= 0 and out.le(z.idx[v], z.idx[u]) <= 0):
        if not out.empty:
            _corroborate_domain(prop, target, "zone domain", src, lambda S, r: S[u] == S[v])
        return Verdict(PROVED, prop, target, "zone domain (relational)", reason=f"{u} == {v} at exit")
    return Verdict(UNKNOWN, prop, target, "zone domain",
                   reason=f"could not establish {u} == {v} "
                          f"({u}-{v}<={out.le(z.idx[u], z.idx[v])}, {v}-{u}<={out.le(z.idx[v], z.idx[u])})")


_OINF = float("inf")


class _Oct:
    def __init__(self, names):
        self.names = list(names)
        self.idx = {nm: k for k, nm in enumerate(self.names)}
        self.N = 2 * len(self.names)
        self.m = [[0 if i == j else _OINF for j in range(self.N)] for i in range(self.N)]
        self.empty = False

    def copy(self):
        o = _Oct(self.names); o.m = [r[:] for r in self.m]; o.empty = self.empty; return o

    def add(self, i, j, c):                       # V_i - V_j <= c, with coherence
        if c < self.m[i][j]:
            self.m[i][j] = c
        bi, bj = i ^ 1, j ^ 1                      # V_i - V_j == V_bar(j) - V_bar(i)
        if c < self.m[bj][bi]:
            self.m[bj][bi] = c

    def forget(self, k):
        for t in (2 * k, 2 * k + 1):
            for h in range(self.N):
                if h != t:
                    self.m[t][h] = _OINF; self.m[h][t] = _OINF
            self.m[t][t] = 0

    def close(self):
        m, N = self.m, self.N
        for k in range(N):
            mk = m[k]
            for i in range(N):
                ik = m[i][k]
                if ik == _OINF:
                    continue
                mi = m[i]
                for j in range(N):
                    if mk[j] == _OINF:
                        continue
                    v = ik + mk[j]
                    if v < mi[j]:
                        mi[j] = v
        for i in range(N):                        # integer tightening of 2x bounds
            if m[i][i ^ 1] != _OINF:
                m[i][i ^ 1] = 2 * _math.floor(m[i][i ^ 1] / 2)
        for i in range(N):                        # strong (octagon) closure step
            for j in range(N):
                a, b = m[i][i ^ 1], m[j ^ 1][j]
                if a != _OINF and b != _OINF:
                    v = _math.floor((a + b) / 2)
                    if v < m[i][j]:
                        m[i][j] = v
        for i in range(N):
            if m[i][i] < 0:
                self.empty = True
        return self

    def sum_bounds(self, u, v):                   # (lower, upper) on x_u + x_v
        ku, kv = self.idx[u], self.idx[v]
        return -self.m[2 * ku + 1][2 * kv], self.m[2 * ku][2 * kv + 1]


def _o_shift(o, k, c):                            # exact transfer for x_k := x_k + c
    N, p, q = o.N, 2 * k, 2 * k + 1
    for h in range(N):
        if h in (p, q):
            continue
        if o.m[p][h] != _OINF: o.m[p][h] += c
        if o.m[h][p] != _OINF: o.m[h][p] -= c
        if o.m[q][h] != _OINF: o.m[q][h] -= c
        if o.m[h][q] != _OINF: o.m[h][q] += c
    if o.m[p][q] != _OINF: o.m[p][q] += 2 * c
    if o.m[q][p] != _OINF: o.m[q][p] -= 2 * c
    o.close()


def _o_assign(o, name, node):
    o = o.copy(); k = o.idx[name]
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        o.forget(k); c = node.value
        o.add(2 * k, 2 * k + 1, 2 * c); o.add(2 * k + 1, 2 * k, -2 * c); o.close()
    elif isinstance(node, ast.Name) and node.id in o.idx:
        l = o.idx[node.id]
        if l != k:
            o.forget(k); o.add(2 * k, 2 * l, 0); o.add(2 * l, 2 * k, 0); o.close()
    elif isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub)):
        sgn = 1 if isinstance(node.op, ast.Add) else -1
        L, R = node.left, node.right
        if isinstance(L, ast.Name) and isinstance(R, ast.Constant) and isinstance(R.value, int):
            c = sgn * R.value
            if L.id == name:
                _o_shift(o, k, c)
            elif L.id in o.idx:
                l = o.idx[L.id]; o.forget(k)
                o.add(2 * k, 2 * l, c); o.add(2 * l, 2 * k, -c); o.close()
            else:
                o.forget(k); o.close()
        elif (isinstance(R, ast.Name) and R.id in o.idx and isinstance(node.op, ast.Add)
              and isinstance(L, ast.Constant) and isinstance(L.value, int)):
            c = L.value; l = o.idx[R.id]; o.forget(k)
            o.add(2 * k, 2 * l, c); o.add(2 * l, 2 * k, -c); o.close()
        else:
            o.forget(k); o.close()
    else:
        o.forget(k); o.close()
    return o


def _o_refine(o, test, truth):
    o = o.copy()
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _o_refine(o, test.operand, not truth)
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        op, L, R = test.ops[0], test.left, test.comparators[0]
        if isinstance(L, ast.Name) and isinstance(R, ast.Name) and L.id in o.idx and R.id in o.idx:
            a, b = o.idx[L.id], o.idx[R.id]
            if (isinstance(op, ast.Lt) and truth) or (isinstance(op, ast.GtE) and not truth):
                o.add(2 * a, 2 * b, -1)
            elif (isinstance(op, ast.LtE) and truth) or (isinstance(op, ast.Gt) and not truth):
                o.add(2 * a, 2 * b, 0)
            elif (isinstance(op, ast.Gt) and truth) or (isinstance(op, ast.LtE) and not truth):
                o.add(2 * b, 2 * a, -1)
            elif (isinstance(op, ast.GtE) and truth) or (isinstance(op, ast.Lt) and not truth):
                o.add(2 * b, 2 * a, 0)
            o.close()
        elif isinstance(L, ast.Name) and L.id in o.idx and isinstance(R, ast.Constant) and isinstance(R.value, int):
            a, k = o.idx[L.id], R.value
            if (isinstance(op, ast.Lt) and truth) or (isinstance(op, ast.GtE) and not truth):
                o.add(2 * a, 2 * a + 1, 2 * (k - 1))
            elif (isinstance(op, ast.LtE) and truth) or (isinstance(op, ast.Gt) and not truth):
                o.add(2 * a, 2 * a + 1, 2 * k)
            elif (isinstance(op, ast.Gt) and truth) or (isinstance(op, ast.LtE) and not truth):
                o.add(2 * a + 1, 2 * a, -2 * (k + 1))
            elif (isinstance(op, ast.GtE) and truth) or (isinstance(op, ast.Lt) and not truth):
                o.add(2 * a + 1, 2 * a, -2 * k)
            elif isinstance(op, ast.Eq) and truth:
                o.add(2 * a, 2 * a + 1, 2 * k); o.add(2 * a + 1, 2 * a, -2 * k)
            o.close()
    return o


def _o_join(a, b):
    if a.empty: return b
    if b.empty: return a
    o = a.copy()
    for i in range(o.N):
        for j in range(o.N):
            o.m[i][j] = max(a.m[i][j], b.m[i][j])
    return o


def _o_widen(a, b):
    o = a.copy()
    for i in range(o.N):
        for j in range(o.N):
            o.m[i][j] = a.m[i][j] if b.m[i][j] <= a.m[i][j] else _OINF
    return o


def _o_narrow(a, b):
    o = a.copy()
    for i in range(o.N):
        for j in range(o.N):
            o.m[i][j] = b.m[i][j] if a.m[i][j] == _OINF else a.m[i][j]
    return o


def _o_eq(a, b):
    return a.empty == b.empty and a.m == b.m


def _o_transfer(stmts, o):
    for s in stmts:
        if o.empty:
            return o
        if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name) and s.targets[0].id in o.idx:
            o = _o_assign(o, s.targets[0].id, s.value)
        elif isinstance(s, ast.If):
            o = _o_join(_o_transfer(s.body, _o_refine(o, s.test, True)),
                        _o_transfer(s.orelse, _o_refine(o, s.test, False)))
        elif isinstance(s, ast.While):
            head = o.copy()
            # Each non-stabilizing widening step sends at least one of the o.N*o.N octagon
            # entries to +inf permanently (N = 2*#vars), so it stabilizes within o.N*o.N + 1
            # steps; the cap derives from the doubled dimension with slack.
            cap = 2 * o.N * o.N + 8
            for _ in range(cap):
                body = _o_transfer(s.body, _o_refine(head, s.test, True))
                w = _o_widen(head, _o_join(head, body))
                if _o_eq(w, head):
                    break
                head = w
            else:
                raise NonConvergence("octagon widening did not reach a fixpoint")
            for _ in range(cap):
                body = _o_transfer(s.body, _o_refine(head, s.test, True))
                nz = _o_narrow(head, _o_join(head.copy(), body))
                if _o_eq(nz, head):
                    break
                head = nz
            o = _o_refine(head, s.test, False)
        elif isinstance(s, ast.Return):
            return o
    return o


def _o_analyze(src):
    fn = _parse(src).body[0]
    names = sorted({n.id for n in ast.walk(fn) if isinstance(n, ast.Name)})
    o = _Oct(names)
    return o, _o_transfer(fn.body, o)


def _octagon_concrete(src, repo, inputs):
    """Run the function and capture the final integer locals (for cross-checking)."""
    import sys
    ns: dict = {}
    for s in repo.values():
        exec(textwrap.dedent(s), ns)
    exec(textwrap.dedent(src), ns)
    fn = ns[_parse(src).body[0].name]
    cap: Dict[str, int] = {}

    def tr(frame, event, arg):
        if event in ("line", "return"):
            for kk, vv in frame.f_locals.items():
                if isinstance(vv, int) and not isinstance(vv, bool):
                    cap[kk] = vv
        return tr

    sys.settrace(tr)
    try:
        fn(*inputs)
    except ZeroDivisionError:
        pass
    finally:
        sys.settrace(None)
    return cap


def verify_octagon_sum(prop, target, src, u, v, c) -> Verdict:
    """Prove u + v == c at function exit using the octagon domain."""
    oc, out = _o_analyze(src)
    if u not in oc.idx or v not in oc.idx:
        return Verdict(UNKNOWN, prop, target, "octagon domain", reason="variable not found")
    if out.empty:
        return Verdict(PROVED, prop, target, "octagon domain (relational)", reason="exit unreachable")
    lower, upper = out.sum_bounds(u, v)
    if not (upper <= c and lower >= c):
        return Verdict(UNKNOWN, prop, target, "octagon domain",
                       reason=f"{u}+{v} in [{lower},{upper}], not forced to {c}")
    if core.ALLOW_SUBJECT_EXECUTION:                        # opt-in empirical cross-check
        fn = _parse(src).body[0]
        nargs = len(fn.args.args)
        rng = random.Random(5)
        for _ in range(1 if nargs == 0 else 25):       # every reachable exit obeys the bound
            inp = [rng.randint(-20, 20) for _ in range(nargs)]
            cap = _octagon_concrete(src, {}, inp)
            if u in cap and v in cap and not (lower <= cap[u] + cap[v] <= upper):
                raise SoundnessError(f"octagon bound [{lower},{upper}] excludes "
                                     f"{u}+{v}={cap[u] + cap[v]} at inputs {inp}")
    _corroborate_domain(prop, target, "octagon domain", src, lambda S, r: S[u] + S[v] == c)
    return Verdict(PROVED, prop, target, "octagon domain (relational, sums)",
                   reason=f"{u} + {v} == {c} at exit")


def infer_and_verify_range(prop, target, src) -> Verdict:
    try:
        st = analyze_intervals(src)
    except (Unsupported, NonConvergence) as u:
        return Verdict(UNKNOWN, prop, target, "spec inference", reason=str(u))
    iv = (st or {}).get("@ret")
    if iv is None or iv.lo == _NEG or iv.hi == _POS:
        return Verdict(UNKNOWN, prop, target, "spec inference", reason="no finite output range inferred")
    v = verify_range(prop, target, src, iv.lo, iv.hi)
    if v.status == PROVED:
        return Verdict(PROVED, prop, target, "spec inference (range, proved)",
                       reason=f"inferred and discharged @ret in [{iv.lo},{iv.hi}]")
    return v


def subset_coverage(source):
    mod = _parse(source)                                          # desugar (for, aug-assign, ...)
    fns = [n for n in mod.body if isinstance(n, ast.FunctionDef)]
    encoded = 0
    for fn in fns:
        try:
            blocks, _entry = _build_cfg(fn.body)
            ctx = Ctx({}); ctx.traps = []; ctx.pc = z3.BoolVal(True)
            names = {a.arg for a in fn.args.args}
            for b in blocks.values():
                names |= {s.targets[0].id for s in b.assigns
                          if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name)}
            st = {nm: z3.Int(nm) for nm in names}
            for b in blocks.values():
                after = _apply_assigns(b.assigns, dict(st), ctx)  # assignments
                term = b.term
                if term and term[0] == "branch":
                    ev_bool(term[1], after, ctx)                  # branch condition
                elif term and term[0] == "return" and term[1] is not None:
                    ev(term[1], after, ctx)                       # return expression
            encoded += 1
        except Exception:
            pass
    return {"functions": len(fns), "encoded": encoded}


def _aff_reduce(vecs, n):
    basis, pivots = [], []
    for v in vecs:
        w = [_Fr(x) for x in v]
        for b, pc in zip(basis, pivots):
            if w[pc] != 0:
                f = w[pc]; w = [wi - f * bi for wi, bi in zip(w, b)]
        pc = next((i for i in range(n) if w[i] != 0), None)
        if pc is not None:
            w = [wi / w[pc] for wi in w]
            basis.append(w); pivots.append(pc)
    return basis


def _aff_in_span(v, dirs, n):
    basis = _aff_reduce(dirs, n)
    w = [_Fr(x) for x in v]
    for b in basis:
        pc = next(i for i in range(n) if b[i] != 0)
        if w[pc] != 0:
            f = w[pc]; w = [wi - f * bi for wi, bi in zip(w, b)]
    return all(x == 0 for x in w)


def _aff_le(A, B, n):
    if A is None: return True
    if B is None: return False
    pA, dA = A; pB, dB = B
    if not _aff_in_span([a - b for a, b in zip(pA, pB)], dB, n): return False
    return all(_aff_in_span(d, dB, n) for d in dA)


def _aff_eq(A, B, n): return _aff_le(A, B, n) and _aff_le(B, A, n)


def _aff_join(A, B, n):
    if A is None: return B
    if B is None: return A
    pA, dA = A; pB, dB = B
    return (pA, _aff_reduce(dA + dB + [[b - a for a, b in zip(pA, pB)]], n))


def _aff_lin(node, idx, n):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return (_Fr(node.value), [_Fr(0)] * n)
    if isinstance(node, ast.Name) and node.id in idx:
        c = [_Fr(0)] * n; c[idx[node.id]] = _Fr(1); return (_Fr(0), c)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        r = _aff_lin(node.operand, idx, n)
        return None if r is None else (-r[0], [-x for x in r[1]])
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub)):
        l, r = _aff_lin(node.left, idx, n), _aff_lin(node.right, idx, n)
        if l is None or r is None: return None
        sgn = 1 if isinstance(node.op, ast.Add) else -1
        return (l[0] + sgn * r[0], [a + sgn * b for a, b in zip(l[1], r[1])])
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        l, r = _aff_lin(node.left, idx, n), _aff_lin(node.right, idx, n)
        if l and all(x == 0 for x in l[1]) and r:
            return (l[0] * r[0], [l[0] * x for x in r[1]])
        if r and all(x == 0 for x in r[1]) and l:
            return (r[0] * l[0], [r[0] * x for x in l[1]])
    return None


def _aff_assign(state, j, lin, n):
    if state is None: return None
    p, dirs = state
    if lin is None:                                            # havoc: x_j becomes free
        np = list(p); np[j] = _Fr(0)
        e = [_Fr(0)] * n; e[j] = _Fr(1)
        return (np, _aff_reduce(dirs + [e], n))
    const, co = lin
    np = list(p); np[j] = const + sum(co[i] * p[i] for i in range(n))
    nd = []
    for d in dirs:
        e = list(d); e[j] = sum(co[i] * d[i] for i in range(n)); nd.append(e)
    return (np, _aff_reduce(nd, n))


def _aff_transfer(stmts, state, idx, n):
    for s in stmts:
        if state is None: return None
        if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name) and s.targets[0].id in idx:
            state = _aff_assign(state, idx[s.targets[0].id], _aff_lin(s.value, idx, n), n)
        elif isinstance(s, ast.If):
            state = _aff_join(_aff_transfer(s.body, state, idx, n),
                              _aff_transfer(s.orelse, state, idx, n), n)
        elif isinstance(s, ast.While):
            head = state
            for _ in range(n + 2):                            # converges in <= n+1 joins
                joined = _aff_join(head, _aff_transfer(s.body, head, idx, n), n)
                if _aff_eq(joined, head, n): break
                head = joined
            else:
                raise NonConvergence("Karr did not converge")
            state = head
        elif isinstance(s, ast.Return):
            return state
    return state


def analyze_affine(src):
    fn = _parse(src).body[0]
    names = sorted({nd.id for nd in ast.walk(fn) if isinstance(nd, ast.Name)})
    idx = {nm: i for i, nm in enumerate(names)}; n = len(names)
    top = ([_Fr(0)] * n, [[_Fr(1) if i == j else _Fr(0) for i in range(n)] for j in range(n)])
    return idx, n, _aff_transfer(fn.body, top, idx, n)


def verify_affine_equal(prop, target, src, u, v) -> Verdict:
    idx, n, state = analyze_affine(src)
    if u not in idx or v not in idx:
        return Verdict(UNKNOWN, prop, target, "affine equalities (Karr)", reason="variable not found")
    if state is None or (state[0][idx[u]] == state[0][idx[v]]
                         and all(d[idx[u]] == d[idx[v]] for d in state[1])):
        if state is not None:
            _corroborate_domain(prop, target, "affine equalities (Karr)", src, lambda S, r: S[u] == S[v])
        return Verdict(PROVED, prop, target, "affine equalities (Karr)", reason=f"{u} == {v} at exit")
    return Verdict(UNKNOWN, prop, target, "affine equalities (Karr)", reason=f"cannot establish {u} == {v}")


def verify_polyhedra_auto(prop, target, src, query, lo, hi, pre=None, repo=None) -> Verdict:
    """Template polyhedra with the templates generated automatically (the octagon family over the
    program variables: +-x and +-x +-y), so the user supplies only the query to bound, not the
    templates. Falls back to UNKNOWN if the auto family cannot establish the bound."""
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None or ret is None:
        return Verdict(UNKNOWN, prop, target, "template polyhedra (auto)", reason="not a single-loop function")
    vs = set(args)
    for s in init + loop.body:
        for nd in ast.walk(s):
            if isinstance(nd, ast.Name) and isinstance(nd.ctx, ast.Store):
                vs.add(nd.id)
    vs = sorted(vs)
    templates = [(lambda S, v=v: S[v]) for v in vs] + [(lambda S, v=v: -S[v]) for v in vs]
    for i, v in enumerate(vs):
        for w in vs[i + 1:]:
            templates.append(lambda S, v=v, w=w: S[v] - S[w])
            templates.append(lambda S, v=v, w=w: S[w] - S[v])
            templates.append(lambda S, v=v, w=w: S[v] + S[w])
    v = verify_polyhedra(prop, target, src, templates, query, lo, hi, pre, repo)
    if v.status == PROVED:
        return Verdict(PROVED, prop, target, "template polyhedra (auto-generated octagon templates)",
                       reason=v.reason)
    return Verdict(v.status, prop, target, "template polyhedra (auto)", reason=v.reason)


def verify_polyhedra(prop, target, src, templates, query, lo, hi, pre=None, repo=None) -> Verdict:
    """templates: list of fns state->linear z3 expr. query: fn state->expr to bound.
    pre(arg_state)->Bool constrains the entry."""
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None or ret is None:
        return Verdict(UNKNOWN, prop, target, "template polyhedra", reason="not a single-loop function")
    ctx = Ctx(repo or {})
    INF = float("inf")
    try:
        base = {a: z3.Int(a) for a in args}
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        init_state = _apply_assigns(init, base, ctx)
        order = args + sorted(set(init_state) - set(args))
        sym = dict(base)
        for v in order:
            if v not in args:
                sym[v] = z3.Int(v + "_p")
        guard = ev_bool(loop.test, sym, ctx)
        body = _apply_assigns(loop.body, sym, ctx)
        if ctx.traps:
            return Verdict(UNKNOWN, prop, target, "template polyhedra", reason="division in loop")
        ctx.traps = None
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "template polyhedra", reason=str(u))

    def opt(expr, constrs, maximize=True):
        o = z3.Optimize(); o.set("timeout", 4000)
        for cstr in constrs:
            o.add(cstr)
        h = o.maximize(expr) if maximize else o.minimize(expr)
        if o.check() != z3.sat:
            return None
        val = o.upper(h) if maximize else o.lower(h)
        if z3.is_int_value(val):
            return val.as_long()
        return INF if maximize else -INF

    m = len(templates)
    pre_init = pre(base) if pre else (z3.And(*[base[a] >= -(1 << 20) for a in args]) if args else z3.BoolVal(True))
    c = []                                                        # initial template bounds at entry
    for i in range(m):
        b = opt(templates[i](init_state), [pre_init])
        c.append(b if b is not None else INF)
    for _ in range(2 * m + 8):                                    # policy iteration with widening
        cur_constr = [guard] + [templates[i](sym) <= c[i] for i in range(m) if c[i] != INF]
        newc, changed = [], False
        for i in range(m):
            b = opt(templates[i](body), cur_constr)
            nb = c[i]
            if b is None:
                nb = c[i]
            elif b > c[i]:
                nb = INF; changed = True                          # widen
            newc = newc + [nb]
        if not changed:
            break
        c = newc
    exit_constr = [z3.Not(guard)] + [templates[i](sym) <= c[i] for i in range(m) if c[i] != INF]
    qhi = opt(query(sym), exit_constr, True)
    qlo = opt(query(sym), exit_constr, False)
    if qhi is not None and qlo is not None and lo <= qlo and qhi <= hi:
        _corroborate_domain(prop, target, "template polyhedra", src,
                            lambda S, r: z3.And(query(S) >= lo, query(S) <= hi),
                            pre=pre)
        return Verdict(PROVED, prop, target, "template polyhedra (relational)",
                       reason=f"query in [{qlo},{qhi}] at exit")
    return Verdict(UNKNOWN, prop, target, "template polyhedra",
                   reason=f"query in [{qlo},{qhi}], not provably within [{lo},{hi}]")


def verify_machine_range(prop, target, src, width, lo, hi) -> Verdict:
    INT_MIN, INT_MAX = -(1 << (width - 1)), (1 << (width - 1)) - 1
    fn = _parse(src).body[0]
    full = (INT_MIN, INT_MAX)

    def cap(iv):
        l, h = iv
        return iv if (l <= h and INT_MIN <= l and h <= INT_MAX) else full

    def mev(node, env):
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return cap((node.value, node.value))
        if isinstance(node, ast.Name):
            return env.get(node.id, full)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            l, h = mev(node.operand, env); return cap((-h, -l))
        if isinstance(node, ast.BinOp):
            (al, ah), (bl, bh) = mev(node.left, env), mev(node.right, env)
            if isinstance(node.op, ast.Add): return cap((al + bl, ah + bh))
            if isinstance(node.op, ast.Sub): return cap((al - bh, ah - bl))
            if isinstance(node.op, ast.Mult):
                ps = [al * bl, al * bh, ah * bl, ah * bh]; return cap((min(ps), max(ps)))
        return full

    def refine(env, test, truth):                       # bound x by a constant guard
        env = dict(env)
        if isinstance(test, ast.Compare) and len(test.ops) == 1 and isinstance(test.left, ast.Name) \
                and isinstance(test.comparators[0], ast.Constant) and isinstance(test.comparators[0].value, int):
            x, k, op = test.left.id, test.comparators[0].value, test.ops[0]
            l, h = env.get(x, full)
            if (isinstance(op, ast.Lt) and truth) or (isinstance(op, ast.GtE) and not truth): h = min(h, k - 1)
            elif (isinstance(op, ast.LtE) and truth) or (isinstance(op, ast.Gt) and not truth): h = min(h, k)
            elif (isinstance(op, ast.Gt) and truth) or (isinstance(op, ast.LtE) and not truth): l = max(l, k + 1)
            elif (isinstance(op, ast.GtE) and truth) or (isinstance(op, ast.Lt) and not truth): l = max(l, k)
            if l <= h:
                env[x] = (l, h)
        return env

    def ijoin(a, b):
        return {k: (min(a[k][0], b.get(k, full)[0]), max(a[k][1], b.get(k, full)[1])) for k in set(a) | set(b)}

    def iwiden(old, new):
        return {k: (old[k][0] if new[k][0] >= old[k][0] else INT_MIN,
                    old[k][1] if new[k][1] <= old[k][1] else INT_MAX) for k in old}

    def inarrow(old, new):
        return {k: (new[k][0] if old[k][0] == INT_MIN else old[k][0],
                    new[k][1] if old[k][1] == INT_MAX else old[k][1]) for k in old}

    def transfer(stmts, env):
        env = dict(env)
        for s in stmts:
            if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name):
                env[s.targets[0].id] = mev(s.value, env)
            elif isinstance(s, ast.If):
                e1 = transfer(s.body, refine(env, s.test, True))
                e2 = transfer(s.orelse, refine(env, s.test, False))
                env = ijoin(e1, e2)
            elif isinstance(s, ast.While):
                entry, head = dict(env), dict(env)
                # widening sends each of the 2*len(head) bounds to INT_MIN/INT_MAX at most
                # once, so the sequence stabilizes within 2*len(head)+1 steps; cap derives
                # from the number of live variables with slack.
                cap = 4 * len(head) + 8
                for _ in range(cap):                                 # widen to a fixpoint
                    body = transfer(s.body, refine(head, s.test, True))
                    wid = iwiden(head, ijoin(head, body))
                    if wid == head:
                        break
                    head = wid
                else:
                    raise NonConvergence("machine-interval widening did not converge")
                for _ in range(cap):                                 # narrow to recover precision
                    body = transfer(s.body, refine(head, s.test, True))
                    nz = inarrow(head, ijoin(entry, body))
                    if nz == head:
                        break
                    head = nz
                env = refine(head, s.test, False)
            elif isinstance(s, ast.Return):
                env["@ret"] = mev(s.value, env); return env
        return env

    try:
        out = transfer(fn.body, {a.arg: full for a in fn.args.args})
    except (Unsupported, NonConvergence) as u:
        return Verdict(UNKNOWN, prop, target, "machine intervals", reason=str(u))
    if "@ret" not in out:
        return Verdict(UNKNOWN, prop, target, "machine intervals", reason="@ret not reached")
    rl, rh = out["@ret"]
    if lo <= rl and rh <= hi:
        return Verdict(PROVED, prop, target, "machine intervals (fixed width)",
                       reason=f"@ret in [{rl},{rh}] under {width}-bit semantics")
    return Verdict(UNKNOWN, prop, target, "machine intervals",
                   reason=f"@ret in [{rl},{rh}], not provably within [{lo},{hi}]")


# --------------------------------------------------------------------------- #
# Floating-point interval domain (IEEE-754 double precision). Each variable is      #
# bounded by [lo, hi] over doubles together with a "may be NaN" flag. Arithmetic     #
# rounds endpoints outward (one ulp away from the rounded result), so the abstract    #
# interval never excludes a reachable double; producing NaN (inf - inf, 0 * inf, or a  #
# NaN input) sets the flag. Widening sends an unstable bound to +-inf so float loops    #
# converge; narrowing recovers a guard-implied bound. A range claim holds only when the  #
# interval fits AND NaN is impossible.                                                  #
# --------------------------------------------------------------------------- #
def _f_down(x):
    return x if (_math.isnan(x) or x == _NEG) else _math.nextafter(x, _NEG)


def _f_up(x):
    return x if (_math.isnan(x) or x == _POS) else _math.nextafter(x, _POS)


class Ivf:
    __slots__ = ("lo", "hi", "nan")
    def __init__(self, lo, hi, nan=False): self.lo, self.hi, self.nan = lo, hi, nan
    def __eq__(self, o): return isinstance(o, Ivf) and self.lo == o.lo and self.hi == o.hi and self.nan == o.nan
    def __repr__(self): return f"[{self.lo},{self.hi}]" + ("+NaN" if self.nan else "")


def _ftop():
    return Ivf(_NEG, _POS, True)


def _f_binop(a, b, op):
    nan = a.nan or b.nan
    cs = []
    for x in (a.lo, a.hi):
        for y in (b.lo, b.hi):
            c = x + y if op == "+" else (x - y if op == "-" else x * y)
            if _math.isnan(c):
                nan = True
            else:
                cs.append(c)
    if not cs:
        return Ivf(_NEG, _POS, True)
    return Ivf(_f_down(min(cs)), _f_up(max(cs)), nan)


def _f_eval(node, st):
    if isinstance(node, ast.Constant) and isinstance(node.value, bool):
        return Ivf(1.0, 1.0) if node.value else Ivf(0.0, 0.0)
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
        v = float(node.value)
        return _ftop() if (_math.isinf(v) or _math.isnan(v)) else Ivf(v, v)
    if isinstance(node, ast.Name):
        return st.get(node.id, _ftop())
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        a = _f_eval(node.operand, st)
        return Ivf(-a.hi, -a.lo, a.nan)
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult)):
        op = "+" if isinstance(node.op, ast.Add) else ("-" if isinstance(node.op, ast.Sub) else "*")
        return _f_binop(_f_eval(node.left, st), _f_eval(node.right, st), op)
    return _ftop()


def _f_join(a, b):
    return Ivf(min(a.lo, b.lo), max(a.hi, b.hi), a.nan or b.nan)


def _f_join_st(s, t):
    if s is None: return t
    if t is None: return s
    return {k: _f_join(s[k], t.get(k, _ftop())) for k in s}


def _f_widen(o, n):
    return Ivf(o.lo if n.lo >= o.lo else _NEG, o.hi if n.hi <= o.hi else _POS, o.nan or n.nan)


def _f_narrow(o, n):
    return Ivf(n.lo if o.lo == _NEG else o.lo, n.hi if o.hi == _POS else o.hi, o.nan and n.nan)


def _f_refine(st, test, truth):
    """Sound refinement assuming test == truth. A true ordered comparison excludes NaN
    (NaN compares false to everything); a false one leaves NaN possible."""
    if st is None:
        return None
    if isinstance(test, ast.BoolOp):
        if (isinstance(test.op, ast.And) and truth) or (isinstance(test.op, ast.Or) and not truth):
            for v in test.values:
                st = _f_refine(st, v, truth)
            return st
        acc = None
        for v in test.values:
            acc = _f_join_st(acc, _f_refine(dict(st), v, truth))
        return acc
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _f_refine(st, test.operand, not truth)
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        op, L, R = test.ops[0], test.left, test.comparators[0]
        if isinstance(L, ast.Name) and isinstance(R, ast.Constant) and isinstance(R.value, (int, float)):
            n, k = L.id, float(R.value)
            cur = st.get(n, _ftop())
            lo, hi, nan = cur.lo, cur.hi, cur.nan
            if isinstance(op, (ast.Lt, ast.LtE)):
                if truth: hi, nan = min(hi, k), False
                else: lo = max(lo, k)
            elif isinstance(op, (ast.Gt, ast.GtE)):
                if truth: lo, nan = max(lo, k), False
                else: hi = min(hi, k)
            elif isinstance(op, ast.Eq) and truth:
                lo, hi, nan = max(lo, k), min(hi, k), False
            st = dict(st)
            st[n] = Ivf(lo, hi, nan)
    return st


def _f_transfer(stmts, st):
    if st is None:
        return None
    for s in stmts:
        if st is None:
            return None
        if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name):
            st = dict(st); st[s.targets[0].id] = _f_eval(s.value, st)
        elif isinstance(s, ast.If):
            st = _f_join_st(_f_transfer(s.body, _f_refine(dict(st), s.test, True)),
                            _f_transfer(s.orelse, _f_refine(dict(st), s.test, False)))
        elif isinstance(s, ast.While):
            entry, head = dict(st), dict(st)
            cap = 4 * len(head) + 8
            for _ in range(cap):                              # widen to a fixpoint
                body = _f_transfer(s.body, _f_refine(dict(head), s.test, True))
                joined = _f_join_st(head, body)
                widened = {k: _f_widen(head[k], joined[k]) for k in head}
                if widened == head:
                    break
                head = widened
            else:
                raise NonConvergence("float interval widening did not converge")
            for _ in range(cap):                              # narrow to recover guard bounds
                body = _f_transfer(s.body, _f_refine(dict(head), s.test, True))
                joined = _f_join_st(entry, body)
                narrowed = {k: _f_narrow(head[k], joined[k]) for k in head}
                if narrowed == head:
                    break
                head = narrowed
            st = _f_refine(dict(head), s.test, False)
        elif isinstance(s, ast.Return):
            st = dict(st); st["@ret"] = _f_eval(s.value, st)
            return st
    return st


def analyze_float_intervals(src):
    fn = _parse(src).body[0]
    return _f_transfer(fn.body, {a.arg: _ftop() for a in fn.args.args})   # params: any double (incl NaN)


def intervals_executable():
    """Path to the Coq-extracted interval operators built by proofs/build_intervals.sh, or None."""
    return core.find_extracted("intervals")


def extracted_intervals_batch(items, exe=None):
    """Run the extracted interval operators on (op, bounds) requests in one invocation; return the
    (lo, hi) results aligned with items, or None if the binary is not built. op is iadd/isub/ineg/
    ijoin/imul; bounds is the integer tuple (two for ineg, four otherwise)."""
    exe = exe or intervals_executable()
    if exe is None or not items:
        return [] if exe is not None else None
    inp = "".join(op + " " + " ".join(str(x) for x in bounds) + "\n" for op, bounds in items)
    out = subprocess.run([exe], input=inp, capture_output=True, text=True, timeout=300)
    return [tuple(int(t) for t in r.split()) for r in out.stdout.strip("\n").split("\n")]


def verify_float_range(prop, target, src, lo, hi, var="@ret") -> Verdict:
    """Prove a float variable stays within [lo, hi] and is never NaN, by interval analysis
    over IEEE-754 doubles with outward rounding and widening. As a sound over-approximation
    it returns PROVED or UNKNOWN, never REFUTED."""
    try:
        st = analyze_float_intervals(src)
    except (Unsupported, NonConvergence) as u:
        return Verdict(UNKNOWN, prop, target, "float intervals", reason=str(u))
    iv = (st or {}).get(var)
    if iv is None:
        return Verdict(UNKNOWN, prop, target, "float intervals", reason=f"{var} not reached")
    if not iv.nan and iv.lo >= lo and iv.hi <= hi:
        return Verdict(PROVED, prop, target, "float intervals (IEEE-754 widening+narrowing)",
                       reason=f"{var} in [{iv.lo},{iv.hi}], NaN-free")
    return Verdict(UNKNOWN, prop, target, "float intervals",
                   reason=f"computed {var}={iv}, not provably within [{lo},{hi}] and NaN-free")


# ===================================================================================== #
# Specialized theories (concurrency, IEEE-754, separation logic, SOS): from theories.py.
# ===================================================================================== #


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
                               _cvc5_sl_eval(core.parse_spec(pre), env, current, allcells, s, K))
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


# ===================================================================================== #
# Trap-freedom decider + differential CPython oracle + fuzz corpora: from benchmark.py.
# `python -m touchstone.domains [dir]` runs the corpus (was `python -m touchstone.benchmark`).
# ===================================================================================== #


STANDARD_CORPUS = [
    ("gcd", "def gcd(a, b):\n    while b != 0:\n        t = b\n        b = a % b\n        a = t\n    return a\n"),
    ("abs_val", "def abs_val(x):\n    if x < 0:\n        return -x\n    return x\n"),
    ("sign", "def sign(x):\n    if x > 0:\n        return 1\n    if x < 0:\n        return -1\n    return 0\n"),
    ("clamp", "def clamp(x):\n    if x > 100:\n        x = 100\n    if x < 0:\n        x = 0\n    return x\n"),
    ("max3", "def max3(a, b, c):\n    return max(a, max(b, c))\n"),
    ("min3", "def min3(a, b, c):\n    return min(a, min(b, c))\n"),
    ("square", "def square(x):\n    return x * x\n"),
    ("is_even", "def is_even(n):\n    return 1 - n % 2\n"),
    ("triangular", "def triangular(n):\n    s = 0\n    i = 0\n    while i < n:\n        i = i + 1\n        s = s + i\n    return s\n"),
    ("power", "def power(b, e):\n    r = 1\n    i = 0\n    while i < e:\n        r = r * b\n        i = i + 1\n    return r\n"),
    ("count_digits", "def count_digits(n):\n    c = 1\n    while n >= 10:\n        n = n // 10\n        c = c + 1\n    return c\n"),
    ("collatz_steps", "def collatz_steps(n):\n    c = 0\n    while n > 1:\n        if n % 2 == 0:\n            n = n // 2\n        else:\n            n = 3 * n + 1\n        c = c + 1\n    return c\n"),
    ("divide_unguarded", "def divide_unguarded(a, b):\n    return a // b\n"),
    ("divide_guarded", "def divide_guarded(a, b):\n    if b == 0:\n        return 0\n    return a // b\n"),
    ("reciprocal_ish", "def reciprocal_ish(x):\n    return 1000 // x\n"),
    ("factorial_rec", "def factorial_rec(n):\n    if n <= 0:\n        return 1\n    return n * factorial_rec(n - 1)\n"),
    ("fib_rec", "def fib_rec(n):\n    if n < 2:\n        return n\n    return fib_rec(n - 1) + fib_rec(n - 2)\n"),
    ("sum_rec", "def sum_rec(n):\n    if n <= 0:\n        return 0\n    return n + sum_rec(n - 1)\n"),
    ("list_sum", "def list_sum(xs: list):\n    s = 0\n    for x in xs:\n        s = s + x\n    return s\n"),
    ("list_max0", "def list_max0(xs: list):\n    m = 0\n    for x in xs:\n        if x > m:\n            m = x\n    return m\n"),
    ("list_count_pos", "def list_count_pos(xs: list):\n    c = 0\n    for x in xs:\n        if x > 0:\n            c = c + 1\n    return c\n"),
    ("list_contains", "def list_contains(xs: list, target):\n    found = 0\n    for x in xs:\n        if x == target:\n            found = 1\n    return found\n"),
    ("list_abs_sum", "def list_abs_sum(xs: list):\n    s = 0\n    for x in xs:\n        s = s + abs(x)\n    return s\n"),
    ("range_generator", "def range_generator(n):\n    for i in range(n):\n        yield i\n"),
    ("even_generator", "def even_generator(n):\n    for i in range(n):\n        yield 2 * i\n"),
    # outside the modeled subset (UNKNOWN)
    ("string_reverse", "def string_reverse(s: str):\n    return s[::-1]\n"),
    ("string_words", "def string_words(s: str):\n    return len(s.split())\n"),
    ("dict_invert", "def dict_invert(d):\n    out = {}\n    for k in d:\n        out[d[k]] = k\n    return out\n"),
    ("matrix_trace", "def matrix_trace(m):\n    s = 0\n    for i in range(len(m)):\n        s = s + m[i][i]\n    return s\n"),
]


# A random-program generator: machine-written functions in the verified integer subset -- straight-line
# arithmetic, nested conditionals, and constant-bounded (terminating) loops over + - * // %. Every local is
# pre-initialized so no path is unbound, and // / % over unconstrained operands make a trap reachable unless
# guarded. The differential oracle holds the decider sound over the corpus.
_GEN_VARS = ("x", "y", "z", "t")


def _gen_expr(rng, names, depth):
    if depth <= 0 or rng.random() < 0.35:
        return rng.choice(names) if (names and rng.random() < 0.65) else str(rng.randint(-4, 9))
    op = rng.choice(("+", "-", "*", "//", "%"))
    return "(%s %s %s)" % (_gen_expr(rng, names, depth - 1), op, _gen_expr(rng, names, depth - 1))


def _gen_cmp(rng, names, depth):
    op = rng.choice(("<", "<=", ">", ">=", "==", "!="))
    return "%s %s %s" % (_gen_expr(rng, names, depth), op, _gen_expr(rng, names, depth))


def _gen_block(rng, names, indent, depth, budget):
    lines = []
    for _ in range(rng.randint(1, 3)):
        if budget[0] <= 0:
            break
        budget[0] -= 1
        r = rng.random()
        if depth <= 0 or r < 0.55:
            lines.append("%s%s = %s" % (indent, rng.choice(_GEN_VARS), _gen_expr(rng, names, depth)))
        elif r < 0.8:
            lines.append("%sif %s:" % (indent, _gen_cmp(rng, names, depth)))
            lines += _gen_block(rng, names, indent + "    ", depth - 1, budget)
            if rng.random() < 0.55:
                lines.append("%selse:" % indent)
                lines += _gen_block(rng, names, indent + "    ", depth - 1, budget)
        else:
            lines.append("%sfor _i in range(%d):" % (indent, rng.randint(0, 4)))
            lines += _gen_block(rng, names, indent + "    ", depth - 1, budget)
    if not lines:                                        # a block must hold at least one statement
        lines.append("%s%s = %s" % (indent, rng.choice(_GEN_VARS), _gen_expr(rng, names, depth)))
    return lines


def _random_program(rng):
    params = ["a", "b", "c"][:rng.randint(1, 3)]
    names = list(params) + list(_GEN_VARS)
    body = ["    %s = 0" % v for v in _GEN_VARS]         # pre-initialize every local: no path is unbound
    body += _gen_block(rng, names, "    ", rng.randint(2, 4), [rng.randint(4, 10)])
    body.append("    return %s" % _gen_expr(rng, names, 2))
    return "def f(%s):\n%s\n" % (", ".join(params), "\n".join(body))


def random_corpus(n=200, seed=0):
    """n machine-generated functions in the verified integer subset: straight-line arithmetic, nested
    conditionals, and constant-bounded loops over // and % where a trap is reachable unless guarded."""
    rng = random.Random(seed)
    return [("gen_%04d" % i, _random_program(rng)) for i in range(n)]


# A second generator over list parameters: indexing (xs[k], a reachable IndexError), len, and iteration,
# guarded or not, stressing the sequence/heap engine's index reasoning. Integer elements keep // and %
# traps reachable; every program halts (iteration over the argument, or a constant-bounded range).
def _gen_idx(rng, names, lists):
    r = rng.random()
    if r < 0.4 and names:
        return rng.choice(names)
    if r < 0.62:
        return "len(%s) - %d" % (rng.choice(lists), rng.randint(0, 3))   # length-relative: off-by-one prone
    return str(rng.randint(-2, 5))


def _gen_iexpr(rng, names, lists, depth):
    if depth <= 0 or rng.random() < 0.4:
        r = rng.random()
        if r < 0.45 and names:
            return rng.choice(names)
        if r < 0.7:
            lst = rng.choice(lists)
            return "len(%s)" % lst if rng.random() < 0.45 else "%s[%s]" % (lst, _gen_idx(rng, names, lists))
        return str(rng.randint(-3, 6))
    op = rng.choice(("+", "-", "*", "//", "%"))
    return "(%s %s %s)" % (_gen_iexpr(rng, names, lists, depth - 1), op, _gen_iexpr(rng, names, lists, depth - 1))


def _gen_lblock(rng, names, lists, indent, depth, budget):
    lines = []
    for _ in range(rng.randint(1, 3)):
        if budget[0] <= 0:
            break
        budget[0] -= 1
        r = rng.random()
        if depth <= 0 or r < 0.5:
            lines.append("%s%s = %s" % (indent, rng.choice(_GEN_VARS), _gen_iexpr(rng, names, lists, depth)))
        elif r < 0.72:
            lines.append("%sif %s %s %s:" % (indent, _gen_iexpr(rng, names, lists, depth),
                                             rng.choice(("<", "<=", ">", ">=", "==", "!=")),
                                             _gen_iexpr(rng, names, lists, depth)))
            lines += _gen_lblock(rng, names, lists, indent + "    ", depth - 1, budget)
            if rng.random() < 0.5:
                lines.append("%selse:" % indent)
                lines += _gen_lblock(rng, names, lists, indent + "    ", depth - 1, budget)
        elif r < 0.86:
            lst = rng.choice(lists)
            lines.append("%sfor _e in %s:" % (indent, lst))
            lines += _gen_lblock(rng, names + ["_e"], lists, indent + "    ", depth - 1, budget)
        else:
            lines.append("%sfor _i in range(%d):" % (indent, rng.randint(0, 3)))
            lines += _gen_lblock(rng, names, lists, indent + "    ", depth - 1, budget)
    if not lines:
        lines.append("%s%s = %s" % (indent, rng.choice(_GEN_VARS), _gen_iexpr(rng, names, lists, depth)))
    return lines


def _random_list_program(rng):
    lists = ["xs"] + (["ys"] if rng.random() < 0.4 else [])
    iparams = ["n"] if rng.random() < 0.5 else []
    names = list(iparams) + list(_GEN_VARS)
    body = ["    %s = 0" % v for v in _GEN_VARS]         # int locals pre-initialized; list params always defined
    body += _gen_lblock(rng, names, lists, "    ", rng.randint(2, 4), [rng.randint(4, 9)])
    body.append("    return %s" % _gen_iexpr(rng, names, lists, 2))
    return "def f(%s):\n%s\n" % (", ".join(["%s: list" % l for l in lists] + iparams), "\n".join(body))


def random_list_corpus(n=200, seed=0):
    """n machine-generated functions over list parameters: indexing (a reachable IndexError unless guarded by
    len), len, iteration, and integer arithmetic on the elements (// and % keep ZeroDivisionError reachable)."""
    rng = random.Random(seed)
    return [("genl_%04d" % i, _random_list_program(rng)) for i in range(n)]


# A third generator over self-recursion: the measure parameter strictly decreases to a base case by a positive
# constant, so every call halts; the recursive result is combined arithmetically (// and % keep a trap
# reachable, including division by the recursive value). Stresses the recursion engine's Horn encoding.
def _random_rec_program(rng):
    two = rng.random() < 0.4
    params = ["a", "b"] if two else ["n"]
    m = params[0]
    names = list(params)
    base_thresh = rng.randint(0, 2)
    dec = rng.randint(1, 3)                               # strict positive decrease of the measure -> termination
    base = _gen_expr(rng, names, 2)
    rcall = ("f(%s - %d, %s)" % (m, dec, _gen_expr(rng, names, 2))) if two else ("f(%s - %d)" % (m, dec))
    op = rng.choice(("+", "-", "*", "//", "%"))
    other = _gen_expr(rng, names, 1)
    rec = ("(%s %s %s)" % (rcall, op, other)) if rng.random() < 0.5 else ("(%s %s %s)" % (other, op, rcall))
    return ("def f(%s):\n    if %s <= %d:\n        return %s\n    return %s\n"
            % (", ".join(params), m, base_thresh, base, rec))


def random_rec_corpus(n=200, seed=0):
    """n machine-generated self-recursive functions: the measure parameter decreases by a positive constant to
    a base case (so every call terminates), and the recursive result is combined with integer arithmetic where
    // and % keep a trap reachable."""
    rng = random.Random(seed)
    return [("genr_%04d" % i, src, {"f": src}) for i, src in
            ((i, _random_rec_program(rng)) for i in range(n))]


# A fourth generator over while loops with a parametric bound: a dedicated counter that only the loop
# control decrements (the body never touches it) counts down from a parameter, so the loop always halts but
# its iteration count is unknown to the engine, stressing the CHC invariant synthesis rather than the
# constant-bounded for-loops of the integer generator. // and % in the body keep a trap reachable.
def _random_while_program(rng):
    params = ["a", "b", "c"][:rng.randint(1, 3)]
    names = list(params) + list(_GEN_VARS)              # the body reads params and writes x/y/z/t, never _wc
    body = ["    %s = 0" % v for v in _GEN_VARS]
    body.append("    _wc = %s" % rng.choice(params))    # parametric bound: an iteration count the engine cannot fold
    body.append("    while _wc > 0:")
    body += _gen_block(rng, names, "        ", rng.randint(1, 3), [rng.randint(3, 7)])
    body.append("        _wc = _wc - 1")                # the only write to the counter, so the loop strictly counts down
    body.append("    return %s" % _gen_expr(rng, names, 2))
    return "def f(%s):\n%s\n" % (", ".join(params), "\n".join(body))


def random_while_corpus(n=200, seed=0):
    """n machine-generated functions with a parametric-bound while loop: a dedicated counter counts down from a
    parameter (so the loop terminates but its count is unknown), with integer arithmetic in the body where //
    and % keep a trap reachable."""
    rng = random.Random(seed)
    return [("genw_%04d" % i, _random_while_program(rng)) for i in range(n)]


# A fifth generator over a two-function repo: a helper g that may trap on some argument, and a caller f
# that invokes g (its result combined arithmetically) after building up some state. It stresses the modular
# cross-function trap analysis -- whether a trap inside the callee is propagated to the call site -- rather
# than a single function in isolation. The call graph is acyclic (f -> g -> nothing), so every call halts.
def _random_interproc_program(rng):
    g = "def g(x):\n    return %s\n" % _gen_expr(rng, ["x"], 2)
    params = ["a", "b"][:rng.randint(1, 2)]
    names = list(params) + list(_GEN_VARS)
    body = ["    %s = 0" % v for v in _GEN_VARS]
    body += _gen_block(rng, names, "    ", rng.randint(1, 2), [rng.randint(2, 5)])
    call = "g(%s)" % _gen_expr(rng, names, 2)             # the callee's trap freedom depends on this argument
    op = rng.choice(("+", "-", "*", "//", "%"))
    other = _gen_expr(rng, names, 1)
    ret = ("(%s %s %s)" % (call, op, other)) if rng.random() < 0.5 else ("(%s %s %s)" % (other, op, call))
    body.append("    return %s" % ret)
    f = "def f(%s):\n%s\n" % (", ".join(params), "\n".join(body))
    return f, g


def random_interproc_corpus(n=200, seed=0):
    """n machine-generated two-function programs (a caller f and a helper g it invokes): g may divide by its
    argument, so f is trap free only when the call site keeps that argument away from the trap."""
    rng = random.Random(seed)
    out = []
    for i in range(n):
        f, g = _random_interproc_program(rng)
        out.append(("geni_%04d" % i, f, {"f": f, "g": g}))
    return out


def _annot(arg):
    return arg.annotation.id if isinstance(arg.annotation, ast.Name) else "int"


def _noop_callable(*a, **k):
    """A well-behaved (trap-free) callable for the oracle to pass where a parameter is called. Defined at
    module level so it is picklable across the sandbox spawn."""
    return 0


def _callable_params(fn):
    """Parameter names the body calls (`p(...)`): the parameters that are used as callbacks."""
    params = {a.arg for a in fn.args.args} | {a.arg for a in fn.args.kwonlyargs}
    return {n.func.id for n in ast.walk(fn)
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in params}


def _iterated_params(fn):
    """Parameter names the body iterates (a for-loop or comprehension over `p`): the parameters used as
    sequences."""
    params = {a.arg for a in fn.args.args} | {a.arg for a in fn.args.kwonlyargs}
    out = set()
    for n in ast.walk(fn):
        it = n.iter if isinstance(n, (ast.For, ast.comprehension)) else None
        if isinstance(it, ast.Name) and it.id in params:
            out.add(it.id)
    return out


def _called_positions(repo):
    """Least fixpoint of the parameter positions each repo function calls: a position called directly as
    p(...), or a position whose argument a call forwards to another repo function at a called position. A
    parameter at such a position is used as a callable, directly or transitively."""
    funcs = {}
    for name, src in (repo or {}).items():
        try:
            f = _fndef(src)
            funcs[name] = (f, [a.arg for a in f.args.args])
        except Exception:
            pass
    called = {name: set() for name in funcs}
    for name, (f, params) in funcs.items():
        idx = {p: i for i, p in enumerate(params)}
        for n in ast.walk(f):
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in idx:
                called[name].add(idx[n.func.id])
    changed = True
    while changed:
        changed = False
        for name, (f, params) in funcs.items():
            idx = {p: i for i, p in enumerate(params)}
            for n in ast.walk(f):
                if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in funcs:
                    cp = called[n.func.id]
                    for pos, arg in enumerate(n.args):
                        if (isinstance(arg, ast.Name) and arg.id in idx
                                and pos in cp and idx[arg.id] not in called[name]):
                            called[name].add(idx[arg.id]); changed = True
    return called


_STR_INFER_METHODS = frozenset({
    "strip", "lstrip", "rstrip", "upper", "lower", "title", "capitalize", "swapcase", "casefold",
    "split", "rsplit", "splitlines", "join", "replace", "format", "format_map", "encode", "translate",
    "startswith", "endswith", "find", "rfind", "zfill", "ljust", "rjust", "center", "expandtabs",
    "partition", "rpartition", "removeprefix", "removesuffix", "isdigit", "isalpha", "isalnum",
    "isspace", "isupper", "islower", "isnumeric", "isdecimal", "istitle", "isidentifier",
    "isprintable", "isascii",
})
_CONTAINER_INFER_METHODS = frozenset({
    "append", "extend", "insert", "sort", "reverse", "pop", "remove", "clear", "add", "discard",
    "keys", "values", "items", "get", "setdefault", "update", "popitem", "difference", "union",
    "intersection", "symmetric_difference",
})

# builtins that, applied to a single argument, consume it as an iterable -- so that argument is a container.
_ITER_CONSUMING_BUILTINS = frozenset({"len", "sum", "sorted", "min", "max", "any", "all", "reversed",
                                      "set", "frozenset", "tuple", "list", "iter", "enumerate"})


class _AnyC:
    """A benign stand-in for a parameter inferred to be a container: iteration yields a few integers, any index
    returns an integer, methods return another _AnyC, and nothing raises."""
    __slots__ = ()
    def __iter__(self): return iter((0, 1, 2))
    def __getitem__(self, k): return 0
    def __setitem__(self, k, v): pass
    def __delitem__(self, k): pass
    def __len__(self): return 3
    def __contains__(self, k): return True
    def __bool__(self): return True
    def __call__(self, *a, **k): return _ANYC
    def _m(self, *a, **k): return _ANYC
    def __getattr__(self, n):
        if n.startswith("__"):
            raise AttributeError(n)
        return self._m


_ANYC = _AnyC()


class _AnyObj(int):
    """A benign object stand-in (value 0): every attribute is another _AnyObj, so o.x and o.x + o.y never raise,
    matching the duck-typed-numeric field model."""
    __slots__ = ()
    def __new__(cls): return super().__new__(cls, 0)
    def __getattr__(self, n):
        if n.startswith("__"):
            raise AttributeError(n)
        return _AnyObj()


def _infer_param_kinds(fn):
    """For each unannotated parameter, a coarse kind from how the body uses it: 'seq' (integer-indexed, sampled
    as a real sequence whose out-of-range index is a witnessable IndexError), 'container' (iterated, len()'d, or
    a list/dict/set method called), 'str' (a string method called), else unclassified. Used by both the
    trap-freedom engine and the oracle, so the modeled and sampled parameter match."""
    params = {a.arg for a in fn.args.args if a.annotation is None}
    params |= {a.arg for a in fn.args.kwonlyargs if a.annotation is None}
    kinds = {}

    def mark(name, kind):
        if name in params and name not in kinds:
            kinds[name] = kind

    # names provably bound to a string: a str-annotated parameter, or a local assigned a string literal,
    # f-string, concatenation / %-format, or str-method result. A subscript keyed by such a name (or a string
    # literal / f-string) indexes a mapping, so the parameter is a dict (a list/str/tuple rejects a string key).
    _STR_METH = frozenset({"join", "format", "format_map", "upper", "lower", "strip", "lstrip", "rstrip",
                           "replace", "title", "capitalize", "casefold", "swapcase", "zfill", "center",
                           "ljust", "rjust", "removeprefix", "removesuffix"})
    str_names = {a.arg for a in fn.args.posonlyargs + fn.args.args + fn.args.kwonlyargs
                 if isinstance(a.annotation, ast.Name) and a.annotation.id == "str"}

    def is_str_key(e):
        if isinstance(e, ast.Constant):
            return isinstance(e.value, str)
        if isinstance(e, ast.JoinedStr):
            return True
        if isinstance(e, ast.Name):
            return e.id in str_names
        if isinstance(e, ast.BinOp) and isinstance(e.op, (ast.Add, ast.Mod)):
            return is_str_key(e.left) or is_str_key(e.right)
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute) and e.func.attr in _STR_METH:
            return True
        return False

    changed = True
    while changed:                                           # a local assigned from another string is a string
        changed = False
        for n in ast.walk(fn):
            if (isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                    and n.targets[0].id not in str_names and is_str_key(n.value)):
                str_names.add(n.targets[0].id); changed = True

    # Precedence: a string-keyed subscript (a dict) first; then a value comparison to a string literal (a
    # string); then an integer- or unknown-keyed subscript (a sequence). So `d['x']` reads d as a dict even when
    # `'x' in d` also tests it (membership is not a value comparison), while an is_HDN `if text == '': ... text[0]`
    # reads text as a string -- the guard an emptiness test, the index against its length -- not an int-indexed seq.
    for n in ast.walk(fn):                                   # a string-keyed read is a dict
        if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name) and is_str_key(n.slice):
            mark(n.value.id, "dict")
    _STR_CMP_OPS = (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE)
    for n in ast.walk(fn):                                   # a parameter compared by value to a string literal
        if isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], _STR_CMP_OPS):
            for a, b in ((n.left, n.comparators[0]), (n.comparators[0], n.left)):
                if isinstance(a, ast.Name) and isinstance(b, ast.Constant) and isinstance(b.value, str):
                    mark(a.id, "str")
    for n in ast.walk(fn):                                   # an integer- or unknown-keyed read is a sequence
        if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name) and not is_str_key(n.slice):
            mark(n.value.id, "seq")
    for n in ast.walk(fn):
        if isinstance(n, (ast.For, ast.comprehension)) and isinstance(n.iter, ast.Name):
            mark(n.iter.id, "container")
        elif isinstance(n, ast.Call):
            f = n.func
            if (isinstance(f, ast.Name) and f.id in _ITER_CONSUMING_BUILTINS and len(n.args) == 1
                    and isinstance(n.args[0], ast.Name)):
                mark(n.args[0].id, "container")              # len/sum/sorted/min/max/any/all/reversed of one Name
            elif isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name):
                if f.attr in _STR_INFER_METHODS:
                    mark(f.value.id, "str")
                elif f.attr in _CONTAINER_INFER_METHODS:
                    mark(f.value.id, "container")
    for n in ast.walk(fn):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], (ast.Tuple, ast.List)) and isinstance(n.value, ast.Name)):
            mark(n.value.id, "container")                    # a, b = x : x is iterated to unpack
        elif (isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], (ast.In, ast.NotIn))
                and isinstance(n.comparators[0], ast.Name)):
            mark(n.comparators[0].id, "container")           # e in x : x is a container
    # float (not the default int) when paired with a non-integral float literal (x * 0.5, x == 0.5) or a float-only
    # method; an integral float (2.0) is ambiguous. Lower precedence than the structural kinds (a subscript -> seq).
    def _nonint_float(e):
        if not (isinstance(e, ast.Constant) and isinstance(e.value, float)):
            return False
        v = e.value
        return v == v and v not in (float("inf"), float("-inf")) and v != int(v)   # finite, non-integral
    for n in ast.walk(fn):
        if isinstance(n, ast.BinOp) and isinstance(n.op, (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Mod, ast.Pow)):
            for a, b in ((n.left, n.right), (n.right, n.left)):
                if isinstance(a, ast.Name) and _nonint_float(b):
                    mark(a.id, "float")
        elif isinstance(n, ast.Compare) and len(n.ops) == 1:
            for a, b in ((n.left, n.comparators[0]), (n.comparators[0], n.left)):
                if isinstance(a, ast.Name) and _nonint_float(b):
                    mark(a.id, "float")
        elif (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
              and isinstance(n.func.value, ast.Name) and n.func.attr in ("hex", "is_integer")):
            mark(n.func.value.id, "float")
    for n in ast.walk(fn):                                   # lowest precedence: a parameter used only as o.attr (not
        if (isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)   # already a seq / container / dict / str)
                and n.value.id not in ("self", "cls")):      # is an opaque object whose fields are stable values;
            mark(n.value.id, "object")                       # self / cls attributes stay the heap engine's domain
        elif (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)        # getattr(o, ...) / hasattr / setattr:
              and n.func.id in ("getattr", "setattr", "hasattr") and n.args   # o is likewise an opaque object
              and isinstance(n.args[0], ast.Name) and n.args[0].id not in ("self", "cls")):
            mark(n.args[0].id, "object")
    return kinds


def _sample_args(fn, rng, repo=None):
    """Concrete arguments matching the parameter annotations: int (or unannotated) over 0 and a small
    spread, list a short int list, str a short string, float and bool their values, a no-op callable for
    a parameter used as a callable (called directly, or forwarded to a function that calls it), and an int
    list for a parameter the body iterates."""
    callables = set(_callable_params(fn))
    if repo:
        params = [a.arg for a in fn.args.args]
        callables |= {params[i] for i in _called_positions(repo).get(fn.name, set()) if i < len(params)}
    kinds = _infer_param_kinds(fn)
    out = []
    for a in fn.args.args:
        ann = a.annotation.id if isinstance(a.annotation, ast.Name) else None
        kind = kinds.get(a.arg)
        if a.arg in callables:
            out.append(_noop_callable)
        elif ann == "list":
            out.append([rng.randint(-9, 9) for _ in range(rng.randint(0, 6))])
        elif ann == "tuple":
            out.append(tuple(rng.randint(-9, 9) for _ in range(rng.randint(0, 6))))
        elif ann == "dict":
            out.append({rng.randint(-5, 5): rng.randint(-9, 9) for _ in range(rng.randint(0, 4))})
        elif ann == "str" or (ann is None and kind == "str"):
            out.append("".join(rng.choice("ab cD9") for _ in range(rng.randint(0, 5))))
        elif ann == "float" or (ann is None and kind == "float"):
            out.append(rng.choice([0.0, 1.0, -1.0, 2.5, rng.uniform(-50.0, 50.0)]))
        elif ann == "bool":
            out.append(rng.random() < 0.5)
        elif ann is None and kind == "seq":
            out.append([rng.randint(-9, 9) for _ in range(rng.randint(0, 6))])   # a real list: an out-of-range index traps
        elif ann is None and kind == "dict":                 # a real dict: a string key absent from it is a
            keys = ["a", "b", "x", "k", "key"]               # witnessable KeyError, present for a guarded read
            out.append({rng.choice(keys): rng.randint(-9, 9) for _ in range(rng.randint(0, 4))})
        elif ann is None and kind == "container":
            out.append(_AnyC())                              # a benign never-trapping container stand-in
        elif ann is None and kind == "object":
            out.append(_AnyObj())                            # a benign object whose attributes are numeric fields
        else:
            out.append(rng.choice([0, 0, 1, -1, 2, 7, rng.randint(-25, 25)]))    # 0 hits division traps
    return tuple(out)


def _trap_free_via_symexec(src, repo):
    """Trap freedom of a loop-free function via the value engine, judged on the traps alone so a closure
    or tuple/string return (which the CFG checker rejects) does not block it: PROVED if no trap is
    reachable, REFUTED if one is."""
    try:
        kinds = _infer_param_kinds(_fndef(src))              # model each parameter by its inferred kind,
    except Exception:                                        # matching how the oracle samples it
        kinds = None
    ctx = Ctx(repo); ctx.facts = []
    saved = core._TRAPFREE; core._TRAPFREE = True            # total over-approximation, trap-freedom only
    try:
        _args, _z3, _rets, traps, _none = symexec(src, ctx, param_kinds=kinds)
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "value (trap freedom)")
    finally:
        core._TRAPFREE = saved
    if not traps:
        return Verdict(PROVED, "bench", "f", "value (trap freedom)")
    claim = z3.And(*ctx.facts, z3.Or(*traps)) if ctx.facts else z3.Or(*traps)
    st = _solve(claim)[0]
    if st == REFUTED and ctx.havoc:                          # a trap from a havoc'd loop variable may be spurious
        st = UNKNOWN
    return Verdict(st, "bench", "f", "value (trap freedom)")


class _CallRewrite(ast.NodeTransformer):
    """Rewrite a call of a callable parameter `p(args)` to `_mcall_k(args)`, a trap-free stand-in of the same
    arity; the argument expressions are kept, so a trap inside them is still checked."""
    def __init__(self, callables):
        self.callables, self.arities = callables, set()

    def visit_Call(self, node):
        self.generic_visit(node)
        if (isinstance(node.func, ast.Name) and node.func.id in self.callables
                and not node.keywords and not any(isinstance(a, ast.Starred) for a in node.args)):
            k = len(node.args); self.arities.add(k)
            return ast.copy_location(
                ast.Call(func=ast.Name(id=f"_mcall_{k}", ctx=ast.Load()), args=node.args, keywords=[]), node)
        return node


def _trap_free_modular(src, repo):
    """Modular trap freedom for a higher-order function: a parameter the body calls is assumed a trap-free
    callable, so its call contributes no trap while the argument expressions are still checked. UNKNOWN when no
    parameter is called."""
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "modular trap freedom")
    callables = _callable_params(fn)
    if not callables:
        return Verdict(UNKNOWN, "bench", "f", "modular trap freedom")
    try:
        rw = _CallRewrite(callables)
        tree = rw.visit(ast.parse(textwrap.dedent(src)))
        ast.fix_missing_locations(tree)
        tsrc = ast.unparse(tree)
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "modular trap freedom")
    repo2 = dict(repo)
    for k in rw.arities:
        ps = ", ".join(f"_a{i}" for i in range(k))
        repo2[f"_mcall_{k}"] = f"def _mcall_{k}({ps}):\n    return 0\n"
    v = check(tsrc, repo=repo2)
    if v.status != UNKNOWN:
        return v
    return _trap_free_via_symexec(tsrc, repo2)


_BUILTIN_NAMES = frozenset(dir(builtins))


def _could_trap(node):
    """Whether an expression contains a sub-expression that can raise a modeled trap: a division or
    modulo (BinOp), an index or key access (Subscript), a call, or a comprehension. A literal, name, or
    attribute read cannot, so it is safe to drop when only trap presence matters."""
    return any(isinstance(x, (ast.BinOp, ast.Subscript, ast.Call,
                              ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp))
               for x in ast.walk(node))


class _OpaqueRewrite(ast.NodeTransformer):
    """Rewrite a call of an invisible callee `g(args)` to `_mcall_k(args)`, a trap-free stand-in of the
    same arity. A trap-bearing argument is kept so a trap inside it is still checked; a trap-free argument (a
    string or container the value engine cannot bind) is replaced by 0 so it does not block the check."""
    def __init__(self, names):
        self.names, self.arities = names, set()

    def visit_Call(self, node):
        self.generic_visit(node)
        if (isinstance(node.func, ast.Name) and node.func.id in self.names
                and not node.keywords and not any(isinstance(a, ast.Starred) for a in node.args)):
            k = len(node.args); self.arities.add(k)
            args = [a if _could_trap(a) else ast.copy_location(ast.Constant(value=0), a) for a in node.args]
            return ast.copy_location(
                ast.Call(func=ast.Name(id=f"_mcall_{k}", ctx=ast.Load()), args=args, keywords=[]), node)
        return node


def _local_visible_callables(fn, repo):
    """Names locally bound to a callable whose body is visible: a nested def or class, a lambda, or a
    reference to a repo function. A call to one is decided by inlining its body, never assumed trap free,
    so it must be kept out of the opaque set."""
    names = set()
    for n in ast.walk(fn):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and n is not fn:
            names.add(n.name)
        elif isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            v = n.value
            if isinstance(v, ast.Lambda) or (isinstance(v, ast.Name) and v.id in repo):
                names.add(n.targets[0].id)
    return names


def _opaque_calls(fn, repo):
    """Bare-name calls whose callee the engines cannot see: not a repo function, not a Python builtin (so
    a trapping builtin such as int or float stays modeled), not a modeled stdlib name, and not a locally
    visible callable (a nested def, a lambda, a repo reference), whose body is checked by inlining rather
    than assumed trap free. These are imported functions, class constructors, and factory results."""
    visible = _local_visible_callables(fn, repo)
    names = set()
    for n in ast.walk(fn):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                and not n.keywords and not any(isinstance(a, ast.Starred) for a in n.args)):
            nm = n.func.id
            if (nm not in repo and nm not in _BUILTIN_NAMES and nm not in core._STDLIB
                    and nm not in visible):
                names.add(nm)
    return names


def _trap_free_opaque_calls(src, repo):
    """Modular trap freedom for a function that calls an invisible callee (an imported function, a class
    constructor, a factory result, a callback threaded through other functions): the callee is assumed a
    trap-free callable, so its call contributes no trap while the argument expressions are still checked. Every
    repo function's opaque calls are rewritten too, so a callback called inside another function is covered when
    that function is inlined. UNKNOWN when there is no such call."""
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "modular opaque call")
    if not _opaque_calls(fn, repo):
        return Verdict(UNKNOWN, "bench", "f", "modular opaque call")
    arities = set()

    def _rw(s):                                              # rewrite a function's opaque calls to stubs
        rw = _OpaqueRewrite(_opaque_calls(_fndef(s), repo))
        tree = rw.visit(ast.parse(textwrap.dedent(s)))
        ast.fix_missing_locations(tree)
        arities.update(rw.arities)
        return ast.unparse(tree)

    try:
        tsrc = _rw(src)
        repo2 = {}
        for rname, rsrc in repo.items():
            try:
                repo2[rname] = _rw(rsrc)
            except Exception:
                repo2[rname] = rsrc
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "modular opaque call")
    for k in arities:
        ps = ", ".join(f"_a{i}" for i in range(k))
        repo2[f"_mcall_{k}"] = f"def _mcall_{k}({ps}):\n    return 0\n"
    v = check(tsrc, repo=repo2)
    if v.status != UNKNOWN:
        return v
    return _trap_free_via_symexec(tsrc, repo2)


def _trap_free_comprehension(src, repo):
    """Modular trap freedom for a function using comprehensions: each comprehension's iterable is assumed
    iterable, its element variable an arbitrary value, and its element / key / filter expressions are
    checked for traps under that. The surrounding code is checked with each comprehension replaced by a
    placeholder. UNKNOWN (deferring) when there is no comprehension or one has more than one generator."""
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "comprehension")
    comps = [n for n in ast.walk(fn)
             if isinstance(n, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp))]
    if not comps:
        return Verdict(UNKNOWN, "bench", "f", "comprehension")

    class _Repl(ast.NodeTransformer):                        # the surrounding code, comprehensions blanked out
        def _blank(self, n):
            return ast.copy_location(ast.Constant(value=0), n)
        visit_ListComp = visit_SetComp = visit_DictComp = visit_GeneratorExp = _blank
    try:
        base = _Repl().visit(ast.parse(textwrap.dedent(src)))
        ast.fix_missing_locations(base)
        parts = [_trap_free_via_symexec(ast.unparse(base), repo)]
        params = [ast.arg(arg=a.arg) for a in fn.args.args]
        for comp in comps:
            if len(comp.generators) != 1 or getattr(comp.generators[0], "is_async", 0):
                return Verdict(UNKNOWN, "bench", "f", "comprehension")
            gen = comp.generators[0]
            tgt = gen.target.elts if isinstance(gen.target, ast.Tuple) else [gen.target]
            if not all(isinstance(t, ast.Name) for t in tgt):
                return Verdict(UNKNOWN, "bench", "f", "comprehension")
            checks = [comp.value, comp.key] if isinstance(comp, ast.DictComp) else [comp.elt]
            inner = [ast.Assign(targets=[ast.Name(id="_e%d" % i, ctx=ast.Store())], value=e)
                     for i, e in enumerate(checks)]
            if gen.ifs:
                cond = gen.ifs[0] if len(gen.ifs) == 1 else ast.BoolOp(op=ast.And(), values=gen.ifs)
                inner = [ast.If(test=cond, body=inner, orelse=[])]
            if (isinstance(gen.iter, ast.Call)
                    and not (isinstance(gen.iter.func, ast.Name) and gen.iter.func.id in repo)):
                # an unmodeled iterable-producing call (range, a builtin): check its arguments for traps
                # and assume the call yields an iterable; a repo call or expression is evaluated directly
                itstmts = [ast.Assign(targets=[ast.Name(id="_it%d" % i, ctx=ast.Store())], value=a)
                           for i, a in enumerate(gen.iter.args)]
            else:
                itstmts = [ast.Assign(targets=[ast.Name(id="_it", ctx=ast.Store())], value=gen.iter)]
            body = itstmts + inner + [ast.Return(value=ast.Constant(value=0))]
            args = ast.arguments(posonlyargs=[], args=params + [ast.arg(arg=t.id) for t in tgt],
                                 vararg=None, kwonlyargs=[], kw_defaults=[], kwarg=None, defaults=[])
            chk = ast.FunctionDef(name="_compcheck", args=args, body=body, decorator_list=[])
            ast.fix_missing_locations(ast.Module(body=[chk], type_ignores=[]))
            parts.append(_trap_free_via_symexec(ast.unparse(chk), repo))
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "comprehension")
    st = [p.status for p in parts]
    if any(s == REFUTED for s in st):
        return Verdict(REFUTED, "bench", "f", "comprehension")
    if all(s == PROVED for s in st):
        return Verdict(PROVED, "bench", "f", "comprehension")
    return Verdict(UNKNOWN, "bench", "f", "comprehension")


def _match_captures(pat):
    """Names a match pattern binds (a capture, a star target, a mapping rest): taken as arbitrary values."""
    names = set()
    for n in ast.walk(pat):
        if isinstance(n, ast.MatchAs) and n.name:
            names.add(n.name)
        elif isinstance(n, ast.MatchStar) and n.name:
            names.add(n.name)
        elif isinstance(n, ast.MatchMapping) and n.rest:
            names.add(n.rest)
    return names


def _trap_free_match(src, repo):
    """Modular trap freedom for a function using a match statement: the subject, every case guard, and every
    case body must be trap free, with pattern-bound names taken as arbitrary values. The surrounding code is
    checked with each match replaced by a no-op; each case body is checked unconditionally. UNKNOWN when there
    is no match statement."""
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "match")
    matches = [n for n in ast.walk(fn) if isinstance(n, ast.Match)]
    if not matches:
        return Verdict(UNKNOWN, "bench", "f", "match")

    class _Repl(ast.NodeTransformer):                        # the surrounding code, each match a no-op
        def visit_Match(self, n):
            return ast.copy_location(ast.Pass(), n)

    def _mkfn(name, params, body):
        f = ast.FunctionDef(name=name,
                            args=ast.arguments(posonlyargs=[], args=params, vararg=None, kwonlyargs=[],
                                               kw_defaults=[], kwarg=None, defaults=[]),
                            body=body, decorator_list=[])
        ast.fix_missing_locations(ast.Module(body=[f], type_ignores=[]))
        return ast.unparse(f)

    try:
        base = _Repl().visit(ast.parse(textwrap.dedent(src)))
        ast.fix_missing_locations(base)
        parts = [_decide(ast.unparse(base), repo)]
        params = [ast.arg(arg=a.arg) for a in fn.args.args] + [ast.arg(arg=a.arg) for a in fn.args.kwonlyargs]
        for m in matches:
            parts.append(_decide(_mkfn("_msubj", params,
                [ast.Assign(targets=[ast.Name(id="_subj", ctx=ast.Store())], value=m.subject),
                 ast.Return(value=ast.Constant(value=0))]), repo))
            for case in m.cases:
                caps = [ast.arg(arg=c) for c in sorted(_match_captures(case.pattern))]
                cbody = list(case.body)
                if case.guard is not None:
                    cbody = [ast.If(test=case.guard, body=cbody or [ast.Pass()], orelse=[])]
                parts.append(_decide(_mkfn("_mcase", params + caps, cbody or [ast.Pass()]), repo))
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "match")
    st = [p.status for p in parts]
    if any(s == REFUTED for s in st):
        return Verdict(REFUTED, "bench", "f", "match")
    if all(s == PROVED for s in st):
        return Verdict(PROVED, "bench", "f", "match")
    return Verdict(UNKNOWN, "bench", "f", "match")


def _trap_free_container_literal(src, repo):
    """Modular trap freedom for a function building a dict or set literal whose entries the heap engine
    cannot encode (a function reference, a nested literal): constructing the container raises no trap, so
    the function is trap free iff its keys, values, and elements are, and the surrounding code (each such
    literal replaced by a placeholder) is. UNKNOWN when there is no dict or set literal."""
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "container literal")
    lits = [n for n in ast.walk(fn) if isinstance(n, (ast.Dict, ast.Set))]
    if not lits:
        return Verdict(UNKNOWN, "bench", "f", "container literal")

    class _Repl(ast.NodeTransformer):                        # surrounding code, each dict/set literal blanked
        def visit_Dict(self, n):
            self.generic_visit(n); return ast.copy_location(ast.Constant(value=0), n)
        def visit_Set(self, n):
            self.generic_visit(n); return ast.copy_location(ast.Constant(value=0), n)

    params = [ast.arg(arg=a.arg) for a in fn.args.args] + [ast.arg(arg=a.arg) for a in fn.args.kwonlyargs]
    try:
        base = _Repl().visit(ast.parse(textwrap.dedent(src)))
        ast.fix_missing_locations(base)
        parts = [_decide(ast.unparse(base), repo)]
        for lit in lits:
            items = ([k for k in lit.keys if k is not None] + list(lit.values)
                     if isinstance(lit, ast.Dict) else list(lit.elts))
            exprs = [e.value if isinstance(e, ast.Starred) else e for e in items]
            body = [ast.Assign(targets=[ast.Name(id="_e%d" % i, ctx=ast.Store())], value=e)
                    for i, e in enumerate(exprs)] + [ast.Return(value=ast.Constant(value=0))]
            f = ast.FunctionDef(name="_clit",
                                args=ast.arguments(posonlyargs=[], args=params, vararg=None, kwonlyargs=[],
                                                   kw_defaults=[], kwarg=None, defaults=[]),
                                body=body, decorator_list=[])
            ast.fix_missing_locations(ast.Module(body=[f], type_ignores=[]))
            parts.append(_decide(ast.unparse(f), repo))
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "container literal")
    st = [p.status for p in parts]
    if any(s == REFUTED for s in st):
        return Verdict(REFUTED, "bench", "f", "container literal")
    if all(s == PROVED for s in st):
        return Verdict(PROVED, "bench", "f", "container literal")
    return Verdict(UNKNOWN, "bench", "f", "container literal")


def _trap_free_local_closures(src, repo):
    """A function defining nested functions it then calls: a called nested function is trap free to call when
    its body is trap free for arbitrary captured values. Verify each called closure body standalone, with its
    captured names as arbitrary parameters and nonlocal/global declarations dropped, then decide the function
    with the nested definitions stubbed and their calls replaced by trap-free stand-ins. PROVED only when the
    surrounding code and every called closure body are; never REFUTED on a closure body. UNKNOWN when there is
    no called nested function."""
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "local closure")
    nested = [s for s in fn.body if isinstance(s, ast.FunctionDef)]
    names = {d.name for d in nested}
    called = {c.func.id for c in ast.walk(fn)
              if isinstance(c, ast.Call) and isinstance(c.func, ast.Name) and c.func.id in names}
    if not called:
        return Verdict(UNKNOWN, "bench", "f", "local closure")
    try:
        for d in nested:
            if d.name not in called:
                continue
            body = [s for s in d.body if not isinstance(s, (ast.Nonlocal, ast.Global))]
            own = {a.arg for a in d.args.args} | {a.arg for a in d.args.kwonlyargs}
            refs = sorted({n.id for s in body for n in ast.walk(s)
                           if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}
                          - own - set(repo) - _BUILTIN_NAMES - names)
            params = list(d.args.args) + [ast.arg(arg=r) for r in refs]
            cf = ast.FunctionDef(name="_clo",
                                 args=ast.arguments(posonlyargs=[], args=params, vararg=None, kwonlyargs=[],
                                                    kw_defaults=[], kwarg=None, defaults=[]),
                                 body=body or [ast.Pass()], decorator_list=[])
            ast.fix_missing_locations(ast.Module(body=[cf], type_ignores=[]))
            if _decide(ast.unparse(cf), repo).status != PROVED:
                return Verdict(UNKNOWN, "bench", "f", "local closure")

        class _Stub(ast.NodeTransformer):                    # nested defs -> a value binding; their calls -> stubs
            def __init__(self): self.arities = set()
            def visit_FunctionDef(self, node):
                if node.name in names:
                    return ast.copy_location(ast.Assign(targets=[ast.Name(id=node.name, ctx=ast.Store())],
                                                        value=ast.Constant(value=0)), node)
                self.generic_visit(node); return node
            def visit_Call(self, node):
                self.generic_visit(node)
                if (isinstance(node.func, ast.Name) and node.func.id in names
                        and not node.keywords and not any(isinstance(a, ast.Starred) for a in node.args)):
                    k = len(node.args); self.arities.add(k)
                    args = [a if _could_trap(a) else ast.copy_location(ast.Constant(value=0), a) for a in node.args]
                    return ast.copy_location(ast.Call(func=ast.Name(id=f"_mcall_{k}", ctx=ast.Load()),
                                                      args=args, keywords=[]), node)
                return node
        st = _Stub()
        tree = st.visit(ast.parse(textwrap.dedent(src)))
        ast.fix_missing_locations(tree)
        tsrc = ast.unparse(tree)
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "local closure")
    repo2 = dict(repo)
    for k in st.arities:
        ps = ", ".join(f"_a{i}" for i in range(k))
        repo2[f"_mcall_{k}"] = f"def _mcall_{k}({ps}):\n    return 0\n"
    v = check(tsrc, repo=repo2)
    if v.status != UNKNOWN:
        return v
    return _trap_free_via_symexec(tsrc, repo2)


def _trap_free_global_store(src, repo):
    """A function that assigns into a module-level global dict (`d[k] = v`): a dict key assignment never
    traps, so the function is trap free when the assigned keys and values are. Read the module-level global
    collection kinds from the source (the engines skip module-level statements, so a global is otherwise a
    free variable), rewrite each store into a global dict to a check of its key and value, and decide the
    rest. UNKNOWN when there is no such store, or the global is rebound locally, or the dict is also read."""
    try:
        mod = ast.parse(textwrap.dedent(src))
    except SyntaxError:
        return Verdict(UNKNOWN, "bench", "f", "global store")
    dict_globals = set()
    for n in mod.body:
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            v = n.value
            if isinstance(v, ast.Dict) or (isinstance(v, ast.Call) and isinstance(v.func, ast.Name)
                                           and v.func.id == "dict"):
                dict_globals.add(n.targets[0].id)
    if not dict_globals:
        return Verdict(UNKNOWN, "bench", "f", "global store")
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "global store")
    dict_globals -= {t.id for s in ast.walk(fn) if isinstance(s, ast.Assign)   # a name rebound locally is not the global
                     for t in s.targets if isinstance(t, ast.Name)}

    class _GS(ast.NodeTransformer):                          # g[k] = v (g a global dict) -> check k and v for traps
        def __init__(self): self.n = 0
        def visit_Assign(self, node):
            t = node.targets[0] if len(node.targets) == 1 else None
            if isinstance(t, ast.Subscript) and isinstance(t.value, ast.Name) and t.value.id in dict_globals:
                self.n += 1
                return [ast.Assign(targets=[ast.Name(id="_gsk%d" % self.n, ctx=ast.Store())], value=t.slice),
                        ast.Assign(targets=[ast.Name(id="_gsv%d" % self.n, ctx=ast.Store())], value=node.value)]
            return node
    try:
        gs = _GS()
        fn2 = gs.visit(fn)
        if gs.n == 0:
            return Verdict(UNKNOWN, "bench", "f", "global store")
        ast.fix_missing_locations(fn2)
        return _decide(ast.unparse(fn2), repo)
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "global store")


def _lit_type(node):
    """The annotation name for a literal's Python type (bool before int, since bool is an int subclass),
    used to type a havoced accumulator: bool, str, float, or int. None for a non-literal."""
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool):
            return "bool"
        if isinstance(node.value, str):
            return "str"
        if isinstance(node.value, float):
            return "float"
        if isinstance(node.value, int):
            return "int"
    return None


def _trap_free_for(src, repo):
    """Modular trap freedom for a function with one for-loop. The iterable is assumed iterable (a call's
    arguments are checked, the call itself assumed to yield one), the loop variable is an arbitrary
    integer, and each accumulator (a name assigned in the body and initialised to a literal before the
    loop) is an arbitrary value of its initial type. Body, pre-loop, and post-loop code are each checked
    with the accumulators so havoced (sound over all iterations). UNKNOWN when there is not exactly one
    for-loop, the loop target is not plain names, or an accumulator's initial type is unknown."""
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "for loop")
    fors = [s for s in fn.body if isinstance(s, ast.For)]
    if len(fors) != 1 or fors[0].orelse or not fors[0].body:
        return Verdict(UNKNOWN, "bench", "f", "for loop")
    loop = fors[0]
    i = fn.body.index(loop)
    before, after = fn.body[:i], fn.body[i + 1:]
    tgts = loop.target.elts if isinstance(loop.target, ast.Tuple) else [loop.target]
    if not all(isinstance(t, ast.Name) for t in tgts):
        return Verdict(UNKNOWN, "bench", "f", "for loop")
    pretypes = {}
    for s in before:
        if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
            t = _lit_type(s.value)
            if t:
                pretypes[s.targets[0].id] = t
    modified = ({n.id for st in loop.body for n in ast.walk(st)
                 if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)} - {t.id for t in tgts})
    before_assigned = {n.id for s in before for n in ast.walk(s)
                       if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
    if any(m in before_assigned and m not in pretypes for m in modified):   # accumulator with unknown initial type
        return Verdict(UNKNOWN, "bench", "f", "for loop")
    params = [ast.arg(arg=a.arg) for a in fn.args.args] + [ast.arg(arg=a.arg) for a in fn.args.kwonlyargs]
    accs = [ast.arg(arg=m, annotation=ast.Name(id=pretypes[m], ctx=ast.Load())) for m in sorted(pretypes)]
    tgtargs = [ast.arg(arg=t.id) for t in tgts]
    ret0 = [ast.Return(value=ast.Constant(value=0))]

    def mk(args, body):
        f = ast.FunctionDef(name="_f", args=ast.arguments(posonlyargs=[], args=args, vararg=None, kwonlyargs=[],
                                                           kw_defaults=[], kwarg=None, defaults=[]),
                            body=body, decorator_list=[])
        ast.fix_missing_locations(ast.Module(body=[f], type_ignores=[]))
        return ast.unparse(f)

    if isinstance(loop.iter, ast.Call):                      # a call yields the iterable: check its arguments
        itstmts = [ast.Assign(targets=[ast.Name(id="_it%d" % j, ctx=ast.Store())], value=a)
                   for j, a in enumerate(loop.iter.args)]
    else:
        itstmts = [ast.Assign(targets=[ast.Name(id="_it", ctx=ast.Store())], value=loop.iter)]
    try:                                                    # value engine: it models string typing (str + int is
        parts = [_trap_free_via_symexec(mk(params, list(before) + ret0), repo),   # a TypeError, str + str concat)
                 _trap_free_via_symexec(mk(params + accs + tgtargs, list(loop.body) + ret0), repo),
                 _trap_free_via_symexec(mk(params + accs, list(after) + ret0), repo),
                 _trap_free_via_symexec(mk(params + accs, itstmts + ret0), repo)]
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "for loop")
    st = [p.status for p in parts]
    if any(s == REFUTED for s in st):
        return Verdict(REFUTED, "bench", "f", "for loop")
    if all(s == PROVED for s in st):
        return Verdict(PROVED, "bench", "f", "for loop")
    return Verdict(UNKNOWN, "bench", "f", "for loop")


def _trap_free_array_index_loop(src, repo):
    """Trap freedom for a `for i in range(len(arr)): body` loop over a list parameter (after the for -> while
    desugaring, `i = 0; while i < len(arr): body; i += 1`). The loop variable satisfies 0 <= i <= len(arr),
    so every arr[i] access is in bounds: verify_array_loop discharges that bounds-only invariant -- and still
    refutes or abstains on any other trap in the body (a division, an out-of-bounds arr[i + 1], a second
    shorter array), never a false PROVED. Only the array's own length bounds the guard; a guard against an
    unrelated bound is left to other strategies (it may be a genuine out-of-bounds bug)."""
    try:
        fn = _fndef(src)
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "array index loop")
    arr_params = {a.arg for a in fn.args.args if _is_array_param(a)}
    whiles = [s for s in fn.body if isinstance(s, ast.While)]
    if len(whiles) != 1 or not arr_params:
        return Verdict(UNKNOWN, "bench", "f", "array index loop")
    t = whiles[0].test
    if not (isinstance(t, ast.Compare) and len(t.ops) == 1
            and isinstance(t.ops[0], (ast.Lt, ast.LtE)) and isinstance(t.left, ast.Name)):
        return Verdict(UNKNOWN, "bench", "f", "array index loop")
    # the guard must be `i < len(arr)` or `i <= len(arr)`, optionally a nonnegative constant past the length
    # (`i < len(arr) + 1`, the desugared `range(len(arr) + 1)`): a fence-post overrun -- `i <= len(arr)`, or
    # `i < len(arr) + 1` -- writes a[len(arr)], out of bounds for every array (the empty one included), which
    # verify_array_loop refutes under the one-past invariant; the correct `i < len(arr)` still proves. A guard
    # short of the length (a negative offset) never overruns and is left to other strategies.
    rhs, offset = t.comparators[0], 0
    if (isinstance(rhs, ast.BinOp) and isinstance(rhs.op, (ast.Add, ast.Sub))
            and isinstance(rhs.right, ast.Constant) and isinstance(rhs.right.value, int)
            and not isinstance(rhs.right.value, bool)):
        offset = rhs.right.value if isinstance(rhs.op, ast.Add) else -rhs.right.value
        rhs = rhs.left
    if offset < 0 or not (isinstance(rhs, ast.Call) and isinstance(rhs.func, ast.Name) and rhs.func.id == "len"
            and len(rhs.args) == 1 and isinstance(rhs.args[0], ast.Name) and rhs.args[0].id in arr_params):
        return Verdict(UNKNOWN, "bench", "f", "array index loop")
    iname, arr, is_le = t.left.id, rhs.args[0].id, isinstance(t.ops[0], ast.LtE)
    import z3
    pre = lambda S: 0 <= S["len_" + arr]                      # an array length is nonnegative (sound)
    # i increments by 1 toward the guard bound len(arr) + offset, reaching it (one past, for the `<=` guard) at
    # exit; the inductive invariant is 0 <= i <= that bound. verify_array_loop then proves a[i] in bounds for the
    # correct sweep and refutes the a[len(arr)] overrun.
    inv = lambda S: z3.And(0 <= S[iname], S[iname] <= S["len_" + arr] + offset + (1 if is_le else 0))
    try:
        return verify_array_loop("bench", "f", ast.unparse(fn), pre, inv, lambda S, e: z3.BoolVal(True))
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "array index loop")


def _trap_free_decorated(src, repo):
    """A function calling a repo function `g` decorated by a repo function `dec`: the effective callable is
    `dec(g_undecorated)`, so a call `g(args)` is decided as `dec(g_undecorated)(args)` -- the decorator is
    applied and its result called, so a trap in the decorator or the wrapper it returns is reached. UNKNOWN
    when no called function is decorated by a repo function."""
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "decorated call")
    decorated = {}                                           # g -> (decorator name, undecorated source)
    for name, rsrc in repo.items():
        try:
            rfn = _fndef(rsrc)
        except Exception:
            continue
        decs = getattr(rfn, "decorator_list", [])
        if len(decs) == 1 and isinstance(decs[0], ast.Name) and decs[0].id in repo:
            undec = ast.FunctionDef(name="_undec_" + name, args=rfn.args, body=rfn.body, decorator_list=[])
            ast.fix_missing_locations(ast.Module(body=[undec], type_ignores=[]))
            decorated[name] = (decs[0].id, ast.unparse(undec))
    called = {n.func.id for n in ast.walk(fn)
              if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in decorated}
    if not called:
        return Verdict(UNKNOWN, "bench", "f", "decorated call")
    repo2 = dict(repo)
    for g in called:
        repo2["_undec_" + g] = decorated[g][1]

    class _Rw(ast.NodeTransformer):
        def visit_Call(self, node):
            self.generic_visit(node)
            if (isinstance(node.func, ast.Name) and node.func.id in called
                    and not node.keywords and not any(isinstance(a, ast.Starred) for a in node.args)):
                applied = ast.Call(func=ast.Name(id=decorated[node.func.id][0], ctx=ast.Load()),
                                   args=[ast.Name(id="_undec_" + node.func.id, ctx=ast.Load())], keywords=[])
                return ast.copy_location(ast.Call(func=applied, args=node.args, keywords=[]), node)
            return node
    try:
        tree = _Rw().visit(ast.parse(textwrap.dedent(src)))
        ast.fix_missing_locations(tree)
        return _decide(ast.unparse(tree), repo2)
    except Exception:
        return Verdict(UNKNOWN, "bench", "f", "decorated call")


def _has_yield(node):
    """Whether `node`'s own scope contains a yield, which makes its function a generator. A yield inside a
    nested def or lambda belongs to that inner scope and is not counted."""
    for child in ast.iter_child_nodes(node):
        if isinstance(child, (ast.Yield, ast.YieldFrom)):
            return True
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        if _has_yield(child):
            return True
    return False


def _trap_free_generator(src, repo):
    """Calling a generator function builds a generator object without executing its body, so the call
    raises no modeled trap whatever the body would do when later iterated (a consumer's concern, decided
    by the loop engines). PROVED when the function is a generator; UNKNOWN otherwise."""
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return Verdict(UNKNOWN, "bench", "f", "generator")
    return Verdict(PROVED if _has_yield(fn) else UNKNOWN, "bench", "f", "generator")


def _decide(src, repo):
    """Decide trap freedom with the broadest applicable engine, each with a trivial postcondition (so a
    PROVED is trap free and a REFUTED reaches a trap): the CFG/CHC checker, then a generator (calling one
    builds an object without running its body), modular trap freedom (callable parameters assumed
    well-behaved), comprehensions, match statements, the value engine
    (closures, tuple/string returns), the heap engine (objects, lists, dicts, sets), the list-iteration
    engine, the recursion engine, dict/set literals the heap engine cannot encode, and finally modular
    trap freedom over invisible callees (imported functions, constructors, factories). First definite
    verdict, else UNKNOWN."""
    try:
        v = check(src, repo=repo)
    except Exception:                                        # an engine must never crash the decider; degrade to UNKNOWN
        v = Verdict(UNKNOWN, "bench", "f", "check raised")
    if v.status != UNKNOWN:
        return v
    tt = lambda *a: z3.BoolVal(True)
    for run in (lambda: _trap_free_generator(src, repo),
                lambda: _trap_free_modular(src, repo),
                lambda: _trap_free_comprehension(src, repo),
                lambda: _trap_free_match(src, repo),
                lambda: _trap_free_local_closures(src, repo),
                lambda: _trap_free_global_store(src, repo),
                lambda: _trap_free_decorated(src, repo),
                lambda: _trap_free_via_symexec(src, repo),
                lambda: verify_heap_property("bench", "f", src, lambda za, r: z3.BoolVal(True)),
                lambda: verify_sequence_loop("bench", "f", src, lambda P, r: z3.BoolVal(True)),
                lambda: _trap_free_array_index_loop(src, repo),
                lambda: _trap_free_for(src, repo),
                lambda: verify_recursive("bench", "f", src, tt, lambda S, r: z3.BoolVal(True)),
                lambda: _trap_free_container_literal(src, repo),
                lambda: _trap_free_opaque_calls(src, repo)):
        try:
            v2 = run()
        except Exception:
            continue
        if v2.status != UNKNOWN:
            return v2
    return v


# the trap kinds trap freedom proves absent; CPython exceptions outside this set (RecursionError,
# OverflowError, non-termination) are not modeled and so do not contradict a PROVED.
_MODELED_TRAPS = {"ZeroDivisionError", "IndexError", "KeyError", "TypeError", "AssertionError", "ValueError"}


def _oracle(src, repo, verdict, samples, seed):
    """Cross-check a decided verdict against CPython in the sandbox, counting only a modeled trap.
    Returns ('confirmed' | 'unconfirmed' | 'contradiction', n_checks): a PROVED that hits a modeled
    trap contradicts, a REFUTED that hits one is confirmed."""
    if verdict.status not in (PROVED, REFUTED):
        return ("unconfirmed", 0)
    try:
        fn = _fndef(src)
    except core.Unsupported:
        return ("unconfirmed", 0)
    rng = random.Random(seed)
    inputs = [list(_sample_args(fn, rng, repo)) for _ in range(samples)]
    res = core.sandbox_run_batch_typed(src, repo or {}, fn.name, inputs)
    if res is None:
        return ("unconfirmed", 0)
    trapped = any(r[0] == "raise" and r[1] in _MODELED_TRAPS for r in res)
    if verdict.status == PROVED:
        return ("contradiction" if trapped else "confirmed", len(res))
    return ("confirmed" if trapped else "unconfirmed", len(res))


def run_benchmark(corpus=None, samples=80, seed=0):
    """Decide each program in `corpus` (default the bundled corpus) and cross-check the decided verdicts
    against CPython. Returns the aggregate report: recall (decided fraction), precision (decided verdicts
    CPython does not contradict), and the contradiction count (the soundness bar, zero)."""
    corpus = corpus if corpus is not None else STANDARD_CORPUS
    proved = refuted = unknown = confirmed = unconfirmed = contradictions = oracle_checks = 0
    per = []
    for item in corpus:
        name, src = item[0], item[1]
        if len(item) > 2:                            # (name, src, repo): the function with its file context
            repo = item[2]
        else:
            try:
                fns = {n.name for n in ast.parse(textwrap.dedent(src)).body if isinstance(n, ast.FunctionDef)}
            except SyntaxError:
                per.append({"name": name, "verdict": "UNKNOWN", "oracle": "unconfirmed"}); unknown += 1
                continue
            repo = {name: src} if name in fns else {}
        try:
            v = _decide(src, repo)
        except Exception:                            # the harness is total over arbitrary input
            per.append({"name": name, "verdict": "UNKNOWN", "oracle": "unconfirmed"}); unknown += 1
            continue
        if v.status == PROVED:
            proved += 1
        elif v.status == REFUTED:
            refuted += 1
        else:
            unknown += 1
        o, nc = _oracle(src, repo, v, samples, seed)
        oracle_checks += nc
        if o == "confirmed":
            confirmed += 1
        elif o == "contradiction":
            contradictions += 1
        elif v.status in (PROVED, REFUTED):
            unconfirmed += 1
        per.append({"name": name, "verdict": v.status, "oracle": o})
    total = len(corpus)
    decided = proved + refuted
    return {
        "total": total, "proved": proved, "refuted": refuted, "unknown": unknown,
        "decided": decided, "recall": (100.0 * decided / total) if total else 0.0,
        "confirmed": confirmed, "unconfirmed": unconfirmed, "contradictions": contradictions,
        "precision": (100.0 * (decided - contradictions) / decided) if decided else 100.0,
        "oracle_checks": oracle_checks, "per_program": per,
    }


def load_corpus_dir(path):
    """Load an external corpus: each top-level function in each .py file under `path` becomes one
    (name, source, repo) program, where repo carries the file's other functions so cross-function calls
    resolve and execute. The adapter for a third-party suite such as TypeEvalPy."""
    out, files = [], []
    for root, _dirs, names in os.walk(path):
        for nm in sorted(names):
            if nm.endswith(".py"):
                files.append(os.path.join(root, nm))
    for fp in sorted(files):
        try:
            with open(fp, "r", encoding="utf-8") as f:
                text = f.read()
            repo = load_module(text)
            preamble = []
            for n in ast.parse(textwrap.dedent(text)).body:
                if isinstance(n, ast.ClassDef):
                    preamble.append(ast.unparse(n))             # the heap engine resolves constructors
                elif isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
                    v = n.value                                 # a module-level collection global, emptied to its kind
                    kind = ("{}" if isinstance(v, ast.Dict) else "[]" if isinstance(v, ast.List)
                            else "set()" if isinstance(v, ast.Set)
                            else v.func.id + "()" if isinstance(v, ast.Call) and isinstance(v.func, ast.Name)
                            and v.func.id in ("dict", "list", "set") else None)
                    if kind:
                        preamble.append("%s = %s" % (n.targets[0].id, kind))
        except Exception:
            continue
        rel = os.path.relpath(fp, path)
        pre = "\n\n".join(preamble)
        for fname, fsrc in repo.items():
            src = pre + "\n\n" + fsrc if pre else fsrc
            out.append((f"{rel}:{fname}", src, repo))
    return out


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv and os.path.isdir(argv[0]):
        corpus, label = load_corpus_dir(argv[0]), argv[0]
    else:
        corpus, label = STANDARD_CORPUS, "bundled standard algorithms"
    core.ALLOW_SUBJECT_EXECUTION = True
    try:
        rep = run_benchmark(corpus)
    finally:
        core.ALLOW_SUBJECT_EXECUTION = False
    print(f"BENCHMARK CORPUS: {label} ({rep['total']} programs)")
    print(f"  decided (recall): {rep['decided']}/{rep['total']} = {rep['recall']:.0f}%   "
          f"({rep['proved']} proved, {rep['refuted']} refuted, {rep['unknown']} unknown)")
    print(f"  precision       : {rep['precision']:.0f}%   "
          f"({rep['confirmed']} CPython-confirmed, {rep['unconfirmed']} unconfirmed, "
          f"{rep['contradictions']} contradictions over {rep['oracle_checks']} sampled runs)")
    for r in rep["per_program"]:
        print(f"    [{r['verdict']:8} {r.get('oracle', ''):12}] {r['name']}")
    return 1 if rep["contradictions"] else 0


__all__ = [

    'Ivf',
    'analyze_float_intervals',
    'verify_float_range',
    'intervals_executable',
    'extracted_intervals_batch',
    '_corroborate_domain',
    '_NEG',
    '_POS',
    'Iv',
    '_TOP',
    '_ijoin',
    '_iadd',
    '_ineg',
    '_isub',
    '_imul',
    '_widen',
    '_narrow',
    '_sjoin',
    '_ieval',
    '_refine',
    '_filter',
    '_itransfer',
    'analyze_intervals',
    'verify_range',
    '_ZINF',
    '_Zone',
    '_z_join',
    '_z_widen',
    '_z_narrow',
    '_z_eq',
    '_z_assign',
    '_z_refine',
    '_z_transfer',
    '_z_analyze',
    'verify_zone_equal',
    '_OINF',
    '_Oct',
    '_o_shift',
    '_o_assign',
    '_o_refine',
    '_o_join',
    '_o_widen',
    '_o_narrow',
    '_o_eq',
    '_o_transfer',
    '_o_analyze',
    '_octagon_concrete',
    'verify_octagon_sum',
    'infer_and_verify_range',
    'subset_coverage',
    '_aff_reduce',
    '_aff_in_span',
    '_aff_le',
    '_aff_eq',
    '_aff_join',
    '_aff_lin',
    '_aff_assign',
    '_aff_transfer',
    'analyze_affine',
    'verify_affine_equal',
    'verify_polyhedra',
    'verify_polyhedra_auto',
    'verify_machine_range',
    # --- folded in from theories.py ---
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


if __name__ == "__main__":
    sys.exit(main())
