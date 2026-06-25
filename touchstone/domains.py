"""Abstract interpretation: the interval, zone (difference-bound), octagon, Karr affine-
equality, template-polyhedra, and machine-integer domains, plus subset coverage. Every PROVED here
is independently re-derived by the CHC engine when core.CROSS_VALIDATE_DOMAINS."""
import ast
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
]
