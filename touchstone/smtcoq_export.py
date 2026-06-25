"""Export the engine's integer obligations as SMTCoq goals. A PROVED (UNSAT) refutation query is recorded;
the linear-integer ones are translated to SMTCoq's boolean-over-Z form and written as Coq goals proved by
`verit`, which re-checks the veriT certificate in Coq's kernel. Translation is partial: anything outside
quantifier-free linear integer arithmetic (floats, arrays, strings, division, nonlinear terms) is skipped."""
import z3
from . import core
from .engines import verify_equiv, verify_predicate, verify_deductive


class _NoCoq(Exception):
    """The term is outside the translatable linear-integer fragment."""


def _coq_var(t, vmap):
    name = t.decl().name()
    if name not in vmap:
        vmap[name] = f"v{len(vmap)}"
    return vmap[name]


def _flatten_ac(t, kind):
    """Operands of an associative-commutative node, flattened through nested same-kind nodes, so that
    (and a (and b c)) and (and (and a b) c) yield the same operand list [a, b, c]."""
    out = []
    for c in t.children():
        if z3.is_app(c) and c.decl().kind() == kind:
            out.extend(_flatten_ac(c, kind))
        else:
            out.append(c)
    return out


def _free_int_var_names(t):
    """Names of the free integer constants in t. Returned as a set; the caller orders them, so the v0/v1/...
    assignment and the serialization are reproducible across processes (z3 does not fix a term order)."""
    names, seen, stack = set(), set(), [t]
    while stack:
        n = stack.pop()
        if not z3.is_ast(n):
            continue
        i = n.get_id()
        if i in seen:
            continue
        seen.add(i)
        if z3.is_const(n) and z3.is_int(n) and not z3.is_int_value(n):
            names.add(n.decl().name())
        if z3.is_app(n):
            stack.extend(n.children())
    return names


def _z_int(t, vmap):
    if not z3.is_int(t):
        raise _NoCoq("non-integer term")
    if z3.is_int_value(t):
        n = t.as_long()
        return f"({n})" if n < 0 else str(n)
    if z3.is_const(t):
        return _coq_var(t, vmap)
    if not z3.is_app(t):
        raise _NoCoq("opaque int term")
    k, a = t.decl().kind(), t.children()
    if k == z3.Z3_OP_ADD:                                  # commutative: sort operands for a canonical form
        return "(" + " + ".join(sorted(_z_int(c, vmap) for c in _flatten_ac(t, k))) + ")"
    if k == z3.Z3_OP_SUB:
        return "(" + " - ".join(_z_int(c, vmap) for c in a) + ")"
    if k == z3.Z3_OP_UMINUS:
        return f"(- {_z_int(a[0], vmap)})"
    if k == z3.Z3_OP_MUL:
        flat = _flatten_ac(t, k)
        if len([c for c in flat if not z3.is_int_value(c)]) > 1:
            raise _NoCoq("nonlinear multiplication")
        return "(" + " * ".join(sorted(_z_int(c, vmap) for c in flat)) + ")"
    if k == z3.Z3_OP_ITE:
        return f"(if {_z_bool(a[0], vmap)} then {_z_int(a[1], vmap)} else {_z_int(a[2], vmap)})"
    raise _NoCoq(f"int op {t.decl().name()}")              # idiv / mod / rem and the rest are left out


def _foldb(op, parts):
    r = parts[-1]
    for p in reversed(parts[:-1]):
        r = f"({op} {p} {r})"
    return r


def _z_bool(t, vmap):
    if not z3.is_bool(t):
        raise _NoCoq("non-boolean term")
    if z3.is_true(t):
        return "true"
    if z3.is_false(t):
        return "false"
    if not z3.is_app(t):
        raise _NoCoq("opaque bool term")
    k, a = t.decl().kind(), t.children()
    if k == z3.Z3_OP_EQ:                                   # equality is symmetric: sort the two sides
        if z3.is_bool(a[0]):
            p = sorted([_z_bool(a[0], vmap), _z_bool(a[1], vmap)])
            return f"(Bool.eqb {p[0]} {p[1]})"
        p = sorted([_z_int(a[0], vmap), _z_int(a[1], vmap)])
        return f"(Z.eqb {p[0]} {p[1]})"
    if k == z3.Z3_OP_DISTINCT and len(a) == 2 and z3.is_int(a[0]):
        p = sorted([_z_int(a[0], vmap), _z_int(a[1], vmap)])
        return f"(negb (Z.eqb {p[0]} {p[1]}))"
    if k == z3.Z3_OP_LE:
        return f"(Z.leb {_z_int(a[0], vmap)} {_z_int(a[1], vmap)})"
    if k == z3.Z3_OP_LT:
        return f"(Z.ltb {_z_int(a[0], vmap)} {_z_int(a[1], vmap)})"
    if k == z3.Z3_OP_GE:
        return f"(Z.leb {_z_int(a[1], vmap)} {_z_int(a[0], vmap)})"
    if k == z3.Z3_OP_GT:
        return f"(Z.ltb {_z_int(a[1], vmap)} {_z_int(a[0], vmap)})"
    if k == z3.Z3_OP_NOT:
        return f"(negb {_z_bool(a[0], vmap)})"
    if k == z3.Z3_OP_AND:                                  # AC: flatten nested ands and sort the conjuncts
        return _foldb("andb", sorted(_z_bool(c, vmap) for c in _flatten_ac(t, k)))
    if k == z3.Z3_OP_OR:                                   # AC: flatten nested ors and sort the disjuncts
        return _foldb("orb", sorted(_z_bool(c, vmap) for c in _flatten_ac(t, k)))
    if k == z3.Z3_OP_IMPLIES:
        return f"(implb {_z_bool(a[0], vmap)} {_z_bool(a[1], vmap)})"
    if k == z3.Z3_OP_XOR:
        return f"(xorb {_z_bool(a[0], vmap)} {_z_bool(a[1], vmap)})"
    if k == z3.Z3_OP_ITE:
        return f"(if {_z_bool(a[0], vmap)} then {_z_bool(a[1], vmap)} else {_z_bool(a[2], vmap)})"
    raise _NoCoq(f"bool op {t.decl().name()}")


def obligation_to_coq(claim_false):
    """(sorted Coq var names, Coq boolean string) for a linear-integer refutation query, or None if
    it is trivial or outside the translatable fragment."""
    t = z3.simplify(claim_false)
    if z3.is_true(t) or z3.is_false(t) or not z3.is_bool(t):
        return None
    # assign v0, v1, ... by sorted variable name so the serialization does not depend on z3's traversal order
    vmap = {name: f"v{i}" for i, name in enumerate(sorted(_free_int_var_names(t)))}
    try:
        body = _z_bool(t, vmap)
    except _NoCoq:
        return None
    return sorted(vmap.values()), body


_SIGN = "def f(x):\n    if x > 0:\n        return 1\n    if x < 0:\n        return -1\n    return 0\n"
_COUNTER = "def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n"

# integer verifications whose discharged obligations are linear; each runs through _solve, which records
_OBLIGATION_CORPUS = [
    lambda: verify_equiv("o", "f", "def f(a):\n    return a + a\n", "def g(a):\n    return 2 * a\n", {}),
    lambda: verify_equiv("o", "f", "def f(a, b):\n    return a + b\n", "def g(a, b):\n    return b + a\n", {}),
    lambda: verify_equiv("o", "f", "def f(a):\n    return a + a + a\n", "def g(a):\n    return 3 * a\n", {}),
    lambda: verify_equiv("o", "f", _SIGN, _SIGN.replace("def f(", "def g("), {}),
    lambda: verify_predicate("o", "f", "def f(x):\n    return max(0, min(100, x))\n",
                             lambda za, o: z3.And(o >= 0, o <= 100), {}),
    lambda: verify_predicate("o", "f", "def f(x):\n    if x < 10:\n        return x\n    return 10\n",
                             lambda za, o: o <= 10, {}),
    lambda: verify_deductive("o", "f", _COUNTER, lambda S: S["n"] >= 0,
                             lambda S: z3.And(0 <= S["i"], S["i"] <= S["n"]), lambda S, r: r == S["n"], {}),
]


def collect_obligations():
    """Run the corpus with recording on; return the real refutation queries the engine discharged."""
    obs, saved = [], core.RECORD_OBLIGATIONS
    core.RECORD_OBLIGATIONS = obs
    try:
        for run in _OBLIGATION_CORPUS:
            try:
                run()
            except Exception:
                pass
    finally:
        core.RECORD_OBLIGATIONS = saved
    return obs


def generate_obligation_lemmas(limit=40):
    """Translate the collected linear-integer obligations to deduplicated SMTCoq goals."""
    seen, lemmas = set(), []
    for cf in collect_obligations():
        r = obligation_to_coq(cf)
        if r is None:
            continue
        vs, body = r
        if (tuple(vs), body) in seen:
            continue
        seen.add((tuple(vs), body))
        binder = f"forall ({' '.join(vs)} : Z), " if vs else ""
        lemmas.append(f"Goal {binder}{body} = false.\nProof. verit. Qed.")
        if len(lemmas) >= limit:
            break
    return lemmas


_HEADER = (
    "(* GENERATED from the engine's actual integer obligations by touchstone.smtcoq_export.\n"
    "   Each goal is a refutation query the engine discharged as PROVED; SMTCoq re-checks the veriT\n"
    "   certificate in Coq's kernel. Regenerate: python -m touchstone.smtcoq_export proofs/touchstone_obligations.v *)\n"
    "From SMTCoq Require Import SMTCoq.\n"
    "From Coq Require Import Bool ZArith.\n"
    "Local Open Scope Z_scope.\n")


def write_obligation_proofs(path):
    """Write the generated SMTCoq goals to `path`; return the number written."""
    lemmas = generate_obligation_lemmas()
    with open(path, "w", encoding="utf-8") as f:
        f.write(_HEADER + "\n" + "\n\n".join(lemmas) + "\n")
    return len(lemmas)


__all__ = ["obligation_to_coq", "collect_obligations", "generate_obligation_lemmas", "write_obligation_proofs"]


if __name__ == "__main__":
    import sys
    out = sys.argv[1] if len(sys.argv) > 1 else "proofs/touchstone_obligations.v"
    print(f"wrote {write_obligation_proofs(out)} obligation goals to {out}")
