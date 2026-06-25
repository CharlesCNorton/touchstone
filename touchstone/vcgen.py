"""The verified verification-condition generator, in the engine. proofs/touchstone_functor.v defines a
syntactic weakest-precondition wpg over an integer IR (assignment, conditional, arithmetic, comparison, and
boolean operators, floor division trap-aware), proves it sound and complete against the operational
semantics, and extracts it to OCaml. This module mirrors that generator in Python, lowers the loop-free
fragment of a function to the same IR, emits the goal through wpg, and discharges it with the solver.
extracted_vcgen_audit holds this Python wpg equal to the OCaml extraction on a random corpus.

The fragment: a function whose body is straight-line assignments and if/else (arbitrarily nested, no loops,
no early return) ending in a single `return <expr>`, over integer parameters; arithmetic is +, -, *, //, %,
comparisons, and and/or/not; a reachable division by zero is a trap the VC refuses to discharge. Parameters
are read at entry in the postcondition, matching prove(). Anything else raises Unsupported."""
import ast
import random
import subprocess
import textwrap
import z3
from . import core
from .core import (Unsupported, Verdict, PROVED, REFUTED, UNKNOWN, _fndef, py_floordiv, py_mod,
                   _solve, solve_corroborated, proof_certificate)


# --------------------------------------------------------------------------- #
# The generator, mirroring proofs/touchstone_functor.v exactly. The IR is tagged tuples:           #
#   expr ::= ('v',n) | ('c',z) | ('add'|'sub'|'mul'|'div'|'mod'|'elt'|'ele'|'eeq'|'eand'|'eor',a,b)#
#          | ('enot', a)                                                                            #
#   prog ::= ('nil',) | ('asgn', n, e, prog) | ('cond', e, prog, prog, prog)                        #
#   kcmd ::= ('kskip',)|('kasgn',n,e)|('kseq',a,b)|('kif',c,t,e)|('kwhile',inv,c,body)  (vcg)       #
#   form ::= ('true',)|('false',) | ('lt'|'le'|'eq', a, b) | ('not', f) | ('and'|'or'|'impl', f, g) #
# --------------------------------------------------------------------------- #
_EBIN = {"add", "sub", "mul", "div", "mod", "elt", "ele", "eeq", "eand", "eor"}


# wpg and vcg are the generator extracted from proofs/touchstone_functor.v, regenerated into
# touchstone/_generated/vcgen_rocq.py by proofs/json_to_python.py. The only engine-side code is the bijection
# between this module's IR (Python-int indices and constants, lowercase tags) and the extracted IR (Peano-nat
# indices, binary-Z constants, inductive tags). extracted_vcgen_audit holds _rocq equal to the OCaml extraction.
from ._generated import vcgen_rocq as _rocq

_E2X = {"add": "EAdd", "sub": "ESub", "mul": "EMul", "div": "EDiv", "mod": "EMod",
        "elt": "ELt", "ele": "ELe", "eeq": "EEq", "eand": "EAnd", "eor": "EOr"}
_X2E = {v: k for k, v in _E2X.items()}
_F2X = {"lt": "FLt", "le": "FLe", "eq": "FEq", "and": "FAnd", "or": "FOr", "impl": "FImpl"}
_X2F = {v: k for k, v in _F2X.items()}


def _nat(n):
    out = ("O",)
    for _ in range(n):
        out = ("S", out)
    return out


def _intnat(x):
    n = 0
    while x[0] == "S":
        n, x = n + 1, x[1]
    return n


def _pos(n):
    return ("XH",) if n == 1 else (("XI", _pos(n >> 1)) if n & 1 else ("XO", _pos(n >> 1)))


def _Z(n):
    return ("Z0",) if n == 0 else (("Zpos", _pos(n)) if n > 0 else ("Zneg", _pos(-n)))


def _intpos(p):
    return 1 if p[0] == "XH" else 2 * _intpos(p[1]) + (1 if p[0] == "XI" else 0)


def _intZ(x):
    return 0 if x[0] == "Z0" else (_intpos(x[1]) if x[0] == "Zpos" else -_intpos(x[1]))


def _e2x(e):                                                         # engine expr -> extracted expr
    t = e[0]
    if t == "v":
        return ("EVar", _nat(e[1]))
    if t == "c":
        return ("EConst", _Z(e[1]))
    if t == "enot":
        return ("ENot", _e2x(e[1]))
    return (_E2X[t], _e2x(e[1]), _e2x(e[2]))


def _f2x(f):                                                         # engine form -> extracted form
    t = f[0]
    if t == "true":
        return ("FTrue",)
    if t == "false":
        return ("FFalse",)
    if t == "not":
        return ("FNot", _f2x(f[1]))
    if t in ("lt", "le", "eq"):
        return (_F2X[t], _e2x(f[1]), _e2x(f[2]))
    return (_F2X[t], _f2x(f[1]), _f2x(f[2]))


def _p2x(p):                                                         # engine prog -> extracted prog
    t = p[0]
    if t == "nil":
        return ("PNil",)
    if t == "asgn":
        return ("PAsgn", _nat(p[1]), _e2x(p[2]), _p2x(p[3]))
    return ("PCond", _e2x(p[1]), _p2x(p[2]), _p2x(p[3]), _p2x(p[4]))


def _k2x(k):                                                         # engine kcmd -> extracted kcmd
    t = k[0]
    if t == "kskip":
        return ("KSkip",)
    if t == "kasgn":
        return ("KAsgn", _nat(k[1]), _e2x(k[2]))
    if t == "kseq":
        return ("KSeq", _k2x(k[1]), _k2x(k[2]))
    if t == "kif":
        return ("KIf", _e2x(k[1]), _k2x(k[2]), _k2x(k[3]))
    return ("KWhile", _f2x(k[1]), _e2x(k[2]), _k2x(k[3]))


def _x2e(e):                                                         # extracted expr -> engine expr
    t = e[0]
    if t == "EVar":
        return ("v", _intnat(e[1]))
    if t == "EConst":
        return ("c", _intZ(e[1]))
    if t == "ENot":
        return ("enot", _x2e(e[1]))
    return (_X2E[t], _x2e(e[1]), _x2e(e[2]))


def _x2f(f):                                                         # extracted form -> engine form
    t = f[0]
    if t == "FTrue":
        return ("true",)
    if t == "FFalse":
        return ("false",)
    if t == "FNot":
        return ("not", _x2f(f[1]))
    if t in ("FLt", "FLe", "FEq"):
        return (_X2F[t], _x2e(f[1]), _x2e(f[2]))
    return (_X2F[t], _x2f(f[1]), _x2f(f[2]))


def subst_expr(x, e, t):
    """Substitute expression e for variable x in expression t, via the extracted substitution."""
    return _x2e(_rocq.subst_expr(_nat(x))(_e2x(e))(_e2x(t)))


def subst_form(x, e, f):
    """Substitute expression e for variable x in formula f, via the extracted substitution."""
    return _x2f(_rocq.subst_form(_nat(x))(_e2x(e))(_f2x(f)))


def defined_expr(t):
    """The definedness condition of expression t (a divisor-nonzero conjunction), via the extraction."""
    return _x2f(_rocq.defined_expr(_e2x(t)))


def wpg(p, q):
    """The weakest-precondition VC for a loop-free program, via the extracted generator."""
    return _x2f(_rocq.wpg(_p2x(p))(_f2x(q)))


def vcg(k, q):
    """The (precondition, side-obligation list) for a command, via the extracted loop generator. The
    extracted obligation list is the OCaml-list encoding ('[]' / '(::)') from touchstone_functor.v."""
    r = _rocq.vcg(_k2x(k))(_f2x(q))                                  # ('(,)', precondition, obligations)
    obs, o = [], r[2]
    while o[0] == "(::)":
        obs.append(_x2f(o[1]))
        o = o[2]
    return (_x2f(r[1]), obs)


# ---- canonical S-expression serialization (byte-identical to proofs/vcgen_main.ml) ----
def ser_expr(e):
    if e[0] == "v":
        return f"(v {e[1]})"
    if e[0] == "c":
        return f"(c {e[1]})"
    if e[0] == "enot":
        return f"(enot {ser_expr(e[1])})"
    return f"({e[0]} {ser_expr(e[1])} {ser_expr(e[2])})"


def ser_prog(p):
    if p[0] == "nil":
        return "nil"
    if p[0] == "asgn":
        return f"(asgn {p[1]} {ser_expr(p[2])} {ser_prog(p[3])})"
    return f"(cond {ser_expr(p[1])} {ser_prog(p[2])} {ser_prog(p[3])} {ser_prog(p[4])})"


def ser_form(f):
    if f[0] in ("true", "false"):
        return f[0]
    if f[0] in ("lt", "le", "eq"):
        return f"({f[0]} {ser_expr(f[1])} {ser_expr(f[2])})"
    if f[0] == "not":
        return f"(not {ser_form(f[1])})"
    return f"({f[0]} {ser_form(f[1])} {ser_form(f[2])})"


def ser_kcmd(k):
    if k[0] == "kskip":
        return "kskip"
    if k[0] == "kasgn":
        return f"(kasgn {k[1]} {ser_expr(k[2])})"
    if k[0] == "kseq":
        return f"(kseq {ser_kcmd(k[1])} {ser_kcmd(k[2])})"
    if k[0] == "kif":
        return f"(kif {ser_expr(k[1])} {ser_kcmd(k[2])} {ser_kcmd(k[3])})"
    return f"(kwhile {ser_form(k[1])} {ser_expr(k[2])} {ser_kcmd(k[3])})"   # kwhile inv c body


def ser_vcg(result):
    """Serialize vcg's (precondition, obligations) as `(vc <pre> <ob>...)`, byte-identical to the extracted
    driver, for the differential audit."""
    pre, obs = result
    return "(vc " + ser_form(pre) + "".join(" " + ser_form(o) for o in obs) + ")"


# --------------------------------------------------------------------------- #
# Lowering a Python function to the IR, and the IR formula to Z3.                                   #
# --------------------------------------------------------------------------- #
_CMP_FORM = {ast.Lt: ("lt", False), ast.LtE: ("le", False), ast.Gt: ("lt", True),
             ast.GtE: ("le", True), ast.Eq: ("eq", False), ast.NotEq: ("eq", "neg")}
_CMP_EXPR = {ast.Lt: ("elt", False), ast.LtE: ("ele", False), ast.Gt: ("elt", True),
             ast.GtE: ("ele", True), ast.Eq: ("eeq", False), ast.NotEq: ("eeq", "neg")}


def _lower_expr(node, resolve):
    """A Python expression to an IR expr; `resolve(name)` gives the IR expr a name denotes."""
    if isinstance(node, ast.Constant) and isinstance(node.value, bool):
        return ("c", 1 if node.value else 0)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return ("c", node.value)
    if isinstance(node, ast.Name):
        return resolve(node.id)
    if isinstance(node, ast.BinOp):
        op = type(node.op)
        a, b = _lower_expr(node.left, resolve), _lower_expr(node.right, resolve)
        if op is ast.Add: return ("add", a, b)
        if op is ast.Sub: return ("sub", a, b)
        if op is ast.Mult: return ("mul", a, b)
        if op is ast.FloorDiv: return ("div", a, b)
        if op is ast.Mod: return ("mod", a, b)                          # the verified EMod (floored modulo)
        raise Unsupported(f"vcgen: operator {op.__name__}")
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return ("sub", ("c", 0), _lower_expr(node.operand, resolve))
    if isinstance(node, ast.Compare) or (isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not)):
        return _lower_cond(node, resolve)               # a comparison / `not` in value position IS its 0/1 truth value
    if isinstance(node, ast.BoolOp):
        # Python `and` / `or` in value position return an operand and short-circuit, so a later operand's
        # traps are conditional; the IR's eand / eor are the 0/1-valued connective, sound only in a test.
        # Decline, so prove() falls back to the symbolic engine, which models the operand and short-circuit.
        raise Unsupported("vcgen: and/or returning an operand is outside the verified IR fragment")
    raise Unsupported(f"vcgen: expression {type(node).__name__}")


def _lower_cond(node, resolve):
    """A Python test to an IR expr that is nonzero exactly when the test is truthy."""
    if isinstance(node, ast.Compare):
        if len(node.ops) != 1:
            raise Unsupported("vcgen: chained comparison")
        a, b = _lower_expr(node.left, resolve), _lower_expr(node.comparators[0], resolve)
        tag, flip = _CMP_EXPR[type(node.ops[0])]
        core_e = (tag, b, a) if flip is True else (tag, a, b)
        return ("enot", core_e) if flip == "neg" else core_e
    if isinstance(node, ast.BoolOp):
        op = "eand" if isinstance(node.op, ast.And) else "eor"
        parts = [_lower_cond(v, resolve) for v in node.values]
        acc = parts[0]
        for p in parts[1:]:
            acc = (op, acc, p)
        return acc
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return ("enot", _lower_cond(node.operand, resolve))
    return _lower_expr(node, resolve)                                   # bare truthiness: nonzero


def _lower_form(node, resolve):
    """A Python boolean expression (a pre/postcondition) to an IR form."""
    if isinstance(node, ast.Constant) and isinstance(node.value, bool):
        return ("true",) if node.value else ("false",)
    if isinstance(node, ast.Compare):
        if len(node.ops) != 1:
            raise Unsupported("vcgen: chained comparison in spec")
        a, b = _lower_expr(node.left, resolve), _lower_expr(node.comparators[0], resolve)
        tag, flip = _CMP_FORM[type(node.ops[0])]
        atom = (tag, b, a) if flip is True else (tag, a, b)
        return ("not", atom) if flip == "neg" else atom
    if isinstance(node, ast.BoolOp):
        op = "and" if isinstance(node.op, ast.And) else "or"
        parts = [_lower_form(v, resolve) for v in node.values]
        acc = parts[0]
        for p in parts[1:]:
            acc = (op, acc, p)
        return acc
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return ("not", _lower_form(node.operand, resolve))
    raise Unsupported(f"vcgen: specification form {type(node).__name__}")


def _lower_prog(stmts, windex):
    """A statement list (assignments and if/else, no loops or early return) to an IR prog."""
    if not stmts:
        return ("nil",)
    s, rest = stmts[0], stmts[1:]
    R = lambda nm: ("v", windex(nm))
    if isinstance(s, ast.Assign):
        if len(s.targets) != 1 or not isinstance(s.targets[0], ast.Name):
            raise Unsupported("vcgen: assignment target")
        e = _lower_expr(s.value, R)                                    # read the right side first
        return ("asgn", windex(s.targets[0].id), e, _lower_prog(rest, windex))
    if isinstance(s, ast.If):
        c = _lower_cond(s.test, R)
        thn = _lower_prog(s.body, windex)
        els = _lower_prog(s.orelse, windex)
        return ("cond", c, thn, els, _lower_prog(rest, windex))
    if isinstance(s, (ast.Pass, ast.Import, ast.ImportFrom)):
        return _lower_prog(rest, windex)
    if isinstance(s, ast.Return):
        raise Unsupported("vcgen: early return is outside the loop-free IR fragment")
    raise Unsupported(f"vcgen: statement {type(s).__name__}")


def lower_function(src):
    """Lower a function to (params, ghost, prog, ret_expr, nvars). Ghost indices 0..k-1 hold the
    entry values of the k parameters (read by the postcondition); working indices k.. hold the live
    values (each parameter's working copy is initialised from its ghost). prog is the working copies
    followed by the body; ret_expr is the returned expression over the working state."""
    fn = _fndef(src)
    if isinstance(fn, ast.AsyncFunctionDef):                            # an async function returns a coroutine, not
        raise Unsupported("vcgen: an async function is not the synchronous body it lowers to")   # its body value
    params = [a.arg for a in fn.args.args]
    for a in fn.args.args:                                              # the IR is integer-only; a float /
        ann = a.annotation                                             # string / list parameter must not be
        if ann is not None and not (isinstance(ann, ast.Name) and ann.id == "int"):   # reasoned about as an integer
            raise Unsupported(f"vcgen: non-integer parameter {a.arg}")
    if fn.args.kwonlyargs or fn.args.vararg or fn.args.kwarg:
        raise Unsupported("vcgen: only positional integer parameters")
    if any(isinstance(n, (ast.While, ast.For)) for n in ast.walk(fn)):
        raise Unsupported("vcgen: a loop is outside the loop-free fragment (use the CHC engine)")
    body = list(fn.body)
    if not body or not isinstance(body[-1], ast.Return) or body[-1].value is None:
        raise Unsupported("vcgen: the body must end in `return <expr>`")
    ghost = {p: i for i, p in enumerate(params)}
    work, ctr = {}, [len(params)]

    def windex(name):
        if name not in work:
            work[name] = ctr[0]; ctr[0] += 1
        return work[name]

    for p in params:
        windex(p)                                                      # a working copy index per parameter
    # lower `return e` as a trailing assignment `__vcg_result__ := e`, so wpg emits e's definedness
    # obligation (a div / mod in the returned expression is a real trap) and the postcondition reads it.
    res = ast.copy_location(
        ast.Assign(targets=[ast.Name(id="__vcg_result__", ctx=ast.Store())], value=body[-1].value), body[-1])
    body_prog = _lower_prog(body[:-1] + [res], windex)
    ret_expr = ("v", work["__vcg_result__"])
    prog = body_prog
    for p in reversed(params):                                         # working_p := ghost_p, before the body
        prog = ("asgn", work[p], ("v", ghost[p]), prog)
    return params, ghost, prog, ret_expr, ctr[0]


def expr_to_z3(e, Z):
    t = e[0]
    if t == "v":
        return Z[e[1]]
    if t == "c":
        return z3.IntVal(e[1])
    if t == "enot":
        return z3.If(expr_to_z3(e[1], Z) == 0, z3.IntVal(1), z3.IntVal(0))
    a, b = expr_to_z3(e[1], Z), expr_to_z3(e[2], Z)
    if t == "add": return a + b
    if t == "sub": return a - b
    if t == "mul": return a * b
    if t == "div": return py_floordiv(a, b)                            # the exact floor-division encoding
    if t == "mod": return py_mod(a, b)                                 # the exact floored-modulo encoding
    one, zero = z3.IntVal(1), z3.IntVal(0)
    if t == "elt": return z3.If(a < b, one, zero)
    if t == "ele": return z3.If(a <= b, one, zero)
    if t == "eeq": return z3.If(a == b, one, zero)
    if t == "eand": return z3.If(z3.And(a != 0, b != 0), one, zero)
    if t == "eor": return z3.If(z3.Or(a != 0, b != 0), one, zero)
    raise Unsupported(f"vcgen: z3 expr {t}")


def form_to_z3(f, Z):
    t = f[0]
    if t == "true": return z3.BoolVal(True)
    if t == "false": return z3.BoolVal(False)
    if t == "lt": return expr_to_z3(f[1], Z) < expr_to_z3(f[2], Z)
    if t == "le": return expr_to_z3(f[1], Z) <= expr_to_z3(f[2], Z)
    if t == "eq": return expr_to_z3(f[1], Z) == expr_to_z3(f[2], Z)
    if t == "not": return z3.Not(form_to_z3(f[1], Z))
    if t == "and": return z3.And(form_to_z3(f[1], Z), form_to_z3(f[2], Z))
    if t == "or": return z3.Or(form_to_z3(f[1], Z), form_to_z3(f[2], Z))
    return z3.Implies(form_to_z3(f[1], Z), form_to_z3(f[2], Z))         # impl


def _audit_against_cpython(src, ensures, requires, params, status, cex_inputs):
    """Cross-check a vcgen verdict against CPython, covering the IR lowering (_lower_*), which is outside the
    Rocq proof. When subject execution is permitted, a PROVED whose postcondition CPython violates -- or a
    REFUTED whose own counterexample CPython satisfies -- raises SoundnessError. No-op unless
    ALLOW_SUBJECT_EXECUTION. For a PROVED with few enough parameters the postcondition is checked exhaustively
    over the box [-12, 12] per parameter (plus a few large magnitudes); otherwise it falls back to random
    sampling. A trapping or unevaluable sample is skipped."""
    if not core.ALLOW_SUBJECT_EXECUTION or status not in (PROVED, REFUTED):
        return
    try:
        fn = core._pyfn(src, {})
        pre_c = compile(textwrap.dedent(requires), "<requires>", "eval")
        post_c = compile(textwrap.dedent(ensures), "<ensures>", "eval")
    except Exception:
        return
    g = {"__builtins__": {"abs": abs, "min": min, "max": max, "len": len, "int": int, "bool": bool}}

    def evaluate(sample):
        """(postcondition_holds, result) on a sample meeting the precondition, or None."""
        if not eval(pre_c, g, dict(sample)):
            return None
        r = fn(*[sample[p] for p in params])
        return bool(eval(post_c, g, {**sample, "result": r})), r

    if status == REFUTED and cex_inputs:                          # the engine's counterexample must violate
        try:
            res = evaluate(cex_inputs)
        except Exception:
            res = None
        if res is not None and res[0]:
            raise core.SoundnessError(
                "vcgen REFUTED but its counterexample %s satisfies the postcondition (result=%r)"
                % (cex_inputs, res[1]))
    if status == PROVED:                                          # the postcondition must hold on every sample
        import itertools
        bound = 12
        if params and (2 * bound + 1) ** len(params) <= 200000:
            samples = [dict(zip(params, combo))                       # EXHAUSTIVE over [-bound, bound]^k: the
                       for combo in itertools.product(range(-bound, bound + 1), repeat=len(params))]
            samples += [{p: v for p in params} for v in (10 ** 6, -(10 ** 6), 10 ** 9, -(10 ** 9))]  # + large
        else:                                                         # too many parameters to enumerate: sample
            rng = random.Random(0)
            pool = [0, 1, -1, 2, -2, 3, 7, -7, 13, -13, 100, -100, 1000, -1000]
            samples = [{p: 0 for p in params}] + [{p: rng.choice(pool) for p in params} for _ in range(256)]
        for s in samples:
            try:
                res = evaluate(s)
            except Exception:
                continue                                          # a trapping / unrunnable sample carries no verdict
            if res is not None and not res[0]:
                raise core.SoundnessError(
                    "vcgen PROVED but CPython violates the postcondition at %s (result=%r)" % (s, res[1]))


def prove_via_vcgen(src, ensures, requires="True", repo=None, prop="property", target=None) -> Verdict:
    """Verify {requires} f {ensures} by emitting the goal through the Rocq-verified generator wpg.
    The function is lowered to the IR, the postcondition (over the parameters and `result`) and
    precondition to IR formulas, the verification condition is wpg(prog, post), and the engine refutes
    `pre AND NOT wpg`. PROVED (corroborated) means the verified generator's condition is valid; a
    reachable division by zero leaves it undischarged. UNKNOWN if the function is outside the fragment."""
    try:
        target = target or _fndef(src).name
    except Unsupported:
        return Verdict(UNKNOWN, prop, target or "f", "verified VC generator", reason="no function definition")
    try:
        from .engines import _use_before_def                           # imported lazily: a top-level `from .engines`
        if _use_before_def(src):                                       # would cycle (engines -> ... -> vcgen) when a
            return Verdict(UNKNOWN, prop, target, "verified VC generator",   # worker imports the engines submodule
                           reason="possible use before assignment")    # directly to unpickle a parallel-triage task
    except Unsupported:
        pass
    try:
        params, ghost, prog, ret_expr, nvars = lower_function(src)
        post_node = ast.parse(textwrap.dedent(ensures), mode="eval").body
        pre_node = ast.parse(textwrap.dedent(requires), mode="eval").body

        def post_resolve(nm):
            if nm == "result":
                return ret_expr
            if nm in ghost:
                return ("v", ghost[nm])
            raise Unsupported(f"vcgen: spec references unknown name {nm}")

        def pre_resolve(nm):
            if nm in ghost:
                return ("v", ghost[nm])
            raise Unsupported(f"vcgen: precondition references unknown name {nm}")

        post_form = _lower_form(post_node, post_resolve)
        pre_form = _lower_form(pre_node, pre_resolve)
        vc = wpg(prog, post_form)
    except (Unsupported, SyntaxError, KeyError) as u:
        return Verdict(UNKNOWN, prop, target, "verified VC generator", reason=f"outside the fragment: {u}")
    Z = {i: z3.Int(f"_g{i}") for i in range(nvars)}
    try:
        claim_false = z3.And(form_to_z3(pre_form, Z), z3.Not(form_to_z3(vc, Z)))
    except (z3.Z3Exception, Unsupported) as u:
        return Verdict(UNKNOWN, prop, target, "verified VC generator", reason=str(u))
    if core.REQUIRE_CORROBORATION:
        status, model, corr = solve_corroborated(claim_false)
    else:
        (status, model), corr = _solve(claim_false), "z3 only"
    cex = cex_in = None
    if status == REFUTED:
        gz = {p: Z[ghost[p]] for p in params}
        # prefer a non-trapping counterexample: definedness holds (wpg(prog, true)) and the postcondition
        # fails (wpg(prog, not post)), so x % y < 0 is shown at y < 0 rather than the y = 0 trap. Fall back
        # to the original witness when the only violation is a trap (x = 0 for 10 // x).
        try:
            clean = z3.And(form_to_z3(pre_form, Z), form_to_z3(wpg(prog, ("true",)), Z),
                           form_to_z3(wpg(prog, ("not", post_form)), Z))
            cst, cm = _solve(clean)
        except (z3.Z3Exception, Unsupported):
            cst, cm = None, None
        if cst == REFUTED:
            model = core.minimize_witness(clean, gz, params) or cm or model
        else:
            model = core.minimize_witness(claim_false, gz, params) or model
        cex_in = {p: model.eval(Z[ghost[p]], model_completion=True).as_long() for p in params}
        cex = ", ".join(f"{p}={cex_in[p]}" for p in params)
    _audit_against_cpython(src, ensures, requires, params, status, cex_in)   # CPython cross-check (raises on a contradiction)
    cert = proof_certificate(corr) if status == PROVED else None
    return Verdict(status, prop, target, "verified VC generator (Rocq-extracted wpg)",
                   counterexample=cex, counterexample_inputs=cex_in, certificate=cert,
                   reason="" if status != UNKNOWN else (corr if corr == core._NL_UNCORROBORATED else "solver returned unknown"))


# --------------------------------------------------------------------------- #
# Bridge to the extracted OCaml generator, for the differential audit.                             #
# --------------------------------------------------------------------------- #
def vcgen_executable():
    """Path to the Coq-extracted generator built by proofs/build_vcgen.sh, or None if not built."""
    return core.find_extracted("vcgen")


def extracted_wpg(prog, post, exe=None):
    """Run the Rocq-extracted generator on (prog, post) and return its verification condition as a
    canonical S-expression string, or None if the extracted binary is unavailable."""
    exe = exe or vcgen_executable()
    if exe is None:
        return None
    out = subprocess.run([exe], input=f"(query {ser_prog(prog)} {ser_form(post)})\n",
                         capture_output=True, text=True, timeout=30)
    return out.stdout.strip()


def extracted_wpg_batch(items, exe=None):
    """Run the Rocq-extracted generator on a list of (prog, post) pairs in one invocation; return the list of
    canonical-S-expression verification conditions (aligned with items), or None if the binary is unavailable."""
    exe = exe or vcgen_executable()
    if exe is None:
        return None
    inp = "".join(f"(query {ser_prog(p)} {ser_form(q)})\n" for p, q in items)
    out = subprocess.run([exe], input=inp, capture_output=True, text=True, timeout=300)
    return out.stdout.strip("\n").split("\n")


def extracted_vcg_batch(items, exe=None):
    """Run the Rocq-extracted loop generator vcg on a list of (kcmd, post) pairs in one invocation; return the
    list of canonical-S-expression results `(vc <pre> <ob>...)` (aligned with items), or None if unavailable."""
    exe = exe or vcgen_executable()
    if exe is None:
        return None
    inp = "".join(f"(querycmd {ser_kcmd(k)} {ser_form(q)})\n" for k, q in items)
    out = subprocess.run([exe], input=inp, capture_output=True, text=True, timeout=300)
    return out.stdout.strip("\n").split("\n")


__all__ = [
    "subst_expr", "subst_form", "defined_expr", "wpg", "vcg",
    "ser_expr", "ser_prog", "ser_form", "ser_kcmd", "ser_vcg",
    "lower_function", "expr_to_z3", "form_to_z3", "prove_via_vcgen",
    "vcgen_executable", "extracted_wpg", "extracted_wpg_batch", "extracted_vcg_batch",
]
