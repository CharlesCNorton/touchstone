"""Rerunnable PROVED/REFUTED/UNKNOWN precision-and-recall harness over external code.

Each program's trap freedom (plus any asserts) is decided with the broadest applicable engine, then
each decided verdict is cross-checked against CPython by sampling typed inputs in the sandbox: a PROVED
that raises is a contradiction, a REFUTED that raises is confirmed. Recall is the decided fraction,
precision the decided verdicts CPython does not contradict, contradictions the soundness bar (zero).

    python -m touchstone.benchmark                 # bundled standard-algorithm corpus
    python -m touchstone.benchmark path/to/dir     # external .py files (e.g. a TypeEvalPy checkout)
"""
import ast
import builtins
import os
import random
import sys
import textwrap
import z3
from . import core
from .core import PROVED, REFUTED, UNKNOWN, Verdict, Ctx, symexec, _solve, _fndef
from .engines import (check, load_module, verify_sequence_loop, verify_recursive, verify_heap_property,
                      verify_array_loop, _is_array_param)


# Standard public algorithms: the default external corpus, spanning integer, list, recursion, and
# generator idioms plus code outside the modeled subset.
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


if __name__ == "__main__":
    sys.exit(main())
