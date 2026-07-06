"""Runnable examples, one per capability, each a function paired with a property it discharges. Contract
properties use the @require / @ensure decorators; the rest use the matching entry point. Run them all,
asserting each verdict:

    python -m touchstone.examples
"""
import sys
import z3
from . import _impl as t


def _array_zero():
    src = "def f(a: list, n: int):\n    i = 0\n    while i < n:\n        a[i] = 0\n        i = i + 1\n    return a\n"
    pre = lambda S: z3.And(S["n"] >= 0, S["n"] <= S["len_a"])
    post = lambda S, E: t.q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < S["n"]), z3.Select(S["a"], j) == 0))
    return t.verify_array_loop_auto("array", "f", src, pre, post)


# (title, thunk -> Verdict, expected status)
EXAMPLES = [
    ("counted loop returns n (loop invariant inferred)",
     lambda: t.verify_contracts('@require("n >= 0")\n@ensure("result == n")\n'
                                'def count(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n'),
     "PROVED"),
    ("Gauss sum: 2 * result == n * (n - 1)",
     lambda: t.verify_contracts('@require("n >= 0")\n@ensure("2 * result == n * (n - 1)")\n'
                                'def gauss(n):\n    s = 0\n    i = 0\n    while i < n:\n'
                                '        s = s + i\n        i = i + 1\n    return s\n'),
     "PROVED"),
    ("recursion: f(n) == n for every n >= 0",
     lambda: t.verify_contracts('@require("n >= 0")\n@ensure("result == n")\n'
                                'def f(n):\n    if n <= 0:\n        return 0\n    return f(n - 1) + 1\n'),
     "PROVED"),
    ("guarded division stays in range and never traps",
     lambda: t.verify_contracts('@require("x >= 1")\n@ensure("result <= 10")\ndef d(x):\n    return 10 // x\n'),
     "PROVED"),
    ("an off-by-one postcondition is refuted with a counterexample",
     lambda: t.verify_contracts('@ensure("result == x")\ndef f(x):\n    return x + 1\n'),
     "REFUTED"),
    ("square root is nonnegative on its domain",
     lambda: t.prove("import math\ndef f(x):\n    return math.sqrt(x)\n", "result >= 0.0", requires="x >= 0.0"),
     "PROVED"),
    ("two implementations agree on every input",
     lambda: t.verify_equiv("equiv", "f", "def f(a):\n    return a + a\n", "def g(a):\n    return 2 * a\n", {}),
     "PROVED"),
    ("the counted loop terminates",
     lambda: t.verify_termination("term", "f",
                                  "def f(n):\n    i = 0\n    while i < n:\n        i = i + 1\n    return i\n"),
     "PROVED"),
    ("array set-to-zero: every element is zero at exit",
     _array_zero, "PROVED"),
    ("IEEE-754: x + x equals 2.0 * x for every double",
     lambda: t.verify_equiv("fp", "f", "def f(x: float):\n    return x + x\n",
                            "def g(x: float):\n    return 2.0 * x\n", {}),
     "PROVED"),
    ("heap aliasing: a write through an alias is visible through the original",
     lambda: t.verify_heap_property("heap", "f",
                                    "def f(p, q):\n    a = object()\n    b = a\n    a.x = p\n    b.x = q\n    return a.x\n",
                                    lambda za, r: r == za["q"]),
     "PROVED"),
    ("a list grown by append in a loop has the expected length",
     lambda: t.prove("def f(n):\n    a = []\n    i = 0\n    while i < n:\n        a.append(i)\n        i = i + 1\n    return len(a)\n",
                     "result == n", requires="n >= 0"),
     "PROVED"),
    ("an unprotected counter loses an update on some interleaving",
     lambda: t.verify_threads("race", "t",
                              ["def th():\n    tmp = x\n    tmp = tmp + 1\n    x = tmp\n"] * 2,
                              {"x": 0}, lambda s: s["x"] == 2),
     "REFUTED"),
    ("a lock-protected counter reaches N for every thread count",
     lambda: t.verify_atomic_threads("locked", "t", "def th():\n    with lock:\n        x = x + 1\n",
                                     {"x": 0}, lambda k, s: s["x"] == k),
     "PROVED"),
    ("a branching thread body is analyzed over every interleaving",
     lambda: t.verify_threads("branch", "t",
                              ["def th():\n    if x < 100:\n        x = x + 1\n    else:\n        x = x + 1\n"] * 2,
                              {"x": 0}, lambda s: 1 <= s["x"] <= 2),
     "PROVED"),
    ("the size of a set built in a loop is bounded by the iteration count",
     lambda: t.verify_growing_set_auto(
         "set", "f", "def f(xs):\n    s = set()\n    for x in xs:\n        s.add(x)\n    return len(s)\n",
         lambda P, c: c <= P["len_xs"]),
     "PROVED"),
    ("summing a list of nonnegative elements yields a nonnegative result",
     lambda: t.verify_sequence_loop(
         "sum", "f", "def f(xs: list):\n    s = 0\n    for x in xs:\n        s = s + x\n    return s\n",
         lambda P, r: r >= 0, forall_pre=lambda x: x >= 0),
     "PROVED"),
    ("every value a range generator yields under a guard satisfies the guard",
     lambda: t.verify_generator_loop(
         "gen", "f", "def f(n):\n    for i in range(n):\n        if i > 0:\n            yield i\n",
         lambda P, v: v >= 1),
     "PROVED"),
    ("the goal is discharged through the Rocq-extracted VC generator",
     lambda: t.prove_via_vcgen("def f(x):\n    if x < 0:\n        x = 0 - x\n    return x\n", "result >= 0"),
     "PROVED"),
    ("sin stays within [-1, 1] over every finite double",
     lambda: t.prove("import math\ndef f(x: float):\n    return math.sin(x)\n",
                     "result <= 1.0 and result >= -1.0", requires="math.isfinite(x)"),
     "PROVED"),
    ("strip never lengthens a string",
     lambda: t.prove("def f(s: str):\n    return s.strip()\n", "len(result) <= len(s)"),
     "PROVED"),
    ("a list built by append holds its index at every position",
     lambda: t.verify_growing_list_auto(
         "build", "f",
         "def f(n):\n    a = []\n    i = 0\n    while i < n:\n        a.append(i)\n        i = i + 1\n    return a\n",
         lambda P, A, ln: t.q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(A, j) == j)),
         pre=lambda S: S["n"] >= 0),
     "PROVED"),
    ("the sum of a list whose every element is nonnegative is nonnegative",
     lambda: t.verify_recursive_list(
         "sum", "sl",
         "def sl(xs: list, i):\n    if i >= len(xs):\n        return 0\n    return xs[i] + sl(xs, i + 1)\n",
         lambda P: z3.And(P["i"] >= 0, P["i"] <= P["len_xs"]), lambda P, r: r >= 0,
         forall_pre=lambda x: x >= 0),
     "PROVED"),
    ("every element of [x * 2 for x in xs] is even",
     lambda: t.verify_map_comprehension(
         "even", "f", "def f(xs):\n    return [x * 2 for x in xs]\n",
         lambda P, R, ln: t.q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(R, j) % 2 == 0))),
     "PROVED"),
    ("every element of [x for x in xs if x > 0] is positive",
     lambda: t.verify_map_comprehension(
         "pos", "f", "def f(xs):\n    return [x for x in xs if x > 0]\n",
         lambda P, R, ln: t.q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < ln), z3.Select(R, j) > 0))),
     "PROVED"),
    ("all(x >= 0 for x in xs) over a nonempty list forces xs[0] >= 0",
     lambda: t.verify_all_any(
         "all", "f", "def f(xs):\n    return all(x >= 0 for x in xs)\n",
         lambda P, r: z3.Implies(z3.And(r, P["len_xs"] > 0), z3.Select(P["xs"], 0) >= 0)),
     "PROVED"),
    ("separation logic over the pointer code a function runs: a cell swap",
     lambda: t.verify_sl_code(
         "swap", "swap", "def swap(p, q):\n    a = p.val\n    b = q.val\n    p.val = b\n    q.val = a\n",
         ["p", "q"], {"p": "init_q", "q": "init_p"}),
     "PROVED"),
    ("separation logic: a function builds a null-terminated list segment",
     lambda: t.verify_sl_code(
         "lseg", "build", "def build():\n    n2 = object()\n    n2.next = 0\n    n1 = object()\n"
         "    n1.next = n2\n    return n1\n", (), {"n1": "n2", "n2": "0"}),
     "PROVED"),
]


def run(verbose=True):
    """Run every example, asserting its verdict. Returns the number that did not match (0 = all good)."""
    bad = 0
    for title, thunk, expected in EXAMPLES:
        v = thunk()
        ok = v.status == expected
        bad += (not ok)
        if verbose:
            print(f"  [{'ok' if ok else 'XX'}] {v.status:8} {title}")
    return bad


if __name__ == "__main__":
    print("EXAMPLES")
    n = run()
    if n:
        print(f"{n} example(s) did not match the expected verdict"); sys.exit(1)
    print(f"all {len(EXAMPLES)} examples discharged as expected")
