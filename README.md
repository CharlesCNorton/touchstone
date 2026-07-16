# Touchstone

An SMT-based verifier for a subset of Python. Touchstone takes a function and a property and returns
**PROVED** (it holds for all inputs), **REFUTED** (with a counterexample), or **UNKNOWN** (with a reason),
by translating the code to Z3 rather than running it. Every PROVED is corroborated by a second solver (cvc5)
and rests on a trust base machine-checked in Rocq.

```sh
pip install touchstone-prover
```

```python
import touchstone as t

# state the property in Python, over the parameters and `result`
t.prove("def f(x):\n    return x + x\n", "result == 2 * x").status        # 'PROVED'

# or write the contract as decorators on the function itself
t.verify_contracts('''
@require("n >= 0")
@ensure("result == n")
def count(n):
    i = 0
    while i < n:
        i = i + 1
    return i
''').status                                                              # 'PROVED'

# or check two implementations agree on every input
t.verify_equiv("double", "f", "def f(a):\n    return a + a\n",
               "def g(a):\n    return 2 * a\n", {}).status                # 'PROVED'
```

## Benchmarks

On the hand-written [TypeEvalPy](https://github.com/secure-software-engineering/TypeEvalPy) micro-benchmark,
ranked by exact match (a matched type set at the exact source position, the metric the benchmark ranks by):

| Tool | Kind | Exact matches |
| --- | --- | --- |
| **Touchstone** | **static** | **841 / 868** |
| Sonnet 4.6 | LLM | 824 / 868 |
| Opus 4.8 | LLM | 822 / 868 |
| gpt-4o | LLM | 806 / 860 |
| HeaderGen | static | 564 / 845 |
| Jedi | static | 415 / 845 |
| Pyright | static | 405 / 845 |
| HiTyper-DL | hybrid (ML) | 369 / 845 |
| Haiku 4.5 | LLM | 281 / 868 (abstained on 466) |
| HiTyper | static | 250 / 845 |
| Scalpel | static | 193 / 845 |
| Type4Py | ML | 157 / 845 |

Sonnet 4.6, Opus 4.8, and Touchstone are scored on the same 868-fact commit (the controlled comparison); gpt-4o
(860 facts) and the paper's static/ML tools (845) are on different commits, so their placement is looser. Haiku
4.5 abstained on 466 of the 868 slots. The static and ML figures are from the TypeEvalPy paper, gpt-4o from the
project's LLM evaluation, and the Claude models through the same emit-and-match harness. The gate is
`python -m touchstone.ci` (self-tests, soundness audits against CPython, a verification benchmark) plus the Rocq
proof check.

### Verifier head-to-head

That table is the type-inference axis; on verification, `python -m touchstone.peer_bench` runs a shared corpus of
small contracted functions (each with a known HOLDS / VIOLATED answer) through Touchstone and every installed
peer, counting a problem as *decided* when the tool returns a definite, correct verdict — proved/confirmed for a
true contract, a counterexample or sound rejection for a false one.

| Verifier | Kind | Decided |
| --- | --- | --- |
| **Touchstone** | **SMT + invariant synthesis** | **12 / 12** |
| CrossHair | concolic falsifier | 10 / 12 |
| Nagini | deductive (Viper/JVM) | 9 / 12 |

The three differ on the same problems: Touchstone proves, refutes, and synthesizes the loop invariants, so it
decides every problem; CrossHair confirms straight-line cases and refutes violated ones but cannot confirm loops
over all paths; Nagini proves straight-line contracts but needs a hand-written invariant for the loops.

## Command line

The verbs run from the shell, with the process exit status mirroring the verdict (0 PROVED, 1 REFUTED,
2 UNKNOWN) so they compose in CI:

```sh
touchstone check  d.py                            # trap freedom (and any asserts) for all inputs
touchstone prove  f.py --ensures 'result == x'    # a postcondition over the parameters and `result`
touchstone verify count.py                        # the @require / @ensure contracts written in a file
touchstone verify-all bank.py                     # every @ensure function in a module (a CI gate)
touchstone equiv  impl.py spec.py --func f        # two implementations agree on every input
touchstone change before.py after.py              # an edit preserves the code's properties (gate an AI diff)
touchstone repo   pkg/                            # triage trap freedom across a package
touchstone coverage pkg/                          # verified-subset coverage of a package, tracked over time
touchstone scan   owner/repo | URL | path         # an owner/repo slug, any GitHub link, or a path: classify reachable traps
touchstone gate   --base HEAD~1                   # gate a diff in CI: only the changed functions
touchstone spec   f.py                            # synthesize a contract the function provably satisfies
touchstone infer  m.py                            # sound over-approximate types of a return and its locals
touchstone explain f.py --ensures 'result == x'   # restate a verdict and the reason behind it in plain terms
touchstone repair f.py --generator CMD            # drive a generator until the verifier signs off on a fix
touchstone metamorphic f.py --relation idempotent # an oracle-free property of a unary function (no spec needed)
touchstone doctest f.py                           # mine the function's own doctests into prove obligations
touchstone returns f.py                           # the declared `-> T` annotation vs what the body can return
touchstone leak   f.py                            # every opened resource is closed on every path
touchstone lock   f.py --guarded db.write         # a guarded operation is never reached without a lock held
touchstone termination f.py                       # a loop or recursion halts on every input (or a diverging one)
touchstone cost   f.py                            # a proven symbolic iteration bound for a counted loop
touchstone overflow f.py --width 16               # no signed add/sub/mul wraps a width-N machine integer
touchstone recheck bundle.json                    # re-validate a saved proof bundle, no fresh solve
touchstone covers                                 # what it can prove, the modeled subset, the trust base
```

A refutation comes back with the counterexample and the path it took; add `--repro` and the same command
also emits a runnable failing test that reproduces it. An UNKNOWN is labeled `budget` (raise `--budget`),
`approximation` (a sound over-approximation it will not certify), or `unmodeled` (a construct outside the
subset, named with its line) so the next step is clear.

`--func` takes a top-level name or a `Class.method` (a bare method name works when it is unique across
the file's classes), so the single-file verbs reach the methods that `repo` / `scan` already triage; the
method is analyzed standalone with `self` an ordinary opaque parameter.

For triage at scale, `scan` and `repo` emit `--sarif` (a SARIF 2.1.0 log for GitHub code scanning or any
viewer); `scan --cache FILE` reuses a content-addressed verdict cache so a re-scan only re-triages changed
code; `scan --baseline FILE` reports every finding but exits nonzero only on one not already recorded, to
adopt the scan on a large codebase without fixing every finding at once; `--exclude` drops vendored or
generated modules from triage; `scan --fail-on {bug,suspected,any,none}` sets the exit policy; and `--jobs N`
/ `--progress` set the worker count and print a live triaged-units counter. `scan --format
{text,json,sarif,markdown,github}` picks the output — `markdown` is a paste-ready findings table, `github`
emits Actions workflow commands that annotate the PR diff inline — and a `# touchstone: ignore` comment in a
function drops its finding (marking that trap intentional in source).

`touchstone init` scaffolds the config block, a GitHub Actions workflow, and a baseline in one step; here are
the pieces it writes, which you can also add by hand:

```toml
[tool.touchstone]
exclude = ["*/migrations/*", "vendor/*"]   # globs dropped from triage (still loaded for call resolution)
fail_on = "bug"                            # bug | suspected | any | none
jobs = 8
baseline = ".touchstone-baseline.json"     # default --baseline path
cache = ".touchstone-cache.json"           # default --cache path
```

```yaml
# .github/workflows/touchstone.yml -- scan and annotate findings in the Security tab
permissions:
  security-events: write
jobs:
  scan:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: CharlesCNorton/touchstone@v1.29.0
        with:
          baseline: .touchstone-baseline.json   # fail only on a newly introduced trap
```

```yaml
# .pre-commit-config.yaml -- gate changed functions before each commit
repos:
  - repo: https://github.com/CharlesCNorton/touchstone
    rev: v1.29.0
    hooks:
      - id: touchstone-gate
```

Plain `prove` / `check` analyze symbolically and spawn nothing. `verify_repo(..., jobs=N)` (the `repo` verb's
parallel triage) and the out-of-process sandbox (only when subject execution is enabled — the differential
oracle, a recursive-callee trap fallback, `scan --execute`) use the multiprocessing **spawn** start method,
which re-imports the calling module in each worker. Touchstone marks those workers, so a re-entered
`scan` / `verify_repo` / `coverage` / `verify_diff` no-ops in the worker rather than recursing into a nested
pool: an unguarded driver still completes with the correct result in the main process. Guarding top-level code
with `if __name__ == "__main__":` is therefore optional — recommended only to avoid the redundant re-import
work and any repeated top-level side effects (a stray print per worker).

```
$ touchstone prove f.py --ensures 'result == x'
REFUTED  [property via verified VC generator (Rocq-extracted wpg)]
  counterexample: x=0
  trace:
    line 2: return x + 1    [x=0]
    => returns 1
```

## What it covers

Functional equivalence and predicates; whole-function and interprocedural reasoning over control flow with
multiple loops, arbitrary nesting, break and continue, and any step direction; self-recursion, mutual
recursion, and recursion over lists; whole-program verification across module boundaries; deductive and
synthesized loop invariants, with a sound over-approximation for a for-loop, comprehension, or complex target
the exact engines decline; abstract interpretation (interval, zone, octagon, Karr, polyhedra, machine-integer);
IEEE-754 floating point total over every double, with Inf and NaN as first-class inputs, exact floor division
and modulo, and the `math` module (domain errors as traps, transcendentals as sound over-approximations); numpy
arrays and torch tensors carried by their shape (broadcasting, matrix multiply, axis reductions, reshape, the
shape-mismatch trap); a curated set of pure standard-library functions proved trap free; arrays with quantified
specifications; termination and cost of counted, container, and data-dependent loops and of self- and mutual
recursion, with non-termination reported as a findable bug; exceptions; rely-guarantee concurrency over locks,
counting semaphores, condition variables, and async/await; and separation logic with the frame rule, the magic
wand, and inductive heap predicates.

Container content is modeled, not just shape: set union, intersection, and difference by their membership;
strided slice length for strings and lists; bytes and bytearray element values in [0, 255]; the ord/chr
Unicode codepoint bijection; and the fields of an opaque object parameter, duck-typed numeric so arithmetic on
an attribute decides. A generator's yielded values are checked at every yield, including a loop-carried
accumulator unrolled to a bound; a recursive callee the inliner cannot unfold is summarized at the call site by
its `@ensure` contract; and `verify_equiv` decides equivalence of two for-loops by a relational product.

A non-integer parameter is carried through the value engine rather than abandoned to the integer engines: a
string method such as `encode`, a starred unpacking `a, *b = seq`, and an in-repo class constructor (its
`__init__` confirmed trap free). A behavior-preserving decorator (`functools.lru_cache` / `cache` / `wraps`, or a
binding marker) is analyzed as its undecorated body; a for-loop counter stepped by an integer constant carries
its exact post-loop value `s_init + step * len(seq)`; and a variable possibly read before assignment makes the
checker abstain.

Values carry their real types through the symbolic core; the heap models object identity, aliasing, mutation,
and method dispatch along the C3 MRO; a sequence index is checked against the container's length and a dict key
against the keys provably present (`*args` is such a sequence, `**kwargs` such a dict). The traps that refute a
totality claim are these, plus None in arithmetic, type mismatches, division by zero, and fixed-width overflow;
inside a for-loop the first iteration is checked exactly, so a per-element trap refutes on a non-empty witness
while later iterations stay an over-approximation.

A property is stated in Python over the parameters and `result` (`prove`), with `len`, indexing, membership,
`old(e)` for the entry value, and bounded `all` / `any` over a concrete range or literal; written as
`@require` / `@ensure` decorators (`verify_contracts`); mined from the code's own assertions (`check`); or
given as a Z3 predicate. A counterexample comes back with its execution trace (`explain`) and, on request, a
failing test (`repro_test`).

## Constraint solving and search

Verdicts are produced by an SMT and CHC backend, so the verbs also serve as a decision procedure for
finite-domain problems written as ordinary Python: a `check` counterexample is a satisfying assignment, and a
PROVED verdict is a proof that no assignment exists. A problem is posed as a function whose mined assertion
fails exactly on a solution, or as a postcondition over its parameters. Within the modeled integer, string,
and floating-point fragments this decides, among others:

- combinatorial constraint satisfaction -- Sudoku, N-queens, graph and map coloring, Latin and magic squares,
  logic-grid puzzles, and cryptarithms;
- number theory and Diophantine search -- integer factorization, Pythagorean and Heronian triangles, Pell
  equations, Frobenius numbers, sums of like powers, and self-descriptive, narcissistic, and taxicab numbers;
- algebraic identities and inequalities, including polynomial nonnegativity by sum-of-squares and the nonlinear
  backend (Cauchy-Schwarz, AM-GM, Schur);
- combinatorial impossibility proofs -- pigeonhole, Ramsey bounds, the non-existence of an Eulerian walk, and
  cellular-automaton predecessor states;
- string synthesis over the sequence theory -- constrained text, palindrome construction, and input-sanitizer
  bypasses;
- applied modeling -- balancing chemical equations, stoichiometry and calorimetry, voltage-divider design,
  orbital resonances, calendar arithmetic, dietary planning, and affine-cipher recovery;
- game theory and social choice -- pure-strategy Nash equilibria and Condorcet cycles.

A problem outside the modeled fragments, or one whose unsatisfiability the backend cannot establish within the
deterministic resource bound (primality posed as the absence of a factorization, or a large pigeonhole
instance), returns UNKNOWN rather than a guess.

## The modeled subset

Touchstone is sound by construction in three tiers of trust: a **machine-checked core** (the integer IR and its
weakest-precondition generators, the fixed-width and division/modulo encodings, the interval transfers, and the
further encoders below, all proved in Rocq and run as extracted code); an **engine-modeled subset** (everything
in "What it covers", modeled soundly and cross-checked against CPython, but not each individually proved); and
everything else, which returns **UNKNOWN with a reason** rather than a guess. `touchstone covers` prints the
tiers and `coverage_report()` measures the modeled fraction. An opt-in best-effort mode (`--best-effort`, off by
default) assumes unmodeled calls and framework methods are well-behaved -- a labeled lower-trust verdict for
framework-heavy code; it relaxes trap freedom only.

What returns UNKNOWN, always named, never guessed:

- a decorator that is not a visible simple wrapper -- an attribute or invisible decorator -- and a custom
  metaclass or an ambiguous `__init_subclass__` hook (a visible simple wrapper and an `@D(args)` factory that
  produces one are inlined; the resolvable `type(name, bases, ns)` form, and a single base `__init_subclass__`
  setting constant class attributes, are modeled);
- dynamic reflection that is not statically resolvable: `getattr` / `setattr` with a name no constant binds,
  and `eval` / `exec` / `compile` (a literal or constant-bound attribute name, and `hasattr` from
  attribute-presence tracking, are decided);
- splatting `f(**d)` of a non-literal mapping into another function's named parameters, and a call into a body
  the engine cannot see -- a C extension, an unmodeled module function that can itself raise -- with no value
  or result-type model, unless `--best-effort` is set (a `*args` / `**kwargs` parameter, a `f(*tuple)` or
  `f(*seq)` splat, and the curated trap-free standard-library functions are modeled);
- exception control flow beyond `raise` / `try` / `except` / `finally` over the named trap types;
- operators with no sound encoding in the active theory: float `**` to a power the axioms do not pin, matrix
  `@` outside the tensor shape model, and bitwise `& | ^` between integer variables the precondition does not
  bound to a finite width (a bounded pair is decided exactly via bitvectors, and the `a & (2**k - 1)` idiom
  exactly as a modulo); `round(float, n)` to an exact value;
- a generator with branching control flow (the object is total; its lazily-yielded elements are left to the
  consumer), and a possible read-before-assignment;
- a nonlinear or hard query left undecided within the deterministic budget, where a larger one is available
  with `--budget high`.

## Soundness

Every construct is encoded soundly or returned as UNKNOWN with a reason; an unsupported feature is never
silently skipped. A PROVED is confirmed by a second, independent procedure -- cvc5 where the fragment
round-trips, otherwise a checked SOS certificate or the real-relaxation nlsat lane, with the certificate naming
which backed it; a verdict the second procedure refutes is reported as a prover bug, and when cvc5 is absent the
PROVED degrades to a labeled single-solver result. The certificate attests that two independent solvers agreed
on the encoded query under a deterministic budget -- it cannot attest that the encoding is CPython, which is
what the machine-checked core (for its fragment) and the differential audits below (for the modeled remainder)
enforce. Verification runs under a deterministic resource bound, so
identical input yields an identical verdict on every machine; `proof_bundle` exports a re-checkable bundle (the
discharged SMT-LIB queries, solver versions, configuration, and a content hash) that `recheck_bundle` or any SMT
solver re-verifies. `prove` / `verify` / `check` establish partial correctness (no trap and the postcondition
holds, not termination -- that is `verify_total` / `check --total`); a UNKNOWN that exceeds the default bound can
be retried at `--budget high`.

The trust base is machine-checked in Rocq (`proofs/`), every theorem closed under the global context with no
axioms and no Admitted: the operational semantics of the modeled subset; the VC generator over it (sound and
complete for straight-line assignment and conditionals, sound for while-loops carrying an invariant,
trap-aware); a fixed-width two's-complement model proven to agree with unbounded arithmetic exactly when no
operation overflows; the division and modulo encoding proven to refine the SMT-LIB theory for every conforming
solver; the abstract-domain transfers; the type-inference lattice join; the string, container, and heap
McCarthy-array (read-after-write and frame) laws; the tensor shape algebra (broadcast, concatenation, matrix
multiply, reshape, and transpose); the separation-logic frame rule; the rely-guarantee concurrency principle;
the float divmod laws (over the rationals the IEEE-754 doubles inhabit, so the proof is axiom-free); the
translation as a semantics-preserving functor; and the end-to-end theorem that a discharged verification
condition implies the property. SMTCoq additionally re-checks each integer obligation's certificate inside
Coq's kernel.

The VC generators, the interval operators, the `//` / `%` encoding, and the type-lattice join are extracted
from those proofs; the engine runs the Python image of that extraction directly, and a shipped audit holds each
module byte-for-byte equal to the committed JSON extraction on every install with no Coq toolchain. The
differential checks against CPython and the machine-generated fuzz corpora (integer, sequence, recursion,
while-invariant, interprocedural) are completeness regressions over that verified core.

## Type inference

The same symbolic core infers types in two modes. `infer_types` is over-approximating and sound: the reported
set of type names is guaranteed to contain the value's runtime type, or the location is left UNKNOWN, so a
stated type is never narrower than the truth. `emit_facts` is best-effort exact in the TypeEvalPy schema and
discovers its own targets, carrying argument types across call boundaries, following a value through
reassignment and `is None` / `isinstance` narrowing, and resolving container element types, dict keys,
constructor-set attributes, decorators, and generators.

Recall is the fraction of ground-truth facts matched; precision the fraction of emitted facts that match one.
The commit rate is the fraction of locations the heuristic types rather than abstaining, and accuracy where
committed is the fraction of those that match; recall is their product.

| Evaluation (emit-and-match) | Recall | Precision | Commit | Accuracy (committed) |
| --- | --- | --- | --- | --- |
| TypeEvalPy micro-benchmark | 841 / 868 (96.9%) | 38.5% | 98.5% | 98.4% |
| TypeEvalPy autogen suite | 73,500 / 77,268 (95.1%) | 49.5% | 95.5% | 99.6% |
| CPython standard library | 1073 / 1218 (88.1%) | 92.9% | 93.4% | 94.3% |

| Sound mode (infer_types) | Commit rate | Soundness | Exact |
| --- | --- | --- | --- |
| TypeEvalPy micro-benchmark | 369 / 868 (42.5%) | 100% | 95.1% |
| TypeEvalPy autogen suite | 27,801 / 77,268 (36.0%) | 100% | 92.7% |
| CPython standard library | 151 / 1218 (12.4%) | 100% | 90.7% |

The sound mode commits only where the type is fixed independent of the inputs, so its reach is narrower than the
heuristic's; a committed bound is a proven over-approximation, holding against the observed runtime type in all
151 CPython-cross-check slots. The TypeEvalPy figures are scored against commit `3719de1`; the CPython
cross-check ran on 3.13.2 (the held-out measurement). Counts move with the benchmark commit and the
standard-library version, so the tables are snapshots `python -m touchstone.typeeval` reproduces.

## Run

```sh
pip install touchstone-prover    # z3-solver and cvc5, pinned in pyproject.toml
python -m touchstone.ci          # self-tests, soundness audits, completeness regressions -> "CI OK"
python -m touchstone.examples    # one runnable example per capability, each verdict asserted
python -m touchstone.typeeval    # type-inference recall + precision (CPython cross-check)
python -m touchstone.peer_bench  # decided-fraction head-to-head vs CrossHair (concolic) and Nagini (Viper)
python -m touchstone             # a demonstration
```

The machine-checked proofs run under the Rocq 9.0 opam switch; `verify_coq.sh` also runs the SMTCoq
certificate check when its separate toolchain (see `proofs/toolchain.lock`) is present, and skips it cleanly
otherwise:

```sh
eval "$(opam env --switch=rocq9)" && cd proofs && bash verify_coq.sh
```

## Layout

```
touchstone/      package: core, domains, engines, vcgen, inference, audit, ci, examples (_impl is the engine)
proofs/          Rocq + SMTCoq proofs, the extracted VC generators + interval operators, verify_coq.sh
.github/         continuous integration: the audits and the proof gate on every change
pyproject.toml   package metadata and pinned Python dependencies
```

## License

MIT. See [LICENSE](LICENSE).
