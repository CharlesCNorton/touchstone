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

Sonnet 4.6, Opus 4.8, and Touchstone are scored on the same 868-fact commit, so those three are a controlled
comparison: Touchstone leads at 841, ahead of the two frontier models (824 and 822, themselves a two-fact gap
inside the noise). gpt-4o's 806 is on a different commit (860 facts) and the paper's tools on a third (845),
so their placement is a looser comparison. Haiku 4.5 is the outlier: it answered "unknown" on 466 of the 868
slots, so its 281 reflects abstention rather than wrong inference, and it was about 70 percent accurate on the
402 it did commit to. Touchstone is the only deterministic, reproducible, machine-checked tool at the top, and
on the same-commit set it now matches more facts than the frontier LLMs do. The
static and ML figures are from the TypeEvalPy paper, gpt-4o from the project's LLM evaluation, and the Claude
models through the same emit-and-match harness. The verifier's own gate is `python -m touchstone.ci` (self-tests,
soundness audits against CPython, and a verification benchmark, all required to pass) plus the Rocq proof check.

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

The three have different profiles on the same problems: Touchstone proves, refutes, and synthesizes the loop
invariants, so it decides every problem; CrossHair confirms the straight-line cases and refutes the violated
ones but cannot confirm the loops over all paths; Nagini proves the straight-line contracts and rejects the
violated ones but needs a hand-written invariant for the loops Touchstone synthesizes. Each peer runs from its
own toolchain when installed, so the figures reproduce.

## Command line

The verbs run from the shell, with the process exit status mirroring the verdict (0 PROVED, 1 REFUTED,
2 UNKNOWN) so they compose in CI:

```sh
touchstone check  d.py                            # trap freedom (and any asserts) for all inputs
touchstone prove  f.py --ensures 'result == x'    # a postcondition over the parameters and `result`
touchstone verify count.py                        # the @require / @ensure contracts written in a file
touchstone equiv  impl.py spec.py --func f        # two implementations agree on every input
touchstone change before.py after.py              # an edit preserves the code's properties (gate an AI diff)
touchstone repo   pkg/                            # triage trap freedom across a package
touchstone scan   owner/repo | URL | path         # an owner/repo slug, any GitHub link, or a path: classify reachable traps
touchstone gate   --base HEAD~1                   # gate a diff in CI: only the changed functions
touchstone spec   f.py                            # synthesize a contract the function provably satisfies
touchstone infer  m.py                            # sound over-approximate types of a return and its locals
touchstone explain f.py --ensures 'result == x'   # restate a verdict and the reason behind it in plain terms
touchstone repair f.py --generator CMD            # drive a generator until the verifier signs off on a fix
touchstone covers                                 # what it can prove, the modeled subset, the trust base
```

A refutation comes back with the counterexample and the path it took; add `--repro` and the same command
also emits a runnable failing test that reproduces it. An UNKNOWN is labeled `budget` (raise `--budget`),
`approximation` (a sound over-approximation it will not certify), or `unmodeled` (a construct outside the
subset, named with its line) so the next step is clear.

Plain `prove` / `check` analyze symbolically and spawn nothing. `verify_repo(..., jobs=N)` (the `repo` verb's
parallel triage) and the out-of-process sandbox (only when subject execution is enabled — the differential
oracle, a recursive-callee trap fallback, `scan --execute`) use the multiprocessing **spawn** start method,
which re-imports the calling module in each worker. A script that drives those must guard its top-level code
with `if __name__ == "__main__":`, or the worker re-runs it (you will see the header print once per worker).

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
recursion, and recursion over lists; whole-program verification across module boundaries through the call
graph, so a callee's trap is seen at the caller; deductive and synthesized loop invariants, with a sound
over-approximation proving a postcondition over a for-loop, comprehension, or complex target the exact
invariant engines decline, withholding REFUTED; abstract
interpretation (interval, zone, octagon, Karr, polyhedra, machine-integer); IEEE-754 floating point total
over every double, with Inf and NaN as first-class inputs, exact floor division and modulo, and the `math`
module modeled with its domain errors as traps and the transcendentals as sound over-approximations; numpy
arrays and torch tensors carried by their shape, with broadcasting, matrix multiply, the axis reductions,
reshape, and the shape-mismatch trap; a curated set of pure standard-library functions proved trap free;
arrays with quantified specifications; termination and cost
of counted, container, and data-dependent loops (linear, lexicographic, and synthesized ranking functions)
and of self- and mutual recursion (well-founded measures), with non-termination reported as a findable bug
(a recurrence set witnessing a diverging input); exceptions; rely-guarantee concurrency for all schedules and
depths over locks, counting semaphores, condition variables, and async/await cooperative scheduling; and
separation logic with the frame rule, the magic wand, and inductive heap predicates.

Container content is modeled, not just shape: set union, intersection, and difference by their membership;
strided slice length for strings and lists; bytes and bytearray element values in [0, 255]; the ord/chr
Unicode codepoint bijection; and the fields of an opaque object parameter, duck-typed numeric so arithmetic on
an attribute decides. A generator's yielded values are checked at every yield, including a loop-carried
accumulator unrolled to a bound; a recursive callee the inliner cannot unfold is summarized at the call site by
its `@ensure` contract; and `verify_equiv` decides equivalence of two for-loops by a relational product.

A non-integer parameter is carried through the value engine rather than abandoned to the integer engines: a string
method such as `encode`, a starred unpacking `a, *b = seq` (the rest bound to the exact middle slice), and an in-repo
class constructor (an opaque dataclass-style instance, its `__init__` confirmed trap free). A behavior-preserving
decorator -- a memoizer (`functools.lru_cache` / `cache`), `functools.wraps`, or a binding / marker -- is analyzed as
its undecorated body, while an unknown decorator is inlined or declined; a for-loop counter stepped by an
unconditional integer constant carries its exact post-loop value `s_init + step * len(seq)`, so a length guard proves
a later trap on it safe; and a variable possibly read before assignment on some branch makes the checker abstain
rather than prove the function total.

Values carry their real types through the symbolic core; the heap models object identity, aliasing, mutation,
and method dispatch along the C3 MRO (multiple inheritance); a sequence index is checked against the
container's length and a dict key against the keys provably present (a `*args` parameter is such a sequence
and `**kwargs` such a dict), so a guarded access is proved safe and an unguarded one refuted with the witness. These, with None
in arithmetic, type mismatches, division by zero, and (alongside every integer proof) fixed-width overflow,
are the traps that refute a totality claim; inside a for-loop over a container the first iteration is checked
exactly, so a per-element trap refutes on a non-empty witness while later iterations stay an over-approximation.

A property is stated in Python over the parameters and `result` (`prove`), with `len`, indexing, membership,
`old(e)` for the entry value, and bounded `all` / `any` over a concrete range or literal; written as
`@require` / `@ensure` decorators (`verify_contracts`); mined from the code's own assertions (`check`); or
given as a Z3 predicate. A counterexample comes back with its execution trace (`explain`) and, on request, a
failing test (`repro_test`).

## The modeled subset

Touchstone is sound by construction in three tiers of trust: a **machine-checked core** (the integer IR and
its weakest-precondition generators, the fixed-width and division/modulo encodings, the interval transfers,
and the further encoders below, all proved in Rocq and run as extracted code); an **engine-modeled subset**
(everything in "What it covers", modeled soundly and cross-checked against CPython, but not each individually
proved); and everything else, which returns **UNKNOWN with a reason** rather than a guess. `touchstone covers`
prints the tiers and `coverage_report()` measures the modeled fraction. An opt-in best-effort mode
(`--best-effort` / `best_effort=True`, off by default) instead assumes unmodeled calls and framework methods
are well-behaved, giving a labeled lower-trust verdict for C-extension- and framework-heavy code; it relaxes
trap freedom only and never proves a postcondition over an assumed value.

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

Every construct is encoded soundly or returned as UNKNOWN with a reason, so an unsupported feature is never
silently skipped or assumed away. A PROVED is confirmed by a second, independent procedure -- cvc5 where the
fragment round-trips (its nonlinear coverings for polynomial goals), otherwise a checked SOS certificate or the
real-relaxation nlsat lane, with the certificate naming which backed it; a verdict the second procedure actively
refutes is reported as a prover bug rather than trusted, and when cvc5 is absent the PROVED degrades to a
clearly-labeled single-solver result rather than vanishing. Verification runs under a deterministic
resource bound, so identical input yields an identical verdict on every machine, and carries a reproducibility
certificate; `proof_bundle` exports it as a re-checkable bundle (the discharged SMT-LIB queries, the solver
versions, the configuration, and a content hash) that `recheck_bundle` or any SMT solver re-verifies
independently. `prove` / `verify` / `check` establish partial correctness (no trap and the postcondition
holds, not termination, which is the separate `verify_total` / `check --total`); a true property that exceeds
the default bound and comes back UNKNOWN can be retried at `--budget high`, so incompleteness is visible.

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
from those proofs; the engine runs the Python image of that extraction directly, and a shipped audit holds
each module byte-for-byte equal to the committed JSON extraction on every install with no Coq toolchain. So
the code that runs is the one proven correct in Rocq. With that core verified, the random differential checks
against CPython are a completeness regression measuring precision, and machine-generated fuzz corpora (integer,
sequence, recursion, while-invariant, and interprocedural) feed code no human wrote through the same CPython
oracle, holding the trap-freedom verdicts sound on inputs no human chose.

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

The sound mode commits only where the type is fixed independent of the inputs, so its reach is narrower than
the heuristic's, but a committed bound is a proven over-approximation: on the CPython cross-check, where the
ground truth is the observed runtime type, the inferred bound contained it in all 151 committed slots. The
TypeEvalPy figures are scored against commit `3719de1`; the CPython cross-check ran on 3.13.2 and is the
held-out, out-of-distribution measurement (the autogen suite is generated from templates the heuristic was
tuned against, and its static ground truth carries a few label errors -- `a = func()` returning an int labeled
`str` -- so its raw `--sound` soundness reads 99.7% against those labels, though every committed bound holds
against the observed runtime types). Counts and rates move with the benchmark commit and the standard-library
version, so the tables are snapshots `python -m touchstone.typeeval` reproduces. Every type is spelled by its
runtime `__name__`, so a match reflects an inferred type, not a naming convention.

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
