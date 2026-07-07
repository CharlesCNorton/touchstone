"""Classify why a query returned UNKNOWN, give the next step, and describe what the verifier covers.
Presentation only, no solver."""

# substrings of a Verdict.reason that mark each kind of UNKNOWN.
_BUDGET = ("solver returned unknown", "engine returned unknown", "engine error")
_APPROX = ("over-approxim", "certified verdict", "over-approximation channel")
_NONLINEAR = ("nonlinear: z3 proved it", "no independent corroborator")


def classify_unknown(reason):
    """Classify an UNKNOWN verdict's reason, returning one of:
      'budget'        the solver hit its deterministic resource bound; a higher --budget may decide it.
      'approximation' the property rests on a sound over-approximation (sin/cos/exp/log, a string bound)
                      the engine will not certify.
      'nonlinear'     z3 proved it but no second procedure corroborated it; --budget cannot close it.
      'unmodeled'     a construct outside the modeled subset; the reason names it, often with a line.
      'none'          no reason was recorded."""
    r = (reason or "").lower()
    if not r:
        return "none"
    if any(k in r for k in _NONLINEAR):
        return "nonlinear"
    if any(k in r for k in _BUDGET):
        return "budget"
    if any(k in r for k in _APPROX):
        return "approximation"
    return "unmodeled"


_ADVICE = {
    "budget": "the solver hit its resource budget; retry with a higher --budget (high or max), or tighten --requires",
    "approximation": "the property rests on an over-approximated operation (sin/cos/exp/log or a string bound); "
                     "the verifier soundly declines to certify it rather than risk an unsound PROVED",
    "nonlinear": "z3 proved it but no second procedure corroborated it; try verify_sos_nonneg for a checked "
                 "Positivstellensatz certificate -- a higher --budget will not close a corroboration gap",
    "unmodeled": "a construct outside the modeled subset is in the way (the reason names it, often with a line); "
                 "rephrase it, add a --requires that bounds it, or it is not yet modeled",
    "none": "",
}


def advice(reason):
    """A one-line, actionable next step for an UNKNOWN verdict's reason (see classify_unknown)."""
    return _ADVICE[classify_unknown(reason)]


def budget_helps(reason):
    """Whether raising --budget can change this UNKNOWN. True only for a 'budget' UNKNOWN (a resource bound);
    an approximation or unmodeled UNKNOWN is undecidable-by-abstraction, so more rlimit is a no-op."""
    return classify_unknown(reason) == "budget"


_CAPABILITIES = """\
Touchstone proves properties of a modeled subset of Python over ALL inputs, returning
PROVED / REFUTED (with a counterexample) / UNKNOWN -- by discharging the obligation to z3 and
corroborating with cvc5, not by testing.

Verbs (touchstone <verb> --help for each):
  check       a function is trap-free (no IndexError / KeyError / ZeroDivisionError / overflow) and its
              asserts hold; --total also requires termination
  verify      the @require / @ensure contracts written on the function
  verify-all  every @ensure function in a module (a CI gate)
  prove       a postcondition over the parameters and `result` (--ensures), under a --requires precondition
  equiv       two implementations agree on every input
  change      a proposed edit preserves the code's properties (gate an AI diff), with a proof bundle
  metamorphic an oracle-free property of a unary function: idempotent f(f(x))==f(x) / involution f(f(x))==x
  doctest     the function's own doctests, mined into prove obligations
  returns     the declared return annotation against what the body can return
  leak        every opened resource (open(...)) is closed on every path
  lock        a guarded operation is never reached without a lock held
  termination a loop or recursion provably halts (or a diverging input is found)
  cost        a proven symbolic iteration bound for a counted loop
  overflow    no signed add/sub/mul wraps a width-N machine integer (--width)
  explain     restate a verdict and show a refutation's path and the live values along it
  repo / gate triage or gate trap-freedom across a package or a git diff
  scan        point at a repo URL, a .py file URL, or a local path and report reachable traps (bugs)
  coverage    verified-subset coverage of a package, tracked over time
  spec        synthesize a contract (@require / @ensure) a function provably satisfies
  infer       sound over-approximate types of a return and its locals
  repair      re-run a generator command until the verifier signs off on a fix
  recheck     re-validate a saved proof bundle (change / gate --bundle) with no fresh solve
  covers      this reference
Add --repro to any verdict verb to emit a runnable failing test from a refutation.

Modeled subset:
  values      bounded and unbounded integers, bools, IEEE-754 floats (NaN, +/-0, inf), strings, tuples,
              lists, dicts, sets, and user objects with attributes (heap + aliasing)
  control     straight-line code, if/else, while and for loops (the invariant is synthesized via
              Constrained Horn Clauses), self-recursion, and interprocedural calls across the call graph
  properties  any boolean Python expression over the parameters and `result`: arithmetic, comparisons,
              membership, len, indexing, and the modeled methods
  traps       division by zero, index and key errors, float overflow, failing asserts, and (as a
              companion) signed machine-integer overflow; a try/except whose handlers provably catch
              every body trap kind (by name, tuple, base class, or catch-all) recovers exactly

Trust base:
  the core encodings (operational semantics, VC generator, division/modulo, intervals, floats, strings,
  containers, the heap and separation-logic frame, rely-guarantee concurrency, the type lattice) are
  machine-checked in Rocq with no axioms and no Admitted; integer obligations also ship SMTCoq kernel
  certificates; the modeled subset is continuously cross-checked against CPython. Every PROVED is corroborated
  by a second procedure -- z3 + cvc5 (its nonlinear coverings for polynomial goals), a checked SOS certificate,
  or the real-relaxation nlsat lane -- recorded in the certificate.

Reading an UNKNOWN: its reason says which of three worlds it is in -- a resource budget (raise --budget),
a sound over-approximation it will not certify, or a construct outside the modeled subset (named, often
with a line). `classify_unknown(reason)` returns budget / approximation / unmodeled.
"""


def capabilities():
    """A plain-text reference of the verbs, the modeled subset, the trust base, and how to read an UNKNOWN;
    surfaced as `touchstone covers`."""
    return _CAPABILITIES


__all__ = ["classify_unknown", "advice", "budget_helps", "capabilities"]
