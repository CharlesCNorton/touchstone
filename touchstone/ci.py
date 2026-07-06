"""Deterministic CI: self-tests, soundness audits, and differential completeness regressions.
python -m touchstone.ci

Soundness rests on the Rocq proofs (proofs/, run by verify_coq.sh) and the SMTCoq certificates: the
operational semantics, the VC generator, the division/modulo encoding, and the interval transfers are
machine-checked. The differential audits below run self-generated programs against CPython as a
completeness and defense-in-depth cross-check, measuring how often a property is decided. They enable
ALLOW_SUBJECT_EXECUTION for their duration.

Exits nonzero on any failed assertion or SoundnessError.
"""
import sys
from . import _impl as t
from . import core
from . import domains as benchmark


def _decided(rep):
    """Percentage of verdicts the verifier resolved (PROVED or REFUTED) -- the completeness rate."""
    total = rep["proved"] + rep["refuted"] + rep["unknown"]
    return 100.0 * (rep["proved"] + rep["refuted"]) / total if total else 100.0


def main():
    t.run_self_tests()

    # The bulk audits below cross-check every verdict against CPython -- a stronger oracle than cvc5's second
    # opinion -- so cvc5 corroboration (and its costly nonlinear CAD) is disabled for them; self-tests above and the
    # verification showcase below keep it on, so the corroboration path stays gated.
    core.REQUIRE_CORROBORATION = False

    rep = t.soundness_audit(trials=200)
    assert rep["model_checks"] > 0 and rep["unknown"] == 0, rep
    print(f"AUDIT model       : {rep['model_checks']} cross-checks "
          f"({rep['proved']} proved, {rep['refuted']} refuted), 0 contradictions")

    pairs = t.division_encoding_audit(bound=60)
    print(f"AUDIT division    : {pairs} (a,b) pairs vs CPython, 0 mismatches")

    fpairs = t.float_divmod_audit()
    print(f"AUDIT float divmod: {fpairs} (a,b) pairs vs CPython float // and %, 0 mismatches")

    tx = t.transcendental_axiom_audit()
    print(f"AUDIT transcendtl : {tx} args vs CPython sin/cos/exp/log axioms, 0 violations")

    pw = t.math_pow_axiom_audit()
    print(f"AUDIT math.pow    : {pw} args vs CPython math.pow domain trap and x ** n power axioms, 0 violations")

    sm = t.string_method_axiom_audit()
    print(f"AUDIT str methods : {sm} strings vs CPython str over-approximation axioms, 0 violations")

    sf = t.string_fragile_op_audit()
    print(f"AUDIT str fragile : {sf} z3 last_indexof/replace_all vs Python (the cvc5-uncorroborated fragment), 0 violations")

    facts = t.relational_domain_audit(trials=300)
    print(f"AUDIT relational  : {facts} relational facts replayed, 0 violations")

    core.ALLOW_SUBJECT_EXECUTION = True
    try:
        d = t.differential_equiv_audit(trials=150)
        dl = t.differential_loop_audit(trials=80)
        dh = t.differential_heap_audit(trials=120)
        ds = t.differential_sequence_audit(trials=60)
        dt = t.differential_typed_audit()
        dm = t.differential_method_audit()
        si = t.differential_sound_inference_audit()
        sl = t.differential_sound_local_audit()
        ref = t.refinement_audit()
    finally:
        core.ALLOW_SUBJECT_EXECUTION = False
    assert d["exec_checks"] > 0, d
    print(f"AUDIT differential: {d['exec_checks']} verdicts vs CPython "
          f"({d['proved']} proved, {d['refuted']} refuted), {_decided(d):.0f}% decided, 0 disagreements")
    assert dl["exec_checks"] > 0, dl
    print(f"AUDIT loop-diff   : {dl['exec_checks']} loop verdicts vs CPython "
          f"({dl['proved']} proved, {dl['refuted']} refuted), {_decided(dl):.0f}% decided, 0 disagreements")
    assert dh["exec_checks"] > 0, dh
    print(f"AUDIT heap-diff   : {dh['exec_checks']} heap verdicts vs CPython "
          f"({dh['proved']} proved, {dh['refuted']} refuted), {_decided(dh):.0f}% decided, 0 disagreements")
    assert ds["exec_checks"] > 0, ds
    print(f"AUDIT seq-diff    : {ds['exec_checks']} sequence-loop verdicts vs CPython "
          f"({ds['proved']} proved, {ds['refuted']} refuted), {_decided(ds):.0f}% decided, 0 disagreements")
    assert dt["checks"] > 0, dt
    print(f"AUDIT typed-diff  : {dt['checks']} float/bool/string verdicts vs CPython "
          f"({dt['proved']} proved, {dt['refuted']} refuted), 0 disagreements")
    assert dm["checks"] > 0 and dm["proved"] > 0, dm
    print(f"AUDIT method-call : {dm['checks']} builtin method calls vs CPython "
          f"({dm['proved']} proved, {dm['refuted']} refuted), 0 contradictions")
    assert si["claims"] > 0 and si["runs"] > 0 and si["abstain"] > 0, si
    print(f"AUDIT type-infer  : {si['claims']} sound return claims over {si['runs']} CPython runs "
          f"({si['abstain']} abstentions), 0 over-approximation violations")
    assert sl["claims"] > 0 and sl["abstain"] > 0, sl
    print(f"AUDIT local-infer : {sl['claims']} sound local claims over {sl['runs']} CPython runs "
          f"({sl['abstain']} abstentions), 0 over-approximation violations")
    assert ref["checks"] > 0, ref
    print(f"AUDIT refinement  : {ref['checks']} per-construct evaluations vs CPython "
          f"({ref['constructs']} constructs), 0 divergences")

    core.REQUIRE_CORROBORATION = True                 # the showcase + examples keep corroboration on, so its
    bm = t.verification_benchmark()                   # path stays exercised (and their verdicts stay faithful)
    assert bm["pass_rate"] == 100.0, bm
    print(f"BENCHMARK         : {bm['total']} problems, {bm['pass_rate']:.0f}% pass, "
          f"{bm['precision']:.0f}% precision")

    from . import examples
    bad = examples.run(verbose=False)
    assert bad == 0, f"{bad} examples did not match"
    print(f"EXAMPLES          : {len(examples.EXAMPLES)} capability examples, all discharged as expected")

    cov = t.coverage_report()
    assert cov["rate"] >= 80.0, cov
    print(f"COVERAGE          : {cov['modeled']}/{cov['functions']} representative functions modeled "
          f"({cov['rate']:.0f}%)")

    core.REQUIRE_CORROBORATION = False                # external + fuzz bulk: CPython-cross-checked, corroboration off
    core.ALLOW_SUBJECT_EXECUTION = True               # the oracle runs the external code in the sandbox
    try:
        bench = benchmark.run_benchmark(samples=40)
    finally:
        core.ALLOW_SUBJECT_EXECUTION = False
    assert bench["contradictions"] == 0 and bench["decided"] > 0, bench
    print(f"EXT BENCHMARK     : {bench['decided']}/{bench['total']} decided ({bench['recall']:.0f}% recall) "
          f"on external code, {bench['precision']:.0f}% precision, {bench['contradictions']} contradictions "
          f"over {bench['oracle_checks']} CPython runs")

    core.ALLOW_SUBJECT_EXECUTION = True               # fuzz: machine-generated programs across the integer,
    try:                                              # sequence, recursion, while-invariant, and interproc engines
        fz = [("integer", benchmark.run_benchmark(benchmark.random_corpus(120, seed=0), samples=25)),
              ("list", benchmark.run_benchmark(benchmark.random_list_corpus(60, seed=0), samples=20)),
              ("recursive", benchmark.run_benchmark(benchmark.random_rec_corpus(60, seed=0), samples=20)),
              ("while", benchmark.run_benchmark(benchmark.random_while_corpus(60, seed=0), samples=20)),
              ("interproc", benchmark.run_benchmark(benchmark.random_interproc_corpus(60, seed=0), samples=20)),
              ("object-attr", benchmark.run_benchmark(benchmark.random_object_attr_corpus(60, seed=0), samples=20))]
    finally:
        core.ALLOW_SUBJECT_EXECUTION = False
    assert all(f["contradictions"] == 0 for _, f in fz), fz
    print("FUZZ              : %s generated programs decided, %d contradictions over %d CPython runs"
          % (" + ".join("%d %s" % (f["decided"], name) for name, f in fz),
             sum(f["contradictions"] for _, f in fz), sum(f["oracle_checks"] for _, f in fz)))

    core.REQUIRE_CORROBORATION = True                 # restore the default for the remainder
    ce = t.committed_extraction_audit()               # always available: each engine module == the committed JSON's
    print(f"EXTRACTION        : {ce['checks']} engine modules (wpg/vcg, intervals, encoding, lattice join) == the "
          f"committed Rocq JSON extraction, transpiled in-process (no coqc / ocamlfind)")
    la = t.extracted_lattice_audit()                  # the type-inference join, held equal to its proof's extraction
    print(f"LATTICE           : {la['checks']} type-bound joins, in-engine soundinfer._join == committed Rocq "
          f"extraction (_generated/encoders_rocq), proven to over-approximate both operands")
    vca = t.extracted_vcgen_audit(trials=2000)        # the OCaml extraction too, where build_vcgen.sh has run
    if vca["available"]:
        print(f"VCGEN (ocaml)     : {vca['checks']} VCs, in-engine generator == the OCaml extraction")
    via = t.extracted_intervals_audit(trials=2000)
    if via["available"]:
        print(f"INTERVALS (ocaml) : {via['checks']} ops, in-engine operators == the OCaml extraction")
    eac = t.extracted_encoding_committed_audit()      # the in-engine z3 encoding vs the committed extraction
    print(f"ENCODING          : {eac['checks']} (a,b) pairs, in-engine py_floordiv/py_mod == committed "
          f"Rocq extraction (_generated/encoding_rocq)")
    ea = t.extracted_encoding_audit()                 # the OCaml extraction too, where build_encoding.sh has run
    if ea["available"]:
        print(f"ENCODING (ocaml)  : {ea['checks']} (a,b) pairs, also == the OCaml extraction")

    ob = t.committed_obligations_audit()              # the engine's integer obligations == the committed file the
    if ob["available"]:                               # smtcoq CI job re-checks in Coq's kernel on every commit
        print(f"OBLIGATIONS       : {ob['checks']} integer obligations == committed proofs/touchstone_obligations.v "
              f"(re-checked in Coq's kernel every commit by the smtcoq CI job)")

    print("CI OK")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, t.SoundnessError) as e:
        import traceback
        traceback.print_exc()
        print(f"CI FAILED: {e}")
        sys.exit(1)
