"""Re-checkable reproducibility bundles for a PROVED.

A PROVED is discharged as an UNSAT refutation query. proof_bundle captures every such query as portable
SMT-LIB2 with the solver versions, the deterministic configuration, and a content hash; recheck_bundle
re-runs each through an SMT solver and requires UNSAT, so a third party re-verifies the PROVED from the
bundle alone. Covers equivalence, predicates, and the loop-free / verified-VC prove fragment; a CHC/Spacer
loop proof discharges an invariant rather than a query, so its bundle is not query-checkable."""
import hashlib
import z3
from . import core


def _solver_versions():
    out = {"z3": ".".join(str(x) for x in z3.get_version())}
    try:
        import cvc5
        out["cvc5"] = getattr(cvc5, "__version__", "unknown")
    except Exception:
        pass
    return out


def _query_smt2(claim_false):
    """One discharged refutation query as a self-contained SMT-LIB2 string (UNSAT means the property holds)."""
    s = z3.Solver()
    s.add(claim_false)
    return "(set-logic ALL)\n" + s.to_smt2()


def proof_bundle(run, label="verification"):
    """Run a verification thunk with obligation recording on and return a re-checkable bundle of the
    refutation queries it discharged as UNSAT. Built only for a PROVED that went through the SMT-query path.
    The bundle holds the queries in SMT-LIB2, the solver versions, the deterministic configuration, and a
    sha256 over them."""
    saved = core.RECORD_OBLIGATIONS
    obs = []
    core.RECORD_OBLIGATIONS = obs
    try:
        v = run()
    finally:
        core.RECORD_OBLIGATIONS = saved
    base = {"status": v.status, "property": v.prop, "target": v.target, "technique": v.technique, "label": label}
    if v.status != core.PROVED:
        return {**base, "checkable": False, "reason": "a re-checkable bundle is built only for a PROVED verdict"}
    try:
        queries = [_query_smt2(cf) for cf in obs]
    except z3.Z3Exception as e:
        return {**base, "checkable": False, "reason": "a query could not be serialized: %s" % e}
    if not queries:
        return {**base, "checkable": False,
                "reason": "PROVED via an engine that discharges no single SMT query (e.g. a CHC invariant)"}
    return {**base, "checkable": True, "queries": queries, "n_queries": len(queries),
            "solvers": _solver_versions(), "config": {"rlimit": core.SOLVE_RLIMIT, "seed": 0},
            "sha256": hashlib.sha256("\n".join(queries).encode()).hexdigest()}


def _recheck_z3(smt2):
    try:
        fs = z3.parse_smt2_string(smt2)
        s = z3.Solver()
        s.add(*fs)
        return s.check() == z3.unsat
    except Exception:
        return False


def _recheck_cvc5(smt2):
    try:
        import cvc5
        solver = cvc5.Solver()
        parser = cvc5.InputParser(solver)
        parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, smt2, "bundle")
        sm = parser.getSymbolManager()
        result = None
        while True:
            cmd = parser.nextCommand()
            if cmd.isNull():
                break
            out = cmd.invoke(solver, sm)
            if out and out.strip() in ("sat", "unsat", "unknown"):
                result = out.strip()
        return result == "unsat"
    except Exception:
        return False


def recheck_bundle(bundle):
    """Independently re-verify a bundle: re-run each SMT-LIB2 query through z3 (and cvc5 where it parses) and
    require UNSAT, after confirming the content hash. `verified` is True only when z3 re-confirms every query
    UNSAT and the hash matches; `cvc5_corroborated` counts the queries the second solver also confirms."""
    if bundle.get("status") != core.PROVED or not bundle.get("checkable"):
        return {"verified": False, "reason": "not a re-checkable PROVED bundle"}
    queries = bundle.get("queries", [])
    if not queries:
        return {"verified": False, "reason": "no queries to re-check"}
    if hashlib.sha256("\n".join(queries).encode()).hexdigest() != bundle.get("sha256"):
        return {"verified": False, "reason": "content hash mismatch (bundle altered)"}
    cvc5_avail = core.cvc5_available()
    z3_all = all(_recheck_z3(q) for q in queries)
    cvc5_ok = sum(1 for q in queries if cvc5_avail and _recheck_cvc5(q))
    return {"verified": bool(z3_all), "queries": len(queries), "z3_unsat_all": z3_all,
            "cvc5_available": cvc5_avail, "cvc5_corroborated": cvc5_ok, "sha256_ok": True}


__all__ = ["proof_bundle", "recheck_bundle"]
