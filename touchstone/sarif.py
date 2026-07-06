"""SARIF 2.1.0 output for the triage verbs (scan / repo / gate), so findings drop into GitHub code scanning
and any SARIF viewer. A scan finding becomes a result with a rule per exception kind, a physical location
(the module's file path and the def's line) and a logical location (the dotted name); a repo / gate row
becomes one result per refuted function. Pure data transformation -- no solver, no I/O."""
from .engines import finding_fingerprint

SARIF_VERSION = "2.1.0"
_SCHEMA = "https://json.schemastore.org/sarif-2.1.0.json"
_TOOL_URI = "https://pypi.org/project/touchstone-prover/"

# A finding's classification to a SARIF result level. A confirmed crashing bug is an error; an unconfirmed or
# suspected trap is a warning; an intended raise or an unreachable helper is a note, not a failure signal.
_LEVEL = {"bug": "error", "suspected": "warning", "unconfirmed": "warning",
          "input-validation": "note", "context-unreachable": "note"}


def _module_uri(module):
    """A dotted module name as a repo-relative file path (the path GitHub code scanning annotates)."""
    return module.replace(".", "/") + ".py" if module else None


def _log(rules, results):
    return {"version": SARIF_VERSION, "$schema": _SCHEMA,
            "runs": [{"tool": {"driver": {"name": "touchstone", "informationUri": _TOOL_URI, "rules": rules}},
                      "results": results}]}


def _logical(name, kind="function"):
    return {"logicalLocations": [{"fullyQualifiedName": name, "kind": kind}]}


def scan_to_sarif(report):
    """The dict scan() returns as a SARIF log: one result per finding, a rule per exception kind, a stable
    partialFingerprint (the trap site, independent of the sampled witness) so a viewer can track a result
    across runs."""
    rules, rule_idx, results = [], {}, []
    for f in report.get("findings", []):
        kindname = f.get("exception") or f.get("classification") or "refuted"
        rid = "trap/" + kindname
        if rid not in rule_idx:
            rule_idx[rid] = len(rules)
            rules.append({"id": rid, "name": rid.replace("/", "-"),
                          "shortDescription": {"text": "a reachable %s" % kindname}})
        loc = _logical(f["location"])
        uri = _module_uri(f.get("module"))
        if uri:
            phys = {"artifactLocation": {"uri": uri}}
            if f.get("line"):
                phys["region"] = {"startLine": f["line"]}
            loc["physicalLocation"] = phys
        result = {"ruleId": rid, "ruleIndex": rule_idx[rid],
                  "level": _LEVEL.get(f.get("classification"), "warning"),
                  "message": {"text": f.get("label") or f["location"]},
                  "locations": [loc],
                  "partialFingerprints": {"touchstone/v1": finding_fingerprint(f)}}
        if f.get("baselined"):                              # a finding the baseline already records: keep it in the
            result["suppressions"] = [{"kind": "external"}]   # log but mark suppressed, so only new ones surface
        results.append(result)
    return _log(rules, results)


def rows_to_sarif(rows):
    """verify_repo / gate rows [(name, status), ...] as a SARIF log: one error result per REFUTED function. A
    gate label of the form `path.py::func` carries a physical location; a plain dotted repo name is logical
    only."""
    rid = "trap/refuted"
    rule = {"id": rid, "name": "trap-refuted",
            "shortDescription": {"text": "a reachable trap with no asserted specification"}}
    results = []
    for name, status in rows:
        if status != "REFUTED":
            continue
        loc = _logical(name)
        if "::" in name:
            uri, _, _fn = name.partition("::")
            loc["physicalLocation"] = {"artifactLocation": {"uri": uri}}
        results.append({"ruleId": rid, "ruleIndex": 0, "level": "error",
                        "message": {"text": "%s: a reachable trap" % name},
                        "locations": [loc],
                        "partialFingerprints": {"touchstone/v1": name}})
    return _log([rule], results)
