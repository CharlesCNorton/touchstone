"""Human / CI text renderings of a scan report: a Markdown findings table (paste into an issue, a PR, or a bug
list) and GitHub Actions workflow commands (inline PR annotations). SARIF lives in sarif.py; this is the
plain-text side. Pure data transformation -- no solver, no I/O."""

_GH_LEVEL = {"bug": "error", "suspected": "warning", "unconfirmed": "warning",
             "input-validation": "notice", "context-unreachable": "notice"}


def _md_cell(s):
    return str(s if s is not None else "").replace("|", "\\|").replace("\n", " ").strip()


def scan_to_markdown(report):
    """A scan report as a Markdown table, one row per finding, ready to paste into an issue or PR."""
    findings = report.get("findings", [])
    head = "## Touchstone scan — %s" % report.get("target", "")
    summary = "%d function(s): %d proved, %d refuted, %d unknown (%s)." % (
        report.get("functions", 0), report.get("proved", 0), report.get("refuted", 0),
        report.get("unknown", 0), "executed" if report.get("executed") else "symbolic")
    if not findings:
        return "%s\n\n%s\n\nNo reachable traps found.\n" % (head, summary)
    rows = ["| Location | Exception | Class | Detail |", "| --- | --- | --- | --- |"]
    for f in findings:
        loc = f["location"] + (":%d" % f["line"] if f.get("line") else "")
        if f.get("baselined"):
            loc += " (baselined)"
        rows.append("| `%s` | %s | %s | %s |" % (_md_cell(loc), _md_cell(f.get("exception")),
                                                 _md_cell(f.get("classification")), _md_cell(f.get("label"))))
    return "%s\n\n%s\n\n%s\n" % (head, summary, "\n".join(rows))


def _gh_data(s):
    return str(s if s is not None else "").replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def _gh_prop(s):
    return _gh_data(s).replace(",", "%2C").replace(":", "%3A")


def scan_to_github(report):
    """Scan findings as GitHub Actions workflow commands -- one ::error / ::warning / ::notice per finding, with
    the file and line when known, so a CI step annotates the PR diff inline. Returns the text to print."""
    out = []
    for f in report.get("findings", []):
        level = _GH_LEVEL.get(f.get("classification"), "warning")
        props = []
        if f.get("module"):
            props.append("file=" + _gh_prop(f["module"].replace(".", "/") + ".py"))
            if f.get("line"):
                props.append("line=%d" % f["line"])
        props.append("title=" + _gh_prop("Touchstone: " + (f.get("exception") or f.get("classification") or "trap")))
        sep = " " + ",".join(props) if props else ""
        out.append("::%s%s::%s" % (level, sep, _gh_data("%s: %s" % (f["location"], f.get("label") or ""))))
    return "\n".join(out) + ("\n" if out else "")
