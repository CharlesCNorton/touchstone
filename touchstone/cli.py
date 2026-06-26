"""Command-line entry points, one per use mode, over the same engine the Python API drives. The verbs:

  verdict-returning (the exit status mirrors the verdict, so they compose in CI):
    touchstone check      FILE [--func NAME] [--requires EXPR] [--total]   trap freedom (and any asserts) for all inputs
    touchstone verify     FILE [--func NAME]                               the @require / @ensure contracts written in FILE
    touchstone verify-all FILE                                            every @ensure function in a module (a CI gate)
    touchstone prove      FILE --ensures EXPR [--requires EXPR] [--func]   a postcondition over the parameters and `result`
    touchstone equiv      IMPL SPEC --func NAME                            two implementations agree on every input
    touchstone change     BEFORE AFTER [--func NAME] [--ensures EXPR]      a change preserves the code's properties (gate an AI diff)
    touchstone explain    FILE [--ensures EXPR] [--func NAME]              check / prove, then show a refutation's path and live values

  triage across a tree:
    touchstone repo       DIR [--total] [--changed PATHS] [--jobs N]       trap freedom of every top-level function in a package
    touchstone scan       TARGET [--execute] [--repro]                     reachable traps in an owner/repo, a URL, or a local path
    touchstone gate       [DIR] [--base REF] [--changed PATHS]             verify each changed function (an AI-diff / PR gate)
    touchstone coverage   DIR [--history FILE] [--jobs N]                  verified-subset coverage of a package, tracked over time

  synthesis and inference:
    touchstone spec       FILE [--func NAME]                               synthesize a contract the function provably satisfies
    touchstone infer      FILE [--func NAME] [--emit]                      sound over-approximate types of a return and its locals
    touchstone repair     --generator CMD [--ensures EXPR] [--before F]    re-run a generator until the property holds

  servers and meta:
    touchstone lsp / mcp                                                  the language server / the MCP verification-tools server (stdio)
    touchstone covers                                                     what it can prove, and the modeled subset
    touchstone examples / selftest / demo                                 the capability gallery / the self-tests / the narrated demo

FILE may be - to read the source from standard input, so the verbs compose with cat and heredocs. The
verdict verbs set the exit status (0 PROVED, 1 REFUTED, 2 UNKNOWN; a usage, read, or syntax error exits 3)
and share --json (one machine-readable object), --quiet (only the verdict word), --timeout MS, --budget
{standard,high,max} (the deterministic resource bound), --repro (a failing test on a refutation), and
--best-effort (assume unmodeled calls are well-behaved, a lower-trust verdict).
"""
import argparse
import ast
import json
import os
import subprocess
import sys

from . import _impl as t

_EXIT = {"PROVED": 0, "REFUTED": 1, "UNKNOWN": 2}

_EPILOG = """\
examples:
  touchstone prove f.py --ensures 'result == 2 * x'
  touchstone prove f.py --ensures 'result >= 0' --requires 'x >= 0'
  cat f.py | touchstone prove - --ensures 'result >= 0'
  touchstone verify bank.py --func withdraw
  touchstone verify-all bank.py --quiet
  touchstone equiv impl.py spec.py --func f
  touchstone check parser.py --total --timeout 5000
  touchstone infer module.py --emit

exit status: 0 PROVED, 1 REFUTED, 2 UNKNOWN, 3 usage / read / syntax error
"""

# A short, actionable nudge for the recurring UNKNOWN reasons, keyed by a substring of the reason.
_HINTS = (
    ("no @ensure", "annotate the function with @ensure(...), or use `prove --ensures EXPR`"),
    ("no function", "the file defines no function to analyze"),
    ("use before assignment", "a variable may be read before it is assigned on some path"),
    ("over-approximated", "the property rests on a sin/cos/exp/log/str bound that yields no certified verdict"),
    ("outside the", "the function uses a construct outside the modeled subset (see the reason)"),
    ("solver returned unknown", "the query may have hit the resource budget; retry with --budget high, or tighten --requires"),
    ("could not translate", "the property references a name or operation the engine does not model"),
)

_COLORS = {"PROVED": "32", "REFUTED": "31", "UNKNOWN": "33",     # green / red / yellow
           "BUG": "1;31", "VALIDATION": "33", "UNCONFIRMED": "33", "SUSPECTED": "1;33"}   # bug = bold red, suspected = bold yellow


def _use_color():
    """Color only when writing to a terminal and NO_COLOR is unset (https://no-color.org)."""
    return sys.stdout.isatty() and not os.environ.get("NO_COLOR")


def _paint(status, width=0):
    """The verdict word, padded to `width`, wrapped in its color when the output is a terminal."""
    text = status.ljust(width) if width else status
    code = _COLORS.get(status)
    return "\033[%sm%s\033[0m" % (code, text) if code and _use_color() else text


def _die(msg, code=3):
    """Print a one-line error to stderr and exit; the CLI never surfaces a traceback for bad input."""
    print("error: " + msg, file=sys.stderr)
    raise SystemExit(code)


def _label(path):
    return "<stdin>" if path == "-" else path


def _read(path):
    if path == "-":
        try:
            return sys.stdin.read()
        except (OSError, UnicodeDecodeError) as e:
            _die("cannot read standard input: %s" % e)
    try:
        with open(path, encoding="utf-8") as fh:
            return fh.read()
    except (OSError, UnicodeDecodeError) as e:
        _die("cannot read %s: %s" % (path, e))


def _functions(src, path):
    """Top-level function names defined in `src`, exiting cleanly on a syntax error."""
    try:
        mod = ast.parse(src)
    except SyntaxError as e:
        _die("%s: invalid Python syntax: line %s: %s" % (path, e.lineno, e.msg))
    return [n.name for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]


def _require_func(src, path, func):
    """Validate the file parses and (if --func was given) defines that function, naming what is there
    when it does not, so a typo or wrong file is a clear message rather than a misleading UNKNOWN."""
    names = _functions(src, path)
    if not names:
        _die("%s: no function definition found" % path)
    if func is not None and func not in names:
        _die("%s: no function %r (found: %s)" % (path, func, ", ".join(names)))


def _resolve_target(src, path, func):
    """The function to verify, named explicitly so the verdict is unambiguous. A given --func is validated;
    with --func omitted the sole function is used, but a module defining several is an explicit usage error
    demanding a choice -- never a silent pick that produces an authoritative verdict about the wrong code."""
    names = _functions(src, path)
    if not names:
        _die("%s: no function definition found" % path)
    if func is not None:
        if func not in names:
            _die("%s: no function %r (found: %s)" % (path, func, ", ".join(names)))
        return func
    if len(names) == 1:
        return names[0]
    _die("%s: defines %d functions (%s); name one with --func -- it is verified by name, never picked "
         "silently" % (path, len(names), ", ".join(names)))


_CONTRACT_DECOS = frozenset({"require", "requires", "ensure", "ensures"})


def _ensure_decos(fn):
    """The @ensure / @ensures decorator calls on a function definition."""
    for d in fn.decorator_list:
        nm = (d.func.attr if isinstance(d, ast.Call) and isinstance(d.func, ast.Attribute)
              else d.func.id if isinstance(d, ast.Call) and isinstance(d.func, ast.Name) else None)
        if nm in ("ensure", "ensures"):
            yield d


def _contracted_functions(src):
    """Names of functions in `src` that carry an @ensure postcondition (a whole-module contract scan)."""
    try:
        mod = ast.parse(src)
    except SyntaxError:
        return []
    return [n.name for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
            and any(True for _ in _ensure_decos(n))]


def _function_ensures(src, func):
    """The first @ensure string expression on `func` (for a --repro test), or None for the lambda form."""
    try:
        mod = ast.parse(src)
    except SyntaxError:
        return None
    for n in mod.body:
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name == func:
            for d in _ensure_decos(n):
                if d.args and isinstance(d.args[0], ast.Constant) and isinstance(d.args[0].value, str):
                    return d.args[0].value
    return None


def _check_spec(expr, label):
    try:
        compile(expr, "<%s>" % label, "eval")
    except SyntaxError as e:
        _die("invalid --%s expression: %s" % (label, e.msg))


def _hint(reason):
    return next((h for k, h in _HINTS if reason and k in reason), None)


def _report(v, src=None, repo=None, json_out=False, quiet=False, repro=None):
    """Print a verdict in a stable, greppable form (or as one JSON object) and return the matching
    process exit code. A refutation is expanded through `explain` so the counterexample and the path
    it took are shown. When `repro` is a generated test (see --repro), it is added as the JSON `repro`
    field, or printed verbatim after the verdict so it can be piped into a test file."""
    if v.status == "REFUTED" and src is not None and v.trace is None:
        v = t.explain(v, src, repo)
    if json_out:
        obj = {"status": v.status, "property": v.prop, "target": v.target,
               "technique": v.technique, "counterexample": v.counterexample,
               "counterexample_inputs": v.counterexample_inputs, "reason": v.reason or None,
               "certificate": v.certificate, "trace": v.trace, "hint": _hint(v.reason)}
        if v.status == "UNKNOWN":
            obj["category"] = t.classify_unknown(v.reason)
            obj["budget_helps"] = t.budget_helps(v.reason)   # whether raising --budget can change it
        if repro is not None:
            obj["repro"] = repro
        print(json.dumps(obj))
        return _EXIT.get(v.status, 3)
    if quiet:
        print(_paint(v.status))
    else:
        print("%s  %s  [%s via %s]" % (_paint(v.status), v.target, v.prop, v.technique))   # name the verified function
        if v.status == "REFUTED":
            if v.counterexample:
                print("  counterexample: %s" % v.counterexample)
            elif v.counterexample_inputs:
                print("  counterexample: %s" % ", ".join("%s=%s" % kv for kv in sorted(v.counterexample_inputs.items())))
            if v.trace:
                print("  trace:")
                for line in v.trace.splitlines():
                    print("    " + line)
        elif v.status == "UNKNOWN":
            if v.reason:
                print("  reason: %s" % v.reason)
            cat = t.classify_unknown(v.reason)
            if cat != "none":
                print("  category: %s" % cat)
            hint = _hint(v.reason) or t.advice(v.reason)
            if hint:
                print("  hint: %s" % hint)
            if cat in ("approximation", "unmodeled"):        # raising --budget cannot change an abstraction limit
                print("  --budget: a no-op here (an abstraction / unmodeled limit, not a resource bound)")
        elif v.status == "PROVED" and v.certificate:
            print("  %s" % v.certificate)
    if repro is not None:
        print("\n# --- reproducing test (run it: it fails on the counterexample) ---")
        print(repro, end="")
    return _EXIT.get(v.status, 3)


def _cmd_check(a):
    src = _read(a.file)
    func = _resolve_target(src, _label(a.file), a.func)
    _check_spec(a.requires, "requires")
    v = t.check(src, requires=a.requires, total=a.total, target=func, best_effort=a.best_effort)
    repro = t.repro_test(v, src, requires=a.requires, func=func) if a.repro else None
    return _report(v, src, json_out=a.json, quiet=a.quiet, repro=repro)


def _cmd_verify(a):
    src = _read(a.file)
    func = _resolve_target(src, _label(a.file), a.func)
    v = t.verify_contracts(src, target=func)
    if v.status == "UNKNOWN" and v.reason and "no @ensure" in v.reason:
        # diagnose contracts across the whole module: distinguish "this function has none" from "the module
        # has none anywhere", and name the contracted functions so working contracts are not hidden.
        contracted = [n for n in _contracted_functions(src) if n != func]
        if contracted:
            print("note: %r carries no @ensure contract; these do: %s -- verify one with --func, or "
                  "verify-all" % (func, ", ".join(contracted)), file=sys.stderr)
        else:
            print("note: no function in this module carries an @ensure contract; state one with "
                  "`prove --ensures EXPR`", file=sys.stderr)
    repro = None
    if a.repro and v.status == "REFUTED":
        ens = _function_ensures(src, func)
        if ens is not None:
            repro = t.repro_test(v, src, ensures=ens, func=func)
    return _report(v, src, json_out=a.json, quiet=a.quiet, repro=repro)


def _cmd_verify_all(a):
    """Verify every @ensure function in the module and report one line per function. The exit status
    is REFUTED-dominant: nonzero if any contract is refuted, so this drops straight into a CI gate."""
    src = _read(a.file)
    _functions(src, _label(a.file))                              # surface a syntax error as a clean line
    results = t.verify_all(src)
    if not results:
        _die("%s: no function carries an @ensure contract" % _label(a.file))
    if a.json:
        print(json.dumps([{"function": n, "status": v.status, "property": v.prop,
                           "technique": v.technique, "reason": v.reason or None} for n, v in results]))
    elif a.quiet:
        for n, v in results:
            print("%s %s" % (_paint(v.status), n))
    else:
        width = max(len(n) for n, _ in results)
        for n, v in results:
            print("%s  %s  [%s]" % (_paint(v.status, 7), n.ljust(width), v.technique))
            if v.status == "UNKNOWN" and v.reason:
                print("    reason: %s" % v.reason)
    statuses = {v.status for _, v in results}
    return 1 if "REFUTED" in statuses else 2 if "UNKNOWN" in statuses else 0


def _cmd_prove(a):
    src = _read(a.file)
    func = _resolve_target(src, _label(a.file), a.func)
    _check_spec(a.ensures, "ensures")
    _check_spec(a.requires, "requires")
    v = t.prove(src, a.ensures, requires=a.requires, target=func, best_effort=a.best_effort)
    repro = t.repro_test(v, src, ensures=a.ensures, requires=a.requires, func=func) if a.repro else None
    return _report(v, src, json_out=a.json, quiet=a.quiet, repro=repro)


def _cmd_explain(a):
    src = _read(a.file)
    func = _resolve_target(src, _label(a.file), a.func)
    _check_spec(a.requires, "requires")
    if a.ensures is not None:
        _check_spec(a.ensures, "ensures")
        v = t.prove(src, a.ensures, requires=a.requires, target=func, best_effort=a.best_effort)
    else:
        v = t.check(src, requires=a.requires, total=a.total, target=func, best_effort=a.best_effort)
    return _report(t.explain(v, src), src, json_out=a.json, quiet=a.quiet)


def _cmd_repair(a):
    _check_spec(a.requires, "requires")
    if a.ensures is not None:
        _check_spec(a.ensures, "ensures")
    before = _read(a.before) if a.before else None

    def generate(feedback):                                  # the external generator: feedback in, candidate source out
        return subprocess.run(a.generator, shell=True, input=feedback or "",
                              capture_output=True, text=True).stdout

    res = t.repair_loop(generate, ensures=a.ensures, requires=a.requires, before=before,
                        func=a.func, max_rounds=a.rounds)
    if a.json:
        print(json.dumps({"status": res["status"], "rounds": res["rounds"],
                          "converged": res["converged"], "source": res.get("source")}))
    else:
        print("%s after %d round(s)%s" % (_paint(res["status"]), res["rounds"],
                                          "" if res["converged"] else " (not converged)"))
        if res.get("source"):
            print("# --- final candidate ---")
            print(res["source"], end="" if res["source"].endswith("\n") else "\n")
    return _EXIT.get(res["status"], 3)


def _cmd_equiv(a):
    if a.impl == "-" and a.spec == "-":
        _die("only one of IMPL or SPEC can be read from standard input")
    impl, spec = _read(a.impl), _read(a.spec)
    _require_func(impl, _label(a.impl), a.func)
    _require_func(spec, _label(a.spec), a.func)
    v = t.verify_equiv(a.func, a.func, impl, spec, {})
    repro = t.repro_test(v, impl, spec_src=spec, func=a.func) if a.repro else None
    return _report(v, impl, json_out=a.json, quiet=a.quiet, repro=repro)


def _cmd_change(a):
    if a.before == "-" and a.after == "-":
        _die("only one of BEFORE or AFTER can be read from standard input")
    before, after = _read(a.before), _read(a.after)
    v = t.verify_change(before, after, requires=a.requires, ensures=a.ensures, func=a.func)
    if a.bundle:
        b = t.change_bundle(before, after, requires=a.requires, ensures=a.ensures, func=a.func,
                            label="change %s" % _label(a.after))
        try:
            with open(a.bundle, "w", encoding="utf-8") as fh:
                json.dump(b, fh, indent=2)
        except OSError as e:
            _die("cannot write bundle %s: %s" % (a.bundle, e))
    return _report(v, after, json_out=a.json, quiet=a.quiet)


def _cmd_repo(a):
    from collections import Counter
    cache = {}
    if a.cache and os.path.exists(a.cache):
        try:
            with open(a.cache, encoding="utf-8") as fh:
                cache = json.load(fh)
        except (OSError, ValueError):
            cache = {}
    jobs = getattr(a, "jobs", 1) or 1
    if a.changed:
        rows = t.verify_diff(a.dir, [c for c in a.changed.split(",") if c], total=a.total, cache=cache, jobs=jobs)
    else:
        rows = t.verify_repo(a.dir, total=a.total, cache=cache, jobs=jobs)
    if a.cache:
        try:
            with open(a.cache, "w", encoding="utf-8") as fh:
                json.dump(cache, fh)
        except OSError:
            pass
    tally = Counter(s for _, s in rows)
    if a.json:
        print(json.dumps({"tally": dict(tally),
                          "functions": [{"name": n, "status": s} for n, s in rows]}))
    else:
        for n, s in rows:
            if not a.quiet or s == "REFUTED":
                print("%-8s %s" % (s, n))
        print("--- %d functions: %d PROVED, %d REFUTED, %d UNKNOWN ---" %
              (len(rows), tally.get("PROVED", 0), tally.get("REFUTED", 0), tally.get("UNKNOWN", 0)))
    return 1 if tally.get("REFUTED") else 0


_SCAN_TAG = {"bug": "BUG", "input-validation": "VALIDATION", "unconfirmed": "UNCONFIRMED",
             "suspected": "SUSPECTED", "context-unreachable": "UNCONFIRMED"}


def _cmd_scan(a):
    """Point at a repo URL, a .py file URL, or a local path and report the reachable traps, classified.
    Symbolic by default (the fetched code is never run); --execute replays each finding in the isolated
    sandbox to confirm the exception and split genuine bugs from intended input validation. Exit status is
    nonzero on a confirmed bug (or, symbolic-only, any reachable trap); --repro prints a runnable failing
    test for each confirmed finding."""
    try:
        rep = t.scan(a.target, execute=a.execute)
    except ValueError as e:
        _die(str(e))
    fail = bool(rep["bugs"] or rep.get("suspected")) if rep["executed"] else bool(rep["refuted"])
    if a.json:
        print(json.dumps(rep))
        return 1 if fail else 0
    where = "fetched" if rep["fetched"] else "local"
    mode = "executed in sandbox" if rep["executed"] else "symbolic, code not run"
    print("scan %s  [%s, %s]" % (rep["target"], where, mode))
    print("  %d functions: %d proved, %d refuted, %d unknown"
          % (rep["functions"], rep["proved"], rep["refuted"], rep["unknown"]))
    if rep["executed"]:
        print("  classified: %d bug(s), %d suspected, %d input-validation, %d unconfirmed"
              % (rep["bugs"], rep.get("suspected", 0), rep["input_validation"], rep["unconfirmed"]))
    for f in rep["findings"]:
        exc = "  [%s]" % f["exception"] if f["exception"] else ""
        print("  %s  %s%s" % (_paint(_SCAN_TAG.get(f["classification"], "REFUTED")), f["location"], exc))
        print("      %s" % f["label"])
        if f["counterexample"]:
            print("      counterexample: %s" % f["counterexample"])
        if a.repro and f["repro"]:
            print("      repro:")
            for line in f["repro"].splitlines():
                print("        %s" % line)
    if not rep["findings"]:
        tail = "" if rep["executed"] else "  (re-run with --execute to confirm with the sandbox)"
        print("  no reachable traps found" + tail)
    return 1 if fail else 0


def _has_func(src, name):
    try:
        return any(isinstance(n, ast.FunctionDef) and n.name == name for n in ast.parse(src).body)
    except SyntaxError:
        return False


def _cmd_gate(a):
    def git(*args):
        return subprocess.run(["git", "-C", a.dir, *args], capture_output=True, text=True)
    if a.changed:
        files = [c for c in a.changed.split(",") if c.endswith(".py")]
    else:
        r = git("diff", "--name-only", "--diff-filter=d", a.base)
        if r.returncode != 0:
            _die("git diff failed: %s" % r.stderr.strip())
        files = [l.strip() for l in r.stdout.splitlines() if l.strip().endswith(".py")]
    if not files:
        print("gate: no changed .py files")
        return 0
    refuted, bundles = [], []
    for f in files:
        try:
            with open(os.path.join(a.dir, f), encoding="utf-8") as fh:
                after = fh.read()
            ast.parse(after)
        except (OSError, SyntaxError):
            continue
        br = git("show", "%s:%s" % (a.base, f))
        before = br.stdout if br.returncode == 0 else None
        for n in ast.parse(after).body:
            if not isinstance(n, ast.FunctionDef):
                continue
            if before is not None and _has_func(before, n.name):
                v = t.verify_change(before, after, func=n.name)   # the change must preserve the function
                kind = "change"
            else:
                v = t.check(after, target=n.name, prop="trap freedom")   # a new function: trap freedom
                kind = "new"
            label = "%s::%s" % (f, n.name)
            print("%-8s %s (%s)" % (v.status, label, kind))
            if v.status == "REFUTED":
                refuted.append(label)
                if v.counterexample:
                    print("    counterexample: %s" % v.counterexample)
            elif a.bundle and v.status == "PROVED" and kind == "change":
                b = t.change_bundle(before, after, func=n.name, label=label)
                if b.get("checkable"):
                    bundles.append(b)
    if a.bundle and bundles:
        try:
            os.makedirs(a.bundle, exist_ok=True)
            with open(os.path.join(a.bundle, "proofs.json"), "w", encoding="utf-8") as fh:
                json.dump(bundles, fh)
        except OSError:
            pass
    print("--- gate: %d function(s) refuted, %d proof bundle(s) ---" % (len(refuted), len(bundles)))
    return 1 if refuted else 0


def _cmd_coverage(a):
    import time
    history = _load_json(a.history, [])
    cache = _load_json(a.cache, {})
    report = t.coverage(a.dir, history=history, cache=cache, jobs=getattr(a, "jobs", 1) or 1)
    report["time"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    if a.cache:
        _dump_json(a.cache, cache)
    if a.history:
        history.append(report)
        _dump_json(a.history, history)
    if a.json:
        print(json.dumps(report))
    else:
        print("coverage: %d/%d functions trap-free (%.1f%%) | %d refuted, %d unknown"
              % (report["proved"], report["total"], report["coverage"], report["refuted"], report["unknown"]))
        if "delta_coverage" in report:
            print("  since last run: %+.1f%% coverage, %+d proved, %d new refusal(s)"
                  % (report["delta_coverage"], report["delta_proved"], len(report.get("new_refusals", []))))
        for n in report.get("new_refusals", []):
            print("  NEW REFUSAL: %s" % n)
    return 1 if report.get("new_refusals") else 0


def _load_json(path, default):
    if path and os.path.exists(path):
        try:
            with open(path, encoding="utf-8") as fh:
                return json.load(fh)
        except (OSError, ValueError):
            pass
    return default


def _dump_json(path, obj):
    try:
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(obj, fh)
    except OSError:
        pass


def _cmd_spec(a):
    src = _read(a.file)
    _require_func(src, _label(a.file), a.func)
    spec = t.synthesize_spec(src, func=a.func)
    if a.json:
        print(json.dumps(spec))
    else:
        if spec["requires"] != "True":
            print('@require("%s")' % spec["requires"])
        for e in spec["ensures"]:
            print('@ensure("%s")' % e)
        if spec["requires"] == "True" and not spec["ensures"]:
            print("# no contract synthesized (outside the modeled subset, or no candidate proved)")
    return 0


def _cmd_infer(a):
    src = _read(a.file)
    _require_func(src, _label(a.file), a.func)
    if a.emit:                                                   # the TypeEvalPy emit-and-match surface
        from . import typeinfer
        # pass the file path (so imports of sibling modules in the same directory resolve) and qualified=True
        # (so an imported / stdlib type keeps the module-path spelling TypeEvalPy's matcher expects, e.g.
        # itertools.count, to_import.A) -- both materially raise the TypeEvalPy exact-match score.
        facts = typeinfer.emit_facts(src, path=a.file, qualified=True)
        if a.func is not None:
            facts = [f for f in facts if f.get("function") == a.func]
        print(json.dumps(facts))
        return 0
    result = t.infer_types(src, target=a.func)

    def lst(x):
        return sorted(x) if isinstance(x, (set, frozenset)) else x

    if a.json:
        out = {}
        for key, val in (result or {}).items():
            out[key] = {n: lst(val[n]) for n in val} if isinstance(val, dict) else lst(val)
        print(json.dumps(out))
        return 0

    def fmt(x):
        if isinstance(x, (set, frozenset)):
            return " | ".join(sorted(x)) if x else "unknown"
        return "unknown" if x is None else x
    if isinstance(result, dict):
        for key in sorted(result, key=str):
            val = result[key]
            if isinstance(val, dict):
                print("%s:" % key)
                for name in sorted(val):
                    print("  %s: %s" % (name, fmt(val[name])))
            else:
                print("%s: %s" % (key, fmt(val)))
    else:
        print(fmt(result))
    return 0


def _cmd_examples(a):
    from . import examples
    bad = examples.run()
    print("%d example(s) did not match" % bad if bad
          else "all %d examples discharged as expected" % len(examples.EXAMPLES))
    return 1 if bad else 0


def _cmd_selftest(a):
    t.run_self_tests()
    return 0


def _cmd_demo(a):
    t.demo()
    return 0


def _cmd_covers(a):
    print(t.capabilities(), end="")
    return 0


def _cmd_lsp(a):
    from .lsp import main as lsp_main
    return lsp_main()


def _cmd_mcp(a):
    from .mcp import main as mcp_main
    return mcp_main()


def _version():
    try:
        from importlib.metadata import version, PackageNotFoundError
        try:
            return version("touchstone-prover")
        except PackageNotFoundError:
            return "0+unknown"
    except Exception:
        return "0+unknown"


def build_parser():
    p = argparse.ArgumentParser(prog="touchstone", description="An SMT-based verifier for Python.",
                                epilog=_EPILOG, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--version", action="version", version="touchstone " + _version())
    verdict = argparse.ArgumentParser(add_help=False)            # shared by the verdict-returning verbs
    verdict.add_argument("--json", action="store_true", help="emit the verdict as one JSON object")
    verdict.add_argument("-q", "--quiet", action="store_true",
                         help="print only the verdict word; rely on the exit status")
    verdict.add_argument("--timeout", type=int, metavar="MS", default=None,
                         help="hard per-query wall-clock budget in milliseconds")
    verdict.add_argument("--budget", choices=("standard", "high", "max"), default="standard",
                         help="solver resource budget (the deterministic rlimit, scaled with the timeouts); "
                              "a higher budget decides more cases but costs more (default: standard)")
    verdict.add_argument("--repro", action="store_true",
                         help="on a refutation, also emit a runnable failing test that reproduces the counterexample")
    verdict.add_argument("--best-effort", action="store_true",
                         help="assume unmodeled calls / framework methods are well-behaved (lower-trust verdict)")
    sub = p.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("check", parents=[verdict],
                       help="prove a function is trap-free (and any asserts hold) for all inputs")
    c.add_argument("file")
    c.add_argument("--func", default=None, help="function to check (default: the one in the file)")
    c.add_argument("--requires", default="True",
                   help="an optional precondition (a Python expression over the parameters); trap freedom "
                        "need only hold for inputs meeting it (default: True)")
    c.add_argument("--total", action="store_true", help="require totality (termination and no traps)")
    c.set_defaults(fn=_cmd_check)

    v = sub.add_parser("verify", parents=[verdict],
                       help="verify the @require / @ensure contracts written in the file")
    v.add_argument("file")
    v.add_argument("--func", default=None, help="function to verify (default: the first)")
    v.set_defaults(fn=_cmd_verify)

    va = sub.add_parser("verify-all", parents=[verdict],
                        help="verify every @ensure function in a module; nonzero exit if any is refuted")
    va.add_argument("file")
    va.set_defaults(fn=_cmd_verify_all)

    pr = sub.add_parser("prove", parents=[verdict],
                        help="prove a postcondition over the parameters and `result`")
    pr.add_argument("file")
    pr.add_argument("--ensures", required=True, help="the postcondition, a Python expression")
    pr.add_argument("--requires", default="True", help="the precondition (default: True)")
    pr.add_argument("--func", default=None, help="function to prove about (default: the first)")
    pr.set_defaults(fn=_cmd_prove)

    eq = sub.add_parser("equiv", parents=[verdict], help="prove two implementations agree on every input")
    eq.add_argument("impl")
    eq.add_argument("spec")
    eq.add_argument("--func", required=True, help="the function name defined in both files")
    eq.set_defaults(fn=_cmd_equiv)

    ch = sub.add_parser("change", parents=[verdict],
                        help="verify a proposed change preserves the code's properties (gate an AI diff)")
    ch.add_argument("before")
    ch.add_argument("after")
    ch.add_argument("--func", default=None, help="the function defined in both files (default: the first)")
    ch.add_argument("--ensures", default=None,
                    help="a postcondition the change must preserve (default: the before version's @ensure, "
                         "else behavioral equivalence)")
    ch.add_argument("--requires", default=None,
                    help="a precondition for that property (default: the before version's @require, else True)")
    ch.add_argument("--bundle", default=None, metavar="FILE", help="write a re-checkable proof bundle to FILE")
    ch.set_defaults(fn=_cmd_change)

    rp = sub.add_parser("repo", parents=[verdict],
                        help="triage trap-freedom of every top-level function across a package directory")
    rp.add_argument("dir")
    rp.add_argument("--total", action="store_true", help="require totality (termination and no traps)")
    rp.add_argument("--cache", default=None, metavar="FILE",
                    help="reuse and update a content-addressed verdict cache so a re-run is incremental")
    rp.add_argument("--changed", default=None, metavar="PATHS",
                    help="comma-separated changed files (git diff --name-only); verify only those functions "
                         "and the callers that depend on them")
    rp.add_argument("--jobs", "-j", type=int, default=1, metavar="N",
                    help="triage across N worker processes (capped at the CPU count); the verdicts are identical "
                         "to a serial run")
    rp.set_defaults(fn=_cmd_repo)

    sc = sub.add_parser("scan",
                        help="point at an owner/repo slug, a GitHub/repo/file URL (or browser link), or a local path; report reachable traps")
    sc.add_argument("target", help="owner/repo, a GitHub repo/blob/tree URL or any github.com link (scheme optional), "
                                   "a .py/raw URL, or a local directory or .py file")
    sc.add_argument("--execute", action="store_true",
                    help="replay each finding in an isolated sandbox to confirm the exception and split genuine "
                         "bugs from intended input validation (default: symbolic only, code never run)")
    sc.add_argument("--repro", action="store_true", help="print a runnable failing test for each finding")
    sc.add_argument("--json", action="store_true", help="emit the full report as one JSON object")
    sc.set_defaults(fn=_cmd_scan)

    gt = sub.add_parser("gate", help="gate a diff: verify each changed function preserves its properties "
                                     "(an AI-diff / PR gate); nonzero exit if any refutes")
    gt.add_argument("dir", nargs="?", default=".", help="the repository root (default: .)")
    gt.add_argument("--base", default="HEAD~1", help="git ref to diff against (default: HEAD~1)")
    gt.add_argument("--changed", default=None, metavar="PATHS",
                    help="comma-separated changed files, instead of computing the git diff")
    gt.add_argument("--bundle", default=None, metavar="DIR",
                    help="write re-checkable proof bundles for the verified changes to DIR")
    gt.set_defaults(fn=_cmd_gate)

    cv = sub.add_parser("coverage",
                        help="verified-subset coverage of a package, tracked over time; nonzero exit on a new refusal")
    cv.add_argument("dir")
    cv.add_argument("--history", default=None, metavar="FILE",
                    help="JSON history to read the trend from and append this run to")
    cv.add_argument("--cache", default=None, metavar="FILE", help="content-addressed verdict cache (see repo)")
    cv.add_argument("--jobs", "-j", type=int, default=1, metavar="N",
                    help="triage across N worker processes (capped at the CPU count); verdicts unchanged")
    cv.add_argument("--json", action="store_true", help="emit the report as one JSON object")
    cv.set_defaults(fn=_cmd_coverage)

    sp = sub.add_parser("spec",
                        help="synthesize a contract (@require / @ensure) a function provably satisfies")
    sp.add_argument("file")
    sp.add_argument("--func", default=None, help="function to synthesize for (default: the first)")
    sp.add_argument("--json", action="store_true", help="emit {requires, ensures} as one JSON object")
    sp.set_defaults(fn=_cmd_spec)

    inf = sub.add_parser("infer", help="report sound over-approximate types of a return and its locals")
    inf.add_argument("file")
    inf.add_argument("--func", default=None, help="function to infer (default: the first)")
    inf.add_argument("--json", action="store_true", help="emit the inferred types as one JSON object")
    inf.add_argument("--emit", action="store_true", help="emit TypeEvalPy-style type facts as a JSON list")
    inf.set_defaults(fn=_cmd_infer)

    ex = sub.add_parser("explain", parents=[verdict],
                        help="check (or prove, with --ensures) and show the failing path and live values of a refutation")
    ex.add_argument("file")
    ex.add_argument("--ensures", default=None, help="a postcondition to prove (default: check trap freedom)")
    ex.add_argument("--requires", default="True", help="an optional precondition (default: True)")
    ex.add_argument("--func", default=None, help="function to explain (default: the one in the file)")
    ex.add_argument("--total", action="store_true", help="require totality (with no --ensures)")
    ex.set_defaults(fn=_cmd_explain)

    rep = sub.add_parser("repair",
                         help="verification-guided repair: re-run a generator command until the property holds")
    rep.add_argument("--generator", required=True, metavar="CMD",
                     help="a shell command that reads repair feedback on stdin and prints a candidate function source")
    rep.add_argument("--ensures", default=None, help="the postcondition to reach (default: trap freedom, or --before)")
    rep.add_argument("--requires", default="True", help="the precondition (default: True)")
    rep.add_argument("--before", default=None, metavar="FILE", help="a reference version whose behavior to preserve")
    rep.add_argument("--func", default=None, help="the function name")
    rep.add_argument("--rounds", type=int, default=5, help="maximum repair rounds (default: 5)")
    rep.add_argument("--json", action="store_true", help="emit the outcome as one JSON object")
    rep.set_defaults(fn=_cmd_repair)

    for name, fn, helptext in (("examples", _cmd_examples, "run the capability gallery"),
                               ("selftest", _cmd_selftest, "run the self-test suite"),
                               ("covers", _cmd_covers, "print what touchstone can prove and the modeled subset"),
                               ("lsp", _cmd_lsp, "run the language server (LSP over stdio) for editor integration"),
                               ("mcp", _cmd_mcp, "run the MCP server (verification tools over stdio) for an AI agent"),
                               ("demo", _cmd_demo, "the narrated demonstration")):
        s = sub.add_parser(name, help=helptext)
        s.set_defaults(fn=fn)
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)
    budget = getattr(args, "budget", "standard")
    if budget != "standard":                                     # scale the deterministic rlimit and the timeouts
        k = {"high": 8, "max": 64}[budget]
        c = t.core
        t.configure(solve_rlimit=c.SOLVE_RLIMIT * k, fp_solve_rlimit=c.FP_SOLVE_RLIMIT * k,
                    solve_timeout_ms=c.SOLVE_TIMEOUT_MS * k, fp_solve_timeout_ms=c.FP_SOLVE_TIMEOUT_MS * k,
                    chc_fast_ms=c.CHC_FAST_MS * k)
    ms = getattr(args, "timeout", None)
    if ms is not None:                                           # an explicit --timeout overrides the budget's
        if ms <= 0:                                              # wall-clock scaling (the rlimit stays raised)
            _die("--timeout must be a positive number of milliseconds")
        t.configure(solve_timeout_ms=ms, fp_solve_timeout_ms=ms)
    try:
        return args.fn(args)
    except SystemExit:
        raise                                                    # _die and argparse already reported
    except KeyboardInterrupt:
        print("interrupted", file=sys.stderr)
        return 130
    except Exception as e:                                       # a bug in a verb: a clean line, not a traceback
        _die("%s: %s" % (type(e).__name__, e))


if __name__ == "__main__":
    raise SystemExit(main())
