"""Head-to-head decided-fraction benchmark of Touchstone against external Python verifiers, so its reach is
externally comparable rather than self-reported. Each peer runs the same corpus of small functions, each with
a postcondition and a known answer (HOLDS / VIOLATED); a tool *decides* a problem when it returns a definite,
correct verdict (proved/confirmed for HOLDS, a counterexample for VIOLATED). CrossHair (a concolic falsifier)
is run through its CLI when installed; Nagini (a Viper/JVM deductive verifier) is run when its toolchain is
present, else reported unavailable. Run: ``python -m touchstone.peer_bench``."""
import re
import shutil
import subprocess
import sys

# (name, function source with a PEP-316 docstring contract, Touchstone `ensures`, `requires`, ground truth).
# The docstring `post:` (over __return__) is what CrossHair checks; Touchstone takes the parallel `result`
# postcondition, so both peers decide the same property from one source.
_CORPUS = [
    ("double", "def double(x: int) -> int:\n    '''\n    post: __return__ == 2 * x\n    '''\n    return x + x\n",
     "result == 2 * x", "True", "HOLDS"),
    ("off_by_one", "def off_by_one(x: int) -> int:\n    '''\n    post: __return__ == x\n    '''\n    return x + 1\n",
     "result == x", "True", "VIOLATED"),
    ("square_nn", "def square_nn(x: int) -> int:\n    '''\n    post: __return__ >= 0\n    '''\n    return x * x\n",
     "result >= 0", "True", "HOLDS"),
    ("abs_nn", "def abs_nn(x: int) -> int:\n    '''\n    post: __return__ >= 0\n    '''\n    return abs(x)\n",
     "result >= 0", "True", "HOLDS"),
    ("expand", "def expand(a: int, b: int) -> int:\n    '''\n    post: __return__ == a*a + 2*a*b + b*b\n    '''\n"
     "    return (a + b) * (a + b)\n", "result == a*a + 2*a*b + b*b", "True", "HOLDS"),
    ("clamp", "def clamp(x: int) -> int:\n    '''\n    post: 0 <= __return__ <= 100\n    '''\n"
     "    return max(0, min(100, x))\n", "result >= 0 and result <= 100", "True", "HOLDS"),
    ("counter", "def counter(n: int) -> int:\n    '''\n    pre: n >= 0\n    post: __return__ == n\n    '''\n"
     "    i = 0\n    while i < n:\n        i = i + 1\n    return i\n", "result == n", "n >= 0", "HOLDS"),
    ("gauss", "def gauss(n: int) -> int:\n    '''\n    pre: n >= 0\n    post: 2 * __return__ == n * (n - 1)\n    '''\n"
     "    s = 0\n    i = 0\n    while i < n:\n        s = s + i\n        i = i + 1\n    return s\n",
     "2 * result == n * (n - 1)", "n >= 0", "HOLDS"),
    ("counter_bad", "def counter_bad(n: int) -> int:\n    '''\n    pre: n >= 0\n    post: __return__ == n + 1\n    '''\n"
     "    i = 0\n    while i < n:\n        i = i + 1\n    return i\n", "result == n + 1", "n >= 0", "VIOLATED"),
    ("bitmask", "def bitmask(a: int) -> int:\n    '''\n    post: __return__ == a % 8\n    '''\n    return a & 7\n",
     "result == a % 8", "True", "HOLDS"),
    ("sign_bad", "def sign_bad(x: int) -> int:\n    '''\n    post: __return__ != 0\n    '''\n"
     "    if x > 0:\n        return 1\n    return 0\n", "result != 0", "True", "VIOLATED"),
    ("expand_bad", "def expand_bad(a: int, b: int) -> int:\n    '''\n    post: __return__ == a*a + b*b\n    '''\n"
     "    return (a + b) * (a + b)\n", "result == a*a + b*b", "True", "VIOLATED"),
]


def _touchstone_verdicts():
    """Touchstone's prove() verdict for each corpus problem: PROVED / REFUTED / UNKNOWN."""
    import touchstone
    out = {}
    for name, src, ens, req, _truth in _CORPUS:
        out[name] = touchstone.prove(src, ens, requires=req, target=name).status
    return out


def crosshair_available():
    """Whether the CrossHair CLI can be invoked in this environment."""
    try:
        import crosshair  # noqa: F401
        return True
    except Exception:
        return False


def _crosshair_verdicts(per_timeout=3.0, tmpdir=None):
    """CrossHair's verdict per problem -- CONFIRMED / REFUTED / CANNOT_CONFIRM -- by writing the corpus to one
    file and parsing `crosshair check --report_all` (an `info: Confirmed over all paths.` is a confirmation; an
    `error: ...` is a counterexample). Problems are matched to reported lines by source span."""
    import os
    import tempfile
    tmpdir = tmpdir or tempfile.mkdtemp(prefix="ts_peer_")
    path = os.path.join(tmpdir, "_peer_corpus.py")
    text, spans, line = "", {}, 1
    for name, src, *_ in _CORPUS:
        nlines = src.count("\n")
        spans[name] = (line, line + nlines)
        text += src + "\n"
        line += nlines + 1
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)
    res = subprocess.run([sys.executable, "-m", "crosshair", "check", "--report_all",
                          "--per_condition_timeout", str(per_timeout), path],
                         capture_output=True, text=True, timeout=600)
    verdict = {}
    for ln in (res.stdout + res.stderr).splitlines():
        m = re.search(r":(\d+):\s*(info|error):\s*(.*)", ln)
        if not m:
            continue
        lno, kind, msg = int(m.group(1)), m.group(2), m.group(3)
        for name, (lo, hi) in spans.items():
            if lo <= lno <= hi:
                if "Confirmed" in msg:
                    verdict[name] = "CONFIRMED"
                elif kind == "error":
                    verdict.setdefault(name, "REFUTED")
    return {name: verdict.get(name, "CANNOT_CONFIRM") for name, *_ in _CORPUS}


def _nagini_translate(name, src, ens, req):
    """Re-express a corpus function in Nagini's contract DSL: the same signature and body (the PEP-316
    docstring dropped), with `requires` / `ensures` as Requires(...) / Ensures(...) and `result` rewritten to
    Nagini's Result(). No loop invariant is added, so a loop verifies only if Nagini carries one itself -- the
    honest deductive-verifier comparison against Touchstone's invariant synthesis."""
    import ast
    import textwrap
    fn = ast.parse(textwrap.dedent(src)).body[0]
    body = fn.body
    if (body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        body = body[1:]                                       # drop the PEP-316 docstring
    ret = (" -> " + ast.unparse(fn.returns)) if fn.returns else ""
    lines = ["from nagini_contracts.contracts import *", "",
             "def %s(%s)%s:" % (name, ast.unparse(fn.args), ret)]
    if req and req.strip() != "True":
        lines.append("    Requires(%s)" % req)
    lines.append("    Ensures(%s)" % re.sub(r"\bresult\b", "Result()", ens))
    for st in body:
        for ln in ast.unparse(st).splitlines():
            lines.append("    " + ln)
    return "\n".join(lines) + "\n"


def _nagini_cmd():
    """The Nagini launcher: $TOUCHSTONE_NAGINI if set (Nagini usually lives in its own venv, since it pins an
    older Python and needs a JVM), else `nagini` on PATH. None when neither resolves."""
    import os
    return os.environ.get("TOUCHSTONE_NAGINI") or shutil.which("nagini")


def nagini_available():
    """Whether the Nagini deductive verifier (Viper/JVM) can be launched here -- a `nagini` on PATH, a
    $TOUCHSTONE_NAGINI launcher, or an importable nagini_translation."""
    if _nagini_cmd() is not None:
        return True
    try:
        import nagini_translation  # noqa: F401
        return True
    except Exception:
        return False


def _nagini_verdicts(per_timeout=120.0, tmpdir=None):
    """Nagini's verdict per problem -- VERIFIED (the contract is proved), FAILED (Nagini could not verify it),
    or CANNOT_CONFIRM (the launcher is absent or the backend errored) -- by writing each translated function to
    a file and parsing `nagini <file>` for `Verification successful` / `Verification failed`. $JAVA_HOME comes
    from $TOUCHSTONE_NAGINI_JAVA_HOME when set, so a portable JDK the Viper backend needs is found."""
    import os
    import tempfile
    exe = _nagini_cmd()
    if exe is None:
        return {name: "CANNOT_CONFIRM" for name, *_ in _CORPUS}
    env = dict(os.environ)
    jh = os.environ.get("TOUCHSTONE_NAGINI_JAVA_HOME")
    if jh:
        env["JAVA_HOME"] = jh
        env["PATH"] = os.path.join(jh, "bin") + os.pathsep + env.get("PATH", "")
    d = tmpdir or tempfile.mkdtemp(prefix="ts_nagini_")
    out = {}
    for name, src, ens, req, _truth in _CORPUS:
        path = os.path.join(d, name + ".py")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(_nagini_translate(name, src, ens, req))
        try:
            res = subprocess.run([exe, path], capture_output=True, text=True, timeout=per_timeout, env=env)
            text = res.stdout + res.stderr
        except Exception:
            out[name] = "CANNOT_CONFIRM"
            continue
        if "Verification successful" in text:
            out[name] = "VERIFIED"
        elif "Verification failed" in text:
            out[name] = "FAILED"
        else:
            out[name] = "CANNOT_CONFIRM"
    return out


def _nagini_tally(verdicts):
    """(#decided, #correct) for Nagini, a sound deductive verifier. It decides a problem when its verdict is
    the one the truth warrants: VERIFIED for a HOLDS contract, or a verification failure for a VIOLATED one (it
    will not verify a false contract). A failure on a HOLDS contract is incompleteness -- Nagini needs a manual
    loop invariant Touchstone synthesizes -- so it is counted undecided, not incorrect; decided equals correct
    because the verifier is sound."""
    dec = 0
    for name, _src, _ens, _req, truth in _CORPUS:
        v = verdicts.get(name)
        if (v == "VERIFIED" and truth == "HOLDS") or (v == "FAILED" and truth == "VIOLATED"):
            dec += 1
    return dec, dec


def _tally(verdicts, decided_states):
    """(#decided, #correct) over the corpus for a tool whose deciding states are `decided_states`
    (the confirming state first, the refuting state second). Correct = the decided verdict matches truth."""
    confirm, refute = decided_states
    dec = ok = 0
    for name, _src, _ens, _req, truth in _CORPUS:
        v = verdicts.get(name)
        if v == confirm:
            dec += 1
            ok += (truth == "HOLDS")
        elif v == refute:
            dec += 1
            ok += (truth == "VIOLATED")
    return dec, ok


def peer_benchmark(per_timeout=3.0):
    """Run the shared corpus through Touchstone and every available peer, returning per-tool tallies
    {tool: {available, decided, correct, total, verdicts}}. A peer not installed is reported unavailable."""
    total = len(_CORPUS)
    tsv = _touchstone_verdicts()
    ts_dec, ts_ok = _tally(tsv, ("PROVED", "REFUTED"))
    out = {"total": total,
           "touchstone": {"available": True, "decided": ts_dec, "correct": ts_ok, "total": total, "verdicts": tsv}}
    if crosshair_available():
        chv = _crosshair_verdicts(per_timeout)
        ch_dec, ch_ok = _tally(chv, ("CONFIRMED", "REFUTED"))
        out["crosshair"] = {"available": True, "decided": ch_dec, "correct": ch_ok, "total": total, "verdicts": chv}
    else:
        out["crosshair"] = {"available": False}
    if nagini_available():                                 # run when the Viper/JVM toolchain is present
        ngv = _nagini_verdicts()
        ng_dec, ng_ok = _nagini_tally(ngv)
        out["nagini"] = {"available": True, "decided": ng_dec, "correct": ng_ok, "total": total, "verdicts": ngv}
    else:
        out["nagini"] = {"available": False}
    return out


def main():
    rep = peer_benchmark()
    total = rep["total"]
    print("PEER BENCHMARK (decided = a definite, correct verdict over a shared %d-problem corpus)\n" % total)
    cols = [("touchstone", "Touchstone (prove)"), ("crosshair", "CrossHair (concolic)"), ("nagini", "Nagini (Viper)")]
    header = "%-13s %-9s" % ("problem", "truth")
    for key, label in cols:
        header += " | %-15s" % label.split(" ")[0]
    print(header)
    ch = rep["crosshair"].get("verdicts", {})
    ng = rep["nagini"].get("verdicts", {})
    for name, _src, _ens, _req, truth in _CORPUS:
        row = "%-13s %-9s" % (name, truth)
        row += " | %-15s" % rep["touchstone"]["verdicts"][name]
        row += " | %-15s" % (ch.get(name, "-") if rep["crosshair"]["available"] else "n/a")
        row += " | %-15s" % (ng.get(name, "-") if rep["nagini"]["available"] else "n/a")
        print(row)
    print()
    for key, label in cols:
        t = rep[key]
        if not t.get("available"):
            print("%-22s: unavailable (toolchain not installed)" % label)
        else:
            print("%-22s: decided %d/%d, correct %d/%d" % (label, t["decided"], total, t["correct"], t["decided"]))


if __name__ == "__main__":
    main()
