"""Emit-and-match evaluation for emit_facts (touchstone.inference): recall and precision.

TypeEvalPy directory: a tree of `*_gt.json` files beside their `.py` sources. Recall is the
fraction of ground-truth facts an emitted fact matches; precision the fraction of emitted facts
that match a ground-truth fact.

CPython cross-check: a fixed corpus exercises eleven pure-Python stdlib modules under sys.settrace
to capture each local and return value's runtime type, then scores emit_facts against it. The
corpus reaches only some locations, so recall and precision are over those.

    python -m touchstone.typeeval                          # CPython cross-check
    python -m touchstone.typeeval PATH/TO/micro-benchmark  # a TypeEvalPy directory

Provenance for the published figures, so each reproduces from this harness alone:
  - TypeEvalPy ground truth: github.com/secure-software-engineering/TypeEvalPy at commit 3719de1.
  - CPython cross-check reference: CPython 3.13.2. Both the reached-location count and the rates move
    with the standard library's version, so the figures are what this harness reports on a given
    Python rather than fixed scores.
"""
import ast
import glob
import importlib
import json
import os
import sys

from .inference import emit_facts

# the eleven pure-Python stdlib modules of the cross-check; force the Python (not C) bisect/datetime
_MODULES = ["fractions", "statistics", "csv", "colorsys", "posixpath", "textwrap",
            "random", "bisect", "datetime", "_pydecimal", "collections"]
# runtime type names that denote a callable, collapsed to one bucket (the schema does not distinguish them)
_CALLABLE = {"function", "builtin_function_or_method", "method", "method-wrapper", "wrapper_descriptor",
             "method_descriptor", "builtin_method", "classmethod_descriptor", "staticmethod", "lambda"}


def _nz(types):
    """Normalize a set of runtime type names: every callable kind to 'callable', None to 'NoneType'."""
    return frozenset(("callable" if t in _CALLABLE else ("NoneType" if t == "None" else t)) for t in types)


# --------------------------------------------------------------------------- #
# TypeEvalPy-format scoring: recall and precision over a directory of *_gt.json #
# --------------------------------------------------------------------------- #
def _fact_key(f):
    """The location/identity a fact is matched on: file basename, line, column, and the named slot."""
    name = f.get("variable") or f.get("parameter") or "<return>"
    return (os.path.basename(f.get("file", "")), f.get("line_number"), f.get("col_offset"),
            f.get("function"), name)


def _match(a, b):
    """Two facts match when they name the same slot at the same position with an equal type set. Type
    names are compared case-insensitively, as TypeEvalPy's own matcher does (its ground truth spells the
    none type 'Nonetype' where the runtime reports 'NoneType')."""
    return (_fact_key(a) == _fact_key(b)
            and frozenset(t.lower() for t in a.get("type", [])) == frozenset(t.lower() for t in b.get("type", [])))


def score_typeevalpy(bench_dir, search_paths=None):
    """Recall, precision, and F1 of emit_facts over a TypeEvalPy directory tree. Returns a dict. When
    `search_paths` is None the standard external-module root (a sibling micro-benchmark-excluded/
    typeevalpy_external_module) is auto-detected and put on the import path."""
    if search_paths is None:
        ext = os.path.join(os.path.dirname(os.path.abspath(bench_dir)),
                           "micro-benchmark-excluded", "typeevalpy_external_module")
        search_paths = [ext] if os.path.isdir(ext) else []
    gt_total = gt_hit = committed = emit_total = emit_hit = files = 0
    for gtf in sorted(glob.glob(os.path.join(bench_dir, "**", "*_gt.json"), recursive=True)):
        pyf = gtf[:-len("_gt.json")] + ".py"
        if not os.path.exists(pyf):
            continue
        try:
            gt = json.load(open(gtf, encoding="utf-8"))
            ef = emit_facts(open(pyf, encoding="utf-8").read(), path=pyf, qualified=True, search_paths=search_paths)
        except Exception:
            continue
        files += 1
        gt_total += len(gt)
        emit_total += len(ef)
        keyed = {}                                        # location/slot -> whether a non-empty fact was emitted there
        for e in ef:
            keyed[_fact_key(e)] = keyed.get(_fact_key(e), False) or bool(e.get("type"))
        committed += sum(1 for g in gt if keyed.get(_fact_key(g)))   # GT slot where the inference committed a type
        gt_hit += sum(1 for g in gt if any(_match(g, e) for e in ef))
        emit_hit += sum(1 for e in ef if any(_match(g, e) for g in gt))
    rec = 100.0 * gt_hit / gt_total if gt_total else 0.0
    prec = 100.0 * emit_hit / emit_total if emit_total else 0.0
    f1 = 2 * prec * rec / (prec + rec) if (prec + rec) else 0.0
    return {"files": files, "gt": gt_total, "emitted": emit_total, "matched_gt": gt_hit,
            "matched_emit": emit_hit, "recall": rec, "precision": prec, "f1": f1,
            "committed": committed, "commit_rate": 100.0 * committed / gt_total if gt_total else 0.0,
            "refusal_rate": 100.0 * (gt_total - committed) / gt_total if gt_total else 0.0,
            "accuracy_committed": 100.0 * gt_hit / committed if committed else 0.0}


# --------------------------------------------------------------------------- #
# CPython cross-check: trace a fixed corpus for runtime-type ground truth       #
# --------------------------------------------------------------------------- #
def _exercise():
    import fractions, statistics, csv, colorsys, posixpath, textwrap, random, bisect, datetime, _pydecimal, collections, io
    F = fractions.Fraction; D = _pydecimal.Decimal
    a = F(3, 4) + F(1, 6); b = F(2, 3) * F(3, 5); c = F(7, 2) - F(1, 3); d = F(5, 6) / F(2, 9); F(2, 4); F(-3, 9)
    a.limit_denominator(5); str(a); float(b); _ = a < b; _ = a == b; -a; abs(F(-1, 2)); a ** 2; F(1, 3) + 1
    for fn in (statistics.mean, statistics.median, statistics.median_low, statistics.median_high):
        fn([1, 2, 3, 4, 5]); fn([2.5, 3.5, 1.5])
    statistics.mode([1, 1, 2, 3]); statistics.variance([1, 2, 3, 4, 5]); statistics.stdev([2, 4, 6, 8])
    statistics.pvariance([1, 2, 3]); statistics.pstdev([1, 2, 3]); statistics.harmonic_mean([1, 2, 4])
    statistics.fmean([1, 2, 3, 4]); statistics.geometric_mean([1, 2, 4]); statistics.quantiles([1, 2, 3, 4, 5, 6, 7, 8])
    text = "a,b,c\n1,2,3\n4,5,6\n"
    list(csv.reader(io.StringIO(text))); list(csv.DictReader(io.StringIO(text)))
    o = io.StringIO(); w = csv.writer(o); w.writerow(["x", "y", "z"]); w.writerows([[1, 2, 3], [4, 5, 6]])
    dw = csv.DictWriter(io.StringIO(), fieldnames=["a", "b", "c"]); dw.writeheader(); dw.writerow({"a": 1, "b": 2, "c": 3})
    sn = csv.Sniffer(); sn.sniff(text); sn.has_header(text)
    for rgb in [(0.2, 0.4, 0.6), (0.9, 0.1, 0.3), (0.5, 0.5, 0.5)]:
        colorsys.rgb_to_hls(*rgb); colorsys.rgb_to_hsv(*rgb); colorsys.rgb_to_yiq(*rgb)
        colorsys.hls_to_rgb(*rgb); colorsys.hsv_to_rgb(*rgb); colorsys.yiq_to_rgb(*rgb)
    posixpath.join("a", "b", "c"); posixpath.split("/a/b/c"); posixpath.splitext("file.txt"); posixpath.basename("/a/b.py")
    posixpath.dirname("/a/b/c"); posixpath.normpath("a/./b/../c"); posixpath.isabs("/x"); posixpath.splitdrive("c:/x"); posixpath.commonprefix(["abc", "abd"])
    textwrap.wrap("the quick brown fox " * 4, 20); textwrap.fill("a " * 40, 25); textwrap.shorten("hello world foo bar baz", 12)
    textwrap.indent("x\ny\nz\n", "  "); textwrap.dedent("    a\n    b\n")
    r = random.Random(42)
    for _ in range(3):
        r.randint(1, 100); r.random(); r.choice([1, 2, 3, 4]); r.uniform(0, 1); r.randrange(10)
        r.gauss(0, 1); r.expovariate(1.0); r.betavariate(2, 3); s = [1, 2, 3, 4, 5]; r.shuffle(s); r.sample(range(20), 3)
    arr = [1, 3, 5, 7, 9]
    bisect.bisect_left(arr, 4); bisect.bisect_right(arr, 5); bisect.bisect(arr, 6)
    bisect.insort_left(arr, 4); bisect.insort_right(arr, 8); bisect.insort(arr, 2)
    dt = datetime.datetime(2024, 6, 18, 10, 30, 15); d0 = datetime.date(2024, 6, 18); t0 = datetime.time(10, 30); td = datetime.timedelta(days=5, hours=3)
    dt.year; dt.weekday(); dt.isoformat(); dt.date(); dt.time(); d0 + td; dt - td; dt - datetime.datetime(2024, 1, 1)
    d0.weekday(); d0.isoformat(); d0.toordinal(); datetime.date.fromordinal(739000); td.total_seconds(); td.days
    x = D("1.5") + D("2.25"); D("10") / D("3"); D("2").sqrt(); x * D("2"); _ = D("1.1") > D("1.0"); int(D("7")); float(D("3.14")); D("5").quantize(D("0.01"))
    cnt = collections.Counter("aabbbcccc"); cnt.most_common(2); cnt["a"]; list(cnt.elements())
    od = collections.OrderedDict([(1, "a"), (2, "b")]); od.move_to_end(1); list(od.keys())
    P = collections.namedtuple("P", ["x", "y"]); p = P(1, 2); p.x; p._asdict()
    dq = collections.deque([1, 2, 3]); dq.appendleft(0); dq.pop(); dq.rotate(1)
    cm = collections.ChainMap({1: 2}, {3: 4}); cm[1]; cm.maps
    dd = collections.defaultdict(int); dd["k"] += 1


def _trace_groundtruth(files):
    """Run the corpus under sys.settrace; return {(module, function, line, name): {runtime type names}}."""
    records, prev = {}, {}

    def norm(qn):
        return qn.replace(".<locals>", "")

    def tr(frame, event, arg):
        co = frame.f_code
        if co.co_filename not in files:
            return tr
        mod = files[co.co_filename]
        func = None if co.co_name == "<module>" else norm(co.co_qualname)
        fid = id(frame)
        if event == "call":
            prev.pop(fid, None)
            ln = frame.f_lineno
            for k, v in frame.f_locals.items():
                records.setdefault((mod, func, ln, k), set()).add(type(v).__name__)
            prev[fid] = (ln, dict(frame.f_locals))
        elif event == "line":
            if fid in prev:
                pl, ploc = prev[fid]
                for k, v in frame.f_locals.items():
                    if k not in ploc or ploc[k] is not v:
                        records.setdefault((mod, func, pl, k), set()).add(type(v).__name__)
            prev[fid] = (frame.f_lineno, dict(frame.f_locals))
        elif event == "return":
            rt = "generator" if (co.co_flags & 0x20) else type(arg).__name__
            records.setdefault((mod, func, "RET", "RET"), set()).add(rt)
            prev.pop(fid, None)
        return tr

    sys.settrace(tr)
    try:
        _exercise()
    except Exception as e:                                # a corpus call that raises is skipped, not fatal
        sys.settrace(None)
        print("  (corpus note: %s %s)" % (type(e).__name__, e), file=sys.stderr)
    finally:
        sys.settrace(None)
    return records


def _driver_for(mod, exercise_src):
    """The corpus body with `mod.attr` rewritten to bare `attr`, so emit_facts (which analyzes the module's
    own source) sees the calls as the module's functions rather than attribute accesses on the import."""
    class _Strip(ast.NodeTransformer):
        def visit_Attribute(self, n):
            self.generic_visit(n)
            if isinstance(n.value, ast.Name) and n.value.id == mod:
                return ast.copy_location(ast.Name(id=n.attr, ctx=n.ctx), n)
            return n
    body = [_Strip().visit(ast.parse(ast.unparse(st)).body[0]) for st in exercise_src.body]
    return ast.unparse(ast.Module(body=body, type_ignores=[]))


def _corpus_files():
    """The (trace co_filename -> module, module -> source, module -> path) maps for the cross-check, forcing
    the pure-Python bisect/datetime and resolving two file-identity quirks so every module is actually
    captured: a frozen stdlib module (posixpath on 3.13) executes under `<frozen name>` though its source is
    on disk, and datetime.py is a shim whose pure-Python classes live in _pydatetime.py -- the file the
    traced frames run in and the inference must analyze."""
    for c in ("_bisect", "_datetime"):                   # force the pure-Python implementations
        sys.modules[c] = None
    for m in ("bisect", "datetime"):
        sys.modules.pop(m, None)
    mods = {m: importlib.import_module(m) for m in _MODULES}
    files, srcs, paths = {}, {}, {}
    for m, mod in mods.items():
        f = getattr(mod, "__file__", None)
        if m == "datetime" and "_pydatetime" in sys.modules:
            f = getattr(sys.modules["_pydatetime"], "__file__", f)   # the shim's real pure-Python source
        if f and f.endswith(".py"):
            files[f] = m
            files["<frozen %s>" % m] = m                 # a frozen module's frames run under <frozen name>
            srcs[m] = open(f, encoding="utf-8").read()
            paths[m] = f
    return files, srcs, paths


def cpython_crosscheck():
    """Trace the corpus, run emit_facts over each module, and score recall (over observed locations) and
    precision (over emitted facts that land on an observed location). Returns a dict."""
    import inspect
    files, srcs, paths = _corpus_files()
    records = _trace_groundtruth(files)
    exfn = ast.parse(inspect.getsource(_exercise)).body[0]

    idx = {}                                             # module -> {(function, name): [(line, is_param, types)]}
    for m, src in srcs.items():
        try:
            # the real module path lets the analyzer resolve the module's imports as it would for a file on
            # disk (a sibling class, a modeled stdlib return); a directory-less path would undercount recall
            ef = emit_facts(src + "\n" + _driver_for(m, exfn), path=paths[m])
        except Exception:
            ef = []
        d = {}
        for e in ef:
            if "variable" in e:
                nm, ip = e["variable"], False
            elif "parameter" in e:
                nm, ip = e["parameter"], True
            else:
                nm, ip = "RET", False
            d.setdefault((e.get("function"), nm), []).append((e.get("line_number"), ip, _nz(set(e.get("type", [])))))
        idx[m] = d

    def at_loc(cands, line, var):
        return [t for (el, ip, t) in cands
                if var == "RET" or ip or (isinstance(el, int) and isinstance(line, int) and abs(el - line) <= 1)]

    obs_by_key = {}                                      # (mod, func, name) -> observed normalized type-sets
    for (mod, func, _line, var), R in records.items():
        Rn = _nz(R)
        if Rn:
            obs_by_key.setdefault((mod, func, var), []).append(Rn)

    gt_total = gt_hit = committed = emit_seen = emit_hit = 0
    permod = {m: [0, 0] for m in srcs}
    for (mod, func, line, var), R in records.items():
        if mod not in idx:
            continue
        Rn = _nz(R)
        if not Rn:
            continue
        gt_total += 1
        permod[mod][1] += 1
        cands = idx[mod].get((func, var), [])
        loc = at_loc(cands, line, var)
        if any(t for t in loc):                          # the inference committed a (non-empty) type here
            committed += 1
        if any(t == Rn for t in loc):
            gt_hit += 1
            permod[mod][0] += 1
    for m in srcs:                                       # precision over emitted facts at observed locations
        for (func, nm), cands in idx[m].items():
            obs_types = obs_by_key.get((m, func, nm))    # the runtime types seen for this slot, or None
            if not obs_types:                            # an emitted location the runtime never reached: not scored
                continue
            for (_el, _ip, t) in cands:
                emit_seen += 1
                if any(t == ot for ot in obs_types):
                    emit_hit += 1
    rec = 100.0 * gt_hit / gt_total if gt_total else 0.0
    prec = 100.0 * emit_hit / emit_seen if emit_seen else 0.0
    return {"recall_caught": gt_hit, "recall_total": gt_total, "recall": rec,
            "precision_matched": emit_hit, "precision_seen": emit_seen, "precision": prec,
            "committed": committed, "commit_rate": 100.0 * committed / gt_total if gt_total else 0.0,
            "refusal_rate": 100.0 * (gt_total - committed) / gt_total if gt_total else 0.0,
            "accuracy_committed": 100.0 * gt_hit / committed if committed else 0.0,
            "per_module": {m: (c, t) for m, (c, t) in permod.items()}}


# --------------------------------------------------------------------------- #
# Sound mode: commit rate and soundness of the over-approximating inference     #
# --------------------------------------------------------------------------- #
def _snz(types):
    """Normalize a type-name set for the sound-mode comparison: the callable family to one bucket, the none
    type to one spelling, everything case-folded -- applied to the inferred bound, the runtime types, and the
    ground truth alike, so the match is the case-insensitive one the heuristic matcher also uses."""
    if types is None:
        return None
    out = set()
    for t in types:
        if t in _CALLABLE or t in ("function", "callable"):
            out.add("callable")
        elif t in ("None", "NoneType"):
            out.add("nonetype")
        else:
            out.add(t.lower())
    return frozenset(out)


def _sound_for(src, func, cache):
    """(return-type bound, {local: bound}) the sound mode infers for function `func` in `src`, each a
    frozenset over the cross-check vocabulary or None (UNKNOWN). A method (inside a class) is not in
    soundinfer's top-level index and comes back None -- an honest abstention, not a wrong answer."""
    from . import inference as soundinfer
    if func in cache:
        return cache[func]
    simple = func.rsplit(".", 1)[-1] if func else None
    try:
        ret = _snz(soundinfer.infer_return_type(src, target=simple))
        loc = {k: _snz(v) for k, v in soundinfer.infer_local_types(src, target=simple).items()}
    except Exception:
        ret, loc = None, {}
    cache[func] = (ret, loc)
    return cache[func]


def _sound_tally(total, committed, sound, exact):
    return {"total": total, "committed": committed, "sound": sound, "exact": exact,
            "commit_rate": 100.0 * committed / total if total else 0.0,
            "soundness": 100.0 * sound / committed if committed else 0.0,
            "exact_rate": 100.0 * exact / committed if committed else 0.0}


def sound_crosscheck():
    """Commit rate and soundness of the sound mode (soundinfer) over the traced stdlib corpus: at how many
    observed return/local locations it gives a bound (commit rate), and of those how often the runtime type
    is contained in the bound (soundness; an over-approximation should be ~100%) or equals it exactly. The
    sound mode abstains on parameter-dependent values and on methods, which is honest rather than wrong."""
    files, srcs, _paths = _corpus_files()
    records = _trace_groundtruth(files)
    caches = {m: {} for m in srcs}
    total = committed = sound = exact = 0
    for (mod, func, line, var), R in records.items():
        if mod not in srcs:
            continue
        Rn = _snz(R)
        if not Rn:
            continue
        ret, loc = _sound_for(srcs[mod], func, caches[mod])
        inferred = ret if var == "RET" else loc.get(var)
        total += 1
        if inferred is not None:
            committed += 1
            sound += (Rn <= inferred)
            exact += (Rn == inferred)
    return _sound_tally(total, committed, sound, exact)


def score_sound_typeevalpy(bench_dir):
    """Commit rate, soundness, and exact rate of the sound mode over a TypeEvalPy directory: the inferred
    bound for each return and local is compared to the ground-truth type set (containment is soundness).
    Parameters and methods are abstentions (the sound mode bounds neither), so the commit rate is over the
    returns and locals of top-level functions."""
    total = committed = sound = exact = 0
    for gtf in sorted(glob.glob(os.path.join(bench_dir, "**", "*_gt.json"), recursive=True)):
        pyf = gtf[:-len("_gt.json")] + ".py"
        if not os.path.exists(pyf):
            continue
        try:
            gt = json.load(open(gtf, encoding="utf-8"))
            src = open(pyf, encoding="utf-8").read()
        except Exception:
            continue
        cache = {}
        for g in gt:
            gtset = _snz(set(g.get("type", [])))
            if not gtset:
                continue
            ret, loc = _sound_for(src, g.get("function"), cache)
            inferred = None if "parameter" in g else (loc.get(g["variable"]) if "variable" in g else ret)
            total += 1
            if inferred is not None:
                committed += 1
                sound += (gtset <= inferred)
                exact += (gtset == inferred)
    return _sound_tally(total, committed, sound, exact)


def _print_sound(rep, scope):
    print("sound mode (infer_types) over %s" % scope)
    print("  commit rate : %d/%d = %.1f%% (locations it gives a bound)" % (rep["committed"], rep["total"], rep["commit_rate"]))
    print("  soundness   : %d/%d = %.1f%% (runtime type contained in the bound)" % (rep["sound"], rep["committed"], rep["soundness"]))
    print("  exact       : %d/%d = %.1f%% (bound equals the observed type set)" % (rep["exact"], rep["committed"], rep["exact_rate"]))


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    sound = "--sound" in argv
    argv = [a for a in argv if a != "--sound"]
    if sound:
        if argv:
            _print_sound(score_sound_typeevalpy(argv[0]), argv[0])
        else:
            _print_sound(sound_crosscheck(), "%d stdlib modules (CPython cross-check)" % len(_MODULES))
        return 0
    if argv:
        rep = score_typeevalpy(argv[0])
        print("emit-and-match over %s (%d files)" % (argv[0], rep["files"]))
        print("  recall    : %d/%d = %.1f%%" % (rep["matched_gt"], rep["gt"], rep["recall"]))
        print("  precision : %d/%d = %.1f%%" % (rep["matched_emit"], rep["emitted"], rep["precision"]))
        print("  F1        : %.1f%%" % rep["f1"])
        print("  commit    : %d/%d = %.1f%% (refusal %.1f%%; accuracy where committed %.1f%%)" % (
            rep["committed"], rep["gt"], rep["commit_rate"], rep["refusal_rate"], rep["accuracy_committed"]))
        return 0
    rep = cpython_crosscheck()
    print("CPython cross-check (emit-and-match vs runtime types over %d stdlib modules)" % len(_MODULES))
    print("  recall    : %d/%d = %.1f%% (over observed locations)" % (rep["recall_caught"], rep["recall_total"], rep["recall"]))
    print("  precision : %d/%d = %.1f%% (emitted facts at observed locations)" % (rep["precision_matched"], rep["precision_seen"], rep["precision"]))
    print("  commit    : %d/%d = %.1f%% (refusal %.1f%%; accuracy where committed %.1f%%)" % (
        rep["committed"], rep["recall_total"], rep["commit_rate"], rep["refusal_rate"], rep["accuracy_committed"]))
    for m in sorted(rep["per_module"]):
        c, t = rep["per_module"][m]
        print("    %-12s %d/%d" % (m, c, t))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
