"""Out-of-process subject runner for the differential CPython oracle.

Run as a standalone script (`python <this file>`), it reads one pickled job from stdin and writes the pickled
results to stdout, so the sandbox works in every launch mode (a file, `-m`, `-c`, the REPL), unlike the
multiprocessing-spawn path, which needs a re-importable `__main__`. The subject runs under a restricted
builtins namespace and, where the platform allows, hard memory / CPU / file-size limits. Launched as a script
rather than `-m`, so it does not import the package (and z3) at startup.
"""
import pickle
import sys
import textwrap

# The builtins the modeled subset may call; anything else (open, eval, __import__) is absent, so a subject
# that reaches for it fails in the child. Kept in sync with core._SANDBOX_BUILTINS.
_SANDBOX_BUILTINS = {
    "abs": abs, "min": min, "max": max, "len": len, "range": range, "enumerate": enumerate,
    "zip": zip, "sorted": sorted, "sum": sum, "map": map, "filter": filter, "all": all, "any": any,
    "int": int, "float": float, "bool": bool, "str": str, "list": list, "dict": dict, "set": set,
    "tuple": tuple, "frozenset": frozenset, "divmod": divmod, "pow": pow, "round": round,
    "reversed": reversed, "isinstance": isinstance, "issubclass": issubclass, "type": type,
    "ord": ord, "chr": chr, "object": object, "True": True, "False": False, "None": None,
}
# Every builtin exception, so a subject that raises or catches a named exception runs as written. Kept in
# sync with core._SANDBOX_BUILTINS.
import builtins as _builtins
_SANDBOX_BUILTINS.update({_n: getattr(_builtins, _n) for _n in dir(_builtins)
                          if isinstance(getattr(_builtins, _n), type) and issubclass(getattr(_builtins, _n), BaseException)})
_SANDBOX_BUILTINS["__build_class__"] = _builtins.__build_class__   # the `class` statement needs it; a class subject
_SANDBOX_BUILTINS["property"] = property                           # (and a method confirmed on a real instance) execs


def _apply_limits(mem_mb):
    try:
        import resource
        soft = mem_mb * 1024 * 1024
        for lim, val in [(resource.RLIMIT_AS, soft), (resource.RLIMIT_CPU, 5), (resource.RLIMIT_FSIZE, 0)]:
            try:
                resource.setrlimit(lim, (val, val))
            except (ValueError, OSError):
                pass
    except Exception:
        pass                                                     # Windows: rely on process isolation + timeout


def _run_trace(src, repo, fname, argvals, max_steps):
    """Run fname(*argvals) under a line tracer, recording (lineno, integer locals) at each step, and return
    ('returned'|'raised'|'diverged'|'setup_error', trace, detail). Mirrors core._sandbox_trace_worker."""
    import sys as _sys
    ns = {"__builtins__": dict(_SANDBOX_BUILTINS), "__name__": "__sandbox__"}   # __name__ so a class body resolves
    try:
        for s in repo.values():
            exec(textwrap.dedent(s), ns)
        exec(textwrap.dedent(src), ns)
        fn = ns[fname]
    except Exception:
        return ("setup_error", [], "")
    trace, steps = [], [0]

    class _Budget(Exception):
        pass

    def tracer(frame, event, arg):
        if event == "line" and frame.f_code.co_filename == "<string>":   # only the subject's own lines
            steps[0] += 1
            if steps[0] > max_steps:
                raise _Budget()
            loc = {k: v for k, v in frame.f_locals.items() if isinstance(v, int) and not isinstance(v, bool)}
            trace.append((frame.f_lineno, loc))
        return tracer

    old = _sys.gettrace(); _sys.settrace(tracer)
    try:
        r = fn(*argvals)
        return ("returned", trace, repr(r))
    except _Budget:
        return ("diverged", trace, "")
    except Exception as e:
        return ("raised", trace, type(e).__name__)
    finally:
        _sys.settrace(old)


def main():
    try:
        job = pickle.load(sys.stdin.buffer)
    except Exception:
        return
    mode = job.get("mode", "value")
    src, repo, fname = job["src"], job["repo"], job["fname"]
    mem_mb = job.get("mem_mb", 512)
    _apply_limits(mem_mb)
    if mode == "trace":                                          # the explain() execution-trace path
        out = _run_trace(src, repo, fname, job["argvals"], job.get("max_steps", 10000))
        try:
            pickle.dump(("trace", out), sys.stdout.buffer); sys.stdout.buffer.flush()
        except Exception:
            pass
        return
    inputs = job["inputs"]
    ns = {"__builtins__": dict(_SANDBOX_BUILTINS), "__name__": "__sandbox__"}   # __name__ so a class body resolves
    try:
        for s in repo.values():
            exec(textwrap.dedent(s), ns)
        exec(textwrap.dedent(src), ns)
        fn = ns[fname]
    except Exception:
        pickle.dump(("setup_error",), sys.stdout.buffer)
        return
    out = []
    for tup in inputs:
        try:
            r = fn(*tup)
            if mode == "typed":
                out.append(("ok",))
            else:
                out.append(("ok", r) if isinstance(r, int) and not isinstance(r, bool) else ("nonint",))
        except Exception as e:                                   # a raise is a trap, modeled separately
            out.append(("raise", type(e).__name__) if mode == "typed" else ("trap",))
    try:
        pickle.dump(("results", out), sys.stdout.buffer)
        sys.stdout.buffer.flush()
    except Exception:
        pass


if __name__ == "__main__":
    main()
