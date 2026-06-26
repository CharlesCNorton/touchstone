"""Touchstone: an SMT-based verifier for a subset of Python.

The full API is available from the top level; the same names are grouped into importable submodules (core,
domains, engines, theories, audit) for callers that want one layer in isolation.

The top level loads lazily: z3 is imported only on first access of a verification name (check, prove,
verify_*, the engines, the domains). `import touchstone` and the stdlib-only inference submodule (inference)
does not pull in the solver.
"""
import importlib

# Resolved from the stdlib-only inference module, so reaching these does not import the solver.
_LIGHT = {
    "infer_types": "inference",
    "infer_return_type": "inference",
    "infer_local_types": "inference",
}


def __getattr__(name):                                    # PEP 562: resolve a top-level name on first access
    mod = _LIGHT.get(name)
    if mod is not None:
        val = getattr(importlib.import_module("." + mod, __name__), name)
        globals()[name] = val
        return val
    if name.startswith("_") and name != "__all__":        # a private / dunder probe (incl. _impl itself) is not an
        raise AttributeError("module %r has no attribute %r" % (__name__, name))   # API name; never load the solver
    impl = importlib.import_module("._impl", __name__)     # import_module, not `from . import` -- the latter would
    if name == "__all__":                                 # re-enter this hook for _impl and recurse
        names = sorted(set(_LIGHT) | {n for n in dir(impl) if not n.startswith("_")})
        globals()["__all__"] = names
        return names
    try:
        val = getattr(impl, name)
    except AttributeError:
        raise AttributeError("module %r has no attribute %r" % (__name__, name)) from None
    globals()[name] = val
    return val


def __dir__():
    impl = importlib.import_module("._impl", __name__)
    return sorted(set(globals()) | set(_LIGHT) | {n for n in dir(impl) if not n.startswith("_")})
