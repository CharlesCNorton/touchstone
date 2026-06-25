"""`import touchstone_prover` -- an alias matching the PyPI install name `touchstone-prover`, so the install
name and the import name converge. The canonical package is `touchstone`; every name forwards to it lazily
(so the solver is still imported only on first verification use)."""
import touchstone as _touchstone


def __getattr__(name):
    return getattr(_touchstone, name)


def __dir__():
    return dir(_touchstone)


__all__ = getattr(_touchstone, "__all__", [])
__version__ = getattr(_touchstone, "__version__", None)
