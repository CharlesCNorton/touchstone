"""Pytest plugin: verify @require / @ensure contracts as collected tests.

Set the `touchstone_files` ini option to the modules to check:

    [tool.pytest.ini_options]
    touchstone_files = ["src/bank.py", "src/*_contracts.py"]

Each @ensure function becomes a test: PROVED passes, REFUTED fails with the counterexample,
UNKNOWN skips. Registered via the pytest11 entry point.
"""
import ast
import fnmatch

import pytest

from . import _impl as t


def _ensure_functions(src):
    """Yield the name of each top-level function decorated with @ensure(...)."""
    for n in ast.parse(src).body:
        if not isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for d in n.decorator_list:
            f = d.func if isinstance(d, ast.Call) else d
            if isinstance(f, ast.Name) and f.id == "ensure":
                yield n.name
                break


def pytest_addoption(parser):
    parser.addini("touchstone_files", type="args", default=[],
                  help="glob(s) of files whose @require / @ensure contracts pytest should verify")


def pytest_collect_file(file_path, parent):
    globs = parent.config.getini("touchstone_files")
    if not globs or file_path.suffix != ".py":
        return None
    if any(fnmatch.fnmatch(file_path.as_posix(), g) or fnmatch.fnmatch(file_path.name, g) for g in globs):
        return _ContractFile.from_parent(parent, path=file_path)
    return None


class _Refuted(Exception):
    pass


class _ContractFile(pytest.File):
    def collect(self):
        src = self.path.read_text(encoding="utf-8")
        for name in _ensure_functions(src):
            yield _ContractItem.from_parent(self, name=name, src=src, func=name)


class _ContractItem(pytest.Item):
    def __init__(self, *, src, func, **kw):
        super().__init__(**kw)
        self._src, self._func = src, func

    def runtest(self):
        v = t.verify_contracts(self._src, target=self._func)
        if v.status == "PROVED":
            return
        if v.status == "UNKNOWN":
            pytest.skip(v.reason or "UNKNOWN")
        v = t.explain(v, self._src)
        cx = v.counterexample or (v.counterexample_inputs and ", ".join(
            "%s=%s" % kv for kv in sorted(v.counterexample_inputs.items()))) or "(none)"
        raise _Refuted("%s REFUTED: counterexample %s%s" % (self._func, cx, ("\n" + v.trace) if v.trace else ""))

    def repr_failure(self, excinfo):
        if isinstance(excinfo.value, _Refuted):
            return str(excinfo.value)
        return super().repr_failure(excinfo)

    def reportinfo(self):
        return self.path, 0, "contract: %s" % self._func
