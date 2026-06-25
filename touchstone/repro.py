"""Turn a REFUTED verdict into a runnable failing test.

The test binds the subject to the counterexample inputs and asserts the refuted property; running it
reproduces the violation (an AssertionError for a postcondition or equivalence mismatch, the trap itself for
a trap-freedom claim). The subject is emitted with its contract decorators stripped, so the test does not
import this package. Returns None when the verdict is not a refutation or carries no concrete inputs."""
import ast
import textwrap
from typing import Optional

# Stripped from the emitted subject so the test runs without importing this package.
_CONTRACT_DECOS = frozenset({"require", "requires", "ensure", "ensures", "pure", "total", "verify", "contract"})


def _deco_name(d):
    n = d.func if isinstance(d, ast.Call) else d
    if isinstance(n, ast.Attribute):
        return n.attr
    if isinstance(n, ast.Name):
        return n.id
    return None


def _clean_module(src, rename=None):
    """The module source with contract decorators stripped, optionally renaming one function."""
    tree = ast.parse(textwrap.dedent(src))
    for n in tree.body:
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            n.decorator_list = [d for d in n.decorator_list if _deco_name(d) not in _CONTRACT_DECOS]
            if rename and n.name == rename[0]:
                n.name = rename[1]
    return ast.unparse(tree).strip("\n")


def _signature(src, func):
    """(function name, positional parameter names) for `func` (or the first function) in src, or (None, None)."""
    for n in ast.parse(textwrap.dedent(src)).body:
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and (func is None or n.name == func):
            return n.name, [a.arg for a in n.args.posonlyargs + n.args.args]
    return None, None


def _call(name, params, inputs):
    return "%s(%s)" % (name, ", ".join("%s=%r" % (p, inputs[p]) for p in params))


def repro_test(verdict, src, *, ensures=None, requires=None, spec_src=None, func=None,
               name="test_touchstone_repro") -> Optional[str]:
    """A runnable failing test reproducing `verdict`'s counterexample, or None if there is none.

    With `spec_src` the test asserts the two implementations agree (equivalence); with `ensures` it asserts
    the postcondition over `result`; otherwise it calls the subject, reaching the refuted trap. A non-trivial
    `requires` is recorded as a comment."""
    if verdict.status != "REFUTED" or not verdict.counterexample_inputs:
        return None
    inputs = verdict.counterexample_inputs
    fname, params = _signature(src, func or verdict.target)
    if fname is None or any(p not in inputs for p in params):
        return None
    call = _call(fname, params, inputs)
    out = []
    if spec_src is not None:                                          # equivalence: the two disagree here
        spec_name = _signature(spec_src, func)[0]
        if spec_name is None:
            return None
        spec_rename = (spec_name, spec_name + "_spec") if spec_name == fname else None
        spec_call_name = spec_rename[1] if spec_rename else spec_name
        out.append(_clean_module(src))
        out.append("")
        out.append(_clean_module(spec_src, rename=spec_rename))
        out += ["", "", "def %s():" % name]
        if requires and requires.strip() not in ("", "True"):
            out.append("    # precondition: %s" % requires.strip())
        out.append("    assert %s == %s" % (call, _call(spec_call_name, params, inputs)))
    else:
        out.append(_clean_module(src))
        out += ["", "", "def %s():" % name]
        if requires and requires.strip() not in ("", "True"):
            out.append("    # precondition: %s" % requires.strip())
        if ensures is not None:                                       # postcondition: it fails on this input
            out.append("    result = %s" % call)
            out.append("    assert %s" % ensures.strip())
        else:                                                        # trap freedom: the call reaches the trap
            out.append("    %s   # touchstone: a reachable trap fires on this input" % call)
    return "\n".join(out) + "\n"


__all__ = ["repro_test"]
