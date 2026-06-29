"""Deductive and Constrained-Horn-Clause verifiers: loop-free equivalence and predicates,
single-loop Hoare/Houdini/Spacer, whole-function and interprocedural CHC, recursion, modular
contracts, arrays, termination and cost, bounded model checking, and the incremental orchestrator."""
import ast
import builtins as _builtins
import copy
import contextlib
import signal
import threading
import hashlib
import inspect
import os
import random
import sys
import textwrap
import math as _math
from fractions import Fraction as _Fr
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Tuple
import z3
from . import core
from .core import *


def _require_str(name, value):
    if not isinstance(value, str):
        raise TypeError("%s must be a str of Python source, got %s" % (name, type(value).__name__))


def _require_repo(repo):
    if repo is not None and not isinstance(repo, dict):
        raise TypeError("repo must be a dict of {name: source}, got %s" % type(repo).__name__)


def _escalate_budget(thunk):
    """Run a verdict thunk; on a budget-bound UNKNOWN (a resource limit, not an abstraction), retry once at an
    8x rlimit (capped, deterministic) before returning, so a decidable-but-starved query is not left UNKNOWN."""
    from .diagnostics import budget_helps
    v = thunk()
    if (v.status == UNKNOWN and not core._BUDGET_ESCALATING
            and core.SOLVE_RLIMIT * 8 <= core.BUDGET_ESCALATE_CAP and budget_helps(v.reason)):
        core._BUDGET_ESCALATING = True
        prior = core.configure(solve_rlimit=core.SOLVE_RLIMIT * 8, fp_solve_rlimit=core.FP_SOLVE_RLIMIT * 4,
                               chc_fast_ms=core.CHC_FAST_MS * 4)
        try:
            v2 = thunk()
        finally:
            core.configure(**prior); core._BUDGET_ESCALATING = False
        if v2.status != UNKNOWN:
            return v2
    return v


def _float_kinds(src):
    """Unannotated parameters inferred float (only the float kind), for symexec in the value channel; None if none."""
    try:
        from .domains import _infer_param_kinds
        k = _infer_param_kinds(_fndef(src))
    except Exception:
        return None
    kf = {n: "float" for n, v in k.items() if v == "float"}
    return kf or None


def _solve_horn(prop, target, technique, proved, relations, declvars, rules, query, *,
                on_error, proved_reason="", refuted_reason="", corroborate=True, timeout=4000, retry=1) -> Verdict:
    """The shared Spacer tail of the CHC engines: build a Fixedpoint over `relations` / `declvars` / `rules`,
    query `query`, and map unsat / sat / unknown to PROVED / REFUTED / UNKNOWN. `technique` labels REFUTED and
    both UNKNOWN verdicts, `proved` the PROVED one; `on_error(msg)` gives the reason on a Z3Exception, and
    `corroborate` gates the cvc5 invariant re-check (`proof_certificate`) on a PROVED."""
    fp = z3.Fixedpoint(); fp.set(engine="spacer"); fp.set("timeout", timeout)
    for rel in relations:
        fp.register_relation(rel)
    fp.declare_var(*declvars)
    for h, b in rules:
        fp.rule(h, b)
    try:
        r = core._fp_query(fp, query, retry=retry)
    except z3.Z3Exception as e:
        return Verdict(UNKNOWN, prop, target, technique, reason=on_error(str(e)))
    if r == z3.unsat:
        cert = core.proof_certificate() if (corroborate and core._corroborate_horn(fp, rules, query)) else None
        return Verdict(PROVED, prop, target, proved, reason=proved_reason, certificate=cert)
    if r == z3.sat:
        return Verdict(REFUTED, prop, target, technique, reason=refuted_reason)
    return Verdict(UNKNOWN, prop, target, technique, reason="engine returned unknown")


def verify_equiv(prop, target, impl_src, spec_src, repo) -> Verdict:
    """Two functions are equivalent iff they trap (divide by zero) on exactly the
    same inputs and return equal values everywhere neither traps."""
    _require_str("impl_src", impl_src); _require_str("spec_src", spec_src); _require_repo(repo)
    impl_src, spec_src = core._strip_async(impl_src), core._strip_async(spec_src)   # equate awaited results
    ctx = Ctx(repo); ctx.facts = []
    try:
        args, z3args, rets, itraps, inone = symexec(impl_src, ctx)
        if core.ALLOW_SUBJECT_EXECUTION:
            soundness_probe(impl_src, z3args, rets, args, repo)
        sargs, sz3, srets, straps, snone = symexec(spec_src, ctx)   # shared ctx: collect both sides' axioms
        if len(sargs) != len(args):
            return Verdict(UNKNOWN, prop, target, "symbolic+SMT", reason="impl/spec arity mismatch")
        subs = [(sz3[sf], z3args[af]) for sf, af in zip(sargs, args)]   # map by position
        impl_val, spec_val = fold(rets), _subst(fold(srets), subs)
        impl_trap, spec_trap = _trap_or(itraps), _trap_or(straps, subs)
        spec_none = z3.substitute(snone, *subs) if subs else snone
        # partial-function equivalence: same trap inputs, same None-return inputs, equal values elsewhere.
        # Incompatible return sorts make the value comparison fail to build; report UNKNOWN, not a sort error.
        claim_false = z3.Or(z3.Xor(impl_trap, spec_trap),
                            z3.Xor(inone, spec_none),
                            z3.And(z3.Not(impl_trap), z3.Not(spec_trap),
                                   z3.Not(inone), z3.Not(spec_none), _term_neq(impl_val, spec_val)))
    except Unsupported as u:
        pv = _loop_equiv_product(prop, target, impl_src, spec_src, repo)   # a for-loop the value engine declines
        return pv if pv is not None else Verdict(UNKNOWN, prop, target, "symbolic+SMT", reason=str(u))
    except (z3.Z3Exception, TypeError, AttributeError):
        return Verdict(UNKNOWN, prop, target, "symbolic+SMT",
                       reason="implementation and specification return incompatible value types")
    claim_false = _with_facts(ctx, claim_false)
    if core.REQUIRE_CORROBORATION and not ctx.overapprox:
        status, model, corr = solve_corroborated(claim_false)
    else:
        (status, model), corr = _solve(claim_false), None
    status, model = _downgrade_overapprox(status, model, ctx)
    cex = cex_in = None
    if status == REFUTED:
        model = minimize_witness(claim_false, z3args, args) or model
        cex, cex_in = _model_cex(model, z3args, args)
    cert = core.proof_certificate(corr) if status == PROVED and corr else None
    if status == UNKNOWN:                                     # a for-loop both sides abstain on (the value engine's
        pv = _loop_equiv_product(prop, target, impl_src, spec_src, repo)   # over-approximation is unsound for ==)
        if pv is not None:
            return pv
    return Verdict(status, prop, target, "symbolic+SMT (all inputs)",
                   counterexample=cex,
                   reason="" if status != UNKNOWN else (corr if corr == core._NL_UNCORROBORATED else "solver returned unknown"),
                   counterexample_inputs=cex_in, certificate=cert)


class _RenameNames(ast.NodeTransformer):
    """Rename every Name per a map, leaving unmapped names (builtins, free globals) alone."""
    def __init__(self, m): self.m = m
    def visit_Name(self, node):
        return ast.copy_location(ast.Name(id=self.m.get(node.id, node.id), ctx=node.ctx), node)


def _loop_fn_parts(src):
    """(fn, params, listparam, elem, init, loop, ret_expr) for a function shaped <init>; for <elem> in <listparam>:
    <body>; return <expr>, with one list-iterated parameter; None if it does not fit that shape."""
    try:
        fn = _fndef(src)
    except Exception:
        return None
    if fn.args.vararg or fn.args.kwarg or fn.args.kwonlyargs:
        return None
    params = [a.arg for a in fn.args.args]
    loops = [s for s in fn.body if isinstance(s, ast.For)]
    rets = [s for s in fn.body if isinstance(s, ast.Return)]
    init = [s for s in fn.body if not isinstance(s, (ast.For, ast.Return))]
    if len(loops) != 1 or len(rets) != 1 or rets[0].value is None or fn.body[-1] is not rets[0]:
        return None
    loop = loops[0]
    if loop.orelse or not (isinstance(loop.iter, ast.Name) and loop.iter.id in params
                           and isinstance(loop.target, ast.Name)):
        return None                                          # only `for elem in xs` over a parameter
    if any(isinstance(n, (ast.For, ast.While)) for s in loop.body for n in ast.walk(s)):
        return None                                          # a nested loop is outside the lockstep product
    return fn, params, loop.iter.id, loop.target.id, init, loop, rets[0].value


def _loop_equiv_product(prop, target, impl_src, spec_src, repo):
    """For-loop equivalence by a relational product: run both `for elem in xs` loops in lockstep over the same
    list, accumulating each side's variables (the spec's renamed apart), and prove the results agree at every
    input by the sequence-loop engine's single inductive invariant. None when either side is not a single
    for-loop over a shared parameter, or the merged proof is UNKNOWN."""
    if repo:
        return None
    ip, sp = _loop_fn_parts(impl_src), _loop_fn_parts(spec_src)
    if ip is None or sp is None:
        return None
    _ifn, iparams, ilist, ielem, iinit, iloop, iret = ip
    _sfn, sparams, slist, selem, sinit, sloop, sret = sp
    if len(iparams) != len(sparams) or iparams.index(ilist) != sparams.index(slist):
        return None                                          # the list parameter must align by position
    imap = {sparams[k]: iparams[k] for k in range(len(sparams))}   # unify spec's params (by position) to impl's
    imap[selem] = ielem                                      # and its loop element
    for nd in ast.walk(_sfn):                                # everything else spec assigns is renamed apart
        if isinstance(nd, ast.Name) and isinstance(nd.ctx, ast.Store) and nd.id not in imap:
            imap[nd.id] = "_s_" + nd.id
    rn = _RenameNames(imap)
    sinit2 = [rn.visit(copy.deepcopy(s)) for s in sinit]
    sbody2 = [rn.visit(copy.deepcopy(s)) for s in sloop.body]
    sret2 = rn.visit(copy.deepcopy(sret))
    margs = ast.arguments(posonlyargs=[], vararg=None, kwonlyargs=[], kw_defaults=[], kwarg=None, defaults=[],
                          args=[ast.arg(arg=p, annotation=ast.Name(id="list", ctx=ast.Load()) if p == ilist else None)
                                for p in iparams])
    merged_loop = ast.For(target=ast.Name(id=ielem, ctx=ast.Store()), iter=ast.Name(id=ilist, ctx=ast.Load()),
                          body=[copy.deepcopy(s) for s in iloop.body] + sbody2, orelse=[])
    diff = ast.BinOp(left=copy.deepcopy(iret), op=ast.Sub(), right=sret2)
    body = [copy.deepcopy(s) for s in iinit] + sinit2 + [merged_loop, ast.Return(value=diff)]
    mod = ast.Module(body=[ast.FunctionDef(name="_eq", args=margs, body=body, decorator_list=[], returns=None)],
                     type_ignores=[])
    ast.fix_missing_locations(mod)
    v = prove(ast.unparse(mod), "result == 0", target="_eq")   # both results agree iff their difference is 0
    if v.status == PROVED:
        return Verdict(PROVED, prop, target, "for-loop equivalence (relational product, inductive invariant)")
    if v.status == REFUTED:
        return Verdict(REFUTED, prop, target, "for-loop equivalence (relational product)",
                       counterexample=v.counterexample, counterexample_inputs=v.counterexample_inputs)
    return None


def verify_predicate(prop, target, impl_src, predicate, repo) -> Verdict:
    """predicate(z3args, out_value) -> Z3 Bool that must hold for ALL inputs. A
    reachable division by zero is itself a violation (the function is not total)."""
    impl_src = core._strip_async(impl_src)               # a property over the coroutine's awaited result
    ctx = Ctx(repo); ctx.facts = []
    try:
        args, z3args, rets, itraps, inone = symexec(impl_src, ctx, param_kinds=_float_kinds(impl_src))
        if core.ALLOW_SUBJECT_EXECUTION:
            soundness_probe(impl_src, z3args, rets, args, repo)
        out = fold(rets)
        impl_trap = _trap_or(itraps)
        post_pred = predicate(z3args, out)               # the spec may not typecheck against `out`
        claim = z3.Not(post_pred)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "symbolic+SMT", reason=str(u))
    except (z3.Z3Exception, TypeError, AttributeError):
        return Verdict(UNKNOWN, prop, target, "symbolic+SMT",
                       reason="specification does not apply to the returned value's type")
    # a trap or a None return is itself a violation of an integer predicate
    claim_false = _with_facts(ctx, z3.Or(impl_trap, inone, claim))
    if core.REQUIRE_CORROBORATION and not ctx.overapprox:
        status, model, corr = solve_corroborated(claim_false)
    else:
        (status, model), corr = _solve(claim_false), None
    status, model = _downgrade_overapprox(status, model, ctx)
    cex = cex_in = None
    if status == REFUTED:
        clean = _with_facts(ctx, z3.And(z3.Not(impl_trap), z3.Not(inone), claim))   # a non-trapping violation,
        cst, cm = _solve(clean)                                                     # preferred when one exists
        if cst == REFUTED:
            model = minimize_witness(clean, z3args, args) or cm or model
        else:
            model = minimize_witness(claim_false, z3args, args) or model
        cex, cex_in = _model_cex(model, z3args, args)
    elif status == UNKNOWN and ctx.overapprox:                       # sample real sin/cos/exp/log for a witness
        w = _refute_overapprox(args, z3args, z3.BoolVal(True), post_pred)
        if w is not None:
            status, cex, cex_in = REFUTED, ", ".join(f"{a}={w[a]}" for a in args), w
    cert = core.proof_certificate(corr) if status == PROVED and corr else None
    why = "" if status != UNKNOWN else (
        corr if corr == core._NL_UNCORROBORATED else
        ("an over-approximated term yields no certified verdict" if ctx.overapprox else "solver returned unknown"))
    return Verdict(status, prop, target, "symbolic+SMT (all inputs)",
                   counterexample=cex, counterexample_inputs=cex_in, certificate=cert, reason=why)


def _with_facts(ctx, claim_false):
    """Conjoin the over-approximation axioms (about uninterpreted transcendental functions) into the
    refutation query. They are true facts, so a still-unsatisfiable query is a sound PROVED."""
    return z3.And(*ctx.facts, claim_false) if getattr(ctx, "facts", None) else claim_false


def _downgrade_overapprox(status, model, ctx):
    """When a transcendental over-approximation was used, a satisfiable query is not a certified
    counterexample (the axioms do not pin the function's value), so REFUTED becomes UNKNOWN. PROVED
    stands: it holds for every value the axioms admit, which includes the real one."""
    if status == REFUTED and getattr(ctx, "overapprox", False):
        return UNKNOWN, None
    return status, model


def _isolate_target(src, fns, target):
    """When `src` defines more than one function, return just the target function's source (with the
    module's globals inlined into it), so a verb verifies the named function alone instead of the first one
    in the file. A single-function module, or a target absent from the definitions, is returned unchanged;
    a call into a sibling stays unresolved unless the caller also supplies it through `repo`."""
    if len(fns) <= 1 or not any(getattr(f, "name", None) == target for f in fns):
        return src
    try:
        return load_module(src)[target]
    except Exception:
        return src


def _wrapper_of(dec_fn):
    """(param_name, wrapper_args, wrapper_body) for a one-parameter decorator whose body is exactly a single
    nested def then `return <that def>`, or a single `return <lambda>` -- the wrapper a decorator applies. None
    for any other shape (extra statements would capture locals the inlining drops)."""
    if len(dec_fn.args.args) != 1 or dec_fn.args.vararg or dec_fn.args.kwarg or dec_fn.args.kwonlyargs:
        return None
    p, body = dec_fn.args.args[0].arg, dec_fn.body
    if (len(body) == 2 and isinstance(body[0], ast.FunctionDef)
            and isinstance(body[1], ast.Return) and isinstance(body[1].value, ast.Name)
            and body[1].value.id == body[0].name and not body[0].decorator_list):
        return p, body[0].args, list(body[0].body)           # def wrapper(...): <body> ; return wrapper
    if len(body) == 1 and isinstance(body[0], ast.Return) and isinstance(body[0].value, ast.Lambda):
        lam = body[0].value
        return p, lam.args, [ast.Return(value=lam.body)]     # return lambda ...: <expr>
    return None


def _is_staticmethod(fn):
    """Whether a method carries @staticmethod, so it takes no receiver -- the form an attribute factory
    `@C.m(args)` can bind positionally (a regular / class method's first parameter is self / cls, which the
    class-attribute call cannot supply, so such a factory is declined rather than mis-bound)."""
    return any(isinstance(d, ast.Name) and d.id == "staticmethod" for d in getattr(fn, "decorator_list", []))


def _subst_names(node, subst):
    """Substitute each loaded Name whose id is in `subst` (id -> replacement AST) throughout `node`, returning
    the node. Used to bind a factory decorator's parameters to its call arguments inside the wrapper body."""
    class _S(ast.NodeTransformer):
        def visit_Name(self, n):
            if isinstance(n.ctx, ast.Load) and n.id in subst:
                return ast.copy_location(ast.fix_missing_locations(subst[n.id]), n)
            return n
    return _S().visit(node)


def _factory_wrapper(make_fn, dec_call):
    """A factory decorator @D(args): D is `def D(cfg...): def deco(f): <wrapper>; return deco`. Bind D's
    parameters to the call's arguments, substitute them into the produced decorator's wrapper, and return that
    wrapper's (param, args, body) -- exactly as _wrapper_of returns for a plain decorator. None for any other
    factory shape, a *args / **kwargs / keyword-only factory, an argument the binding cannot carry, or a
    factory parameter that collides with or is rebound inside the wrapper (where substitution is unfaithful)."""
    if make_fn.args.vararg or make_fn.args.kwarg or make_fn.args.kwonlyargs:
        return None
    body = make_fn.body
    if not (len(body) == 2 and isinstance(body[0], ast.FunctionDef)
            and isinstance(body[1], ast.Return) and isinstance(body[1].value, ast.Name)
            and body[1].value.id == body[0].name):
        return None
    wr = _wrapper_of(body[0])                                 # the produced decorator must be a simple wrapper
    if wr is None:
        return None
    p, wargs, wbody = wr
    params = [a.arg for a in make_fn.args.args]
    defaults = make_fn.args.defaults
    if len(dec_call.args) > len(params):
        return None
    bound = {}
    for name, val in zip(params, dec_call.args):
        bound[name] = val
    for kw in dec_call.keywords:
        if kw.arg is None or kw.arg not in params:
            return None                                      # **kwargs splat or an unknown keyword
        bound[kw.arg] = kw.value
    for idx, name in enumerate(params):
        if name not in bound:
            di = idx - (len(params) - len(defaults))
            if di < 0:
                return None                                  # a required factory parameter with no argument
            bound[name] = defaults[di]
    shadow = {p} | {a.arg for a in wargs.args} | {a.arg for a in wargs.kwonlyargs}
    if shadow & set(bound):
        return None                                          # a factory parameter shadowed by a wrapper parameter
    if any(isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store) and n.id in bound
           for s in wbody for n in ast.walk(s)):
        return None                                          # a factory parameter rebound inside the wrapper
    return p, wargs, [_subst_names(s, bound) for s in wbody]


def _rewrite_calls(stmts, fromname, toname):
    """Rewrite every call `fromname(...)` to `toname(...)` in a statement list. Returns the rewritten list, or
    None if `fromname` appears as anything other than a call target (a bare reference the rewrite cannot carry,
    so the inlining is declined rather than left unfaithful)."""
    ok = [True]

    class _R(ast.NodeTransformer):
        def visit_Call(self, n):
            if isinstance(n.func, ast.Name) and n.func.id == fromname:
                args = [self.visit(a) for a in n.args]
                kw = [ast.keyword(arg=k.arg, value=self.visit(k.value)) for k in n.keywords]
                return ast.copy_location(ast.Call(func=ast.Name(id=toname, ctx=ast.Load()), args=args, keywords=kw), n)
            self.generic_visit(n)
            return n

        def visit_Name(self, n):
            if n.id == fromname:
                ok[0] = False                                # a use of the decorated function other than calling it
            return n

    out = [_R().visit(s) for s in stmts]
    return out if ok[0] else None


def _inline_decorators(src, target, repo):
    """When `target` carries non-identity decorators that resolve to visible simple wrappers, return
    (effective_source, augmented_repo): the function the decorators actually produce, with the original inlined
    as a repo helper the wrapper calls. A decorator resolves as a bare name (in `src` or `repo`), an `@D(args)`
    factory, `@C.m` where C is a local class and m a one-parameter wrapper method (its sole parameter -- self or
    a static f -- is the decorated function), an `@C.m(args)` attribute factory where m is a staticmethod factory
    method, or an `@m.deco` / `@m.deco(args)` module attribute whose name `deco` is a wrapper / factory supplied
    in `repo`. Decorators apply innermost-first. None when a decorator is an invisible name (no visible wrapper),
    a non-static attribute factory, or not a simple wrapper, so the engine declines (UNKNOWN)."""
    try:
        mod = _parse(src)
    except Exception:
        return None
    tfn = next((n for n in mod.body if isinstance(n, ast.FunctionDef) and n.name == target), None)
    if tfn is None or not tfn.decorator_list:
        return None
    decsrc = {n.name: ast.unparse(n) for n in mod.body if isinstance(n, ast.FunctionDef)}
    decsrc.update(repo or {})
    classes = {n.name: n for n in mod.body if isinstance(n, ast.ClassDef)}

    def _method_of(attrnode):                                # @C.m -> local class C's method m (a FunctionDef),
        if isinstance(attrnode, ast.Attribute) and isinstance(attrnode.value, ast.Name):   # or None
            cls = classes.get(attrnode.value.id)
            if cls is not None:
                return next((s for s in cls.body if isinstance(s, ast.FunctionDef) and s.name == attrnode.attr), None)
        return None

    def _attr_decorator(attrnode):                           # resolve an attribute decorator to its FunctionDef:
        m = _method_of(attrnode)                             # @C.m -> the local class method, else
        if m is not None:                                    # @m.deco -> a module function named `deco` supplied in
            return m                                         # decsrc/repo (m is an imported module, not a local class)
        if (isinstance(attrnode, ast.Attribute) and isinstance(attrnode.value, ast.Name)
                and classes.get(attrnode.value.id) is None and attrnode.attr in decsrc):
            try:
                return next((n for n in _parse(decsrc[attrnode.attr]).body if isinstance(n, ast.FunctionDef)), None)
            except Exception:
                return None
        return None

    undec = ast.FunctionDef(name=target, args=tfn.args, body=tfn.body, decorator_list=[], returns=tfn.returns)
    ast.fix_missing_locations(ast.copy_location(undec, tfn))
    aug = dict(repo or {})
    inner = "_undec_" + target
    aug[inner] = ast.unparse(undec)
    n_decos = len(tfn.decorator_list)
    eff_src = None
    for i, dec in enumerate(reversed(tfn.decorator_list)):    # innermost-first
        call = None
        if isinstance(dec, ast.Name) and dec.id in decsrc:
            try:
                dfn = next(n for n in _parse(decsrc[dec.id]).body if isinstance(n, ast.FunctionDef))
            except Exception:
                return None
        elif isinstance(dec, ast.Call) and isinstance(dec.func, ast.Name) and dec.func.id in decsrc:
            call = dec                                        # @D(args): a factory decorator
            try:
                dfn = next(n for n in _parse(decsrc[dec.func.id]).body if isinstance(n, ast.FunctionDef))
            except Exception:
                return None
        elif isinstance(dec, ast.Call) and isinstance(dec.func, ast.Attribute):   # @C.m(args) / @m.deco(args): an
            call = dec                                        # attribute factory -- a staticmethod factory on a local
            dfn = _attr_decorator(dec.func)                   # class, or a module function supplied in the repo
            if dfn is None or (_method_of(dec.func) is not None and not _is_staticmethod(dfn)):
                return None                                   # a non-static class-method factory cannot bind its self/cls
        elif isinstance(dec, ast.Attribute):                 # @C.m: a local class's method, or @m.deco: a module
            dfn = _attr_decorator(dec)                        # function supplied in the repo (sole param = decorated fn)
            if dfn is None:
                return None
        else:
            return None                                       # an invisible name: declined
        wr = _factory_wrapper(dfn, call) if call is not None else _wrapper_of(dfn)
        if wr is None:
            return None
        p, wargs, wbody = wr
        newbody = _rewrite_calls(wbody, p, inner)
        if newbody is None:
            return None
        last = (i == n_decos - 1)
        newname = target if last else "_dec%d_%s" % (i, target)
        newfn = ast.FunctionDef(name=newname, args=wargs, body=newbody, decorator_list=[], returns=None)
        ast.fix_missing_locations(ast.copy_location(newfn, tfn))
        if last:
            eff_src = ast.unparse(newfn)
        else:
            aug[newname] = ast.unparse(newfn)
            inner = newname
    return (eff_src, aug) if eff_src is not None else None


def _has_unmodeled_decorator(fn, modfns):
    """Whether `fn` carries a decorator that is neither an identity decorator (returns its argument unchanged,
    so the body is verified as-is) nor one the engine inlined -- such a decorator may replace the function with
    a different callable, so verifying the written body would be unsound and the engine must decline."""
    def ident(dec):
        if not isinstance(dec, ast.Name):
            return False
        d = modfns.get(dec.id)
        return (d is not None and len(d.args.args) == 1 and len(d.body) == 1
                and isinstance(d.body[0], ast.Return) and isinstance(d.body[0].value, ast.Name)
                and d.body[0].value.id == d.args.args[0].arg)
    return any(not ident(d) and not core._is_passthrough_decorator(d) for d in fn.decorator_list)


def _all_int_params(src):
    """Every parameter is integer-typed (unannotated or annotated `int`), so the fixed-width overflow
    companion applies; a float / str / container parameter is not an integer proof and is left alone."""
    try:
        fn = _fndef(src)
    except Unsupported:
        return False
    return all(a.annotation is None or (isinstance(a.annotation, ast.Name) and a.annotation.id == "int")
               for a in fn.args.args)


class _StripOld(ast.NodeTransformer):
    """Rewrite old(e) to e in a specification: in the functional value model a parameter named in the
    postcondition already denotes its value at function entry, so old(e) (the pre-state value) equals e.
    This lets a contract use the conventional old(...) without it reading as an unmodeled call."""
    def visit_Call(self, node):
        self.generic_visit(node)
        if (isinstance(node.func, ast.Name) and node.func.id == "old"
                and len(node.args) == 1 and not node.keywords):
            return node.args[0]
        return node


def _strip_old(node):
    return ast.fix_missing_locations(_StripOld().visit(node))


def _label_best_effort(v, assumed=True):
    """Tag a best-effort PROVED lower-trust (drop certificate) only when an assumption was actually used."""
    if not assumed or v.status != PROVED:
        return v
    v.certificate = None
    note = "best-effort (unmodeled calls/methods assumed well-behaved)"
    v.reason = (v.reason + "; " + note) if v.reason else note
    v.technique += " [best-effort]"
    return v


def _init_attrs(classes, cname):
    """(init_param_names, {attribute: value_expr}) for instances of `cname` whose attributes are statically a
    constant or an expression over __init__'s parameters: the class-level constant assignments along the MRO,
    plus a __init__ (no *args / **kwargs / keyword-only / defaults) whose body is only `self.attr = <expr>`
    (and pass), each value referencing only the init parameters and constants -- no self read, no call, no
    branch. Each attribute is then the call argument it is bound from, so an arg-taking constructor is pinned
    (o = C(v) gives _obj_o_count = v). None when __init__ does anything else."""
    attrs = {}
    for c in reversed(core._class_mro(classes, cname)):          # base-first, a derived class's value wins
        cnode = classes.get(c)
        if cnode is None:
            continue
        for st in cnode.body:
            if (isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name)
                    and isinstance(st.value, ast.Constant)):
                attrs[st.targets[0].id] = st.value
            elif (isinstance(st, ast.AnnAssign) and isinstance(st.target, ast.Name)
                  and isinstance(st.value, ast.Constant)):
                attrs[st.target.id] = st.value
    init = core._find_method(classes, cname, "__init__")
    initparams = []
    if init is not None:
        if (not init.args.args or init.args.vararg or init.args.kwarg or init.args.kwonlyargs
                or init.args.defaults):
            return None                                          # variadic / defaulted __init__: not pinnable
        selfn = init.args.args[0].arg
        initparams = [a.arg for a in init.args.args[1:]]
        allowed = set(initparams)
        for st in init.body:
            if isinstance(st, ast.Pass):
                continue
            if not (isinstance(st, ast.Assign) and len(st.targets) == 1
                    and isinstance(st.targets[0], ast.Attribute)
                    and isinstance(st.targets[0].value, ast.Name) and st.targets[0].value.id == selfn):
                return None                                      # not `self.attr = ...`: not modelable
            names = {n.id for n in ast.walk(st.value) if isinstance(n, ast.Name)}
            if not names <= allowed or any(isinstance(n, ast.Call) for n in ast.walk(st.value)):
                return None                                      # reads self / a free name, or calls: not a pure binding
            attrs[st.targets[0].attr] = st.value
    return initparams, attrs


def _mutator_body_ok(stmts, selfn):
    """Every statement is `self.attr = <expr>`, pass, or an if/else whose branches recursively are -- the
    shape the object rewrite can inline (a conditional mutator like `if v > 0: self.count = self.count + 1`
    becomes a guarded accumulator the loop engines handle)."""
    for st in stmts:
        if isinstance(st, ast.Pass):
            continue
        if (isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Attribute)
                and isinstance(st.targets[0].value, ast.Name) and st.targets[0].value.id == selfn):
            continue
        if isinstance(st, ast.If) and _mutator_body_ok(st.body, selfn) and _mutator_body_ok(st.orelse, selfn):
            continue
        return False
    return True


def _simple_mutator(classes, cname, mname):
    """(self_name, params, body) for a method the object rewrite can inline as in-place attribute updates: its
    body is `self.attr = <expr>` assignments, pass, and if/else over those, self is used only as `self.attr`
    (never aliased, passed, or with a method called on it), and it returns no value (so a call is a statement,
    not used in an expression). None for any other method, so a call to it declines the object rather than
    guessing."""
    m = core._find_method(classes, cname, mname)
    if m is None or not m.args.args or m.args.vararg or m.args.kwarg or m.args.kwonlyargs or m.args.defaults:
        return None
    selfn = m.args.args[0].arg
    for n in ast.walk(m):
        if isinstance(n, ast.Return) and n.value is not None:
            return None                                          # returns a value: a call could be used as an expression
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and isinstance(n.func.value, ast.Name) and n.func.value.id == selfn):
            return None                                          # self.method(): a nested call, not inlined
    ok_ids = {id(n.value) for n in ast.walk(m) if isinstance(n, ast.Attribute)
              and isinstance(n.value, ast.Name) and n.value.id == selfn}
    if any(isinstance(n, ast.Name) and n.id == selfn and id(n) not in ok_ids for n in ast.walk(m)):
        return None                                              # self used bare: escapes
    if not _mutator_body_ok(m.body, selfn):
        return None                                              # not a (conditional) attribute-assignment body
    return selfn, [a.arg for a in m.args.args[1:]], m.body


def _simple_accessor(classes, cname, mname):
    """(self_name, params, return_expr) for a pure-getter method: its body is a single `return <expr>` (after
    optional pass) whose expr reads only self.<attr>, the method's parameters, and constants -- no attribute
    store, no nested self.method() call, self never bare (escaping). A call to it is inlined in expression
    position as the returned expression with self.<attr> the accumulator variable, so a value-returning method
    over loop-mutated object state is reasoned about. None for any other method, so a non-getter call declines."""
    m = core._find_method(classes, cname, mname)
    if m is None or not m.args.args or m.args.vararg or m.args.kwarg or m.args.kwonlyargs or m.args.defaults:
        return None
    selfn = m.args.args[0].arg
    body = [s for s in m.body if not isinstance(s, ast.Pass)]
    if len(body) != 1 or not isinstance(body[0], ast.Return) or body[0].value is None:
        return None                                              # not a single `return <expr>`
    for n in ast.walk(m):
        if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Attribute) \
                and isinstance(n.target.value, ast.Name) and n.target.value.id == selfn:
            return None                                          # mutates self: not a pure accessor
        if isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Attribute) and isinstance(t.value, ast.Name) and t.value.id == selfn:
                    return None
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and isinstance(n.func.value, ast.Name) and n.func.value.id == selfn):
            return None                                          # self.method(): a nested call, not inlined
    ok_ids = {id(n.value) for n in ast.walk(m) if isinstance(n, ast.Attribute)
              and isinstance(n.value, ast.Name) and n.value.id == selfn}
    if any(isinstance(n, ast.Name) and n.id == selfn and id(n) not in ok_ids for n in ast.walk(m)):
        return None                                              # self used bare: escapes
    return selfn, [a.arg for a in m.args.args[1:]], body[0].value


def _object_attribute_only(fn, oname, assign_node, classes, cname):
    """The set of mutator-method names called on `oname` when it is used only as the single `oname = C()`
    construction, as `oname.attr` loads/stores, and as `oname.m(args)` calls to simple mutator methods (which
    the rewrite inlines). None when the object escapes -- a bare use (aliased `p = oname`, passed `f(oname)`,
    returned, indexed, compared) or a method that is not a simple mutator."""
    ok_ids = {id(assign_node.targets[0])}                        # the construction's target Name
    mutators = set()
    for n in ast.walk(fn):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Name) \
                and n.func.value.id == oname:
            if _simple_mutator(classes, cname, n.func.attr) is None \
                    and _simple_accessor(classes, cname, n.func.attr) is None:
                return None                                      # not a simple mutator or accessor: declines o
            mutators.add(n.func.attr)
            ok_ids.add(id(n.func.value))
        if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == oname:
            ok_ids.add(id(n.value))                              # oname.attr : a legitimate attribute use
    if any(isinstance(n, ast.Name) and n.id == oname and id(n) not in ok_ids for n in ast.walk(fn)):
        return None
    return mutators


def _rewrite_single_object(src, target):
    """Rewrite single non-aliased local objects whose class has a no-argument constant-attribute __init__ into
    plain accumulator variables, so a loop mutating o.attr becomes a loop over variables the loop engines
    handle: `o = C()` becomes the constant attribute initializers and every `o.attr` becomes `_obj_o_attr`.
    Returns the rewritten function source, or None when no object qualifies (an object that escapes, has a
    method called on it, or whose __init__ is arg-taking or non-constant is left to the heap engine / UNKNOWN)."""
    try:
        mod = _parse(src)
        fn = next(n for n in mod.body if isinstance(n, ast.FunctionDef) and n.name == target)
    except Exception:
        return None
    classes = {n.name: n for n in mod.body if isinstance(n, ast.ClassDef)}
    if not classes:
        return None
    assigns = {}
    for s in ast.walk(fn):
        if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
            assigns.setdefault(s.targets[0].id, []).append(s)
    targets = {}
    for oname, slist in assigns.items():
        if len(slist) != 1:
            continue                                             # reassigned: not a single stable object
        v = slist[0].value
        if not (isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id in classes
                and not v.keywords and not any(isinstance(a, ast.Starred) for a in v.args)):
            continue
        ia = _init_attrs(classes, v.func.id)
        if ia is None:
            continue
        initparams, attrs = ia
        if len(v.args) != len(initparams):
            continue                                             # constructor arity must match the __init__ parameters
        muts = _object_attribute_only(fn, oname, slist[0], classes, v.func.id)
        if muts is None:
            continue
        targets[oname] = (attrs, v.func.id, initparams)
    if not targets:
        return None
    pfx = lambda o, a: "_obj_%s_%s" % (o, a)

    class _Inline(ast.NodeTransformer):                          # o.m(args) statement -> the mutator body inlined
        def visit_Expr(self, node):                              # with self -> o and the parameters -> the call args
            self.generic_visit(node)
            c = node.value
            if (isinstance(c, ast.Call) and isinstance(c.func, ast.Attribute)
                    and isinstance(c.func.value, ast.Name) and c.func.value.id in targets):
                o = c.func.value.id
                mut = _simple_mutator(classes, targets[o][1], c.func.attr)
                if mut is not None and len(c.args) == len(mut[1]):
                    selfn, params, body = mut
                    subst = {selfn: ast.Name(id=o, ctx=ast.Load())}
                    subst.update({p: copy.deepcopy(a) for p, a in zip(params, c.args)})
                    out = [_subst_names(copy.deepcopy(s), subst) for s in body if not isinstance(s, ast.Pass)]
                    return out or [ast.copy_location(ast.Pass(), node)]
            return node

        def visit_Call(self, node):                              # o.get(args) expression -> the accessor's return
            self.generic_visit(node)                             # expr inlined (self.attr becomes the accumulator)
            if (isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name)
                    and node.func.value.id in targets):
                o = node.func.value.id
                acc = _simple_accessor(classes, targets[o][1], node.func.attr)
                if acc is not None and len(node.args) == len(acc[1]):
                    selfn, params, rexpr = acc
                    subst = {selfn: ast.Name(id=o, ctx=ast.Load())}
                    subst.update({p: copy.deepcopy(a) for p, a in zip(params, node.args)})
                    return ast.copy_location(_subst_names(copy.deepcopy(rexpr), subst), node)
            return node

    fn = _Inline().visit(copy.deepcopy(fn)); ast.fix_missing_locations(fn)

    class _Rw(ast.NodeTransformer):
        def visit_Assign(self, node):
            self.generic_visit(node)
            if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name) and node.targets[0].id in targets:
                o = node.targets[0].id                           # o = C(args) -> the attribute initializers, with the
                attrs, _cn, initparams = targets[o]              # constructor arguments bound into each value
                callargs = node.value.args if isinstance(node.value, ast.Call) else []
                bind = {p: copy.deepcopy(a) for p, a in zip(initparams, callargs)}
                inits = [ast.Assign(targets=[ast.Name(id=pfx(o, a), ctx=ast.Store())],
                                    value=_subst_names(copy.deepcopy(c), bind))
                         for a, c in attrs.items()]
                return [ast.copy_location(s, node) for s in inits] or [ast.copy_location(ast.Pass(), node)]
            if (len(node.targets) == 1 and isinstance(node.targets[0], ast.Attribute)
                    and isinstance(node.targets[0].value, ast.Name) and node.targets[0].value.id in targets):
                t = node.targets[0]                              # o.attr = e -> _obj_o_attr = e
                node.targets = [ast.copy_location(ast.Name(id=pfx(t.value.id, t.attr), ctx=ast.Store()), t)]
            return node

        def visit_Attribute(self, node):
            self.generic_visit(node)
            if (isinstance(node.value, ast.Name) and node.value.id in targets and isinstance(node.ctx, ast.Load)):
                return ast.copy_location(ast.Name(id=pfx(node.value.id, node.attr), ctx=ast.Load()), node)
            return node

    new_fn = _Rw().visit(copy.deepcopy(fn))
    ast.fix_missing_locations(new_fn)
    try:
        return ast.unparse(new_fn)
    except Exception:
        return None


def _try_sequence_loop(prop, target, src, post_node, pre_node, repo, spec):
    """Route a for-loop over a list parameter to verify_sequence_loop, which relates the result to the list
    length and to per-element accumulators -- a property the general CHC engine leaves UNKNOWN. The Python
    pre/post are compiled with each list parameter bound to a sized container, so len(xs) reads its length.
    Intraprocedural only; UNKNOWN outside the for-over-list shape (the engine then declines)."""
    if repo:
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason="interprocedural")
    try:
        fn = _fndef(src)
    except Unsupported:
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason="no function")
    listparams = [a.arg for a in fn.args.args if isinstance(a.annotation, ast.Name) and a.annotation.id == "list"]
    if fn.args.vararg is not None:
        listparams.append(fn.args.vararg.arg)
    if not listparams:
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason="no list parameter")

    class _LenRw(ast.NodeTransformer):                                            # len(xs) -> the bound length name
        def visit_Call(self, n):                                                 # len_xs (verify_sequence_loop's P
            self.generic_visit(n)                                                # carries len_<list>), so the spec
            if (isinstance(n.func, ast.Name) and n.func.id == "len" and len(n.args) == 1   # need not go through the
                    and isinstance(n.args[0], ast.Name) and n.args[0].id in listparams):   # value engine's len() path
                return ast.copy_location(ast.Name(id="len_" + n.args[0].id, ctx=ast.Load()), n)
            return n

    pn = ast.fix_missing_locations(_LenRw().visit(copy.deepcopy(post_node)))
    forall_pre = None                                                            # a per-element precondition
    if (isinstance(pre_node, ast.Call) and isinstance(pre_node.func, ast.Name) and pre_node.func.id == "all"
            and len(pre_node.args) == 1 and isinstance(pre_node.args[0], ast.GeneratorExp)):
        g = pre_node.args[0]                                                      # all(<pred> for x in xs)
        if (len(g.generators) == 1 and not g.generators[0].ifs and isinstance(g.generators[0].target, ast.Name)
                and isinstance(g.generators[0].iter, ast.Name) and g.generators[0].iter.id in listparams):
            _ev, _ep = g.generators[0].target.id, g.elt
            forall_pre = lambda e: ev_bool(_ep, {_ev: e}, spec)                   # assumed of every element
    rn = (ast.parse("True", mode="eval").body if forall_pre is not None
          else ast.fix_missing_locations(_LenRw().visit(copy.deepcopy(pre_node))))
    pre = lambda P: ev_bool(rn, dict(P), spec)
    post = lambda P, r: ev_bool(pn, {**P, "result": r}, spec)
    try:
        return verify_sequence_loop(prop, target, src, post, pre, forall_pre=forall_pre)
    except Exception as e:
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason=str(e))


def _ev_arr_bool(node, st):
    """A boolean spec expression over an array state: and / or / not / True / False, with each leaf a
    comparison `_ev_arr` decides (a subscript a[j] is Select, len(a) the length term). Lets a quantified
    spec's per-element body and an array-loop precondition be translated without the value engine."""
    if isinstance(node, ast.Constant) and isinstance(node.value, bool):
        return z3.BoolVal(node.value)
    if isinstance(node, ast.BoolOp):
        parts = [_ev_arr_bool(v, st) for v in node.values]
        return z3.And(*parts) if isinstance(node.op, ast.And) else z3.Or(*parts)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return z3.Not(_ev_arr_bool(node.operand, st))
    return _ev_arr(node, st, [], z3.BoolVal(True))


def _quantified_post_spec(post_node):
    """Recognize an element-universal postcondition all(<body> for <var> in <iter>) and return
    (var, iter_node, body), or None. A single filter-free generator is required; any(...), a filter,
    or multiple clauses decline, so only a sound universal is compiled."""
    if not (isinstance(post_node, ast.Call) and isinstance(post_node.func, ast.Name)
            and post_node.func.id == "all" and len(post_node.args) == 1
            and isinstance(post_node.args[0], ast.GeneratorExp)):
        return None
    g = post_node.args[0]
    if len(g.generators) != 1:
        return None
    gen = g.generators[0]
    if gen.ifs or getattr(gen, "is_async", 0) or not isinstance(gen.target, ast.Name):
        return None
    return gen.target.id, gen.iter, g.elt


def _prove_forall(prop, target, src, post_node, pre_node):
    """Discharge an element-universal spec all(P(result[j]) ...) / all(P(a[j]) for j in range(n)) by compiling
    it into the callback the existing quantified-spec engines already accept (verify_map_comprehension for a
    map-comprehension return, verify_array_loop_auto for an array-write loop), so prove decides a forall the
    general CHC engine leaves UNKNOWN. The body is translated by the engines' own _ev_arr / q_forall (a forall
    bounded by the quantifier range), so no new trust is added; an untranslatable body declines (UNKNOWN)."""
    q = _quantified_post_spec(post_node)
    if q is None:
        return Verdict(UNKNOWN, prop, target, "forall spec", reason="not an all(... for ...) postcondition")
    var, it, body = q
    try:
        fn = _fndef(src)
    except Unsupported:
        return Verdict(UNKNOWN, prop, target, "forall spec", reason="no function")
    is_range = (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range"
                and len(it.args) == 1)
    is_result = isinstance(it, ast.Name) and it.id == "result"
    # a single list-comprehension return: the result is the exact map, so all(P(result[j])) / all(P(e) for e in
    # result) is checked over the result array.
    if len(fn.body) == 1 and isinstance(fn.body[0], ast.Return) and isinstance(fn.body[0].value, ast.ListComp):
        def post(P, R, Rn):
            env = {**P, "result": R, "len_result": Rn}
            if is_result:
                return q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < Rn),
                                                     _ev_arr_bool(body, {**env, var: z3.Select(R, j)})))
            if is_range:
                b = _ev_arr(it.args[0], env, [], z3.BoolVal(True))   # range(len(result)) / range(len(xs))
                return q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < b),
                                                     _ev_arr_bool(body, {**env, var: j})))
            raise Unsupported("unsupported forall iterable over a comprehension")
        try:
            return verify_map_comprehension(prop, target, src, post)
        except (Unsupported, z3.Z3Exception, TypeError, KeyError) as e:
            return Verdict(UNKNOWN, prop, target, "forall spec", reason=str(e))
    # an array-write loop: all(P(a[j]) for j in range(<bound>)) over the loop-exit array.
    if is_range and any(isinstance(n, (ast.While, ast.For)) for n in ast.walk(fn)):
        pre = lambda S: _ev_arr_bool(pre_node, S)

        def post(S, _E):
            b = _ev_arr(it.args[0], S, [], z3.BoolVal(True))
            return q_forall(lambda j: z3.Implies(z3.And(0 <= j, j < b),
                                                 _ev_arr_bool(body, {**S, var: j})))
        try:
            return verify_array_loop_auto(prop, target, src, pre, post)
        except (Unsupported, z3.Z3Exception, TypeError, KeyError) as e:
            return Verdict(UNKNOWN, prop, target, "forall spec", reason=str(e))
    return Verdict(UNKNOWN, prop, target, "forall spec", reason="not a map comprehension or array-write loop")


def _try_sos_prove(prop, target, impl_src, post_node, pre_node, repo):
    """A polynomial nonnegativity goal e1 >= e2 (>, <=, < too) over integer parameters with no precondition and a
    trap-free body, routed to the SOS engine (an exact-rational-checked certificate). None unless SOS proves it."""
    import math as _m
    if repo or not _all_int_params(impl_src):
        return None
    if not (isinstance(pre_node, ast.Constant) and pre_node.value is True):
        return None                                          # a precondition needs constrained Positivstellensatz
    if not (isinstance(post_node, ast.Compare) and len(post_node.ops) == 1
            and type(post_node.ops[0]) in (ast.GtE, ast.Gt, ast.LtE, ast.Lt)):
        return None
    try:
        ctx = Ctx(repo or {}); ctx.facts = []
        args, z3args, rets, itraps, inone = symexec(impl_src, ctx)
        if itraps or not z3.is_false(z3.simplify(inone)) or ctx.facts or getattr(ctx, "overapprox", False):
            return None                                      # a possible trap / None return / over-approximation
        out = fold(rets)
        spec = Ctx(repo or {}); spec.traps = None
        lhs = ev(post_node.left, {**z3args, "result": out}, spec)
        rhs = ev(post_node.comparators[0], {**z3args, "result": out}, spec)
    except Exception:
        return None
    if not (z3.is_expr(lhs) and z3.is_int(lhs) and z3.is_expr(rhs) and z3.is_int(rhs)):
        return None
    op = type(post_node.ops[0])
    base = (lhs - rhs) if op in (ast.GtE, ast.Gt) else (rhs - lhs)   # prove base >= 0
    polyterm = (base - 1) if op in (ast.Gt, ast.Lt) else base        # p > 0 over the integers == p - 1 >= 0
    intargs = [z3args[a] for a in args]
    nvars = len(intargs)
    if nvars == 0:
        return None

    def poly(X):
        return z3.substitute(polyterm, *[(intargs[i], X[i]) for i in range(nvars)])
    from .domains import verify_sos_nonneg
    for deg in (2, 4):
        if _m.comb(nvars + deg // 2, deg // 2) > 10:         # bound the 2^k PSD-minor enumeration
            continue
        try:
            v = verify_sos_nonneg(prop, target, poly, nvars, degree=deg)
        except Exception:
            v = None
        if v is not None and v.status == PROVED:
            return v
    return None


def _prove_via_havoc(prop, target, impl_src, pre_node, post_node, repo):
    """Discharge a postcondition through the havoc / over-approximation value engine, which handles for-loops,
    complex assignment targets, comprehensions, and annotated assignments the exact engine declines. The
    over-approximation widens the reachable states, so a post holding over all of them holds for the real ones
    (PROVED is sound); a violation may be spurious, so this only ever PROVES, never refutes."""
    try:
        from .domains import _infer_param_kinds
        kinds = _infer_param_kinds(_fndef(impl_src))
    except Exception:
        kinds = None
    ctx = Ctx(repo or {}); ctx.facts = []
    saved = core._TRAPFREE; core._TRAPFREE = True
    try:
        args, z3args, rets, traps, inone = symexec(impl_src, ctx, param_kinds=kinds)
        out = fold(rets)
        pspec = Ctx(repo or {}); pspec.traps = None; pspec.pc = z3.BoolVal(True); pspec.facts = ctx.facts
        pre_t = ev_bool(pre_node, dict(z3args), pspec)
        post_t = ev_bool(post_node, {**z3args, "result": out}, pspec)
    except Exception:
        return Verdict(UNKNOWN, prop, target, "property (over-approximation)", reason="not modeled")
    finally:
        core._TRAPFREE = saved
    if getattr(ctx, "none_havoc", False):                     # a None masked by havoc could violate the post
        return Verdict(UNKNOWN, prop, target, "property (over-approximation)", reason="a None may survive a loop")
    claim_false = z3.And(pre_t, *ctx.facts, z3.Or(_trap_or(traps), inone, z3.Not(post_t))) if ctx.facts \
        else z3.And(pre_t, z3.Or(_trap_or(traps), inone, z3.Not(post_t)))
    if _solve(claim_false)[0] == PROVED:
        return Verdict(PROVED, prop, target, "property (over-approximation, all inputs)",
                       reason="holds over the loop / value over-approximation")
    return Verdict(UNKNOWN, prop, target, "property (over-approximation)", reason="not proved under over-approximation")


def prove(impl_src, ensures, requires="True", repo=None, prop="property", target=None, best_effort=False) -> Verdict:
    """State a property in Python rather than raw Z3. `ensures` is a boolean expression over the parameters and
    `result`; `requires` is an optional precondition. Both are translated by the same symbolic core that models
    the code. A looping function is routed to the whole-function Horn engine (which infers the loop invariant);
    a loop-free function is checked by typed symbolic execution. Returns PROVED, REFUTED (with a
    counterexample), or UNKNOWN.

    PROVED is partial correctness: for every input meeting the precondition the function returns without a trap
    and the postcondition holds, but termination is NOT implied. Prove termination separately with verify_total
    (or `check --total`)."""
    _require_str("impl_src", impl_src); _require_str("ensures", ensures); _require_str("requires", requires)
    _require_repo(repo)
    if best_effort and not core.BEST_EFFORT:                  # opt-in lower-trust run (off by default)
        saved = core.BEST_EFFORT; core.BEST_EFFORT = True
        core.BEST_EFFORT_ASSUMED = False                      # taint: was a best-effort assumption actually used?
        try:
            v = prove(impl_src, ensures, requires, repo, prop, target)
            return _label_best_effort(v, core.BEST_EFFORT_ASSUMED)
        finally:
            core.BEST_EFFORT = saved
    return _escalate_budget(lambda: _prove_core(impl_src, ensures, requires, repo, prop, target))


def _prove_recursive_list(prop, target, src, pre_node, post_node, spec):
    """Auto-route a self-recursion over a `list`-annotated parameter to the array-encoded recursive-list engine,
    so `prove` reaches it without the named verify_recursive_list entry point. The Python spec's len(xs) bridges
    to the array's length by binding the list parameter to a sized container; a spec that subscripts the list
    (xs[j]) is declined (the bridge cannot represent element content soundly). None when no list parameter."""
    try:
        fn = _fndef(src)
    except Exception:
        return None
    listparams = [a.arg for a in fn.args.args if isinstance(a.annotation, ast.Name) and a.annotation.id == "list"]
    if not listparams:
        return None
    for node in (pre_node, post_node):
        if any(isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name) and n.value.id in listparams
               for n in ast.walk(node)):
            return None                                       # an element-content spec is outside the length bridge

    class _LenToVar(ast.NodeTransformer):                      # len(xs) -> the array's length variable len_xs
        def visit_Call(self, node):
            self.generic_visit(node)
            if (isinstance(node.func, ast.Name) and node.func.id == "len" and len(node.args) == 1
                    and isinstance(node.args[0], ast.Name) and node.args[0].id in listparams):
                return ast.copy_location(ast.Name(id="len_" + node.args[0].id, ctx=ast.Load()), node)
            return node
    pre2 = ast.fix_missing_locations(_LenToVar().visit(copy.deepcopy(pre_node)))
    post2 = ast.fix_missing_locations(_LenToVar().visit(copy.deepcopy(post_node)))
    pre = lambda P: ev_bool(pre2, dict(P), spec)
    post = lambda P, r: ev_bool(post2, {**P, "result": r}, spec)
    try:
        return verify_recursive_list(prop, target, src, pre, post)
    except Exception:
        return None


def _prove_core(impl_src, ensures, requires, repo, prop, target):
    repo = repo or {}
    # An async function returns a coroutine; its body runs (and yields its `return` value) when that
    # coroutine is awaited. The property is read over that awaited result, so the async function is
    # desugared to the synchronous body the await drives (await e -> e, async for/with -> for/with) and
    # then verified by every engine exactly as a sync function -- sound for the awaited value and its traps.
    impl_src = core._strip_async(impl_src)
    _top = _parse(impl_src).body
    _fns = [n for n in _top if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    target = target or (_fns[0].name if _fns else "f")
    _deco = _inline_decorators(impl_src, target, repo)          # a non-identity decorator: verify what it produces
    if _deco is not None:                                       # (the wrapper, with the original inlined), not the
        impl_src, repo = _deco                                 # written body, and not declined
        _fns = [n for n in _parse(impl_src).body if isinstance(n, ast.FunctionDef)]
    else:
        _tfn = next((n for n in _fns if n.name == target), None)
        if _tfn is not None and _tfn.decorator_list and _has_unmodeled_decorator(_tfn, {n.name: n for n in _fns}):
            return Verdict(UNKNOWN, prop, target, "property (Python spec)",
                           reason="unresolved decorator: the callable it produces is not modeled")
    if not repo:                                                 # a single non-aliased local object with a
        _objrw = _rewrite_single_object(impl_src, target)        # constant __init__: rewrite o.attr to plain
        if _objrw is not None:                                   # accumulator variables so a loop over object
            impl_src = _objrw                                    # state is reasoned about by the loop engines
            _fns = [n for n in _parse(impl_src).body if isinstance(n, ast.FunctionDef)]
    impl_src = _isolate_target(impl_src, _fns, target)           # a multi-function module: prove about `target` alone
    spec = Ctx(repo); spec.traps = None; spec.pc = z3.BoolVal(True)
    try:
        pre_node = core.parse_spec(requires)
        post_node = core.parse_spec(ensures)
    except SyntaxError as e:
        return Verdict(UNKNOWN, prop, target, "property (Python spec)", reason=f"spec syntax: {e}")
    pre_node, post_node = _strip_old(pre_node), _strip_old(post_node)
    pre_fn = lambda S: ev_bool(pre_node, dict(S), spec)
    post_fn = lambda S, r: ev_bool(post_node, {**S, "result": r}, spec)
    if not repo and _quantified_post_spec(post_node) is not None:                # an element-universal spec:
        fv = _prove_forall(prop, target, impl_src, post_node, pre_node)          # all(P(result[j]) / a[j] ...),
        if fv.status != UNKNOWN:                                                 # routed to the quantified-spec
            return fv                                                           # engines (map comp / array loop)
    if any(isinstance(n, (ast.While, ast.For)) for n in ast.walk(_parse(impl_src))):
        v = verify_chc(prop, target, impl_src, pre_fn, post_fn, repo)           # single loop: synthesizes the
        if v.status != UNKNOWN:                                                 # invariant Spacer misses
            return v
        vf = verify_function(prop, target, impl_src, pre_fn, post_fn, repo)     # general control flow (nested loops:
        if vf.status != UNKNOWN:                                               # the per-block CHC system synthesizes
            return vf                                                          # an independent invariant per loop)
        sl = _try_sequence_loop(prop, target, impl_src, post_node, pre_node, repo, spec)   # for-over-list vs len/accumulator
        if sl.status != UNKNOWN:
            return sl
        hv = _prove_via_havoc(prop, target, impl_src, pre_node, post_node, repo)   # over-approximation fallback (PROVED-only)
        return hv if hv.status != UNKNOWN else vf
    if _is_self_recursive(impl_src):                                            # self-recursion: inductive relation
        rl = _prove_recursive_list(prop, target, impl_src, pre_node, post_node, spec)   # structural recursion over a
        if rl is not None and rl.status != UNKNOWN:                             # list parameter, auto-routed to the
            return rl                                                          # array-encoded engine (no named entry)
        return verify_recursive(prop, target, impl_src, pre_fn, post_fn)
    if any(isinstance(n, ast.ClassDef) for n in _top):                          # object construction + method
        # a loop-free class-using function (instantiation, attribute access, method dispatch along the C3 MRO)   #
        # is modeled by the heap engine, which the integer/value path cannot resolve; route the Python property  #
        # to it, falling through when it abstains. Sound: the heap engine only refutes a genuinely false claim.  #
        try:
            hv = verify_heap_property(prop, target, impl_src,
                                      lambda za, r: ev_bool(post_node, {**za, "result": r}, Ctx(repo)))
            if hv.status != UNKNOWN:
                return hv
        except Exception:
            pass
    if not repo:                                                                # the integer loop-free fragment is
        from .vcgen import prove_via_vcgen                                      # discharged through the Rocq-verified
        vg = prove_via_vcgen(impl_src, ensures, requires, prop=prop, target=target)   # VC generator; fall back below
        if vg.status != UNKNOWN:                                               # when the function is outside it
            return _annotate_machine_overflow(vg, impl_src, pre_fn, repo) if _all_int_params(impl_src) else vg
        sv = _try_sos_prove(prop, target, impl_src, post_node, pre_node, repo)   # nonlinear nonnegativity: SOS certificate
        if sv is not None:
            return _annotate_machine_overflow(sv, impl_src, pre_fn, repo) if _all_int_params(impl_src) else sv
    if (_has_var_bitwise(impl_src) or _ast_has_var_bitwise(post_node)           # a bitwise claim (in body, spec, OR a
            or _ast_has_var_bitwise(pre_node)):                                # width-bounding precondition) the
        _w = _infer_bv_width(pre_node, impl_src, repo) or 64                    # over-approximation leaves UNKNOWN:
        bw = verify_bitwise(prop, target, impl_src, post_node, pre_node, repo, width=_w)   # when the precondition bounds
        if bw.status != UNKNOWN:                                               # the operands to a finite width, decide it
            return bw                                                          # exactly via bitvectors (else fall through)
    ctx = Ctx(repo); ctx.facts = []
    try:
        args, z3args, rets, itraps, inone = symexec(impl_src, ctx, param_kinds=_float_kinds(impl_src))
        if core.ALLOW_SUBJECT_EXECUTION:
            soundness_probe(impl_src, z3args, rets, args, repo)
        out = fold(rets)
        pre_term = ev_bool(pre_node, dict(z3args), spec)
        post_term = ev_bool(post_node, {**z3args, "result": out}, spec)
    except (Unsupported, KeyError, z3.Z3Exception, TypeError, AttributeError) as u:
        hv = _prove_via_havoc(prop, target, impl_src, pre_node, post_node, repo)   # complex targets / AnnAssign /
        if hv.status != UNKNOWN:                                                   # comprehensions the exact engine declines
            return hv
        return Verdict(UNKNOWN, prop, target, "property (Python spec)",
                       reason=f"could not translate the property: {u}")
    claim_false = _with_facts(ctx, z3.And(pre_term, z3.Or(_trap_or(itraps), inone, z3.Not(post_term))))
    if core.REQUIRE_CORROBORATION and not ctx.overapprox:
        status, model, corr = solve_corroborated(claim_false)
    else:
        (status, model), corr = _solve(claim_false), None
    status, model = _downgrade_overapprox(status, model, ctx)
    cex = cex_in = None
    if status == REFUTED:
        # prefer a non-trapping, returning counterexample (a genuine postcondition violation) over one that
        # merely traps or returns None, when one exists -- x % y < 0 is shown at y < 0, not the y = 0 trap.
        clean = _with_facts(ctx, z3.And(pre_term, z3.Not(_trap_or(itraps)), z3.Not(inone), z3.Not(post_term)))
        cst, cm = _solve(clean)
        if cst == REFUTED:
            model = minimize_witness(clean, z3args, args) or cm or model
        else:
            model = minimize_witness(claim_false, z3args, args) or model
        cex, cex_in = _model_cex(model, z3args, args)
    elif status == UNKNOWN and getattr(ctx, "overapprox", False):   # sample real sin/cos/exp/log for a witness
        w = _refute_overapprox(args, z3args, pre_term, post_term)
        if w is not None:
            status, cex, cex_in = REFUTED, ", ".join(f"{a}={w[a]}" for a in args), w
    why = "" if status != UNKNOWN else (
        corr if corr == core._NL_UNCORROBORATED else
        ((getattr(ctx, "overapprox_reason", None) or "an over-approximated term yields no certified verdict")
         if getattr(ctx, "overapprox", False) else "solver returned unknown"))
    cert = core.proof_certificate(corr) if status == PROVED and corr else None
    v = Verdict(status, prop, target, "property (Python spec, all inputs)",
                counterexample=cex, counterexample_inputs=cex_in, reason=why, certificate=cert)
    return _annotate_machine_overflow(v, impl_src, pre_fn, repo) if _all_int_params(impl_src) else v


def _isinstance_guards_guessed_scalar(fn, kinds) -> bool:
    """True if the body tests `isinstance(p, ...)` for an unannotated parameter `p` that the value engine models
    as a guessed z3 scalar: a `str` or `float` inferred from usage, or the default `int` of a parameter with no
    sequence / container / dict / object usage. The value engine answers isinstance on a z3 scalar statically
    from its sort, so `isinstance(p, str)` on a String-modeled `p` (or `isinstance(p, int)` on the default Int)
    is unconditionally true and the non-matching branch is pruned -- but `p`'s type was guessed, not declared,
    and the isinstance test is itself evidence the function handles other types, whose path (and any trap on it)
    the pruning would hide. A container, sequence, dict, or object parameter is unaffected: isinstance on a
    non-scalar value already yields a fresh bool (both branches live), and a declared `p: str` / `p: int` is a
    real precondition the pruning honours. A local bound directly to such a parameter (`x = p`) inherits the
    guess -- `isinstance(x, int)` prunes on the same unproven type -- so the taint propagates to plain aliases;
    `x = p + 1` does not taint (reaching it proves `p` an int, else the add traps first)."""
    k = kinds or {}
    guessed = {a.arg for a in fn.args.posonlyargs + fn.args.args + fn.args.kwonlyargs
               if a.annotation is None and k.get(a.arg) not in ("container", "seq", "dict", "object")}
    if not guessed:
        return False
    changed = True
    while changed:                                               # a plain alias of a guessed scalar is also guessed
        changed = False
        for n in ast.walk(fn):
            if (isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                    and isinstance(n.value, ast.Name) and n.value.id in guessed and n.targets[0].id not in guessed):
                guessed.add(n.targets[0].id); changed = True
    return any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "isinstance"
               and n.args and isinstance(n.args[0], ast.Name) and n.args[0].id in guessed
               for n in ast.walk(fn))


def _check_trapfree_symexec(prop, target, src, pre_node, spec, repo, has_pre, trapfree_callees=frozenset()) -> Verdict:
    """Trap-freedom fallback through the value engine, for a loop-free function the CFG/CHC checker declines
    (a local dict built by `d[k] = v` then read). `core._TRAPFREE` makes the value engine total, so the verdict
    rests on the traps alone (a missing-key KeyError, a division by zero, a failing assert). PROVED when no trap
    is reachable under the precondition; a reachable trap REFUTES only with no precondition and no havoc, where
    the query is exact. `trapfree_callees` are recursive callees verified trap free standalone, inlined as a
    fresh result so the caller proceeds."""
    gated = _definite_assignment_guard(prop, target, "implicit contracts (asserts + trap freedom)", [src])
    if gated is not None:                                        # a variable possibly read before assignment on some
        return gated                                             # branch raises UnboundLocalError, not precisely modeled,
    #                                                              so the value engine abstains rather than proving total
    try:
        from .domains import _infer_param_kinds
        _fn = _fndef(src)
        kinds = _infer_param_kinds(_fn)
        risky_isinstance = _isinstance_guards_guessed_scalar(_fn, kinds)
    except Exception:
        kinds = None
        risky_isinstance = False
    ctx = Ctx(repo or {}); ctx.facts = []; ctx.trapfree_callees = trapfree_callees
    ctx.exact_traps = []                                          # precise first-iteration loop traps (refutable)
    saved = core._TRAPFREE; core._TRAPFREE = True
    try:
        _a, z3args, _r, traps, _n = symexec(src, ctx, param_kinds=kinds)
        pre_term = ev_bool(pre_node, dict(z3args), spec)
    except Exception:
        return Verdict(UNKNOWN, prop, target, "implicit contracts (asserts + trap freedom)", reason="not modeled")
    finally:
        core._TRAPFREE = saved
    if getattr(ctx, "none_havoc", False):
        # a possibly-None variable crossed a loop and was havoc'd to a fresh integer, which would mask a
        # surviving None used in arithmetic; this engine cannot soundly PROVE here. The optional CFG/CHC
        # engine (verify_no_raise_optional, tried first in check) carries the None precisely instead.
        return Verdict(UNKNOWN, prop, target, "implicit contracts (asserts + trap freedom)",
                       reason="a None may survive a loop; the value engine's havoc cannot model it soundly")
    if not traps:
        if risky_isinstance:                                     # a guessed-scalar parameter is isinstance-tested, so
            return Verdict(UNKNOWN, prop, target, "implicit contracts (asserts + trap freedom)",   # the value engine's
                           reason="an isinstance test narrows an inferred-typed parameter; a branch the engine pruned "
                                  "may carry a trap the committed type hides")   # static isinstance unsoundly prunes a branch
        return Verdict(PROVED, prop, target, "implicit contracts (asserts + trap freedom)",
                       reason="no trap reachable (value engine)")
    claim = z3.And(pre_term, *ctx.facts, z3.Or(*traps)) if ctx.facts else z3.And(pre_term, z3.Or(*traps))
    st = _solve(claim)[0]                                          # claim asserts a reachable trap
    if st == PROVED:                                              # no trap reachable under the precondition
        if risky_isinstance:                                     # see above: a static isinstance on a guessed-scalar
            return Verdict(UNKNOWN, prop, target, "implicit contracts (asserts + trap freedom)",   # parameter prunes a
                           reason="an isinstance test narrows an inferred-typed parameter; a branch the engine pruned "
                                  "may carry a trap the committed type hides")   # branch whose trap would be hidden
        return Verdict(PROVED, prop, target, "implicit contracts (asserts + trap freedom)",
                       reason="no trap reachable (value engine)")
    if st == REFUTED and not has_pre and not ctx.havoc and not getattr(ctx, "overapprox", False):
        # a precise trap: no precondition, no loop havoc, and no over-approximated term (a float **, a
        # transcendental, a string bound) on which a satisfiable trap query could be spurious -- exactly as
        # _downgrade_overapprox withholds REFUTED for prove / verify_predicate.
        return Verdict(REFUTED, prop, target, "implicit contracts (asserts + trap freedom)",
                       reason="a trap is reachable")
    exact = getattr(ctx, "exact_traps", None)                    # a precise first-iteration loop trap refutes even
    if exact and not has_pre and not getattr(ctx, "overapprox", False):   # under the loop's havoc (the element is
        ec = z3.And(pre_term, *ctx.facts, z3.Or(*exact)) if ctx.facts else z3.And(pre_term, z3.Or(*exact))   # free,
        if _solve(ec)[0] == REFUTED:                             # the prior state exact, so the witness is real)
            return Verdict(REFUTED, prop, target, "implicit contracts (asserts + trap freedom)",
                           reason="a trap is reachable on a loop iteration")
    return Verdict(UNKNOWN, prop, target, "implicit contracts (asserts + trap freedom)", reason="solver returned unknown")


def _trapfree_recursive_callees(src, repo):
    """The in-repo callees reachable from `src` that are self-recursive (which the value-engine inliner cannot
    unfold, bailing the caller to UNKNOWN) and provably trap free standalone, so they can be inlined as a
    trap-free opaque result. Each is verified by the recursion engine with a trivial postcondition, so a PROVED
    is exactly trap freedom -- restricted to a callee whose parameters are all integers, where the recursion
    engine's integer model is sound (a container / string parameter it int-models could vacuously prove, so it
    is skipped, leaving the caller UNKNOWN). Returns the (possibly empty) frozenset of such callee names."""
    if not repo:
        return frozenset()
    edges = {k: _called_repo_names(repo[k], repo) for k in repo}
    reach, stack = set(), list(_called_repo_names(src, repo))
    while stack:                                                  # the transitive callees of src
        k = stack.pop()
        if k in reach or k not in repo:
            continue
        reach.add(k)
        stack.extend(edges.get(k, set()) - reach)
    triv = lambda S: z3.BoolVal(True)
    out = set()
    for g in reach:
        if g not in edges.get(g, set()) or not _all_int_params(repo[g]):
            continue                                             # not self-recursive, or a non-integer parameter
        try:
            v = verify_recursive("tf", g, repo[g], triv, lambda S, r: z3.BoolVal(True))
        except Exception:
            v = None
        if v is not None and v.status == PROVED:                 # the recursion engine proved it trap free
            out.add(g)
    return frozenset(out)


def _trap_witness(src, pre_node, spec, repo):
    """A concrete input on which `src` reaches a trap, found by the exact value engine, as
    ({name: value} dict, formatted string) -- or (None, None) when the value engine over-approximates (a
    havoc'd loop, a surviving None) so a model need not be a real input, or cannot model the body. With no
    havoc the symbolic execution is exact, so a model of the trap condition is a genuine trapping input."""
    try:
        from .domains import _infer_param_kinds
        kinds = _infer_param_kinds(_fndef(src))
    except Exception:
        kinds = None
    ctx = Ctx(repo or {}); ctx.facts = []; ctx.track_trap_lines = True
    saved = core._TRAPFREE; core._TRAPFREE = True
    try:
        args, z3args, _rets, traps, _none = symexec(src, ctx, param_kinds=kinds)
        pre_term = ev_bool(pre_node, dict(z3args), spec)
    except Exception:
        return None, None, None
    finally:
        core._TRAPFREE = saved
    if not traps or ctx.havoc or getattr(ctx, "none_havoc", False) or getattr(ctx, "overapprox", False):
        return None, None, None                                   # over-approx / havoc: a model is not a guaranteed witness
    claim = z3.And(pre_term, *ctx.facts, z3.Or(*traps)) if ctx.facts else z3.And(pre_term, z3.Or(*traps))
    st, model = _solve(claim)
    if st != REFUTED or model is None:
        return None, None, None
    model = minimize_witness(claim, z3args, args) or model        # the smallest triggering input
    trap_info = _firing_trap_info(src, traps, model)              # the firing trap's exception type and line
    try:                                                          # only scalar (int/bool/str/float) params yield a
        cex_str, cex_in = _model_cex(model, z3args, args)         # replayable value; a dict/list param has no model
    except Exception:                                            # value here, so report no witness rather than crash
        return None, None, None
    return cex_in, cex_str, trap_info


def _trap_type_at_line(src, line):
    """The modeled exception type a trap on `line` raises, read statically from the line's AST: an explicit
    raise names its exception, an assert is AssertionError, a division is ZeroDivisionError, a subscript is
    KeyError (a string key) or IndexError, else None. Best-effort -- the line is exact, the type its likely kind."""
    try:
        mod = ast.parse(textwrap.dedent(src))
    except SyntaxError:
        return None
    nodes = [n for n in ast.walk(mod) if getattr(n, "lineno", None) == line]
    for n in nodes:
        if isinstance(n, ast.Raise):
            exc = n.exc.func if isinstance(n.exc, ast.Call) else n.exc
            return exc.id if isinstance(exc, ast.Name) else "an exception"
        if isinstance(n, ast.Assert):
            return "AssertionError"
    for n in nodes:
        if isinstance(n, ast.BinOp) and isinstance(n.op, (ast.FloorDiv, ast.Mod, ast.Div)):
            return "ZeroDivisionError"
    for n in nodes:
        if isinstance(n, ast.Subscript):
            sl = n.slice
            return "KeyError" if (isinstance(sl, ast.Constant) and isinstance(sl.value, str)) else "IndexError"
    return None


def _firing_trap_info(src, traps, model):
    """'TYPE at line N' for the first trap condition the witness model satisfies, or None. The line is exact
    (recorded per condition by the value engine's trap list); the type is read statically from that line."""
    lines = getattr(traps, "lines", None)
    if not lines:
        return None
    for cond, ln in zip(traps, lines):
        try:
            if ln is not None and z3.is_true(model.eval(cond, model_completion=True)):
                return "%s at line %d" % (_trap_type_at_line(src, ln) or "a modeled trap", ln)
        except z3.Z3Exception:
            continue
    return None


def _trap_info_for_witness(src, pre_node, spec, repo, witness):
    """'TYPE at line N' for the trap a known witness reaches, by re-running the value engine with line tracking
    and substituting the witness into each trap condition -- so a refutation from any engine (not only the
    value engine) names the exception type and offending line symbolically. None when the value engine cannot
    model the body or no trap resolves under the witness."""
    if not witness:
        return None
    try:
        from .domains import _infer_param_kinds
        kinds = _infer_param_kinds(_fndef(src))
    except Exception:
        kinds = None
    ctx = Ctx(repo or {}); ctx.facts = []; ctx.track_trap_lines = True
    saved = core._TRAPFREE; core._TRAPFREE = True
    try:
        args, z3args, _r, traps, _n = symexec(src, ctx, param_kinds=kinds)
    except Exception:
        return None
    finally:
        core._TRAPFREE = saved
    if not getattr(traps, "lines", None) or not traps:
        return None
    try:
        pre_term = ev_bool(pre_node, dict(z3args), spec)
    except Exception:
        pre_term = z3.BoolVal(True)
    eqs = []                                                      # pin the scalar parameters to the witness
    for a in args:
        za, w = z3args.get(a), witness.get(a)
        if a not in witness or not z3.is_expr(za):
            continue
        if isinstance(w, bool):
            eqs.append(za == z3.BoolVal(w))
        elif isinstance(w, int) and z3.is_int(za):
            eqs.append(za == z3.IntVal(w))
        elif isinstance(w, str) and za.sort() == z3.StringSort():
            eqs.append(za == z3.StringVal(w))
    try:
        st, model = _solve(z3.And(pre_term, *eqs, z3.Or(*traps)))   # a witness-consistent model that fires a trap
    except z3.Z3Exception:
        return None
    if st != REFUTED or model is None:                            # _solve REFUTED == the claim is satisfiable
        return None
    return _firing_trap_info(src, traps, model)


def _bmc_trap_witness(src, pre_node, spec, repo, k=24):
    """A concrete trapping input for a single-loop function, by bounded unrolling -- the witness the havoc'd
    value engine (_trap_witness) cannot give for a loop. Execute the first k iterations exactly (no havoc),
    collecting every trap condition under the exact path that reaches it -- a body trap under `guard held so
    far`, a post-loop return trap under `guard fails now` -- then solve `pre AND some trap` for an input that
    fires one. Returns ({name: value}, formatted string) or (None, None). Sound: the unrolling introduces no
    over-approximation (it bails if any creeps in), so a model is a real input whose execution reaches that
    trap within k iterations. Incomplete: a trap first reachable only after more than k iterations is missed."""
    try:
        fn, args, init, loop, ret = _parse_single_loop(src)
    except Exception:
        return None, None
    if loop is None:
        return None, None
    ctx = Ctx(repo or {}); ctx.traps = []; ctx.facts = []
    saved = core._TRAPFREE; core._TRAPFREE = True
    try:
        base = {a.arg: _param_term(a) for a in fn.args.args}      # one typed term per parameter
        ctx.pc = z3.BoolVal(True)
        cur = _apply_assigns(init, base, ctx, raise_is_trap=True) # the straight-line prelude (a guarded raise here --
        #                                                          input validation before the loop -- is a witness)
        reached = z3.BoolVal(True)                                # "the guard held through every earlier iteration"
        for _ in range(k):
            ctx.pc = reached
            g = ev_bool(loop.test, cur, ctx)                      # guard, evaluated while still in the loop
            if ret is not None:
                ctx.pc = z3.And(reached, z3.Not(g))               # exit here -> the post-loop return runs on this state
                ev(ret.value, cur, ctx)                           # its traps, under the exact exit condition
            ctx.pc = z3.And(reached, g)                           # the body runs only if the guard held now
            cur = _apply_assigns(loop.body, cur, ctx, raise_is_trap=True)   # a raise in the body is reachable too
            reached = z3.And(reached, g)
    except Exception:
        return None, None
    finally:
        core._TRAPFREE = saved
    if ctx.havoc or getattr(ctx, "none_havoc", False) or getattr(ctx, "overapprox", False) or not ctx.traps:
        return None, None                                         # an over-approximation slipped in: a model is not a witness
    pre_term = ev_bool(pre_node, dict(base), spec)
    claim = z3.And(pre_term, *ctx.facts, z3.Or(*ctx.traps)) if ctx.facts else z3.And(pre_term, z3.Or(*ctx.traps))
    st, model = _solve(claim)
    if st != REFUTED or model is None:
        return None, None
    model = minimize_witness(claim, base, args) or model         # the smallest triggering input
    try:
        cex_str, cex_in = _model_cex(model, base, args)
    except Exception:
        return None, None
    if not cex_in or any(a not in cex_in for a in args):          # a non-scalar param yields no replayable value
        return None, None
    return cex_in, cex_str


def _sandbox_first_trap(fn, src, repo, requires, prefer=None, trials=48, seed=20240916):
    """Sample precondition-satisfying inputs for a plain-positional-parameter function (an optional `prefer`
    witness tried first), run the real function in the isolated sandbox, and return ({name: value},
    exception_name) for the first input that raises a modeled trap (ZeroDivision / Index / Key / Type / Value
    / Assertion), else (None, None). The shared core of check's interprocedural oracle and scan's
    finding-confirmation; the sampled values are built-in types so they cross the sandbox boundary cleanly."""
    params = [a.arg for a in fn.args.args]
    if params and params[0] in ("self", "cls"):                  # a method receiver cannot be sampled standalone:
        return None, None                                        # a trap on an int self is a type artifact, not a bug
    try:
        from .domains import _infer_param_kinds
        kinds = _infer_param_kinds(fn)                            # usage-inferred kind of each unannotated parameter
    except Exception:
        kinds = {}
    rng = random.Random(seed)

    def _samp(a):                                                 # one built-in-typed value per parameter, matching
        ann = a.annotation.id if isinstance(a.annotation, ast.Name) else None   # the annotation or the inferred kind so
        kind = kinds.get(a.arg)                                   # a string/list parameter is not sampled as an int
        if ann == "list" or kind in ("seq", "container"):        # (which would TypeError -- a confirmation artifact)
            return [rng.randint(-9, 9) for _ in range(rng.randint(0, 4))]
        if ann == "tuple":
            return tuple(rng.randint(-9, 9) for _ in range(rng.randint(0, 4)))
        if ann == "dict" or kind == "dict":
            return {rng.randint(-4, 4): rng.randint(-9, 9) for _ in range(rng.randint(0, 3))}
        if ann == "str" or kind == "str":
            return "".join(rng.choice("ab 0") for _ in range(rng.randint(0, 4)))
        if ann == "float":
            return rng.choice([0.0, 1.0, -1.0, 2.5, rng.uniform(-50.0, 50.0)])
        if ann == "bool":
            return rng.random() < 0.5
        return rng.choice([0, 0, 1, -1, 2, 7, rng.randint(-64, 64)])   # int / unannotated: 0 hits div/mod traps

    samples = []
    if prefer and all(p in prefer for p in params) \
            and all(isinstance(prefer[p], (int, float, bool, str)) for p in params):
        samples.append({p: prefer[p] for p in params})           # the engine's own witness, replayed first
    if not params:
        samples.append({})
    else:
        int_like = all((a.annotation is None or (isinstance(a.annotation, ast.Name) and a.annotation.id == "int"))
                       and kinds.get(a.arg) not in ("seq", "container", "str", "dict")
                       for a in fn.args.args)
        if int_like and len(params) <= 4:                        # an integer boundary grid: the corner inputs
            import itertools                                      # that trap (0, +-1, equal arguments) hit for sure
            for combo in itertools.product((0, 1, -1, 2, -2), repeat=len(params)):
                samples.append(dict(zip(params, combo)))
        for _ in range(trials):
            samples.append({a.arg: _samp(a) for a in fn.args.args})

    pre_ok = lambda s: True
    if requires.strip() != "True":                              # keep only the inputs the precondition admits
        try:
            code = compile(textwrap.dedent(requires), "<requires>", "eval")
        except SyntaxError:
            return None, None
        g = {"__builtins__": {"abs": abs, "min": min, "max": max, "len": len, "int": int, "bool": bool}}
        pre_ok = lambda s, _c=code, _g=g: bool(eval(_c, _g, dict(s)))

    kept = []
    for s in samples:
        try:
            if pre_ok(s):
                kept.append(s)
        except Exception:
            continue                                            # a sample the precondition cannot evaluate on: skip
    if not kept:
        return None, None
    inputs = [[s[a] for a in params] for s in kept]
    res = core.sandbox_run_batch_typed(src, repo or {}, fn.name, inputs)
    if res is None:
        return None, None
    for s, r in zip(kept, res):
        if r[0] == "raise" and r[1] in core._MODELED_TRAP_NAMES:   # a real, reachable modeled trap
            return dict(s), r[1]
    return None, None


def _oracle_trap_refute(src, requires, repo):
    """Concrete-execution trap refutation for check, for the interprocedural gap where the symbolic inliner
    bails (a recursive callee, e.g. f's `// gcd(...)` where gcd recurses): sample inputs, run the real function
    in the isolated sandbox, and return the first that raises a modeled trap as ({name: value}, "name=value,
    ..."), so a REFUTED over it is sound. (None, None) when no trap is found or execution is disabled."""
    if not (core.SANDBOX_SUBJECT or core.ALLOW_SUBJECT_EXECUTION):
        return None, None
    try:
        fn = _fndef(src)
    except Unsupported:
        return None, None
    if fn.args.vararg or fn.args.kwarg or fn.args.kwonlyargs or fn.args.posonlyargs or not fn.args.args:
        return None, None
    w, _exc = _sandbox_first_trap(fn, src, repo, requires)
    if w is None:
        return None, None
    return w, ", ".join("%s=%s" % (a.arg, w[a.arg]) for a in fn.args.args)


class _RaiseStripper(ast.NodeTransformer):
    """Replace every `raise` with a bare `return`, so re-checking trap freedom isolates the failures that are
    NOT explicit raises. A `return` (like `raise`) terminates the path, so a raise that guards a later operation
    (`if x == 0: raise; return 10 // x`) still excludes the trapping input. What remains REFUTED is a genuine
    operation crash."""
    def visit_Raise(self, node):
        return ast.copy_location(ast.Return(value=None), node)


def _strip_raises(src):
    tree = _RaiseStripper().visit(_parse(src))
    ast.fix_missing_locations(tree)
    return ast.unparse(tree)


class _AssertStripper(ast.NodeTransformer):
    """Rewrite `assert c` to `if not c: return None`: drops the AssertionError, keeps the guard on later code."""
    def visit_Assert(self, node):
        guard = ast.If(test=ast.UnaryOp(op=ast.Not(), operand=node.test),
                       body=[ast.Return(value=None)], orelse=[])
        return ast.copy_location(guard, node)


def _strip_guards(src):
    """The source with raises and asserts rewritten to guarding returns (see _RaiseStripper, _AssertStripper)."""
    tree = _AssertStripper().visit(_RaiseStripper().visit(_parse(src)))
    ast.fix_missing_locations(tree)
    return ast.unparse(tree)


def _classify_partiality(target, src, requires, repo, reason):
    """Annotate a REFUTED trap-freedom reason as a likely bug or intended input validation. A function with no
    raise or assert can only fail on an operation trap (a crash). Otherwise re-check a variant with each raise
    and assert rewritten to a guarding return: trap-free means the guard was the only failure (validation), a
    remaining trap means a real crash. The re-check goes through the full check path, so a container/string trap
    is decided; the stripped variant has no guards, so the recursion is one level deep. The verdict stays
    REFUTED; an undecided variant leaves the reason unchanged."""
    try:
        fn = _parse(src)
    except Exception:
        return reason
    if not any(isinstance(n, (ast.Raise, ast.Assert)) for n in ast.walk(fn)):
        kind = "likely a bug (a reachable operation trap, no explicit raise or assert to excuse it)"
    else:
        try:
            v2 = check(_strip_guards(src), requires=requires, repo=repo, target=target)
        except Exception:
            return reason
        if v2.status == PROVED:
            kind = "likely intended input validation (an explicit raise or assert; trap free once it is removed)"
        elif v2.status == REFUTED:
            kind = "likely a bug (an operation still traps with the explicit raises and asserts removed)"
        else:
            return reason
    return (reason + "; " + kind) if reason else kind


def _dispatch_annotated_methods(src, target, repo):
    """(src, repo) variants dispatching o.method(args) on a class-annotated parameter o: C to a concrete instance
    method body -- one variant per candidate class K in {C} and its module subclasses, since the receiver could
    be any subclass. A trap in any reachable body then refutes; upgrade-only at the call site."""
    try:
        tree = _parse(src)
    except SyntaxError:
        return []
    classes = {n.name: n for n in tree.body if isinstance(n, ast.ClassDef)}
    fn = next((n for n in tree.body
               if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name == target), None)
    if not classes or fn is None:
        return []
    param_class = {a.arg: a.annotation.id for a in fn.args.args
                   if isinstance(a.annotation, ast.Name) and a.annotation.id in classes}
    if not param_class:
        return []

    def subclasses(cname):                                   # cname and every module class with it as an ancestor
        out = {cname}
        while True:
            grew = {s for s, n in classes.items() if s not in out
                    and any(isinstance(b, ast.Name) and b.id in out for b in n.bases)}
            if not grew:
                return out
            out |= grew

    def method_of(cname, mname):                             # a regular instance method along the module MRO
        seen, stack = set(), [cname]
        while stack:
            c = stack.pop()
            if c in seen or c not in classes:
                continue
            seen.add(c)
            for s in classes[c].body:
                if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef)) and s.name == mname:
                    if any(isinstance(d, ast.Name) and d.id in ("staticmethod", "classmethod", "property")
                           for d in s.decorator_list):
                        return None
                    ps = s.args.args
                    return s if (ps and ps[0].arg in ("self", "cls")) else None
            stack.extend(b.id for b in classes[c].bases if isinstance(b, ast.Name))
        return None

    variants = []
    for pname, cname in param_class.items():
        for k in subclasses(cname):                          # the receiver o: C could be C or any subclass
            added = {}

            class _Rw(ast.NodeTransformer):
                def visit_Call(self, node, _p=pname, _k=k, _a=added):
                    self.generic_visit(node)
                    f = node.func
                    if (isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id == _p
                            and not node.keywords and not any(isinstance(a, ast.Starred) for a in node.args)):
                        m = method_of(_k, f.attr)
                        if m is not None:
                            key = "__ts_disp_%s_%s" % (_k, f.attr)
                            if key not in _a:
                                dm = copy.deepcopy(m); dm.name = key; dm.decorator_list = []
                                _a[key] = ast.unparse(ast.fix_missing_locations(dm))
                            return ast.copy_location(ast.Call(func=ast.Name(id=key, ctx=ast.Load()),
                                                              args=[ast.Name(id=_p, ctx=ast.Load())] + node.args,
                                                              keywords=[]), node)
                    return node

            newfn = _Rw().visit(copy.deepcopy(fn))
            if not added:
                continue
            newtree = copy.deepcopy(tree)
            newtree.body = [newfn if (isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name == target)
                            else n for n in newtree.body]
            new_repo = dict(repo); new_repo.update(added)
            variants.append((ast.unparse(ast.fix_missing_locations(newtree)), new_repo))
    return variants


def check(src, requires="True", repo=None, total=False, prop="implicit", target=None, best_effort=False) -> Verdict:
    """Verify a function with no externally supplied property: mine the contracts the code already
    states. Every `assert` in the body becomes an obligation (it must hold on all inputs the optional
    precondition admits), and reaching a division by zero or other trap is itself a failure, so the
    function is proved free of failing assertions and traps. With total=True the function must also
    terminate. The property is taken from the code, so the caller supplies only the precondition (if
    any) and what they want proven."""
    _require_str("src", src); _require_str("requires", requires); _require_repo(repo)
    if best_effort and not core.BEST_EFFORT:                  # opt-in lower-trust run (off by default)
        saved = core.BEST_EFFORT; core.BEST_EFFORT = True
        core.BEST_EFFORT_ASSUMED = False                      # taint: was a best-effort assumption actually used?
        try:
            v = check(src, requires, repo, total, prop, target)
            return _label_best_effort(v, core.BEST_EFFORT_ASSUMED)
        finally:
            core.BEST_EFFORT = saved
    return _escalate_budget(lambda: _check_core(src, requires, repo, total, prop, target))


def _check_core(src, requires, repo, total, prop, target):
    repo = repo or {}
    src = core._strip_async(src)                                 # an async function: mine the asserts and traps its
    #                                                              awaited coroutine reaches (await e -> e); see prove
    _top = _parse(src).body
    _fns = [n for n in _top if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    target = target or (_fns[0].name if _fns else "f")
    _deco = _inline_decorators(src, target, repo)                # a non-identity decorator: check what it produces
    if _deco is not None:
        src, repo = _deco
        _fns = [n for n in _parse(src).body if isinstance(n, ast.FunctionDef)]
    else:
        _tfn = next((n for n in _fns if n.name == target), None)
        if _tfn is not None and _tfn.decorator_list and _has_unmodeled_decorator(_tfn, {n.name: n for n in _fns}):
            return Verdict(UNKNOWN, prop, target, "implicit contracts",
                           reason="unresolved decorator: the callable it produces is not modeled")
    _heap_src = src                                              # pre-rewrite source (classes intact) for the heap fallback
    if not repo:                                                 # a single non-aliased local object with a constant
        _objrw = _rewrite_single_object(src, target)             # __init__: rewrite o.attr to plain variables so a
        if _objrw is not None:                                   # loop mutating object state is triaged for traps
            src = _objrw                                         # (a div by an object attribute that can be 0, etc.)
            _fns = [n for n in _parse(src).body if isinstance(n, ast.FunctionDef)]
    src = _isolate_target(src, _fns, target)                     # a multi-function module: check `target` alone
    spec = Ctx(repo); spec.traps = None; spec.pc = z3.BoolVal(True)
    try:
        pre_node = core.parse_spec(requires)
    except SyntaxError as e:
        return Verdict(UNKNOWN, prop, target, "implicit contracts", reason=f"precondition syntax: {e}")
    pre_node = _strip_old(pre_node)
    pre_fn = lambda S: ev_bool(pre_node, dict(S), spec)
    safe = verify_no_raise(prop, target, src, pre_fn, repo)        # asserts and traps are escaping raises
    if safe.status == UNKNOWN and _mentions_none(src):            # carry None through the loop as an Opt value, so
        opt = verify_no_raise_optional(prop, target, src, pre_node, repo)   # a None reaching arithmetic refutes
        if opt.status != UNKNOWN:                                 # instead of abstaining (and a havoc cannot
            safe = opt                                           # unsoundly turn a surviving None into an int)
    if safe.status == UNKNOWN:                                     # a construct the CFG checker declines
        alt = _check_trapfree_symexec(prop, target, src, pre_node, spec, repo, requires.strip() != "True")
        if alt.status != UNKNOWN:                                  # (e.g. a local dict built then read)
            safe = alt
    # _called_repo_names and _is_self_recursive each walk the whole function, and the trap-freedom fallbacks
    # below consult them up to three times on this unchanged src; memoize each to one lazy computation (a
    # function decided above never pays for them).
    _crn_cache, _sr_cache = [], []

    def _called_names():
        if not _crn_cache:
            _crn_cache.append(_called_repo_names(src, repo))
        return _crn_cache[0]

    def _self_rec():
        if not _sr_cache:
            _sr_cache.append(_is_self_recursive(src))
        return _sr_cache[0]
    if safe.status == UNKNOWN and _called_names():
        # the value engine bailed inlining a recursive callee; when that callee is itself trap free, inline it
        # as a trap-free result and re-run, so the caller decides symbolically instead of staying UNKNOWN.
        _tfc = _trapfree_recursive_callees(src, repo)
        if _tfc:
            alt = _check_trapfree_symexec(prop, target, src, pre_node, spec, repo,
                                          requires.strip() != "True", trapfree_callees=_tfc)
            if alt.status != UNKNOWN:
                safe = alt
    if safe.status == UNKNOWN and _self_rec():
        # the value engine bails on the recursive self-call, but the recursion engine decides trap freedom
        # symbolically (a reachable base-case or recursive-step trap is an Err under the call's path condition),
        # so it refutes even with a leading import that would block the sandbox oracle. Take only its REFUTED;
        # a container recursion it int-models could vacuously "prove", so a PROVED there is left to the flow.
        _rpre = (lambda P: z3.BoolVal(True)) if requires.strip() == "True" else pre_fn
        try:
            _rrec = verify_recursive(prop, target, src, _rpre, lambda S, r: z3.BoolVal(True))
        except Exception:
            _rrec = None
        if _rrec is not None and _rrec.status == REFUTED:
            safe = _rrec
    if safe.status == UNKNOWN and (_called_names() or _self_rec()):
        # before the sandbox oracle: bounded symbolic unrolling of the caller and its (recursive) callees
        # reaches the trap through an un-inlinable callee, taking a witness only on a fully-unrolled (exact)
        # path -- so the recursive-callee trap (f's `x // gcd(...)`, a callee whose base case traps) refutes.
        _iin, _icex = _interproc_bmc_witness(src, pre_node, spec, repo)
        if _iin is not None:
            safe = Verdict(REFUTED, prop, target, "implicit contracts (interprocedural unrolling)",
                           counterexample=_icex, counterexample_inputs=_iin,
                           reason="a modeled trap is reachable through an un-inlinable callee (bounded symbolic unrolling)")
    if safe.status == UNKNOWN and (_called_names() or _self_rec()):
        # every symbolic engine abstained on a function whose callee the inliner could not resolve (a recursive
        # callee, e.g. f's `// gcd(...)`, or self-recursion): the isolated sandbox decides a reachable trap the
        # engines could not. Silent when execution is disabled, so a symbolic run still never runs the subject.
        tin, tcex = _oracle_trap_refute(src, requires, repo)
        if tin is not None:
            safe = Verdict(REFUTED, prop, target, "implicit contracts (interprocedural concrete trap)",
                           counterexample=tcex, counterexample_inputs=tin,
                           reason="a modeled trap is reachable through an un-inlinable callee on a concrete input")
    if safe.status == UNKNOWN and not repo and any(isinstance(n, ast.ClassDef) for n in _parse(_heap_src).body):
        # object state across the method lifecycle: a function that constructs a local object and calls
        # value-returning methods on it (which the object rewrite declines) is triaged by the heap engine, which
        # threads attribute state through dispatch. Precise (loop-free), so its PROVED/REFUTED is taken directly.
        hv = verify_heap_property(prop, target, _heap_src, lambda za, r: z3.BoolVal(True))
        if hv.status in (PROVED, REFUTED):
            safe = hv
    if safe.status == PROVED:                                     # a method call on a class-annotated parameter was
        for _dsrc, _drepo in _dispatch_annotated_methods(src, target, repo):   # dispatch to the visible method body
            _dv = check(_dsrc, requires=requires, repo=_drepo, target=target)   # (and each subclass override) -- a trap
            if _dv.status == REFUTED:                            # there refutes the false PROVED with a plain-receiver
                safe = _dv; break                                # witness. Upgrade only; never regresses a verdict.
    if safe.status != PROVED or not total:
        cex, cex_in = safe.counterexample, safe.counterexample_inputs
        trap_info = None
        if safe.status == REFUTED and not cex_in:                 # a trap-freedom refutation without a witness:
            cex_in, cex, trap_info = _trap_witness(src, pre_node, spec, repo)   # the trapping input and its trap (type, line)
            if not cex_in:                                        # a loop the value engine havocs: unroll it instead
                cex_in, cex = _bmc_trap_witness(src, pre_node, spec, repo)
        if safe.status == REFUTED and cex_in and trap_info is None:   # a witness from another engine: name its trap too
            trap_info = _trap_info_for_witness(src, pre_node, spec, repo, cex_in)
        reason = safe.reason
        if safe.status == REFUTED:                                # label the partiality: input validation vs crash
            reason = _classify_partiality(target, src, requires, repo, reason)
            if trap_info:                                         # name the exception type and offending line, symbolically
                reason = "%s (%s)" % (reason, trap_info)
        return Verdict(safe.status, prop, target, "implicit contracts (asserts + trap freedom)",
                       counterexample=cex, reason=reason, counterexample_inputs=cex_in)
    term = verify_termination(prop, target, src, repo)
    if term.status == PROVED:
        return Verdict(PROVED, prop, target, "implicit contracts + termination", reason=term.reason)
    nonterm = verify_nontermination(prop, target, src, repo, pre=pre_fn)   # a diverging input is a totality bug
    if nonterm.status == REFUTED:
        return Verdict(REFUTED, prop, target, "implicit contracts + termination",
                       counterexample=nonterm.counterexample, counterexample_inputs=nonterm.counterexample_inputs,
                       reason=f"contracts hold but the loop provably does not terminate: {nonterm.reason}",
                       trace=nonterm.trace)   # the divergence certificate, not an unbounded diverging trace
    return Verdict(term.status, prop, target, "implicit contracts + termination",
                   reason=f"contracts hold but termination is {term.status}: {term.reason}")


_CONTRACT_DECORATORS = {"require", "ensure", "pre", "post"}


def _contract_conditions(fn):
    """Extract precondition and postcondition strings from a function's @require / @ensure (or
    @pre / @post) contract decorators, in the style of the contracts and icontract packages. A
    decorator's condition is a string argument (@require("x > 0")) or a lambda over the parameters
    and, for a postcondition, `result` (@ensure(lambda result, x: result >= x)). Returns
    (requires, ensures, contract_decorator_nodes)."""
    requires, ensures, decos = [], [], []
    for d in fn.decorator_list:
        if not isinstance(d, ast.Call) or not d.args:
            continue
        f = d.func
        name = f.attr if isinstance(f, ast.Attribute) else (f.id if isinstance(f, ast.Name) else None)
        if name not in _CONTRACT_DECORATORS:
            continue
        arg = d.args[0]
        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
            cond = arg.value
        elif isinstance(arg, ast.Lambda):
            cond = ast.unparse(arg.body)
        else:
            continue
        (requires if name in ("require", "pre") else ensures).append(cond)
        decos.append(d)
    return requires, ensures, decos


def verify_contracts(src, repo=None, prop="contract", target=None) -> Verdict:
    """Verify a function carrying @require / @ensure contract decorators (the contracts / icontract
    style): the require conditions become the precondition and the ensure conditions the
    postcondition over the parameters and `result`, and the function is proved against them by the
    same engine prove() uses, so an ordinary decorated function is itself the specification. UNKNOWN
    if there is no function or no postcondition to check."""
    _require_str("src", src); _require_repo(repo)
    mod = ast.parse(textwrap.dedent(src))
    fns = [n for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    fn = next((n for n in fns if n.name == target), None) if target else (fns[0] if fns else None)
    if fn is None:
        return Verdict(UNKNOWN, prop, target or "f", "contracts", reason="no function definition")
    target = fn.name
    requires, ensures, decos = _contract_conditions(fn)
    if not ensures:
        return Verdict(UNKNOWN, prop, target, "contracts", reason="no @ensure postcondition to verify")
    fn.decorator_list = [d for d in fn.decorator_list if d not in decos]   # strip the contract decorators
    stripped = ast.unparse(fn)
    pre_s = " and ".join(f"({c})" for c in requires) if requires else "True"
    post_s = " and ".join(f"({c})" for c in ensures)
    return prove(stripped, post_s, requires=pre_s, repo=repo, prop=prop, target=target)


def verify_all(src, repo=None):
    """Verify every function in `src` that carries an @ensure contract, returning a list of
    (function name, Verdict); functions without a postcondition are skipped. Lets a whole module's
    contracts be checked at once -- the pytest plugin builds on this."""
    out = []
    for n in ast.parse(textwrap.dedent(src)).body:
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _, ensures, _ = _contract_conditions(n)
            if ensures:
                out.append((n.name, verify_contracts(src, repo=repo, target=n.name)))
    return out


def _strip_contracts(fn):
    """The function's source with its @require / @ensure contract decorators removed, so the body is
    modeled directly rather than declined as a decorated function."""
    decos = _contract_conditions(fn)[2]
    fn.decorator_list = [d for d in fn.decorator_list if d not in decos]
    return ast.unparse(fn)


def verify_change(before, after, requires=None, ensures=None, func=None, repo=None) -> Verdict:
    """Confirm a proposed change preserves the properties the code states, so an AI-generated (or any)
    diff is checked before it is accepted. `before` and `after` are the two versions of one function. If
    `ensures` is given, or the before version carries an @ensure contract, the after version must satisfy
    that postcondition -- the change keeps its promise. Otherwise the after version must be behaviorally
    equivalent to the before version: a refactor that must not alter a returned value or add a trap. PROVED
    means the change is property-preserving; REFUTED returns an input where the after version breaks it."""
    _require_str("before", before); _require_str("after", after); _require_repo(repo)
    if requires is not None:
        _require_str("requires", requires)
    if ensures is not None:
        _require_str("ensures", ensures)
    repo = repo or {}

    def _pick(src):
        fns = [n for n in _parse(src).body if isinstance(n, ast.FunctionDef)]
        return next((n for n in fns if n.name == func), None) if func else (fns[0] if fns else None)

    bfn, afn = _pick(before), _pick(after)
    if afn is None:
        return Verdict(UNKNOWN, "change", func or "f", "change", reason="no function in the after version")
    target = afn.name
    pre, post = requires, ensures
    if post is None and bfn is not None:                          # mine the before version's @ensure contract
        breq, bens, _ = _contract_conditions(bfn)
        if bens:
            post = " and ".join("(%s)" % c for c in bens)
            if pre is None and breq:
                pre = " and ".join("(%s)" % c for c in breq)
    after_src = _strip_contracts(afn)
    if post is not None:                                         # a stated property: the change must keep meeting it
        return prove(after_src, post, requires=pre or "True", repo=repo,
                     prop="change preserves property", target=target)
    if bfn is None:
        return Verdict(UNKNOWN, "change", target, "change", reason="no before version to compare against")
    return verify_equiv("change preserves behavior", target, _strip_contracts(bfn), after_src, repo)


def change_bundle(before, after, requires=None, ensures=None, func=None, repo=None, label="change"):
    """Verify a change with verify_change and return a re-checkable proof bundle for it, so a verified diff
    carries its own evidence: a reviewer re-runs recheck_bundle to re-confirm the change is property-
    preserving, trusting only their own solver rather than the engine that produced it. The bundle is
    checkable when the change is PROVED through the SMT-query path (an equivalence or a loop-free contract);
    a CHC loop proof discharges an invariant rather than a single query and the bundle says so."""
    from .vcgen import proof_bundle
    return proof_bundle(lambda: verify_change(before, after, requires=requires, ensures=ensures,
                                              func=func, repo=repo), label=label)


def _repair_feedback(v, src, repo=None):
    """The structured repair signal returned to a generator after a non-PROVED verdict: the verdict, the unmet
    property, the counterexample inputs, and (for a REFUTED) the execution trace from explain."""
    fb = {"status": v.status, "property": v.prop, "reason": v.reason,
          "counterexample": v.counterexample, "counterexample_inputs": v.counterexample_inputs}
    if v.status == REFUTED:
        try:
            ev = explain(v, src, repo or {})
            if getattr(ev, "trace", None):
                fb["trace"] = ev.trace
        except Exception:
            pass
    return fb


def repair_loop(generate, ensures=None, requires="True", before=None, func=None, repo=None, max_rounds=5):
    """Drive a verification-guided repair loop for a code-generating model. `generate(feedback)` returns a
    candidate function source; `feedback` is None on the first round and, after a non-PROVED verdict, the
    structured signal from _repair_feedback (the failing input, the trace, the unmet property). Each candidate
    is verified against `ensures` (a postcondition), else the `before` version's contract or behavior
    (verify_change), else trap freedom (check). Iterates until PROVED or `max_rounds`. Returns {status, source,
    rounds, history, converged}."""
    feedback, src, v, history, seen = None, None, None, [], set()
    for rnd in range(1, max_rounds + 1):
        src = generate(feedback)
        if src in seen:                                    # the generator returned a candidate already tried: a
            return {"status": v.status if v else UNKNOWN, "source": src, "rounds": rnd,   # fixpoint, so the loop
                    "history": history, "feedback": feedback, "converged": True}          # has converged short of a
        #                                                    proof and further rounds cannot make progress
        seen.add(src)
        if ensures is not None:
            v = prove(src, ensures, requires=requires, repo=repo, target=func)
        elif before is not None:
            v = verify_change(before, src, requires=(requires if requires != "True" else None),
                              func=func, repo=repo)
        else:
            v = check(src, requires=requires, repo=repo, target=func)
        history.append({"round": rnd, "status": v.status, "source": src})
        if v.status == PROVED:
            return {"status": PROVED, "source": src, "rounds": rnd, "history": history, "converged": True}
        feedback = _repair_feedback(v, src, repo)
    return {"status": v.status if v else UNKNOWN, "source": src, "rounds": max_rounds,
            "history": history, "feedback": feedback, "converged": False}


def _spec_precond_candidates(params):
    out = []                                                # weakest templates first, so the first candidate that
    for p in params:                                        # makes the function trap free is its weakest precondition.
        out += ["%s != 0" % p, "%s >= 0" % p, "%s > 0" % p, "%s >= 1" % p, "len(%s) > 0" % p]   # != 0 and >= 0 are
    return out                                              # the two weakest and never both needed (their union is total)


def _body_int_constants(fn):
    """The integer constants appearing in a function body (a clamp's 0 / 100), used as candidate
    postcondition bounds so a synthesized spec can reach the function's own limits."""
    out = set()
    for n in ast.walk(fn):
        if isinstance(n, ast.Constant) and isinstance(n.value, int) and not isinstance(n.value, bool):
            out.add(n.value)
        elif (isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub)
              and isinstance(n.operand, ast.Constant) and isinstance(n.operand.value, int)):
            out.add(-n.operand.value)
    return out


def _spec_postcond_candidates(params, bounds=()):
    out = ["result >= 0", "result <= 0", "result > 0", "result < 0", "result == 0", "result != 0",
           "result == True", "result == False"]
    for c in sorted(bounds):                                    # the function's own integer bounds (clamp -> 0, 100)
        out += ["result >= %d" % c, "result <= %d" % c, "result == %d" % c]
    for p in params:
        out += ["result == %s" % p, "result >= %s" % p, "result <= %s" % p, "result > %s" % p,
                "result < %s" % p, "result == %s + 1" % p, "result == %s - 1" % p, "result == -%s" % p,
                "result == 2 * %s" % p, "result == %s * %s" % (p, p)]
    return out


def _prune_ensures(ens, params):
    import re
    e = set(ens)                                                # drop a postcondition a stronger one implies

    def nums(rel):                                              # the integer constants in `result REL N` clauses
        return [int(m.group(1)) for s in e
                for m in [re.fullmatch(r"result %s (-?\d+)" % re.escape(rel), s)] if m]
    los, his, eqs = nums(">="), nums("<="), nums("==")
    if los:                                                     # keep only the tightest numeric lower bound
        e -= {"result >= %d" % v for v in los if v != max(los)}
    if his:                                                     # and the tightest numeric upper bound
        e -= {"result <= %d" % v for v in his if v != min(his)}
    if eqs:                                                     # result == N pins both bounds: drop the looser ones
        e -= {"result >= %d" % v for v in los} | {"result <= %d" % v for v in his}
    if "result > 0" in e:
        e -= {"result >= 0", "result != 0"}
    if "result < 0" in e:
        e -= {"result <= 0", "result != 0"}
    if "result == 0" in e:
        e -= {"result >= 0", "result <= 0"}
    for p in params:
        if ("result == %s" % p) in e:
            e -= {"result >= %s" % p, "result <= %s" % p}
        if ("result == %s + 1" % p) in e:                       # result == p + 1 implies result > p
            e -= {"result > %s" % p, "result >= %s" % p}
        if ("result == %s - 1" % p) in e:                       # result == p - 1 implies result < p
            e -= {"result < %s" % p, "result <= %s" % p}
        if ("result > %s" % p) in e:
            e.discard("result >= %s" % p)
        if ("result < %s" % p) in e:
            e.discard("result <= %s" % p)
    return sorted(e)


def synthesize_spec(src, func=None, repo=None):
    """Propose a contract a function provably satisfies: a precondition (from a small candidate set) under which
    it is trap free if it is not already, and the postconditions over the parameters and result it provably
    meets. A sound, machine-checked starting spec for a repair loop or a review. Returns {requires, ensures}."""
    repo = repo or {}
    fns = [n for n in _parse(src).body if isinstance(n, ast.FunctionDef)]
    fn = next((n for n in fns if n.name == func), None) if func else (fns[0] if fns else None)
    if fn is None:
        return {"requires": "True", "ensures": []}
    target = fn.name
    params = [p.arg for p in fn.args.args]
    pre = "True"
    try:
        trapfree = check(src, repo=repo, target=target).status == PROVED
    except Exception:
        trapfree = True
    if not trapfree:                                            # find a precondition that makes it trap free
        for cand in _spec_precond_candidates(params):
            try:
                if check(src, requires=cand, repo=repo, target=target).status == PROVED:
                    pre = cand
                    break
            except Exception:
                continue
    bounds = set(_body_int_constants(fn))                       # the function's own constants, plus the inferred
    try:                                                        # @ret interval, so the spec can reach tight bounds
        from .domains import analyze_intervals, _NEG, _POS
        iv = (analyze_intervals(src) or {}).get("@ret")
        if iv is not None:
            if iv.lo != _NEG:
                bounds.add(iv.lo)
            if iv.hi != _POS:
                bounds.add(iv.hi)
    except Exception:
        pass
    ensures = []
    for cand in _spec_postcond_candidates(params, bounds):      # keep each postcondition it provably meets
        try:
            if prove(src, cand, requires=pre, repo=repo, target=target).status == PROVED:
                ensures.append(cand)
        except Exception:
            continue
    ensures = _prune_ensures(ensures, params)
    if len(ensures) > 1:                                        # confirm the conjunction is itself provable, not only
        conj = " and ".join("(%s)" % c for c in ensures)        # each clause -- the strongest contract it certifies
        try:
            if prove(src, conj, requires=pre, repo=repo, target=target).status != PROVED:
                ensures = ensures[:1]                           # independent proofs compose, so this is a safety net
        except Exception:
            pass
    return {"requires": pre, "ensures": ensures}


def _is_doctest_literal(node):
    """A scalar literal usable as a doctest argument or expected value: a constant (int / float / str / bool /
    None) or a unary +/- of a constant. A container is excluded -- its element types may not match the
    parameter's modeled sort, so it would only ever abstain."""
    if isinstance(node, ast.Constant):
        return True
    return (isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd))
            and isinstance(node.operand, ast.Constant))


def prove_doctests(src, repo=None, target=None):
    """Mine a function's doctests into prove obligations. Each interactive example whose call is the function
    applied to scalar literals and whose expected output is a scalar literal -- the `>>> f(2)` / `4` form, or
    `>>> f(2) == 4` / `True` -- becomes `prove(result == <expected>)` under the literal arguments. Returns a
    list of (example, Verdict); an example outside that shape is skipped."""
    import doctest as _doctest
    repo = repo or {}
    try:
        mod = _parse(src)
    except SyntaxError:
        return []
    fns = [n for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    fn = next((n for n in fns if n.name == target), None) if target else (fns[0] if fns else None)
    if fn is None:
        return []
    target = fn.name
    doc = ast.get_docstring(fn)
    if not doc:
        return []
    params = [a.arg for a in fn.args.args]
    out = []
    for ex in _doctest.DocTestParser().get_examples(doc):
        want = ex.want.strip()
        line = ex.source.strip()
        if not want:
            continue
        try:
            call = ast.parse(line, mode="eval").body
            wantnode = ast.parse(want, mode="eval").body
        except SyntaxError:
            continue
        negate = False
        if (isinstance(call, ast.Compare) and len(call.ops) == 1 and isinstance(call.ops[0], (ast.Eq, ast.NotEq))
                and want in ("True", "False")):                   # `>>> f(x) == v` / `True`
            negate = isinstance(call.ops[0], ast.NotEq) ^ (want == "False")
            callexpr, expected = call.left, call.comparators[0]
        else:                                                     # `>>> f(x)` / `v`
            callexpr, expected = call, wantnode
        if not (isinstance(callexpr, ast.Call) and isinstance(callexpr.func, ast.Name)
                and callexpr.func.id == target and not callexpr.keywords
                and len(callexpr.args) == len(params)
                and all(_is_doctest_literal(a) for a in callexpr.args)
                and _is_doctest_literal(expected)):
            continue
        reqs = " and ".join("%s == %s" % (p, ast.unparse(a)) for p, a in zip(params, callexpr.args)) or "True"
        ens = "result %s %s" % ("!=" if negate else "==", ast.unparse(expected))
        v = prove(src, ens, requires=reqs, repo=repo, prop="doctest", target=target)
        out.append((line + " -> " + want, v))
    return out


# annotation name -> the set of runtime type names it admits. `int` admits bool (a bool IS an int), so a
# bool return under an `-> int` annotation is not a mismatch.
_ANN_BUILTIN = {"int": {"int", "bool"}, "bool": {"bool"}, "float": {"float"}, "str": {"str"},
                "bytes": {"bytes"}, "complex": {"complex"}, "list": {"list"}, "dict": {"dict"},
                "set": {"set"}, "frozenset": {"frozenset"}, "tuple": {"tuple"}, "None": {"NoneType"}}


def _annotation_types(node):
    """The set of runtime type names a return annotation admits, or None when it is not a mappable builtin
    (a user class, Any, a callable type) -- in which case the check abstains rather than guess."""
    if isinstance(node, ast.Constant) and node.value is None:
        return {"NoneType"}
    if isinstance(node, ast.Name):
        return set(_ANN_BUILTIN[node.id]) if node.id in _ANN_BUILTIN else None
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):     # X | Y (PEP 604), incl. `int | None`
        a, b = _annotation_types(node.left), _annotation_types(node.right)
        return (a | b) if (a is not None and b is not None) else None
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
        base = node.value.id
        if base == "Optional":
            inner = _annotation_types(node.slice)
            return (inner | {"NoneType"}) if inner is not None else None
        if base == "Union":
            elts = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
            parts = [_annotation_types(e) for e in elts]
            return set().union(*parts) if parts and all(p is not None for p in parts) else None
        gen = {"list": "list", "List": "list", "dict": "dict", "Dict": "dict", "set": "set", "Set": "set",
               "frozenset": "frozenset", "FrozenSet": "frozenset", "tuple": "tuple", "Tuple": "tuple"}
        return {gen[base]} if base in gen else None
    return None


def _literal_type_name(node):
    """The runtime type name of a literal return value, or None when the value is not a literal."""
    if isinstance(node, ast.Constant):
        v = node.value
        if v is None:
            return "NoneType"
        for ty in (bool, int, float, complex, str, bytes):       # bool before int (bool is an int subclass)
            if isinstance(v, ty):
                return ty.__name__
    if isinstance(node, ast.JoinedStr):
        return "str"
    if isinstance(node, ast.List):
        return "list"
    if isinstance(node, ast.Dict):
        return "dict"
    if isinstance(node, ast.Set):
        return "set"
    if isinstance(node, ast.Tuple):
        return "tuple"
    return None


def _own_nodes(fn):
    """Every node in `fn`'s own scope, not descending into a nested function / lambda / class -- so a nested
    def's return does not count as the outer function's."""
    out, stack = [], list(fn.body)
    while stack:
        n = stack.pop()
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)):
            continue
        out.append(n)
        stack.extend(ast.iter_child_nodes(n))
    return out


def _always_returns_simple(body):
    """True iff every path through `body` reaches a return or raise, judged EXACTLY for straight-line code
    and if/else (a prefix statement that is a return/raise, or an if with both branches always-returning,
    guarantees it). Used only on bodies free of loops / try / match / with, where this is exact, so a False
    result soundly means the function can fall through to an implicit None."""
    for s in body:
        if isinstance(s, (ast.Return, ast.Raise)):
            return True
        if isinstance(s, ast.If) and s.orelse \
                and _always_returns_simple(s.body) and _always_returns_simple(s.orelse):
            return True
    return False


def check_return_annotation(src, repo=None, target=None) -> Verdict:
    """Compare a function's declared return annotation against what it can return. REFUTED on a concrete return
    of a type the annotation excludes: an explicit `return None` or a wrong-typed literal, or (where the control
    flow is simple enough to judge exactly) an implicit fall-through to None under a non-Optional annotation.
    PROVED when the sound inferred return type is within the annotation. UNKNOWN when there is no annotation, the
    annotation is not a mappable builtin, or neither direction is decided. A flag is always backed by a concrete
    offending return, never by the inferred set's over-approximation."""
    repo = repo or {}
    try:
        mod = _parse(src)
    except SyntaxError:
        return Verdict(UNKNOWN, "return-annotation", target or "f", "type/annotation", reason="syntax error")
    fns = [n for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    fn = next((n for n in fns if n.name == target), None) if target else (fns[0] if fns else None)
    if fn is None or fn.returns is None:
        return Verdict(UNKNOWN, "return-annotation", target or "f", "type/annotation", reason="no return annotation")
    target = fn.name
    allowed = _annotation_types(fn.returns)
    if allowed is None:
        return Verdict(UNKNOWN, "return-annotation", target, "type/annotation",
                       reason="annotation is not a mappable builtin type")
    annsrc = ast.unparse(fn.returns)
    for r in _own_nodes(fn):
        if not isinstance(r, ast.Return):
            continue
        tname = "NoneType" if r.value is None else _literal_type_name(r.value)
        if tname is not None and tname not in allowed:
            what = "returns None" if tname == "NoneType" else "returns a %s" % tname
            return Verdict(REFUTED, "return-annotation", target, "type/annotation", counterexample=what,
                           reason="%s but the annotation is %s" % (what, annsrc))
    complex_ctrl = any(isinstance(n, (ast.While, ast.For, ast.Try, ast.Match, ast.With)) for n in _own_nodes(fn))
    if "NoneType" not in allowed and not complex_ctrl and not _always_returns_simple(fn.body):
        return Verdict(REFUTED, "return-annotation", target, "type/annotation",
                       counterexample="falls through to None",
                       reason="can fall through to an implicit None but the annotation is %s" % annsrc)
    try:
        from .inference import infer_return_type
        s = infer_return_type(src, repo, target)
    except Exception:
        s = None
    if s is not None and set(s) <= allowed:
        return Verdict(PROVED, "return-annotation", target, "type/annotation",
                       reason="the sound inferred return type %s is within the annotation %s" % (sorted(s), annsrc))
    return Verdict(UNKNOWN, "return-annotation", target, "type/annotation",
                   reason="no definite mismatch, and the sound return type is not provably within the annotation")


def verify_metamorphic(src, relation="idempotent", target=None, repo=None) -> Verdict:
    """Verify an oracle-free metamorphic property of a unary function, needing no reference implementation:
    'idempotent' (f(f(x)) == f(x)) or 'involution' (f(f(x)) == x). The function is composed with itself and the
    equality is discharged over all inputs by the equivalence engine. PROVED holds for every input, REFUTED
    returns a witness, UNKNOWN for a non-unary function or an unsupported relation."""
    repo = repo or {}
    try:
        mod = _parse(src)
    except SyntaxError:
        return Verdict(UNKNOWN, "metamorphic", target or "f", "metamorphic", reason="syntax error")
    fns = [n for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    fn = next((n for n in fns if n.name == target), None) if target else (fns[0] if fns else None)
    if fn is None:
        return Verdict(UNKNOWN, "metamorphic", target or "f", "metamorphic", reason="no function definition")
    target = fn.name
    if (len(fn.args.args) != 1 or fn.args.vararg or fn.args.kwarg or fn.args.kwonlyargs or fn.args.posonlyargs):
        return Verdict(UNKNOWN, "metamorphic", target, "metamorphic",
                       reason="a metamorphic relation here needs a single-parameter function")
    if relation not in ("idempotent", "involution"):
        return Verdict(UNKNOWN, "metamorphic", target, "metamorphic", reason="unknown relation %r" % relation)
    p = fn.args.args[0].arg
    ann = (": " + ast.unparse(fn.args.args[0].annotation)) if fn.args.args[0].annotation is not None else ""
    try:
        fsrc = load_module(src).get(target) or ast.unparse(fn)
    except Exception:
        fsrc = ast.unparse(fn)
    repo2 = dict(repo); repo2[target] = fsrc
    lhs = "def __mm_lhs(%s%s):\n    return %s(%s(%s))\n" % (p, ann, target, target, p)
    rhs = ("def __mm_rhs(%s%s):\n    return %s(%s)\n" % (p, ann, target, p) if relation == "idempotent"
           else "def __mm_rhs(%s%s):\n    return %s\n" % (p, ann, p))
    return verify_equiv("metamorphic (%s)" % relation, "__mm_lhs", lhs, rhs, repo2)


def explain(verdict, src, repo=None) -> Verdict:
    """Enrich a REFUTED verdict with an execution trace: run the subject on the counterexample inputs
    in the sandbox, recording the path taken and the integer values live at each line, and return a
    new Verdict whose `.trace` holds that readable trace. A non-refuted verdict, one without concrete
    inputs, or an unavailable sandbox is returned unchanged, so this never fabricates a trace."""
    if verdict.status != REFUTED or not verdict.counterexample_inputs:
        return verdict
    try:
        fn = next(n for n in _parse(src).body if isinstance(n, ast.FunctionDef))
    except StopIteration:
        return verdict
    args = [a.arg for a in fn.args.args]
    inputs = verdict.counterexample_inputs
    if any(a not in inputs for a in args):
        return verdict
    res = core.sandbox_trace(src, repo or {}, fn.name, [inputs[a] for a in args])
    if res is None:
        return verdict
    outcome, steps, detail = res
    lines = textwrap.dedent(src).splitlines()
    out = ["at " + ", ".join(f"{a}={inputs[a]}" for a in args)]
    rows = []
    for lineno, loc in steps:
        srcline = lines[lineno - 1].strip() if 1 <= lineno <= len(lines) else "?"
        env = ", ".join(f"{k}={v}" for k, v in sorted(loc.items()))
        rows.append(f"  line {lineno}: {srcline}" + (f"    [{env}]" if env else ""))
    head, keep = 12, 8                                           # cap a long (looping / diverging) trace to a
    if len(rows) > head + keep + 1:                              # head-and-tail window with an explicit elision marker
        rows = rows[:head] + [f"  ... ({len(rows) - head - keep} steps elided) ..."] + rows[-keep:]
    out += rows
    tail = {"returned": f"returns {detail}", "raised": f"raises {detail}",
            "diverged": "did not terminate within the step budget",
            "setup_error": "could not run"}.get(outcome, outcome)
    out.append("  => " + tail)
    return Verdict(verdict.status, verdict.prop, verdict.target, verdict.technique,
                   counterexample=verdict.counterexample, reason=verdict.reason,
                   counterexample_inputs=verdict.counterexample_inputs, trace="\n".join(out))


def _inline_globals(fn, glob):
    """Prepend the read-only module globals (NAME = expr) that `fn` transitively reads, in module order."""
    params = {a.arg for a in fn.args.args} | {a.arg for a in fn.args.kwonlyargs}
    assigned = {n.id for n in ast.walk(fn) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
    used = {n.id for n in ast.walk(fn) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}
    need = {g for g in glob if g in used and g not in params and g not in assigned}
    changed = True
    while changed:                                           # pull in globals referenced by globals
        changed = False
        for g in list(need):
            for n in ast.walk(glob[g].value):
                if isinstance(n, ast.Name) and n.id in glob and n.id not in need:
                    need.add(n.id); changed = True
    fn.body = [glob[g] for g in glob if g in need] + fn.body


def load_module(src):
    """Build a repo {name: source} from a whole module or file: every top-level function becomes
    an entry, and module-level global constants (NAME = expr) are inlined (transitively) into the
    functions that read them, so a multi-function file with shared globals verifies directly
    instead of a hand-built per-function dict. Read-only globals; rebinding via `global` is out
    of scope."""
    mod = ast.parse(textwrap.dedent(src))
    glob = {a.targets[0].id: a for a in mod.body
            if isinstance(a, ast.Assign) and len(a.targets) == 1 and isinstance(a.targets[0], ast.Name)}
    modfns = {f.name: f for f in mod.body if isinstance(f, ast.FunctionDef)}

    def _identity_dec(dec):                                  # a decorator that returns its argument unchanged,
        if not isinstance(dec, ast.Name):                   # so applying it leaves the function's behavior intact
            return False
        d = modfns.get(dec.id)
        if d is None or len(d.args.args) != 1 or len(d.body) != 1:
            return False
        s = d.body[0]
        return (isinstance(s, ast.Return) and isinstance(s.value, ast.Name)
                and s.value.id == d.args.args[0].arg)

    repo = {}
    for fn in mod.body:
        if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if fn.decorator_list and all(_identity_dec(d) for d in fn.decorator_list):
            fn.decorator_list = []                           # identity decorators: the body is verified as-is.
        #                                                      A non-identity decorator is left in place, so the
        #                                                      front end declines (UNKNOWN) rather than verifying
        #                                                      a body the decorator may have replaced.
        _inline_globals(fn, glob)
        repo[fn.name] = ast.unparse(fn)
    return repo


def load_package(*sources):
    """Merge several module sources into one repo, so a whole repository verifies as one assembled
    system. Every top-level function across the modules becomes an entry and cross-module calls
    resolve by name; each module's own global constants are inlined into its functions first. A later
    module's function shadows an earlier one of the same name, as a real import would."""
    repo = {}
    for src in sources:
        repo.update(load_module(src))
    return repo


def _mangle(mod, fn):
    return mod.replace(".", "_") + "__" + fn


def _dotted(node):
    """The dotted name of a pure attribute/name chain (a.b.c -> 'a.b.c'), or None for anything else."""
    parts = []
    while isinstance(node, ast.Attribute):
        parts.append(node.attr)
        node = node.value
    if isinstance(node, ast.Name):
        parts.append(node.id)
        return ".".join(reversed(parts))
    return None


class _CallResolver(ast.NodeTransformer):
    """Rewrite the call sites in one module's function so a program-internal call names the mangled
    callee: a bare g() (a same-module function or a `from m import g [as g]`) and an attribute chain
    m.g() or pkg.sub.g() (an `import m`, `import pkg.sub [as x]`, or a relative import) both become
    <mod>__g(). A call to a function outside the program is left untouched, so the stdlib contracts and
    modular handling still apply to it."""
    def __init__(self, this_mod, modfuncs, name_imports, mod_imports):
        self.this_mod, self.modfuncs = this_mod, modfuncs
        self.name_imports, self.mod_imports = name_imports, mod_imports

    def visit_Call(self, node):
        self.generic_visit(node)
        f = node.func
        if isinstance(f, ast.Name):
            if f.id in self.name_imports:
                node.func = ast.Name(id=_mangle(*self.name_imports[f.id]), ctx=ast.Load())
            elif f.id in self.modfuncs.get(self.this_mod, ()):
                node.func = ast.Name(id=_mangle(self.this_mod, f.id), ctx=ast.Load())
        elif isinstance(f, ast.Attribute):                   # m.g() or pkg.sub.g(): the chain before the final
            full = _dotted(f)                                # attribute names an imported module (possibly dotted)
            if full and "." in full:
                modpart, _, fn = full.rpartition(".")
                tmod = self.mod_imports.get(modpart)
                if tmod and fn in self.modfuncs.get(tmod, ()):
                    node.func = ast.Name(id=_mangle(tmod, fn), ctx=ast.Load())
        return node


def _resolve_from(this_mod, node, trees, modfuncs, name_imports, mod_imports):
    """Resolve a from-import against the program's modules and record it: a function import in name_imports,
    a submodule import in mod_imports. Handles an absolute (`from pkg.sub import f`), a relative (`from .
    import g`, `from ..pkg import h`), and a star (`from m import *`) import; the relative form anchors at
    this module's package, dropping `level` trailing components of the importing module's dotted name."""
    if node.level:
        base = ".".join(this_mod.split(".")[:-node.level] + ([node.module] if node.module else []))
    else:
        base = node.module or ""
    for al in node.names:
        if al.name == "*":                                   # from base import *  -> every function of base
            for fn in modfuncs.get(base, ()):
                name_imports.setdefault(fn, (base, fn))
            continue
        sub = (base + "." + al.name) if base else al.name
        if sub in trees:                                     # from base import <submodule>
            mod_imports[al.asname or al.name] = sub
        elif al.name in modfuncs.get(base, ()):              # from base import <function>
            name_imports[al.asname or al.name] = (base, al.name)


def _rewrite_decorator(dec, this_mod, modfuncs, name_imports, mod_imports):
    """Rewrite a decorator to the mangled program-internal callee it names, so a decorated function survives
    load_program's name mangling and the decorator inliner resolves it: a bare @g / @deco (a same-module
    function or a from-import) and an attribute @m.deco (through `import m`) both become @<mod>__deco, and the
    factory forms @g(args) / @m.deco(args) rewrite their callee likewise. A decorator naming a function outside
    the program is left untouched, so the inliner declines it (UNKNOWN)."""
    def mangled(node):
        if isinstance(node, ast.Name):
            if node.id in name_imports:
                return _mangle(*name_imports[node.id])
            if node.id in modfuncs.get(this_mod, ()):
                return _mangle(this_mod, node.id)
        elif isinstance(node, ast.Attribute):
            full = _dotted(node)
            if full and "." in full:
                modpart, _, fn = full.rpartition(".")
                tmod = mod_imports.get(modpart)
                if tmod and fn in modfuncs.get(tmod, ()):
                    return _mangle(tmod, fn)
        return None
    if isinstance(dec, ast.Call):
        nm = mangled(dec.func)
        if nm is None:
            return dec
        return ast.copy_location(ast.Call(func=ast.Name(id=nm, ctx=ast.Load()),
                                          args=dec.args, keywords=dec.keywords), dec)
    nm = mangled(dec)
    return ast.copy_location(ast.Name(id=nm, ctx=ast.Load()), dec) if nm is not None else dec


def load_program(modules, on_collision="raise"):
    """Build a repo from a multi-module program {module_name: source}, resolving imports across the
    modules so a cross-module call inlines instead of being assumed well-behaved. Each function is
    mangled to a unique name <module>__<func>, and a same-module call, a `from m import g [as h]` (absolute,
    relative `from . import g`, dotted `from pkg.sub import g`, or star `from m import *`), and an attribute
    call through `import m [as m]` / `import pkg.sub` all rewrite to that name; each module's globals are
    inlined into its own functions. A call to a function outside the program is left to the stdlib contracts
    / modular handling. Returns {mangled_name: source}; verify a member with check / prove (repo[name],
    repo=repo, target=name), or use verify_program."""
    trees = {m: ast.parse(textwrap.dedent(src)) for m, src in modules.items()}
    modfuncs = {m: {f.name for f in t.body if isinstance(f, ast.FunctionDef)} for m, t in trees.items()}
    repo = {}
    for m, tree in trees.items():
        glob = {a.targets[0].id: a for a in tree.body
                if isinstance(a, ast.Assign) and len(a.targets) == 1 and isinstance(a.targets[0], ast.Name)}
        name_imports, mod_imports = {}, {}
        for node in tree.body:
            if isinstance(node, ast.ImportFrom):             # absolute / relative / dotted / star from-import
                _resolve_from(m, node, trees, modfuncs, name_imports, mod_imports)
            elif isinstance(node, ast.Import):
                for al in node.names:                        # import m [as mm]; import pkg.sub [as x]
                    if al.name in trees:
                        mod_imports[al.asname or al.name] = al.name
        resolver = _CallResolver(m, modfuncs, name_imports, mod_imports)
        for fn in tree.body:
            if isinstance(fn, ast.FunctionDef):
                resolver.visit(fn)
                fn.decorator_list = [_rewrite_decorator(d, m, modfuncs, name_imports, mod_imports)
                                     for d in fn.decorator_list]   # a cross-module decorator survives mangling
                _inline_globals(fn, glob)
                fn.name = _mangle(m, fn.name)
                if fn.name in repo:                          # two functions in sibling modules mangle alike (a rare
                    if on_collision == "skip":               # underscore-boundary coincidence): a best-effort scan
                        continue                             # keeps the first and skips the rest rather than crash;
                    raise ValueError(f"mangled name collision: {fn.name}")   # a rigorous verify still rejects it
                repo[fn.name] = ast.unparse(fn)
    return repo


def check_program(modules, module, func, requires="True", total=False):
    """Verify trap-freedom of `func` in `module` across the whole program in `modules`, inlining calls
    over the resolved cross-module call graph (see load_program). The companion load_program also feeds
    the Horn whole-program prover verify_program for contract proofs spanning module imports. Returns a
    Verdict."""
    repo = load_program(modules)
    key = _mangle(module, func)
    if key not in repo:
        return Verdict(UNKNOWN, f"{module}.{func}", func, "whole-program",
                       reason="no such function in the program")
    return check(repo[key], requires=requires, repo=repo, total=total, target=key, prop=f"{module}.{func}")


def _module_name(rel):
    """The dotted module name for a .py file path relative to a package root: pkg/sub/mod.py -> pkg.sub.mod,
    pkg/__init__.py -> pkg."""
    rel = rel.replace(os.sep, "/")
    if rel.endswith(".py"):
        rel = rel[:-3]
    if rel.endswith("/__init__"):
        rel = rel[: -len("/__init__")]
    elif rel == "__init__":
        rel = ""
    return rel.replace("/", ".")


def repo_modules(root):
    """Map every .py file under directory `root` to its dotted module name and source, so a package on disk
    becomes the {module: source} dict load_program consumes. Skips hidden / dotted directories and
    __pycache__, and any file that does not read or parse."""
    modules = {}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if not d.startswith(".") and d != "__pycache__"]
        for fn in filenames:
            if not fn.endswith(".py"):
                continue
            full = os.path.join(dirpath, fn)
            name = _module_name(os.path.relpath(full, root))
            if not name:
                continue
            try:
                with open(full, encoding="utf-8") as fh:
                    src = fh.read()
                ast.parse(src)
            except (OSError, UnicodeDecodeError, SyntaxError):
                continue
            modules[name] = src
    return modules


def load_repo(root):
    """Build the whole-program verification repo for a package directory: every .py file under `root`
    becomes a module named by its path, and load_program resolves the cross-module imports across the
    tree. Returns the {mangled_name: source} repo (see load_program)."""
    return load_program(repo_modules(root))


def _called_repo_names(src, repo):
    """The mangled callee names a function calls that are themselves program functions (keys of `repo`)."""
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return set()
    return {n.func.id for n in ast.walk(tree)
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in repo}


def _closure_hasher(repo):
    """Return (hash, edges): hash(key) is a sha256 over repo[key] and every function transitively reachable
    from it (so a verdict is reused only when the function and all it inlines are byte-identical), and edges
    is the forward call graph (each function parsed once) used to compute it and to find affected callers."""
    edges = {k: _called_repo_names(v, repo) for k, v in repo.items()}

    def closure_hash(key):
        seen, stack = set(), [key]
        while stack:                                                     # the function and everything it inlines
            k = stack.pop()
            if k in seen:
                continue
            seen.add(k)
            stack.extend(edges.get(k, set()) - seen)
        blob = "\n".join("%s\0%s" % (k, repo[k]) for k in sorted(seen))
        return hashlib.sha256(blob.encode("utf-8")).hexdigest()

    return closure_hash, edges


def _repo_labels(modules):
    """Map each mangled repo key to its readable module.function label, for the triage report."""
    label = {}
    for m, src in modules.items():
        for n in ast.parse(src).body:
            if isinstance(n, ast.FunctionDef):
                label[_mangle(m, n.name)] = "%s.%s" % (m, n.name)
    return label


def _standalone_def_src(m, drop_receiver=False):
    """A class method re-emitted as a standalone function (decorators and any return annotation dropped) so
    the trap-freedom engine can triage it: `self`/`cls` and any attribute access fall outside the modeled
    subset and yield UNKNOWN, while a method that is a pure function of its parameters is still verified. With
    drop_receiver, the receiver (`self`/`cls`) is dropped so it reads as a free opaque name -- used when
    computing the trap-freedom *verdict*, since a 'trap' pinned only to `self=<value>` is spurious (a receiver
    is an object, not a sampled scalar); a genuine parameter-only trap (a // b) still refutes. The default keeps
    the receiver, naming a real instance method for confirmation and repro (_confirm_method)."""
    fn = core._clone_ast(m)                                   # a fast structural clone (~4x cheaper than deepcopy)
    fn.decorator_list = []
    if drop_receiver and fn.args.args and fn.args.args[0].arg in ("self", "cls"):
        fn.args.args = fn.args.args[1:]                       # receiver -> free opaque name, not a modeled param
    return ast.unparse(ast.fix_missing_locations(fn))


_TRIAGE_REPO = None   # the shared repo a parallel-triage worker checks against, set once per worker by _triage_init


def _triage_init(repo):
    global _TRIAGE_REPO
    _TRIAGE_REPO = repo


def _triage_check(job):
    """Worker for the whole-repo triage: check one item (hash, src, key, total) and return (hash, status). A
    top-level function (key not None) is checked against the shared repo set by _triage_init; a standalone
    method (key None) without one. Module-level and picklable so a spawn pool can use it, with its own z3
    context; the verdict is the deterministic rlimit-bound result, identical to the serial check."""
    h, src, key, total = job
    try:
        status = check(src, repo=(_TRIAGE_REPO if key is not None else None), target=key, total=total).status
    except Exception:
        status = UNKNOWN
    return h, status


def _run_triage(work, repo, jobs):
    """Discharge the cache-miss items {hash: (hash, src, key, total)} and return {hash: status}. jobs <= 1 runs
    serially (deterministic, the default); jobs > 1 runs a spawn-based process pool capped at the CPU count, so
    each worker gets a core (no oversubscription) and the rlimit-bound verdict is identical to the serial one --
    the triage's wall-clock cost drops with no verdict change. A pool that cannot start (a restricted
    environment) falls back to serial."""
    items = list(work.values())
    if not items:
        return {}
    n = min(jobs, len(items), os.cpu_count() or 1) if (jobs and jobs > 1) else 1
    if n > 1:
        import concurrent.futures
        import multiprocessing as _mp
        from . import _partriage                                  # the worker lives in its own module so a spawned
        try:                                                      # worker imports the package through its normal entry
            with concurrent.futures.ProcessPoolExecutor(max_workers=n, mp_context=_mp.get_context("spawn"),
                                                        initializer=_partriage.init, initargs=(repo,)) as ex:
                return dict(ex.map(_partriage.run, items))
        except Exception:
            pass                                                  # a pool that cannot start: fall through to serial
    _triage_init(repo)
    return dict(_triage_check(job) for job in items)


def _triage_collect(modules, repo, total, closure_hash, keys=None):
    """Walk the modules into a deterministic display order [(name, hash)] and the unique cache-miss work items
    {hash: (hash, src, key, total)} -- every top-level function (resolved through the cross-module graph) and
    every class method (triaged standalone). `keys` restricts the top-level functions to a given mangled-name
    set (for a diff-scoped triage); None covers all. The hash dedupes identical closures so each is checked
    once, and methods hash on their standalone source."""
    order, work = [], {}
    for modname, src in sorted(modules.items()):
        body = ast.parse(src).body
        for n in body:
            if not isinstance(n, ast.FunctionDef):
                continue
            key = _mangle(modname, n.name)
            if key not in repo or (keys is not None and key not in keys):
                continue
            h = closure_hash(key)
            order.append(("%s.%s" % (modname, n.name), h))
            work.setdefault(h, (h, repo[key], key, total))
        for cls in body:                                          # methods inside classes, triaged standalone
            if not isinstance(cls, ast.ClassDef):
                continue
            for m in cls.body:
                if not isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                msrc = _standalone_def_src(m)
                h = hashlib.sha256(("M\0" + msrc).encode("utf-8")).hexdigest()
                order.append(("%s.%s.%s" % (modname, cls.name, m.name), h))
                work.setdefault(h, (h, msrc, None, total))
    return order, work


def verify_repo(root, total=False, cache=None, jobs=1, exclude=None):
    """Trap-freedom triage of a whole repository on disk: check every top-level function in every module,
    following calls across the resolved cross-module call graph, and check every method inside a class as
    well, returning a list of (module.function or module.Class.method, status). A method is triaged
    standalone, so its `self`/`cls` and any attribute access fall outside the modeled subset and come back
    UNKNOWN, while a method that is a pure function of its parameters is verified. A construct outside the
    modeled subset comes back UNKNOWN, so the PROVED / REFUTED / UNKNOWN split is the verified-subset
    coverage of the codebase. `cache` is a {content_hash: status} dict reused and updated in place: a
    top-level function whose own source and whole transitive callee closure are byte-identical to a previous
    run, or a method whose source is unchanged, is not re-verified, so passing a cache makes a re-run
    incremental. `jobs > 1` triages the cache misses across that many worker processes (capped at the CPU
    count); the verdicts are the deterministic rlimit-bound ones, identical to a serial run. `exclude`, a list
    of fnmatch globs, drops matching modules from triage while still loading them for call resolution."""
    modules = repo_modules(root)
    repo = load_program(modules)                              # the full load set, so excluded modules still resolve
    verdicts = cache if cache is not None else {}
    closure_hash, _ = _closure_hasher(repo)
    order, work = _triage_collect(_filter_excluded(modules, exclude), repo, total, closure_hash)
    miss = {h: job for h, job in work.items() if h not in verdicts}
    verdicts.update(_run_triage(miss, repo, jobs))
    return [(name, verdicts[h]) for name, h in order]


def verify_diff(root, changed, total=False, cache=None, jobs=1, exclude=None):
    """Verify only the functions a change touches: the functions in the `changed` modules and every caller
    whose proof transitively depends on one of them, leaving the rest of the repository unverified, so a
    gate's cost tracks the change rather than the repository size. `changed` is a list of file paths
    relative to `root` (the output of `git diff --name-only`) or dotted module names. Returns
    (module.function, status) for the affected set, ordered."""
    modules = repo_modules(root)
    repo = load_program(modules)
    label = _repo_labels(modules)
    closure_hash, edges = _closure_hasher(repo)

    def to_mod(c):
        c = str(c)
        if not c.endswith(".py"):
            return c
        if os.path.isabs(c):                                  # an absolute path is relativized against root; a path
            try:                                              # already relative to root (git diff --name-only) is used
                c = os.path.relpath(c, root)                  # as given, so the module name does not depend on the
            except ValueError:                                # current directory (a Windows cross-drive absolute path
                pass                                          # cannot be relativized and falls back to the raw path)
        return _module_name(c)

    changed_mods = {to_mod(c) for c in changed}
    affected = {k for k, lab in label.items() if lab.rsplit(".", 1)[0] in changed_mods}
    rev = {}                                                              # callee -> its callers
    for caller, callees in edges.items():
        for callee in callees:
            rev.setdefault(callee, set()).add(caller)
    stack = list(affected)
    while stack:                                                         # add every transitive caller of a change
        k = stack.pop()
        for caller in rev.get(k, ()):
            if caller not in affected:
                affected.add(caller)
                stack.append(caller)
    verdicts = cache if cache is not None else {}
    order, work = [], {}
    for key in sorted(affected):
        if key not in repo:
            continue
        if _excluded(label.get(key, key).rsplit(".", 1)[0], exclude):   # drop a change in a user-excluded module
            continue
        h = closure_hash(key)
        order.append((label.get(key, key), h))
        work.setdefault(h, (h, repo[key], key, total))
    miss = {h: job for h, job in work.items() if h not in verdicts}
    verdicts.update(_run_triage(miss, repo, jobs))                # serial (default) or jobs worker processes
    return [(name, verdicts[h]) for name, h in order]


def coverage(root, history=None, cache=None, jobs=1, exclude=None):
    """The verified-subset coverage of a repository: the count and fraction of top-level functions PROVED
    trap-free, with the REFUTED and UNKNOWN counts and the names that refute. When `history` (the list of
    prior reports) is given, the report also carries the change since the last entry -- the coverage delta
    and any function that newly refutes -- so verification debt and a regression are visible over time.
    Returns the report dict; append it to a persisted history to track the trend. `jobs > 1` triages across
    that many worker processes."""
    rows = verify_repo(root, cache=cache, jobs=jobs, exclude=exclude)
    proved = sum(1 for _, s in rows if s == PROVED)
    refuted = sorted(n for n, s in rows if s == REFUTED)
    unknown = sum(1 for _, s in rows if s == UNKNOWN)
    total = len(rows)
    report = {"total": total, "proved": proved, "refuted": len(refuted), "unknown": unknown,
              "coverage": round(100.0 * proved / total, 1) if total else 0.0,
              "refuted_functions": refuted}
    if history:
        prev = history[-1]
        report["delta_proved"] = proved - prev.get("proved", 0)
        report["delta_coverage"] = round(report["coverage"] - prev.get("coverage", 0.0), 1)
        report["new_refusals"] = sorted(set(refuted) - set(prev.get("refuted_functions", [])))
    return report


def _safe_check(src, repo, target, total):
    """check() that degrades any internal failure to UNKNOWN, so a single unmodelable function never aborts a
    whole-target scan."""
    try:
        return check(src, repo=repo, target=target, total=total)
    except Exception as e:
        return Verdict(UNKNOWN, target or "f", target or "f", "scan", reason="check raised: %s" % type(e).__name__)


class _UnitBudgetExceeded(BaseException):
    """A scanned unit hit its per-unit wall-clock backstop. BaseException (not Exception) so an inner
    `except Exception` deep in the cascade cannot swallow it -- it unwinds to the per-unit guard, which records
    UNKNOWN. Scan-only; never raised on a direct check / prove."""


@contextlib.contextmanager
def _unit_deadline(seconds):
    """Bound the wrapped per-unit work by `seconds` of wall-clock via SIGALRM, raising _UnitBudgetExceeded on
    overrun. A no-op when seconds is falsey, where SIGALRM is unavailable, or off the main thread (an LSP / MCP
    worker thread cannot take the signal) -- there the deterministic node budget is the only guard. The parallel
    scan's spawn workers run each unit on their own main thread, so the backstop applies there."""
    if not seconds or not hasattr(signal, "SIGALRM") or threading.current_thread() is not threading.main_thread():
        yield
        return

    def _fire(signum, frame):
        raise _UnitBudgetExceeded("unit exceeded the %gs scan wall-clock budget" % seconds)

    old = signal.signal(signal.SIGALRM, _fire)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old)


def _unit_over_budget(node):
    """A reason string when the unit's AST node count exceeds SCAN_UNIT_NODE_BUDGET (the deterministic size cap),
    else None: a giant generated body blows an engine up unbounded, so a scan skips it before any engine runs."""
    budget = core.SCAN_UNIT_NODE_BUDGET
    if not budget:
        return None
    n = sum(1 for _ in ast.walk(node))
    return "exceeds the scan complexity budget (%d AST nodes > %d)" % (n, budget) if n > budget else None


def _guarded_fn_check(node, src, repo, key, total):
    """The scan-triage check for a top-level function under the per-unit budget: a unit over the deterministic
    node budget, or one whose check overruns the wall-clock backstop, is abandoned to UNKNOWN (sound) rather than
    left to stall or OOM the whole scan."""
    over = _unit_over_budget(node)
    if over is not None:
        return Verdict(UNKNOWN, key or "f", key or "f", "scan", reason=over)
    try:
        with _unit_deadline(core.SCAN_UNIT_TIMEOUT_S):
            return _safe_check(src, repo, key, total)
    except _UnitBudgetExceeded as e:
        return Verdict(UNKNOWN, key or "f", key or "f", "scan", reason=str(e))


def _guarded_method_verdict(module_src, class_node, method_node, total):
    """_method_verdict under the same per-unit budget. An over-budget method skips straight to UNKNOWN with an
    empty standalone source -- an UNKNOWN unit yields no finding, so its source is never consulted, and the giant
    body is never even re-emitted."""
    over = _unit_over_budget(method_node)
    if over is not None:
        return Verdict(UNKNOWN, method_node.name, method_node.name, "scan", reason=over), ""
    try:
        with _unit_deadline(core.SCAN_UNIT_TIMEOUT_S):
            return _method_verdict(module_src, class_node, method_node, total)
    except _UnitBudgetExceeded as e:
        return Verdict(UNKNOWN, method_node.name, method_node.name, "scan", reason=str(e)), ""


def _heap_driver_worthwhile(method_node):
    """Whether the (solver-backed) heap driver can find a trap the standalone self-opaque check missed: only
    a subscript (IndexError / KeyError), a container-method call (pop / append / remove / ...), or a floor-
    division / modulo over instance state can trap inside a constructed-receiver run. A method with none of
    these has no heap-only trap, so the driver is skipped -- keeping a whole-repo scan from paying a solver
    call per method where it cannot help."""
    has_self_attr = has_div = False
    for n in ast.walk(method_node):
        if isinstance(n, ast.Subscript):
            return True
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) \
                and n.func.attr in ("pop", "append", "add", "remove", "discard", "insert", "popitem"):
            return True
        if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == "self":
            has_self_attr = True
        if isinstance(n, ast.BinOp) and isinstance(n.op, (ast.FloorDiv, ast.Mod)):
            has_div = True
    return has_self_attr and has_div


def _class_constructible_no_args(class_node):
    """Whether `ClassName()` builds with no arguments -- the heap driver constructs the receiver that way, so a
    class whose __init__ needs a positional argument (the common nn.Module / dataclass-with-fields shape)
    cannot be driven and the driver is skipped. No own __init__ (a default or inherited constructor) counts as
    constructible, as does one whose extra positional params all carry defaults or are *args/**kwargs."""
    init = next((s for s in class_node.body
                 if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef)) and s.name == "__init__"), None)
    if init is None:
        return True
    a = init.args
    n_required_pos = (len(a.args) - 1) - len(a.defaults)         # positional params past self with no default
    n_required_kw = sum(1 for d in a.kw_defaults if d is None)
    return n_required_pos <= 0 and n_required_kw == 0


def _method_heap_refute(module_src, class_name, method_node, total):
    """Find an implicit method bug symbolically by constructing the receiver and invoking the method through
    the heap engine: build `obj = ClassName(); return obj.method(<params>)` over the module's classes (minus
    its imports, which the heap engine cannot follow) and verify trap freedom. A reachable trap on a
    freshly-constructed instance -- an empty self.items.pop(), an unguarded self.items[0], a missing
    self.d[k] -- is REFUTED with a witness the standalone (self-opaque) check cannot see. Returns that Verdict
    or None; only a heap refutation is trusted (the heap model defaults an unset attribute to 0). Declines a
    staticmethod, a vararg/kwarg method, or a receiver the driver cannot construct without arguments."""
    m = method_node
    params = [a.arg for a in m.args.args]
    if not params or params[0] not in ("self", "cls"):          # a staticmethod is a plain function, handled elsewhere
        return None
    if m.args.vararg or m.args.kwarg or m.args.kwonlyargs or m.args.posonlyargs:
        return None
    if not _heap_driver_worthwhile(m):                          # no subscript / container-method / instance division
        return None
    names = [a.arg for a in m.args.args[1:]]                     # the method's non-receiver parameters
    try:
        mod = ast.parse(textwrap.dedent(module_src))
    except SyntaxError:
        return None
    mod.body = [s for s in mod.body if not isinstance(s, (ast.Import, ast.ImportFrom))]   # sibling classes resolve
    driver = ("def __ts_drive__(%s):\n    __obj = %s()\n    return __obj.%s(%s)\n"
              % (", ".join(names), class_name, m.name, ", ".join(names)))
    try:
        src = ast.unparse(mod) + "\n\n" + driver
        v = verify_heap_property("method", "__ts_drive__", src, lambda za, r: z3.BoolVal(True))
    except Exception:
        return None
    return v if v.status == REFUTED else None


def _method_verdict(module_src, class_node, method_node, total):
    """The triage verdict for a method, with its standalone trap-freedom source. The standalone check models
    self as opaque, so a self/attribute bug is UNKNOWN there; the heap driver upgrades that to a refutation
    when constructing the receiver and invoking the method reaches a trap (an empty-container method, an
    unguarded index). A standalone REFUTED (a parameter-only bug like a // b) already decides and is kept."""
    ms = _standalone_def_src(method_node)                       # keeps self/cls: names a real method for confirm/repro
    v = _safe_check(_standalone_def_src(method_node, drop_receiver=True), {}, None, total)   # receiver opaque, so a
    if v.status != REFUTED and _class_constructible_no_args(class_node):   # a non-refuting opaque-self check, with a
        hv = _method_heap_refute(module_src, class_node.name, method_node, total)   # no-arg-constructible receiver
        if hv is not None:                                       # to drive: only then can the heap engine reach a
            return hv, ms                                        # self-state trap the standalone check could not see
    return v, ms


def _triage_file_verdicts(src, total=False):
    """Trap-freedom triage of one module's source, keeping for each function its Verdict plus the source,
    repo, name, and kind a scan needs to confirm and reproduce a finding. Top-level functions resolve their
    in-file callees through the module repo; a method is triaged standalone (self/attributes fall outside the
    subset, so a method finding is rarely confirmable)."""
    try:
        repo = load_module(src)
        dsrc = textwrap.dedent(src)                           # def linenos are relative to the dedented source
        body = ast.parse(dsrc).body
    except SyntaxError:
        return [], {}, set()
    out, locmap, suppressed = [], {}, set()
    for n in body:
        if isinstance(n, ast.FunctionDef) and n.name in repo:
            out.append((n.name, _guarded_fn_check(n, repo[n.name], repo, n.name, total), repo[n.name], repo, n.name, "function", None))
            locmap[n.name] = (None, n.lineno)
            if _span_suppressed(dsrc, (n.lineno, getattr(n, "end_lineno", n.lineno))):
                suppressed.add(n.name)
        elif isinstance(n, ast.ClassDef):
            for m in n.body:                                 # the module source + class name, so a method finding
                if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)):   # confirms on a real constructed instance
                    v, ms = _guarded_method_verdict(src, n, m, total)   # standalone + heap driver, under the unit budget
                    lbl = "%s.%s" % (n.name, m.name)
                    out.append((lbl, v, ms, {}, m.name, "method", (src, n.name)))
                    locmap[lbl] = (None, m.lineno)
                    if _span_suppressed(dsrc, (m.lineno, getattr(m, "end_lineno", m.lineno))):
                        suppressed.add(lbl)
    return out, locmap, suppressed


def _is_test_module(modname):
    """Whether a module is a test file (so a whole-repo scan skips it -- a test's helpers and fixtures are not
    the code under audit, and their standalone findings are noise). True for a `tests`/`test` package component,
    or a leaf named test_*, *_test, or conftest."""
    parts = modname.split(".")
    if any(p in ("test", "tests") for p in parts):
        return True
    leaf = parts[-1]
    return leaf.startswith("test_") or leaf.endswith("_test") or leaf == "conftest"


def _excluded(modname, patterns):
    """Whether a module is user-excluded from triage -- its dotted name, its slash-path form, or that path with a
    .py suffix matches any of the fnmatch glob `patterns` (None / empty excludes nothing). An excluded module is
    still loaded for cross-module call resolution; it is only dropped from the set of units checked and reported,
    so excluding vendored or generated code does not turn a caller's resolved callee into an UNKNOWN."""
    if not patterns:
        return False
    import fnmatch as _fn
    path = modname.replace(".", "/")
    return any(_fn.fnmatch(modname, p) or _fn.fnmatch(path, p) or _fn.fnmatch(path + ".py", p) for p in patterns)


def _filter_excluded(modules, patterns):
    """The modules dict with user-excluded modules removed -- for the triage iteration set, never the load set."""
    return modules if not patterns else {m: src for m, src in modules.items() if not _excluded(m, patterns)}


_PAR_TRIAGE_MIN_MODULES = 8        # below this a scan's repo triage stays serial: the spawn cost would not pay off


def _module_rows(modname, src, repo, total):
    """The triage rows for one module -- top-level functions checked against the cross-module `repo`, each class
    method triaged standalone (upgraded by the heap driver). Each row is the lightweight, picklable
    (modname, label, verdict, srcref, fname, kind, class_name): a function's srcref is its mangled repo key, a
    method's its standalone source; _triage_repo_verdicts re-expands these into the full scan rows. Shared by
    the serial and the parallel (per-module spawn-pool) triage paths -- one module is an independent unit."""
    out = []
    try:
        body = ast.parse(src).body
    except SyntaxError:
        return out
    for n in body:
        if isinstance(n, ast.FunctionDef):
            key = _mangle(modname, n.name)
            if key in repo:
                out.append((modname, "%s.%s" % (modname, n.name),
                            _guarded_fn_check(n, repo[key], repo, key, total), key, key, "function", None))
        elif isinstance(n, ast.ClassDef):
            for m in n.body:
                if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    v, ms = _guarded_method_verdict(src, n, m, total)   # standalone + heap driver, under the unit budget
                    out.append((modname, "%s.%s.%s" % (modname, n.name, m.name), v, ms, m.name, "method", n.name))
    return out


def _unit_lite_row(job, repo, modules, total, crash_on=None):
    """Compute one unit's lite triage row -- the same tuple _module_rows emits. A function unit (job[1] == 'F')
    is checked against the cross-module repo; a method unit ('M') is triaged standalone + heap driver. crash_on,
    when a substring of the unit's label, aborts the process here: a test hook that exercises crash tolerance by
    simulating a z3 SIGABRT on a chosen unit."""
    modname, kind = job[0], job[1]
    if kind == "F":
        fname = job[2]
        label = "%s.%s" % (modname, fname)
        if crash_on and crash_on in label:
            os._exit(134)
        key = _mangle(modname, fname)
        node = _fndef(repo[key])
        return (modname, label, _guarded_fn_check(node, repo[key], repo, key, total), key, key, "function", None)
    cname, mname = job[2], job[3]
    label = "%s.%s.%s" % (modname, cname, mname)
    if crash_on and crash_on in label:
        os._exit(134)
    cnode = next((c for c in ast.parse(modules[modname]).body
                  if isinstance(c, ast.ClassDef) and c.name == cname), None)
    mnode = next((m for m in cnode.body if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))
                  and m.name == mname), None) if cnode is not None else None
    if mnode is None:                                            # the method went away (a parse quirk): abstain
        return (modname, label, Verdict(UNKNOWN, mname, mname, "scan", reason="method not found"), "", mname, "method", cname)
    v, ms = _guarded_method_verdict(modules[modname], cnode, mnode, total)
    return (modname, label, v, ms, mname, "method", cname)


def _crash_unknown(job):
    """The lite row for a unit whose worker died on it (a z3 abort) -- UNKNOWN, isolated to this one unit."""
    modname, kind = job[0], job[1]
    reason = "worker aborted on this unit (z3 crash); isolated to UNKNOWN"
    if kind == "F":
        key = _mangle(modname, job[2])
        return (modname, "%s.%s" % (modname, job[2]), Verdict(UNKNOWN, key, key, "scan", reason=reason),
                key, key, "function", None)
    cname, mname = job[2], job[3]
    return (modname, "%s.%s.%s" % (modname, cname, mname), Verdict(UNKNOWN, mname, mname, "scan", reason=reason),
            "", mname, "method", cname)


def _build_unit_tasks(items, repo):
    """Flatten the modules into one task per unit (function or method): the crash-tolerant pool processes each
    unit independently, so a worker that aborts loses only that unit. Order matches the serial _module_rows
    iteration, so the reassembled rows are identical to the serial path for every unit that does not crash."""
    tasks = []
    for modname, src, _t in items:
        try:
            body = ast.parse(src).body
        except SyntaxError:
            continue
        for n in body:
            if isinstance(n, ast.FunctionDef):
                if _mangle(modname, n.name) in repo:
                    tasks.append((modname, "F", n.name))
            elif isinstance(n, ast.ClassDef):
                for m in n.body:
                    if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        tasks.append((modname, "M", n.name, m.name))
    return tasks


_UNIT_POOL_STALL_S = 180.0      # no result and no worker death for this long: a worker is wedged in a non-aborting
#                                 C call; mark the remaining units UNKNOWN and stop, rather than hang the scan


def _run_unit_pool(tasks, repo, modules, total, n, progress=None, done0=0, ntotal=None):
    """Triage the unit tasks across a supervised spawn pool that tolerates a worker dying mid-unit. Each worker
    records the index of the unit it is on in a shared slot; when it aborts (a z3 SIGABRT no in-process bound can
    catch, an OOM kill, a segfault), the supervisor marks exactly that unit UNKNOWN, respawns the worker, and the
    rest of the units -- queued or on other workers -- are unaffected. Returns a lite row per task, in task
    order (so a non-crashing unit's row is identical to the serial path). `progress(done0 + completed, ntotal)`
    is called as units finish, so a caller counting cache hits in done0 can report whole-scan progress."""
    import multiprocessing as _mp
    import time as _time
    from . import _partriage
    ctx = _mp.get_context("spawn")
    mgr = ctx.Manager()
    results = mgr.dict()                                      # idx -> lite row; in a separate server process, so a
    current = mgr.list([-1] * n)                              # worker crash cannot corrupt it (unlike a shared Queue)
    task_q = ctx.Queue()                                      # read-only to workers: a reader's abort cannot corrupt it
    for i, job in enumerate(tasks):
        task_q.put((i, job))
    rest = (task_q, results, current, repo, modules, total,
            core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION, core._SCAN_CRASH_ON)

    def _spawn(widx):
        p = ctx.Process(target=_partriage.scan_unit_worker, args=(widx,) + rest, daemon=True)
        p.start()
        return p

    workers = [_spawn(i) for i in range(n)]
    ntasks = len(tasks)
    if ntotal is None:
        ntotal = ntasks
    respawn_cap = ntasks + 4 * n + 8                          # each genuine crash consumes a task; far beyond this is
    respawns = 0                                              # a worker dying without progress -- stop, do not spin
    last = _time.monotonic()
    last_done = 0
    while len(results) < ntasks:
        _time.sleep(0.1)
        nd = len(results)
        if nd != last_done:
            last_done = nd
            last = _time.monotonic()
            if progress:
                progress(done0 + nd, ntotal)
        for i, w in enumerate(workers):
            if not w.is_alive():                             # a worker aborted/exited: the unit it recorded in
                cur = current[i]                             # current[i] is the casualty -- mark only that one
                if isinstance(cur, int) and 0 <= cur < ntasks and cur not in results:
                    results[cur] = _crash_unknown(tasks[cur])
                    last = _time.monotonic()
                if len(results) < ntasks and respawns < respawn_cap:
                    workers[i] = _spawn(i)                   # respawn to finish any remaining queued units
                    respawns += 1
        if respawns >= respawn_cap or _time.monotonic() - last > _UNIT_POOL_STALL_S:
            break                                            # runaway respawns or a non-aborting wedge: stop here
    rd = dict(results.items())                               # one fetch of the whole map, not a per-task RPC
    out = [rd[i] if i in rd else _crash_unknown(tasks[i]) for i in range(ntasks)]
    for w in workers:
        try:
            w.terminate()
            w.join(timeout=1)
        except Exception:
            pass
    try:
        mgr.shutdown()
    except Exception:
        pass
    if progress and last_done < ntasks:                      # the in-loop report already hit ntotal unless we broke
        progress(done0 + ntasks, ntotal)                     # out early (a stall); then account for the crash rows
    return out


def _unit_cache_keyer(repo, modules, execute, total):
    """Return key(task): a content-addressed cache key for a scan unit, or None when it is not cacheable. A
    function keys on its closure hash (its own source and every function it inlines, so a verdict is reused only
    when the whole inlined closure is byte-identical -- the same soundness verify_repo's cache uses); a method
    keys on its own module's full source plus its class/method name (a method is triaged with its whole module
    as context, so any change to that module re-triages it). The key is prefixed with the execution mode and the
    totality flag, since both change the verdict, so a symbolic and an --execute cache never cross-contaminate."""
    closure_hash, _ = _closure_hasher(repo)
    pref = "%s%d\0" % ("x" if execute else "s", 1 if total else 0)

    def key(task):
        modname, kind = task[0], task[1]
        if kind == "F":
            mk = _mangle(modname, task[2])
            return pref + closure_hash(mk) if mk in repo else None
        cname, mname = task[2], task[3]
        blob = "M\0%s\0%s\0%s" % (cname, mname, modules.get(modname, ""))
        return pref + hashlib.sha256(blob.encode("utf-8")).hexdigest()

    return key


def _verdict_to_cache(v):
    """A scan unit's (non-REFUTED) verdict as a JSON-serializable record; only the fields a re-expanded row and
    the proved/unknown tally consult. A REFUTED verdict is never cached, so a finding's counterexample / repro is
    always recomputed fresh and no sampled witness has to round-trip through the cache file."""
    return {"status": v.status, "prop": v.prop, "target": v.target, "technique": v.technique, "reason": v.reason}


def _verdict_from_cache(d):
    """Rebuild a Verdict from a _verdict_to_cache record (a cache hit, always non-REFUTED)."""
    return Verdict(d["status"], d.get("prop"), d.get("target"), d.get("technique"), reason=d.get("reason"))


def _row_from_cache(task, repo, modules, v):
    """The lite triage row for a cache hit -- the structural fields of _unit_lite_row with the cached verdict
    substituted for the solve. A hit is always non-REFUTED, so a method row's source slot (consulted only when a
    finding is built) is never read and stays empty."""
    modname, kind = task[0], task[1]
    if kind == "F":
        key = _mangle(modname, task[2])
        return (modname, "%s.%s" % (modname, task[2]), v, key, key, "function", None)
    cname, mname = task[2], task[3]
    return (modname, "%s.%s.%s" % (modname, cname, mname), v, "", mname, "method", cname)


def _unit_lines(modname, modules, line_idx, kind, fname, cname):
    """The (def line, end line) span of a unit in its module: the def line gives a finding's physical location
    (SARIF), the full span bounds an inline-suppression search. The module is parsed once and memoized."""
    idx = line_idx.get(modname)
    if idx is None:
        idx = {}
        try:
            for n in ast.parse(modules[modname]).body:
                if isinstance(n, ast.FunctionDef):
                    idx[("F", _mangle(modname, n.name))] = (n.lineno, getattr(n, "end_lineno", n.lineno))
                elif isinstance(n, ast.ClassDef):                 # a function row's fname slot is its mangled key
                    for m in n.body:
                        if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            idx[("M", n.name, m.name)] = (m.lineno, getattr(m, "end_lineno", m.lineno))
        except (SyntaxError, KeyError):
            pass
        line_idx[modname] = idx
    return idx.get(("F", fname)) if kind == "function" else idx.get(("M", cname, fname))


def _span_suppressed(src, span):
    """Whether an inline `# touchstone: ignore` comment appears within a unit's source span (its def line through
    its end line), by which the author marks the trap intentional so the finding is dropped. A comment is any line
    whose `#`-comment carries both `touchstone:` and `ignore`, so `# touchstone: ignore` (with or without the
    space) is recognized."""
    lo, hi = span if span else (None, None)
    if not lo:
        return False
    lines = src.splitlines()
    for i in range(lo - 1, min(hi or lo, len(lines))):
        c = lines[i].find("#")
        if c != -1 and "touchstone:" in lines[i][c:] and "ignore" in lines[i][c:]:
            return True
    return False


def _triage_repo_verdicts(root, total=False, jobs=None, cache=None, progress=None, exclude=None):
    """Trap-freedom triage of a package tree, keeping for each function its Verdict plus the source, repo,
    name, and kind a scan needs to confirm and reproduce a finding, and a {label: (module, line)} location map.
    Reuses the same cross-module load_program resolution and the same check, so a callee's trap is seen at the
    call site. jobs > 1 (or the jobs=None auto default, on a repo of at least _PAR_TRIAGE_MIN_MODULES modules)
    triages the units across a crash-tolerant spawn pool capped at the CPU count: per-unit work, so a worker that
    aborts (a z3 SIGABRT no in-process bound can catch) costs only that one unit (UNKNOWN), not the run -- and
    every unit that does not crash gets a row identical to the serial path. A pool that cannot start falls back to
    serial. `cache`, a {content_key: verdict_record} dict reused and updated in place, skips re-triaging a unit
    whose source and inlined closure are byte-identical to a previous run (only its non-REFUTED verdicts are
    stored, so findings stay fresh). `progress(done, total)` is called as units are decided."""
    modules = repo_modules(root)
    repo = load_program(modules, on_collision="skip")         # a scan tolerates a rare mangle collision, not crash
    items = [(m, src, total) for m, src in sorted(modules.items())
             if not _is_test_module(m) and not _excluded(m, exclude)]
    tasks = _build_unit_tasks(items, repo)
    ntotal = len(tasks)
    keyfn = _unit_cache_keyer(repo, modules, core.SANDBOX_SUBJECT, total) if cache is not None else None
    keys = [keyfn(t) for t in tasks] if keyfn else None
    lite = [None] * ntotal
    miss = []
    for i, t in enumerate(tasks):                             # split cache hits (reuse the verdict) from misses
        if keys and keys[i] is not None and keys[i] in cache:
            lite[i] = _row_from_cache(t, repo, modules, _verdict_from_cache(cache[keys[i]]))
        else:
            miss.append(i)
    done0 = ntotal - len(miss)
    if progress:
        progress(done0, ntotal)
    miss_tasks = [tasks[i] for i in miss]
    if jobs is None:                                          # auto: parallelize a sizable repo, serial otherwise
        want = (os.cpu_count() or 1) if len(items) >= _PAR_TRIAGE_MIN_MODULES else 1
    else:
        want = jobs
    n = min(want, len(miss_tasks), os.cpu_count() or 1) if (want and want > 1) else 1
    miss_rows = None
    if n > 1 and miss_tasks:
        try:                                                  # per-unit tasks across the supervised, crash-tolerant
            miss_rows = _run_unit_pool(miss_tasks, repo, modules, total, n,   # pool (_run_unit_pool)
                                       progress=progress, done0=done0, ntotal=ntotal)
        except Exception:
            miss_rows = None                                  # a pool that cannot start: fall through to serial
    if miss_rows is None:
        miss_rows = []
        for k, t in enumerate(miss_tasks):
            try:
                row = _unit_lite_row(t, repo, modules, total)
            except BaseException:
                row = _crash_unknown(t)
            miss_rows.append(row)
            if progress and (k % 16 == 0 or k + 1 == len(miss_tasks)):
                progress(done0 + k + 1, ntotal)
    for j, i in enumerate(miss):                              # place misses back at their task index; cache the
        lite[i] = miss_rows[j]                                # cheap-to-serialize non-REFUTED verdicts
        if cache is not None and keys[i] is not None and miss_rows[j][2].status != REFUTED:
            cache[keys[i]] = _verdict_to_cache(miss_rows[j][2])
    out, locmap, line_idx, suppressed = [], {}, {}, set()
    for (modname, label, v, srcref, fname, kind, cname) in lite:    # re-expand to the full scan rows (repo /
        if kind == "function":                                     # module source filled here, not shipped per row)
            out.append((label, v, repo[srcref], repo, fname, "function", None))
        else:
            out.append((label, v, srcref, {}, fname, "method", (modules[modname], cname)))
        span = _unit_lines(modname, modules, line_idx, kind, fname, cname)
        locmap[label] = (modname, span[0] if span else None)
        if (v.status == REFUTED or (v.status == UNKNOWN and kind == "function")) \
                and _span_suppressed(modules.get(modname, ""), span):   # an inline ignore drops this finding
            suppressed.add(label)
    return out, locmap, suppressed


def _has_explicit_raise(src, exc):
    """Whether the function body explicitly raises exception `exc` (or, for AssertionError, contains an
    assert) -- the signal that a confirmed ValueError / AssertionError is intended input validation rather
    than a latent crash."""
    try:
        fn = _fndef(src)
    except Unsupported:
        return False
    if exc == "AssertionError":
        return any(isinstance(n, ast.Assert) for n in ast.walk(fn))
    for n in ast.walk(fn):
        if isinstance(n, ast.Raise) and n.exc is not None:
            e = n.exc.func if isinstance(n.exc, ast.Call) else n.exc
            nm = e.id if isinstance(e, ast.Name) else (e.attr if isinstance(e, ast.Attribute) else None)
            if nm == exc:
                return True
    return False


def _callee_closure_repo(start_src, repo):
    """The transitive in-repo callees of a function (given its source) as a {name: source} repo. The sandbox
    confirmation execs this, not the whole program: exec'ing a directory scan's full cross-module repo would
    fail setup on an unresolved name and mask every confirmable trap."""
    seen, stack = set(), list(_called_repo_names(start_src, repo))
    while stack:
        k = stack.pop()
        if k in seen or k not in repo:
            continue
        seen.add(k)
        stack.extend(_called_repo_names(repo[k], repo) - seen)
    return {k: repo[k] for k in seen}


def _confirm_finding(src, repo, v):
    """Replay a finding's witness (or sample one) in the sandbox to confirm the trap and name the exception.
    Returns {"confirmed": bool, "exception": name|None, "witness": dict|None}, or None when execution is
    unavailable or the function is outside the plain-positional-parameter shape the sampler supports (so the
    finding stays an unconfirmed symbolic one)."""
    if not (core.SANDBOX_SUBJECT or core.ALLOW_SUBJECT_EXECUTION):
        return None
    try:
        fn = _fndef(src)
    except Unsupported:
        return None
    if fn.args.vararg or fn.args.kwarg or fn.args.kwonlyargs or fn.args.posonlyargs:
        return None
    callees = _callee_closure_repo(src, repo) if repo else {}   # only what the subject calls, not the whole program
    w, exc = _sandbox_first_trap(fn, src, callees, "True", prefer=v.counterexample_inputs)
    if w is not None:
        return {"confirmed": True, "exception": exc, "witness": w}
    return {"confirmed": False, "exception": None, "witness": None}


def _confirm_method(module_src, class_name, method_src, v):
    """Confirm a method finding against a real receiver: construct ClassName() with no constructor arguments and
    invoke the method in the isolated sandbox on sampled method arguments. An empty data structure's method --
    Stack().pop(), Queue().get(), Heap().top() -- confirms as a real trap, where running the method standalone
    with an integer self cannot. The receiver is built against the whole module minus its imports, so a sibling
    helper class (a Node) the class needs is defined while an import-dependent path simply fails to reproduce.
    Returns {"confirmed", "exception", "witness"}, or None when the subject is not a plain instance method or
    the class is not constructible without arguments here."""
    if not (core.SANDBOX_SUBJECT or core.ALLOW_SUBJECT_EXECUTION):
        return None
    try:
        m = _fndef(method_src)
    except Unsupported:
        return None
    params = [a.arg for a in m.args.args]
    if not params or params[0] not in ("self", "cls"):          # a staticmethod is a plain function: handled elsewhere
        return None
    if m.args.vararg or m.args.kwarg or m.args.kwonlyargs or m.args.posonlyargs:
        return None
    rest = m.args.args[1:]                                       # the method's non-receiver parameters
    names = [a.arg for a in rest]
    try:                                                        # the module minus its imports: sibling classes the
        mod = ast.parse(textwrap.dedent(module_src))           # receiver needs resolve; the sandbox cannot import, so
    except SyntaxError:                                        # an import-dependent path fails to reproduce (unconfirmed)
        return None
    mod.body = [s for s in mod.body if not isinstance(s, (ast.Import, ast.ImportFrom))]
    wrapper = "def __ts_invoke__(%s):\n    return %s().%s(%s)\n" % (
        ", ".join(names), class_name, m.name, ", ".join(names))
    full = ast.unparse(mod) + "\n\n" + wrapper
    try:
        wfn = next(n for n in ast.parse(full).body
                   if isinstance(n, ast.FunctionDef) and n.name == "__ts_invoke__")
    except Exception:
        return None
    wfn.args.args = rest                                        # the method params' annotations drive type-aware sampling
    w, exc = _sandbox_first_trap(wfn, full, {}, "True")
    if w is not None:
        return {"confirmed": True, "exception": exc, "witness": w}
    return {"confirmed": False, "exception": None, "witness": None}


def _repro_module(fname, fsrc, repo):
    """`fname` plus its transitive in-repo callees, as one module source, so a generated repro test is
    self-contained -- a call into a recursive or helper callee resolves rather than raising NameError."""
    seen, order, stack = set(), [], [fname]
    while stack:
        k = stack.pop()
        if k in seen or k not in repo:
            continue
        seen.add(k)
        order.append(k)
        stack.extend(_called_repo_names(repo[k], repo) - seen)
    return "\n\n".join(repo[k] for k in order) if order else fsrc


def _const_arg_value(node):
    """The Python int / str / bool value of a constant call argument (a unary-minus integer folded), or None
    when the argument is not a plain literal -- used to decide whether a call site pins a parameter away from a
    finding's witness value."""
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, str, bool)):
        return node.value
    if (isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub)
            and isinstance(node.operand, ast.Constant) and isinstance(node.operand.value, int)
            and not isinstance(node.operand.value, bool)):
        return -node.operand.value
    return None


def _calls_to(key, repo):
    """Every (caller_key, ast.Call) pair where a repo function calls `key` by name, across the whole repo --
    the in-repo call sites of a function, for the context-confirmation of a private-helper scan finding."""
    out = []
    for ck, src in repo.items():
        try:
            tree = _parse(src)
        except Exception:
            continue
        for n in ast.walk(tree):
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == key:
                out.append((ck, n))
    return out


def _context_unreachable(key, repo, witness, verdict_by_key):
    """Whether a private function `key`'s standalone trap is unreachable in its real repo context, so a scan
    demotes the finding rather than presenting it as a candidate. SCAN RANKING ONLY, never a verdict. True when
    `key` has in-repo callers and EITHER (a) every call site pins a witnessing parameter to a constant that
    misses the witness, OR (b) every caller's own trap-freedom check is PROVED (so the inlined call cannot reach
    the trap). A symbolic / keyword / starred call argument, a call passing exactly the witness, or any caller
    left UNKNOWN or REFUTED keeps the finding (surface, do not hide)."""
    calls = _calls_to(key, repo)
    callers = {ck for ck, _ in calls if ck != key}
    if not calls or not callers:
        return False                                          # no in-repo caller: the standalone finding stands
    try:
        params = [a.arg for a in _fndef(repo[key]).args.args]
    except Unsupported:
        params = []
    if witness and params:                                    # (a) constant-call-site exclusion
        excluded_all, reachable = True, False
        for _ck, c in calls:
            if c.keywords or any(isinstance(a, ast.Starred) for a in c.args) or len(c.args) > len(params):
                excluded_all = False                          # an argument the analysis cannot pin
                continue
            this_excl = False
            for i, a in enumerate(c.args):
                p = params[i]
                if p in witness:
                    cval = _const_arg_value(a)
                    if cval is None:
                        excluded_all = False                  # a symbolic witnessing argument: could be the witness
                    elif cval == witness[p]:
                        reachable = True                      # a call passes exactly the witness value
                    else:
                        this_excl = True                      # this parameter is pinned away from the witness
            if not this_excl:
                excluded_all = False
        if reachable:
            return False
        if excluded_all:
            return True
    cv = [verdict_by_key.get(ck) for ck in callers]           # (b) every caller verified trap free
    return bool(cv) and all(s == PROVED for s in cv)


def _build_finding(label, v, src, repo, fname, kind, execute, classinfo=None):
    """One scan finding, confirmed and classified. In execute mode the sandbox replays/samples a witness and
    names the exception, so the finding is classified bug | input-validation | unconfirmed (a confirmed
    ZeroDivision/Index/Key/Type is a bug; a confirmed ValueError/AssertionError the body explicitly raises is
    intended validation; a method or a symbolic verdict the sandbox cannot reproduce is unconfirmed). Symbolic
    findings are unconfirmed hints, with a standalone-method finding demoted (its self/attributes are
    unmodeled). A confirmed (or otherwise replayable) finding carries a runnable repro test and the source."""
    sev, hint = _scan_severity(v)
    if not execute:
        confirm = None
    elif kind == "method" and classinfo:                        # construct a real instance and invoke the method
        confirm = _confirm_method(classinfo[0], classinfo[1], src, v)
    else:
        confirm = _confirm_finding(src, repo, v)
    exception = witness = None
    if confirm is not None and confirm["confirmed"]:
        exception, witness = confirm["exception"], confirm["witness"]
        if _has_explicit_raise(src, exception):                  # any exception the body explicitly raises (an empty
            classification, rank, txt = "input-validation", 1, ("confirmed intended raise: %s (the body raises it; "  # container's
                "input validation)" % exception)                                                        # raise IndexError) is
        elif exception == "TypeError":                                                                   # the contract, not a bug
            # a TypeError under sampled inputs is overwhelmingly a type mismatch from sampling (e.g. an int for a
            # string parameter the kind inference missed), not a function bug -- the edge-case traps cannot arise
            # that way; surface it as unconfirmed rather than a confirmed bug.
            classification, rank, txt = "unconfirmed", 1, "a TypeError under sampled inputs (likely a type mismatch, not a bug)"
        else:
            _short = label.split(".")[-1]                        # a single-underscore private helper (not a dunder)
            if _short.startswith("_") and not _short.startswith("__"):   # relies on caller-maintained invariants, so a
                classification, rank, txt = "bug", 2, ("confirmed %s in a private helper -- likely an internal "    # standalone
                    "precondition; verify it is reachable from the public API" % exception)                        # crash is
            else:                                                                                                  # often not
                classification, rank, txt = "bug", 3, "confirmed bug: %s" % exception                              # reachable
    elif confirm is not None:                                    # executed, but the sandbox did not reproduce a trap
        classification, rank = "unconfirmed", (1 if kind == "method" else 2)
        txt = "unconfirmed: the sandbox did not reproduce a trap"
    elif "intended input validation" in (v.reason or ""):       # symbolic: the only trap is an explicit raise/assert
        classification, rank = "input-validation", 0            # (the reason annotator re-checked that stripping the
        txt = "reachable raise the body makes explicitly (intended input validation, not a crash)"   # guards proves it)
    elif kind == "method":                                      # symbolic only: a standalone method, self/attrs unmodeled
        classification, rank, txt = "unconfirmed", 1, "method triaged standalone (self/attributes unmodeled) -- low confidence"
    else:                                                       # symbolic only: a function hint, run --execute to confirm
        _short = label.split(".")[-1]                            # a single-underscore private helper (not a dunder)
        if _short.startswith("_") and not _short.startswith("__"):   # may trap only on inputs its callers never pass
            classification, rank = "unconfirmed", 1                  # (a caller-maintained precondition), so demote and
            txt = hint + " in a private helper -- reachability depends on its callers; run with --execute to confirm"
        else:
            classification, rank = "unconfirmed", (2 if sev >= 2 else 1)
            txt = hint + " -- run with --execute to confirm"
    if kind == "method" and classinfo and confirm is not None and confirm["confirmed"]:
        _margs = ", ".join("%s=%s" % (k, witness[k]) for k in witness) if witness else ""
        cex = "%s().%s(%s)" % (classinfo[1], label.split(".")[-1], _margs)   # on a constructed instance
    else:
        cex = (", ".join("%s=%s" % (k, witness[k]) for k in witness) if witness else v.counterexample)
    repl = witness or (v.counterexample_inputs if kind == "function" else None)
    repro = None
    if repl and kind == "function":
        try:
            from .repro import repro_test
            repro = repro_test(Verdict(REFUTED, v.prop, fname, v.technique, counterexample_inputs=repl),
                               _repro_module(fname, src, repo), func=fname)
        except Exception:
            repro = None
    return {"location": label, "kind": kind, "classification": classification, "rank": rank, "severity": sev,
            "label": txt, "exception": exception, "counterexample": cex, "witness": witness,
            "reason": v.reason, "repro": repro, "source": src.strip()}


def _escalate_unknown(label, src, repo, fname):
    """Pursue a symbolic UNKNOWN in execute mode rather than dropping it: guided fuzzing in the sandbox over a
    spread of edge-case inputs (empty containers, zero, small ints, short strings). If any input raises a
    modeled trap, report a distinct `suspected` finding with the triggering input. Returns the finding dict or
    None. A TypeError under fuzzed inputs is a sampling type mismatch, not a function bug, so it is not reported."""
    import itertools as _it
    try:
        fn = _fndef(src)
    except Exception:
        return None
    params = [a.arg for a in fn.args.args]
    if not params or len(params) > 3 or fn.args.vararg or fn.args.kwarg or fn.args.kwonlyargs:
        return None
    pool = [0, 1, -1, 2, [], [0], [0, 0], "", "x", {}, {0: 0}]    # edge cases the symbolic engine could not rule out
    combos = [list(c) for c in _it.islice(_it.product(pool, repeat=len(params)), 0, 400)]
    res = core.sandbox_run_batch_typed(src, repo or {}, fname, combos)
    if res is None:
        return None
    from .domains import _MODELED_TRAPS
    for tup, r in zip(combos, res):
        if r and r[0] == "raise" and r[1] in _MODELED_TRAPS and r[1] != "TypeError":
            wit = {params[i]: tup[i] for i in range(len(params))}
            repro = None
            try:
                from .repro import repro_test
                repro = repro_test(Verdict(REFUTED, "trap freedom", fname, "sandbox fuzz", counterexample_inputs=wit),
                                   _repro_module(fname, src, repo), func=fname)
            except Exception:
                repro = None
            return {"location": label, "kind": "function", "classification": "suspected", "rank": 1, "severity": 2,
                    "label": "suspected %s, found by sandbox fuzzing after a symbolic UNKNOWN "
                             "(reachability not symbolically confirmed)" % r[1], "exception": r[1],
                    "counterexample": ", ".join("%s=%r" % (p, wit[p]) for p in params), "witness": wit,
                    "reason": "symbolic analysis was inconclusive; a guided sandbox fuzz reached %s" % r[1],
                    "repro": repro, "source": src.strip()}
    return None


def _scan_severity(v):
    """A coarse severity (3..1) and label for a REFUTED scan finding, keyed on the verdict reason (the
    technique is normalized away by check's return). A trap the sandbox oracle executed, or a value-engine
    division / index / key / None trap, ranks above a reachable bare `raise`, which the CFG engine reports
    identically for a genuine crash and an intended input-validation `raise` (so that tier warrants review).
    This orders and labels the report; every finding is a genuinely reachable trap."""
    r = (v.reason or "").lower()
    if "concrete" in r:                                          # the sandbox oracle executed it: a confirmed crash
        return 3, "confirmed crash (executed in the sandbox)"
    if "a trap is reachable" in r:                              # value engine: a division / index / key / None trap
        return 2, "likely crash (division / index / key / None)"
    if "uncaught raise" in r:                                   # CFG: a reachable raise -- a crash, or intended
        return 1, "reachable raise (inspect: a crash or intended input validation)"
    return 2, "reachable trap"


def _normalize_url(target):
    """Normalize a casual scan target into a fetchable reference, so exact URL formatting is not needed:
      - an `owner/repo` slug                 -> https://github.com/owner/repo
      - a scheme-less host URL               -> https:// prefixed (github.com/..., raw.githubusercontent.com/...,
                                                gitlab.com/..., bitbucket.org/...)
      - a GitHub web (blob) file URL         -> its raw.githubusercontent.com form (so a browser link fetches
                                                source, not the rendered HTML page)
      - any other github.com/owner/repo/...  -> the repo root (a pull / commit / issue page becomes the repo)
    A GitHub `tree` directory URL is returned intact for the resolver (which clones the repo and scans the
    subpath); a full git/http(s) URL or a local path is returned unchanged."""
    import re
    t = target.strip().rstrip("/")
    if re.match(r"^[A-Za-z0-9_][A-Za-z0-9_.-]*/[A-Za-z0-9_][A-Za-z0-9_.-]*$", t):    # owner/repo slug
        return "https://github.com/" + t
    if re.match(r"^[A-Za-z0-9_][A-Za-z0-9_.-]*/[A-Za-z0-9_][A-Za-z0-9_.-]*/(?:blob|tree)/", t):
        t = "https://github.com/" + t                                                 # bare owner/repo/blob|tree path
    elif re.match(r"^(?:www\.)?(?:github\.com|raw\.githubusercontent\.com|gitlab\.com|bitbucket\.org)/", t):
        t = "https://" + t                                                            # scheme-less host
    t = re.sub(r"^https?://www\.github\.com/", "https://github.com/", t).split("#")[0]
    m = re.match(r"^https?://github\.com/([^/]+)/([^/?]+)/blob/(.+)$", t)
    if m:                                                                             # blob (web file) -> raw
        return "https://raw.githubusercontent.com/%s/%s/%s" % (m.group(1), m.group(2), m.group(3).split("?")[0])
    if re.match(r"^https?://github\.com/[^/]+/[^/?]+/tree/", t):                      # tree (web dir): see resolver
        return t.split("?")[0]
    m = re.match(r"^https?://github\.com/([^/]+)/([^/?]+)(?:/.*)?$", t)
    if m:                                                                             # any other github link -> repo
        return "https://github.com/%s/%s" % (m.group(1), m.group(2))
    return t


def _resolve_scan_target(target):
    """Resolve a scan target to local source. Returns (dir_path | None, file_source | None, tmp_to_clean |
    None, fetched). A local directory or .py file is used in place; a .py URL is downloaded; any other
    git/GitHub/http(s) URL is shallow-cloned. A fetched target lands in a temporary location the caller
    removes. Raises ValueError with a clear message on a bad target, a missing git, or a failed fetch."""
    import os
    if os.path.isdir(target):
        return target, None, None, False
    if os.path.isfile(target) and target.endswith(".py"):
        with open(target, encoding="utf-8") as fh:
            return None, fh.read(), None, False
    target = _normalize_url(target)                             # a GitHub blob URL -> its raw form, so a link
    low = target.lower()                                        # copied from the browser fetches source, not HTML
    if not (low.startswith("http://") or low.startswith("https://") or target.startswith("git@")):
        raise ValueError("not a directory, a .py file, or an http(s)/git URL: %s" % target)
    import re, tempfile, subprocess, urllib.request, shutil
    if low.endswith(".py"):                                      # a single-file URL: download, never execute here
        try:
            with urllib.request.urlopen(target, timeout=30) as r:
                src = r.read().decode("utf-8", "replace")
        except Exception as e:
            raise ValueError("could not download %s: %s" % (target, e))
        try:
            ast.parse(src)                                      # a page URL serves HTML, which parses to no
        except SyntaxError:                                     # functions -- fail loudly, never a false "no traps"
            raise ValueError("fetched content from %s is not valid Python (a GitHub page URL serves HTML; "
                             "use the raw file URL)" % target)
        return None, src, None, True
    tree = re.match(r"^https?://github\.com/([^/]+)/([^/]+)/tree/([^/]+)(?:/(.*))?$", target)
    if tree:                                                    # a browser directory link: clone the repo, scan the subpath
        repo_url = "https://github.com/%s/%s" % (tree.group(1), tree.group(2))
        ref, sub = tree.group(3), (tree.group(4) or "")
        tdir = tempfile.mkdtemp(prefix="touchstone_scan_")
        try:
            r = subprocess.run(["git", "clone", "--quiet", "--depth", "1", "--branch", ref, repo_url, tdir],
                               capture_output=True, text=True, timeout=300)
            if r.returncode != 0:                              # ref may be a commit SHA, not a branch: retry the default
                shutil.rmtree(tdir, ignore_errors=True)
                tdir = tempfile.mkdtemp(prefix="touchstone_scan_")
                r = subprocess.run(["git", "clone", "--quiet", "--depth", "1", repo_url, tdir],
                                   capture_output=True, text=True, timeout=300)
        except FileNotFoundError:
            shutil.rmtree(tdir, ignore_errors=True)
            raise ValueError("git is not installed; cannot clone %s" % repo_url)
        except subprocess.TimeoutExpired:
            shutil.rmtree(tdir, ignore_errors=True)
            raise ValueError("git clone timed out for %s" % repo_url)
        if r.returncode != 0:
            shutil.rmtree(tdir, ignore_errors=True)
            raise ValueError("git clone failed for %s: %s" % (repo_url, (r.stderr or "").strip().splitlines()[-1:]))
        sub_dir = os.path.realpath(os.path.join(tdir, sub)) if sub else tdir
        if not (os.path.isdir(sub_dir) and os.path.realpath(sub_dir).startswith(os.path.realpath(tdir))):
            shutil.rmtree(tdir, ignore_errors=True)
            raise ValueError("subdirectory %r not found in %s" % (sub, repo_url))
        return sub_dir, None, tdir, True
    tmp = tempfile.mkdtemp(prefix="touchstone_scan_")           # otherwise a repository: shallow clone
    try:
        subprocess.run(["git", "clone", "--quiet", "--depth", "1", target, tmp],
                       capture_output=True, text=True, timeout=300, check=True)
    except FileNotFoundError:
        shutil.rmtree(tmp, ignore_errors=True)
        raise ValueError("git is not installed; cannot clone %s" % target)
    except subprocess.CalledProcessError as e:
        shutil.rmtree(tmp, ignore_errors=True)
        raise ValueError("git clone failed for %s: %s" % (target, (e.stderr or "").strip().splitlines()[-1:]))
    except subprocess.TimeoutExpired:
        shutil.rmtree(tmp, ignore_errors=True)
        raise ValueError("git clone timed out for %s" % target)
    return tmp, None, tmp, True


def scan(target, execute=False, total=False, jobs=None, cache=None, progress=None, exclude=None):
    """Point Touchstone at a target and return a ranked trap-freedom bug report. The target is resolved
    leniently, so exact URL formatting is not required: an `owner/repo` slug, a scheme-less or full GitHub URL
    (a repo, a blob file link, a tree directory link, or any other page -- reduced to what it references), a
    raw or .py file URL, a git URL, or a local directory or .py file. A remote target is fetched (shallow git
    clone or file download) into a temporary location removed afterward.

    By default the fetched code is never executed: the triage is symbolic (check over every top-level function
    and method, following the call graph), so every finding comes back `unconfirmed`. execute=True replays each
    finding in the isolated sandbox and classifies it: a confirmed ZeroDivisionError / IndexError / KeyError /
    TypeError is a `bug`; a confirmed ValueError / AssertionError the body explicitly raises is
    `input-validation`; anything the sandbox cannot reproduce stays `unconfirmed`. Findings are ranked bugs
    first; a replayable one carries a runnable repro test and the source. The repo triage runs in parallel by
    default (a spawn pool capped at the CPU count); pass jobs to set the worker count, or jobs=1 to force serial.
    `cache`, a dict reused across runs (the CLI persists it as JSON), makes a re-scan incremental -- a unit whose
    source and inlined closure are byte-identical to the cached run is not re-triaged. `progress(done, total)` is
    called as units are decided, for a live counter on a long scan. `exclude`, a list of fnmatch globs over module
    dotted-name / path forms, drops matching modules from triage (vendored or generated code) while still loading
    them for call resolution.

    An inline `# touchstone: ignore` comment anywhere in a unit's body drops that unit's finding (marking the
    trap intentional in source), counted as `suppressed_in_source`. Returns {target, fetched, executed,
    functions, proved, refuted, unknown, bugs, input_validation, unconfirmed, suppressed_in_source, findings},
    each finding {location, module, line, kind, classification, exception, counterexample, witness, reason,
    repro, source, severity, label}."""
    import shutil
    path, single_src, tmp, fetched = _resolve_scan_target(target)
    saved = (core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION)
    core.SANDBOX_SUBJECT = bool(execute)                        # execute -> sandbox replay + oracle on; else the
    core.ALLOW_SUBJECT_EXECUTION = False                        # code is never run (no in-process path either)
    n_suppressed = 0
    try:
        if single_src is not None:
            rows, locmap, suppressed = _triage_file_verdicts(single_src, total=total)
        else:
            rows, locmap, suppressed = _triage_repo_verdicts(path, total=total, jobs=jobs, cache=cache,
                                                             progress=progress, exclude=exclude)
        raw = [_build_finding(label, v, fsrc, frepo, fname, kind, execute, classinfo)
               for label, v, fsrc, frepo, fname, kind, classinfo in rows if v.status == REFUTED]
        findings = [f for f in raw if f["location"] not in suppressed]   # drop inline `# touchstone: ignore` units
        n_suppressed = len(raw) - len(findings)
        n_refuted = len(findings)
        if execute:                                            # pursue each symbolic UNKNOWN by guided sandbox fuzzing
            for label, v, fsrc, frepo, fname, kind, classinfo in rows:   # rather than dropping it (a missed bug)
                if v.status == UNKNOWN and kind == "function":
                    sf = _escalate_unknown(label, fsrc, frepo, fname)
                    if sf is not None and sf["location"] in suppressed:
                        n_suppressed += 1
                    elif sf is not None:
                        findings.append(sf)
    finally:
        core.SANDBOX_SUBJECT, core.ALLOW_SUBJECT_EXECUTION = saved
        if tmp is not None:
            shutil.rmtree(tmp, ignore_errors=True)
    # context-confirmation: demote a private helper's finding whose trap is unreachable through its real in-repo
    # callers (constant arguments that miss the witness, or callers all verified trap free) -- a caller-maintained
    # precondition, not a candidate reachable from the public surface. Ranking only; never changes a verdict.
    vbk = {r[4]: r[1].status for r in rows if r[5] == "function"}
    crepo = next((r[3] for r in rows if r[5] == "function" and r[3]), {})
    row_by_label = {r[0]: r for r in rows}
    for f in findings:
        if f["kind"] != "function" or f["classification"] not in ("bug", "unconfirmed"):
            continue
        leaf = f["location"].split(".")[-1]
        if not (leaf.startswith("_") and not leaf.startswith("__")):
            continue
        r = row_by_label.get(f["location"])
        wit = (f["witness"] or r[1].counterexample_inputs) if r is not None else None
        if r is not None and _context_unreachable(r[4], crepo, wit, vbk):
            f["classification"] = "context-unreachable"
            f["rank"] = 0
            f["label"] = "trap unreachable through its in-repo callers (caller-maintained precondition); " + f["label"]
    proved = sum(1 for r in rows if r[1].status == PROVED)
    unknown = sum(1 for r in rows if r[1].status == UNKNOWN)
    findings.sort(key=lambda f: (-f["rank"], f["location"]))
    for f in findings:                                          # attach the source location (module path + def line)
        f["module"], f["line"] = locmap.get(f["location"], (None, None))   # for SARIF and a richer report
    cls = lambda c: sum(1 for f in findings if f["classification"] == c)
    return {"target": target, "fetched": fetched, "executed": bool(execute),
            "functions": len(rows), "proved": proved, "refuted": n_refuted, "unknown": unknown,
            "bugs": cls("bug"), "input_validation": cls("input-validation"), "unconfirmed": cls("unconfirmed"),
            "context_unreachable": cls("context-unreachable"), "suspected": cls("suspected"),
            "suppressed_in_source": n_suppressed, "findings": findings}


def finding_fingerprint(f):
    """A stable identity for a scan finding across runs -- the trap site (its dotted location) and the exception
    kind, independent of the sampled counterexample -- so a baseline can suppress findings already seen and fail
    only on a new one. The same trap reported on two runs has the same fingerprint even if the witness differs."""
    return "%s|%s" % (f.get("location", ""), f.get("exception") or f.get("classification") or "")


def baseline_partition(findings, baseline):
    """Split findings into (new, known) against a baseline -- an iterable of fingerprints from a prior run. A
    finding is `known` when its fingerprint is in the baseline, else `new`. Order within each list is preserved."""
    seen = set(baseline or ())
    new, known = [], []
    for f in findings:
        (known if finding_fingerprint(f) in seen else new).append(f)
    return new, known


def verify_system(prop, target, repo, contracts) -> Verdict:
    """Assemble per-function proofs into a whole-system proof. Every contracted function is verified
    against its contract with each call replaced by the callee's contract rather than its body
    (reusing the single-function modular check). If every function meets its contract under its
    callees' contracts, the target's contract holds for the assembled system. `contracts` maps a
    function name to (pre, post) over a parameter dict and the return value; loop-free bodies."""
    fns = {name: _fndef(src) for name, src in repo.items()}
    missing = [g for g in contracts if g not in fns]
    if missing:
        return Verdict(UNKNOWN, prop, target, "system composition", reason=f"no such function: {missing[0]}")
    callee = {}                                              # verify_modular wants callee contracts over a
    for g, (gpre, gpost) in contracts.items():               # positional argument list, so adapt the dict form
        gp = [a.arg for a in fns[g].args.args]
        callee[g] = (lambda al, gpre=gpre, gp=gp: gpre({gp[i]: al[i] for i in range(len(gp))}),
                     lambda al, r, gpost=gpost, gp=gp: gpost({gp[i]: al[i] for i in range(len(gp))}, r))
    for name, (pre, post) in contracts.items():
        v = verify_modular(prop, name, repo[name], pre, post, callee)
        if v.status != PROVED:
            return Verdict(v.status, prop, target, "system composition", reason=f"{name}: {v.reason}")
    return Verdict(PROVED, prop, target, "system composition (per-function contracts assembled)",
                   reason="every function meets its contract under its callees' contracts")


def verify_heap_property(prop, target, src, post) -> Verdict:
    """Verify a property of a loop-free function that allocates and mutates objects through
    the general heap. `object()`/`new()` allocate fresh distinct identities; aliasing copies
    a reference, so a write through one name is observed through every alias; attribute
    writes leave disjoint objects and other attributes unchanged (the frame). `post(z3args,
    return_value)` must hold for all inputs."""
    mod = _parse(src)
    classes = {n.name: n for n in mod.body if isinstance(n, ast.ClassDef)}
    fns = [n for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    if not fns:
        return Verdict(UNKNOWN, prop, target, "heap", reason="no function to verify")
    fn = next((n for n in fns if n.name == target), fns[-1])   # the named target, else the last
    args = [a.arg for a in fn.args.args]
    z3args = {a.arg: _param_term(a) for a in fn.args.args}
    traps, rets = [], []
    try:                                                       # seed each container-valued attribute's kind, so a
        kinds0 = core._attr_kinds(classes)                     # self.<attr> list/dict/set drives its own operations
        _heap_walk(fn.body, dict(z3args), {"@classes": classes}, z3.BoolVal(True), [0], traps, rets, kinds0)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "heap", reason=str(u))
    if not rets:                                            # returns None on every path: a postcondition over
        st, model = _solve_corro(z3.Or(*traps) if traps else z3.BoolVal(False))   # the return is vacuous, so
        if st == PROVED:                                    # only a reachable trap can refute (trap freedom)
            return Verdict(PROVED, prop, target, "heap (objects + lists: identity, aliasing, frame)")
        if st == REFUTED:
            model = minimize_witness(z3.Or(*traps), z3args, args) or model
            cex, cex_in = _model_cex(model, z3args, args)
            return Verdict(REFUTED, prop, target, "heap", counterexample=cex, counterexample_inputs=cex_in)
        return Verdict(UNKNOWN, prop, target, "heap", reason="no value returned")
    wants_heap = post.__code__.co_argcount >= 3              # post(z3args, ret[, heap]) -- heap-quantifying spec
    bad = []
    for pc, val, hsnap in rets:                              # check the postcondition at each return point
        claim = post(z3args, val, hsnap) if wants_heap else post(z3args, fold([(pc, val)]))
        bad.append(z3.And(pc, z3.Not(claim)))
    trap_or = z3.Or(*traps) if traps else z3.BoolVal(False)   # IndexError etc. refute the property
    claim = z3.Or(trap_or, *bad)
    status, model = _solve_corro(claim)
    if status == PROVED:
        return Verdict(PROVED, prop, target, "heap (objects + lists: identity, aliasing, frame)")
    if status == REFUTED:
        model = minimize_witness(claim, z3args, args) or model
        cex, cex_in = _model_cex(model, z3args, args)
        return Verdict(REFUTED, prop, target, "heap", counterexample=cex, counterexample_inputs=cex_in)
    return Verdict(UNKNOWN, prop, target, "heap", reason="solver returned unknown")


# --------------------------------------------------------------------------- #
# None as a first-class value (Optional). A value is None or an integer, modeled as     #
# the datatype Opt = none | some(int). None flows through assignments, merges across     #
# branches, and is tested with is / is not / == / != ; truthiness follows Python (None    #
# and 0 are falsy). Using None where an integer is required -- arithmetic, ordering, or   #
# negation -- is a TypeError, emitted as a trap exactly as division by zero is. This is   #
# None as a value, not merely the return-path condition the value engine already tracks.  #
# --------------------------------------------------------------------------- #
_Opt = z3.Datatype("Opt")
_Opt.declare("none")
_Opt.declare("some", ("oval", z3.IntSort()))
_Opt = _Opt.create()


def opt_none():
    return _Opt.none


def opt_some(k):
    return _Opt.some(z3.IntVal(k) if isinstance(k, int) else k)


def opt_is_none(t):
    return _Opt.is_none(t)


def opt_val(t):
    return _Opt.oval(t)


def _opt_truth(t):
    return z3.And(_Opt.is_some(t), _Opt.oval(t) != 0)


def _opt_eval(node, env, traps, pc):
    if isinstance(node, ast.Constant):
        v = node.value
        if v is None:
            return _Opt.none
        if isinstance(v, bool):
            return _Opt.some(z3.IntVal(1 if v else 0))
        if isinstance(v, int):
            return _Opt.some(z3.IntVal(v))
        raise Unsupported(f"optional constant {type(v).__name__}")
    if isinstance(node, ast.Name):
        if node.id not in env:
            raise Unsupported(f"free variable {node.id}")
        return env[node.id]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        x = _opt_eval(node.operand, env, traps, pc)
        traps.append(z3.And(pc, _Opt.is_none(x)))                # -None is a TypeError
        return _Opt.some(-_Opt.oval(x))
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        x = _opt_eval(node.operand, env, traps, pc)              # not x is total (None is falsy)
        return _Opt.some(z3.If(_opt_truth(x), z3.IntVal(0), z3.IntVal(1)))
    if isinstance(node, ast.BoolOp):
        is_and = isinstance(node.op, ast.And)                    # value semantics: returns an operand
        vals = [_opt_eval(v, env, traps, pc) for v in node.values]
        acc = vals[-1]
        for v in reversed(vals[:-1]):
            acc = z3.If(_opt_truth(v), acc, v) if is_and else z3.If(_opt_truth(v), v, acc)
        return acc
    if isinstance(node, ast.BinOp):
        op = type(node.op)
        if op not in _BINOPS:
            raise Unsupported(f"optional binop {op.__name__}")
        l = _opt_eval(node.left, env, traps, pc)
        r = _opt_eval(node.right, env, traps, pc)
        traps.append(z3.And(pc, z3.Or(_Opt.is_none(l), _Opt.is_none(r))))   # None in arithmetic
        lv, rv = _Opt.oval(l), _Opt.oval(r)
        if op in (ast.FloorDiv, ast.Mod):                                   # // and % over present ints
            traps.append(z3.And(pc, _Opt.is_some(l), _Opt.is_some(r), rv == 0))   # ZeroDivisionError
            return _Opt.some(py_floordiv(lv, rv) if op is ast.FloorDiv else py_mod(lv, rv))
        return _Opt.some(_BINOPS[op](lv, rv))
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        op = node.ops[0]
        l = _opt_eval(node.left, env, traps, pc)
        r = _opt_eval(node.comparators[0], env, traps, pc)
        if isinstance(op, (ast.Is, ast.IsNot, ast.Eq, ast.NotEq)):
            eq = z3.If(_Opt.is_none(l), _Opt.is_none(r),         # None==None; None!=int; int==int by value
                       z3.And(_Opt.is_some(r), _Opt.oval(l) == _Opt.oval(r)))
            b = eq if isinstance(op, (ast.Is, ast.Eq)) else z3.Not(eq)
            return _Opt.some(z3.If(b, z3.IntVal(1), z3.IntVal(0)))
        traps.append(z3.And(pc, z3.Or(_Opt.is_none(l), _Opt.is_none(r))))   # None < int is a TypeError
        return _Opt.some(z3.If(_CMP[type(op)](_Opt.oval(l), _Opt.oval(r)), z3.IntVal(1), z3.IntVal(0)))
    raise Unsupported(f"optional expression {type(node).__name__}")


def _opt_walk(stmts, env, pc, traps, rets):
    falls = [(dict(env), pc)]
    for s in stmts:
        nxt = []
        for e, p in falls:
            if isinstance(s, ast.Return):
                rets.append((p, _Opt.none if s.value is None else _opt_eval(s.value, e, traps, p)))
            elif isinstance(s, ast.Assign):
                if len(s.targets) != 1 or not isinstance(s.targets[0], ast.Name):
                    raise Unsupported("optional assignment target")
                e2 = dict(e)
                e2[s.targets[0].id] = _opt_eval(s.value, e2, traps, p)
                nxt.append((e2, p))
            elif isinstance(s, ast.If):
                c = _opt_truth(_opt_eval(s.test, e, traps, p))
                nxt += _opt_walk(s.body, e, z3.And(p, c), traps, rets)
                nxt += _opt_walk(s.orelse, e, z3.And(p, z3.Not(c)), traps, rets)
            else:
                raise Unsupported(f"optional statement {type(s).__name__}")
        falls = nxt
    return falls


def verify_optional(prop, target, src, post, pre=None) -> Verdict:
    """Verify a property of a loop-free function over Optional[int] values, where None is a
    first-class value. Unannotated parameters are nullable; `int`-annotated parameters are
    present. `post(z3args, ret)` is a Z3 Bool over the Opt-sorted parameters and result;
    `pre(z3args)` optionally constrains the inputs. A reachable use of None as a number is a
    trap and refutes the property, just as a division by zero does."""
    fn = _fndef(src)
    args = [a.arg for a in fn.args.args]

    def mk(a):
        ann = a.annotation
        if isinstance(ann, ast.Name) and ann.id == "int":
            return _Opt.some(z3.Int(a.arg))                      # annotated int: present
        return z3.Const(a.arg, _Opt)                             # otherwise nullable

    z3args = {a.arg: mk(a) for a in fn.args.args}
    traps, rets = [], []
    try:
        open_falls = _opt_walk(fn.body, dict(z3args), z3.BoolVal(True), traps, rets)
        for _e, p in open_falls:
            rets.append((p, _Opt.none))                          # fell off the end -> None
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "optional", reason=str(u))
    ret = _Opt.none
    for pc, v in reversed(rets):
        ret = z3.If(pc, v, ret)
    pre_c = pre(z3args) if pre else z3.BoolVal(True)
    trap_or = z3.Or(*traps) if traps else z3.BoolVal(False)
    status, model = _solve_corro(z3.And(pre_c, z3.Or(trap_or, z3.Not(post(z3args, ret)))))
    if status == PROVED:
        return Verdict(PROVED, prop, target, "optional (None as a first-class value)")
    if status == REFUTED:
        cex = ", ".join(f"{a}={model.eval(z3args[a], model_completion=True)}" for a in args)
        return Verdict(REFUTED, prop, target, "optional", counterexample=cex)
    return Verdict(UNKNOWN, prop, target, "optional", reason="solver returned unknown")


def _mentions_none(src) -> bool:
    """Whether the function literally involves None: a None constant (a `= None`, a `return None`, an
    `x is None` guard, or a None default). Only such a function needs the optional (None-carrying) engine,
    so None-free code keeps the integer CHC encoding unchanged."""
    try:
        return any(isinstance(n, ast.Constant) and n.value is None for n in ast.walk(_parse(src)))
    except Exception:
        return False


class _Maybe:
    """A possibly-None integer for the trap-freedom Horn encoding: `none` is a z3 Bool (the value may be
    None) and `val` is its integer value when present. Carried as two relation arguments (a Bool flag and an
    Int), so the encoding stays in linear integer arithmetic -- no datatype accessor on a Horn variable,
    which Spacer rejects -- while modeling None as a first-class value across the loop back edge."""
    __slots__ = ("none", "val")
    def __init__(self, none, val):
        self.none, self.val = none, val


def _mb_split(v):
    """(none-flag, int value) of an evaluated value; a plain z3 Int is present (none = False)."""
    return (v.none, v.val) if isinstance(v, _Maybe) else (z3.BoolVal(False), v)


def _optnull_eval(node, env, traps, pc, aux, auxv):
    """Evaluate an integer-or-None expression to a z3 Int (present) or a _Maybe, appending the path-guarded
    conditions under which it traps (None in arithmetic / ordering, a zero divisor) to `traps`. Floor
    division and modulo are linearized (a fresh quotient in `auxv` with its bounds in `aux`) so the encoding
    stays first-order for Spacer. The integer + None fragment only; raises Unsupported on anything else
    (a call, subscript, string, or float)."""
    if isinstance(node, ast.Constant):
        x = node.value
        if x is None:
            return _Maybe(z3.BoolVal(True), z3.IntVal(0))
        if isinstance(x, bool):
            return z3.IntVal(1 if x else 0)
        if isinstance(x, int):
            return z3.IntVal(x)
        raise Unsupported(f"optional constant {type(x).__name__}")
    if isinstance(node, ast.Name):
        if node.id not in env:
            raise Unsupported(f"optional free variable {node.id}")
        return env[node.id]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        n, x = _mb_split(_optnull_eval(node.operand, env, traps, pc, aux, auxv))
        traps.append(z3.And(pc, n))                                      # -None is a TypeError
        return -x
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return z3.If(_optnull_truth(node.operand, env, traps, pc, aux, auxv), z3.IntVal(0), z3.IntVal(1))
    if isinstance(node, ast.BinOp):
        op = type(node.op)
        if op not in _BINOPS:
            raise Unsupported(f"optional binop {op.__name__}")
        ln, lx = _mb_split(_optnull_eval(node.left, env, traps, pc, aux, auxv))
        rn, rx = _mb_split(_optnull_eval(node.right, env, traps, pc, aux, auxv))
        traps.append(z3.And(pc, z3.Or(ln, rn)))                          # None in arithmetic
        if op in (ast.FloorDiv, ast.Mod):
            traps.append(z3.And(pc, z3.Not(ln), z3.Not(rn), rx == 0))    # ZeroDivisionError
            q = z3.Int(f"_oq{len(auxv)}"); auxv.append(q)                # floor division, linearized
            aux.append(z3.Implies(rx > 0, z3.And(rx * q <= lx, lx < rx * q + rx)))
            aux.append(z3.Implies(rx < 0, z3.And(rx * q >= lx, lx > rx * q + rx)))
            return q if op is ast.FloorDiv else (lx - rx * q)
        return _BINOPS[op](lx, rx)
    if isinstance(node, (ast.Compare, ast.BoolOp)):
        return z3.If(_optnull_truth(node, env, traps, pc, aux, auxv), z3.IntVal(1), z3.IntVal(0))
    raise Unsupported(f"optional expression {type(node).__name__}")


def _optnull_truth(node, env, traps, pc, aux, auxv):
    """The z3 Bool truth value of a test over integer-or-None values, with the traps it raises (ordering a
    None, None in arithmetic inside the test). Models and / or short-circuiting and the is / is not / == /
    != / ordering comparisons with None exactly (None == int is False, None < int traps), so a guard that
    rules None out is reflected on the branch that follows it."""
    if isinstance(node, ast.BoolOp):
        is_and = isinstance(node.op, ast.And)
        parts, guard = [], pc
        for v in node.values:
            pv = _optnull_truth(v, env, traps, guard, aux, auxv)
            parts.append(pv)
            guard = z3.And(guard, pv) if is_and else z3.And(guard, z3.Not(pv))   # short-circuit guard
        return z3.And(*parts) if is_and else z3.Or(*parts)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return z3.Not(_optnull_truth(node.operand, env, traps, pc, aux, auxv))
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        op = node.ops[0]
        ln, lx = _mb_split(_optnull_eval(node.left, env, traps, pc, aux, auxv))
        rn, rx = _mb_split(_optnull_eval(node.comparators[0], env, traps, pc, aux, auxv))
        if isinstance(op, (ast.Is, ast.IsNot, ast.Eq, ast.NotEq)):
            eq = z3.If(ln, rn, z3.And(z3.Not(rn), lx == rx))             # None==None; None!=int; int==int by value
            return eq if isinstance(op, (ast.Is, ast.Eq)) else z3.Not(eq)
        traps.append(z3.And(pc, z3.Or(ln, rn)))                          # ordering a None is a TypeError
        return _CMP[type(op)](lx, rx)
    n, x = _mb_split(_optnull_eval(node, env, traps, pc, aux, auxv))     # atom truthiness: present and nonzero
    return z3.And(z3.Not(n), x != 0)


def _nullable_vars(fn):
    """The local names None can flow to: assigned the None literal, or assigned (directly, through a
    conditional expression, or through and / or) from a nullable name. A least fixpoint, so a chain of
    None-carrying assignments is all included. These get the optional (flag + value) encoding; the rest stay
    plain integers."""
    null = set()

    def rhs_null(v):
        if isinstance(v, ast.Constant):
            return v.value is None
        if isinstance(v, ast.Name):
            return v.id in null
        if isinstance(v, ast.IfExp):
            return rhs_null(v.body) or rhs_null(v.orelse)
        if isinstance(v, ast.BoolOp):
            return any(rhs_null(o) for o in v.values)
        return False

    changed = True
    while changed:
        changed = False
        for n in ast.walk(fn):
            if (isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                    and n.targets[0].id not in null and rhs_null(n.value)):
                null.add(n.targets[0].id); changed = True
    return null


def _optnull_apply(stmts, state, traps, nullable, aux, auxv):
    """Apply a straight-line CFG block over the integer-or-None state. A non-nullable target an assignment
    would make None means the nullable analysis under-approximated, so abstain (Unsupported) rather than
    drop the value into an integer slot."""
    st = dict(state)
    T = z3.BoolVal(True)
    for s in stmts:
        if isinstance(s, ast.Assign):
            if len(s.targets) != 1 or not isinstance(s.targets[0], ast.Name):
                raise Unsupported("optional assignment target")
            val = _optnull_eval(s.value, st, traps, T, aux, auxv)
            nm = s.targets[0].id
            if isinstance(val, _Maybe) and nm not in nullable:
                raise Unsupported("a non-nullable variable became optional")
            st[nm] = val
        elif isinstance(s, ast.Expr):
            _optnull_eval(s.value, st, traps, T, aux, auxv)  # a bare expression statement: for its traps
        else:
            raise Unsupported(f"optional block statement {type(s).__name__}")
    return st


def verify_no_raise_optional(prop, target, src, pre_node=None, repo=None, timeout=4000) -> Verdict:
    """Trap freedom with None carried through the whole-function Horn encoding as a first-class value, so a None
    that reaches arithmetic across a loop refutes rather than abstaining, and a None a guard rules out proves.
    Each nullable variable is encoded as a (may-be-None flag, integer value) pair in the per-block CHC relations
    (the rest plain integers), so None-ness flows through assignments, branch merges, and the loop back edge in
    linear integer arithmetic Spacer decides. `pre_node`'s parameters are taken present. UNKNOWN outside the
    integer + None fragment (a call, subscript, string, or float)."""
    src = _lower_list_lengths(src)
    gated = _definite_assignment_guard(prop, target, "exception safety (optional)", [src])
    if gated is not None:
        return gated
    fn = _fndef(src)
    params = [a.arg for a in fn.args.args]
    nullable = _nullable_vars(fn)
    try:
        blocks, entry = _build_cfg(fn.body)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "exception safety (optional)", reason=str(u))
    order = _cfg_vars(fn, blocks)
    cur, declvars, arg_sorts = {}, [], []
    for v in order:
        if v in nullable:
            nv, xv = z3.Bool("n_" + v), z3.Int("x_" + v)
            cur[v] = _Maybe(nv, xv); declvars += [nv, xv]; arg_sorts += [z3.BoolSort(), z3.IntSort()]
        else:
            xv = z3.Int("x_" + v); cur[v] = xv; declvars.append(xv); arg_sorts.append(z3.IntSort())
    R = {bid: z3.Function(f"OptR{bid}", *(arg_sorts + [z3.BoolSort()])) for bid in blocks}
    Err = z3.Function("OptErr", z3.BoolSort())
    rules = []
    auxv = []                                                # fresh quotient variables from linearized // and %
    T = z3.BoolVal(True)

    def tup(state):
        out = []
        for v in order:
            sv = state[v]
            if v in nullable:
                n, x = _mb_split(sv); out += [n, x]
            elif isinstance(sv, _Maybe):
                raise Unsupported("a non-nullable variable became optional")
            elif not (z3.is_expr(sv) and z3.is_int(sv)):       # the relation slot is Int-sorted, so a float or other
                raise Unsupported("a non-integer value crosses a block")   # non-integer crossing a block: abstain
            else:
                out.append(sv)
        return out

    try:
        entry_pre = [z3.Not(cur[p].none) for p in params if p in nullable]   # parameters are present (non-None)
        if pre_node is not None:
            ptraps, paux = [], []
            pv = _optnull_truth(pre_node, {p: cur[p] for p in params}, ptraps, T, paux, auxv)
            if ptraps:
                return Verdict(UNKNOWN, prop, target, "exception safety (optional)", reason="precondition uses None")
            entry_pre += paux + [pv]
        init = {}
        for v in order:
            if v in params:
                init[v] = cur[v]
            elif v in nullable:
                init[v] = _Maybe(z3.BoolVal(True), z3.IntVal(0))   # uninitialized local: None (definite-assignment gated)
            else:
                init[v] = z3.IntVal(0)
        rules.append((R[entry](*tup(init)), entry_pre))
        for bid, b in blocks.items():
            baux, btraps = [], []
            after = _optnull_apply(b.assigns, cur, btraps, nullable, baux, auxv)
            term = b.term
            cond, cond_traps, ret_traps = None, [], []
            if term and term[0] == "branch":
                cond = _optnull_truth(term[1], after, cond_traps, T, baux, auxv)
            elif term and term[0] == "return" and term[1] is not None:
                _optnull_eval(term[1], after, ret_traps, T, baux, auxv)   # the returned expression is trap-checked
            body = [R[bid](*tup(cur))] + baux                # the block, plus its division-definedness constraints
            for t in btraps + cond_traps + ret_traps:        # any None-in-arithmetic / zero-divisor trap
                rules.append((Err(), body + [t]))
            if term is None:
                continue
            if term[0] == "goto":
                rules.append((R[term[1]](*tup(after)), body))
            elif term[0] == "branch":
                rules.append((R[term[2]](*tup(after)), body + [cond]))
                rules.append((R[term[3]](*tup(after)), body + [z3.Not(cond)]))
            elif term[0] == "raise":
                rules.append((Err(), body))                  # a reachable uncaught raise (an assert is one)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "exception safety (optional)", reason=str(u))

    return _solve_horn(prop, target, "exception safety (optional)",
                       "exception safety (optional: None as a value, CFG/CHC)",
                       list(R.values()) + [Err], [*declvars, *auxv], rules, Err(), corroborate=False,
                       on_error=lambda m: "engine error",
                       proved_reason="no uncaught raise or None-in-arithmetic reachable",
                       refuted_reason="a None reaches arithmetic (or an uncaught raise) on some path")


def verify_deductive(prop, target, src, pre, inv, post, repo) -> Verdict:
    fn = _fndef(src)
    args = [a.arg for a in fn.args.args]
    ctx = Ctx(repo)

    init_stmts, loop, ret, bad = [], None, None, False
    for s in fn.body:
        if isinstance(s, ast.While):
            if loop is None:
                loop = s
            else:
                bad = True                 # a second loop is not single-loop
        elif isinstance(s, ast.Return):
            ret = s
        elif loop is None:
            init_stmts.append(s)
        else:
            bad = True                     # a statement after the loop would be dropped
    if bad or loop is None or ret is None:
        return Verdict(UNKNOWN, prop, target, "deductive", reason="not a single-loop function")

    try:
        base = {a: z3.Int(a) for a in args}
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        init_state = _apply_assigns(init_stmts, base, ctx)      # state at loop head, 1st time
        init_traps = _trap_or(ctx.traps)
        loop_vars = sorted(set(init_state) - set(args))
        sym = dict(base)                                        # arbitrary loop-head state
        for v in loop_vars:
            sym[v] = z3.Int(v + "_s")
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        guard = ev_bool(loop.test, sym, ctx)
        body_state = _apply_assigns(loop.body, sym, ctx)
        body_traps = _trap_or(ctx.traps)
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        ret_at_exit = ev(ret.value, sym, ctx)
        ret_traps = _trap_or(ctx.traps)
        ctx.traps = None
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "deductive", reason=str(u))

    # VC0 safety: no division by zero reachable in init, body, or the return
    for cond, why in [(z3.And(pre(base), init_traps), "division by zero before the loop"),
                      (z3.And(inv(sym), guard, body_traps), "division by zero in the loop body"),
                      (z3.And(inv(sym), z3.Not(guard), ret_traps), "division by zero in the return")]:
        s0, _ = _solve_corro(cond)
        if s0 == REFUTED:
            return Verdict(REFUTED, prop, target, "deductive (Hoare)", reason=why)
        if s0 == UNKNOWN:
            return Verdict(UNKNOWN, prop, target, "deductive (Hoare)", reason="solver unknown: " + why)

    # VC1 initiation: pre AND init => inv
    st1, m1 = _solve_corro(z3.And(pre(base), z3.Not(inv(init_state))))
    if st1 != PROVED:
        return Verdict(REFUTED if st1 == REFUTED else UNKNOWN, prop, target,
                       "deductive (Hoare)", reason="initiation fails")
    # VC2 preservation: inv AND guard => inv[body]
    st2, m2 = _solve_corro(z3.And(inv(sym), guard, z3.Not(inv(body_state))))
    if st2 != PROVED:
        cex = None
        if st2 == REFUTED:
            cex = ", ".join(f"{v}={m2.eval(sym[v], model_completion=True)}" for v in loop_vars)
        return Verdict(REFUTED if st2 == REFUTED else UNKNOWN, prop, target,
                       "deductive (Hoare)", counterexample=cex, reason="invariant not preserved")
    # VC3 postcondition: inv AND not guard => post
    st3, m3 = _solve_corro(z3.And(inv(sym), z3.Not(guard), z3.Not(post(base, ret_at_exit))))
    if st3 != PROVED:
        return Verdict(REFUTED if st3 == REFUTED else UNKNOWN, prop, target,
                       "deductive (Hoare)", reason="postcondition fails")
    return Verdict(PROVED, prop, target, "deductive (Hoare, unbounded loop)")


_HELD, _NOTHELD = "HELD", "NOTHELD"


def _meet(a, b):                       # held only if held on ALL incoming paths
    return _HELD if (a == _HELD and b == _HELD) else _NOTHELD


def verify_no_leak(prop, target, src) -> Verdict:
    """Resource safety over handle identity. A handle from open(...) must be released before return:
    h.close() through any alias, `with open(...) as x`, returning it, or storing it into an object or
    container (ownership escapes). Names map to the handle they hold, so a close through an alias
    counts and a handle kept only through an alias after the original is rebound still leaks. A handle
    open on any path at return is the counterexample."""
    mod = ast.parse(textwrap.dedent(src))                    # raw AST: `with` is not desugared away here
    fn = next((n for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
    if fn is None:
        return Verdict(UNKNOWN, prop, target, "resource safety", reason="no function")
    hid = [0]
    leaks = []

    def opener(node):
        return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "open"

    def handle_of(node, env):
        """The handle a value expression denotes: a fresh one for open(...), the handle a name
        currently holds, or None."""
        if opener(node):
            hid[0] += 1
            return hid[0]
        if isinstance(node, ast.Name):
            return env.get(node.id)
        return None

    def walk(stmts, env, opens):
        env = dict(env); opens = set(opens)
        for s in stmts:
            if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
                name = s.targets[0].id
                if opener(s.value):
                    h = handle_of(s.value, env); env[name] = h; opens.add(h)      # fresh open handle
                elif isinstance(s.value, ast.Name) and env.get(s.value.id) is not None:
                    env[name] = env[s.value.id]                                   # alias an existing handle
                else:
                    env[name] = None                                             # rebinding drops this name's ref
            elif (isinstance(s, ast.Assign) and s.targets
                  and isinstance(s.targets[0], (ast.Attribute, ast.Subscript))):
                h = handle_of(s.value, env)                                       # handle stored into the heap:
                if h is not None:
                    opens.discard(h)                                             # ownership escapes this function
            elif (isinstance(s, ast.Expr) and isinstance(s.value, ast.Call)
                  and isinstance(s.value.func, ast.Attribute) and s.value.func.attr == "close"
                  and isinstance(s.value.func.value, ast.Name)):
                h = env.get(s.value.func.value.id)
                if h is not None:
                    opens.discard(h)                                             # close through this name or an alias
            elif isinstance(s, ast.With):
                managed = []
                for it in s.items:
                    if opener(it.context_expr):
                        hid[0] += 1; h = hid[0]; opens.add(h); managed.append(h)
                        if isinstance(it.optional_vars, ast.Name):
                            env[it.optional_vars.id] = h
                    elif isinstance(it.optional_vars, ast.Name):
                        env[it.optional_vars.id] = handle_of(it.context_expr, env)
                env, opens = walk(s.body, env, opens)
                opens -= set(managed)                                            # with closes its managed handles
            elif isinstance(s, ast.If):
                ea, oa = walk(s.body, env, opens)
                eb, ob = walk(s.orelse, env, opens)
                opens = oa | ob                                                  # open on either branch may leak
                env = {k: (ea.get(k) if ea.get(k) == eb.get(k) else None)
                       for k in set(ea) | set(eb)}                               # keep a name's handle only if agreed
            elif isinstance(s, ast.Return):
                o = set(opens)
                h = handle_of(s.value, env) if s.value is not None else None
                if h is not None:
                    o.discard(h)                                                 # returning a handle hands out ownership
                if o:
                    leaks.append(sorted(o))
                return env, set()                                                # this path has returned
            elif isinstance(s, (ast.While, ast.For)):
                walk(s.body, env, opens)                                         # a handle opened in a loop leaks
        return env, opens

    _env, rem = walk(fn.body, {}, set())
    if rem:
        leaks.append(sorted(rem))                            # fell off the end with handles open
    if leaks:
        return Verdict(REFUTED, prop, target, "resource safety",
                       counterexample=f"resource leak: handle {leaks[0]} not closed on some path")
    return Verdict(PROVED, prop, target, "resource safety (no leak on any path)")


def verify_lock(prop, target, src, repo=None, guarded=("db.write",)) -> Verdict:
    """Lock safety over a held-set, for arbitrary lock variables and nested regions. A lock is held by
    acquire_lock() (a default lock), L.acquire(), or `with L:`, and released by release_lock(),
    L.release(), or leaving the with. A guarded operation (default db.write) reached with no lock held
    is a violation; a branch keeps a lock only if both arms hold it; a loop is summarized by its
    held-set fixpoint. `guarded` is a set (each op needs some lock) or a map op -> required lock."""
    fn = next((n for n in ast.parse(textwrap.dedent(src)).body
               if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
    if fn is None:
        return Verdict(UNKNOWN, prop, target, "lock safety", reason="no function")
    need = guarded if isinstance(guarded, dict) else {op: None for op in guarded}
    violations: List[str] = []

    def callname(call):
        f = call.func
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name):
            return f"{f.value.id}.{f.attr}"
        if isinstance(f, ast.Name):
            return f.id
        return None

    def interp(stmts, held, record=True):
        held = set(held)
        for s in stmts:
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Call):
                f = s.value.func
                nm = callname(s.value)
                if nm == "acquire_lock":
                    held.add("_lock")
                elif nm == "release_lock":
                    held.discard("_lock")
                elif isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.attr == "acquire":
                    held.add(f.value.id)                          # L.acquire()
                elif isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.attr == "release":
                    held.discard(f.value.id)                      # L.release()
                elif nm in need:
                    req = need[nm]
                    ok = (req in held) if req is not None else bool(held)
                    if record and not ok:
                        violations.append(ast.unparse(s).strip())
            elif isinstance(s, ast.With):
                locks = [it.context_expr.id for it in s.items if isinstance(it.context_expr, ast.Name)]
                held = interp(s.body, held | set(locks), record) - set(locks)   # with releases at scope exit
            elif isinstance(s, ast.If):
                held = interp(s.body, held, record) & interp(s.orelse, held, record)   # held only if on both
            elif isinstance(s, (ast.While, ast.For)):
                # the held-set entering the body is the meet of the entry and the back-edge; intersection
                # only removes locks, so the chain stabilizes within #locks + 1 steps.
                cur = set(held)
                for _ in range(2 * len(cur) + 4):
                    nxt = held & interp(s.body, cur, record=False)
                    if nxt == cur:
                        break
                    cur = nxt
                else:
                    raise NonConvergence("lock analysis fixpoint did not converge")
                interp(s.body, cur, record=record)                # check the body under the stable held-set
                held = held & cur                                 # loop may execute 0 times
        return held

    try:
        interp(fn.body, set())
    except NonConvergence as e:
        return Verdict(UNKNOWN, prop, target, "lock safety", reason=str(e))
    if violations:
        return Verdict(REFUTED, prop, target, "lock safety (held-set, all paths)",
                       counterexample="unprotected: " + "; ".join(sorted(set(violations))))
    return Verdict(PROVED, prop, target, "lock safety (held-set, all paths)")


@dataclass
class Prop:
    name: str
    target: str
    run: Callable[[Dict[str, str]], Verdict]


class Orchestrator:
    def __init__(self, repo: Dict[str, str], props: List[Prop]):
        self.repo = dict(repo)
        self.props = props
        self.cache: Dict[str, Tuple[Tuple[str, ...], Verdict]] = {}

    # ---- static call graph among repo functions ----
    def _callees(self, name: str) -> set:
        tree = _parse(self.repo[name])
        return {n.func.id for n in ast.walk(tree)
                if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                and n.func.id in self.repo}

    def _transitive(self, name: str) -> set:
        seen, stack = set(), [name]
        while stack:
            f = stack.pop()
            if f in seen:
                continue
            seen.add(f)
            stack += [c for c in self._callees(f) if c not in seen]
        return seen

    def _hash(self, name: str) -> str:
        return hashlib.sha256(ast.dump(_parse(self.repo[name])).encode()).hexdigest()

    def _signature(self, target: str) -> Tuple[str, ...]:
        # a property depends on its target plus everything the target transitively calls
        return tuple(sorted(f"{f}:{self._hash(f)}" for f in self._transitive(target)))

    def verify(self, only: Optional[set] = None, label="verify") -> List[Verdict]:
        out, hits, misses = [], 0, 0
        for p in self.props:
            sig = self._signature(p.target)
            cached = self.cache.get(p.name)
            recompute = (only is None) or (p.target in only) or \
                        (cached is None) or (cached[0] != sig)
            if not recompute and cached is not None:
                hits += 1
                out.append(cached[1])
                continue
            misses += 1
            v = p.run(self.repo)
            if v.status == UNKNOWN:
                v = escalate(v)
            self.cache[p.name] = (sig, v)
            out.append(v)
        print(f"  [{label}] verified {misses} (cache hits: {hits})")
        return out

    def change(self, func: str, new_src: str) -> List[Verdict]:
        self.repo[func] = new_src
        # invalidate every property whose transitive deps include the changed func
        affected = {func} | {p.target for p in self.props if func in self._transitive(p.target)}
        return self.verify(only=affected, label=f"after change to {func}")


def fix_loop(orch: Orchestrator, func: str, attempts: List[str], max_rounds=6) -> bool:
    print(f"\n=== change to `{func}` (author iterates until proved) ===")
    for i, src in enumerate(attempts[:max_rounds], 1):
        verds = orch.change(func, src)
        # the merge gate must consider EVERY property the change can affect,
        # including ones whose target is downstream of `func` (e.g. a caller).
        failing = [v for v in verds if v.status != PROVED]
        for v in failing:
            line = f"  [round {i}] [{v.prop}] {v.status} on `{v.target}` via {v.technique}"
            if v.counterexample:
                line += f"  |  counterexample: {v.counterexample}"
            if v.reason and v.status == UNKNOWN:
                line += f"  |  {v.reason}"
            print(line)
        if not failing:
            print(f"  [round {i}] all affected properties PROVED -> MERGED")
            return True
        print(f"  -> bounced to author")
    print(f"  -> BLOCKED (not merged)")
    return False


def _gen_candidates(allvars, consts, quad):
    C = []
    for v in allvars:
        for k in consts:
            C.append((f"{v}>={k}", (lambda s, v=v, k=k: s[v] >= k)))
            C.append((f"{v}<={k}", (lambda s, v=v, k=k: s[v] <= k)))
    for v in allvars:
        for w in allvars:
            if v == w: continue
            C.append((f"{v}<={w}", (lambda s, v=v, w=w: s[v] <= s[w])))
            C.append((f"{v}<={w}+1", (lambda s, v=v, w=w: s[v] <= s[w] + 1)))
    if quad:
        for a in allvars:
            for u in allvars:
                for m in (1, 2):
                    for c in (-1, 0, 1):
                        C.append((f"{m}*{a}=={u}*({u}-1)+{c}",
                                  (lambda s, a=a, u=u, m=m, c=c: m * s[a] == s[u] * (s[u] - 1) + c)))
    return C


def _minimize(kept, sym):
    """Drop conjuncts implied by the rest (keeps meaning, improves readability)."""
    changed = True
    while changed and len(kept) > 1:
        changed = False
        for i, (lbl, p) in enumerate(kept):
            others = [q for j, (_, q) in enumerate(kept) if j != i]
            rest = z3.And(*[q(sym) for q in others]) if others else z3.BoolVal(True)
            st, _ = _solve(z3.And(rest, z3.Not(p(sym))))
            if st == PROVED:                 # rest => p, so p is redundant
                kept.pop(i); changed = True
                break
    return kept


def verify_deductive_auto(prop, target, src, pre, post, repo=None, quad=True) -> Verdict:
    repo = repo or {}
    fn = _fndef(src)
    args = [a.arg for a in fn.args.args]
    ctx = Ctx(repo)
    init_stmts, loop, ret, bad = [], None, None, False
    for s in fn.body:
        if isinstance(s, ast.While):
            if loop is None: loop = s
            else: bad = True
        elif isinstance(s, ast.Return): ret = s
        elif loop is None: init_stmts.append(s)
        else: bad = True
    if bad or loop is None or ret is None:
        return Verdict(UNKNOWN, prop, target, "Houdini", reason="not a single-loop function")
    try:
        base = {a: z3.Int(a) for a in args}
        init_state = _apply_assigns(init_stmts, base, ctx)
        loopvars = sorted(set(init_state) - set(args))
        sym = dict(base)
        for v in loopvars: sym[v] = z3.Int(v + "_s")
        guard = ev_bool(loop.test, sym, ctx)
        body_state = _apply_assigns(loop.body, sym, ctx)
        ret_exit = ev(ret.value, sym, ctx)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "Houdini", reason=str(u))

    consts = {0, 1}
    for n in ast.walk(fn):
        if isinstance(n, ast.Constant) and isinstance(n.value, int): consts.add(n.value)
    C = _gen_candidates(args + loopvars, sorted(consts), quad)

    kept = [(l, p) for (l, p) in C
            if _solve(z3.And(pre(base), z3.Not(p(init_state))))[0] == PROVED]
    changed = True
    while changed:
        changed = False
        inv = z3.And(*[p(sym) for _, p in kept]) if kept else z3.BoolVal(True)
        for lbl, p in list(kept):
            if _solve(z3.And(inv, guard, z3.Not(p(body_state))))[0] != PROVED:
                kept.remove((lbl, p)); changed = True
    inv = z3.And(*[p(sym) for _, p in kept]) if kept else z3.BoolVal(True)
    if _solve_corro(z3.And(inv, z3.Not(guard), z3.Not(post(base, ret_exit))))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "Houdini",
                       reason="no sufficient invariant found in template space")
    kept = _minimize(kept, sym)
    inv_str = " ∧ ".join(l for l, _ in kept) or "True"
    return Verdict(PROVED, prop, target, "deductive (auto-invariant via Houdini)",
                   reason=f"discovered invariant: {inv_str}")


def _bv_eval(node, env, W, obligs, pc):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return z3.BitVecVal(node.value, W)
    if isinstance(node, ast.Name):
        if node.id not in env: raise Unsupported(f"free var {node.id}")
        return env[node.id]
    if isinstance(node, ast.BinOp):
        l = _bv_eval(node.left, env, W, obligs, pc)
        r = _bv_eval(node.right, env, W, obligs, pc)
        if isinstance(node.op, ast.Add):
            obligs.append(z3.Implies(pc, z3.And(z3.BVAddNoOverflow(l, r, True),
                                                z3.BVAddNoUnderflow(l, r))))
            return l + r
        if isinstance(node.op, ast.Sub):
            obligs.append(z3.Implies(pc, z3.And(z3.BVSubNoOverflow(l, r),
                                                z3.BVSubNoUnderflow(l, r, True))))
            return l - r
        if isinstance(node.op, ast.Mult):
            obligs.append(z3.Implies(pc, z3.And(z3.BVMulNoOverflow(l, r, True),
                                                z3.BVMulNoUnderflow(l, r))))
            return l * r
        raise Unsupported(f"bv binop {type(node.op).__name__}")
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -_bv_eval(node.operand, env, W, obligs, pc)
    raise Unsupported(f"bv expr {type(node).__name__}")


def _bv_cond(node, env, W, obligs, pc):
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        l = _bv_eval(node.left, env, W, obligs, pc)
        r = _bv_eval(node.comparators[0], env, W, obligs, pc)
        op = node.ops[0]               # Z3Py BitVec comparisons are signed
        if isinstance(op, ast.Lt): return l < r
        if isinstance(op, ast.LtE): return l <= r
        if isinstance(op, ast.Gt): return l > r
        if isinstance(op, ast.GtE): return l >= r
        if isinstance(op, ast.Eq): return l == r
        if isinstance(op, ast.NotEq): return l != r
    raise Unsupported("bv cond")


def verify_no_overflow(prop, target, src, repo=None, width=None, pre=None) -> Verdict:
    """Prove no add/sub/mul wraps a signed `width`-bit machine integer. With `pre` supplied, an
    operation need only stay in range for inputs the precondition admits, which is what makes this
    usable as an always-on companion to an unbounded-integer proof. `width` defaults to the module
    setting core.MACHINE_WIDTH, so callers do not pick a width per invocation."""
    width = width if width is not None else core.MACHINE_WIDTH
    fn = _fndef(src)
    args = [a.arg for a in fn.args.args]
    env = {a: z3.BitVec(a, width) for a in args}
    obligs: list = []
    try:
        assume = pre({a: env[a] for a in args}) if pre is not None else z3.BoolVal(True)
    except Exception:                                        # a precondition not expressible over machine
        return Verdict(UNKNOWN, prop, target, f"bitvector[{width}]",   # integers leaves the companion silent
                       reason="precondition is not expressible over machine integers")

    def walk(stmts, e, pc):
        falls = [(dict(e), pc)]
        for s in stmts:
            nxt = []
            for ee, p in falls:
                if isinstance(s, ast.Return):
                    if s.value is not None:
                        _bv_eval(s.value, ee, width, obligs, p)
                elif isinstance(s, ast.Assign):
                    ee2 = dict(ee)
                    ee2[s.targets[0].id] = _bv_eval(s.value, ee2, width, obligs, p)
                    nxt.append((ee2, p))
                elif isinstance(s, ast.If):
                    c = _bv_cond(s.test, ee, width, obligs, p)
                    nxt += walk(s.body, ee, z3.And(p, c))
                    nxt += walk(s.orelse, ee, z3.And(p, z3.Not(c)))
                else:
                    raise Unsupported(f"bv stmt {type(s).__name__}")
            falls = nxt
        return falls

    try:
        walk(fn.body, env, z3.BoolVal(True))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, f"bitvector[{width}]", reason=str(u))
    if not obligs:
        return Verdict(PROVED, prop, target, f"bitvector[{width}] (no arithmetic)")
    status, model = _solve_corro(z3.And(assume, z3.Not(z3.And(*obligs))))
    cex = None
    if status == REFUTED:
        cex = ", ".join(f"{a}={model.eval(env[a], model_completion=True).as_signed_long()}" for a in args)
    return Verdict(status, prop, target, f"bitvector[{width}] (machine integers)",
                   counterexample=cex,
                   reason="" if status != UNKNOWN else "solver returned unknown")


def _ast_has_var_bitwise(node):
    """True if the AST uses a bitwise & / | / ^ that is not the exact low-bit-mask idiom (a & (2^k-1)) -- the
    case the over-approximation leaves undecided and the bitvector engine can decide exactly."""
    if node is None:
        return False
    for n in ast.walk(node):
        if isinstance(n, ast.BinOp) and isinstance(n.op, (ast.BitAnd, ast.BitOr, ast.BitXor)):
            if isinstance(n.op, ast.BitAnd) and any(
                    isinstance(b, ast.Constant) and isinstance(b.value, int) and not isinstance(b.value, bool)
                    and b.value >= 0 and (b.value & (b.value + 1)) == 0 for b in (n.left, n.right)):
                continue                                          # a & (2^k - 1): already exact, not this engine's job
            return True
    return False


def _has_var_bitwise(src):
    """True if the function's body uses a non-mask bitwise operator (see _ast_has_var_bitwise)."""
    try:
        return _ast_has_var_bitwise(_fndef(src))
    except Unsupported:
        return False


def _infer_bv_width(pre_node, src, repo=None):
    """The smallest standard bitvector width (8/16/32/64) the precondition provably bounds every integer
    parameter into [0, 2^W), or None when no such bound is provable. Lets the exact bitvector engine pick a
    faithful, easily-discharged width instead of a fixed 64 -- a width-inference pass over the operands."""
    if pre_node is None:
        return None
    try:
        fn = _fndef(src)
        args = [a.arg for a in fn.args.args]
        if not args:
            return None
        spec = Ctx(repo or {}); spec.traps = None; spec.pc = z3.BoolVal(True)
        z3a = {a: z3.Int(a) for a in args}
        pre_t = ev_bool(pre_node, dict(z3a), spec)
    except Exception:
        return None
    for W in (8, 16, 32, 64):
        cap, half = 1 << W, 1 << (W - 1)
        unsigned = z3.And(*[z3.And(z3a[a] >= 0, z3a[a] < cap) for a in args])
        signed = z3.And(*[z3.And(z3a[a] >= -half, z3a[a] < half) for a in args])
        try:
            if _solve(z3.And(pre_t, z3.Not(z3.Or(unsigned, signed))))[0] == PROVED:
                return W
        except z3.Z3Exception:
            return None
    return None


def _bitwise_bvnative(prop, target, src, post_node, pre_node, width) -> Optional[Verdict]:
    """Discharge a width-bounded nonnegative bitwise/arithmetic identity in the pure bitvector domain, avoiding
    the Int2BV/BV2Int bridge that leaves both z3 and cvc5 UNKNOWN at width 16 and 32 (the bridge couples integer
    arithmetic with bitvector results, a theory mix neither solver bit-blasts). Each parameter maps to a wider
    bitvector held in [0, 2^width); bitwise and arithmetic run at that wider width with no-overflow / nonnegativity
    side conditions. When those side conditions provably hold on the whole valid region, the bitvector computation
    equals the unbounded-integer one, so the bitvector verdict transfers exactly. Straight-line nonnegative
    fragment only (assignments then a single return); returns None on anything outside it, so the caller's
    UNKNOWN stands -- this path only ever adds a decision, never overrides a sound abstention."""
    try:
        fn = _fndef(src)
    except Exception:
        return None
    params = [a.arg for a in fn.args.args]
    if not params:
        return None
    wide = width + 32                                            # headroom so + / - / * cannot silently overflow
    cap = z3.BitVecVal(1 << width, wide)
    lo, hi = -(1 << (wide - 1)), 1 << (wide - 1)
    env = {p: z3.BitVec("_bvn_" + p, wide) for p in params}
    obl = []                                                    # the side conditions that make BV == integer

    def ev_e(node, scope):
        if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
            if not (lo <= node.value < hi):
                raise Unsupported("bvnative: constant out of range")
            return z3.BitVecVal(node.value, wide)
        if isinstance(node, ast.Name):
            if node.id not in scope:
                raise Unsupported("bvnative: free variable")
            return scope[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            x = ev_e(node.operand, scope)
            obl.append(z3.BVSubNoOverflow(z3.BitVecVal(0, wide), x))
            obl.append(z3.BVSubNoUnderflow(z3.BitVecVal(0, wide), x, True))
            return z3.BitVecVal(0, wide) - x
        if isinstance(node, ast.BinOp):
            x, y = ev_e(node.left, scope), ev_e(node.right, scope)
            op = type(node.op)
            if op in (ast.BitAnd, ast.BitOr, ast.BitXor):
                obl.append(x >= 0); obl.append(y >= 0)         # integer bitwise == BV bitwise only for nonnegatives
                return x & y if op is ast.BitAnd else (x | y if op is ast.BitOr else x ^ y)
            if op is ast.Add:
                obl.append(z3.BVAddNoOverflow(x, y, True)); obl.append(z3.BVAddNoUnderflow(x, y))
                return x + y
            if op is ast.Sub:
                obl.append(z3.BVSubNoOverflow(x, y)); obl.append(z3.BVSubNoUnderflow(x, y, True))
                return x - y
            if op is ast.Mult:
                obl.append(z3.BVMulNoOverflow(x, y, True)); obl.append(z3.BVMulNoUnderflow(x, y))
                return x * y
            raise Unsupported("bvnative: operator")
        raise Unsupported("bvnative: expression")

    def ev_b(node, scope):
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            l, r = ev_e(node.left, scope), ev_e(node.comparators[0], scope)
            op = type(node.ops[0])
            table = {ast.Eq: l == r, ast.NotEq: l != r, ast.Lt: l < r, ast.LtE: l <= r, ast.Gt: l > r, ast.GtE: l >= r}
            if op not in table:                                # signed BV comparison (exact for the nonneg values here)
                raise Unsupported("bvnative: comparison")
            return table[op]
        if isinstance(node, ast.BoolOp):
            parts = [ev_b(v, scope) for v in node.values]
            return z3.And(*parts) if isinstance(node.op, ast.And) else z3.Or(*parts)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return z3.Not(ev_b(node.operand, scope))
        raise Unsupported("bvnative: boolean")

    try:
        scope = dict(env)
        ret = None
        for st in fn.body:                                     # straight-line: assignments then a single return
            if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name):
                scope[st.targets[0].id] = ev_e(st.value, scope)
            elif isinstance(st, ast.Return) and st.value is not None:
                ret = ev_e(st.value, scope); break
            else:
                return None                                    # control flow / unsupported statement: abstain
        if ret is None:
            return None
        region = [z3.ULT(env[p], cap) for p in params]         # every parameter in [0, 2^width)
        if pre_node is not None:
            region.append(ev_b(pre_node, dict(env)))
        post_t = ev_b(post_node, {**env, "result": ret})
    except (Unsupported, z3.Z3Exception):
        return None
    reg = z3.And(*region) if region else z3.BoolVal(True)
    obls = z3.And(*obl) if obl else z3.BoolVal(True)
    if _solve(z3.And(reg, z3.Not(obls)))[0] != PROVED:         # an overflow on the valid region would make the
        return None                                            # bitvector model unfaithful: abstain rather than risk it
    status, model = _solve(z3.And(reg, z3.Not(post_t)))
    if status == UNKNOWN:
        return None
    cex = cex_in = None
    if status == REFUTED and model is not None:
        cex_in = {p: model.eval(env[p], model_completion=True).as_long() for p in params}
        cex = ", ".join(f"{p}={cex_in[p]}" for p in params)
    return Verdict(status, prop, target, f"bitvector (exact bitwise, unsigned width {width})",
                   counterexample=cex, counterexample_inputs=cex_in)


def verify_bitwise(prop, target, src, post_node, pre_node=None, repo=None, width=64) -> Verdict:
    """Decide a property over a loop-free function whose body (or specification) uses bitwise & / | / ^
    between variables, exactly, by encoding each bitwise operator -- in the body AND in the spec -- through
    fixed-width bitvectors (Int2BV) rather than the nonnegative-operand over-approximation, so a bounded
    bitwise claim is PROVED or REFUTED, not left UNKNOWN. Int2BV reduces an out-of-range operand modulo
    2^width, so the encoding equals the unbounded bitwise value only where every operand is nonnegative and
    below 2^width; the precondition must prove that (the in-range obligation), which is what transfers the
    bitvector verdict to Python's unbounded integers. UNKNOWN when the precondition does not bound the
    operands (the over-approximation stands) or the function is outside the integer fragment. `post_node` is
    the postcondition AST over the parameters and `result`; `pre_node` the precondition AST."""
    last = Verdict(UNKNOWN, prop, target, "bitvector (exact bitwise)",
                   reason=f"precondition does not bound the bitwise operands to a width-{width} range")
    for signed in (False, True):                                 # unsigned [0, 2^w), else two's complement (negatives)
        ctx = Ctx(repo or {}); ctx.facts = []; ctx.bv_width = width; ctx.bv_signed = signed; ctx.bv_obligs = []
        spec = Ctx(repo or {}); spec.traps = None; spec.pc = z3.BoolVal(True)
        spec.facts = ctx.facts; spec.bv_width = width; spec.bv_signed = signed; spec.bv_obligs = ctx.bv_obligs
        try:
            args, z3args, rets, itraps, inone = symexec(src, ctx)
            if not args or any(not z3.is_int(z3args[a]) for a in args):
                return Verdict(UNKNOWN, prop, target, "bitvector (exact bitwise)", reason="needs integer parameters")
            out = fold(rets)
            pre_t = ev_bool(pre_node, dict(z3args), spec) if pre_node is not None else z3.BoolVal(True)
            post_t = ev_bool(post_node, {**z3args, "result": out}, spec)
        except (Unsupported, KeyError, z3.Z3Exception, TypeError, AttributeError) as u:
            return Verdict(UNKNOWN, prop, target, "bitvector (exact bitwise)", reason=str(u))
        if not ctx.bv_obligs or ctx.overapprox or spec.overapprox:    # no exact bitwise encoded, or another over-approx used
            return Verdict(UNKNOWN, prop, target, "bitvector (exact bitwise)", reason="no exact bitwise to decide")
        if _solve(z3.And(pre_t, z3.Not(z3.And(*ctx.bv_obligs))))[0] != PROVED:   # the precondition must keep operands in range
            continue                                             # try the signed encoding
        inrange = z3.And(*ctx.bv_obligs)
        claim = z3.And(pre_t, inrange, z3.Or(_trap_or(itraps), inone, z3.Not(post_t)))
        status, model = _solve(claim)
        if status == UNKNOWN and not signed and z3.is_false(z3.simplify(z3.Or(_trap_or(itraps), inone))):
            bvn = _bitwise_bvnative(prop, target, src, post_node, pre_node, width)   # BV2Int leaves the solver
            if bvn is not None:                                                      # UNKNOWN at width 16/32: decide
                return bvn                                                           # it in the pure bitvector domain
        cex = cex_in = None
        if status == REFUTED:
            model = minimize_witness(claim, z3args, args) or model
            cex, cex_in = _model_cex(model, z3args, args)
        return Verdict(status, prop, target,
                       f"bitvector (exact bitwise, {'signed' if signed else 'unsigned'} width {width})",
                       counterexample=cex, counterexample_inputs=cex_in,
                       reason="" if status != UNKNOWN else "solver returned unknown")
    return last


def verify_chc(prop, target, src, pre, post, repo=None) -> Verdict:
    """Single-loop invariant synthesis via Spacer. On divergence (UNKNOWN): refute a false specification
    cheaply by concrete sampling, then synthesize the inductive invariant Spacer missed by template
    learning, and if the invariant engine is still inconclusive fall back to bounded model checking,
    which refutes a false postcondition with a concrete witness within k unrollings."""
    v = _verify_chc_core(prop, target, src, pre, post, repo)
    if v.status != UNKNOWN:
        return v
    try:
        args = _parse_single_loop(src)[1]
    except Exception:
        args = None
    if args:
        ref = _chc_fallback(v, src, pre, post, args, repo or {})   # cheap refutation before expensive synthesis
        if ref.status == REFUTED:
            return ref
    ps = _powersum_invariant(prop, target, src, pre, post, repo)             # a power sum's closed-form invariant,
    if ps.status == PROVED:                                                  # interpolated cheaply (beyond the degree
        return ps                                                           # cap the data-driven learner stops at)
    li = learn_invariant(prop, target, src, pre, post, repo, max_degree=4)   # the invariant Spacer missed,
    if li.status == PROVED:                                                  # escalating the polynomial degree
        return li                                                            # (degree 3 sum-of-squares, 4 cubes)
    if args:                                                        # symbolic witness within k unrollings
        bm = bmc_check(prop, target, src, pre, post, k=20, repo=repo)
        if bm.status == REFUTED:
            return bm
    return v


def _verify_chc_core(prop, target, src, pre, post, repo=None) -> Verdict:
    src = _lower_list_lengths(src)                            # a list grown by append -> an integer length
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None or ret is None:
        return Verdict(UNKNOWN, prop, target, "CHC/Spacer", reason="not a single-loop function")
    ctx = Ctx(repo or {})
    try:
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        init0 = _apply_assigns(init, {a: z3.Int(a) for a in args}, ctx)
        order = args + sorted(set(init0) - set(args))
        Inv = z3.Function("Inv", *([z3.IntSort()] * len(order)), z3.BoolSort())
        cur = {v: z3.Int("c_" + v) for v in order}
        argcur = {a: cur[a] for a in args}
        init_state = _apply_assigns(init, argcur, ctx)
        guard = ev_bool(loop.test, cur, ctx)
        nxt = _apply_assigns(loop.body, cur, ctx)
        rules = [(Inv(*[init_state[v] for v in order]), [pre(argcur)]),
                 (Inv(*[nxt[v] for v in order]), [Inv(*[cur[v] for v in order]), guard])]
        ret_expr = ev(ret.value, cur, ctx)
        if ctx.traps:
            return Verdict(UNKNOWN, prop, target, "CHC/Spacer",
                           reason="division in loop is outside the CHC encoding")
        ctx.traps = None
        bad = z3.And(Inv(*[cur[v] for v in order]), z3.Not(guard), z3.Not(post(cur, ret_expr)))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "CHC/Spacer", reason=str(u))
    return _solve_horn(prop, target, "CHC/Spacer", "CHC/Spacer (invariant synthesis)",
                       [Inv], list(cur.values()), rules, bad,
                       on_error=lambda m: "engine timeout (nonlinear?)", timeout=core.CHC_FAST_MS, retry=0)


def verify_loop_auto(prop, target, src, pre, post, repo=None, quad=True) -> Verdict:
    engines = (("CHC/Spacer", lambda: verify_chc(prop, target, src, pre, post, repo)),
               ("Houdini", lambda: verify_deductive_auto(prop, target, src, pre, post, repo or {}, quad=quad)))
    attempts = []
    for _name, run in engines:
        try:
            v = run()
        except Exception as e:                       # an engine's spec may not type-check
            v = Verdict(UNKNOWN, prop, target, _name, reason=f"{type(e).__name__}: {e}")
        attempts.append(v)
        if v.status == PROVED:
            return Verdict(PROVED, prop, target, f"loop-auto via {v.technique}", reason=v.reason)
        if v.status == REFUTED:
            return v
    return Verdict(UNKNOWN, prop, target, "loop-auto",
                   reason="; ".join(f"{v.technique}: {v.reason}" for v in attempts if v.reason))


class _Block:
    __slots__ = ("id", "assigns", "term")
    def __init__(self, bid):
        self.id = bid
        self.assigns: list = []          # straight-line ast.Assign with Name targets
        self.term = None


def _exc_ancestors(name, user_bases):
    """The set of exception class names `name` is or inherits from -- its MRO -- combining the module's
    user-defined `class Sub(Base)` hierarchy (user_bases: {class: [base names]}) with Python's real builtin
    exception tree, so an `except Base` handler is known to catch a `raise Sub` (and `except LookupError` a
    `raise IndexError`). A name that resolves to neither a module class nor a builtin exception contributes
    only itself, so it is matched only by a handler naming it exactly -- a missed catch is a sound
    over-refutation (a spurious uncaught raise), never a missed escape (an unsound trap-freedom claim)."""
    out, stack = set(), [name]
    while stack:
        n = stack.pop()
        if n is None or n in out:
            continue
        out.add(n)
        if user_bases and n in user_bases:                   # a module-defined class: follow its declared bases
            stack.extend(user_bases[n])
        else:                                                # else, where it is a builtin exception, take its real MRO
            cls = getattr(_builtins, n, None)
            if isinstance(cls, type) and issubclass(cls, BaseException):
                out.update(c.__name__ for c in cls.__mro__ if issubclass(c, BaseException))
    return out


def _handler_caught(h):
    """The set of exception class names an `except` handler names -- a single type, a tuple of types -- or
    None for a bare `except:` (which catches everything). A non-name element (an attribute like mod.Error)
    is dropped, so the handler is matched conservatively (it may miss a catch, never invent one)."""
    if h.type is None:
        return None                                          # bare `except:` catches everything
    elts = h.type.elts if isinstance(h.type, ast.Tuple) else [h.type]
    return frozenset(e.id for e in elts if isinstance(e, ast.Name))


def _build_cfg(body, user_bases=None):
    """Lower a statement list to basic blocks. Returns (blocks, entry_id). `user_bases` ({class: [base
    names]}) is the module's class hierarchy, used to match a raised exception against an `except` handler
    along the class MRO; without it, the builtin exception tree alone is used."""
    blocks: Dict[int, _Block] = {}
    ctr = [0]

    def nb():
        b = _Block(ctr[0]); ctr[0] += 1; blocks[b.id] = b; return b

    def exc_name(node):
        if node is None:
            return None
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            return node.func.id
        if isinstance(node, ast.Name):
            return node.id
        return None

    def emit(stmts, cur, loops, handlers):   # handlers: list of (handler_id, caught_type|None)
        for s in stmts:
            if cur is None:              # unreachable tail after return/break/continue/raise
                break
            if isinstance(s, ast.Assign):
                if len(s.targets) != 1 or not isinstance(s.targets[0], ast.Name):
                    raise Unsupported("complex assignment target")
                cur.assigns.append(s)
            elif isinstance(s, ast.Expr):
                cur.assigns.append(s)                         # bare expression statement: trap-checked in the block
            elif isinstance(s, ast.If):
                tb, eb, jb = nb(), nb(), nb()
                cur.term = ("branch", s.test, tb.id, eb.id)
                te = emit(s.body, tb, loops, handlers)
                if te is not None: te.term = ("goto", jb.id)
                ee = emit(s.orelse, eb, loops, handlers)
                if ee is not None: ee.term = ("goto", jb.id)
                cur = jb
            elif isinstance(s, ast.While):
                hb, bb, xb = nb(), nb(), nb()
                cur.term = ("goto", hb.id)
                if s.orelse:                                  # while/else (and for/else): the else
                    eb = nb()                                 # runs on normal exit; break skips it
                    hb.term = ("branch", s.test, bb.id, eb.id)
                    be = emit(s.body, bb, loops + [(hb.id, xb.id)], handlers)
                    if be is not None: be.term = ("goto", hb.id)
                    ee = emit(s.orelse, eb, loops, handlers)
                    if ee is not None: ee.term = ("goto", xb.id)
                else:
                    hb.term = ("branch", s.test, bb.id, xb.id)
                    be = emit(s.body, bb, loops + [(hb.id, xb.id)], handlers)
                    if be is not None: be.term = ("goto", hb.id)
                cur = xb
            elif isinstance(s, ast.Return):
                cur.term = ("return", s.value); cur = None
            elif isinstance(s, ast.Break):
                if not loops: raise Unsupported("break outside loop")
                cur.term = ("goto", loops[-1][1]); cur = None
            elif isinstance(s, ast.Continue):
                if not loops: raise Unsupported("continue outside loop")
                cur.term = ("goto", loops[-1][0]); cur = None
            elif isinstance(s, ast.Raise):
                raised = exc_name(s.exc)                      # None for a bare re-raise or an unresolvable type
                anc = _exc_ancestors(raised, user_bases) if raised is not None else None
                target_h = None
                for hid, caught in reversed(handlers):        # innermost handler that catches it, by the class MRO
                    if caught is None:                        # a bare `except:` catches everything
                        target_h = hid; break
                    if anc is None:                           # an unresolvable raise: only a catch-all handles it
                        if "Exception" in caught or "BaseException" in caught:
                            target_h = hid; break
                    elif anc & caught:                        # the raised type, or one of its ancestors, is named
                        target_h = hid; break
                cur.term = ("goto", target_h) if target_h is not None else ("raise", raised)
                cur = None
            elif isinstance(s, ast.Try):
                if not s.handlers and not s.finalbody:
                    raise Unsupported("try without except or finally")
                after = nb()

                def run_finally(end, _final=s.finalbody, _outer=handlers, _after=after):
                    # `finally` runs on the normal and handled exit paths (propagating paths
                    # end in an uncaught raise, where the postcondition is not asserted).
                    if not _final:
                        if end is not None:
                            end.term = ("goto", _after.id)
                        return
                    if end is None:
                        return
                    fb = nb(); end.term = ("goto", fb.id)
                    fe = emit(_final, fb, loops, _outer)
                    if fe is not None:
                        fe.term = ("goto", _after.id)

                hblocks = [(nb(), _handler_caught(h), h) for h in s.handlers]
                bstart = nb(); cur.term = ("goto", bstart.id)
                be = emit(s.body, bstart, loops, handlers + [(hb.id, caught) for hb, caught, _h in hblocks])
                if s.orelse and be is not None:               # try/except/else: else runs on normal exit
                    ob = nb(); be.term = ("goto", ob.id)
                    run_finally(emit(s.orelse, ob, loops, handlers))
                else:
                    run_finally(be)
                for hb, _caught, h in hblocks:                # each handler body, then finally
                    run_finally(emit(h.body, hb, loops, handlers))
                cur = after
            elif isinstance(s, ast.Assert):
                rb, cb = nb(), nb()                           # assert e  ==  if not e: raise AssertionError
                cur.term = ("branch", s.test, cb.id, rb.id)
                rb.term = ("raise", "AssertionError")
                cur = cb
            elif isinstance(s, (ast.Pass, ast.Import, ast.ImportFrom, ast.Global, ast.Nonlocal)):
                pass                                          # import / global / nonlocal: no-ops here
            else:
                raise Unsupported(f"statement {type(s).__name__}")
        return cur

    entry = nb()
    tail = emit(body, entry, [], [])
    if tail is not None:
        tail.term = ("return", None)     # fall off the end -> return None
    return blocks, entry.id


def _cfg_vars(fn, blocks):
    names = list(a.arg for a in fn.args.args)
    seen = set(names)
    for b in blocks.values():
        for s in b.assigns:
            if not isinstance(s, ast.Assign):                # a bare expression statement binds no name
                continue
            n = s.targets[0].id
            if n not in seen:
                seen.add(n); names.append(n)
    return names


_BUILTIN_NAMES = {"abs", "min", "max", "len", "range", "True", "False", "None"}


def _lower_list_lengths(src):
    """Rewrite length-only list locals into integer counters so a list grown by append in a loop is in
    reach of the integer engines: `a = []` becomes `_len_a = 0`, `a.append(e)` becomes `_len_a += 1`,
    and `len(a)` becomes `_len_a`. Applied only to a list whose every use is the empty init, append, or
    len -- any element access, return, or other method leaves the function untouched (its contents are
    not tracked here). Returns the rewritten source, or the original when no list qualifies."""
    try:
        tree = ast.parse(textwrap.dedent(src))
    except SyntaxError:
        return src
    fn = next((n for n in tree.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
    if fn is None:
        return src

    def is_empty_list(v):
        return ((isinstance(v, ast.List) and not v.elts)
                or (isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id == "list" and not v.args))

    lists = {s.targets[0].id for s in ast.walk(fn)
             if isinstance(s, ast.Assign) and len(s.targets) == 1
             and isinstance(s.targets[0], ast.Name) and is_empty_list(s.value)}
    if not lists:
        return src
    total = {k: 0 for k in lists}
    explained = {k: 0 for k in lists}
    for n in ast.walk(fn):
        if isinstance(n, ast.Name) and n.id in lists:
            total[n.id] += 1
        if (isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                and n.targets[0].id in lists and is_empty_list(n.value)):
            explained[n.targets[0].id] += 1                                  # the empty-list init target
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr == "append"
                and isinstance(n.func.value, ast.Name) and n.func.value.id in lists and len(n.args) == 1):
            explained[n.func.value.id] += 1                                  # the list in a.append(e)
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "len"
                and len(n.args) == 1 and isinstance(n.args[0], ast.Name) and n.args[0].id in lists):
            explained[n.args[0].id] += 1                                     # the list in len(a)
    keep = {k for k in lists if total[k] == explained[k]}
    if not keep:
        return src

    def counter(name):
        return "_len_" + name

    class _Lower(ast.NodeTransformer):
        def visit_Assign(self, node):
            self.generic_visit(node)
            if (len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                    and node.targets[0].id in keep and is_empty_list(node.value)):
                return ast.Assign(targets=[ast.Name(id=counter(node.targets[0].id), ctx=ast.Store())],
                                  value=ast.Constant(value=0))
            return node

        def visit_Expr(self, node):
            self.generic_visit(node)
            c = node.value
            if (isinstance(c, ast.Call) and isinstance(c.func, ast.Attribute) and c.func.attr == "append"
                    and isinstance(c.func.value, ast.Name) and c.func.value.id in keep):
                nm = counter(c.func.value.id)
                return ast.Assign(targets=[ast.Name(id=nm, ctx=ast.Store())],
                                  value=ast.BinOp(left=ast.Name(id=nm, ctx=ast.Load()),
                                                  op=ast.Add(), right=ast.Constant(value=1)))
            return node

        def visit_Call(self, node):
            self.generic_visit(node)
            if (isinstance(node.func, ast.Name) and node.func.id == "len" and len(node.args) == 1
                    and isinstance(node.args[0], ast.Name) and node.args[0].id in keep):
                return ast.Name(id=counter(node.args[0].id), ctx=ast.Load())
            return node

    return ast.unparse(ast.fix_missing_locations(_Lower().visit(tree)))


def _scope_bound_names(body):
    """Names bound in this scope: Store targets and nested def/class names, not descending into a nested
    function, class, or lambda (each is a separate scope). Only such names can be unbound-local."""
    names = set()

    def rec(n):
        for c in ast.iter_child_nodes(n):
            if isinstance(c, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                names.add(c.name)                            # binds the name here; its body is another scope
            elif isinstance(c, (ast.Lambda, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
                continue                                     # a lambda or comprehension is a separate scope
            else:
                if isinstance(c, ast.Name) and isinstance(c.ctx, ast.Store):
                    names.add(c.id)
                rec(c)
    for s in body:
        rec(s)
    return names


def _block_exits(stmts) -> bool:
    """True if the block provably never falls through (every path ends in return / raise / break / continue), so
    code after it is unreachable. Conservative -- False when unsure -- so the caller's over-approximation stays
    sound. Lets a try whose handlers all exit treat the try body's assignments as definite afterward."""
    if not stmts:
        return False
    last = stmts[-1]
    if isinstance(last, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
        return True
    if isinstance(last, ast.If) and last.orelse:
        return _block_exits(last.body) and _block_exits(last.orelse)
    if isinstance(last, ast.With):
        return _block_exits(last.body)
    return False


def _use_before_def(src):
    """The sorted names that may be read before assignment on some path. Only a name bound somewhere in
    the function's own scope can be unbound-local (Python raises UnboundLocalError for those alone); a
    free or global name, including a sibling function or class used as a value, resolves elsewhere and is
    not flagged. A nested def/class binds its name. (For/aug-assign are already desugared to while/assign.)"""
    fn = _fndef(src)
    params = {a.arg for a in fn.args.args} | {a.arg for a in fn.args.kwonlyargs}
    local_names = _scope_bound_names(fn.body)
    reassigned = {nd.id for nd in ast.walk(fn) if isinstance(nd, ast.Name) and isinstance(nd.ctx, ast.Store)}
    bad = []
    brk_stack = []                                           # per-active-loop stack of the definite sets at each break

    # Path sensitivity over correlated guards: a side-effect-free test whose variables are never reassigned has a
    # stable value, so `if c: x = ...` and a later `if c: ... x ...` at the same block level run x's def with its use.
    _PURE = (ast.Name, ast.Constant, ast.Load, ast.BoolOp, ast.UnaryOp, ast.BinOp, ast.Compare, ast.And, ast.Or,
             ast.Not, ast.USub, ast.UAdd, ast.Add, ast.Sub, ast.Mult, ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt,
             ast.GtE, ast.Is, ast.IsNot, ast.In, ast.NotIn)

    def guard_key(test):
        for nd in ast.walk(test):
            if not isinstance(nd, _PURE):
                return None                                  # a call / subscript / other node: the guard is not stable
            if isinstance(nd, ast.Name) and isinstance(nd.ctx, ast.Load) and nd.id in reassigned:
                return None                                  # a reassigned variable: the guard's value can change
        return ast.dump(test)

    def uses(node, defined):
        for nd in ast.walk(node):
            if (isinstance(nd, ast.Name) and isinstance(nd.ctx, ast.Load)
                    and nd.id in local_names and nd.id not in defined):
                bad.append(nd.id)

    def stores(tgt):
        return {nd.id for nd in ast.walk(tgt) if isinstance(nd, ast.Name) and isinstance(nd.ctx, ast.Store)}

    def binds(node):                                         # names a walrus (`x := e`) binds in this scope
        return {nd.target.id for nd in ast.walk(node)
                if isinstance(nd, ast.NamedExpr) and isinstance(nd.target, ast.Name)}

    def walk(stmts, defined):
        defined = set(defined)
        cond_defs = {}                                       # stable-guard key -> names defined under it; local per
        #                                                      block, so it never leaks across a loop body or nesting
        for s in stmts:
            if isinstance(s, ast.Assign):
                uses(s.value, defined)
                defined |= binds(s.value)
                for t in s.targets:
                    defined |= stores(t)
            elif isinstance(s, ast.AnnAssign):
                if s.value is not None:                       # x: T = v binds x (a bare x: T does not, in Python)
                    uses(s.value, defined)
                    defined |= binds(s.value)
                    defined |= stores(s.target)
            elif isinstance(s, ast.AugAssign):
                for nm in stores(s.target):                  # x += e reads x first, so x must already be bound
                    if nm in local_names and nm not in defined:
                        bad.append(nm)
                uses(s.target, defined)                       # a[i] += e also reads a and i (its Load-context names)
                uses(s.value, defined)
                defined |= stores(s.target)
            elif isinstance(s, ast.For):
                uses(s.iter, defined)                         # the loop variable is bound, but the body may not run,
                defined |= stores(s.target)                   # so the body's own bindings do not survive the loop
                brk_stack.append([])
                walk(s.body, defined | binds(s.iter))
                brk = brk_stack.pop()
                else_defs = walk(s.orelse, defined)
                if s.orelse:                                  # for/else: definite after iff defined on the else path
                    defined |= set.intersection(else_defs, *brk)   # (no-break completion) AND at every break
            elif isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                defined.add(s.name)                          # binds its name; the body is a separate scope
            elif isinstance(s, ast.Return):
                if s.value is not None:
                    uses(s.value, defined)
            elif isinstance(s, ast.Expr):
                uses(s.value, defined)                       # a bare call may read a local in its arguments
                defined |= binds(s.value)
            elif isinstance(s, ast.If):
                uses(s.test, defined)
                defined |= binds(s.test)                     # a walrus in the test binds in both branches and after
                key = guard_key(s.test)                      # a stable guard correlates a def and a later use under it
                body_in = defined | cond_defs.get(key, set()) if key is not None else defined
                db = walk(s.body, body_in)
                if key is not None:                          # names the true branch adds hold whenever the guard recurs
                    cond_defs[key] = cond_defs.get(key, set()) | (db - defined)
                defined |= (db & walk(s.orelse, defined))    # both branches define it unconditionally
            elif isinstance(s, ast.While):
                uses(s.test, defined)
                brk_stack.append([])
                walk(s.body, defined | binds(s.test))        # a walrus in the test binds in the body; body may not run
                brk = brk_stack.pop()
                else_defs = walk(s.orelse, defined)
                always = isinstance(s.test, ast.Constant) and bool(s.test.value)   # while True: only a break exits
                exits = list(brk)
                if not always:                                # a test-false (0-iteration) exit runs the else, else
                    exits.append(else_defs)                   # leaves the pre-loop state
                if exits:
                    defined |= set.intersection(*exits)
            elif isinstance(s, ast.Try):
                # an exception may fire before any body assignment, so a name is defined afterwards only if
                # assigned in the body AND on every handler path that reaches past the try. A handler that exits
                # (return / raise / break / continue) never reaches there, so it does not constrain the body's
                # definitions -- `try: x = next(it) except StopIteration: return` leaves x definite afterward.
                db = walk(s.body, defined)
                hs = [hd for h in s.handlers for hd in [walk(h.body, defined)] if not _block_exits(h.body)]
                defined |= db.intersection(*hs) if hs else db
                defined |= walk(s.finalbody, defined)
            elif isinstance(s, ast.Break):
                if brk_stack:                                 # the definite set where this loop exits via break --
                    brk_stack[-1].append(set(defined))        # for/else and while-True establish a binding through it
            elif isinstance(s, ast.Delete):
                for t in s.targets:
                    if isinstance(t, ast.Name):
                        defined.discard(t.id)
            # raise / pass / continue / import reference globals or nothing: no-ops for definite assignment.
        return defined

    walk(fn.body, params)
    return sorted(set(bad))


def _definite_assignment_guard(prop, target, technique, srcs):
    """UNKNOWN verdict if any function reads a variable before assigning it on some
    path, else None. Conservative: a possible (not certain) use is enough to gate."""
    for s in srcs:
        try:
            bad = _use_before_def(s)
        except Unsupported:
            bad = []
        if bad:
            return Verdict(UNKNOWN, prop, target, technique,
                           reason=f"possible use before assignment: {bad}")
    return None


def verify_function(prop, target, src, pre, post, repo=None, timeout=4000) -> Verdict:
    """Verify {pre} f {post} for arbitrary intraprocedural control flow, plus
    no-division-by-zero, via a per-block CHC system discharged by Spacer.
    `pre(param_state)` and `post(exit_state, return_value)` return Z3 Bools.
    Returns None-return safety only (no integer postcondition on a None return)."""
    src = _lower_list_lengths(src)                            # a list grown by append -> an integer length
    gated = _definite_assignment_guard(prop, target, "CFG/CHC", [src])
    if gated is not None:
        return gated
    fn = _fndef(src)
    params = [a.arg for a in fn.args.args]
    try:
        blocks, entry = _build_cfg(fn.body)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "CFG/CHC", reason=str(u))
    order = _cfg_vars(fn, blocks)
    ctx = Ctx(repo or {}); ctx.divvars = []
    cur = {v: z3.Int("s_" + v) for v in order}
    R = {bid: z3.Function(f"R{bid}", *([z3.IntSort()] * len(order)), z3.BoolSort())
         for bid in blocks}
    Err = z3.Function("Err", z3.BoolSort())
    rules = []

    def tup(state):
        vals = [state[v] for v in order]
        for x in vals:                                       # the relations are Int-sorted, so a non-integer value
            if not (z3.is_expr(x) and z3.is_int(x)):          # (a float, string, or None) crossing a block cannot be
                raise Unsupported("a non-integer value crosses a block")   # passed into one -- abstain, do not crash
        return vals

    try:
        init = {v: (cur[v] if v in params else z3.IntVal(0)) for v in order}
        rules.append((R[entry](*tup(init)), [pre({p: cur[p] for p in params})]))

        for bid, b in blocks.items():
            ctx.traps = []; ctx.pc = z3.BoolVal(True); ctx.divaux = []
            after = _apply_assigns(b.assigns, cur, ctx)          # straight-line block
            term = b.term
            cond = retval = None
            if term and term[0] == "branch":
                cond = ev_bool(term[1], after, ctx)
            elif term and term[0] == "return" and term[1] is not None:
                retval = ev(term[1], after, ctx)
            body_rel = R[bid](*tup(cur))
            aux = list(ctx.divaux)                               # division side constraints
            for t in ctx.traps:                                  # a reachable zero divisor
                rules.append((Err(), [body_rel] + aux + [t]))
            if term is None:
                continue
            if term[0] == "goto":
                rules.append((R[term[1]](*tup(after)), [body_rel] + aux))
            elif term[0] == "branch":
                rules.append((R[term[2]](*tup(after)), [body_rel] + aux + [cond]))
                rules.append((R[term[3]](*tup(after)), [body_rel] + aux + [z3.Not(cond)]))
            elif term[0] == "return" and term[1] is not None:
                rules.append((Err(), [body_rel] + aux + [z3.Not(post(after, retval))]))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "CFG/CHC", reason=str(u))

    return _annotate_machine_overflow(
        _solve_horn(prop, target, "CFG/CHC", "CFG/CHC (whole-function Horn)",
                    list(R.values()) + [Err], [*cur.values(), *ctx.divvars], rules, Err(),
                    on_error=lambda m: "engine timeout (nonlinear?)" if ("canceled" in m or "timeout" in m) else f"engine: {m}"),
        src, pre, repo)


def _annotate_machine_overflow(v, src, pre, repo):
    """Always-on companion: a function proved over Python's unbounded integers is additionally checked for
    signed wraparound at the default machine width under the same precondition. If an operation can wrap, that
    witness is attached to the (still PROVED, for Python semantics) verdict. A looping or nonlinear body the
    straight-line bitvector check cannot model is left unannotated."""
    if not core.CHECK_MACHINE_OVERFLOW or v.status != PROVED:
        return v
    mv = verify_no_overflow(v.prop, v.target, src, repo, pre=pre)
    if mv.status == REFUTED:
        note = f"holds over Python integers, but wraps signed {core.MACHINE_WIDTH}-bit at {mv.counterexample}"
        v.reason = (v.reason + "; " + note) if v.reason else note
    return v


_DIV_OPS = (ast.FloorDiv, ast.Mod, ast.Div)


def _stmt_divisors(s):
    """The divisor expressions of every division / modulo / true-division in statement `s`'s own evaluated
    expressions -- an assignment value, a return value, a bare expression, or an `if` test (each evaluated once
    before the statement) -- not descending into a nested statement body or a loop test (a guard before the
    statement would not track a divisor that changes per iteration)."""
    exprs = ([s.value] if isinstance(s, (ast.Assign, ast.Return, ast.Expr)) and getattr(s, "value", None) is not None
             else [s.test] if isinstance(s, ast.If) else [])
    out = []
    for e in exprs:
        for n in ast.walk(e):
            if isinstance(n, ast.BinOp) and isinstance(n.op, _DIV_OPS):
                out.append(n.right)
    return out


def _guard_div_block(stmts):
    """Prepend `if d == 0: raise ZeroDivisionError()` before each statement that divides by d, recursing into
    nested blocks, so the CFG routes the division's trap through the enclosing try/except."""
    import copy
    out = []
    for s in stmts:
        for d in _stmt_divisors(s):
            out.append(ast.If(
                test=ast.Compare(left=copy.deepcopy(d), ops=[ast.Eq()], comparators=[ast.Constant(value=0)]),
                body=[ast.Raise(exc=ast.Call(func=ast.Name(id="ZeroDivisionError", ctx=ast.Load()),
                                             args=[], keywords=[]), cause=None)], orelse=[]))
        for attr in ("body", "orelse", "finalbody"):
            sub = getattr(s, attr, None)
            if isinstance(sub, list):
                setattr(s, attr, _guard_div_block(sub))
        for h in getattr(s, "handlers", None) or []:
            h.body = _guard_div_block(h.body)
        out.append(s)
    return out


def _guard_op_traps(src):
    """If the function uses a try (or a with, which desugars to one -- including contextlib.suppress), prepend
    `if d == 0: raise ZeroDivisionError()` before each statement that divides by d, so the division's
    ZeroDivisionError is an explicit raise the CFG routes through the enclosing handler along the exception MRO:
    a caught division (`try: 10 // x except ZeroDivisionError`, `with suppress(ZeroDivisionError)`) proves, an
    uncaught one refutes with the divisor==0 witness. A loop-test divisor is left untransformed. Returns src
    unchanged when there is no try/with, so such a function is byte-identical and its verdict cannot move."""
    try:
        tree = _parse(src)                                   # parse + desugar (with / contextlib.suppress -> try)
    except Exception:
        return src
    fn = next((n for n in tree.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
    if fn is None or not any(isinstance(n, ast.Try) for n in ast.walk(fn)):
        return src
    if not any(isinstance(n, ast.BinOp) and isinstance(n.op, _DIV_OPS) for n in ast.walk(fn)):
        return src                                           # no division to guard: leave the source byte-identical
    fn.body = _guard_div_block(fn.body)
    return ast.unparse(ast.fix_missing_locations(tree))


def verify_no_raise(prop, target, src, pre, repo=None, timeout=4000) -> Verdict:
    src = _lower_list_lengths(src)                            # a list grown by append -> an integer length
    src = _guard_op_traps(src)                                # a division inside a try/with: route its
    #                                                          ZeroDivisionError raise through the handler
    gated = _definite_assignment_guard(prop, target, "exception safety", [src])
    if gated is not None:
        return gated
    fn = _fndef(src)
    params = [a.arg for a in fn.args.args]
    # a str/bytes parameter bound as an integer relation would read int(s) / s + 1 / floor division as total
    # integer ops, though they trap on the real value; abstain so the value engine (which models strings) decides.
    _strparams = {a.arg for a in fn.args.args
                  if isinstance(a.annotation, ast.Name) and a.annotation.id in ("str", "bytes")}
    if _strparams and any(isinstance(n, ast.Name) and n.id in _strparams for n in ast.walk(fn)):
        return Verdict(UNKNOWN, prop, target, "exception safety",
                       reason="a str/bytes-typed parameter is outside the integer CHC model (value engine decides)")
    # an object-typed parameter bound as an integer would read a scalar op on it (100 // proto) as a total
    # integer op, though it is a TypeError on the real object; abstain so the value engine decides it.
    _objparams = {a.arg for a in fn.args.args if core._is_object_annotation(a.annotation)}
    if _objparams and any(isinstance(n, ast.Name) and n.id in _objparams for n in ast.walk(fn)):
        return Verdict(UNKNOWN, prop, target, "exception safety",
                       reason="an object-typed parameter is outside the integer CHC model (value engine decides)")
    # a float parameter bound as a z3.Int loses IEEE-754 semantics (NaN non-reflexivity, signed zero, the
    # infinities), so a trap guarded by them reads as unreachable; abstain so the value engine decides it over z3.FP.
    _floatparams = {a.arg for a in fn.args.args
                    if isinstance(a.annotation, ast.Name) and a.annotation.id == "float"}
    if _floatparams and any(isinstance(n, ast.Name) and n.id in _floatparams for n in ast.walk(fn)):
        return Verdict(UNKNOWN, prop, target, "exception safety",
                       reason="a float-typed parameter is outside the integer CHC model (value engine decides)")
    # a method call on a number-typed (int/float/bool) parameter (n.append(...)) reads as a trap-free opaque
    # call though a number has no such method (AttributeError), and a list/dict/set/tuple parameter used as a
    # scalar (a + 1, -a, int(a)) reads as a total integer op though it is a TypeError; abstain on both so the
    # value engine decides. A container used as a container, or a class-annotated receiver, is sound and stays.
    _numparams = {a.arg for a in fn.args.args
                  if isinstance(a.annotation, ast.Name) and a.annotation.id in ("int", "float", "bool")}
    if _numparams and any(isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                          and isinstance(n.func.value, ast.Name) and n.func.value.id in _numparams
                          for n in ast.walk(fn)):
        return Verdict(UNKNOWN, prop, target, "exception safety",
                       reason="a method call on a number-typed parameter is outside the integer CHC model "
                              "(value engine decides)")
    def _ctnr_ann(ann):                                      # a container annotation, bare (list) or parameterized
        if isinstance(ann, ast.Name):                        # (list[int], dict[str, int], or a typing alias)
            return ann.id in ("list", "dict", "set", "frozenset", "tuple")
        if isinstance(ann, ast.Subscript) and isinstance(ann.value, ast.Name):
            return ann.value.id in ("list", "dict", "set", "frozenset", "tuple", "List", "Dict", "Set",
                                    "FrozenSet", "Tuple", "Sequence", "MutableSequence", "MutableSet",
                                    "Mapping", "MutableMapping")
        return False
    _ctnrparams = {a.arg for a in fn.args.args if _ctnr_ann(a.annotation)}
    if _ctnrparams:
        def _scalar_operand(n):
            if isinstance(n, ast.BinOp):
                return [n.left, n.right]
            if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.USub, ast.UAdd, ast.Invert)):
                return [n.operand]
            if isinstance(n, ast.Compare) and any(isinstance(o, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)) for o in n.ops):
                return [n.left, *n.comparators]   # a < 1 / 1 < a: ordering a container against a number is a TypeError
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in ("int", "float", "abs"):
                return list(n.args)
            return []
        if any(isinstance(op, ast.Name) and op.id in _ctnrparams
               for node in ast.walk(fn) for op in _scalar_operand(node)):
            return Verdict(UNKNOWN, prop, target, "exception safety",
                           reason="a container-typed parameter is used as a scalar, outside the integer CHC model "
                                  "(value engine decides)")
    try:
        _ub = {n.name: [b.id for b in n.bases if isinstance(b, ast.Name)]   # the module's class hierarchy, so an
               for n in _parse(src).body if isinstance(n, ast.ClassDef)}     # `except Base` catches a `raise Sub`
        blocks, entry = _build_cfg(fn.body, _ub)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "exception safety", reason=str(u))
    order = _cfg_vars(fn, blocks)
    ctx = Ctx(repo or {}); ctx.divvars = []
    cur = {v: z3.Int("s_" + v) for v in order}
    R = {bid: z3.Function(f"R{bid}", *([z3.IntSort()] * len(order)), z3.BoolSort()) for bid in blocks}
    Err = z3.Function("ErrRaise", z3.BoolSort())
    rules = []
    def tup(state):
        vals = [state[v] for v in order]
        for x in vals:                                        # the relations are Int-sorted, so a None, float, or
            if not (z3.is_expr(x) and z3.is_int(x)):           # other non-integer value crossing a block cannot be
                raise Unsupported("a non-integer value crosses a block")   # passed into one -- abstain, do not crash
        return vals
    try:
        init = {v: (cur[v] if v in params else z3.IntVal(0)) for v in order}
        rules.append((R[entry](*tup(init)), [pre({p: cur[p] for p in params})]))
        for bid, b in blocks.items():
            # division is linearized in-encoding; a reachable zero divisor is itself an
            # (uncaught) ZeroDivisionError, so it is an edge to Err like any escaping raise.
            ctx.traps = []; ctx.pc = z3.BoolVal(True); ctx.divaux = []
            after = _apply_assigns(b.assigns, cur, ctx)
            term = b.term
            cond = None
            if term and term[0] == "branch":
                cond = ev_bool(term[1], after, ctx)
            elif term and term[0] == "return" and term[1] is not None:
                ev(term[1], after, ctx)                  # surface division traps in the return
            body_rel = R[bid](*tup(cur))
            aux = list(ctx.divaux)
            for t in ctx.traps:                          # a reachable division by zero raises
                rules.append((Err(), [body_rel] + aux + [t]))
            if term is None:
                continue
            if term[0] == "goto":
                rules.append((R[term[1]](*tup(after)), [body_rel] + aux))
            elif term[0] == "branch":
                rules.append((R[term[2]](*tup(after)), [body_rel] + aux + [cond]))
                rules.append((R[term[3]](*tup(after)), [body_rel] + aux + [z3.Not(cond)]))
            elif term[0] == "raise":
                rules.append((Err(), [body_rel] + aux))  # a reachable uncaught raise
    except (Unsupported, z3.Z3Exception, KeyError, TypeError) as u:   # a z3 sort/type clash leaves the body unmodelable
        return Verdict(UNKNOWN, prop, target, "exception safety", reason=str(u))
    return _solve_horn(prop, target, "exception safety", "exception safety (CFG/CHC)",
                       list(R.values()) + [Err], [*cur.values(), *ctx.divvars], rules, Err(),
                       on_error=lambda m: "engine error", proved_reason="no uncaught raise reachable",
                       refuted_reason="an uncaught raise is reachable")


def verify_recursive(prop, target, src, pre, post, timeout=4000) -> Verdict:
    """Self-recursive verification via Spacer, with a concrete-refutation fallback on UNKNOWN."""
    v = _verify_recursive_core(prop, target, src, pre, post, timeout)
    try:
        args = [a.arg for a in _fndef(src).args.args]
    except Exception:
        return v
    v = _chc_fallback(v, src, pre, post, args, {})
    # a replayable witness with no execution, by bounded symbolic unrolling -- a sound refutation, so it also
    # upgrades an UNKNOWN the inductive (Spacer) engine could not close to a witness-backed REFUTED.
    if v.status in (REFUTED, UNKNOWN) and not v.counterexample_inputs:
        inp, cex = _recursive_bmc_witness(src, pre, post)
        if inp is not None:
            reason = v.reason if v.status == REFUTED else \
                "a recursive call violates the postcondition on a bounded input (no inductive proof needed)"
            v = Verdict(REFUTED, v.prop, v.target, v.technique + " + bmc witness",
                        counterexample=cex, reason=reason, counterexample_inputs=inp)
    return v


def _verify_recursive_core(prop, target, src, pre, post, timeout=4000) -> Verdict:
    fn = _fndef(src)
    name = fn.name
    if not any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == name
               for n in ast.walk(fn)):
        # not self-recursive: the recursion engine models every parameter as an integer, so on a non-recursive
        # body it would vacuously prove e.g. `return a + 1` for a list parameter (a TypeError). Decline; such a
        # function is decided by check / the value engine earlier in the cascade.
        return Verdict(UNKNOWN, prop, target, "CHC/recursion", reason="not a self-recursive function")
    params = [a.arg for a in fn.args.args]
    pv = {p: z3.Int("p_" + p) for p in params}
    allvars = list(pv.values())
    ctr = [0]

    def fresh():
        v = z3.Int(f"_r{ctr[0]}"); ctr[0] += 1; allvars.append(v); return v

    F = z3.Function(name + "_rel", *([z3.IntSort()] * (len(params) + 1)), z3.BoolSort())
    Err = z3.Function("Err_rec", z3.BoolSort())

    def E(node, env, sub, traps):
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return z3.IntVal(node.value)
        if isinstance(node, ast.Name):
            if node.id not in env: raise Unsupported(f"free var {node.id}")
            return env[node.id]
        if isinstance(node, ast.BinOp):
            op = type(node.op)
            if op in (ast.Add, ast.Sub, ast.Mult):
                return _BINOPS[op](E(node.left, env, sub, traps), E(node.right, env, sub, traps))
            if op in (ast.FloorDiv, ast.Mod):            # floor division, linearized; b==0 is a trap
                l = E(node.left, env, sub, traps); r = E(node.right, env, sub, traps)
                q = fresh()
                sub.append(z3.Implies(r > 0, z3.And(r * q <= l, l < r * q + r)))
                sub.append(z3.Implies(r < 0, z3.And(r * q >= l, l > r * q + r)))
                traps.append(r == 0)
                return q if op is ast.FloorDiv else (l - r * q)
            raise Unsupported("recursion binop")
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -E(node.operand, env, sub, traps)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return z3.If(_as_bool(E(node.operand, env, sub, traps)), z3.IntVal(0), z3.IntVal(1))
        if isinstance(node, ast.IfExp):
            return z3.If(_as_bool(E(node.test, env, sub, traps)),
                         E(node.body, env, sub, traps), E(node.orelse, env, sub, traps))
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            cop = type(node.ops[0])
            if cop in (ast.In, ast.NotIn):                # n in {0, 1} -> a disjunction of equalities (a base-case
                comp = node.comparators[0]                # test in a recursive validator)
                if not isinstance(comp, (ast.Set, ast.List, ast.Tuple)):
                    raise Unsupported("recursion membership over a non-literal")
                lv = E(node.left, env, sub, traps)
                mem = z3.Or(*[lv == E(e, env, sub, traps) for e in comp.elts]) if comp.elts else z3.BoolVal(False)
                return mem if cop is ast.In else z3.Not(mem)
            if cop not in _CMP:
                raise Unsupported(f"recursion compare {cop.__name__}")
            return _CMP[cop](E(node.left, env, sub, traps), E(node.comparators[0], env, sub, traps))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            fid = node.func.id
            if fid == name:
                at = [E(a, env, sub, traps) for a in node.args]
                if len(at) != len(params): raise Unsupported("recursive arity")
                r = fresh(); sub.append(F(*at, r)); return r
            if fid == "isinstance" and len(node.args) == 2:   # a type guard, decided from the argument's sort
                v = E(node.args[0], env, sub, traps)          # (a recursive input validator: if not isinstance(...))
                tn = node.args[1]
                tnames = [t.id for t in (tn.elts if isinstance(tn, ast.Tuple) else [tn]) if isinstance(t, ast.Name)]
                if tnames and all(t in ("int", "bool", "float") for t in tnames):
                    ok = (("int" in tnames and (z3.is_int(v) or z3.is_bool(v)))
                          or ("bool" in tnames and z3.is_bool(v)) or ("float" in tnames and z3.is_fp(v)))
                    return z3.BoolVal(bool(ok))
                raise Unsupported("recursion isinstance of an unmodeled type")
            if fid == "abs" and len(node.args) == 1:
                a = E(node.args[0], env, sub, traps); return z3.If(a >= 0, a, -a)
            if fid in ("min", "max") and len(node.args) >= 2:    # over values; a single iterable may be empty
                vals = [E(a, env, sub, traps) for a in node.args]; acc = vals[0]
                for x in vals[1:]:
                    acc = z3.If(x < acc, x, acc) if fid == "min" else z3.If(x > acc, x, acc)
                return acc
            raise Unsupported(f"recursion call {fid}")
        raise Unsupported(f"recursion expr {type(node).__name__}")

    raise_pcs = []                                      # (pc, sub, traps) for each reachable `raise` -- an Err

    def returns(stmts, pc, env, sub, traps):           # env: assignments; sub: subgoals; traps: div-by-zero
        rs = []; env = dict(env); sub = list(sub); traps = list(traps)
        for idx, s in enumerate(stmts):
            if isinstance(s, ast.Return):
                if s.value is None: raise Unsupported("recursive function returns None")
                v = E(s.value, env, sub, traps)
                rs.append((pc, v, list(sub), list(traps))); return rs, None, None
            if isinstance(s, ast.Raise):
                raise_pcs.append((pc, list(sub), list(traps)))   # a reachable raise escapes: an Err under its pc;
                return rs, None, None                   # the path ends here (it does not return a value, and the
                #                                         exception's message expression is not trap-checked --
                #                                         the raise is already the failure)
            if isinstance(s, ast.Assign):
                if not isinstance(s.targets[0], ast.Name): raise Unsupported("complex target")
                env[s.targets[0].id] = E(s.value, env, sub, traps)
            elif isinstance(s, ast.If):
                csub = list(sub); ctraps = list(traps); c = _as_bool(E(s.test, env, csub, ctraps))
                tr, tf, tenv = returns(s.body, z3.And(pc, c), env, csub, ctraps)
                er, ef, eenv = returns(s.orelse, z3.And(pc, z3.Not(c)), env, csub, ctraps)
                rs += tr + er
                falls = [(p, e) for p, e in ((tf, tenv), (ef, eenv)) if p is not None]
                if not falls:
                    return rs, None, None
                if len(falls) == 2:                    # merge fall-through environments
                    fenv = {}
                    for k in set(tenv) | set(eenv):
                        a, b = tenv.get(k, env.get(k)), eenv.get(k, env.get(k))
                        fenv[k] = a if (a is b or z3.eq(a, b)) else z3.If(c, a, b)
                    fpc = z3.Or(falls[0][0], falls[1][0])
                else:
                    fpc, fenv = falls[0]
                rest, restf, restenv = returns(stmts[idx + 1:], fpc, fenv, csub, ctraps)
                return rs + rest, restf, restenv
            else:
                raise Unsupported(f"recursion statement {type(s).__name__}")
        return rs, pc, env

    rules = []
    try:
        rpaths, _, _ = returns(fn.body, z3.BoolVal(True), dict(pv), [], [])
        for pc, val, sub, traps in rpaths:
            notrap = [z3.Not(t) for t in traps]         # a path returns its value only if no div-by-zero
            rules.append((F(*[pv[p] for p in params], val), [pc] + sub + notrap))
            for t in traps:                             # a reachable div-by-zero under pre violates the spec
                rules.append((Err(), [pre(pv), pc] + sub + [t]))
        for pc, sub, traps in raise_pcs:                # a reachable raise (an input-validation guard or a hard
            notrap = [z3.Not(t) for t in traps]         # error) is an escaping exception: Err when its path is
            rules.append((Err(), [pre(pv), pc] + sub + notrap))   # reachable under the precondition with no prior trap
        rr = fresh()
        rules.append((Err(), [pre(pv), F(*[pv[p] for p in params], rr), z3.Not(post(pv, rr))]))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "CHC/recursion", reason=str(u))

    return _solve_horn(prop, target, "CHC/recursion", "CHC/recursion (inductive)",
                       [F, Err], allvars, rules, Err(),
                       on_error=lambda m: "engine timeout (nonlinear?)" if ("canceled" in m or "timeout" in m) else f"engine: {m}")


def _recursive_bmc_witness(src, pre, post, k=12):
    """A concrete witness for a recursive REFUTED, by bounded symbolic unrolling (no execution). Inline the
    self-recursive function to depth k, then solve for an input meeting the precondition whose recursion bottoms
    out within k (so the unrolled value is exact) and whose return violates the postcondition. Returns
    ({name: value}, str) or (None, None) when none is found within k or the body is outside this unroller.
    Reports an exact spec-violating return, else an input reaching a division trap on a bottomed-out path."""
    try:
        fn = _fndef(src)
    except Unsupported:
        return None, None
    name = fn.name
    params = [a.arg for a in fn.args.args]
    if not params:
        return None, None
    P0 = {p: z3.Int("bw_" + p) for p in params}
    fc = [0]
    traps, deep = [], []

    def fresh():
        fc[0] += 1
        return z3.Int("bwf_%d" % fc[0])

    def E(node, env, pc, depth):
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return z3.IntVal(node.value)
        if isinstance(node, ast.Name):
            if node.id not in env:
                raise Unsupported("free var")
            return env[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -E(node.operand, env, pc, depth)
        if isinstance(node, ast.BinOp):
            op = type(node.op)
            l, r = E(node.left, env, pc, depth), E(node.right, env, pc, depth)
            if op is ast.Add:
                return l + r
            if op is ast.Sub:
                return l - r
            if op is ast.Mult:
                return l * r
            if op in (ast.FloorDiv, ast.Mod):
                traps.append(z3.And(pc, r == 0))
                return py_floordiv(l, r) if op is ast.FloorDiv else py_mod(l, r)
            raise Unsupported("binop")
        if isinstance(node, ast.IfExp):
            c = _as_bool(E(node.test, env, pc, depth))
            return z3.If(c, E(node.body, env, z3.And(pc, c), depth),
                         E(node.orelse, env, z3.And(pc, z3.Not(c)), depth))
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            return _CMP[type(node.ops[0])](E(node.left, env, pc, depth), E(node.comparators[0], env, pc, depth))
        if isinstance(node, ast.BoolOp):
            vs = [_as_bool(E(v, env, pc, depth)) for v in node.values]
            return z3.And(*vs) if isinstance(node.op, ast.And) else z3.Or(*vs)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            fid = node.func.id
            if fid == name:
                avs = [E(a, env, pc, depth) for a in node.args]
                if len(avs) != len(params):
                    raise Unsupported("arity")
                if depth <= 0:
                    deep.append(pc)                          # recursion did not bottom out within k: inexact here
                    return fresh()
                rs, _, _ = walk(fn.body, pc, dict(zip(params, avs)), depth - 1)
                if not rs:
                    return fresh()
                acc = rs[-1][1]
                for ppc, pv in reversed(rs[:-1]):
                    acc = z3.If(ppc, pv, acc)
                return acc
            if fid == "abs" and len(node.args) == 1:
                a = E(node.args[0], env, pc, depth)
                return z3.If(a >= 0, a, -a)
            if fid in ("min", "max") and len(node.args) >= 2:
                vs = [E(a, env, pc, depth) for a in node.args]
                acc = vs[0]
                for x in vs[1:]:
                    acc = z3.If(x < acc, x, acc) if fid == "min" else z3.If(x > acc, x, acc)
                return acc
            raise Unsupported("call")
        raise Unsupported("expr")

    def walk(stmts, pc, env, depth):                         # (returns=[(pc, value)], fall_pc, fall_env)
        rs, env = [], dict(env)
        for idx, s in enumerate(stmts):
            if isinstance(s, ast.Return):
                if s.value is None:
                    raise Unsupported("returns None")
                rs.append((pc, E(s.value, env, pc, depth)))
                return rs, None, None
            if isinstance(s, ast.Assign):
                if len(s.targets) != 1 or not isinstance(s.targets[0], ast.Name):
                    raise Unsupported("complex target")
                env[s.targets[0].id] = E(s.value, env, pc, depth)
            elif isinstance(s, ast.If):
                c = _as_bool(E(s.test, env, pc, depth))
                tr, tf, tenv = walk(s.body, z3.And(pc, c), env, depth)
                er, ef, eenv = walk(s.orelse, z3.And(pc, z3.Not(c)), env, depth)
                rs += tr + er
                falls = [(p, e) for p, e in ((tf, tenv), (ef, eenv)) if p is not None]
                if not falls:
                    return rs, None, None
                if len(falls) == 2:
                    fenv = {}
                    for key in set(tenv) | set(eenv):
                        a, b = tenv.get(key, env.get(key)), eenv.get(key, env.get(key))
                        fenv[key] = a if (a is b or z3.eq(a, b)) else z3.If(c, a, b)
                    fpc = z3.Or(falls[0][0], falls[1][0])
                else:
                    fpc, fenv = falls[0]
                rest, restf, restenv = walk(stmts[idx + 1:], fpc, fenv, depth)
                return rs + rest, restf, restenv
            else:
                raise Unsupported("stmt")
        return rs, pc, env

    try:
        rs, _, _ = walk(fn.body, z3.BoolVal(True), dict(P0), k)
    except Unsupported:
        return None, None
    if not rs:
        return None, None
    val = rs[-1][1]
    for ppc, pv in reversed(rs[:-1]):
        val = z3.If(ppc, pv, val)
    sol = z3.Solver(); sol.set("timeout", 2000)
    try:
        sol.add(pre(P0), *[z3.Not(d) for d in deep])         # only an input whose recursion bottoms out (exact value)
        sol.push()
        sol.add(z3.Not(post(P0, val)), *[z3.Not(tr) for tr in traps])   # a spec-violating, non-trapping return
        if sol.check() != z3.sat:
            sol.pop()                                        # none: try a reachable trap (a div-by-zero) instead, so a
            sol.add(z3.Or(*traps) if traps else z3.BoolVal(False))   # trap-freedom REFUTED (trivial post) also gets a
            if sol.check() != z3.sat:                        # witness, on a path that bottoms out within k (exact)
                return None, None
    except Exception:
        return None, None
    try:
        m = minimize_witness(z3.And(*sol.assertions()), P0, params) or sol.model()   # the smallest triggering input
        inputs = {p: m.eval(P0[p], model_completion=True).as_long() for p in params}
    except Exception:
        return None, None
    return inputs, ", ".join("%s=%s" % (p, inputs[p]) for p in params)


def _interproc_bmc_witness(src, pre_node, spec, repo, k=10):
    """A concrete trapping input for a function whose only crash is reached THROUGH an in-repo callee the
    value-engine inliner bails on (a recursive callee, e.g. f's `x // gcd(x, y)` where gcd recurses, or a
    callee whose own base case traps), by bounded symbolic unrolling of the caller AND its callees -- no
    execution. Each call to an in-repo function (recursive or not) is inlined to a bounded depth; a call that
    does not bottom out within k returns a fresh havoc value and its path is marked inexact (`deep`), so a
    witness is taken only on a fully-unrolled path where the computation is exact. Returns ({name: value}, str)
    reaching a division / modulo trap under the precondition, or (None, None) when none is found within k or the
    bodies are outside this unroller."""
    try:
        fn = _fndef(src)
    except Unsupported:
        return None, None
    params = [a.arg for a in fn.args.args]
    if not params:
        return None, None
    defs = {}                                                    # the callable bodies: the caller plus every in-repo function
    for nm, s in (repo or {}).items():
        try:
            defs[nm] = _fndef(s)
        except Unsupported:
            pass
    defs[fn.name] = fn
    if any(a.annotation is not None and not (isinstance(a.annotation, ast.Name) and a.annotation.id == "int")
           for d in defs.values() for a in d.args.args):
        return None, None                                        # a non-integer parameter: outside this integer unroller
    P0 = {p: z3.Int("iw_" + p) for p in params}
    fc = [0]; traps = []; deep = []

    def fresh():
        fc[0] += 1
        return z3.Int("iwf_%d" % fc[0])

    def E(node, env, pc, depth):
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return z3.IntVal(node.value)
        if isinstance(node, ast.Name):
            if node.id not in env:
                raise Unsupported("free var")
            return env[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -E(node.operand, env, pc, depth)
        if isinstance(node, ast.BinOp):
            op = type(node.op)
            l, r = E(node.left, env, pc, depth), E(node.right, env, pc, depth)
            if op is ast.Add:
                return l + r
            if op is ast.Sub:
                return l - r
            if op is ast.Mult:
                return l * r
            if op in (ast.FloorDiv, ast.Mod):
                traps.append(z3.And(pc, r == 0))
                return py_floordiv(l, r) if op is ast.FloorDiv else py_mod(l, r)
            raise Unsupported("binop")
        if isinstance(node, ast.IfExp):
            c = _as_bool(E(node.test, env, pc, depth))
            return z3.If(c, E(node.body, env, z3.And(pc, c), depth),
                         E(node.orelse, env, z3.And(pc, z3.Not(c)), depth))
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            return _CMP[type(node.ops[0])](E(node.left, env, pc, depth), E(node.comparators[0], env, pc, depth))
        if isinstance(node, ast.BoolOp):
            vs = [_as_bool(E(v, env, pc, depth)) for v in node.values]
            return z3.And(*vs) if isinstance(node.op, ast.And) else z3.Or(*vs)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            fid = node.func.id
            if fid in defs:                                      # inline an in-repo callee (recursive or not) to a bound
                callee = defs[fid]
                cps = [a.arg for a in callee.args.args]
                avs = [E(a, env, pc, depth) for a in node.args]
                if len(avs) != len(cps):
                    raise Unsupported("arity")
                if depth <= 0:
                    deep.append(pc)                              # not bottomed out within k: inexact on this path
                    return fresh()
                rs, _, _ = walk(callee.body, pc, dict(zip(cps, avs)), depth - 1)
                if not rs:
                    return fresh()
                acc = rs[-1][1]
                for ppc, pv in reversed(rs[:-1]):
                    acc = z3.If(ppc, pv, acc)
                return acc
            if fid == "abs" and len(node.args) == 1:
                a = E(node.args[0], env, pc, depth)
                return z3.If(a >= 0, a, -a)
            if fid in ("min", "max") and len(node.args) >= 2:
                vs = [E(a, env, pc, depth) for a in node.args]
                acc = vs[0]
                for x in vs[1:]:
                    acc = z3.If(x < acc, x, acc) if fid == "min" else z3.If(x > acc, x, acc)
                return acc
            raise Unsupported("call")
        raise Unsupported("expr")

    def walk(stmts, pc, env, depth):
        rs, env = [], dict(env)
        for idx, s in enumerate(stmts):
            if isinstance(s, ast.Return):
                if s.value is None:
                    raise Unsupported("returns None")
                rs.append((pc, E(s.value, env, pc, depth)))
                return rs, None, None
            if isinstance(s, ast.Assign):
                if len(s.targets) != 1 or not isinstance(s.targets[0], ast.Name):
                    raise Unsupported("complex target")
                env[s.targets[0].id] = E(s.value, env, pc, depth)
            elif isinstance(s, ast.If):
                c = _as_bool(E(s.test, env, pc, depth))
                tr, tf, tenv = walk(s.body, z3.And(pc, c), env, depth)
                er, ef, eenv = walk(s.orelse, z3.And(pc, z3.Not(c)), env, depth)
                rs += tr + er
                falls = [(p, e) for p, e in ((tf, tenv), (ef, eenv)) if p is not None]
                if not falls:
                    return rs, None, None
                if len(falls) == 2:
                    fenv = {}
                    for key in set(tenv) | set(eenv):
                        a, b = tenv.get(key, env.get(key)), eenv.get(key, env.get(key))
                        fenv[key] = a if (a is b or z3.eq(a, b)) else z3.If(c, a, b)
                    fpc = z3.Or(falls[0][0], falls[1][0])
                else:
                    fpc, fenv = falls[0]
                rest, restf, restenv = walk(stmts[idx + 1:], fpc, fenv, depth)
                return rs + rest, restf, restenv
            elif isinstance(s, (ast.Pass, ast.Import, ast.ImportFrom)):
                continue
            else:
                raise Unsupported("stmt")
        return rs, pc, env

    try:
        walk(fn.body, z3.BoolVal(True), dict(P0), k)             # populates traps / deep as a side effect
    except Unsupported:
        return None, None
    if not traps:
        return None, None
    try:
        pre_term = ev_bool(pre_node, dict(P0), spec)
    except Exception:
        pre_term = z3.BoolVal(True)
    claim_w = z3.And(pre_term, *[z3.Not(d) for d in deep], z3.Or(*traps))   # a reachable trap on a fully-unrolled (exact) path
    sol = z3.Solver(); sol.set("timeout", 2000)
    try:
        sol.add(claim_w)
        if sol.check() != z3.sat:
            return None, None
        m = minimize_witness(claim_w, P0, params) or sol.model()   # the smallest triggering input
        inputs = {p: m.eval(P0[p], model_completion=True).as_long() for p in params}
    except Exception:
        return None, None
    return inputs, ", ".join("%s=%s" % (p, inputs[p]) for p in params)


class _StepBudget(Exception):
    """Raised by the bounded executor when a sampled run exceeds its step budget."""


def _run_bounded(fn, argvals, max_steps=60000):
    """Run fn(*argvals) under a line-step budget so a divergent sample (an infinite loop on
    some concrete input) cannot hang the verifier. Returns (value, True) on a clean finish, or
    (None, False) if it exceeded the budget or raised. Deep recursion self-limits via
    RecursionError; this bounds the looping case too."""
    steps = [0]

    def tracer(frame, event, arg):
        steps[0] += 1
        if steps[0] > max_steps:
            raise _StepBudget()
        return tracer

    old = sys.gettrace()
    sys.settrace(tracer)
    try:
        return fn(*argvals), True
    except Exception:
        return None, False
    finally:
        sys.settrace(old)


def _refute_batch(src, repo, fname, args, samples):
    """Execute the subject on the sampled inputs and return a list of ('ok', int) / ('trap',) /
    ('nonint',) aligned with `samples`, or None if no execution path is available. By default the
    runs happen in an isolated, resource-limited child process (core.SANDBOX_SUBJECT), so the
    concrete check needs no trust in the subject; when execution is explicitly trusted
    (ALLOW_SUBJECT_EXECUTION) an in-process step-bounded run is used, which is faster."""
    inputs = [[s[a] for a in args] for s in samples]
    if core.SANDBOX_SUBJECT:
        out = core.sandbox_run_batch(src, repo or {}, fname, inputs)
        if out is not None:
            return out
        if not core.ALLOW_SUBJECT_EXECUTION:                  # sandbox unavailable and not trusted in-process
            return None
    elif not core.ALLOW_SUBJECT_EXECUTION:
        return None
    try:                                                      # trusted in-process path
        fn = _pyfn(src, repo or {})
    except Exception:
        return None
    out = []
    for argvals in inputs:
        r, done = _run_bounded(fn, argvals)
        out.append(("ok", r) if done and isinstance(r, int) and not isinstance(r, bool)
                   else (("nonint",) if done else ("trap",)))
    return out


def _concrete_refute(src, pre, post, args, repo, trials=400, bound=64, seed=20240916):
    """Fallback for an inconclusive Horn-clause result: sample concrete integer inputs that satisfy the
    precondition, run the real function, and report REFUTED if the postcondition fails on any of them
    (refutation only). The subject runs sandboxed by default; the precondition and postcondition (unpicklable
    Z3 terms) are evaluated here in the parent. Returns a Verdict(REFUTED, ...) or None."""
    if not args or not (core.SANDBOX_SUBJECT or core.ALLOW_SUBJECT_EXECUTION):
        return None
    try:
        fname = next(n for n in _parse(src).body if isinstance(n, ast.FunctionDef)).name
    except StopIteration:
        return None
    rng = random.Random(seed)
    pool = [0, 1, -1, 2, -2, 3, bound, -bound, bound - 1]      # boundary values plus random spread
    samples = []
    for _ in range(trials):
        sample = {a: (rng.choice(pool) if rng.random() < 0.35 else rng.randint(-bound, bound))
                  for a in args}
        try:
            if not z3.is_true(z3.simplify(pre({a: z3.IntVal(sample[a]) for a in args}))):
                continue                                      # only inputs that meet the precondition
        except Exception:
            return None                                       # pre not concretely evaluable: no fallback
        samples.append(sample)
    if not samples:
        return None
    results = _refute_batch(src, repo, fname, args, samples)
    if results is None:
        return None
    for sample, res in zip(samples, results):
        if res[0] != "ok":                                    # a trap / non-int is modeled separately
            continue
        P = {a: z3.IntVal(sample[a]) for a in args}
        try:
            ok = z3.is_true(z3.simplify(post(P, z3.IntVal(res[1]))))
        except Exception:
            return None
        if not ok:
            cex = ", ".join(f"{a}={sample[a]}" for a in args)
            return Verdict(REFUTED, "", "", "concrete refutation (sandboxed CPython oracle)",
                           counterexample=cex, counterexample_inputs=dict(sample),
                           reason="postcondition fails on a concrete execution")
    return None


def _chc_fallback(v, src, pre, post, args, repo):
    """Apply refutation fallbacks to an inconclusive Horn verdict, preserving prop/target/technique
    on the upgraded verdict. PROVED and REFUTED pass through untouched; only UNKNOWN is revisited."""
    if v.status != UNKNOWN:
        return v
    ref = _concrete_refute(src, pre, post, args, repo)
    if ref is not None:
        return Verdict(REFUTED, v.prop, v.target, ref.technique,
                       counterexample=ref.counterexample, reason=ref.reason,
                       counterexample_inputs=ref.counterexample_inputs)
    return v


_REAL_TRANSC = [(core._SIN, _math.sin), (core._COS, _math.cos), (core._EXP, _math.exp), (core._LOG, _math.log)]


def _eval_real_transc(term):
    """Reduce a term whose free variables are already concrete, replacing each sin/cos/exp/log
    application (innermost first) with its real math value. Returns the simplified term, or None on a
    transcendental domain or overflow error (a trap on this input)."""
    t = z3.simplify(term)
    for _ in range(64):
        reps, seen, stack = [], set(), [t]
        while stack:
            n = stack.pop()
            if not z3.is_ast(n) or n.get_id() in seen:
                continue
            seen.add(n.get_id())
            if z3.is_app(n):
                if n.num_args() == 1 and any(n.decl().eq(d) for d, _ in _REAL_TRANSC):
                    arg = z3.simplify(n.arg(0))
                    if z3.is_fp_value(arg) and not z3.is_true(z3.simplify(z3.fpIsNaN(arg))):
                        x = core._fp_to_py(arg)
                        fn = next(f for d, f in _REAL_TRANSC if n.decl().eq(d))
                        try:
                            reps.append((n, z3.FPVal(fn(x), _F64)))
                        except (ValueError, OverflowError):
                            return None
                stack.extend(n.children())
        if not reps:
            break
        t = z3.simplify(z3.substitute(t, *reps))
    return t


def _refute_overapprox(args, z3args, pre_term, post_term, trials=600, seed=20240922):
    """Refute a false transcendental property by sampling concrete finite floats: where the precondition
    holds and the real sin/cos/exp/log make the postcondition false, return the witness dict, else None.
    Sound for refutation -- a concrete input on which the real function violates the property is genuine."""
    if not any(_is_fp(z3args[a]) for a in args):
        return None
    rng = random.Random(seed)
    specials = [0.0, 1.0, -1.0, 0.5, -0.5, _math.pi, -_math.pi, _math.pi / 2, -_math.pi / 2,
                2 * _math.pi, _math.pi / 4, 3 * _math.pi / 2, 1e-9, 1e9, 100.0, -100.0, 709.0]
    for _ in range(trials):
        sample = {a: (rng.choice(specials) if rng.random() < 0.5 else rng.uniform(-20.0, 20.0))
                  if _is_fp(z3args[a]) else rng.randint(-100, 100) for a in args}
        subs = [(z3args[a], z3.FPVal(sample[a], _F64) if _is_fp(z3args[a]) else z3.IntVal(sample[a]))
                for a in args]
        pre_c = _eval_real_transc(z3.substitute(pre_term, *subs))
        if pre_c is None or not z3.is_true(pre_c):
            continue
        post_c = _eval_real_transc(z3.substitute(post_term, *subs))
        if post_c is not None and z3.is_false(post_c):
            return sample
    return None


def _expr_has_quantifier(e):
    """True if the Z3 expression tree contains a quantifier (forall/exists)."""
    seen, stack = set(), [e]
    while stack:
        n = stack.pop()
        if not z3.is_ast(n):
            continue
        if z3.is_quantifier(n):
            return True
        k = n.get_id()
        if k in seen:
            continue
        seen.add(k)
        if z3.is_app(n):
            stack.extend(n.children())
    return False


def verify_recursive_list(prop, target, src, pre, post, timeout=4000, forall_pre=None, forall_post=None) -> Verdict:
    """Recursion over a data structure: a self-recursive function with one or more list-typed parameters
    (annotated `: list`). Each list is encoded as an immutable Z3 array plus its integer length, and the
    function relation ranges over those arrays and the integer arguments. Index recursion is modeled (the list
    threaded through unchanged while an integer index advances toward the length), element reads `xs[i]` become
    array selects, and a read outside `[0, len)` is a trap. `pre(P)` and `post(P, r)` see `P[name]` (the array)
    and `P['len_'+name]`, so a specification may quantify over the list through `len(xs)` and `xs[j]`.

    `forall_pre(element)` assumes a per-element precondition of every element read; `forall_post(element,
    result)` proves a per-element postcondition of every element against the result -- without a quantifier term
    Spacer would reject (forall_pre asserted on each `xs[i]` read, forall_post checked with a free index)."""
    fn = _fndef(src)
    name = fn.name
    pargs = fn.args.args
    params = [a.arg for a in pargs]
    is_list = {a.arg: _is_array_param(a) for a in pargs}
    if not any(is_list.values()):
        return Verdict(UNKNOWN, prop, target, "CHC/recursion (list)",
                       reason="no list-typed parameter; use verify_recursive")
    arr_sort = z3.ArraySort(z3.IntSort(), z3.IntSort())
    pv, sorts = {}, []
    for a in pargs:
        if is_list[a.arg]:
            pv[a.arg] = z3.Array(a.arg, z3.IntSort(), z3.IntSort())
            pv["len_" + a.arg] = z3.Int("len_" + a.arg)
            sorts += [arr_sort, z3.IntSort()]
        else:
            pv[a.arg] = z3.Int("p_" + a.arg)
            sorts.append(z3.IntSort())
    allvars = list(pv.values())
    ctr = [0]

    def fresh():
        v = z3.Int(f"_rl{ctr[0]}"); ctr[0] += 1; allvars.append(v); return v

    F = z3.Function(name + "_lrel", *(sorts + [z3.IntSort(), z3.BoolSort()]))
    Err = z3.Function("Err_lrec", z3.BoolSort())

    # a universally-quantified-over-elements precondition. Spacer rejects a quantifier inside a
    # recursive rule, so rather than carry a forall, the per-element fact is asserted on each element
    # the function actually reads (xs[i] becomes a select constrained by forall_pre): the constraint
    # lands at exactly the recursion level that reads it, so the induction needs no separate relation.
    # This restricts F's relation to inputs whose read elements satisfy the precondition, which is
    # exactly what assuming the universal means for the query.
    first_list = next(a.arg for a in pargs if is_list[a.arg])
    # the integer parameter the recursion uses to index the first list (xs[i]); forall_post quantifies
    # over [that index, len) so the proved universal covers exactly the elements the recursion ranges,
    # falling back to the whole list when no single index parameter is found.
    _post_idxs = {n.slice.id for n in ast.walk(fn) if isinstance(n, ast.Subscript)
                  and isinstance(n.value, ast.Name) and n.value.id == first_list
                  and isinstance(n.slice, ast.Name) and n.slice.id in pv and not is_list.get(n.slice.id, False)}

    def flat(env):                                          # params, in order, flattened to F's args
        out = []
        for a in pargs:
            out += ([env[a.arg], env["len_" + a.arg]] if is_list[a.arg] else [env[a.arg]])
        return out

    def E(node, env, sub, traps):
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return z3.IntVal(node.value)
        if isinstance(node, ast.Name):
            if node.id not in env: raise Unsupported(f"free var {node.id}")
            return env[node.id]
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
            arr = node.value.id
            if "len_" + arr not in env: raise Unsupported(f"subscript of non-list {arr}")
            idx = E(node.slice, env, sub, traps)
            traps.append(z3.Or(idx < 0, idx >= env["len_" + arr]))   # index out of bounds is a trap
            elem = z3.Select(env[arr], idx)
            if forall_pre is not None and arr == first_list:         # assume the quantified precondition
                sub.append(forall_pre(elem))                         #   on every element actually read
            return elem
        if isinstance(node, ast.BinOp):
            op = type(node.op)
            if op in (ast.Add, ast.Sub, ast.Mult):
                return _BINOPS[op](E(node.left, env, sub, traps), E(node.right, env, sub, traps))
            if op in (ast.FloorDiv, ast.Mod):
                l = E(node.left, env, sub, traps); r = E(node.right, env, sub, traps); q = fresh()
                sub.append(z3.Implies(r > 0, z3.And(r * q <= l, l < r * q + r)))
                sub.append(z3.Implies(r < 0, z3.And(r * q >= l, l > r * q + r)))
                traps.append(r == 0)
                return q if op is ast.FloorDiv else (l - r * q)
            raise Unsupported("recursion binop")
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -E(node.operand, env, sub, traps)
        if isinstance(node, ast.IfExp):
            return z3.If(_as_bool(E(node.test, env, sub, traps)),
                         E(node.body, env, sub, traps), E(node.orelse, env, sub, traps))
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            return _CMP[type(node.ops[0])](E(node.left, env, sub, traps),
                                           E(node.comparators[0], env, sub, traps))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            fid = node.func.id
            if fid == "len" and len(node.args) == 1 and isinstance(node.args[0], ast.Name) \
                    and "len_" + node.args[0].id in env:
                return env["len_" + node.args[0].id]
            if fid == name:
                if len(node.args) != len(params): raise Unsupported("recursive arity")
                call_env = {}
                for a, arg in zip(pargs, node.args):
                    if is_list[a.arg]:                     # a list argument must thread the same list through
                        if not (isinstance(arg, ast.Name) and "len_" + arg.id in env):
                            raise Unsupported("list recursion changes the container")
                        call_env[a.arg] = env[arg.id]; call_env["len_" + a.arg] = env["len_" + arg.id]
                    else:
                        call_env[a.arg] = E(arg, env, sub, traps)
                r = fresh(); sub.append(F(*flat(call_env), r)); return r
            if fid == "abs" and len(node.args) == 1:
                a = E(node.args[0], env, sub, traps); return z3.If(a >= 0, a, -a)
            if fid in ("min", "max") and len(node.args) >= 2:    # over values; a single iterable may be empty
                vals = [E(a, env, sub, traps) for a in node.args]; acc = vals[0]
                for x in vals[1:]:
                    acc = z3.If(x < acc, x, acc) if fid == "min" else z3.If(x > acc, x, acc)
                return acc
            raise Unsupported(f"recursion call {fid}")
        raise Unsupported(f"recursion expr {type(node).__name__}")

    def returns(stmts, pc, env, sub, traps):
        rs = []; env = dict(env); sub = list(sub); traps = list(traps)
        for idx, s in enumerate(stmts):
            if isinstance(s, ast.Return):
                if s.value is None: raise Unsupported("recursive function returns None")
                v = E(s.value, env, sub, traps)
                rs.append((pc, v, list(sub), list(traps))); return rs, None, None
            if isinstance(s, ast.Assign):
                if not isinstance(s.targets[0], ast.Name): raise Unsupported("complex target")
                env[s.targets[0].id] = E(s.value, env, sub, traps)
            elif isinstance(s, ast.If):
                csub = list(sub); ctraps = list(traps); c = _as_bool(E(s.test, env, csub, ctraps))
                tr, tf, tenv = returns(s.body, z3.And(pc, c), env, csub, ctraps)
                er, ef, eenv = returns(s.orelse, z3.And(pc, z3.Not(c)), env, csub, ctraps)
                rs += tr + er
                falls = [(p, e) for p, e in ((tf, tenv), (ef, eenv)) if p is not None]
                if not falls:
                    return rs, None, None
                if len(falls) == 2:
                    fenv = {}
                    for k in set(tenv) | set(eenv):
                        a, b = tenv.get(k, env.get(k)), eenv.get(k, env.get(k))
                        fenv[k] = a if (a is b or z3.eq(a, b)) else z3.If(c, a, b)
                    fpc = z3.Or(falls[0][0], falls[1][0])
                else:
                    fpc, fenv = falls[0]
                rest, restf, restenv = returns(stmts[idx + 1:], fpc, fenv, csub, ctraps)
                return rs + rest, restf, restenv
            else:
                raise Unsupported(f"recursion statement {type(s).__name__}")
        return rs, pc, env

    rules = []
    try:
        rpaths, _, _ = returns(fn.body, z3.BoolVal(True), dict(pv), [], [])
        for pc, val, sub, traps in rpaths:
            notrap = [z3.Not(t) for t in traps]
            rules.append((F(*flat(pv), val), [pc] + sub + notrap))
            for t in traps:
                rules.append((Err(), [pre(pv), pc] + sub + [t]))
        rr = fresh()
        rules.append((Err(), [pre(pv), F(*flat(pv), rr), z3.Not(post(pv, rr))]))
        if forall_post is not None:                        # prove the per-element postcondition for every
            jp = fresh()                                   # element: a free index variable is the universal
            start = pv[next(iter(_post_idxs))] if len(_post_idxs) == 1 else z3.IntVal(0)
            rules.append((Err(), [pre(pv), F(*flat(pv), rr), start <= jp, jp < pv["len_" + first_list],
                                  z3.Not(forall_post(z3.Select(pv[first_list], jp), rr))]))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "CHC/recursion (list)", reason=str(u))

    if any(_expr_has_quantifier(b) for _, body in rules for b in body):
        # Spacer rejects a quantifier inside a recursive rule, so a specification that
        # quantifies over every element (e.g. "all elements are nonneg") is outside this
        # fragment. State the element property pointwise or keep the spec quantifier-free
        # (over len(xs) and individual indices), which this engine discharges inductively.
        return Verdict(UNKNOWN, prop, target, "CHC/recursion (list)",
                       reason="specification quantifies over list elements; outside the recursive CHC fragment")

    return _solve_horn(prop, target, "CHC/recursion (list)", "CHC/recursion (list, inductive)",
                       [F, Err], allvars, rules, Err(), corroborate=False,
                       on_error=lambda m: "engine timeout" if ("canceled" in m or "timeout" in m) else f"engine: {m}")


def _is_self_recursive(src) -> bool:
    fn = _fndef(src)
    return any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == fn.name
               for n in ast.walk(fn))


def _collect_termination_edges(bodies, params, is_target_call, prefix, arity_msg):
    """Walk the loop-free bodies of the recursion-termination engines, collecting each recursive / cycle call
    as an edge (pc, callee-args-by-name, division side-constraints): the arithmetic evaluator and path walk
    shared by verify_recursive_termination and verify_mutual_termination. is_target_call(fid) selects a call
    into the recursion (the self-name, or any function in the cycle), recorded under the guards that reach it;
    abs / min / max evaluate over values; anything else is Unsupported. Fresh division-quotient and call-result
    vars carry `prefix`; an arity mismatch on a target call raises Unsupported(arity_msg)."""
    edges = []
    ctr = [0]

    def fresh():
        ctr[0] += 1; return z3.Int(f"{prefix}{ctr[0]}")

    def E(node, env, pc, aux):
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return z3.IntVal(node.value)
        if isinstance(node, ast.Name):
            if node.id not in env: raise Unsupported(f"free var {node.id}")
            return env[node.id]
        if isinstance(node, ast.BinOp):
            op = type(node.op)
            if op in (ast.Add, ast.Sub, ast.Mult):
                return _BINOPS[op](E(node.left, env, pc, aux), E(node.right, env, pc, aux))
            if op in (ast.FloorDiv, ast.Mod):                    # linearized floor division for n // 2 recursions
                l = E(node.left, env, pc, aux); r = E(node.right, env, pc, aux); q = fresh()
                aux.append(z3.Implies(r > 0, z3.And(r * q <= l, l < r * q + r)))
                aux.append(z3.Implies(r < 0, z3.And(r * q >= l, l > r * q + r)))
                return q if op is ast.FloorDiv else (l - r * q)
            raise Unsupported("termination binop")
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -E(node.operand, env, pc, aux)
        if isinstance(node, ast.IfExp):
            return z3.If(_as_bool(E(node.test, env, pc, aux)),
                         E(node.body, env, pc, aux), E(node.orelse, env, pc, aux))
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            return _CMP[type(node.ops[0])](E(node.left, env, pc, aux), E(node.comparators[0], env, pc, aux))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            fid = node.func.id
            if is_target_call(fid):
                if len(node.args) != len(params): raise Unsupported(arity_msg)
                args = {params[i]: E(node.args[i], env, pc, aux) for i in range(len(params))}
                edges.append((pc, args, list(aux)))
                return fresh()                                   # the call's result is irrelevant to termination
            if fid == "abs" and len(node.args) == 1:
                a = E(node.args[0], env, pc, aux); return z3.If(a >= 0, a, -a)
            if fid in ("min", "max") and len(node.args) >= 2:    # over values; a single iterable may be empty
                vals = [E(a, env, pc, aux) for a in node.args]; acc = vals[0]
                for x in vals[1:]:
                    acc = z3.If(x < acc, x, acc) if fid == "min" else z3.If(x > acc, x, acc)
                return acc
            raise Unsupported(f"termination call {fid}")
        raise Unsupported(f"termination expr {type(node).__name__}")

    def walk(stmts, pc, env):
        # thread the fall-through path condition: a recursive call is recorded under the guards that
        # actually reach it, so `if n <= 0: return ...; return f(n - 1)` records the call under n > 0.
        env = dict(env)
        for idx, s in enumerate(stmts):
            if isinstance(s, ast.Return):
                if s.value is not None:
                    E(s.value, env, pc, [])
                return None, None                                # this path ends
            if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
                env[s.targets[0].id] = E(s.value, env, pc, [])
            elif isinstance(s, ast.If):
                c = _as_bool(E(s.test, env, pc, []))
                tpc, tenv = walk(s.body, z3.And(pc, c), env)
                epc, eenv = walk(s.orelse, z3.And(pc, z3.Not(c)), env)
                falls = [(p, e) for p, e in ((tpc, tenv), (epc, eenv)) if p is not None]
                if not falls:
                    return None, None
                if len(falls) == 2:
                    fenv = {}
                    for k in set(tenv) | set(eenv):
                        a, b = tenv.get(k, env.get(k)), eenv.get(k, env.get(k))
                        fenv[k] = a if (a is b or z3.eq(a, b)) else z3.If(c, a, b)
                    fpc = z3.Or(falls[0][0], falls[1][0])
                else:
                    fpc, fenv = falls[0]
                return walk(stmts[idx + 1:], fpc, fenv)          # continue under the merged fall-through
            else:
                raise Unsupported(f"termination statement {type(s).__name__}")
        return pc, env

    pv = {p: z3.Int(p) for p in params}
    for body in bodies:
        walk(body, z3.BoolVal(True), dict(pv))
    return edges


def _linear_measures(params):
    """The linear measure candidates over `params` shared by the recursion-termination engines: each
    parameter and its negation, and for every unordered pair the two differences and the sum. Each is
    (label, lambda S: term) so it applies to both the caller's parameters and a recursive callee's argument
    terms."""
    cands = []
    for p in params:
        cands.append((p, lambda S, p=p: S[p]))
        cands.append((f"-{p}", lambda S, p=p: -S[p]))
    for i, p in enumerate(params):
        for q in params[i + 1:]:
            cands.append((f"{p}-{q}", lambda S, p=p, q=q: S[p] - S[q]))
            cands.append((f"{q}-{p}", lambda S, p=p, q=q: S[q] - S[p]))
            cands.append((f"{p}+{q}", lambda S, p=p, q=q: S[p] + S[q]))
    return cands


def verify_recursive_termination(prop, target, src, pre=None, repo=None) -> Verdict:
    """Termination of self-recursion by a well-founded measure over the parameters: a linear measure
    (a parameter, its negation, or a pairwise difference/sum) that at every recursive call strictly
    decreases, stays >= 0, and preserves the precondition. A decreasing sequence of naturals is finite.
    PROVED with the measure, else UNKNOWN."""
    fn = _fndef(src)
    name = fn.name
    params = [a.arg for a in fn.args.args]
    pv = {p: z3.Int(p) for p in params}
    pre = pre or (lambda P: z3.BoolVal(True))
    try:
        calls = _collect_termination_edges([fn.body], params,
                                           lambda fid: fid == name, "_tm", "recursive arity")
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "recursion termination", reason=str(u))
    if not calls:
        return Verdict(PROVED, prop, target, "recursion termination (no recursive call: halts)")
    cands = _linear_measures(params)                             # linear measures over the parameters
    for lbl, m in cands:
        ok = True
        for pc, args, aux in calls:
            assume = z3.And(pre(pv), pc, *aux)
            dec = _solve(z3.And(assume, z3.Not(m(pv) >= m(args) + 1)))[0]       # m strictly decreases
            bnd = _solve(z3.And(assume, m(args) < 0))[0]                        # the callee's measure stays >= 0
            prs = _solve(z3.And(assume, z3.Not(pre(args))))[0]                  # the precondition is preserved
            if not (dec == PROVED and bnd == PROVED and prs == PROVED):
                ok = False; break
        if ok:
            return Verdict(PROVED, prop, target, "recursion termination (well-founded measure)",
                           reason=f"measure {lbl} decreases and stays >= 0 at every recursive call")
    for i1, (l1, m1) in enumerate(cands):                        # lexicographic measure (size-change flavored): a
        for i2, (l2, m2) in enumerate(cands):                    # recursion whose progress lives in no single
            if i1 == i2:                                         # measure -- a two-counter recursion that resets
                continue                                         # the inner counter when the outer one decrements
            ok = True
            for pc, args, aux in calls:
                assume = z3.And(pre(pv), pc, *aux)
                # per-edge lexicographic descent, bounding only the component that carries the decrease on this
                # edge: either the first strictly decreases and its callee value is >= 0 (the second is then free
                # -- an unconstrained nested-call argument, as in Ackermann), or the first is unchanged and the
                # second strictly decreases and is >= 0. Sound: the first stays in N along any path, so it falls
                # only finitely often, and between its falls the second is a strictly decreasing sequence in N.
                lex_ok = z3.Or(z3.And(m1(pv) > m1(args), m1(args) >= 0),
                               z3.And(m1(pv) == m1(args), m2(pv) > m2(args), m2(args) >= 0))
                dec = _solve(z3.And(assume, z3.Not(lex_ok)))[0]
                prs = _solve(z3.And(assume, z3.Not(pre(args))))[0]   # the precondition is preserved
                if not (dec == PROVED and prs == PROVED):
                    ok = False; break
            if ok:
                return Verdict(PROVED, prop, target, "recursion termination (lexicographic measure)",
                               reason=f"lexicographic measure ({l1}, {l2}) decreases at every recursive call")
    return Verdict(UNKNOWN, prop, target, "recursion termination",
                   reason="no linear or lexicographic well-founded measure found among candidates")


def _termination_scc(target, repo):
    """The strongly-connected component of `target` in the repo call graph: every function mutually
    co-recursive with it (reachable from target and reaching target back). A size > 1 is a mutual-recursion
    cycle; a size 1 is either non-recursive or self-recursive."""
    if target not in repo:
        return set()
    def callees(f):
        try:
            tree = _parse(repo[f])
        except Exception:
            return set()
        return {n.func.id for n in ast.walk(tree)
                if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in repo}
    def closure(start, adj):
        seen, stack = {start}, [start]
        while stack:
            for c in adj(stack.pop()):
                if c not in seen:
                    seen.add(c); stack.append(c)
        return seen
    fwd = closure(target, callees)
    radj = {}
    for f in repo:
        for c in callees(f):
            radj.setdefault(c, set()).add(f)
    bwd = closure(target, lambda f: radj.get(f, set()))
    return fwd & bwd


def verify_mutual_termination(prop, target, repo, pre=None) -> Verdict:
    """Termination of a mutual-recursion cycle by one well-founded measure shared across the cycle: a linear
    measure over the parameters (which the cycle's functions share by name) that, at every call edge inside
    the cycle, strictly decreases, stays >= 0, and preserves the precondition. is_even(n) -> is_odd(n - 1) ->
    is_even(n - 1) halts by the measure n. A single-function cycle defers to verify_recursive_termination.
    PROVED with the measure, else UNKNOWN (the cycle may still halt by a measure outside the candidate set)."""
    scc = _termination_scc(target, repo)
    if len(scc) <= 1:
        if target in repo and _is_self_recursive(repo[target]):
            return verify_recursive_termination(prop, target, repo[target], pre, repo)
        return Verdict(UNKNOWN, prop, target, "mutual recursion termination", reason="not a mutual recursion cycle")
    try:
        fns = {n: _fndef(repo[n]) for n in scc}
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "mutual recursion termination", reason=str(u))
    params = [a.arg for a in fns[target].args.args]
    if any([a.arg for a in fns[n].args.args] != params for n in scc):
        return Verdict(UNKNOWN, prop, target, "mutual recursion termination",
                       reason="cycle functions do not share parameter names; no shared positional measure")
    pre = pre or (lambda P: z3.BoolVal(True))
    pv = {p: z3.Int(p) for p in params}
    try:
        edges = _collect_termination_edges([fns[n].body for n in scc], params,
                                           lambda fid: fid in scc, "_mt", "cycle-call arity")
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "mutual recursion termination", reason=str(u))
    if not edges:
        return Verdict(PROVED, prop, target, "mutual recursion termination (no recursive call: halts)")
    cands = _linear_measures(params)
    for lbl, m in cands:
        ok = True
        for pc, args, aux in edges:
            assume = z3.And(pre(pv), pc, *aux)
            dec = _solve(z3.And(assume, z3.Not(m(pv) >= m(args) + 1)))[0]       # m strictly decreases
            bnd = _solve(z3.And(assume, m(args) < 0))[0]                        # the callee's measure stays >= 0
            prs = _solve(z3.And(assume, z3.Not(pre(args))))[0]                  # the precondition is preserved
            if not (dec == PROVED and bnd == PROVED and prs == PROVED):
                ok = False; break
        if ok:
            return Verdict(PROVED, prop, target, "mutual recursion termination (well-founded measure)",
                           reason="shared measure %s decreases around the cycle (%s)" % (lbl, ", ".join(sorted(scc))))
    return Verdict(UNKNOWN, prop, target, "mutual recursion termination",
                   reason="no shared well-founded measure found among candidates")


def verify_total(prop, target, src, pre, post, inv=None, repo=None) -> Verdict:
    if _is_self_recursive(src):                                  # recursion: partial via CHC, halting via a measure
        partial = verify_recursive(prop, target, src, pre, post)
        if partial.status != PROVED:
            return partial
        term = verify_recursive_termination(prop, target, src, pre, repo)
        if term.status != PROVED:
            return Verdict(term.status, prop, target, "total correctness",
                           reason=f"partial correctness holds but recursion termination is {term.status}: {term.reason}")
        return Verdict(PROVED, prop, target, "total correctness (recursion: partial + well-founded measure)",
                       reason=term.reason)
    partial = verify_function(prop, target, src, pre, post, repo)
    if partial.status != PROVED:
        return partial
    term = verify_termination(prop, target, src, repo, inv=inv)
    if term.status == PROVED:
        return Verdict(PROVED, prop, target, "total correctness (partial + termination)",
                       reason=term.reason)
    # termination not proven: a recurrence set under `pre` refutes total correctness with a diverging witness
    nonterm = verify_nontermination(prop, target, src, repo, pre=pre)
    if nonterm.status == REFUTED:
        return Verdict(REFUTED, prop, target, "total correctness",
                       counterexample=nonterm.counterexample, counterexample_inputs=nonterm.counterexample_inputs,
                       reason=f"partial correctness holds but the loop provably does not terminate: {nonterm.reason}",
                       trace=nonterm.trace)   # the divergence certificate
    return Verdict(term.status, prop, target, "total correctness",
                   reason=f"partial correctness holds but termination is {term.status}: {term.reason}")


def _is_array_param(arg):
    ann = arg.annotation
    if isinstance(ann, ast.Name):
        return ann.id == "list"                              # bare list: integer-element over-approximation
    # a parameterized generic with an INTEGER element -- list[int], List[int], Sequence[int] -- is the same
    # integer-array model; a non-int element (list[str], list[float]) is excluded, since the engine models
    # every element as an Int and a str/float element op would otherwise read as a total integer op.
    if (isinstance(ann, ast.Subscript) and isinstance(ann.value, ast.Name)
            and ann.value.id in ("list", "List", "Sequence", "MutableSequence")):
        return isinstance(ann.slice, ast.Name) and ann.slice.id in ("int", "bool")
    return False


def _ev_arr(node, st, obligs, pc):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return z3.IntVal(node.value)
    if isinstance(node, ast.Name):
        if node.id not in st:
            raise Unsupported(f"free var {node.id}")
        return st[node.id]
    if isinstance(node, ast.Subscript):
        idx = _ev_arr(node.slice, st, obligs, pc)
        obligs.append(z3.Implies(pc, z3.And(idx >= 0, idx < st["len_" + node.value.id])))
        return z3.Select(st[node.value.id], idx)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "len":
        return st["len_" + node.args[0].id]
    if isinstance(node, ast.BinOp):
        l = _ev_arr(node.left, st, obligs, pc)
        r = _ev_arr(node.right, st, obligs, pc)
        if isinstance(node.op, ast.Add): return l + r
        if isinstance(node.op, ast.Sub): return l - r
        if isinstance(node.op, ast.Mult): return l * r
        raise Unsupported(f"arr binop {type(node.op).__name__}")
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        l = _ev_arr(node.left, st, obligs, pc)
        r = _ev_arr(node.comparators[0], st, obligs, pc)
        op = node.ops[0]
        if isinstance(op, ast.Lt): return l < r
        if isinstance(op, ast.LtE): return l <= r
        if isinstance(op, ast.Gt): return l > r
        if isinstance(op, ast.GtE): return l >= r
        if isinstance(op, ast.Eq): return l == r
        if isinstance(op, ast.NotEq): return l != r
    raise Unsupported(f"arr expr {type(node).__name__}")


def _arr_state(args):
    st = {}
    for a in args:
        if _is_array_param(a):
            st[a.arg] = z3.Array(a.arg, z3.IntSort(), z3.IntSort())
            st["len_" + a.arg] = z3.Int("len_" + a.arg)
        else:
            st[a.arg] = z3.Int(a.arg)
    return st


def _local_array_alloc(node, st, obligs, pc):
    """A locally-allocated integer array as (array_term, length_term), or None. Recognizes `[c] * n` / `n *
    [c]` and `[c for _ in range(n)]` (a constant fill, length n clamped at 0) and a list literal `[e0, e1,
    ...]` (length len(elts)); the array is a Z3 array so a later a[i] store / read bounds-checks against the
    length exactly as a parameter array does. The allocated length is exact, but the engine only relies on
    `n <= len_a`, so a longer model would stay sound."""
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):       # [c] * n  or  n * [c]
        for lst, cnt in ((node.left, node.right), (node.right, node.left)):
            if (isinstance(lst, ast.List) and len(lst.elts) == 1 and isinstance(lst.elts[0], ast.Constant)
                    and isinstance(lst.elts[0].value, int) and not isinstance(lst.elts[0].value, bool)):
                n = _ev_arr(cnt, st, obligs, pc)
                return z3.K(z3.IntSort(), z3.IntVal(lst.elts[0].value)), z3.If(n > 0, n, z3.IntVal(0))
    if (isinstance(node, ast.ListComp) and len(node.generators) == 1 and not node.generators[0].ifs
            and isinstance(node.elt, ast.Constant) and isinstance(node.elt.value, int)
            and not isinstance(node.elt.value, bool)):                       # [c for _ in range(n)]
        it = node.generators[0].iter
        if (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range"
                and len(it.args) == 1):
            n = _ev_arr(it.args[0], st, obligs, pc)
            return z3.K(z3.IntSort(), z3.IntVal(node.elt.value)), z3.If(n > 0, n, z3.IntVal(0))
    if isinstance(node, ast.List):                                          # a list literal [e0, e1, ...]
        arr = z3.K(z3.IntSort(), z3.IntVal(0))
        for k, el in enumerate(node.elts):
            arr = z3.Store(arr, z3.IntVal(k), _ev_arr(el, st, obligs, pc))
        return arr, z3.IntVal(len(node.elts))
    return None


def _arr_apply(stmts, st, obligs, pc):
    st = dict(st)
    for s in stmts:
        if isinstance(s, ast.Assign):
            tgt = s.targets[0]
            if isinstance(tgt, ast.Subscript):
                idx = _ev_arr(tgt.slice, st, obligs, pc)
                obligs.append(z3.Implies(pc, z3.And(idx >= 0, idx < st["len_" + tgt.value.id])))
                st[tgt.value.id] = z3.Store(st[tgt.value.id], idx, _ev_arr(s.value, st, obligs, pc))
            elif isinstance(tgt, ast.Name) and (_alloc := _local_array_alloc(s.value, st, obligs, pc)) is not None:
                st[tgt.id], st["len_" + tgt.id] = _alloc      # a locally-allocated array: a fresh Z3 array + length
            else:
                st[tgt.id] = _ev_arr(s.value, st, obligs, pc)
        elif isinstance(s, ast.If):                          # merge branches with z3.If
            cond = _ev_arr(s.test, st, obligs, pc)
            then_st = _arr_apply(s.body, st, obligs, z3.And(pc, cond))
            else_st = _arr_apply(s.orelse, st, obligs, z3.And(pc, z3.Not(cond)))
            merged = dict(st)
            for k in set(then_st) | set(else_st):
                tv, ev_ = then_st.get(k, st.get(k)), else_st.get(k, st.get(k))
                # one-sided definition (and not defined before the if): havoc the
                # undefined side under the guard (fresh constant of the same sort).
                if tv is None and ev_ is None:
                    continue
                elif tv is None:
                    merged[k] = z3.If(cond, z3.FreshConst(ev_.sort(), "undef"), ev_)
                elif ev_ is None:
                    merged[k] = z3.If(cond, tv, z3.FreshConst(tv.sort(), "undef"))
                elif tv is ev_ or z3.eq(tv, ev_):
                    merged[k] = tv
                else:
                    merged[k] = z3.If(cond, tv, ev_)
            st = merged
        else:
            raise Unsupported(f"array-loop statement {type(s).__name__}")
    return st


def _fresh_like(state, suffix="#"):
    return {k: (z3.Array(k + suffix, z3.IntSort(), z3.IntSort()) if z3.is_array(v) else z3.Int(k + suffix))
            for k, v in state.items()}


def q_forall(body_fn, name="j"):
    j = z3.Int(name)
    return z3.ForAll([j], body_fn(j))


def verify_array_loop(prop, target, src, pre, inv, post) -> Verdict:
    """Deductive array-loop verification. `post(exit_state, entry_state)` receives the
    loop-exit state and the distinct pre-loop (entry) state, so a postcondition may
    relate the result to the inputs as they were on entry."""
    fn, _names, init, loop, ret = _parse_single_loop(src)
    if loop is None:
        return Verdict(UNKNOWN, prop, target, "array deductive", reason="not a single-loop function")
    try:
        base = _arr_state(fn.args.args)
        ob = []
        init_state = _arr_apply(init, base, ob, z3.BoolVal(True))
        sym = _fresh_like(init_state)
        ob_body = []
        guard = _ev_arr(loop.test, sym, ob_body, z3.BoolVal(True))
        body_state = _arr_apply(loop.body, sym, ob_body, guard)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "array deductive", reason=str(u))
    for o in ob_body:                                   # bounds-safety in the loop body
        st, model = _solve(z3.And(inv(sym), guard, z3.Not(o)))
        if st == REFUTED:
            return Verdict(REFUTED, prop, target, "array deductive (bounds)",
                           reason="index can be out of bounds under the invariant")
        if st == UNKNOWN:
            return Verdict(UNKNOWN, prop, target, "array deductive (bounds)", reason="solver unknown")
    if _solve(z3.And(pre(base), z3.Not(inv(init_state))))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "array deductive", reason="initiation not established")
    if _solve(z3.And(inv(sym), guard, z3.Not(inv(body_state))))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "array deductive", reason="invariant not preserved")
    if _solve(z3.And(inv(sym), z3.Not(guard), z3.Not(post(sym, init_state))))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "array deductive", reason="postcondition not established")
    return Verdict(PROVED, prop, target, "array deductive (bounds + quantified spec)")


def verify_array_loop_auto(prop, target, src, pre, post) -> Verdict:
    """Infer the invariant for the canonical single-write array loop and discharge
    {pre} f {post} with no supplied invariant. For
        i = 0; while i < n: a[i] = e; i = i + 1     (e not reading a)
    the inferred invariant is the standard prefix invariant
        0 <= i <= n <= len_a  and  for all j in [0, i): a[j] == e[i := j]."""
    fn, _names, init, loop, ret = _parse_single_loop(src)
    if loop is None:
        return Verdict(UNKNOWN, prop, target, "array deductive (auto)", reason="not a single-loop function")
    test = loop.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1 and isinstance(test.ops[0], ast.Lt)
            and isinstance(test.left, ast.Name) and isinstance(test.comparators[0], ast.Name)):
        return Verdict(UNKNOWN, prop, target, "array deductive (auto)", reason="guard is not `i < n`")
    i_name, n_name = test.left.id, test.comparators[0].id
    writes = [s for s in loop.body if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Subscript)]
    if len(writes) != 1:
        return Verdict(UNKNOWN, prop, target, "array deductive (auto)", reason="not a single array write")
    w = writes[0]
    if not (isinstance(w.targets[0].value, ast.Name) and isinstance(w.targets[0].slice, ast.Name)
            and w.targets[0].slice.id == i_name):
        return Verdict(UNKNOWN, prop, target, "array deductive (auto)", reason="write is not a[i] = e")
    arr, rhs = w.targets[0].value.id, w.value
    read_arrs = {nd.value.id for nd in ast.walk(rhs)
                 if isinstance(nd, ast.Subscript) and isinstance(nd.value, ast.Name)}
    if arr in read_arrs:                                      # in-place self-read needs a ghost of the entry array
        return Verdict(UNKNOWN, prop, target, "array deductive (auto)",
                       reason="the written value reads the array being written (in-place transform)")
    # reading OTHER (unwritten, hence stable) arrays is fine: b[i] = a[i] + c is a cross-array
    # transform whose prefix invariant relates b[0:i] to a[0:i] element-wise.
    step = 1                                                  # the counter's stride: i = i + step (a constant > 0)
    for s in loop.body:
        if (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                and s.targets[0].id == i_name and isinstance(s.value, ast.BinOp)
                and isinstance(s.value.op, ast.Add)):
            for a, b in ((s.value.left, s.value.right), (s.value.right, s.value.left)):
                if (isinstance(a, ast.Name) and a.id == i_name and isinstance(b, ast.Constant)
                        and isinstance(b.value, int) and not isinstance(b.value, bool) and b.value > 0):
                    step = b.value

    def inv(S):
        i, n = S[i_name], S[n_name]
        # a non-unit stride writes only the indices congruent to 0 mod step; i stays a multiple of step and
        # overshoots n by at most step - 1, so the prefix invariant is over the strided indices.
        bounds = [0 <= i, i <= n + (step - 1)]
        if step > 1:
            bounds.append(i % step == 0)
        for arrname in {arr} | read_arrs:                    # every array touched is long enough
            bounds.append(n <= S["len_" + arrname])

        def prefix(j):
            st = dict(S); st[i_name] = j
            inrange = z3.And(0 <= j, j < i) if step == 1 else z3.And(0 <= j, j < i, j % step == 0)
            return z3.Implies(inrange, z3.Select(S[arr], j) == _ev_arr(rhs, st, [], z3.BoolVal(True)))
        return z3.And(*bounds, q_forall(prefix))

    v = verify_array_loop(prop, target, src, pre, inv, post)
    if v.status == PROVED:
        return Verdict(PROVED, prop, target, "array deductive (auto-invariant)",
                       reason=f"inferred prefix invariant over a[0:{i_name}]" + (f" stride {step}" if step > 1 else ""))
    return v


def verify_array_code(prop, target, src, post, pre=None) -> Verdict:
    """Discharge a separation / frame / disjointness property over the actual loads and stores of a loop-free
    function on `list`-annotated parameters. Each list parameter is a distinct Z3 array (so two arrays never
    alias: a write to one frames the other), an integer index outside [0, len) is a trap that refutes, and
    `post(final_state, entry_state)` relates the final array contents to the entry ones (S[name] the array,
    S['len_'+name] the length). `pre(entry_state)` optionally constrains the inputs. UNKNOWN for a function with
    a loop (use verify_array_loop) or outside the array fragment."""
    pre = pre or (lambda S: z3.BoolVal(True))
    fn = _fndef(src)
    if any(isinstance(n, (ast.While, ast.For)) for n in ast.walk(fn)):
        return Verdict(UNKNOWN, prop, target, "array code", reason="a loop: use verify_array_loop")
    try:
        entry = _arr_state(fn.args.args)
        ob = []
        body = [s for s in fn.body if not isinstance(s, ast.Return)]   # the post is over array state, not a return
        final = _arr_apply(body, entry, ob, z3.BoolVal(True))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "array code", reason=str(u))
    for o in ob:                                              # bounds safety: every index obligation under pre
        st, model = _solve(z3.And(pre(entry), z3.Not(o)))
        if st == REFUTED:
            return Verdict(REFUTED, prop, target, "array code (bounds)", reason="index can be out of bounds")
        if st == UNKNOWN:
            return Verdict(UNKNOWN, prop, target, "array code (bounds)", reason="solver unknown")
    try:
        claim = z3.And(pre(entry), z3.Not(post(final, entry)))
    except (z3.Z3Exception, KeyError, TypeError) as u:
        return Verdict(UNKNOWN, prop, target, "array code", reason=str(u))
    st, model = _solve_corro(claim)
    if st == PROVED:
        return Verdict(PROVED, prop, target, "array code (frame + disjointness over actual loads/stores)")
    if st == REFUTED:
        return Verdict(REFUTED, prop, target, "array code")
    return Verdict(UNKNOWN, prop, target, "array code", reason="solver returned unknown")


def _only_incremented(fn, var):
    """True if `var` is assigned only `var = 0` (initialization) and `var = var + c` for a positive integer
    constant c, and nothing else (no other store), so var >= 0 holds throughout. This makes the index
    invariants of a nested counter loop sound by construction, without a separately discharged invariant."""
    for n in ast.walk(fn):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                and n.targets[0].id == var:
            v = n.value
            zero = isinstance(v, ast.Constant) and v.value == 0
            incr = (isinstance(v, ast.BinOp) and isinstance(v.op, ast.Add)
                    and ((isinstance(v.left, ast.Name) and v.left.id == var and isinstance(v.right, ast.Constant)
                          and isinstance(v.right.value, int) and not isinstance(v.right.value, bool) and v.right.value > 0)
                         or (isinstance(v.right, ast.Name) and v.right.id == var and isinstance(v.left, ast.Constant)
                             and isinstance(v.left.value, int) and not isinstance(v.left.value, bool) and v.left.value > 0)))
            if not (zero or incr):
                return False
        elif isinstance(n, (ast.AugAssign, ast.AnnAssign)) and isinstance(getattr(n, "target", None), ast.Name) \
                and n.target.id == var:
            return False                                         # an aug/annotated store: not the plain pattern
    return True


def verify_nested_array_bounds(prop, target, src, pre=None) -> Verdict:
    """Bounds-safety of a doubly-nested array loop:
        i = 0; while i < n: j = 0; while j < m: <body with array accesses>; j = j + sj; i = i + si
    Every array index in the inner body is proved within [0, len) under the precondition (which typically
    supplies n * m <= len(a), so a flattened index i * m + j stays in bounds -- a nonlinear bound z3
    discharges) together with i >= 0, j >= 0 (guaranteed because each counter starts at 0 and only increments
    by a positive constant) and the loop guards i < n, j < m that hold wherever the body runs. PROVED when
    every access is in bounds, REFUTED when one is provably out, UNKNOWN outside the pattern. This is trap
    freedom for the nested fill; the array contents are not proved here (see verify_array_loop for content)."""
    pre = pre or (lambda S: z3.BoolVal(True))
    try:
        fn = _fndef(src)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "nested array bounds", reason=str(u))
    outers = [s for s in fn.body if isinstance(s, ast.While)]
    if len(outers) != 1:
        return Verdict(UNKNOWN, prop, target, "nested array bounds", reason="not a single outer loop")
    outer, g = outers[0], outers[0].test
    if not (isinstance(g, ast.Compare) and len(g.ops) == 1 and isinstance(g.ops[0], ast.Lt)
            and isinstance(g.left, ast.Name) and isinstance(g.comparators[0], ast.Name)):
        return Verdict(UNKNOWN, prop, target, "nested array bounds", reason="outer guard is not i < n")
    i_name, n_name = g.left.id, g.comparators[0].id
    inners = [s for s in outer.body if isinstance(s, ast.While)]
    if len(inners) != 1:
        return Verdict(UNKNOWN, prop, target, "nested array bounds", reason="not a single inner loop")
    inner, ig = inners[0], inners[0].test
    if not (isinstance(ig, ast.Compare) and len(ig.ops) == 1 and isinstance(ig.ops[0], ast.Lt)
            and isinstance(ig.left, ast.Name) and isinstance(ig.comparators[0], ast.Name)):
        return Verdict(UNKNOWN, prop, target, "nested array bounds", reason="inner guard is not j < m")
    j_name, m_name = ig.left.id, ig.comparators[0].id
    if not (_only_incremented(fn, i_name) and _only_incremented(fn, j_name)):
        return Verdict(UNKNOWN, prop, target, "nested array bounds",
                       reason="a loop counter is modified beyond start-at-0 and positive increment")
    if any(isinstance(s, (ast.While, ast.For)) for s in ast.walk(ast.Module(body=list(inner.body), type_ignores=[]))):
        return Verdict(UNKNOWN, prop, target, "nested array bounds", reason="a third loop level is not modeled")
    try:
        st = _arr_state(fn.args.args)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "nested array bounds", reason=str(u))
    st[i_name], st[j_name] = z3.Int(i_name), z3.Int(j_name)
    obligs = []
    try:
        guard = z3.And(st[i_name] < st[n_name], st[j_name] < st[m_name])
        _arr_apply(list(inner.body), st, obligs, guard)          # collect the inner body's index obligations
        assume = z3.And(pre(st), st[i_name] >= 0, st[j_name] >= 0, guard)
    except (Unsupported, KeyError, z3.Z3Exception, TypeError) as u:
        return Verdict(UNKNOWN, prop, target, "nested array bounds", reason=str(u))
    if not obligs:
        return Verdict(UNKNOWN, prop, target, "nested array bounds", reason="no array access in the inner body")
    for o in obligs:
        st_, _model = _solve(z3.And(assume, z3.Not(o)))
        if st_ == REFUTED:
            return Verdict(REFUTED, prop, target, "nested array bounds",
                           reason="an inner-loop array index can be out of bounds")
        if st_ == UNKNOWN:
            return Verdict(UNKNOWN, prop, target, "nested array bounds", reason="solver unknown on a bounds obligation")
    return Verdict(PROVED, prop, target, "nested array bounds (doubly-nested index in [0, len))")


def _unit_increment(fn, var):
    """True if every `var = var + c` / `var = c + var` in `fn` steps by exactly 1, so a counter fills a
    contiguous range (needed for a flat-index nested-fill invariant; a stride would leave gaps)."""
    for n in ast.walk(fn):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                and n.targets[0].id == var and isinstance(n.value, ast.BinOp) and isinstance(n.value.op, ast.Add)):
            v = n.value
            for a, b in ((v.left, v.right), (v.right, v.left)):
                if isinstance(a, ast.Name) and a.id == var and not (isinstance(b, ast.Constant) and b.value == 1):
                    return False
    return True


def verify_nested_array_content(prop, target, src, post, pre=None) -> Verdict:
    """Content of a doubly-nested CONSTANT array fill:
        i = 0; while i < n: j = 0; while j < m: a[i * m + j] = c; j = j + 1; i = i + 1
    proved through the contiguous flat-index invariant `forall k in [0, i * m + j): a[k] == c` -- the prefix
    written so far, a single linear region since unit-step counters fill 0, 1, 2, ... in order. `post(exit,
    entry)` -- typically `forall k in [0, n * m): a[k] == c` -- is discharged at the outer exit and the write
    index is shown in [0, len). Only a constant fill is in scope: a value reading i or j needs the
    2D-decomposed invariant a[k] == e(k // m, k % m), a nonlinear quantified index z3 does not discharge.
    PROVED / REFUTED (a real out-of-bounds write) / UNKNOWN."""
    pre = pre or (lambda S: z3.BoolVal(True))
    try:
        fn = _fndef(src)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "nested array content", reason=str(u))
    outers = [s for s in fn.body if isinstance(s, ast.While)]
    if len(outers) != 1:
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="not a single outer loop")
    outer, g = outers[0], outers[0].test
    inners = [s for s in outer.body if isinstance(s, ast.While)]
    if not (len(inners) == 1 and isinstance(g, ast.Compare) and len(g.ops) == 1 and isinstance(g.ops[0], ast.Lt)
            and isinstance(g.left, ast.Name) and isinstance(g.comparators[0], ast.Name)):
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="outer is not `while i < n` with one inner loop")
    inner, ig = inners[0], inners[0].test
    if not (isinstance(ig, ast.Compare) and len(ig.ops) == 1 and isinstance(ig.ops[0], ast.Lt)
            and isinstance(ig.left, ast.Name) and isinstance(ig.comparators[0], ast.Name)):
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="inner guard is not `j < m`")
    i_name, n_name, j_name, m_name = g.left.id, g.comparators[0].id, ig.left.id, ig.comparators[0].id
    writes = [s for s in inner.body if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Subscript)
              and isinstance(s.targets[0].value, ast.Name)]
    if len(writes) != 1:
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="not a single a[...] write in the inner body")
    w = writes[0]
    arr_name = w.targets[0].value.id
    if not (_only_incremented(fn, i_name) and _only_incremented(fn, j_name)
            and _unit_increment(fn, i_name) and _unit_increment(fn, j_name)):
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="counters are not unit-step from 0")
    try:
        st = _arr_state(fn.args.args)
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "nested array content", reason=str(u))
    if arr_name not in st or ("len_" + arr_name) not in st or m_name not in st or n_name not in st:
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="array, n, or m is not a parameter")
    I, J, M, N = z3.Int(i_name), z3.Int(j_name), st[m_name], st[n_name]
    if not (z3.is_int(M) and z3.is_int(N)):
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="n or m is not an integer parameter")
    st[i_name], st[j_name] = I, J
    try:
        idx = _ev_arr(w.targets[0].slice, st, [], z3.BoolVal(True))                  # reads i, j, m -> i * m + j
        st0 = {k: v for k, v in st.items() if k not in (i_name, j_name)}             # the value must be constant in i, j
        c = _ev_arr(w.value, st0, [], z3.BoolVal(True))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="the fill value reads i/j or is unmodeled: " + str(u))
    if _solve(idx != I * M + J)[0] != PROVED:                                        # the row-major flatten
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="the write index is not i * m + j")
    arr = z3.Array(arr_name + "#nc", z3.IntSort(), z3.IntSort())                     # the loop's current array
    lenA = st["len_" + arr_name]

    def inv(ii, jj, a):
        k = z3.FreshInt("k")
        return z3.ForAll([k], z3.Implies(z3.And(0 <= k, k < ii * M + jj), z3.Select(a, k) == c))

    P = pre(st)
    bounds = z3.Implies(z3.And(P, 0 <= I, I < N, 0 <= J, J < M), z3.And(I * M + J >= 0, I * M + J < lenA))
    pres = z3.Implies(z3.And(P, inv(I, J, arr), 0 <= I, I < N, 0 <= J, J < M), inv(I, J + 1, z3.Store(arr, I * M + J, c)))
    step = z3.Implies(z3.And(P, inv(I, M, arr), 0 <= I, I < N), inv(I + 1, z3.IntVal(0), arr))
    init = z3.Implies(P, inv(z3.IntVal(0), z3.IntVal(0), arr))
    exit_st = dict(st); exit_st[i_name], exit_st[arr_name] = N, arr
    try:
        post_vc = z3.Implies(z3.And(P, inv(N, z3.IntVal(0), arr)), post(exit_st, st))
    except (z3.Z3Exception, KeyError, TypeError):
        return Verdict(UNKNOWN, prop, target, "nested array content", reason="postcondition over the state failed")
    bst, _bm = _solve(z3.Not(bounds))
    if bst == REFUTED:
        return Verdict(REFUTED, prop, target, "nested array content (bounds)", reason="the write index can be out of bounds")
    if bst != PROVED:
        return Verdict(UNKNOWN, prop, target, "nested array content (bounds)", reason="solver unknown on the bounds obligation")
    for vc in (init, pres, step, post_vc):
        if _solve(z3.Not(vc))[0] != PROVED:
            return Verdict(UNKNOWN, prop, target, "nested array content", reason="a verification condition did not discharge")
    return Verdict(PROVED, prop, target, "nested array content (flat-index invariant over the constant fill)")


def _empty_list_lit(v):
    return ((isinstance(v, ast.List) and not v.elts)
            or (isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id == "list" and not v.args))


def verify_growing_list_auto(prop, target, src, post, pre=None) -> Verdict:
    """The CONTENT of a list grown by append in a counted loop (a = []; while i < n: a.append(e); i += 1),
    not only its length: models the list as an array whose length grows with the counter, infers the
    prefix invariant len(a) == i and a[j] == e[i := j], and discharges the Hoare conditions.
    post(params, a, length) is the claim about the built list at exit. UNKNOWN outside this pattern."""
    pre = pre or (lambda S: z3.BoolVal(True))
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None:
        return Verdict(UNKNOWN, prop, target, "growing list", reason="not a single-loop function")
    t = loop.test
    if not (isinstance(t, ast.Compare) and len(t.ops) == 1 and isinstance(t.ops[0], ast.Lt)
            and isinstance(t.left, ast.Name) and isinstance(t.comparators[0], ast.Name)):
        return Verdict(UNKNOWN, prop, target, "growing list", reason="guard is not `i < n`")
    iname, nname = t.left.id, t.comparators[0].id
    built = [s.targets[0].id for s in init if isinstance(s, ast.Assign) and len(s.targets) == 1
             and isinstance(s.targets[0], ast.Name) and _empty_list_lit(s.value)]
    if len(built) != 1:
        return Verdict(UNKNOWN, prop, target, "growing list", reason="not a single list initialized to []")
    aname = built[0]
    appends = [s.value for s in loop.body if isinstance(s, ast.Expr) and isinstance(s.value, ast.Call)
               and isinstance(s.value.func, ast.Attribute) and s.value.func.attr == "append"
               and isinstance(s.value.func.value, ast.Name) and s.value.func.value.id == aname
               and len(s.value.args) == 1]
    if len(appends) != 1:
        return Verdict(UNKNOWN, prop, target, "growing list", reason="not a single append to the list")
    aexpr = appends[0].args[0]
    body_assigns = [s for s in loop.body if isinstance(s, ast.Assign)]
    incr = [s for s in body_assigns if isinstance(s.targets[0], ast.Name) and s.targets[0].id == iname]
    if len(incr) != 1:
        return Verdict(UNKNOWN, prop, target, "growing list", reason="counter not updated once")
    # A running accumulator alongside the counter is fine, but only if the appended value does not read it:
    # the prefix invariant a[j] == e[i := j] requires e to be a function of the counter and parameters, so an
    # appended expression that reads a loop-updated accumulator (not the counter) is declined.
    extra = {s.targets[0].id for s in body_assigns if isinstance(s.targets[0], ast.Name)} - {iname}
    if extra & {n.id for n in ast.walk(aexpr) if isinstance(n, ast.Name)}:
        return Verdict(UNKNOWN, prop, target, "growing list", reason="the appended value reads a loop accumulator")
    try:
        params = {p: z3.Int(p) for p in args}
        n = params[nname]
        inc_val = _ev_arr(incr[0].value, {**params, iname: z3.Int(iname)}, [], z3.BoolVal(True))
        if not z3.eq(z3.simplify(inc_val), z3.simplify(z3.Int(iname) + 1)):
            return Verdict(UNKNOWN, prop, target, "growing list", reason="counter does not advance by 1")

        def e_at(jterm):                                       # the append expression with the counter set to j
            return _ev_arr(aexpr, {**params, iname: jterm}, [], z3.BoolVal(True))

        def inv(i, ln, arr):
            j = z3.FreshInt("j")
            return z3.And(0 <= i, i <= n, ln == i,
                          z3.ForAll([j], z3.Implies(z3.And(0 <= j, j < ln), z3.Select(arr, j) == e_at(j))))

        i_s, ln_s = z3.Int(iname + "_s"), z3.Int("len_" + aname + "_s")
        A_s = z3.Array(aname + "_s", z3.IntSort(), z3.IntSort())
        A_body = z3.Store(A_s, ln_s, e_at(i_s))                # a.append(e): store at the current length
        A0 = z3.Array(aname + "0", z3.IntSort(), z3.IntSort())
        vcs = [(z3.And(pre(params), z3.Not(inv(z3.IntVal(0), z3.IntVal(0), A0))), "initiation (needs n >= 0)"),
               (z3.And(inv(i_s, ln_s, A_s), i_s < n, z3.Not(inv(i_s + 1, ln_s + 1, A_body))), "preservation"),
               (z3.And(inv(i_s, ln_s, A_s), z3.Not(i_s < n), z3.Not(post(params, A_s, ln_s))), "postcondition")]
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "growing list", reason=str(u))
    for claim, why in vcs:
        if _solve(claim)[0] != PROVED:
            return Verdict(UNKNOWN, prop, target, "growing list", reason=f"{why} not established")
    return Verdict(PROVED, prop, target, "growing list (append loop, inferred prefix invariant)",
                   reason=f"len({aname}) == {iname} and a[j] == <append expr>[{iname} := j] for j < len")


def verify_growing_set_auto(prop, target, src, post, pre=None) -> Verdict:
    """The SIZE of a set or dict grown in a loop -- s = set(); for x in xs: s.add(x); return len(s).
    Element values are not tracked, but each add changes the size by 0 or 1 and the first add to an
    empty collection by exactly 1, so the final size lies in [0, N] (N the iteration count) and in
    [1, N] for a non-empty unguarded build -- exactly the reachable sizes, so the bound is sound both
    ways. The loop is `for x in <list parameter>` (N = len of the parameter) or `for i in range(n)`
    (N = max(0, n)); the add may be guarded by an `if`. post(params, size) is the claim; pre(params)
    optionally constrains the inputs. UNKNOWN outside this pattern."""
    pre = pre or (lambda P: z3.BoolVal(True))
    try:
        fn = next(n for n in ast.parse(textwrap.dedent(src)).body
                  if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)))
    except StopIteration:
        return Verdict(UNKNOWN, prop, target, "growing set", reason="no function")
    params = [a.arg for a in fn.args.args]
    init = [s for s in fn.body if isinstance(s, ast.Assign) and len(s.targets) == 1
            and isinstance(s.targets[0], ast.Name) and isinstance(s.value, ast.Call)
            and isinstance(s.value.func, ast.Name) and s.value.func.id in ("set", "dict") and not s.value.args]
    loops = [s for s in fn.body if isinstance(s, ast.For)]
    rets = [s for s in fn.body if isinstance(s, ast.Return)]
    if len(init) != 1 or len(loops) != 1 or len(rets) != 1:
        return Verdict(UNKNOWN, prop, target, "growing set", reason="not a single set/dict built in one loop")
    sname, is_dict, loop = init[0].targets[0].id, init[0].value.func.id == "dict", loops[0]

    def is_add(st):                                              # d[k] = v for a dict, s.add(e) for a set
        if is_dict:
            return (isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Subscript)
                    and isinstance(st.targets[0].value, ast.Name) and st.targets[0].value.id == sname)
        return (isinstance(st, ast.Expr) and isinstance(st.value, ast.Call) and isinstance(st.value.func, ast.Attribute)
                and st.value.func.attr == "add" and isinstance(st.value.func.value, ast.Name)
                and st.value.func.value.id == sname)
    # The body may carry extra scalar work (a running accumulator) alongside the add; the size claim is
    # unaffected by it, so locate the single add (direct, or guarded by an if with no else) and require the
    # collection is named nowhere else (a second add or a removal would change the size), then ignore the rest.
    body = loop.body
    direct = [st for st in body if is_add(st)]
    guarded_l = [st for st in body if isinstance(st, ast.If) and not st.orelse
                 and len(st.body) == 1 and is_add(st.body[0])]
    if len(direct) == 1 and not guarded_l:
        guarded, add_stmt = False, direct[0]
    elif len(guarded_l) == 1 and not direct:
        guarded, add_stmt = True, guarded_l[0]
    else:
        return Verdict(UNKNOWN, prop, target, "growing set", reason="loop body is not a single (optionally guarded) add")
    if any(isinstance(n, ast.Name) and n.id == sname            # the collection touched outside the one add:
           for st in body if st is not add_stmt for n in ast.walk(st)):   # its size is no longer bounded by N
        return Verdict(UNKNOWN, prop, target, "growing set", reason="the collection is modified outside the single add")
    rv = rets[0].value
    if not ((isinstance(rv, ast.Name) and rv.id == sname)
            or (isinstance(rv, ast.Call) and isinstance(rv.func, ast.Name) and rv.func.id == "len"
                and len(rv.args) == 1 and isinstance(rv.args[0], ast.Name) and rv.args[0].id == sname)):
        return Verdict(UNKNOWN, prop, target, "growing set", reason="return is not the collection or its length")
    P = {p: z3.Int(p) for p in params}
    it = loop.iter
    extra = z3.BoolVal(True)
    if isinstance(it, ast.Name):                                # for x in <list parameter>: N = its length
        N = z3.Int("len_" + it.id); P["len_" + it.id] = N; extra = N >= 0
    elif (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range"
          and len(it.args) == 1 and isinstance(it.args[0], ast.Name) and it.args[0].id in P):
        n = P[it.args[0].id]; N = z3.If(n >= 0, n, z3.IntVal(0))   # range(n): max(0, n) iterations
    else:
        return Verdict(UNKNOWN, prop, target, "growing set", reason="loop is not over a list parameter or range(n)")
    c = z3.Int("_size")                                          # the final size, ranging over its reachable set
    reachable = (z3.And(c >= 0, c <= N) if guarded
                 else z3.And(c >= 0, c <= N, z3.Implies(N == 0, c == 0), z3.Implies(N >= 1, c >= 1)))
    try:
        claim_false = z3.And(extra, pre(P), reachable, z3.Not(post(P, c)))
    except (z3.Z3Exception, TypeError, KeyError) as u:
        return Verdict(UNKNOWN, prop, target, "growing set", reason=str(u))
    status, model = _solve_corro(claim_false)
    kind = "dict" if is_dict else "set"
    if status == PROVED:
        return Verdict(PROVED, prop, target, f"growing {kind} (size in [0, iterations], reachable-exact)")
    if status == REFUTED:
        return Verdict(REFUTED, prop, target, f"growing {kind}",
                       counterexample=f"a reachable size {model.eval(c, model_completion=True)} violates the property")
    return Verdict(UNKNOWN, prop, target, f"growing {kind}", reason="solver returned unknown")


class _SubElt(ast.NodeTransformer):
    """Rewrite, inside a loop body, `xs[i]` (the iterated array indexed by the loop variable) to the
    element name and `len(xs)` to a bound length name, so the body reads the element and the length as
    plain scalars. `.other` records an `xs[...]` indexed by something other than the loop variable."""
    def __init__(self, arr, idx, elt, lenn):
        self.arr, self.idx, self.elt, self.lenn, self.other = arr, idx, elt, lenn, False

    def visit_Subscript(self, node):
        self.generic_visit(node)
        if isinstance(node.value, ast.Name) and node.value.id == self.arr:
            if isinstance(node.slice, ast.Name) and node.slice.id == self.idx:
                return ast.copy_location(ast.Name(id=self.elt, ctx=ast.Load()), node)
            self.other = True
        return node

    def visit_Call(self, node):
        self.generic_visit(node)
        if (isinstance(node.func, ast.Name) and node.func.id == "len" and len(node.args) == 1
                and isinstance(node.args[0], ast.Name) and node.args[0].id == self.arr):
            return ast.copy_location(ast.Name(id=self.lenn, ctx=ast.Load()), node)
        return node


class _DesugarAug(ast.NodeTransformer):
    """`x op= e` -> `x = x op e`, for a name, subscript, or attribute target. Applied so an accumulator
    loop body (the common `result += x`) reduces to the plain assignment the sequence-loop engine models."""
    def visit_AugAssign(self, node):
        self.generic_visit(node)
        tgt = node.target
        if isinstance(tgt, ast.Name):
            load, store = ast.Name(id=tgt.id, ctx=ast.Load()), ast.Name(id=tgt.id, ctx=ast.Store())
        elif isinstance(tgt, ast.Subscript):
            load = ast.Subscript(value=tgt.value, slice=tgt.slice, ctx=ast.Load())
            store = ast.Subscript(value=tgt.value, slice=tgt.slice, ctx=ast.Store())
        elif isinstance(tgt, ast.Attribute):
            load = ast.Attribute(value=tgt.value, attr=tgt.attr, ctx=ast.Load())
            store = ast.Attribute(value=tgt.value, attr=tgt.attr, ctx=ast.Store())
        else:
            return node
        return ast.copy_location(ast.Assign(targets=[store],
                                            value=ast.BinOp(left=load, op=node.op, right=node.value)), node)


def verify_sequence_loop(prop, target, src, post, pre=None, forall_pre=None, timeout=4000) -> Verdict:
    """Verify a single loop iterating a `list`-annotated parameter, with the elements treated as
    universally-quantified integers so Spacer synthesizes the loop invariant. The loop is `for x in xs`,
    `for i, x in enumerate(xs)`, or `for i in range(len(xs))` reading `xs[i]`; the body is scalar
    assignments and if/else updating accumulators from the element and the index; the function returns a
    scalar. Each element is an arbitrary integer, so a PROVED property holds for every list and a REFUTED
    one fails on a concrete list; `forall_pre(element)` assumes a per-element precondition, and a division
    by zero in the body refutes. `post(P, ret)` and `pre(P)` range over the scalar parameters and the
    length `len_<xs>`. UNKNOWN outside this shape (a non-loop-variable index, a reference to the array
    itself, or a non-scalar body)."""
    pre = pre or (lambda P: z3.BoolVal(True))
    try:
        fn = next(n for n in ast.parse(textwrap.dedent(src)).body
                  if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)))
    except StopIteration:
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason="no function")
    fn = _DesugarAug().visit(fn); ast.fix_missing_locations(fn)                    # result += x -> result = result + x
    listparams = {a.arg for a in fn.args.args if isinstance(a.annotation, ast.Name) and a.annotation.id == "list"}
    if fn.args.vararg is not None:
        listparams.add(fn.args.vararg.arg)                                        # *args is a sequence of elements
    scalars = [a.arg for a in fn.args.args if a.arg not in listparams]
    loops = [s for s in fn.body if isinstance(s, ast.For)]
    init_stmts = [s for s in fn.body if not isinstance(s, (ast.For, ast.Return))]
    rets = [s for s in fn.body if isinstance(s, ast.Return)]
    if len(loops) != 1 or len(rets) != 1 or rets[0].value is None:
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason="not a single for-loop ending in one return")
    loop = loops[0]
    if loop.orelse:
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason="for-else not modeled")
    it, tgt = loop.iter, loop.target
    arrname = elemname = idxname = None
    if isinstance(it, ast.Name) and it.id in listparams and isinstance(tgt, ast.Name):
        arrname, elemname = it.id, tgt.id                                         # for x in xs
    elif (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "enumerate"
          and len(it.args) == 1 and isinstance(it.args[0], ast.Name) and it.args[0].id in listparams
          and isinstance(tgt, ast.Tuple) and len(tgt.elts) == 2 and all(isinstance(e, ast.Name) for e in tgt.elts)):
        arrname, idxname, elemname = it.args[0].id, tgt.elts[0].id, tgt.elts[1].id  # for i, x in enumerate(xs)
    elif (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range"
          and len(it.args) == 1 and isinstance(it.args[0], ast.Call) and isinstance(it.args[0].func, ast.Name)
          and it.args[0].func.id == "len" and len(it.args[0].args) == 1 and isinstance(it.args[0].args[0], ast.Name)
          and it.args[0].args[0].id in listparams and isinstance(tgt, ast.Name)):
        arrname, idxname, elemname = it.args[0].args[0].id, tgt.id, "_elt_" + it.args[0].args[0].id   # for i in range(len(xs))
    else:
        return Verdict(UNKNOWN, prop, target, "sequence loop",
                       reason="loop is not `for x in xs`, enumerate, or range(len(xs)) over a list parameter")
    lenname = "len_" + arrname
    lenc = "_lenc_" + arrname                                                     # body-local name for len(xs)
    sub = _SubElt(arrname, idxname or "", elemname, lenc)
    body = [sub.visit(copy.deepcopy(s)) for s in loop.body]
    ret_node = sub.visit(copy.deepcopy(rets[0].value))
    if sub.other:
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason="body indexes the array off the loop variable")
    if any(isinstance(n, ast.Name) and n.id == arrname for s in body + [ret_node] for n in ast.walk(s)):
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason="body references the array other than its element")
    internal_idx = idxname is None
    idx = idxname or "_seqi"
    pj = sorted(scalars + [lenname])
    pv = {p: z3.Int("p_" + p) for p in pj}
    elt = z3.Int("_elt")
    paramd = lambda vp: {**{p: vp[p] for p in scalars}, lenname: vp[lenname]}
    try:
        ictx = Ctx({}); ictx.traps = []; ictx.pc = z3.BoolVal(True)
        ienv = dict(pv); ienv[idx] = z3.IntVal(0)
        istate = _apply_assigns(init_stmts, ienv, ictx)
        if ictx.traps:
            return Verdict(UNKNOWN, prop, target, "sequence loop", reason="a trap before the loop")
        order = sorted(k for k in istate if k not in pv)                          # the index + accumulators
        cur = {v: z3.Int("s_" + v) for v in order}
        Inv = z3.Function("SeqInv", *([z3.IntSort()] * (len(order) + len(pj))), z3.BoolSort())
        Err = z3.Function("SeqErr", z3.BoolSort())
        args = lambda st: [st[v] for v in order] + [pv[v] for v in pj]
        rules = [(Inv(*args({v: istate[v] for v in order})), [pre(paramd(pv)), pv[lenname] >= 0])]
        sctx = Ctx({}); sctx.traps = []; sctx.pc = z3.BoolVal(True); sctx.divaux = []; sctx.divvars = []
        benv = dict(cur); benv.update(pv); benv[elemname] = elt; benv[lenc] = pv[lenname]
        if not internal_idx:
            benv[idx] = cur[idx]
        after = _apply_assigns(body, benv, sctx)
        nxt = {v: after.get(v, cur[v]) for v in order}; nxt[idx] = cur[idx] + 1
        guard = cur[idx] < pv[lenname]
        body_rel = Inv(*args(cur))
        elem_assume = [forall_pre(elt)] if forall_pre is not None else []
        aux = list(sctx.divaux)
        for t in sctx.traps:                                                     # a body div-by-zero refutes
            rules.append((Err(), [body_rel, guard] + elem_assume + aux + [t]))
        rules.append((Inv(*args(nxt)), [body_rel, guard] + elem_assume + aux))
        rctx = Ctx({}); rctx.traps = []; rctx.pc = z3.BoolVal(True)
        renv = dict(cur); renv.update(pv); renv[lenc] = pv[lenname]
        ret_expr = ev(ret_node, renv, rctx)
        done = z3.Not(guard)
        for t in rctx.traps:
            rules.append((Err(), [body_rel, done, t]))
        rules.append((Err(), [body_rel, done, z3.Not(post(paramd(pv), ret_expr))]))
    except (Unsupported, KeyError, z3.Z3Exception, TypeError, AttributeError) as u:
        return Verdict(UNKNOWN, prop, target, "sequence loop", reason=str(u))
    return _solve_horn(prop, target, "sequence loop", "sequence loop (CHC over universally-quantified elements)",
                       [Inv, Err], [*[cur[v] for v in order], *[pv[v] for v in pj], elt, *sctx.divvars], rules, Err(),
                       on_error=lambda m: "engine timeout (nonlinear?)" if "canceled" in m else f"engine: {m}")


_GEN_UNROLL = 8


def _collect_generator_yields(stmts, env, pc, spec, in_loop=False, tails=None):
    """A generator's yield points as (path_condition, value) pairs, collected symbolically. Handles
    straight-line yields, if/elif/else branching, yield from a finite iterable, assignments outside a
    loop, and a single non-nested range for-loop. A loop whose body has no carried state has each yield as a
    function of a fresh symbolic index; a loop with loop-carried state (an accumulator) is unrolled to a bound,
    threading the accumulator, with the uncovered tail (more iterations than the bound) recorded in `tails` so
    the caller withholds a full PROVED unless the loop is provably within the bound (REFUTED stays sound)."""
    out = []
    for s in stmts:
        if isinstance(s, ast.Expr) and isinstance(s.value, ast.Yield) and s.value.value is not None:
            out.append((pc, ev(s.value.value, env, spec)))
        elif isinstance(s, ast.Expr) and isinstance(s.value, ast.YieldFrom):
            it = ev(s.value.value, env, spec)
            if not isinstance(it, tuple):
                raise Unsupported("yield from a non-finite iterable")
            out.extend((pc, e) for e in it)
        elif isinstance(s, ast.If):
            c = ev_bool(s.test, env, spec)
            out += _collect_generator_yields(s.body, env, z3.And(pc, c), spec, in_loop, tails)
            out += _collect_generator_yields(s.orelse, env, z3.And(pc, z3.Not(c)), spec, in_loop, tails)
        elif isinstance(s, (ast.Assign, ast.AugAssign)) and not in_loop and isinstance(s.targets[0]
                if isinstance(s, ast.Assign) else s.target, ast.Name) \
                and (not isinstance(s, ast.Assign) or len(s.targets) == 1):
            tgt = (s.targets[0] if isinstance(s, ast.Assign) else s.target).id
            rhs = s.value if isinstance(s, ast.Assign) else ast.BinOp(left=ast.Name(id=tgt, ctx=ast.Load()),
                                                                      op=s.op, right=s.value)
            env = dict(env); env[tgt] = ev(rhs, env, spec)
        elif isinstance(s, ast.For) and not in_loop and not s.orelse and isinstance(s.target, ast.Name) \
                and isinstance(s.iter, ast.Call) and isinstance(s.iter.func, ast.Name) \
                and s.iter.func.id == "range":
            a = s.iter.args
            if len(a) == 3 and not (isinstance(a[2], ast.Constant) and a[2].value == 1):
                raise Unsupported("non-unit range step in a generator loop")
            if len(a) not in (1, 2, 3):
                raise Unsupported("range() arity in a generator loop")
            lo = z3.IntVal(0) if len(a) == 1 else ev(a[0], env, spec)
            hi = ev(a[0], env, spec) if len(a) == 1 else ev(a[1], env, spec)
            carried = any(isinstance(n, (ast.Assign, ast.AugAssign)) for st in s.body for n in ast.walk(st))
            if not carried:                                   # each yield is a function of the index alone
                idx = z3.FreshConst(z3.IntSort(), "gi")
                lenv = dict(env); lenv[s.target.id] = idx
                out += _collect_generator_yields(s.body, lenv, z3.And(pc, lo <= idx, idx < hi), spec, in_loop=True)
            else:                                             # loop-carried accumulator: unroll, threading the state
                lenv = dict(env)
                for it in range(_GEN_UNROLL):
                    lenv2 = dict(lenv); lenv2[s.target.id] = lo + z3.IntVal(it)
                    pts, lenv = _unroll_gen_iter(s.body, lenv2, z3.And(pc, lo + z3.IntVal(it) < hi), spec)
                    out += pts                                # each iteration's yields see the accumulator so far
                if tails is not None:
                    tails.append(z3.And(pc, hi - lo > z3.IntVal(_GEN_UNROLL)))   # iterations past the unroll bound
        elif isinstance(s, ast.Pass) or (isinstance(s, ast.Return) and s.value is None):
            continue
        else:
            raise Unsupported("generator statement %s outside the modeled shape" % type(s).__name__)
    return out


def _unroll_gen_iter(stmts, env, guard, spec):
    """One unrolled generator-loop iteration: thread the body's assignments (the accumulator update) through env
    in order while collecting each `yield`'s (guard, value) with the accumulator current at that point. Returns
    (points, post_iteration_env). A guarded update (if/else) merges its branches' accumulators with z3.If."""
    out, env = [], dict(env)
    for s in stmts:
        if isinstance(s, ast.Expr) and isinstance(s.value, ast.Yield) and s.value.value is not None:
            out.append((guard, ev(s.value.value, env, spec)))
        elif isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
            env[s.targets[0].id] = ev(s.value, env, spec)
        elif isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
            env[s.target.id] = ev(ast.BinOp(left=ast.Name(id=s.target.id, ctx=ast.Load()),
                                            op=s.op, right=s.value), env, spec)
        elif isinstance(s, ast.If):
            c = ev_bool(s.test, env, spec)
            tp, te = _unroll_gen_iter(s.body, env, z3.And(guard, c), spec)
            ep, ee = _unroll_gen_iter(s.orelse, env, z3.And(guard, z3.Not(c)), spec)
            out += tp + ep
            for k in set(te) | set(ee):
                tv, ev_ = te.get(k, env.get(k)), ee.get(k, env.get(k))
                if tv is ev_:
                    env[k] = tv
                elif z3.is_expr(tv) and z3.is_expr(ev_):
                    env[k] = z3.If(c, tv, ev_)
                else:
                    raise Unsupported("non-scalar guarded accumulator in a generator loop")
        elif isinstance(s, ast.Pass):
            continue
        else:
            raise Unsupported("generator loop-carried statement %s is outside the unrolled shape" % type(s).__name__)
    return out, env


def verify_generator_loop(prop, target, src, post, pre=None) -> Verdict:
    """A generator's yielded set, summarized symbolically: straight-line yields, if/elif/else branching, yield
    from a finite iterable, and a single range for-loop (each yield a function of the index, or a loop-carried
    accumulator unrolled to a bound). `post(params, value)` must hold for every yielded value. Sound both ways: a
    PROVED holds for every yield, a REFUTED exhibits a reachable yield that fails; an accumulator loop whose tail
    runs past the unroll bound withholds PROVED (UNKNOWN). UNKNOWN for a while-loop or nested loops."""
    pre = pre or (lambda P: z3.BoolVal(True))
    try:
        fn = next(n for n in ast.parse(textwrap.dedent(src)).body
                  if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)))
    except StopIteration:
        return Verdict(UNKNOWN, prop, target, "generator", reason="no function")
    if not any(isinstance(n, (ast.Yield, ast.YieldFrom)) for n in ast.walk(fn)):
        return Verdict(UNKNOWN, prop, target, "generator", reason="not a generator")
    spec = Ctx({}); spec.traps = None; spec.pc = z3.BoolVal(True)
    P = {p.arg: z3.Int(p.arg) for p in fn.args.args}
    body = [s for s in fn.body if not (isinstance(s, ast.Return) and s.value is None)]
    tails = []                                                  # uncovered-tail conditions of an unrolled accumulator loop
    try:
        points = _collect_generator_yields(body, dict(P), z3.BoolVal(True), spec, tails=tails)
        if not points:                                          # a generator that never yields: post holds vacuously
            return Verdict(PROVED, prop, target, "generator (yields nothing)")
        claim_false = z3.Or(*[z3.And(pre(P), pc, z3.Not(post(P, v))) for pc, v in points])
    except (Unsupported, KeyError, z3.Z3Exception, TypeError) as u:
        return Verdict(UNKNOWN, prop, target, "generator", reason=str(u))
    status, model = _solve_corro(claim_false)
    if status == REFUTED:                                       # a concrete reachable yield violates post (sound)
        return Verdict(REFUTED, prop, target, "generator", counterexample="a reachable yield violates the property")
    if status == PROVED:
        if tails and _solve(z3.And(*([pre(P)] + [z3.Or(*tails)])))[0] == REFUTED:   # the loop can exceed the bound
            return Verdict(UNKNOWN, prop, target, "generator",
                           reason="a loop-carried generator yields past the unroll bound; bounded check is inconclusive")
        return Verdict(PROVED, prop, target, "generator (every yielded value)")
    return Verdict(UNKNOWN, prop, target, "generator", reason="solver returned unknown")


def verify_map_comprehension(prop, target, src, post) -> Verdict:
    """A list comprehension over a list parameter. Unfiltered, [e(x) for x in xs] is the exact map
    result[j] == e(xs[j]) with len(result) == len(xs), sound both ways. Filtered, [x for x in xs if
    p(x)] is a sound over-approximation: len(result) <= len(xs) and every element satisfies p, so a
    property following from p is PROVED (else UNKNOWN). post(params, result_array, result_len)."""
    fn = _fndef(src)
    if not (len(fn.body) == 1 and isinstance(fn.body[0], ast.Return)
            and isinstance(fn.body[0].value, ast.ListComp)):
        return Verdict(UNKNOWN, prop, target, "map comprehension", reason="not a single list-comprehension return")
    comp = fn.body[0].value
    if len(comp.generators) != 1 or getattr(comp.generators[0], "is_async", 0):
        return Verdict(UNKNOWN, prop, target, "map comprehension", reason="needs a single generator")
    gen = comp.generators[0]
    if not (isinstance(gen.target, ast.Name) and isinstance(gen.iter, ast.Name)):
        return Verdict(UNKNOWN, prop, target, "map comprehension", reason="iterate a list parameter by name")
    var, source = gen.target.id, gen.iter.id
    pnames = [a.arg for a in fn.args.args]
    if source not in pnames:
        return Verdict(UNKNOWN, prop, target, "map comprehension", reason="source is not a parameter")
    S, Sn = z3.Array(source, z3.IntSort(), z3.IntSort()), z3.Int("len_" + source)
    P = {source: S, "len_" + source: Sn}
    for p in pnames:
        if p != source:
            P[p] = z3.Int(p)
    if gen.ifs:                                                     # [x for x in xs if p(x)]: over-approximation
        if not (isinstance(comp.elt, ast.Name) and comp.elt.id == var):
            return Verdict(UNKNOWN, prop, target, "map comprehension", reason="filtered map with a non-identity element")
        if len(gen.ifs) != 1:
            return Verdict(UNKNOWN, prop, target, "map comprehension", reason="multiple filter clauses")
        R, Rn, jf = z3.Array("_fc", z3.IntSort(), z3.IntSort()), z3.Int("_fcn"), z3.Int("_fcj")
        try:
            kept = _ev_arr(gen.ifs[0], {**P, var: z3.Select(R, jf)}, [], z3.BoolVal(True))   # p(result[j])
            facts = [Sn >= 0, Rn >= 0, Rn <= Sn,                    # a subsequence, no longer than the source
                     z3.ForAll([jf], z3.Implies(z3.And(0 <= jf, jf < Rn), kept))]   # every element passed the filter
            claim = z3.And(*facts, z3.Not(post(P, R, Rn)))
        except (z3.Z3Exception, Unsupported, TypeError) as u:
            return Verdict(UNKNOWN, prop, target, "map comprehension", reason=str(u))
        return Verdict(PROVED if _solve(claim)[0] == PROVED else UNKNOWN, prop, target,
                       "map comprehension (filtered, over-approximation)",
                       reason=f"len(result) <= len({source}) and every element satisfies the filter")
    jv = z3.Int("_mc")
    try:
        elem = _ev_arr(comp.elt, {**P, var: z3.Select(S, jv)}, [], z3.BoolVal(True))   # e(xs[j])
        claim = z3.And(Sn >= 0, z3.Not(post(P, z3.Lambda([jv], elem), Sn)))            # result[j] == e(xs[j])
    except (z3.Z3Exception, Unsupported, TypeError) as u:
        return Verdict(UNKNOWN, prop, target, "map comprehension", reason=str(u))
    status, _ = _solve(claim)
    if status == PROVED:
        return Verdict(PROVED, prop, target, "map comprehension (exact map over a list)",
                       reason=f"result[j] == <elt>[{var} := {source}[j]] and len(result) == len({source})")
    if status == REFUTED:
        return Verdict(REFUTED, prop, target, "map comprehension")
    return Verdict(UNKNOWN, prop, target, "map comprehension", reason="solver returned unknown")


def verify_all_any(prop, target, src, post) -> Verdict:
    """all(p(x) for x in xs) / any(p(x) for x in xs) over a list parameter, modeled as exactly the
    universal / existential quantifier it is: the boolean result is forall (resp. exists) j in
    [0, len(xs)) of p(xs[j]). Sound both ways. post(params, result) is the claim, with params[xs] /
    params['len_'+xs] the source. UNKNOWN outside a single unfiltered generator over a list parameter."""
    fn = _fndef(src)
    if not (len(fn.body) == 1 and isinstance(fn.body[0], ast.Return)
            and isinstance(fn.body[0].value, ast.Call)):
        return Verdict(UNKNOWN, prop, target, "all/any", reason="not a single all(...) / any(...) return")
    call = fn.body[0].value
    if not (isinstance(call.func, ast.Name) and call.func.id in ("all", "any") and len(call.args) == 1
            and isinstance(call.args[0], (ast.GeneratorExp, ast.ListComp))):
        return Verdict(UNKNOWN, prop, target, "all/any", reason="not all/any of a generator over a list")
    arg = call.args[0]
    if len(arg.generators) != 1 or arg.generators[0].ifs or getattr(arg.generators[0], "is_async", 0):
        return Verdict(UNKNOWN, prop, target, "all/any", reason="needs a single unfiltered generator")
    gen = arg.generators[0]
    if not (isinstance(gen.target, ast.Name) and isinstance(gen.iter, ast.Name)):
        return Verdict(UNKNOWN, prop, target, "all/any", reason="iterate a list parameter by name")
    var, source = gen.target.id, gen.iter.id
    pnames = [a.arg for a in fn.args.args]
    if source not in pnames:
        return Verdict(UNKNOWN, prop, target, "all/any", reason="source is not a parameter")
    S, Sn = z3.Array(source, z3.IntSort(), z3.IntSort()), z3.Int("len_" + source)
    P = {source: S, "len_" + source: Sn}
    for p in pnames:
        if p != source:
            P[p] = z3.Int(p)
    j = z3.Int("_aa")
    try:
        pred = _as_bool(_ev_arr(arg.elt, {**P, var: z3.Select(S, j)}, [], z3.BoolVal(True)))   # p(xs[j])
        rng = z3.And(0 <= j, j < Sn)
        result = z3.ForAll([j], z3.Implies(rng, pred)) if call.func.id == "all" else z3.Exists([j], z3.And(rng, pred))
        claim = z3.And(Sn >= 0, z3.Not(post(P, result)))
    except (z3.Z3Exception, Unsupported, TypeError) as u:
        return Verdict(UNKNOWN, prop, target, "all/any", reason=str(u))
    status, _ = _solve(claim)
    if status == PROVED:
        return Verdict(PROVED, prop, target, f"{call.func.id} over a list (exact quantifier)",
                       reason=f"result == {call.func.id} of p({source}[j]) over j in [0, len({source}))")
    if status == REFUTED:
        return Verdict(REFUTED, prop, target, f"{call.func.id} over a list")
    return Verdict(UNKNOWN, prop, target, "all/any", reason="solver returned unknown")


_FINITE_ITER_CALLS = {"enumerate", "reversed", "sorted", "list", "tuple", "set", "frozenset"}
_FINITE_ITER_METHODS = {"items", "keys", "values"}
_GROW_METHODS = {"append", "extend", "insert", "pop", "remove", "clear", "add",
                 "update", "discard", "popitem", "setdefault"}


def _iter_roots(it):
    """The container names a for-loop's iterable reads, or None if the iterable is
    not a finite container expression. range() is handled earlier by desugaring;
    here we cover names, the finite-iterator builtins, .items()/.keys()/.values(),
    zip of them, and literal containers (which are finite by construction)."""
    if isinstance(it, ast.Name):
        return {it.id}
    if isinstance(it, (ast.List, ast.Tuple, ast.Set, ast.Dict, ast.Constant)):
        return set()                                          # literal: finite, no live root
    if isinstance(it, ast.Call) and isinstance(it.func, ast.Name):
        if it.func.id == "range":
            return None                                       # range stays a counted while loop
        if it.func.id == "zip":
            roots = set()
            for a in it.args:
                r = _iter_roots(a)
                if r is None:
                    return None
                roots |= r
            return roots
        if it.func.id in _FINITE_ITER_CALLS and it.args:
            return _iter_roots(it.args[0])
    if (isinstance(it, ast.Call) and isinstance(it.func, ast.Attribute)
            and it.func.attr in _FINITE_ITER_METHODS and isinstance(it.func.value, ast.Name)):
        return {it.func.value.id}                             # d.items() etc.
    return None


_PURE_CALLS = {"len", "sum", "min", "max", "any", "all", "sorted", "reversed", "abs",
               "enumerate", "zip", "range", "int", "float", "str", "bool", "repr", "id",
               "type", "print", "isinstance", "ord", "chr", "round", "divmod", "pow"}


def _body_mutates(body, roots):
    """True if the body may change the length of the iterated container -- unsound for iteration
    counting, since CPython walks the live object. Growth reaches it directly (xs.append), via an
    alias (ys = xs), via heap escape (o.f = xs), or via a callee it is passed to. Tracks aliases and
    treats escape as mutation: over-approximate, never missing a grow."""
    mod = ast.Module(body=list(body), type_ignores=[])

    def _may_alias(node, aliases):
        # an expression that can evaluate to one of the alias OBJECTS: a bare copy (ys = xs) or a
        # choice among aliases (xs if c else zs / xs or []). A slice, concatenation, index, or call
        # builds a fresh object or a non-container value, so it does not alias the container.
        if isinstance(node, ast.Name):
            return node.id in aliases
        if isinstance(node, ast.IfExp):
            return _may_alias(node.body, aliases) or _may_alias(node.orelse, aliases)
        if isinstance(node, ast.BoolOp):
            return any(_may_alias(v, aliases) for v in node.values)
        return False

    aliases = set(roots)                                      # names that may refer to a root container
    changed = True
    while changed:                                            # a name copied from an alias may alias it too
        changed = False
        for n in ast.walk(mod):
            if isinstance(n, ast.Assign) and _may_alias(n.value, aliases):
                for tg in n.targets:
                    if isinstance(tg, ast.Name) and tg.id not in aliases:
                        aliases.add(tg.id); changed = True
    for n in ast.walk(mod):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr in _GROW_METHODS and isinstance(n.func.value, ast.Name)
                and n.func.value.id in aliases):
            return True                                       # xs.append(...) / ys.pop() where ys aliases a root
        if isinstance(n, ast.Call):                           # a root passed to a callee that may grow it
            pure = isinstance(n.func, ast.Name) and n.func.id in _PURE_CALLS
            if not pure and any(isinstance(a, ast.Name) and a.id in aliases
                                for a in n.args):
                return True                                   # grow(xs, ...) -- callee not analyzed here
        if isinstance(n, ast.Assign) and _may_alias(n.value, aliases):
            for tg in n.targets:                              # storing the container into the heap (o.lst = xs,
                if isinstance(tg, (ast.Attribute, ast.Subscript)):   # d[k] = xs) escapes precise tracking: a later
                    return True                                      # grow through that location cannot be ruled out
        if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
            tgts = n.targets if isinstance(n, ast.Assign) else [n.target]
            for tg in tgts:
                if isinstance(tg, ast.Name) and tg.id in roots:
                    return True                               # rebinding the iterated name (the alias copy
                #                                               `ys = xs` is harmless: the iterator holds the object)
                if (isinstance(tg, ast.Subscript) and isinstance(tg.value, ast.Name)
                        and tg.value.id in aliases):
                    return True                               # xs[i] = ...
        if isinstance(n, ast.Delete):
            for tg in n.targets:
                base = tg.value if isinstance(tg, ast.Subscript) else tg
                if isinstance(base, ast.Name) and base.id in aliases:
                    return True                               # del xs[i]  /  del xs
    return False


def _terminate_for_container(prop, target, src):
    """Termination for a single `for <var> in <finite container>` loop. Such a loop
    runs once per element of a finite iterable, so it always halts unless the body
    grows the very container it iterates. Returns a Verdict, or None when the
    function is not a single for-over-container loop (so the caller falls through)."""
    try:                                                      # raw parse: the for-loop survives even
        fn = next(n for n in ast.parse(textwrap.dedent(src)).body  # when desugaring would unroll a
                  if isinstance(n, ast.FunctionDef))          # constant iterable, and matches CPython
    except StopIteration:                                     # source for the mutation check below.
        return None
    loops = [s for s in fn.body if isinstance(s, (ast.For, ast.While))]
    if len(loops) != 1 or not isinstance(loops[0], ast.For):
        return None                                           # not a single top-level for-loop
    loop = loops[0]
    if any(isinstance(n, (ast.For, ast.While)) for n in ast.walk(
            ast.Module(body=loop.body, type_ignores=[]))):
        return None                                           # nested loop: leave to the ranking path
    roots = _iter_roots(loop.iter)
    if roots is None:
        return None
    if _body_mutates(loop.body, roots):
        return Verdict(UNKNOWN, prop, target, "ranking function",
                       reason="loop may modify the container it iterates")
    where = " and ".join(sorted(roots)) if roots else "a literal sequence"
    return Verdict(PROVED, prop, target, "ranking function (finite iteration)",
                   reason=f"for-loop over finite container ({where}): one step per element")


def _recurrence_candidates(sym, order, guard):
    """Candidate recurrence sets (half-spaces over the loop variables) for a non-termination certificate:
    the loop guard itself (already inductive for a monotone-away counter), each variable bounded one way
    (v >= c / v <= c), and each pair difference bounded (v - w >= c / v - w <= c), for small offsets c. Each
    is a guess; z3 discharges the recurrence conditions, so an uncertified guess is discarded."""
    cands = [("guard", guard)]
    for v in order:
        for c in (0, 1, -1, 2, -2):
            cands.append((f"{v} >= {c}", sym[v] >= c))
            cands.append((f"{v} <= {c}", sym[v] <= c))
    for v in order:
        for w in order:
            if v == w:
                continue
            for c in (0, 1, -1):
                cands.append((f"{v} - {w} >= {c}", sym[v] - sym[w] >= c))
    return cands


def verify_nontermination(prop, target, src, repo=None, pre=None) -> Verdict:
    """Prove a single while-loop function diverges from some reachable input -- a definite non-termination bug,
    reported as REFUTED with the diverging witness. A recurrence set R (a half-space over the loop variables)
    is synthesized and every condition discharged with z3: R implies the loop guard, R is closed under the body,
    the body does not trap on R, and R is reachable (an input satisfying `pre` whose trap-free pre-loop
    initialization lands in R). UNKNOWN when no recurrence set is found; never PROVED (the dual of
    verify_termination, which asks whether every input halts)."""
    src = _lower_list_lengths(src)
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None:
        return Verdict(UNKNOWN, prop, target, "recurrence set", reason="not a single while-loop")
    pre = pre or (lambda S: z3.BoolVal(True))
    ctx = Ctx(repo or {})
    try:
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        init_state = _apply_assigns(init, {a: z3.Int(a) for a in args}, ctx)
        init_traps = list(ctx.traps)
        order = args + sorted(set(init_state) - set(args))
        sym = {v: z3.Int(v + "_r") for v in order}
        guard = ev_bool(loop.test, sym, ctx)
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        body = _apply_assigns(loop.body, sym, ctx)
        body_traps = list(ctx.traps)
        ctx.traps = None
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "recurrence set", reason=str(u))
    if not all(z3.is_expr(body.get(v)) and z3.is_int(body[v]) for v in order):
        return Verdict(UNKNOWN, prop, target, "recurrence set",
                       reason="loop body is not a self-contained integer transition")
    subst_body = lambda R: z3.substitute(R, *[(sym[v], body[v]) for v in order])
    entry = [(sym[v], init_state.get(v, z3.Int(v))) for v in order]     # the loop-entry state over the parameters
    pre_args = pre({a: z3.Int(a) for a in args})
    body_trap = z3.Or(*body_traps) if body_traps else z3.BoolVal(False)
    init_trap = z3.Or(*init_traps) if init_traps else z3.BoolVal(False)
    z3args = {a: z3.Int(a) for a in args}
    for label, R in _recurrence_candidates(sym, order, guard):
        try:
            if _solve_corro(z3.And(R, z3.Not(guard)))[0] != PROVED:            # R => guard (the loop continues)
                continue
            if _solve_corro(z3.And(R, z3.Not(subst_body(R))))[0] != PROVED:    # R => R[body] (closed under the body)
                continue
            if _solve_corro(z3.And(R, body_trap))[0] != PROVED:                # R => not trap (the body completes)
                continue
            reach = z3.And(pre_args, z3.Not(init_trap), z3.substitute(R, *entry))   # reachable, trap-free entry into R
            st, model = _solve(reach)
        except z3.Z3Exception:
            continue
        if st == REFUTED and model is not None:                                # SAT: a concrete diverging input
            model = minimize_witness(reach, z3args, args) or model              # the smallest diverging input
            cex, inputs = _model_cex(model, z3args, args)
            try:
                guard_src = ast.unparse(loop.test)
            except Exception:
                guard_src = "<loop guard>"
            # the divergence certificate, presented in place of an unbounded diverging trace: the preserved
            # loop guard and the invariant region R closed under the body -- why no variant can decrease.
            cert = ("non-termination certificate:\n"
                    f"  recurrence set R:  {label}\n"
                    f"  preserved guard:   while {guard_src}:   (R => the guard holds, so the loop never exits)\n"
                    "  closed under body: every iteration maps R into R, so no variant decreases\n"
                    f"  reachable:         the witness state satisfies R, so its run is infinite")
            return Verdict(REFUTED, prop, target, "recurrence set",
                           counterexample=cex or None, counterexample_inputs=inputs or None,
                           reason=f"provably non-terminating: the loop diverges on the recurrence set {label}",
                           trace=cert)
    return Verdict(UNKNOWN, prop, target, "recurrence set",
                   reason="no recurrence set found (non-termination not shown)")


def _lex_ok(measures, nxt):
    """The lexicographic-decrease condition for an ordered tuple of measures (each a (label, term) pair): the
    first component that changes must strictly decrease. Built innermost-first, so at each level the component
    strictly decreases, or it stays equal and the remaining suffix decreases; the innermost has no fallback,
    so it must strictly decrease when every higher component is unchanged."""
    cond = z3.BoolVal(False)
    for _lbl, r in reversed(measures):
        cond = z3.Or(nxt(r) < r, z3.And(nxt(r) == r, cond))
    return cond


def _loop_state(ctx, args, init, loop, suffix):
    """The shared single-loop preamble (run inside the caller's Unsupported guard, on the caller's Ctx): an
    empty trap channel and true path condition, the initial state from the pre-loop assignments, the variable
    order (parameters then the sorted assigned locals), the loop-head symbol map (each var an Int suffixed
    with `suffix`), and the symbolic guard and one-iteration body. Returns (init_state, order, sym, guard,
    body); the post-body trap policy stays with the caller."""
    ctx.traps = []; ctx.pc = z3.BoolVal(True)
    init_state = _apply_assigns(init, {a: z3.Int(a) for a in args}, ctx)
    order = args + sorted(set(init_state) - set(args))
    sym = {v: z3.Int(v + suffix) for v in order}
    guard = ev_bool(loop.test, sym, ctx)
    body = _apply_assigns(loop.body, sym, ctx)
    return init_state, order, sym, guard, body


def verify_termination(prop, target, src, repo=None, inv=None) -> Verdict:
    """Prove a counted loop halts. Candidates over program variables (values, differences, and sums) are tried
    first as a single linear ranking function, then as a lexicographic tuple (a pair, then a triple) for a
    multiphase loop whose progress lives in no single measure. `inv`, if given, is an assumed loop-head context
    under which the ranking conditions are discharged (e.g. to bound a component)."""
    src = _lower_list_lengths(src)                            # a list grown by append -> an integer length
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None:
        forv = _terminate_for_container(prop, target, src)    # for x in <finite container>
        if forv is not None:
            return forv
        return Verdict(UNKNOWN, prop, target, "ranking function", reason="no loop")
    ctx = Ctx(repo or {})
    try:
        init_state, order, sym, guard, body = _loop_state(ctx, args, init, loop, "_r")
        ctx.traps = None                                     # division is allowed: the body's floor-div
        #                                                      term feeds the ranking, so data-dependent
        #                                                      loops (e.g. halving) can be proved to halt.
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "ranking function", reason=str(u))
    cond = z3.And(inv(sym), guard) if inv else guard
    nxt = lambda r: z3.substitute(r, *[(sym[v], body[v]) for v in order])
    cands = []
    for v in order:
        cands.append((v, sym[v]))
        cands.append(("-" + v, -sym[v]))
    for v in order:
        for w in order:
            if v != w:
                cands.append((f"{v}-{w}", sym[v] - sym[w]))
    for i, v in enumerate(order):                              # sums (octagon-style)
        for w in order[i + 1:]:
            cands.append((f"{v}+{w}", sym[v] + sym[w]))
    for i, v in enumerate(order):                              # products (nonlinear, beyond the
        for w in order[i:]:                                    # linear/lexicographic family)
            cands.append((f"{v}*{w}", sym[v] * sym[w]))
    bounded = [(lbl, r) for lbl, r in cands                    # provably bounded below
               if _solve(z3.And(cond, r < 0))[0] == PROVED]
    for lbl, r in bounded:                                     # single linear ranking
        if _solve_corro(z3.And(cond, nxt(r) > r - 1))[0] == PROVED:  # cond => r' <= r - 1
            return Verdict(PROVED, prop, target, "ranking function",
                           reason=f"ranking function: {lbl}")
    for l1, r1 in bounded:                                     # lexicographic pair
        for l2, r2 in bounded:
            if l1 == l2:
                continue
            if _solve(z3.And(cond, z3.Not(_lex_ok([(l1, r1), (l2, r2)], nxt))))[0] == PROVED:
                return Verdict(PROVED, prop, target, "ranking function (lexicographic)",
                               reason=f"lexicographic ranking: ({l1}, {l2})")
    pool = bounded[:8]                                          # lexicographic triple (capped pool): a three-phase
    for i1 in range(len(pool)):                                # loop whose progress lives in no single measure
        for i2 in range(len(pool)):                            # or pair (e.g. a flattened triple-nested counter)
            if i2 == i1:
                continue
            for i3 in range(len(pool)):
                if i3 in (i1, i2):
                    continue
                combo = [pool[i1], pool[i2], pool[i3]]
                if _solve(z3.And(cond, z3.Not(_lex_ok(combo, nxt))))[0] == PROVED:
                    return Verdict(PROVED, prop, target, "ranking function (lexicographic)",
                                   reason="lexicographic ranking: (%s)" % ", ".join(l for l, _ in combo))
    # final fallback: synthesize a general linear ranking function with arbitrary integer coefficients by
    # CEGIS, covering measures outside the unit-coefficient template and lexicographic families (e.g. a
    # weighted sum 3*x + y whose components are individually unbounded under the guard but whose combination
    # is bounded and decreasing). Deterministic (rlimit, bounded refinement loop); UNKNOWN if it cannot fit.
    synth = verify_ranking_synth(prop, target, src, repo)
    if synth.status == PROVED:
        return synth
    return Verdict(UNKNOWN, prop, target, "ranking function",
                   reason="no linear, lexicographic, or synthesized ranking function found among candidates")


def verify_iteration_bound(prop, target, src, repo=None) -> Verdict:
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None:
        return Verdict(UNKNOWN, prop, target, "cost", reason="not a single-loop function")
    ctx = Ctx(repo or {})
    try:
        init_state, order, sym, guard, body = _loop_state(ctx, args, init, loop, "_c")
        if ctx.traps:
            return Verdict(UNKNOWN, prop, target, "cost", reason="division in loop")
        ctx.traps = None
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "cost", reason=str(u))
    cands = []
    for v in order:
        cands.append((v, sym[v])); cands.append(("-" + v, -sym[v]))
    for v in order:
        for w in order:
            if v != w:
                cands.append((f"{v}-{w}", sym[v] - sym[w]))
    nxt = lambda r: z3.substitute(r, *[(sym[v], body[v]) for v in order])
    for lbl, r in cands:
        if (_solve(z3.And(guard, r < 0))[0] == PROVED
                and _solve(z3.And(guard, nxt(r) > r - 1))[0] == PROVED):
            bound = z3.simplify(z3.substitute(r, *[(sym[v], init_state[v]) for v in order]))
            return Verdict(PROVED, prop, target, "cost (ranking bound)",
                           reason=f"at most {bound} iterations (ranking {lbl})")
    return Verdict(UNKNOWN, prop, target, "cost", reason="no linear ranking bound found")


def export_grounding(repo, props) -> dict:
    orch = Orchestrator(repo, props)
    verds = orch.verify(label="grounding")
    facts = [{"property": p.name, "target": p.target, "status": v.status,
              "technique": v.technique, "reason": v.reason, "counterexample": v.counterexample,
              "certificate": v.certificate}
             for p, v in zip(props, verds)]
    return {"functions": sorted(repo),
            "call_graph": {f: sorted(orch._callees(f)) for f in repo},
            "ir_signatures": {f: orch._hash(f) for f in repo},
            "verified_properties": facts}


def recheck_grounding(bundle, repo) -> dict:
    """Re-validate an exported grounding bundle against the current code WITHOUT a live solver, so
    the CI gate is a deterministic re-check of a saved certificate rather than a fresh solver race
    that could time out into UNKNOWN and flip the verdict. A proven fact stands only if every IR
    signature in the bundle still matches the current code (nothing drifted) and each recorded PROVED
    carries a corroboration certificate. Returns counts; signatures_match is the gate."""
    orch = Orchestrator(repo, [])
    current = {f: orch._hash(f) for f in repo}
    signatures_match = bundle.get("ir_signatures") == current
    facts = bundle.get("verified_properties", [])
    proved = [f for f in facts if f["status"] == PROVED]
    certified = [f for f in proved if f.get("certificate")]
    rechecked = len(facts) if signatures_match and len(certified) == len(proved) else 0
    return {"signatures_match": signatures_match, "total": len(facts),
            "proved": len(proved), "certified": len(certified), "rechecked": rechecked}


def verify_modular(prop, target, src, pre, post, contracts) -> Verdict:
    fn = _fndef(src)
    args = [a.arg for a in fn.args.args]
    z3a = {a: z3.Int(a) for a in args}
    paths = []                                          # (pc, retval, assumes, obligs)
    fresh = [0]

    def newr():
        fresh[0] += 1; return z3.Int(f"_call{fresh[0]}")

    def E(node, env, asm, obl):
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return z3.IntVal(node.value)
        if isinstance(node, ast.Name):
            if node.id not in env: raise Unsupported(f"free var {node.id}")
            return env[node.id]
        if isinstance(node, ast.BinOp):
            op = type(node.op)
            if op not in _BINOPS or op in (ast.FloorDiv, ast.Mod): raise Unsupported("modular binop")
            return _BINOPS[op](E(node.left, env, asm, obl), E(node.right, env, asm, obl))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -E(node.operand, env, asm, obl)
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            return _CMP[type(node.ops[0])](E(node.left, env, asm, obl), E(node.comparators[0], env, asm, obl))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in contracts:
            gpre, gpost = contracts[node.func.id]
            gargs = [E(a, env, asm, obl) for a in node.args]
            r = newr()
            obl.append(gpre(gargs))                     # caller must establish callee pre
            asm.append(gpost(gargs, r))                 # caller may assume callee post
            return r
        raise Unsupported(f"modular expr {type(node).__name__}")

    def walk(stmts, env, pc, asm, obl):
        falls = [(dict(env), pc, list(asm), list(obl))]
        for s in stmts:
            nxt = []
            for e, p, a, o in falls:
                if isinstance(s, ast.Return):
                    paths.append((p, E(s.value, e, a, o), list(a), list(o)))
                elif isinstance(s, ast.Assign):
                    e2 = dict(e); e2[s.targets[0].id] = E(s.value, e2, a, o)
                    nxt.append((e2, p, a, o))
                elif isinstance(s, ast.If):
                    c = _as_bool(E(s.test, e, a, o))
                    nxt += walk(s.body, e, z3.And(p, c), a, o)
                    nxt += walk(s.orelse, e, z3.And(p, z3.Not(c)), a, o)
                else:
                    raise Unsupported(f"modular statement {type(s).__name__}")
            falls = nxt
        return falls

    try:
        walk(fn.body, z3a, z3.BoolVal(True), [], [])
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "modular contracts", reason=str(u))
    fpre = pre(z3a)
    post_bad = z3.Or(*[z3.And(fpre, pc, *asm, z3.Not(post(z3a, rv))) for pc, rv, asm, obl in paths])
    oblig_bad = z3.Or(*[z3.And(fpre, pc, *asm[:i], z3.Not(o))
                        for pc, rv, asm, obl in paths for i, o in enumerate(obl)]) \
        if any(p[3] for p in paths) else z3.BoolVal(False)
    s1, m = _solve_corro(post_bad)
    if s1 == REFUTED:
        return Verdict(REFUTED, prop, target, "modular contracts", reason="postcondition fails")
    if s1 == UNKNOWN:
        return Verdict(UNKNOWN, prop, target, "modular contracts", reason="solver unknown (post)")
    s2, _ = _solve_corro(oblig_bad)
    if s2 == REFUTED:
        return Verdict(REFUTED, prop, target, "modular contracts", reason="a callee precondition is not met")
    if s2 == UNKNOWN:
        return Verdict(UNKNOWN, prop, target, "modular contracts", reason="solver unknown (precondition)")
    return Verdict(PROVED, prop, target, "modular contracts (assume-guarantee)",
                   reason="post holds and every callee precondition is discharged")


def verify_program(prop, target, repo, tgt, pre, post, timeout=4000) -> Verdict:
    """Whole-program (mutual-recursion) CHC, with a concrete-refutation fallback on UNKNOWN."""
    v = _verify_program_core(prop, target, repo, tgt, pre, post, timeout)
    if v.status == UNKNOWN and tgt in repo:
        try:
            args = [a.arg for a in _parse(repo[tgt]).body[0].args.args]
        except Exception:
            return v
        return _chc_fallback(v, repo[tgt], pre, post, args, repo)
    return v


def _verify_program_core(prop, target, repo, tgt, pre, post, timeout=4000) -> Verdict:
    gated = _definite_assignment_guard(prop, target, "whole-program CHC", list(repo.values()))
    if gated is not None:
        return gated
    fns = {name: _fndef(src) for name, src in repo.items()}
    if tgt not in fns:
        return Verdict(UNKNOWN, prop, target, "whole-program CHC", reason="unknown target")
    if any(isinstance(n, (ast.While, ast.For)) for fn in fns.values() for n in ast.walk(fn)):
        return Verdict(UNKNOWN, prop, target, "whole-program CHC", reason="loops out of scope")
    params = {name: [a.arg for a in fn.args.args] for name, fn in fns.items()}
    F = {name: z3.Function(name + "_rel", *([z3.IntSort()] * (len(params[name]) + 1)), z3.BoolSort())
         for name in fns}
    Err = z3.Function("ErrProg", z3.BoolSort())
    allvars = []
    ctr = [0]

    def fresh():
        ctr[0] += 1; v = z3.Int(f"_w{ctr[0]}"); allvars.append(v); return v

    def E(node, env, sub):
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return z3.IntVal(node.value)
        if isinstance(node, ast.Name):
            if node.id not in env: raise Unsupported(f"free var {node.id}")
            return env[node.id]
        if isinstance(node, ast.BinOp):
            op = type(node.op)
            if op in (ast.Add, ast.Sub, ast.Mult):
                return _BINOPS[op](E(node.left, env, sub), E(node.right, env, sub))
            if op in (ast.FloorDiv, ast.Mod):
                # division by a nonzero integer constant is linear and cannot trap, so it
                # is admitted in-encoding; a non-constant divisor would need interprocedural
                # trap propagation across summaries and stays out of scope here.
                if isinstance(node.right, ast.Constant) and isinstance(node.right.value, int) \
                        and node.right.value != 0:
                    l = E(node.left, env, sub); k = node.right.value; q = fresh()
                    if k > 0:
                        sub.append(z3.And(k * q <= l, l < k * q + k))
                    else:
                        sub.append(z3.And(k * q >= l, l > k * q + k))
                    return q if op is ast.FloorDiv else (l - k * q)
                raise Unsupported("whole-program division by a non-constant divisor")
            raise Unsupported("binop")
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -E(node.operand, env, sub)
        if isinstance(node, ast.IfExp):
            return z3.If(_as_bool(E(node.test, env, sub)), E(node.body, env, sub), E(node.orelse, env, sub))
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            return _CMP[type(node.ops[0])](E(node.left, env, sub), E(node.comparators[0], env, sub))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in fns:
            g = node.func.id
            at = [E(a, env, sub) for a in node.args]
            r = fresh(); sub.append(F[g](*at, r)); return r
        raise Unsupported(f"expr {type(node).__name__}")

    def returns(stmts, pc):
        rs = []
        for idx, s in enumerate(stmts):
            if isinstance(s, ast.Return):
                rs.append((pc, s.value)); return rs, None
            if isinstance(s, ast.If):
                sub = []; c = _as_bool(E(s.test, cur_env[0], sub))
                if sub: raise Unsupported("call in condition")
                tr, tf = returns(s.body, z3.And(pc, c))
                er, ef = returns(s.orelse, z3.And(pc, z3.Not(c)))
                rs += tr + er
                falls = [f for f in (tf, ef) if f is not None]
                if not falls:
                    return rs, None
                rest, restf = returns(stmts[idx + 1:], falls[0] if len(falls) == 1 else z3.Or(*falls))
                return rs + rest, restf
            raise Unsupported(f"statement {type(s).__name__}")
        return rs, pc

    cur_env = [None]
    rules = []
    try:
        for name, fn in fns.items():
            pv = {p: z3.Int(f"{name}_{p}") for p in params[name]}
            allvars.extend(pv.values())
            cur_env[0] = pv
            rpaths, _ = returns(fn.body, z3.BoolVal(True))
            for pc, expr in rpaths:
                sub = []; term = E(expr, pv, sub)
                rules.append((F[name](*[pv[p] for p in params[name]], term), [pc] + sub))
        tv = {p: z3.Int(f"q_{p}") for p in params[tgt]}
        allvars.extend(tv.values())
        rr = fresh()
        rules.append((Err(), [pre(tv), F[tgt](*[tv[p] for p in params[tgt]], rr), z3.Not(post(tv, rr))]))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "whole-program CHC", reason=str(u))
    return _solve_horn(prop, target, "whole-program CHC", "whole-program CHC (mutual recursion)",
                       list(F.values()) + [Err], allvars, rules, Err(),
                       on_error=lambda m: "engine timeout (nonlinear?)" if "canceled" in m else f"engine: {m}")


def verify_program_loops(prop, target, repo, tgt, pre, post, timeout=4000) -> Verdict:
    """Interprocedural CHC over functions with loops, with a concrete-refutation fallback on UNKNOWN."""
    v = _verify_program_loops_core(prop, target, repo, tgt, pre, post, timeout)
    if v.status == UNKNOWN and tgt in repo:
        try:
            args = [a.arg for a in _parse(repo[tgt]).body[0].args.args]
        except Exception:
            return v
        return _chc_fallback(v, repo[tgt], pre, post, args, repo)
    return v


def _verify_program_loops_core(prop, target, repo, tgt, pre, post, timeout=4000) -> Verdict:
    gated = _definite_assignment_guard(prop, target, "interprocedural CHC", list(repo.values()))
    if gated is not None:
        return gated
    fns = {name: _fndef(src) for name, src in repo.items()}
    if tgt not in fns:
        return Verdict(UNKNOWN, prop, target, "interprocedural CHC", reason="unknown target")
    params = {name: [a.arg for a in fn.args.args] for name, fn in fns.items()}
    Sum = {name: z3.Function(name + "_sum", *([z3.IntSort()] * (len(params[name]) + 1)), z3.BoolSort())
           for name in fns}
    Err = z3.Function("ErrIP", z3.BoolSort())
    ctx = Ctx({}); ctx.summaries = Sum; ctx.divvars = []; ctx.callvars = []
    R, rules, allvars = {}, [], []
    try:
        for name, fn in fns.items():
            blocks, entry = _build_cfg(fn.body)
            order = _cfg_vars(fn, blocks)
            og = params[name]
            ghosts = {p: z3.Int(f"o_{name}_{p}") for p in og}
            curm = {v: z3.Int(f"s_{name}_{v}") for v in order}
            allvars += list(ghosts.values()) + list(curm.values())
            Rb = {bid: z3.Function(f"R_{name}_{bid}", *([z3.IntSort()] * (len(og) + len(order))), z3.BoolSort())
                  for bid in blocks}
            R.update({(name, bid): rel for bid, rel in Rb.items()})

            def tup(st):
                return [ghosts[p] for p in og] + [st[v] for v in order]

            init = {v: (ghosts[v] if v in og else z3.IntVal(0)) for v in order}
            rules.append((Rb[entry](*tup(init)), []))
            for bid, b in blocks.items():
                ctx.traps = []; ctx.pc = z3.BoolVal(True); ctx.divaux = []; ctx.callsub = []
                after = _apply_assigns(b.assigns, curm, ctx)
                term = b.term
                cond = retval = None
                if term and term[0] == "branch":
                    cond = ev_bool(term[1], after, ctx)
                elif term and term[0] == "return" and term[1] is not None:
                    retval = ev(term[1], after, ctx)
                body_rel = Rb[bid](*tup(curm))
                aux = list(ctx.divaux) + list(ctx.callsub)
                for t in ctx.traps:
                    rules.append((Err(), [body_rel] + aux + [t]))
                if term is None:
                    continue
                if term[0] == "goto":
                    rules.append((Rb[term[1]](*tup(after)), [body_rel] + aux))
                elif term[0] == "branch":
                    rules.append((Rb[term[2]](*tup(after)), [body_rel] + aux + [cond]))
                    rules.append((Rb[term[3]](*tup(after)), [body_rel] + aux + [z3.Not(cond)]))
                elif term[0] == "return" and term[1] is not None:
                    rules.append((Sum[name](*([ghosts[p] for p in og] + [retval])), [body_rel] + aux))
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "interprocedural CHC", reason=str(u))
    tv = {p: z3.Int(f"q_{p}") for p in params[tgt]}
    rr = z3.Int("_ipret")
    allvars += list(tv.values()) + [rr]
    rules.append((Err(), [pre(tv), Sum[tgt](*([tv[p] for p in params[tgt]] + [rr])), z3.Not(post(tv, rr))]))
    return _solve_horn(prop, target, "interprocedural CHC", "interprocedural CHC (summaries, loops)",
                       list(R.values()) + list(Sum.values()) + [Err], [*allvars, *ctx.divvars, *ctx.callvars],
                       rules, Err(),
                       on_error=lambda m: "engine timeout (nonlinear?)" if "canceled" in m else f"engine: {m}")


def lower_to_ir(src):
    fn = _fndef(src)
    instrs = []
    for s in fn.body:
        if isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name):
            instrs.append((s.targets[0].id, s.value))
        elif isinstance(s, ast.Return):
            break
        else:
            raise Unsupported(f"core IR statement {type(s).__name__}")
    return instrs


def denote_ir(prog, state, ctx=None):
    ctx = ctx or Ctx({})
    st = dict(state)
    for var, expr in prog:
        st[var] = ev(expr, st, ctx)
    return st


def compose_ir(p, q):
    return p + q


class IR:
    """A morphism in the category of state transformers: a program lowered to a sequence of
    (variable, expression) assignments. Identity and composition are first-class operations on this
    object, so the category structure the functor proof describes is the structure the engine
    actually manipulates. `f.then(g)` (also `f @ g`) sequences f before g; `IR.identity()` is the
    empty program; `denote` is the state transformer the morphism realizes."""

    def __init__(self, instrs):
        self.instrs = list(instrs)

    @staticmethod
    def identity():
        return IR([])                                        # the empty program: identity transformer

    @staticmethod
    def lower(src):
        return IR(lower_to_ir(src))

    def then(self, other):
        return IR(compose_ir(self.instrs, other.instrs))     # composition = sequencing

    __matmul__ = then                                        # f @ g reads as "f then g"

    def denote(self, state, ctx=None):
        return denote_ir(self.instrs, state, ctx)

    def __repr__(self):
        return f"IR({len(self.instrs)} instr)"


def _ir_state(*morphs):
    names = set()
    for m in morphs:
        for v, e in m.instrs:
            names.add(v)
            names |= {n.id for n in ast.walk(e) if isinstance(n, ast.Name)}
    return {v: z3.Int(v) for v in sorted(names)} or {"_s": z3.Int("_s")}


def verify_category_laws(prop, target, f_src, g_src) -> Verdict:
    """Verify, on all states, that the engine's IR satisfies the category functor laws through its
    first-class identity and composition: the identity morphism denotes to the identity transformer,
    and composition denotes to composition of transformers. These are the laws the Rocq functor proof
    establishes, here checked on the IR objects the engine composes with."""
    ctx = Ctx({})
    f, g, idm = IR.lower(f_src), IR.lower(g_src), IR.identity()
    state = _ir_state(f, g)
    id_out = idm.denote(state, ctx)                          # law 1: denote(identity) = id
    if _solve_corro(z3.Not(z3.And(*[id_out.get(v, state[v]) == state[v] for v in state])))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "IR category", reason="identity law does not hold")
    lhs = f.then(g).denote(state, ctx)                       # law 2: denote(f then g) = denote g . denote f
    rhs = g.denote(f.denote(state, ctx), ctx)
    keys = set(lhs) | set(rhs) | set(state)
    if _solve_corro(z3.Not(z3.And(*[lhs.get(k, state.get(k)) == rhs.get(k, state.get(k)) for k in keys])))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "IR category", reason="composition law does not hold")
    return Verdict(PROVED, prop, target, "IR category (identity + composition functor laws)",
                   reason="denote(identity) = id and denote(f then g) = denote g . denote f on all states")


def verify_ranking_synth(prop, target, src, repo=None) -> Verdict:
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None:
        return Verdict(UNKNOWN, prop, target, "ranking synthesis", reason="not a single-loop function")
    ctx = Ctx(repo or {})
    try:
        init_state, order, sym, guard, body = _loop_state(ctx, args, init, loop, "_k")
        if ctx.traps:
            return Verdict(UNKNOWN, prop, target, "ranking synthesis", reason="division in loop")
        ctx.traps = None
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "ranking synthesis", reason=str(u))
    coeffs = [z3.Int(f"rc{i}") for i in range(len(order) + 1)]
    rank = lambda st: coeffs[0] + z3.Sum([coeffs[i + 1] * st[order[i]] for i in range(len(order))])
    r_sym, r_body = rank(sym), rank(body)
    # The synthesis condition is exists-coeffs forall-states, and r is bilinear (coeff * state), so a
    # monolithic quantified query is nonlinear and times out nondeterministically. Solve it by CEGIS: the
    # synthesizer fits coefficients to a growing set of concrete sample states (each constraint linear in the
    # coefficients, a fast quantifier-free solve), and a verifier checks the candidate over all states with one
    # more quantifier-free solve, feeding back any counterexample. Terminates, deterministic.
    synth = z3.Solver(); synth.set("rlimit", core.SOLVE_RLIMIT)   # deterministic bound, not wall-clock
    synth.add(z3.Or(*[c != 0 for c in coeffs[1:]]))
    subst = lambda expr, st: z3.substitute(expr, *[(sym[w], z3.IntVal(st[w])) for w in order])
    for _ in range(64):
        if synth.check() != z3.sat:
            return Verdict(UNKNOWN, prop, target, "ranking synthesis",
                           reason="no linear ranking function consistent with the samples")
        m = synth.model()
        cval = [m.eval(c, model_completion=True).as_long() for c in coeffs]
        rc_sym = cval[0] + z3.Sum([cval[i + 1] * sym[order[i]] for i in range(len(order))])
        rc_body = cval[0] + z3.Sum([cval[i + 1] * body[order[i]] for i in range(len(order))])
        chk, model = _solve(z3.And(guard, z3.Not(z3.And(rc_sym >= 0, rc_body <= rc_sym - 1))))
        if chk == PROVED:                                     # candidate holds for every state
            terms = ([str(cval[0])] if cval[0] else []) + \
                    [f"{cval[i + 1]}*{order[i]}" for i in range(len(order)) if cval[i + 1]]
            return Verdict(PROVED, prop, target, "ranking synthesis (CEGIS, exists-forall)",
                           reason="synthesized ranking function: " + " + ".join(terms or ["0"]))
        if chk == UNKNOWN:
            return Verdict(UNKNOWN, prop, target, "ranking synthesis", reason="verifier returned unknown")
        cex = {v: model.eval(sym[v], model_completion=True).as_long() for v in order}
        # require the next candidate to satisfy the conditions at this concrete state (linear in coeffs)
        synth.add(z3.Implies(subst(guard, cex),
                             z3.And(rank({v: z3.IntVal(cex[v]) for v in order}) >= 0,
                                    rank({v: subst(body[v], cex) for v in order}) <= rank({v: z3.IntVal(cex[v]) for v in order}) - 1)))
    return Verdict(UNKNOWN, prop, target, "ranking synthesis", reason="CEGIS did not converge")


def bmc_check(prop, target, src, pre, post, k=12, repo=None) -> Verdict:
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None or ret is None:
        return Verdict(UNKNOWN, prop, target, "BMC", reason="not a single-loop function")
    ctx = Ctx(repo or {})
    try:
        base = {a.arg: _param_term(a) for a in fn.args.args}      # typed: float params reason under IEEE-754
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        cur = _apply_assigns(init, base, ctx)
        exit_bad, reached = [], z3.BoolVal(True)
        for _ in range(k):
            g = ev_bool(loop.test, cur, ctx)
            rexpr = ev(ret.value, cur, ctx)
            exit_bad.append(z3.And(reached, z3.Not(g), z3.Not(post(base, rexpr))))
            reached = z3.And(reached, g)
            cur = _apply_assigns(loop.body, cur, ctx)
        ctx.traps = None
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "BMC", reason=str(u))
    st, model = _solve(z3.And(pre(base), z3.Or(*exit_bad)))
    if st == REFUTED:
        cex = ", ".join(f"{a}={model.eval(base[a], model_completion=True)}" for a in args)
        return Verdict(REFUTED, prop, target, f"BMC(k={k})",
                       counterexample=cex, reason="bounded counterexample to the postcondition")
    return Verdict(UNKNOWN, prop, target, f"BMC(k={k})", reason=f"no counterexample within {k} unrollings")


def _null_space(M, ncols):
    rows = [[_Fr(x) for x in r] for r in M]
    pivots, r = [], 0
    for col in range(ncols):
        piv = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][col]; rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]; rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        pivots.append(col); r += 1
        if r == len(rows):
            break
    basis = []
    for fc in [c for c in range(ncols) if c not in pivots]:
        v = [_Fr(0)] * ncols; v[fc] = _Fr(1)
        for ri, pc in enumerate(pivots):
            v[pc] = -rows[ri][fc]
        basis.append(v)
    return basis


def _interp_findiff(ys):
    """Newton forward-difference interpolation of integer samples y_0..y_K = p(0..K) for an unknown polynomial
    p: return (degree, [Δ^0 y_0, ..., Δ^degree y_0]) so p(x) = sum_d coeff_d * C(x, d), or None when the data is
    not a polynomial of degree < K (the (degree+1)-th forward difference must vanish, confirming the fit is
    determined, not under-constrained). Pure big-integer subtraction -- no matrix, no rational arithmetic --
    so it is cheap even when the y values themselves are large (a high-power sum)."""
    diffs = [list(ys)]
    while len(diffs[-1]) > 1:
        prev = diffs[-1]
        diffs.append([prev[k + 1] - prev[k] for k in range(len(prev) - 1)])
    coeffs = [row[0] for row in diffs]                          # coeffs[d] = Δ^d y_0
    deg = max((d for d, c in enumerate(coeffs) if c != 0), default=0)
    if deg + 1 >= len(coeffs) or coeffs[deg + 1] != 0:         # need Δ^{deg+1} y_0 == 0 to confirm the degree
        return None
    return deg, coeffs[:deg + 1]


def _powersum_invariant(prop, target, src, pre, post, repo=None, maxdeg=8) -> Verdict:
    """A single-loop accumulator whose body is param-free and whose counter advances by one (i = i + 1) has
    every loop variable a polynomial in the counter, so the closed-form invariant `var == p(counter)` is
    recovered by interpolating p through a few small concrete steps (finite differences) rather than searching a
    monomial null-space -- the exact-rational-over-huge-values cost wall the data-driven learner hits past
    degree 4. The interpolated polynomials, the counter's guard-derived bound, and `counter >= start` form a
    candidate invariant the solver checks for initiation, preservation, and the postcondition at exit; a wrong
    interpolation fails a check and yields UNKNOWN. Discharges an arbitrary-degree power sum (sum of i^k);
    UNKNOWN outside the param-free unit-counter shape."""
    import math
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None or ret is None or not args:
        return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="single-loop with parameters")
    if not (isinstance(loop.test, ast.Compare) and len(loop.test.ops) == 1
            and isinstance(loop.test.ops[0], (ast.Lt, ast.LtE)) and isinstance(loop.test.left, ast.Name)):
        return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="guard is not `counter < bound`")
    counter = loop.test.left.id
    ctx = Ctx(repo or {})
    try:
        base = {a: z3.Int(a) for a in args}
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        init_state = _apply_assigns(init, base, ctx)
        order = args + sorted(set(init_state) - set(args))
        if counter not in order or counter in args:
            return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="counter is not a loop local")
        sym = dict(base)
        for v in order:
            if v not in args:
                sym[v] = z3.Int(v + "_l")
        guard = ev_bool(loop.test, sym, ctx)
        body = _apply_assigns(loop.body, sym, ctx)
        ret_exit = ev(ret.value, sym, ctx)
        bound = ev(loop.test.comparators[0], sym, ctx)         # the guard's right side (the counter's bound)
        if ctx.traps:
            return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="division in loop")
        ctx.traps = None
        if not (z3.is_expr(bound) and z3.is_int(bound)):
            return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="non-integer guard bound")
        if z3.simplify(body[counter] - sym[counter]).as_long() != 1:   # unit-step counter only
            return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="counter does not step by one")
    except (Unsupported, z3.Z3Exception, AttributeError):
        return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="not modeled")
    locals_ = [v for v in order if v not in args]
    state = {}
    for v in locals_:                                          # the loop-variable starts must be constants
        sv = z3.simplify(init_state[v])
        if not z3.is_int_value(sv):
            return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="non-constant loop-variable start")
        state[v] = sv.as_long()
    cstart = state[counter]
    points = []                                                # (counter value, {loop var: value}) at each loop head
    for _ in range(maxdeg + 2):
        points.append(dict(state))
        sub = [(sym[v], z3.IntVal(state[v])) for v in locals_]
        nxt = {}
        for v in locals_:
            bv = z3.simplify(z3.substitute(body[v], *sub))     # param-free body: a concrete next value
            if not z3.is_int_value(bv):
                return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="body references a parameter")
            nxt[v] = bv.as_long()
        state = nxt
    conj = [sym[counter] >= cstart]
    if isinstance(loop.test.ops[0], ast.Lt):
        conj.append(sym[counter] <= bound)                     # counter < bound: counter <= bound is inductive
    else:
        conj.append(sym[counter] <= bound + 1)                 # counter <= bound: exit one past
    for v in locals_:
        if v == counter:
            continue
        fit = _interp_findiff([pt[v] for pt in points])
        if fit is None:
            return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason=f"{v} is not polynomial in the counter")
        deg, cs = fit
        L = 1
        for d in range(deg + 1):
            L = L * math.factorial(d) // math.gcd(L, math.factorial(d))     # lcm of the factorials clears denominators
        rhs = z3.IntVal(0)
        x = sym[counter] - cstart
        for d, c in enumerate(cs):
            fall = z3.IntVal(1)                                # falling factorial x*(x-1)*...*(x-d+1)
            for m in range(d):
                fall = fall * (x - m)
            rhs = rhs + z3.IntVal(c * (L // math.factorial(d))) * fall
        conj.append(L * sym[v] == rhs)                         # L*var == the integer-coefficient polynomial in the counter
    inv = z3.And(*conj)
    at_init = z3.substitute(inv, *[(sym[v], init_state[v]) for v in order])
    at_body = z3.substitute(inv, *[(sym[v], body[v]) for v in order])
    if _solve(z3.And(pre(base), z3.Not(at_init)))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="initiation not established")
    if _solve(z3.And(inv, guard, z3.Not(at_body)))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="invariant not preserved")
    if _solve_corro(z3.And(inv, z3.Not(guard), z3.Not(post(base, ret_exit))))[0] != PROVED:
        return Verdict(UNKNOWN, prop, target, "power-sum invariant", reason="postcondition not established")
    return Verdict(PROVED, prop, target, "power-sum invariant (interpolated, verified)",
                   reason="closed-form invariant interpolated through the counter and verified inductively")


def learn_invariant(prop, target, src, pre, post, repo=None, degree=2, max_degree=None) -> Verdict:
    max_degree = degree if max_degree is None else max_degree      # try degree..max_degree (default: just degree)
    fn, args, init, loop, ret = _parse_single_loop(src)
    if loop is None or ret is None or len(args) > 3:
        return Verdict(UNKNOWN, prop, target, "invariant learning", reason="single-loop, <=3 params")
    ctx = Ctx(repo or {})
    try:
        base = {a: z3.Int(a) for a in args}
        ctx.traps = []; ctx.pc = z3.BoolVal(True)
        init_state = _apply_assigns(init, base, ctx)
        order = args + sorted(set(init_state) - set(args))
        sym = dict(base)                                            # params shared with base
        for v in order:
            if v not in args:
                sym[v] = z3.Int(v + "_l")
        guard = ev_bool(loop.test, sym, ctx)
        body = _apply_assigns(loop.body, sym, ctx)
        ret_exit = ev(ret.value, sym, ctx)
        if ctx.traps:
            return Verdict(UNKNOWN, prop, target, "invariant learning", reason="division in loop")
        ctx.traps = None
    except Unsupported as u:
        return Verdict(UNKNOWN, prop, target, "invariant learning", reason=str(u))

    import itertools
    pvals = (3, 5, 7) if len(args) >= 2 else (3, 5, 7, 9, 11)
    samples = []
    for combo in itertools.product(pvals, repeat=len(args)):        # grid over parameters
        psub = [(base[args[i]], z3.IntVal(combo[i])) for i in range(len(args))]
        st, ok = {args[i]: combo[i] for i in range(len(args))}, True
        for v in order:
            if v in args:
                continue
            val = z3.simplify(z3.substitute(init_state[v], *psub))
            if not z3.is_int_value(val):
                ok = False; break
            st[v] = val.as_long()
        if not ok:
            continue
        for _ in range(30):
            samples.append(dict(st))
            sub = [(sym[v], z3.IntVal(st[v])) for v in order]
            if not z3.is_true(z3.simplify(z3.substitute(guard, *sub))):
                break
            nxt, ok = {}, True
            for v in order:
                bv = z3.simplify(z3.substitute(body[v], *sub))
                if not z3.is_int_value(bv):
                    ok = False; break
                nxt[v] = bv.as_long()
            if not ok:
                break
            st = nxt
    if len(samples) < 4:
        return Verdict(UNKNOWN, prop, target, "invariant learning", reason="insufficient samples")

    import itertools as _it
    import math

    def mono_val(lbl, s):
        if lbl == "1":
            return 1
        prod = 1
        for f in lbl.split("*"):
            prod *= s[f]
        return prod

    def mono_z3(lbl):
        if lbl == "1":
            return z3.IntVal(1)
        acc = z3.IntVal(1)
        for f in lbl.split("*"):
            acc = acc * sym[f]
        return acc

    fixed = []                                                     # candidates independent of the degree
    for u in order:                                                # learned difference inequalities
        for v in order:
            if u != v:
                k = max(s[u] - s[v] for s in samples)
                fixed.append((f"{u}-{v} <= {k}", sym[u] - sym[v] <= k))
    for u in order:                                                # learned single-variable bounds
        lo, hi = min(s[u] for s in samples), max(s[u] for s in samples)
        fixed.append((f"{u} >= {lo}", sym[u] >= lo))
        fixed.append((f"{u} <= {hi}", sym[u] <= hi))
    at_init = lambda p: z3.substitute(p, *[(sym[v], init_state[v]) for v in order])
    at_body = lambda p: z3.substitute(p, *[(sym[v], body[v]) for v in order])

    def attempt(deg):
        """Learn and Houdini-filter an invariant whose equalities range over monomials up to `deg`,
        then check the surviving conjunction entails the postcondition at loop exit. None if it cannot."""
        monos = ["1"] + list(order)
        for d in range(2, deg + 1):                                # monomials of degree 2..deg
            for combo in _it.combinations_with_replacement(order, d):
                monos.append("*".join(combo))
        M = [[mono_val(lbl, s) for lbl in monos] for s in samples]
        cands = []                                                 # (label, predicate over sym)
        for c in _null_space(M, len(monos)):                       # learned polynomial equalities of degree deg
            L = 1
            for d in (x.denominator for x in c):
                L = L * d // math.gcd(L, d)
            ci = [int(x * L) for x in c]
            if all(x == 0 for x in ci):
                continue
            expr = z3.Sum([ci[j] * mono_z3(monos[j]) for j in range(len(monos)) if ci[j] != 0])
            lbl = " + ".join(f"{ci[j]}*{monos[j]}" for j in range(len(monos)) if ci[j] != 0) + " == 0"
            cands.append((lbl, expr == 0))
        cands.extend(fixed)
        kept = [(l, p) for l, p in cands                           # hold at the loop entry
                if _solve(z3.And(pre(base), z3.Not(at_init(p))))[0] == PROVED]
        changed = True
        while changed:                                             # Houdini inductive filter
            changed = False
            conj = z3.And(*[p for _, p in kept]) if kept else z3.BoolVal(True)
            for l, p in list(kept):
                if _solve(z3.And(conj, guard, z3.Not(at_body(p))))[0] != PROVED:
                    kept.remove((l, p)); changed = True
        if not kept:
            return None
        conj = z3.And(*[p for _, p in kept])
        _sr = core.SOLVE_RLIMIT                               # a nonlinear (degree-3/4 SOS) invariant verification is
        core.SOLVE_RLIMIT = max(_sr, 64_000_000)             # borderline at the default rlimit and flakes to UNKNOWN
        try:                                                  # under contention; 4x headroom is deterministic and
            _ok = _solve_corro(z3.And(conj, z3.Not(guard), z3.Not(post(base, ret_exit))))[0] == PROVED   # reliably proves
        finally:                                              # a valid invariant (more rlimit never yields a false PROVED)
            core.SOLVE_RLIMIT = _sr
        if _ok:
            return Verdict(PROVED, prop, target, "invariant learning (data-driven, verified)",
                           reason="learned invariant: " + " ; ".join(l for l, _ in kept))
        return None

    for deg in range(degree, max_degree + 1):                      # escalate the polynomial degree on failure
        got = attempt(deg)
        if got is not None:
            return got
    return Verdict(UNKNOWN, prop, target, "invariant learning",
                   reason="learned invariants insufficient for the postcondition")


__all__ = [
    'verify_equiv',
    'prove_doctests',
    'check_return_annotation',
    'verify_metamorphic',
    'verify_predicate',
    'prove',
    'check',
    '_contract_conditions',
    'verify_contracts',
    'verify_all',
    'verify_change',
    'change_bundle',
    'repair_loop',
    'synthesize_spec',
    'explain',
    'verify_heap_property',
    'load_module',
    'load_package',
    'load_program',
    'check_program',
    'repo_modules',
    'load_repo',
    'verify_repo',
    'verify_diff',
    'coverage',
    'scan',
    'finding_fingerprint',
    'baseline_partition',
    'verify_system',
    'verify_optional',
    'opt_none',
    'opt_some',
    'opt_is_none',
    'opt_val',
    'verify_deductive',
    '_HELD',
    '_NOTHELD',
    '_meet',
    'verify_lock',
    'Prop',
    'Orchestrator',
    'fix_loop',
    '_gen_candidates',
    '_minimize',
    'verify_deductive_auto',
    '_bv_eval',
    '_bv_cond',
    'verify_no_overflow',
    '_has_var_bitwise',
    'verify_bitwise',
    'verify_chc',
    'verify_loop_auto',
    '_Block',
    '_build_cfg',
    '_cfg_vars',
    '_BUILTIN_NAMES',
    '_scope_bound_names',
    '_use_before_def',
    '_definite_assignment_guard',
    'verify_function',
    'verify_no_raise',
    'verify_no_raise_optional',
    'verify_no_leak',
    'verify_recursive',
    'verify_recursive_list',
    '_is_self_recursive',
    'verify_recursive_termination',
    'verify_mutual_termination',
    'verify_total',
    '_is_array_param',
    '_ev_arr',
    '_arr_state',
    '_arr_apply',
    '_fresh_like',
    'q_forall',
    'verify_array_loop',
    'verify_array_loop_auto',
    'verify_array_code',
    'verify_nested_array_bounds',
    'verify_nested_array_content',
    '_empty_list_lit',
    'verify_growing_list_auto',
    'verify_growing_set_auto',
    '_SubElt',
    'verify_sequence_loop',
    'verify_generator_loop',
    'verify_map_comprehension',
    'verify_all_any',
    'verify_termination',
    'verify_nontermination',
    'verify_iteration_bound',
    'export_grounding',
    'recheck_grounding',
    'verify_modular',
    'verify_program',
    'verify_program_loops',
    'lower_to_ir',
    'denote_ir',
    'compose_ir',
    'IR',
    'verify_category_laws',
    'verify_ranking_synth',
    'bmc_check',
    '_null_space',
    'learn_invariant',
]
