"""Sound type inference: an over-approximating abstract interpretation that reports, for a function's return
value (and the locals feeding it), a set of Python type names guaranteed to contain the runtime type, or
UNKNOWN when no such bound can be established.

The soundness dual of the heuristic inferencer in typeinfer.py: there a single most-likely type, scored by
exact match; here a proven over-approximation -- type(...).__name__ is always one of the names returned, on
every input. A type is claimed only where Python's semantics fix it: a literal or container carries its type,
a fixed-return builtin (len, str, sorted, ...) its result type, `not` / `is` / `in` and comparisons of known
scalars yield bool, and arithmetic over known numeric/sequence types yields the type the operation produces.
Anything the rules cannot bound -- a bare parameter, a subscript, an attribute, an unmodeled call -- widens to
UNKNOWN, which is sound. Locals are bounded by the union of their assignments; a parameter is unbounded here.
differential_sound_inference_audit holds the result against concrete execution.
"""
import ast

_NUMERIC = frozenset({"int", "bool", "float", "complex"})
_ORDERABLE = frozenset({"int", "bool", "float", "str", "bytes"})        # comparisons return bool
_EQUATABLE = _ORDERABLE | {"complex"}                                   # == / != return bool

# builtins whose return type is fixed regardless of the argument (the real builtins, not shadowed names)
_BUILTIN_RET = {
    "len": "int", "ord": "int", "id": "int", "hash": "int",
    "chr": "str", "hex": "str", "oct": "str", "bin": "str", "repr": "str", "ascii": "str",
    "str": "str", "format": "str", "input": "str",
    "bool": "bool", "isinstance": "bool", "issubclass": "bool", "callable": "bool",
    "all": "bool", "any": "bool", "hasattr": "bool",
    "int": "int", "float": "float", "complex": "complex", "bytes": "bytes", "bytearray": "bytearray",
    "list": "list", "sorted": "list", "dir": "list", "dict": "dict", "vars": "dict",
    "set": "set", "frozenset": "frozenset", "tuple": "tuple", "divmod": "tuple", "range": "range",
    "zip": "zip", "map": "map", "filter": "filter", "enumerate": "enumerate",      # iterator/view builtins each
    "memoryview": "memoryview", "slice": "slice", "object": "object",              # return one fixed concrete type
    "globals": "dict", "locals": "dict", "print": "NoneType",
}
# string methods whose return type is fixed (the value's type when the call returns, on a str receiver)
_STR_METHOD_RET = {
    "upper": "str", "lower": "str", "strip": "str", "lstrip": "str", "rstrip": "str", "capitalize": "str",
    "title": "str", "swapcase": "str", "casefold": "str", "center": "str", "ljust": "str", "rjust": "str",
    "zfill": "str", "replace": "str", "format": "str", "join": "str", "expandtabs": "str", "translate": "str",
    "removeprefix": "str", "removesuffix": "str", "format_map": "str",
    "split": "list", "rsplit": "list", "splitlines": "list",
    "find": "int", "rfind": "int", "index": "int", "rindex": "int", "count": "int",
    "startswith": "bool", "endswith": "bool", "isdigit": "bool", "isalpha": "bool", "isalnum": "bool",
    "isspace": "bool", "isupper": "bool", "islower": "bool", "isnumeric": "bool", "isdecimal": "bool",
    "istitle": "bool", "isidentifier": "bool", "isprintable": "bool", "isascii": "bool",
    "encode": "bytes", "partition": "tuple", "rpartition": "tuple",
}
# container methods whose return type is fixed, keyed by the receiver's type (mutators return None)
_METHOD_RET = {
    "list": {"copy": "list", "count": "int", "index": "int", "append": "NoneType", "extend": "NoneType",
             "insert": "NoneType", "remove": "NoneType", "sort": "NoneType", "reverse": "NoneType",
             "clear": "NoneType"},
    "dict": {"copy": "dict", "keys": "dict_keys", "values": "dict_values", "items": "dict_items",
             "update": "NoneType", "clear": "NoneType"},
    "set": {"copy": "set", "add": "NoneType", "discard": "NoneType", "remove": "NoneType", "clear": "NoneType",
            "update": "NoneType", "union": "set", "intersection": "set", "difference": "set",
            "symmetric_difference": "set", "isdisjoint": "bool", "issubset": "bool", "issuperset": "bool"},
    "frozenset": {"copy": "frozenset", "union": "frozenset", "intersection": "frozenset",
                  "difference": "frozenset", "isdisjoint": "bool", "issubset": "bool", "issuperset": "bool"},
    "tuple": {"count": "int", "index": "int"},
    "bytes": {"decode": "str", "hex": "str", "count": "int", "find": "int", "index": "int",
              "startswith": "bool", "endswith": "bool", "split": "list", "replace": "bytes"},
}


def _const_type(v):
    if isinstance(v, bool):
        return "bool"
    if isinstance(v, int):
        return "int"
    if isinstance(v, float):
        return "float"
    if isinstance(v, complex):
        return "complex"
    if isinstance(v, str):
        return "str"
    if isinstance(v, bytes):
        return "bytes"
    if v is None:
        return "NoneType"
    return None


_ANN_TYPES = frozenset({"int", "float", "str", "bool", "bytes", "bytearray", "complex",
                        "list", "dict", "set", "frozenset", "tuple", "range"})


def _ann_sound_type(ann):
    """The type-name set a parameter annotation declares, trusting it as a caller-honored contract, or
    None when the annotation is absent or not a plain builtin type. `int` -> {int}; `list[int]` /
    `List[int]` -> {list} (the container, not its elements); `None` -> {NoneType}."""
    if ann is None:
        return None
    if isinstance(ann, ast.Name) and ann.id in _ANN_TYPES:
        return {ann.id}
    if isinstance(ann, ast.Constant) and ann.value is None:
        return {"NoneType"}
    if isinstance(ann, ast.Subscript) and isinstance(ann.value, ast.Name) and ann.value.id.lower() in _ANN_TYPES:
        return {ann.value.id.lower()}                          # subscripted generic: the container type
    return None


def _num_result(a, b):
    """The type of an additive/multiplicative result over two numeric types (widest wins; bool acts as
    int, so True + True is int)."""
    if "complex" in (a, b):
        return "complex"
    if "float" in (a, b):
        return "float"
    return "int"


def _binop_pair(lt, rt, op):
    """The result type of `lt op rt` for two concrete type names, or None when the operation does not
    fix a single result type (so the caller widens to UNKNOWN)."""
    ln, rn = lt in _NUMERIC, rt in _NUMERIC
    if isinstance(op, ast.Add):
        if ln and rn:
            return _num_result(lt, rt)
        if lt == rt and lt in ("str", "list", "tuple", "bytes"):
            return lt
        return None
    if isinstance(op, ast.Sub):
        if ln and rn:
            return _num_result(lt, rt)
        if lt in ("set", "frozenset") and rt in ("set", "frozenset"):
            return lt                                           # set/frozenset difference: the left operand's type
        return None
    if isinstance(op, ast.Mult):
        if ln and rn:
            return _num_result(lt, rt)
        for s, n in ((lt, rt), (rt, lt)):                       # sequence * int -> sequence
            if s in ("str", "list", "tuple", "bytes") and n in ("int", "bool"):
                return s
        return None
    if isinstance(op, ast.Div):
        if ln and rn:
            return "complex" if "complex" in (lt, rt) else "float"
        return None
    if isinstance(op, (ast.FloorDiv, ast.Mod)):
        if lt in ("int", "bool", "float") and rt in ("int", "bool", "float"):
            return "float" if "float" in (lt, rt) else "int"
        if isinstance(op, ast.Mod) and lt in ("str", "bytes"):  # printf-style `s % args` yields s's own type
            return lt
        return None
    if isinstance(op, (ast.LShift, ast.RShift)):
        if lt in ("int", "bool") and rt in ("int", "bool"):
            return "int"                                        # shifting an int/bool by an int/bool yields int
        return None
    if isinstance(op, (ast.BitAnd, ast.BitOr, ast.BitXor)):
        if lt in ("int", "bool") and rt in ("int", "bool"):     # bool op bool stays bool (True & False is a bool);
            return "bool" if lt == "bool" and rt == "bool" else "int"   # any int operand makes the result int
        if lt in ("set", "frozenset") and rt in ("set", "frozenset"):
            return lt                                           # set/frozenset &, |, ^ : the left operand's type
        if isinstance(op, ast.BitOr) and lt == "dict" and rt == "dict":
            return "dict"                                       # PEP 584 dict union d1 | d2 is a dict
        return None
    return None                                                 # Pow: not bounded here


def _join(a, b):
    """Join two type sets in the over-approximation lattice; None is top (UNKNOWN)."""
    if a is None or b is None:
        return None
    return a | b


_CLASS_TRANSPARENT_DECO = frozenset({"dataclass", "total_ordering", "final", "runtime_checkable"})


def _transparent_class_decorator(d):
    """True if class decorator `d` returns the same class object, so the class name stays a sound constructor
    and type: dataclass, functools.total_ordering, and the typing markers final / runtime_checkable modify
    the class in place and return it. Any other decorator may replace the class with a different one, so a
    class bearing it is not treated as a sound constructor."""
    name = d.func if isinstance(d, ast.Call) else d
    if isinstance(name, ast.Attribute):
        return name.attr in _CLASS_TRANSPARENT_DECO
    if isinstance(name, ast.Name):
        return name.id in _CLASS_TRANSPARENT_DECO
    return False


def _new_instance_name(m):
    """In a `__new__`, the single local bound to a freshly created instance (`x = <...>.__new__(...)`) and
    returned on every path, or None when the pattern is not exactly that. Lets fields_of capture the fields a
    __new__ sets on the instance it returns -- the instance there is a local, not the `cls` first parameter.
    The strict conditions keep the capture sound: a __new__ that returns a different object, or rebinds the
    local, contributes no fields rather than a wrong one."""
    created = set()
    for s in ast.walk(m):
        if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) \
                and isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Attribute) \
                and s.value.func.attr == "__new__":
            created.add(s.targets[0].id)
    if len(created) != 1:
        return None                                              # zero or several fresh instances: not this pattern
    name = next(iter(created))
    rebinds = 0
    for s in ast.walk(m):
        if isinstance(s, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name for t in s.targets):
            rebinds += 1
        elif isinstance(s, (ast.AugAssign, ast.AnnAssign)) and isinstance(s.target, ast.Name) \
                and s.target.id == name:
            rebinds += 1
    if rebinds != 1:
        return None                                              # the instance local is reassigned: unsound to track
    rets = [s for s in ast.walk(m) if isinstance(s, ast.Return)]
    if not rets or not all(isinstance(r.value, ast.Name) and r.value.id == name for r in rets):
        return None                                              # does not return exactly that instance on every path
    return name


class _Ctx:
    def __init__(self, src, repo):
        self.funcs = {}                                         # name -> FunctionDef
        self.classes = set()                                    # class names (constructors)
        self.methods = {}                                       # class name -> {method name -> FunctionDef}
        self._fields = {}                                       # lazy cache: class name -> {field: bound}
        self._fields_computing = set()                          # re-entrancy guard for fields_of
        bases = {}                                              # class name -> simple-Name base names
        used_as_base = set()                                    # every name used as a base by some class
        foreign_base = set()                                    # classes with a base (or keyword) this pass cannot resolve
        for unit in [src] + list((repo or {}).values()):
            try:
                mod = ast.parse(unit)
            except SyntaxError:
                continue
            for n in mod.body:
                if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    self.funcs.setdefault(n.name, n)
                elif isinstance(n, ast.ClassDef):
                    bnames = [b.id for b in n.bases if isinstance(b, ast.Name)]
                    bases.setdefault(n.name, []).extend(bnames)
                    used_as_base.update(bnames)
                    if n.keywords or any(not isinstance(b, ast.Name) for b in n.bases):
                        foreign_base.add(n.name)        # an Attribute/Subscript base or a metaclass: unanalyzable
                    if all(_transparent_class_decorator(d) for d in n.decorator_list):
                        self.classes.add(n.name)        # an undecorated class, or one bearing only transparent
                        self.methods.setdefault(n.name, {})     # decorators, is a sound constructor; its directly
                        for m in n.body:                        # defined undecorated methods resolve on instances
                            if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)) and not m.decorator_list:
                                self.methods[n.name].setdefault(m.name, m)
        self._bases = bases
        # "analyzable": a sound constructor whose every base is object or another analyzable repo class, so the
        # complete set of methods that assign its instance fields is visible (no external base hides a setter)
        self.analyzable = set()
        changed = True
        while changed:
            changed = False
            for c in self.classes:
                if c in self.analyzable or c in foreign_base:
                    continue
                if all(b == "object" or (b in self.classes and b in self.analyzable) for b in bases.get(c, [])):
                    self.analyzable.add(c)
                    changed = True
        # self : C is sound to assume only where C is never subclassed, so an instance of it is exactly it and
        # never a subclass that overrides a field's type; the field map itself unions the whole base chain
        self.field_classes = {c for c in self.analyzable if c not in used_as_base}

    def fields_of(self, cls):
        """`{field: type bound}` for the instance fields of an analyzable class: the union, over every
        `self.field = expr` in the class's own methods and the methods of its (analyzable) base chain, of
        expr's bound. A field assigned in any other way (augmented, annotated, unpacked, via setattr) is
        dropped, so a read of a kept field is soundly bounded. Computed once; the guard returns {} on re-entry
        so a field defined in terms of another (`self.x = self.y`) widens to UNKNOWN rather than recursing."""
        if cls in self._fields:
            return self._fields[cls]
        if cls in self._fields_computing or cls not in self.analyzable:
            return {}
        self._fields_computing.add(cls)
        try:
            acc, bad = {}, set()
            for b in self._bases.get(cls, []):                  # inherited fields: union the base chain's map
                if b != "object":
                    for f, bnd in self.fields_of(b).items():
                        acc[f] = bnd if f not in acc else (acc[f] | bnd)
            for m in self.methods.get(cls, {}).values():
                pos = m.args.posonlyargs + m.args.args
                if m.name == "__new__":                         # the instance is a local (x = cls.__new__(cls)),
                    selfname = _new_instance_name(m)            # not the `cls` first parameter
                    if selfname is None:                        # not the clean fresh-and-return pattern: no fields
                        continue
                    argb = None                                 # cls is the class object, not an instance: leave it untyped
                else:
                    if not pos:
                        continue
                    selfname = pos[0].arg
                    argb = [({cls}, None)]
                env = _local_env(m, self, argb, track_elements=False)
                simple = set()                                  # ids of `self.f = e` single-assign targets
                for s in ast.walk(m):
                    if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Attribute) \
                            and isinstance(s.targets[0].value, ast.Name) and s.targets[0].value.id == selfname:
                        simple.add(id(s.targets[0]))
                        vt = _sound_type(s.value, env, self, frozenset())
                        if vt is None:
                            bad.add(s.targets[0].attr)
                        else:
                            acc[s.targets[0].attr] = vt if s.targets[0].attr not in acc else (acc[s.targets[0].attr] | vt)
                    elif isinstance(s, ast.Call) and isinstance(s.func, ast.Name) \
                            and s.func.id in ("setattr", "delattr") and s.args \
                            and isinstance(s.args[0], ast.Name) and s.args[0].id == selfname:
                        return self._fields.setdefault(cls, {})   # dynamic attribute set: no field is safe
                for s in ast.walk(m):                           # any other store to self.<f> (aug/ann/unpack/del/for)
                    if isinstance(s, ast.Attribute) and isinstance(s.value, ast.Name) and s.value.id == selfname \
                            and isinstance(s.ctx, (ast.Store, ast.Del)) and id(s) not in simple:
                        bad.add(s.attr)
            result = {f: b for f, b in acc.items() if f not in bad}
            self._fields[cls] = result
            return result
        finally:
            self._fields_computing.discard(cls)

    def resolve_method(self, cls, name):
        """The method `cls.name` dispatches to, following single-inheritance base links (an unambiguous MRO),
        or None if not found or the base chain forks. Sound for a constructor-exact receiver, whose call
        dispatches to exactly this definition."""
        seen = set()
        while cls is not None and cls not in seen:
            m = self.methods.get(cls, {}).get(name)
            if m is not None:
                return m
            seen.add(cls)
            bs = [b for b in self._bases.get(cls, []) if b != "object"]
            cls = bs[0] if len(bs) == 1 else None
        return None



def _note(target, untracked):
    for n in ast.walk(target):
        if isinstance(n, ast.Name):
            untracked.add(n.id)


def _scope_stmts(body):
    """The statements belonging to one scope: each statement in `body`, descending through control flow
    (if / for / while / with / try) but not into nested function, class, or lambda definitions, which open
    their own scope."""
    for s in body:
        yield s
        if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        for field in ("body", "orelse", "finalbody"):
            sub = getattr(s, field, None)
            if isinstance(sub, list):
                yield from _scope_stmts(sub)
        for h in getattr(s, "handlers", []):
            yield from _scope_stmts(h.body)


def _identity_of(node, env, ctx):
    """The callable identity `node` may evaluate to -- a set of repo-function names and/or lambda nodes -- or
    None when it is not provably a callable with a known body. A bare repo-function name is itself; a lambda
    is itself; a local or parameter carries the identity recorded under the ("@id", name) key; else unknown."""
    if isinstance(node, ast.Lambda):
        return frozenset({node})
    if isinstance(node, ast.Name):
        if node.id not in env and node.id in ctx.funcs:
            return frozenset({node.id})
        ids = env.get(("@id", node.id))
        return ids if isinstance(ids, frozenset) else None
    return None


def _track_identity(nm, value, env, ctx):
    """Maintain the callable-identity bound for `nm` across its assignments: the union of each assignment's
    function identity, or None (broken) once any assignment is not a provably-known function -- so a later
    call of `nm` resolves to a return type only when every assignment makes it a known function."""
    key = ("@id", nm)
    if env.get(key, "unset") is None:
        return                                                  # already broken: stays unknown
    ident = _identity_of(value, env, ctx)
    if ident is None:
        env[key] = None                                         # an assignment not pinned to a function: broken
    elif key not in env:
        env[key] = ident
    else:
        env[key] = env[key] | ident


def _argbounds(args, env, ctx, seen):
    """The per-positional-argument (type bound, callable-identity bound) pairs for a call, evaluated in the
    caller's environment -- threaded into the callee so a parameter passthrough or callback is bounded."""
    return [(_sound_type(a, env, ctx, seen), _identity_of(a, env, ctx)) for a in args]


def _callable_return(cid, ctx, seen, argbounds):
    """The sound return-type set of a callable identity `cid` -- a repo-function name, a lambda node, or a
    nested FunctionDef node -- for a call with the given positional-argument bounds, or None (UNKNOWN). A
    callable already on the stack recurses to UNKNOWN; a lambda's return is its body expression and a nested
    function's is analyzed as any function body would be, parameters seeded from the arguments."""
    if isinstance(cid, str):
        return _func_return(cid, ctx, seen, argbounds)
    if cid in seen:
        return None
    if isinstance(cid, ast.Lambda):
        return _sound_type(cid.body, _local_env(cid, ctx, argbounds), ctx, seen | {cid})
    return _func_return_node(cid, ctx, seen | {cid}, argbounds)     # a nested def: its body's sound return


def _bind_stmt(s, env, untracked, ctx):
    """Fold one binding statement into `env` (a sound type bound per name) or mark its targets untracked.
    Shared by the function-local and module-level passes; the union over a name's assignments is sound."""
    if isinstance(s, ast.Assign):
        if all(isinstance(tg, ast.Name) for tg in s.targets):     # `x = e` and chained `a = b = e`: every target
            t = _sound_type(s.value, env, ctx, set())             # name binds to the one value's bound
            for tg in s.targets:
                env[tg.id] = t if tg.id not in env else _join(env.get(tg.id), t)
                _track_identity(tg.id, s.value, env, ctx)
        elif (len(s.targets) == 1 and isinstance(s.targets[0], (ast.Tuple, ast.List))
              and isinstance(s.value, (ast.Tuple, ast.List))
              and not any(isinstance(e, ast.Starred) for e in s.value.elts)):
            T, V = s.targets[0].elts, s.value.elts                # unpack of a literal `a, b = e1, e2` (and the
            stars = [i for i, e in enumerate(T) if isinstance(e, ast.Starred)]   # starred form `a, *b, c = ...`):
            pairs = None                                          # each target's bound, or None to abstain on all
            if not stars and len(T) == len(V):                    # plain parallel unpack: positional element bounds
                pairs = [(te, _sound_type(ve, env, ctx, set())) for te, ve in zip(T, V)]
            elif len(stars) == 1 and len(T) - 1 <= len(V):        # one starred target: the names before it take the
                k = stars[0]                                      # leading elements, the names after it the trailing
                pairs = [(T[i], _sound_type(V[i], env, ctx, set())) for i in range(k)]
                pairs.append((T[k].value, {"list"}))              # the starred name always collects a list
                back = len(T) - 1 - k
                pairs += [(T[k + 1 + j], _sound_type(V[len(V) - back + j], env, ctx, set())) for j in range(back)]
            if pairs is None:
                for tg in s.targets:
                    _note(tg, untracked)
            else:
                for te, vt in pairs:
                    if isinstance(te, ast.Name):
                        env[te.id] = vt if te.id not in env else _join(env.get(te.id), vt)
                    else:
                        _note(te, untracked)
        else:
            for tg in s.targets:
                _note(tg, untracked)
    elif isinstance(s, ast.AnnAssign) and isinstance(s.target, ast.Name):
        nm = s.target.id                                  # a local annotation is a trusted contract, exactly as
        ann = _ann_sound_type(s.annotation)               # a parameter annotation is, so `x: int` bounds x to int
        t = ann if ann is not None else (_sound_type(s.value, env, ctx, set()) if s.value is not None else None)
        env[nm] = t if nm not in env else _join(env.get(nm), t)
    elif isinstance(s, ast.AugAssign):
        prior = env.get(s.target.id) if isinstance(s.target, ast.Name) else None
        rhs = _sound_type(s.value, env, ctx, set())         # x op= e is type-wise x = x op e on the builtins, so
        t = None                                            # _binop_pair over x's prior bound and e gives a sound
        if isinstance(s.target, ast.Name) and isinstance(s.op, ast.Mod) and prior is not None \
                and prior <= {"str", "bytes"}:              # x %= e on a str/bytes x stays that type whatever e is
            t = set(prior)                                  # (printf-style; the right operand cannot intercept)
        elif isinstance(s.target, ast.Name) and prior is not None and rhs is not None:   # result, else abstain
            acc, ok = set(), True
            for a in prior:
                for b in rhs:
                    r = _binop_pair(a, b, s.op)
                    if r is None:
                        ok = False
                        break
                    acc.add(r)
                if not ok:
                    break
            t = acc if ok else None
        if t is not None:                                   # union the result with the prior bound: x holds the
            env[s.target.id] = _join(prior, t)              # prior type before the op and the result type after
        else:
            _note(s.target, untracked)
    elif isinstance(s, (ast.For, ast.AsyncFor)):
        if (isinstance(s.target, ast.Name) and isinstance(s.iter, ast.Call)
                and isinstance(s.iter.func, ast.Name) and s.iter.func.id == "range"
                and "range" not in ctx.funcs):            # `for i in range(...)`: i is int for any arguments,
            nm = s.target.id                              # so the loop variable carries a guaranteed int bound
            env[nm] = {"int"} if nm not in env else _join(env.get(nm), {"int"})
        elif (isinstance(s.iter, ast.Call) and isinstance(s.iter.func, ast.Name)
              and s.iter.func.id == "enumerate" and "enumerate" not in ctx.funcs):
            if isinstance(s.target, ast.Name):            # `for p in enumerate(...)`: p is an (index, item) tuple
                nm = s.target.id
                env[nm] = {"tuple"} if nm not in env else _join(env.get(nm), {"tuple"})
            elif (isinstance(s.target, ast.Tuple) and len(s.target.elts) == 2
                  and isinstance(s.target.elts[0], ast.Name)):
                idx = s.target.elts[0].id                 # `for i, x in enumerate(...)`: i is int, x is the item
                env[idx] = {"int"} if idx not in env else _join(env.get(idx), {"int"})
                _note(s.target.elts[1], untracked)
            else:
                _note(s.target, untracked)
        elif isinstance(s.target, ast.Name) and isinstance(s.iter, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
            items = s.iter.keys if isinstance(s.iter, ast.Dict) else s.iter.elts   # `for x in <literal>`: x ranges
            elts, ok = set(), bool(items)                                          # over the elements (a dict yields
            for e in items:                                                        # its keys), whose types are known
                if e is None or isinstance(e, ast.Starred):
                    ok = False
                    break
                et = _sound_type(e, env, ctx, set())
                if et is None:
                    ok = False
                    break
                elts |= et
            if ok:
                nm = s.target.id
                env[nm] = elts if nm not in env else _join(env.get(nm), elts)
            else:
                _note(s.target, untracked)
        elif isinstance(s.target, ast.Name) and isinstance(s.iter, ast.Name) and ("@elt", s.iter.id) in env:
            nm = s.target.id                                  # `for x in xs` where xs's element type is known
            elt = env[("@elt", s.iter.id)]                    # (e.g. xs is *args with known element types)
            env[nm] = elt if nm not in env else _join(env.get(nm), elt)
        else:
            _note(s.target, untracked)
    elif isinstance(s, ast.NamedExpr):
        if isinstance(s.target, ast.Name):                  # (y := e) binds y to e's value, so e's bound is y's
            t = _sound_type(s.value, env, ctx, set())
            nm = s.target.id
            env[nm] = t if nm not in env else _join(env.get(nm), t)
        else:
            _note(s.target, untracked)
    elif isinstance(s, (ast.With, ast.AsyncWith)):
        for item in s.items:
            if item.optional_vars is not None:
                _note(item.optional_vars, untracked)


def _union_positions(a, b):
    """Position-wise union of two per-position element-type lists, aligned by index (a position present in
    only one list keeps that list's type; indexing beyond a given return traps, producing no value)."""
    m = max(len(a), len(b))
    return [(a[i] if i < len(a) else set()) | (b[i] if i < len(b) else set()) for i in range(m)]


def _list_elements_of(expr, env, ctx, seen):
    """Per-position element types if `expr` provably evaluates to a list with known elements -- a list literal,
    or a call that itself returns such a list (a repo function, or a parameter/local holding known callable
    identities, e.g. a callback or a default-valued parameter) -- else None."""
    if isinstance(expr, ast.List):
        pos = []
        for e in expr.elts:
            et = None if isinstance(e, ast.Starred) else _sound_type(e, env, ctx, seen)
            if et is None:
                return None
            pos.append(et)
        return pos
    if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name):
        fid = expr.func.id
        if fid in env:                                          # a parameter/local holding callable identities
            ids = env.get(("@id", fid))
            if not (isinstance(ids, frozenset) and ids and all(isinstance(c, str) for c in ids)):
                return None
            targets = ids
        elif fid in ctx.funcs:
            targets = {fid}
        else:
            return None
        cols = None
        for cid in targets:
            p = _func_list_elements(cid, ctx, seen)
            if p is None:
                return None
            cols = p if cols is None else _union_positions(cols, p)
        return cols
    return None


def _func_list_elements(name, ctx, seen, argbounds=None):
    """The per-position element types of the list that `name(...)` returns for a call with the given argument
    bounds, or None. Every value-return must resolve to a list with bounded elements (a list literal, or a
    call returning such a list -- a callback or default-valued parameter included); positions are unioned
    across returns. `seen` bounds recursion."""
    if name in seen or name not in ctx.funcs:
        return None
    fn = ctx.funcs[name]
    if fn.decorator_list or _has_own_yield(fn):
        return None
    seen = seen | {name}
    env = _local_env(fn, ctx, argbounds, seen, track_elements=False)
    cols, saw = None, False
    for n in ast.walk(fn):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)) and n is not fn:
            continue
        if isinstance(n, ast.Return) and n.value is not None and _enclosing_is(fn, n):
            saw = True
            pos = _list_elements_of(n.value, env, ctx, seen)
            if pos is None:
                return None
            cols = pos if cols is None else _union_positions(cols, pos)
    return cols if (saw and cols) else None


def _indexable_lists(root, params, env, ctx, seen):
    """Names provably bound to a single read-only list literal in `root`'s scope: assigned exactly one list
    literal (with bounded elements) and used only by index/slice read -- never mutated (no `c[k]=`, no method
    call), aliased, passed as an argument, or otherwise referenced bare. For such a name `c[i]` is always the
    i-th literal element, so each index is soundly typed. Returns name -> list of per-position type sets; any
    disqualifying use drops the name."""
    assigns, disq, sub_value, uniform = {}, set(params), set(), {}
    for n in ast.walk(root):
        if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name):
            sub_value.add(id(n.value))
            if not isinstance(n.ctx, ast.Load):
                disq.add(n.value.id)                            # `c[k] = v` / `del c[k]`: mutation
    names = lambda t: [x.id for x in ast.walk(t) if isinstance(x, ast.Name)]
    for n in ast.walk(root):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                and (isinstance(n.value, (ast.List, ast.Tuple, ast.Dict))
                     or (isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Name)
                         and n.value.func.id in ctx.funcs)):
            assigns.setdefault(n.targets[0].id, []).append(n.value)   # list/dict literal, or c = make(...) where
        elif isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Attribute) \
                and n.value.func.attr in ("split", "rsplit", "splitlines") \
                and _sound_type(n.value.func.value, env, ctx, seen) == {"str"}:
            uniform[n.targets[0].id] = {"str"}                        # str.split family returns a list of str
        elif isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                and isinstance(n.value, ast.ListComp) and len(n.value.generators) == 1 \
                and isinstance(n.value.generators[0].target, ast.Name) \
                and isinstance(n.value.generators[0].iter, ast.Call) \
                and isinstance(n.value.generators[0].iter.func, ast.Name) \
                and n.value.generators[0].iter.func.id == "range" and "range" not in ctx.funcs:
            env2 = dict(env)                                          # [expr for i in range(...)]: i is int, so the
            env2[n.value.generators[0].target.id] = {"int"}          # list is uniform in the element expr's type
            et = _sound_type(n.value.elt, env2, ctx, seen)
            if et is not None:
                uniform[n.targets[0].id] = et
            else:
                disq.add(n.targets[0].id)
        elif isinstance(n, ast.Assign):                               # make's returns are list literals
            for t in n.targets:
                disq.update(names(t))
        elif isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name):
            disq.add(n.target.id)
        elif isinstance(n, ast.AugAssign):
            disq.update(names(n.target))
        elif isinstance(n, (ast.For, ast.AsyncFor)):
            disq.update(names(n.target))
        elif isinstance(n, ast.NamedExpr):
            disq.update(names(n.target))
        elif isinstance(n, (ast.With, ast.AsyncWith)):
            for it in n.items:
                if it.optional_vars is not None:
                    disq.update(names(it.optional_vars))
    pure = {"len", "sum", "min", "max", "sorted", "reversed", "any", "all", "print", "repr", "ascii",
            "str", "bool", "list", "tuple", "set", "frozenset", "dict", "iter", "enumerate", "zip",
            "map", "filter", "hash", "id"}
    safe_arg = set()
    for n in ast.walk(root):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in pure \
                and n.func.id not in ctx.funcs:                 # these builtins read the list, never mutate it,
            for a in n.args:                                    # so passing the list to them does not let it escape
                if isinstance(a, ast.Name):
                    safe_arg.add(id(a))
    for n in ast.walk(root):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) \
                and id(n) not in sub_value and id(n) not in safe_arg:
            disq.add(n.id)                                      # a bare load (alias / arg / attribute / iter): escapes
    out = {}
    for nm, lits in assigns.items():
        if nm in disq or len(lits) != 1:                        # one literal assignment, used only by index read
            continue
        node, items, ok = lits[0], [], True
        if isinstance(node, (ast.List, ast.Tuple)):
            for i, e in enumerate(node.elts):
                et = None if isinstance(e, ast.Starred) else _sound_type(e, env, ctx, seen)
                if et is None:
                    ok = False
                    break
                items.append((str(i), et))                      # c[0], c[1], ...
        elif isinstance(node, ast.Call):                        # c = make(...): make's returned list, by position,
            if any(isinstance(a, ast.Starred) for a in node.args):   # resolved for this call's actual arguments
                continue
            ab = "@defaults" if (not node.args and not node.keywords) else _argbounds(node.args, env, ctx, seen)
            positions = _func_list_elements(node.func.id, ctx, seen, ab)
            if positions is None:
                continue
            items = [(str(i), et) for i, et in enumerate(positions)]
        else:                                                   # a dict literal with constant keys: d[key] -> value
            for k, v in zip(node.keys, node.values):
                if not isinstance(k, ast.Constant):
                    ok = False
                    break
                vt = _sound_type(v, env, ctx, seen)
                if vt is None:
                    ok = False
                    break
                items.append((ast.unparse(k), vt))              # d['a'], d[0], ...
        if ok and items:
            out[nm] = items
    if uniform:                                                 # uniform-element containers (str.split -> list[str]):
        accessed = {}                                           # every index read is that one element type
        for n in ast.walk(root):
            if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name) \
                    and isinstance(n.ctx, ast.Load) and not isinstance(n.slice, ast.Slice):
                accessed.setdefault(n.value.id, set()).add(ast.unparse(n.slice))
        for nm, et in uniform.items():
            if nm in disq or nm in out:
                continue
            keys = accessed.get(nm, set())
            if keys:
                out[nm] = [(k, et) for k in keys]
    return out


def _local_env(fn, ctx, argbounds=None, seen=frozenset(), track_elements=True):
    """A sound type bound per local name: the union of the types of its simple `name = expr` assignments,
    or None (UNKNOWN) if any assignment is unbounded or the name is bound in a way this pass does not track
    (parameter, tuple unpacking, augmented/annotated-without-value, for-target, with-target, walrus).
    `argbounds` is the list of positional-argument type bounds from a specific call site; it seeds the
    parameters so an analysis of that call (e.g. a `return param` passthrough) can be bounded."""
    env = {}
    untracked = set()
    params = {a.arg for a in fn.args.posonlyargs + fn.args.args + fn.args.kwonlyargs}
    if fn.args.vararg:
        params.add(fn.args.vararg.arg)
    if fn.args.kwarg:
        params.add(fn.args.kwarg.arg)
    # An annotated parameter carries its declared type (trusting the annotation as a contract the caller
    # honors); an unannotated parameter is fixed by call sites and stays unbounded here. *args is always a
    # tuple and **kwargs always a dict, regardless of annotation.
    for a in fn.args.posonlyargs + fn.args.args + fn.args.kwonlyargs:
        at = _ann_sound_type(a.annotation)
        if at is not None:
            env[a.arg] = at
        else:
            untracked.add(a.arg)
    # A call site supplies concrete arguments, so each positional parameter's runtime type on this call is
    # its argument's: seed the parameter with the argument's bound (the actual argument supersedes the
    # annotation), which lets a parameter passthrough be bounded for this call.
    positional = fn.args.posonlyargs + fn.args.args
    if argbounds == "@defaults":                                # a bare call func(): every parameter takes its
        nd = len(positional) - len(fn.args.defaults)            # default value, which is its runtime value here
        defaulted = [(positional[i], fn.args.defaults[i - nd]) for i in range(nd, len(positional))]
        defaulted += [(a, d) for a, d in zip(fn.args.kwonlyargs, fn.args.kw_defaults) if d is not None]
        for a, dflt in defaulted:
            dt = _sound_type(dflt, {}, ctx, set())
            if dt is not None:
                env[a.arg] = dt
                untracked.discard(a.arg)
            di = _identity_of(dflt, {}, ctx)
            if di is not None:
                env[("@id", a.arg)] = di
    else:
        varelts = set()
        for i, ab in enumerate(argbounds or []):
            if ab is None:
                continue
            tb, idb = ab                                        # (type bound, callable-identity bound)
            if i >= len(positional):                            # an extra positional argument goes into *args, so
                if fn.args.vararg is not None and tb is not None:   # its type is an element type of that tuple
                    varelts |= tb
                continue
            if tb is not None:
                env[positional[i].arg] = tb
                untracked.discard(positional[i].arg)
            if idb is not None:
                env[("@id", positional[i].arg)] = idb
        if fn.args.vararg is not None and varelts:
            env[("@elt", fn.args.vararg.arg)] = varelts
    if fn.args.vararg:
        env[fn.args.vararg.arg] = {"tuple"}
    if fn.args.kwarg:
        env[fn.args.kwarg.arg] = {"dict"}
    for d in ast.walk(fn):                                      # a nested `def name(...)` directly in this scope
        if isinstance(d, (ast.FunctionDef, ast.AsyncFunctionDef)) and d is not fn and _enclosing_is(fn, d):
            if d.decorator_list:                                # a decorator may return any object
                untracked.add(d.name)
            else:                                               # a plain nested def names a function object, bound
                env[d.name] = {"function"}                      # before assignments that reference it; its identity
                env[("@id", d.name)] = frozenset({d})           # lets a direct call `name(...)` resolve its return
    for s in ast.walk(fn):
        if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)) and s is not fn:
            continue
        _bind_stmt(s, env, untracked, ctx)
    for nm in untracked:
        env[nm] = None                                          # top: not soundly bounded here
    if track_elements:
        for nm, items in _indexable_lists(fn, params, env, ctx, seen).items():
            env[("@elt", nm)] = set().union(*[_t for _, _t in items])   # read-only list/dict literal: any-element
            for _k, _et in items:                                       # bound, plus each index c[i] / key d['k']
                env["%s[%s]" % (nm, _k)] = _et                          # -- the slots the benchmark scores
    return env


def _module_env(mod, ctx):
    """Sound type bounds for module-level (global) variables: the union of their top-level assignments, the
    same analysis as a function's locals but over the module body and not descending into function or class
    definitions. A name some function rebinds under a `global` declaration is not soundly bounded by the
    top-level assignments alone, so it widens to UNKNOWN."""
    env = {}
    untracked = set()
    for s in _scope_stmts(mod.body):
        _bind_stmt(s, env, untracked, ctx)
    # A function that declares `global x` may rebind x; union that function's own binding of x (a sound
    # over-approximation of the reassignment) into the module bound rather than abstaining outright. An
    # unbounded reassignment makes the function's binding None, which joins to UNKNOWN -- still sound.
    for fnode in ast.walk(mod):
        if not isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        gnames = {nm for s in _scope_stmts(fnode.body) if isinstance(s, ast.Global) for nm in s.names}
        if not gnames:
            continue
        fenv = _local_env(fnode, ctx)
        for nm in gnames:
            if nm in fenv:                                      # the function actually (re)binds the global
                env[nm] = _join(env[nm], fenv[nm]) if nm in env else fenv[nm]
            elif nm not in env:                                 # declared global but bound nowhere visible here
                untracked.add(nm)
    for nm in untracked:
        env[nm] = None
    for nm, items in _indexable_lists(mod, set(), env, ctx, frozenset()).items():
        env[("@elt", nm)] = set().union(*[_t for _, _t in items])
        for _k, _et in items:
            env["%s[%s]" % (nm, _k)] = _et
    return env


def _sound_type(node, env, ctx, seen):
    """A type-name set guaranteed to contain `node`'s runtime type, or None (UNKNOWN / top)."""
    if isinstance(node, ast.Constant):
        t = _const_type(node.value)
        return {t} if t else None
    if isinstance(node, (ast.List, ast.ListComp)):
        return {"list"}
    if isinstance(node, (ast.Dict, ast.DictComp)):
        return {"dict"}
    if isinstance(node, (ast.Set, ast.SetComp)):
        return {"set"}
    if isinstance(node, ast.Tuple):
        return {"tuple"}
    if isinstance(node, ast.GeneratorExp):
        return {"generator"}
    if isinstance(node, ast.JoinedStr):
        return {"str"}
    if isinstance(node, ast.Lambda):
        return {"function"}
    if isinstance(node, ast.Name):
        if node.id in ("True", "False"):
            return {"bool"}
        if node.id == "None":
            return {"NoneType"}
        if node.id in env:
            return env[node.id]                                 # a local: its bounded type (or None)
        if node.id in ctx.funcs:
            return {"function"}                                 # a function used as a value
        if node.id in ctx.classes:
            return {"type"}                                     # a class used as a value
        return None                                             # parameter / import / builtin name: unbounded
    if isinstance(node, ast.NamedExpr):
        return _sound_type(node.value, env, ctx, seen)
    if isinstance(node, ast.UnaryOp):
        if isinstance(node.op, ast.Not):
            return {"bool"}                                     # `not x` is always a bool
        t = _sound_type(node.operand, env, ctx, seen)           # +x / -x / ~x preserve a numeric type
        if t is not None and t <= _NUMERIC:
            if isinstance(node.op, ast.Invert):
                return {"int"} if t <= {"int", "bool"} else None
            return {"int" if x == "bool" else x for x in t}
        return None
    if isinstance(node, ast.BoolOp):                            # and / or evaluate to one of the operands
        out = set()
        for v in node.values:
            out = _join(out, _sound_type(v, env, ctx, seen))
            if out is None:
                return None
        return out
    if isinstance(node, ast.Compare):
        if all(isinstance(op, (ast.Is, ast.IsNot, ast.In, ast.NotIn)) for op in node.ops):
            return {"bool"}                                     # identity / membership are always bool (each
            #                                                     link of a chain is bool, joined by implicit and)
        operands = [_sound_type(node.left, env, ctx, seen)] + \
                   [_sound_type(c, env, ctx, seen) for c in node.comparators]
        if any(o is None for o in operands):
            return None
        allowed = _EQUATABLE if all(isinstance(op, (ast.Eq, ast.NotEq)) for op in node.ops) else _ORDERABLE
        return {"bool"} if all(o <= allowed for o in operands) else None
    if isinstance(node, ast.IfExp):
        return _join(_sound_type(node.body, env, ctx, seen), _sound_type(node.orelse, env, ctx, seen))
    if isinstance(node, ast.BinOp):
        lt = _sound_type(node.left, env, ctx, seen)
        rt = _sound_type(node.right, env, ctx, seen)
        # printf-style `s % args`: a str / bytes left operand yields its own type whatever the right operand is,
        # since str.__mod__ / bytes.__mod__ return that type or raise -- they never return NotImplemented, so no
        # __rmod__ on the right can intercept (unlike `*`). So the result is bounded even when the right is not.
        # Fires only on a PROVEN str / bytes left (a literal, f-string, or inferred local), never a `s: str`
        # annotation, which is not a runtime guarantee.
        if isinstance(node.op, ast.Mod) and lt is not None and lt <= {"str", "bytes"}:
            return set(lt)
        if lt is None or rt is None:
            return None
        out = set()
        for a in lt:
            for b in rt:
                r = _binop_pair(a, b, node.op)
                if r is None:
                    return None                                 # one operand pair is unbounded
                out.add(r)
        return out
    if isinstance(node, ast.Call):
        f = node.func
        if isinstance(f, ast.Lambda):                           # a directly-called lambda: its body is the return
            if any(isinstance(a, ast.Starred) for a in node.args):
                return None
            return _callable_return(f, ctx, seen, _argbounds(node.args, env, ctx, seen))
        if isinstance(f, ast.Name):
            starred = any(isinstance(a, ast.Starred) for a in node.args)
            if f.id in env:                                     # a local/parameter holds a value; if it provably
                ids = env.get(("@id", f.id))                    # holds known callable(s), resolve the call via each
                if isinstance(ids, frozenset) and ids and not starred:
                    argb = _argbounds(node.args, env, ctx, seen)
                    out = set()
                    for cid in ids:
                        r = _callable_return(cid, ctx, seen, argb)
                        if r is None:
                            return None
                        out |= r
                    return out
                return None                                     # otherwise the call's return is unknown
            if f.id in ctx.classes:                             # class/function this name would otherwise spell
                return {f.id}                                   # constructor: an instance of the class
            if f.id in ctx.funcs:                               # a repo function call: propagate the positional
                if starred:                                     # argument bounds (types + callable identities) so a
                    return _func_return(f.id, ctx, seen)        # passthrough/callback is bounded; a bare call lets
                if not node.args and not node.keywords:         # every parameter take its default value
                    return _func_return(f.id, ctx, seen, "@defaults")
                return _func_return(f.id, ctx, seen, _argbounds(node.args, env, ctx, seen))
            if f.id in _BUILTIN_RET:
                return {_BUILTIN_RET[f.id]}                     # a fixed-return builtin
            if f.id == "abs" and len(node.args) == 1:           # abs preserves the numeric kind (complex -> float)
                t = _sound_type(node.args[0], env, ctx, seen)
                if t is not None and t <= _NUMERIC:
                    return {"int" if x in ("int", "bool") else "float" for x in t}
            if f.id == "round" and len(node.args) == 1:         # round(x) with no ndigits is int for a builtin numeric
                t = _sound_type(node.args[0], env, ctx, seen)
                if t is not None and t <= _NUMERIC:
                    return {"int"}
            if f.id in ("min", "max") and len(node.args) >= 2 and not node.keywords:   # of explicit arguments,
                out = set()                                     # min / max returns one of them unchanged, so the
                for a in node.args:                             # bound is the join of the argument bounds
                    at = None if isinstance(a, ast.Starred) else _sound_type(a, env, ctx, seen)
                    if at is None:
                        out = None
                        break
                    out |= at
                if out:
                    return out
        if isinstance(f, ast.Attribute):                        # a method on a provably-single-type receiver
            recv = _sound_type(f.value, env, ctx, seen)         # with a fixed return type
            if recv is not None and len(recv) == 1:
                rt = next(iter(recv))
                m = _STR_METHOD_RET.get(f.attr) if rt == "str" else _METHOD_RET.get(rt, {}).get(f.attr)
                if m is not None:
                    return {m}
                meth = ctx.resolve_method(rt, f.attr)           # a method called on a repo-class instance: resolve
                if meth is not None and not any(isinstance(a, ast.Starred) for a in node.args):   # its return for
                    key = rt + "." + f.attr                     # this call. A single repo-class receiver bound only
                    if key not in seen:                         # arises from a `C()` constructor (a repo-class
                        return _func_return_node(meth, ctx, seen | {key},   # annotation stays unbounded), so self
                                                 [(recv, None)] + _argbounds(node.args, env, ctx, seen))   # is rt
        return None                                             # other method / attribute / unmodeled call
    if isinstance(node, ast.Subscript):
        if isinstance(node.value, ast.Name) and not isinstance(node.slice, ast.Slice):
            elt = env.get(("@elt", node.value.id))
            if elt is not None:
                return elt                                      # a read-only list literal: c[i] is one element
        recv = _sound_type(node.value, env, ctx, seen)          # indexing a provably-str/bytes value: a str index
        if recv is not None and len(recv) == 1:                 # or slice yields str; a bytes slice yields bytes
            rt = next(iter(recv))                               # and a bytes index yields int
            if rt == "str":
                return {"str"}
            if rt == "bytes":
                return {"bytes"} if isinstance(node.slice, ast.Slice) else {"int"}
        return None
    if isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load):
        recv = _sound_type(node.value, env, ctx, seen)          # a field read on a provably-single-class instance:
        if recv is not None and len(recv) == 1:                 # its type comes from that class's field map
            b = ctx.fields_of(next(iter(recv))).get(node.attr)
            if b is not None:
                return b
    return None


_TRANSPARENT_DECO = frozenset({"staticmethod", "classmethod", "property", "cached_property",
                               "abstractmethod", "abstractproperty", "final", "override"})


def _transparent_decorator(d):
    """True if decorator `d` does not change what the function returns, so the body's return bound still
    holds. The binding and marker decorators (staticmethod, classmethod, property, cached_property, the
    abstract/typing markers) dispatch to or merely tag the wrapped function and pass its return value
    through unchanged; any decorator outside this known set may replace the return value, so it is not
    treated as transparent and the function abstains."""
    name = d.func if isinstance(d, ast.Call) else d
    if isinstance(name, ast.Attribute):
        return name.attr in _TRANSPARENT_DECO
    if isinstance(name, ast.Name):
        return name.id in _TRANSPARENT_DECO
    return False


def _func_return(name, ctx, seen, argbounds=None):
    """The sound return-type set of repo function `name` (a top-level function, used for call resolution),
    or None (UNKNOWN). `argbounds` carries the call site's positional-argument bounds. Recursion through a
    function already on the stack widens to UNKNOWN."""
    if name in seen or name not in ctx.funcs:
        return None
    return _func_return_node(ctx.funcs[name], ctx, seen | {name}, argbounds)


def _func_return_node(fn, ctx, seen, argbounds=None):
    """The sound return-type set of a function or method body `fn`, or None (UNKNOWN). A method defined in a
    class is analyzed exactly as a top-level function: its only class-specific references -- `self`, an
    unannotated parameter, and `self.attr` / `self.method(...)`, attribute accesses -- already widen to
    UNKNOWN, so the same rules over literals, numeric/sequence operations and fixed-return calls remain
    sound."""
    if any(not _transparent_decorator(d) for d in fn.decorator_list):
        return None                                             # a non-transparent decorator can replace the return
    if _has_own_yield(fn):                                      # a generator function returns a generator object
        return {"generator"}
    env = _local_env(fn, ctx, argbounds, seen)
    out = set()
    saw_value = False
    for n in ast.walk(fn):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)) and n is not fn:
            continue
        if isinstance(n, ast.Return) and n.value is not None and _enclosing_is(fn, n):
            saw_value = True
            out = _join(out, _sound_type(n.value, env, ctx, seen))
            if out is None:
                return None
    if not saw_value:
        return {"NoneType"}                                     # only bare returns / falls through
    if not _always_returns(fn.body):
        out = out | {"NoneType"}                                # a path falls through to an implicit None
    return out


def _has_own_yield(node):
    """True if `node`'s body contains a yield outside any nested function/lambda, i.e. it is a generator
    function (calling it returns a generator object rather than running the body)."""
    for c in ast.iter_child_nodes(node):
        if isinstance(c, (ast.Yield, ast.YieldFrom)):
            return True
        if isinstance(c, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        if _has_own_yield(c):
            return True
    return False


def _enclosing_is(fn, target):
    """True if `target` is lexically inside `fn` and not inside a nested function/lambda."""
    found = [False]

    def rec(node):
        for c in ast.iter_child_nodes(node):
            if c is target:
                found[0] = True
                return True
            if isinstance(c, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
                continue
            if rec(c):
                return True
        return False
    rec(fn)
    return found[0]


def _always_returns(body):
    """True if every path through `body` reaches a value-returning Return (or raises) before falling
    through, so the function never returns an implicit None. Conservative: unhandled control flow is
    treated as possibly falling through."""
    for s in body:
        if isinstance(s, ast.Return):
            return s.value is not None
        if isinstance(s, ast.Raise):
            return True
        if isinstance(s, ast.If) and s.orelse:
            if _always_returns(s.body) and _always_returns(s.orelse):
                return True
        if isinstance(s, (ast.With, ast.AsyncWith)):
            if _always_returns(s.body):
                return True
        if isinstance(s, ast.Try):
            body_ok = _always_returns(s.body) and (not s.orelse or _always_returns(s.orelse))
            handlers_ok = all(_always_returns(h.body) for h in s.handlers)
            if (body_ok and handlers_ok) or (s.finalbody and _always_returns(s.finalbody)):
                return True
    return False


def _resolve_targets(mod, target):
    """Every function or method definition `target` could name. A top-level function is matched first and
    returned alone (exact, preserving prior behavior). Otherwise every function or method whose simple name
    matches (`Class.method` -> `method`) is a candidate: a unique match resolves exactly, and an ambiguous
    one -- the same name on several methods -- yields all of them, so the caller takes the join of their
    bounds. The join is sound because the union of every candidate's bound contains the type of whichever
    definition is actually meant, whatever class it lives in."""
    if not target:
        fn = next((n for n in mod.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
        return [fn] if fn is not None else []
    simple = target.rsplit(".", 1)[-1]
    for n in mod.body:
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name == simple:
            return [n]
    return [n for n in ast.walk(mod)
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name == simple]


def _method_owner_map(mod, field_classes):
    """`id(method node) -> owning class name` for the directly-defined methods of `mod`'s field-typeable
    classes, so a method analyzed on its own can be given its receiver's type (self : that class) and resolve
    self.<field>. Sound because a field-typeable class is never subclassed, so its method runs only on an
    exact instance of it."""
    owner = {}
    for n in mod.body:
        if isinstance(n, ast.ClassDef) and n.name in field_classes:
            for m in n.body:
                if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)) and not m.decorator_list:
                    owner[id(m)] = n.name
    return owner


def infer_return_type(src, repo=None, target=None):
    """A set of Python type names guaranteed to contain the return value's runtime type, on every input,
    or None when no sound bound is established. `target` selects the function or method by name (default:
    the first top-level function). Soundness: the set is an over-approximation, so type(f(...)).__name__ is
    always a member; a function that can also trap or not terminate does not weaken this (it simply produces
    no value to type)."""
    ctx = _Ctx(src, repo)
    try:
        mod = ast.parse(src)
    except SyntaxError:
        return None
    fns = _resolve_targets(mod, target)
    if not fns:
        return None
    owner = _method_owner_map(mod, ctx.field_classes)
    out = set()
    for fn in fns:
        c = owner.get(id(fn))                                   # a method of a field-typeable class: self is it
        b = _func_return_node(fn, ctx, {fn.name}, [({c}, None)] if c else None)
        if b is None:
            return None                                         # one candidate is unbounded: the join is UNKNOWN
        out |= b
    return out


def infer_local_types(src, repo=None, target=None):
    """Sound type bounds for a function or method's local variables: each set is guaranteed to contain the
    variable's runtime type at every program point where it is bound, or None (UNKNOWN). A parameter, or a
    local whose assignment cannot be bounded, is None. Soundness rests on the union over all of a name's
    assignments being an over-approximation of its type on any path."""
    ctx = _Ctx(src, repo)
    try:
        mod = ast.parse(src)
    except SyntaxError:
        return {}
    if target is None or target.rsplit(".", 1)[-1] == "<module>":
        return {k: v for k, v in _module_env(mod, ctx).items() if isinstance(k, str)}   # module globals only
    fns = _resolve_targets(mod, target)
    if not fns:
        return {}
    owner = _method_owner_map(mod, ctx.field_classes)
    combined = {}
    for fn in fns:                                              # join each local's bound across candidates: a name
        params = {a.arg for a in fn.args.posonlyargs + fn.args.args + fn.args.kwonlyargs}   # bounded in one method
        if fn.args.vararg:                                      # and unbounded in another widens to UNKNOWN, sound
            params.add(fn.args.vararg.arg)
        if fn.args.kwarg:
            params.add(fn.args.kwarg.arg)
        c = owner.get(id(fn))                                   # a method of a field-typeable class: self is it
        for k, v in _local_env(fn, ctx, [({c}, None)] if c else None).items():
            if not isinstance(k, str) or k in params:
                continue
            combined[k] = v if k not in combined else _join(combined[k], v)
    return combined


def infer_types(src, repo=None, target=None):
    """The sound inference for a function as a dict: the return type and the local-variable types, each a
    proven over-approximation (a set of type names) or None (UNKNOWN, no sound bound)."""
    return {"return": infer_return_type(src, repo, target), "locals": infer_local_types(src, repo, target)}
