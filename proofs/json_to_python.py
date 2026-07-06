#!/usr/bin/env python3
"""Mechanically translate a Rocq/Coq JSON extraction (Extraction Language JSON) into Python, so the
verified VC generator, interval operators, and division encoding run as the exact code proven in Rocq
rather than a hand transcription. The input is the MiniML abstract syntax the same extraction pipeline
lowers to OCaml; this walks that syntax with no semantic interpretation -- every inductive constructor
becomes a tagged tuple, every match a tag dispatch, every function a curried def -- so the translation
is a faithful structural map, auditable by inspection and checked against the OCaml extraction by the
engine's differential audits.

Usage:  python json_to_python.py <module.json> <ModuleName>   > out.py

Representation:
  * a constructor  C of t1 * t2   builds the tuple  ("C", v1, v2)  ;  a nullary C builds ("C",).
  * a match on x branches on x[0]; a constructor pattern binds its fields from x[1], x[2], ...
  * every function is curried (one argument at a time), so a partial application is a closure, exactly
    as in the MiniML source; `f a b` lowers to f(a)(b).
"""
import json
import keyword
import sys


def sanitize(name):
    """A MiniML identifier (a', x'0, a Coq keyword) as a distinct, valid Python identifier. Constructor
    names are never sanitized -- they are string tags, not identifiers."""
    if name == "_":
        return "_"
    s = name.replace("'", "_prime")
    s = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in s)
    if not s or not (s[0].isalpha() or s[0] == "_"):
        s = "v_" + s
    if keyword.iskeyword(s):
        s = s + "_"
    return s


def unwrap(node):
    """An expr:lambda with no parameters is a vacuous wrapper (Coq spells a point-free value `f x` this
    way); it denotes its body. Peel such wrappers so a 0-argument lambda is never given a parameter."""
    while node.get("what") == "expr:lambda" and not node["argnames"]:
        node = node["body"]
    return node


class Translator:
    def __init__(self):
        self.tmp = 0
        self.lam = 0

    def fresh(self, p="_t"):
        self.tmp += 1
        return "%s%d" % (p, self.tmp)

    # ----- expression position: return a single Python expression string, hoisting any match/let in
    #       `node` into `out` as statements that compute a temporary at indentation `ind`. -----
    def expr(self, node, out, ind):
        node = unwrap(node)
        w = node["what"]
        if w == "expr:rel":
            return sanitize(node["name"])
        if w == "expr:global":
            return sanitize(node["name"])
        if w == "expr:constructor":
            args = [self.expr(a, out, ind) for a in node["args"]]
            inner = ", ".join([repr(node["name"])] + args)
            return "(" + inner + ",)" if not args else "(" + inner + ")"
        if w == "expr:apply":
            s = self.expr(node["func"], out, ind)
            for a in node["args"]:
                s = "%s(%s)" % (s, self.expr(a, out, ind))
            return s
        if w == "expr:lambda":
            return self.lambda_expr(node, out, ind)
        if w in ("expr:case", "expr:let"):                # hoist into statements computing a temp
            res = self.fresh()
            out.append("%s%s = None" % (ind, res))
            self.stmt(node, out, ind, res)
            return res
        if w == "expr:dummy":
            return "None"
        raise NotImplementedError("expr " + w)

    def lambda_expr(self, node, out, ind):
        """A lambda in expression position: emit a curried nested def and return its name."""
        self.lam += 1
        name = "_lam%d" % self.lam
        body = []
        self.curried_def(name, node["argnames"], node["body"], body, ind)
        out.extend(body)
        return name

    def curried_def(self, name, argnames, body_node, out, ind):
        """def name(a1): def _k(a2): ... return <body>  -- one parameter per nesting level, so the curried
        function matches the MiniML source and a partial application is a closure."""
        args = [sanitize(a) for a in argnames] or ["_unit"]
        for i, a in enumerate(args):
            out.append("%sdef %s(%s):" % (ind, name if i == 0 else "_k", a))
            ind = ind + "    "
        self.stmt(body_node, out, ind, None)             # innermost body returns the result
        for _ in range(len(args) - 1):                   # each enclosing def returns the next closure
            ind = ind[:-4]
            out.append("%sreturn _k" % ind)

    # ----- statement position: emit statements computing `node`; the result is `return`ed (retvar is
    #       None) or assigned to `retvar`. Handles match and let without an expression form. -----
    def stmt(self, node, out, ind, retvar):
        node = unwrap(node)
        w = node["what"]
        if w == "expr:case":
            scr = self.expr(node["expr"], out, ind)
            st = self.fresh()
            out.append("%s%s = %s" % (ind, st, scr))
            for i, case in enumerate(node["cases"]):
                self.case_branch(case, st, out, ind, retvar, first=(i == 0))
            return
        if w == "expr:let":
            nm = sanitize(node.get("name", "_let"))
            val = self.expr(node["nameval"] if "nameval" in node else node["value"], out, ind)
            out.append("%s%s = %s" % (ind, nm, val))
            self.stmt(node["body"], out, ind, retvar)
            return
        e = self.expr(node, out, ind)
        out.append("%s%s" % (ind, "return " + e if retvar is None else "%s = %s" % (retvar, e)))

    def case_branch(self, case, scrut, out, ind, retvar, first):
        pat = case["pat"]
        w = pat["what"]
        if w == "pat:wild":
            out.append("%selse:" % ind)
            self.stmt(case["body"], out, ind + "    ", retvar)
            return
        if w == "pat:rel":                                # a variable pattern: binds the whole scrutinee
            kw = "if True:" if first else "else:"
            out.append("%s%s" % (ind, kw))
            out.append("%s    %s = %s" % (ind, sanitize(pat["name"]), scrut))
            self.stmt(case["body"], out, ind + "    ", retvar)
            return
        # pat:constructor
        cond = "%s[0] == %r" % (scrut, pat["name"])
        out.append("%s%s %s:" % (ind, "if" if first else "elif", cond))
        bind = ind + "    "
        for j, a in enumerate(pat["argnames"]):
            if a != "_":
                out.append("%s%s = %s[%d]" % (bind, sanitize(a), scrut, j + 1))
        self.stmt(case["body"], out, bind, retvar)

    # ----- top-level declarations -----
    def decl(self, d, out):
        w = d["what"]
        if w in ("decl:ind", "decl:type"):
            return                                        # constructors are tagged tuples; no type needed
        if w == "decl:term":
            self.toplevel(sanitize(d["name"]), d["value"], out)
            return
        if w == "decl:fixgroup":
            for it in d["fixlist"]:
                self.toplevel(sanitize(it["name"]), it["value"], out)
            return
        raise NotImplementedError("decl " + w)

    def toplevel(self, name, value, out):
        value = unwrap(value)
        if value["what"] == "expr:lambda":
            self.curried_def(name, value["argnames"], value["body"], out, "")
            out.append("")
            return
        pre = []
        e = self.expr(value, pre, "")                     # a point-free value (a partial application)
        out.extend(pre)
        out.append("%s = %s" % (name, e))
        out.append("")

    def module(self, doc):
        out = ["# Generated by proofs/json_to_python.py from a Rocq JSON extraction. Do not edit by hand.",
               "# Every function below is the structural image of the verified MiniML source.", ""]
        for d in doc["declarations"]:
            self.decl(d, out)
        return "\n".join(out)


def main():
    doc = json.load(open(sys.argv[1], encoding="utf-8"))
    sys.stdout.write(Translator().module(doc))


if __name__ == "__main__":
    main()
