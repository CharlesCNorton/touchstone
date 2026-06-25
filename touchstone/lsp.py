"""A Language Server that surfaces touchstone verdicts inline in an editor. On open and save it verifies each
top-level function -- its @ensure contract when present, otherwise trap freedom -- and publishes one
diagnostic per function (a refutation with its counterexample, an UNKNOWN with its reason, or a PROVED).
Speaks the Language Server Protocol over stdio (Content-Length-framed JSON-RPC) using only the standard
library.

    python -m touchstone.lsp        # the server command an editor launches
    touchstone-lsp                  # the same, via the installed console script

Diagnostics refresh on open and save, not per keystroke (verification runs Z3/cvc5)."""
import ast
import json
import sys

from .core import PROVED, REFUTED, UNKNOWN, Verdict
from .engines import check, load_module, verify_contracts, synthesize_spec
from .diagnostics import classify_unknown

_ERROR, _INFORMATION, _HINT = 1, 3, 4                         # LSP DiagnosticSeverity


def _read_message(stream):
    """Read one Content-Length-framed JSON-RPC message from a binary stream, or None at end of input."""
    length = 0
    while True:
        line = stream.readline()
        if not line:
            return None
        text = line.decode("ascii", "replace").strip()
        if text == "":
            break
        if ":" in text:
            key, val = text.split(":", 1)
            if key.strip().lower() == "content-length":
                length = int(val.strip())
    if length <= 0:
        return None
    body = b""
    while len(body) < length:                                # read exactly `length` bytes
        chunk = stream.read(length - len(body))
        if not chunk:
            return None
        body += chunk
    return json.loads(body.decode("utf-8"))


def _write_message(stream, obj):
    data = json.dumps(obj).encode("utf-8")
    stream.write(b"Content-Length: " + str(len(data)).encode("ascii") + b"\r\n\r\n" + data)
    stream.flush()


def _has_ensure(fn):
    """Whether a function carries an @ensure contract decorator (so it is verified against it)."""
    for dec in fn.decorator_list:
        f = dec.func if isinstance(dec, ast.Call) else dec
        if isinstance(f, ast.Name) and f.id == "ensure":
            return True
    return False


def _message(v):
    if v.status == REFUTED:
        m = "touchstone REFUTED: " + (v.prop or "property")
        if v.counterexample:
            m += "  [counterexample: %s]" % v.counterexample
        elif v.reason:
            m += "  [%s]" % v.reason
        return m
    if v.status == PROVED:
        return "touchstone PROVED: " + (v.prop or "property")
    cat = classify_unknown(v.reason)                             # budget / approximation / unmodeled
    base = "touchstone UNKNOWN: " + (v.reason or "not decided")
    return base + ("  [%s]" % cat if cat != "none" else "")


def _severity(status):
    return {REFUTED: _ERROR, PROVED: _INFORMATION}.get(status, _HINT)


def diagnostics(text):
    """Verify every top-level function in `text` and return a list of LSP Diagnostic dicts. A function
    with an @ensure contract is checked against it; any other is checked for trap freedom. Sibling
    functions in the document are inlined (load_module), so a call into a same-file helper is followed."""
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return []                                            # leave syntax errors to the editor's Python tooling
    try:
        repo = load_module(text)
    except Exception:
        repo = {}
    out = []
    for node in tree.body:
        if not isinstance(node, ast.FunctionDef):
            continue
        src = ast.unparse(node)                              # verify each function from its own source, so the
        try:                                                 # other functions' traps do not leak into this verdict;
            if _has_ensure(node):                            # the sibling repo still resolves a call into a same-file
                v = verify_contracts(src, repo=repo)         # helper
            else:
                v = check(src, repo=repo, prop="trap freedom")
        except Exception as e:                               # an unmodeled construct is a withheld verdict, not a crash
            v = Verdict(UNKNOWN, "trap freedom", node.name, "lsp",
                        reason="%s: %s" % (type(e).__name__, e))
        line = node.lineno - 1                               # AST is 1-based by line, 0-based by column; LSP is 0-based
        col = node.col_offset + len("def ")                  # point at the function name, just past `def `
        out.append({
            "range": {"start": {"line": line, "character": col},
                      "end": {"line": line, "character": col + len(node.name)}},
            "severity": _severity(v.status),
            "source": "touchstone",
            "message": _message(v),
        })
    return out


def _code_actions(text, uri, rng):
    """CodeActions for the contract-free functions overlapping `rng`: synthesize a contract each provably
    satisfies (synthesize_spec) and offer to insert it as @require / @ensure decorators above the def. A
    function that already carries an @ensure, or for which nothing is proved, yields no action."""
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return []
    try:
        repo = load_module(text)
    except Exception:
        repo = {}
    start = (rng.get("start") or {}).get("line", 0)
    end = (rng.get("end") or {}).get("line", start)
    actions = []
    for node in tree.body:
        if not isinstance(node, ast.FunctionDef) or _has_ensure(node):
            continue
        fstart, fend = node.lineno - 1, (node.end_lineno or node.lineno) - 1
        if fend < start or fstart > end:                        # this function does not overlap the requested range
            continue
        try:
            spec = synthesize_spec(text, func=node.name, repo=repo)
        except Exception:
            continue
        if spec.get("requires", "True") == "True" and not spec.get("ensures"):
            continue                                            # nothing proved to assert
        indent = " " * node.col_offset
        lines = []
        if spec["requires"] != "True":
            lines.append('%s@require("%s")' % (indent, spec["requires"]))
        lines += ['%s@ensure("%s")' % (indent, e) for e in spec["ensures"]]
        at = (node.decorator_list[0].lineno - 1) if node.decorator_list else fstart
        edit = {"range": {"start": {"line": at, "character": 0}, "end": {"line": at, "character": 0}},
                "newText": "\n".join(lines) + "\n"}
        actions.append({"title": "touchstone: insert proven contract for %s" % node.name,
                        "kind": "refactor.rewrite", "edit": {"changes": {uri: [edit]}}})
    return actions


def _publish(out, uri, text):
    _write_message(out, {"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
                         "params": {"uri": uri, "diagnostics": diagnostics(text)}})


def main(argv=None):
    """Run the language server, reading requests from stdin and writing responses and diagnostic
    notifications to stdout, until the client sends exit (or the stream closes)."""
    stdin, stdout = sys.stdin.buffer, sys.stdout.buffer
    docs = {}
    while True:
        msg = _read_message(stdin)
        if msg is None:
            return 0
        method, mid, params = msg.get("method"), msg.get("id"), msg.get("params") or {}
        if method == "initialize":
            _write_message(stdout, {"jsonrpc": "2.0", "id": mid, "result": {
                "capabilities": {"textDocumentSync": {"openClose": True, "change": 1, "save": True},
                                 "codeActionProvider": True},
                "serverInfo": {"name": "touchstone"},
            }})
        elif method == "textDocument/didOpen":
            doc = params["textDocument"]
            docs[doc["uri"]] = doc["text"]
            _publish(stdout, doc["uri"], doc["text"])
        elif method == "textDocument/didChange":
            uri = params["textDocument"]["uri"]
            changes = params.get("contentChanges") or []
            if changes:                                      # full sync (change=1): the last change is the whole text
                docs[uri] = changes[-1]["text"]
        elif method == "textDocument/didSave":
            uri = params["textDocument"]["uri"]
            text = params.get("text")
            if text is None:
                text = docs.get(uri, "")
            docs[uri] = text
            _publish(stdout, uri, text)
        elif method == "textDocument/codeAction":
            uri = params.get("textDocument", {}).get("uri")
            text = docs.get(uri, "")
            _write_message(stdout, {"jsonrpc": "2.0", "id": mid,
                                    "result": _code_actions(text, uri, params.get("range") or {})})
        elif method == "textDocument/didClose":
            uri = params["textDocument"]["uri"]
            docs.pop(uri, None)
            _write_message(stdout, {"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
                                    "params": {"uri": uri, "diagnostics": []}})
        elif method == "shutdown":
            _write_message(stdout, {"jsonrpc": "2.0", "id": mid, "result": None})
        elif method == "exit":
            return 0
        elif mid is not None:                                # an unsupported request still needs a response
            _write_message(stdout, {"jsonrpc": "2.0", "id": mid, "result": None})


if __name__ == "__main__":
    raise SystemExit(main())
