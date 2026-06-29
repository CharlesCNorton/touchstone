"""An MCP (Model Context Protocol) server exposing touchstone as tools, so a model can call the verifier in
its own loop. Speaks MCP over stdio (newline-delimited JSON-RPC) using only the standard library.

    python -m touchstone.mcp        # the server command an MCP client launches
    touchstone-mcp                  # the same, via the installed console script

The tools are check, prove, verify_change, synthesize_spec, and scan; each returns the verdict, with the
counterexample and execution trace on a REFUTED."""
import json
import sys

from . import _impl as t


def _server_version():
    """The installed package version for the MCP `serverInfo` (the spec requires it), with a stable
    fallback when running from an uninstalled source tree."""
    try:
        from importlib.metadata import version
        return version("touchstone-prover")
    except Exception:
        return "0+unknown"


_TOOLS = [
    {"name": "check",
     "description": "Prove a Python function is trap-free (no reachable IndexError, KeyError, division by "
                    "zero, or failing assert) for all inputs. Returns PROVED, REFUTED (with a counterexample "
                    "and execution trace when one is available), or UNKNOWN with a reason.",
     "inputSchema": {"type": "object",
                     "properties": {"source": {"type": "string", "description": "the function's source"},
                                    "requires": {"type": "string", "description": "optional precondition"},
                                    "func": {"type": "string", "description": "function name (default: first)"}},
                     "required": ["source"]}},
    {"name": "prove",
     "description": "Prove a postcondition over the parameters and `result` holds for all inputs of a "
                    "function. Returns PROVED, REFUTED with a counterexample and execution trace, or UNKNOWN "
                    "with a reason.",
     "inputSchema": {"type": "object",
                     "properties": {"source": {"type": "string"},
                                    "ensures": {"type": "string", "description": "the postcondition"},
                                    "requires": {"type": "string"}, "func": {"type": "string"}},
                     "required": ["source", "ensures"]}},
    {"name": "verify_change",
     "description": "Confirm a proposed change (before -> after) preserves the function's properties: its "
                    "@ensure contract if present (or an explicit `ensures`), else behavioral equivalence. "
                    "Returns PROVED, or REFUTED with the input where it breaks.",
     "inputSchema": {"type": "object",
                     "properties": {"before": {"type": "string"}, "after": {"type": "string"},
                                    "ensures": {"type": "string"}, "func": {"type": "string"}},
                     "required": ["before", "after"]}},
    {"name": "synthesize_spec",
     "description": "Propose a contract (a precondition and the postconditions) the function provably "
                    "satisfies, as a sound starting specification.",
     "inputSchema": {"type": "object",
                     "properties": {"source": {"type": "string"}, "func": {"type": "string"}},
                     "required": ["source"]}},
    {"name": "scan",
     "description": "Point Touchstone at a target -- a git/GitHub repo URL, a .py file URL, or a local "
                    "directory or .py file -- and get a classified trap-freedom report (per function: a "
                    "reachable ZeroDivisionError / IndexError / KeyError / TypeError / failing assert / "
                    "uncaught raise, with a counterexample). Symbolic by default and the fetched code is never "
                    "executed -- findings come back unconfirmed. Set execute=true to replay each finding in an "
                    "isolated sandbox: it confirms the actual exception, classifies it as a genuine bug or "
                    "intended input validation, and returns a runnable repro test.",
     "inputSchema": {"type": "object",
                     "properties": {"target": {"type": "string",
                                               "description": "a repo URL, a .py file URL, or a local path"},
                                    "execute": {"type": "boolean",
                                                "description": "replay each finding in the sandbox to confirm "
                                                               "and classify it (default false)"}},
                     "required": ["target"]}},
]


def _verdict_text(v, src=None, repo=None):
    """A verdict as model-readable text. A REFUTED verdict carries its counterexample and, when the inputs are
    replayable, the execution trace from explain(). `src` is the function the verdict is about."""
    out = "%s: %s" % (v.status, v.prop)
    if v.counterexample:
        out += "\ncounterexample: %s" % v.counterexample
    if v.reason:
        out += "\nreason: %s" % v.reason
    if v.status == t.REFUTED and src is not None and getattr(v, "counterexample_inputs", None):
        try:
            ev = t.explain(v, src, repo or {})
            if getattr(ev, "trace", None):
                out += "\ntrace:\n" + ev.trace
        except Exception:
            pass                                             # the trace is a best-effort enrichment, never required
    return out


def _scan_text(rep):
    """A scan report as model-readable text: the headline counts, then one line per finding (classification,
    confirmed exception, counterexample), with a runnable repro test for each replayable finding."""
    mode = "executed in an isolated sandbox" if rep["executed"] else "symbolic only, code not run"
    lines = ["scan of %s (%s, %s): %d functions -- %d proved, %d refuted, %d unknown"
             % (rep["target"], "fetched" if rep["fetched"] else "local", mode,
                rep["functions"], rep["proved"], rep["refuted"], rep["unknown"])]
    if rep["executed"]:
        lines.append("classified: %d bug(s), %d suspected, %d input-validation, %d unconfirmed"
                     % (rep["bugs"], rep.get("suspected", 0), rep["input_validation"], rep["unconfirmed"]))
    for f in rep["findings"]:
        line = "[%s] %s -- %s" % (f["classification"], f["location"], f["label"])
        if f["exception"]:
            line += " | exception: %s" % f["exception"]
        if f["counterexample"]:
            line += " | counterexample: %s" % f["counterexample"]
        lines.append(line)
        if f["repro"]:
            lines.append("repro:\n" + f["repro"])
    if not rep["findings"]:
        lines.append("no reachable traps found"
                     + ("" if rep["executed"] else " (pass execute=true to confirm with the sandbox)"))
    return "\n".join(lines)


def call_tool(name, args):
    """Run a tool by name with its argument dict and return the text result; the testable core of the server."""
    if name == "scan":
        return _scan_text(t.scan(args["target"], execute=bool(args.get("execute", False))))
    if name == "check":
        return _verdict_text(t.check(args["source"], requires=args.get("requires", "True"),
                                     target=args.get("func")), args["source"])
    if name == "prove":
        return _verdict_text(t.prove(args["source"], args["ensures"], requires=args.get("requires", "True"),
                                     target=args.get("func")), args["source"])
    if name == "verify_change":
        return _verdict_text(t.verify_change(args["before"], args["after"],
                                             ensures=args.get("ensures"), func=args.get("func")), args["after"])
    if name == "synthesize_spec":
        return json.dumps(t.synthesize_spec(args["source"], func=args.get("func")))
    raise ValueError("unknown tool: %s" % name)


def _write(out, obj):
    out.write(json.dumps(obj).encode("utf-8") + b"\n")
    out.flush()


def main(argv=None):
    """Run the MCP server, reading newline-delimited JSON-RPC requests from stdin and writing responses to
    stdout until the stream closes."""
    out = sys.stdout.buffer
    for raw in sys.stdin.buffer:
        line = raw.strip()
        if not line:
            continue
        try:
            msg = json.loads(line.decode("utf-8"))
        except ValueError:
            continue
        if not isinstance(msg, dict):                        # a non-object line (a bare number/string, or a
            continue                                         # JSON-RPC batch array) is not a request: ignore it
        method, mid, params = msg.get("method"), msg.get("id"), msg.get("params") or {}
        if method == "initialize":
            _write(out, {"jsonrpc": "2.0", "id": mid, "result": {
                "protocolVersion": "2024-11-05", "capabilities": {"tools": {}},
                "serverInfo": {"name": "touchstone", "version": _server_version()}}})
        elif method == "tools/list":
            _write(out, {"jsonrpc": "2.0", "id": mid, "result": {"tools": _TOOLS}})
        elif method == "tools/call":
            try:
                text = call_tool(params.get("name"), params.get("arguments") or {})
                _write(out, {"jsonrpc": "2.0", "id": mid,
                             "result": {"content": [{"type": "text", "text": text}], "isError": False}})
            except Exception as e:
                _write(out, {"jsonrpc": "2.0", "id": mid,
                             "result": {"content": [{"type": "text", "text": "%s: %s" % (type(e).__name__, e)}],
                                        "isError": True}})
        elif method == "ping":
            _write(out, {"jsonrpc": "2.0", "id": mid, "result": {}})
        elif method and method.startswith("notifications/"):
            pass                                             # initialized / cancelled etc. take no response
        elif mid is not None:
            _write(out, {"jsonrpc": "2.0", "id": mid,
                         "error": {"code": -32601, "message": "method not found: %s" % method}})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
