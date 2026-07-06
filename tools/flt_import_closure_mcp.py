#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server exposing the FLT import-closure tool.

Speaks JSON-RPC 2.0 over newline-delimited stdio (MCP stdio transport), so it
needs no third-party packages -- only the Python standard library and the
project's own ``scripts/dag_traversal.py`` (which shells out to
``lean --deps-json``).

Exposed tool:
    flt_import_closure(root?, leaves_only?, as_json?)
        List every FLT file transitively imported by an FLT "boss" file,
        following only FLT.* import edges and stopping at leaf files whose
        remaining imports are all Mathlib.

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/flt_import_closure_mcp.py
"""

import json
import sys
from pathlib import Path

# Reuse the closure logic and DAG builder from the sibling CLI tool.
_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))
sys.path.insert(0, str(_HERE.parent / "scripts"))

from dag_traversal import DAG  # noqa: E402
from flt_import_closure import DEFAULT_ROOT, flt_closure  # noqa: E402

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "flt-import-closure", "version": "1.0.0"}

TOOLS = [
    {
        "name": "flt_import_closure",
        "description": (
            "List all FLT files transitively required by an FLT 'boss' file "
            "(default FLT.NumberField.AdeleRing, which contains the boss "
            "theorems NumberField.AdeleRing.cocompact and .discrete). Walks the "
            "import graph following only FLT.* edges and stops at leaf files "
            "whose remaining imports are all Mathlib."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "root": {
                    "type": "string",
                    "description": f"Root FLT module (default: {DEFAULT_ROOT}).",
                },
                "leaves_only": {
                    "type": "boolean",
                    "description": "Return only leaf FLT files (imports are all Mathlib).",
                },
                "as_json": {
                    "type": "boolean",
                    "description": "Return a structured JSON payload instead of text.",
                },
            },
        },
    }
]


def _run_closure(root: str, leaves_only: bool, as_json: bool) -> str:
    dag = DAG.from_directories(_HERE.parent, ["FLT"])
    reached = flt_closure(dag, root)
    leaves = sorted(name for name, imps in reached.items() if not imps)
    non_leaves = sorted(name for name, imps in reached.items() if imps)

    if as_json:
        return json.dumps({
            "root": root,
            "count": len(reached),
            "leaf_count": len(leaves),
            "modules": sorted(reached),
            "leaves": leaves,
            "imports": {k: reached[k] for k in sorted(reached)},
        }, indent=2)

    if leaves_only:
        lines = [f"# {len(leaves)} leaf FLT files (all remaining imports are Mathlib)"]
        lines += leaves
        return "\n".join(lines)

    lines = [
        f"Root: {root}",
        f"Total FLT files required: {len(reached)} "
        f"({len(leaves)} leaves, {len(non_leaves)} intermediate)",
        "",
        "All required FLT files (alphabetical):",
    ]
    for name in sorted(reached):
        marker = "  (leaf)" if not reached[name] else ""
        lines.append(f"  {name}{marker}")
    return "\n".join(lines)


def _handle(msg: dict) -> dict | None:
    """Return a JSON-RPC response dict, or None for notifications."""
    method = msg.get("method")
    msg_id = msg.get("id")

    # Notifications (no id) get no response.
    if msg_id is None and method != "initialize":
        return None

    if method == "initialize":
        return _ok(msg_id, {
            "protocolVersion": PROTOCOL_VERSION,
            "capabilities": {"tools": {}},
            "serverInfo": SERVER_INFO,
        })

    if method == "tools/list":
        return _ok(msg_id, {"tools": TOOLS})

    if method == "tools/call":
        params = msg.get("params") or {}
        name = params.get("name")
        args = params.get("arguments") or {}
        if name != "flt_import_closure":
            return _err(msg_id, -32602, f"Unknown tool: {name}")
        try:
            text = _run_closure(
                root=args.get("root") or DEFAULT_ROOT,
                leaves_only=bool(args.get("leaves_only", False)),
                as_json=bool(args.get("as_json", False)),
            )
            return _ok(msg_id, {"content": [{"type": "text", "text": text}]})
        except KeyError as e:
            return _ok(msg_id, {
                "content": [{"type": "text", "text": str(e)}],
                "isError": True,
            })
        except Exception as e:  # noqa: BLE001 - surface any failure to the client
            return _ok(msg_id, {
                "content": [{"type": "text", "text": f"error: {e}"}],
                "isError": True,
            })

    return _err(msg_id, -32601, f"Method not found: {method}")


def _ok(msg_id, result):
    return {"jsonrpc": "2.0", "id": msg_id, "result": result}


def _err(msg_id, code, message):
    return {"jsonrpc": "2.0", "id": msg_id, "error": {"code": code, "message": message}}


def main() -> int:
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        response = _handle(msg)
        if response is not None:
            sys.stdout.write(json.dumps(response) + "\n")
            sys.stdout.flush()
    return 0


if __name__ == "__main__":
    sys.exit(main())
