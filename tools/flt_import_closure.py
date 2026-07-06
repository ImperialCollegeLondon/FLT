#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server exposing the FLT import-closure tool.

Speaks JSON-RPC 2.0 over newline-delimited stdio (MCP stdio transport), so it
needs no third-party packages -- only the Python standard library and the
project's own ``scripts/dag_traversal.py`` (which shells out to
``lean --deps-json`` and therefore understands the ``module`` /
``public import`` syntax correctly).

Exposed tool:
    flt_import_closure(root?, leaves_only?, as_json?, write_output?)
        List every FLT file transitively imported by an FLT "boss" file,
        following only FLT.* import edges and stopping at leaf files whose
        remaining imports are all Mathlib. By default the result is also
        written to .cache/flt_import_closure.<txt|json> (alongside log.jsonl).

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/flt_import_closure.py
"""

import json
import sys
from collections import deque
from pathlib import Path

# Make scripts/ importable regardless of the current working directory.
_HERE = Path(__file__).resolve().parent
_PROJECT_ROOT = _HERE.parent
sys.path.insert(0, str(_PROJECT_ROOT / "scripts"))

from dag_traversal import DAG  # noqa: E402

DEFAULT_ROOT = "FLT.NumberField.AdeleRing"

# Persistent cache for multi-pass workflows, sitting alongside the project-root log.jsonl.
_CACHE_DIR = _PROJECT_ROOT / ".cache"

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
                "write_output": {
                    "type": "boolean",
                    "description": (
                        "Also write the result to .cache/flt_import_closure.<txt|json> "
                        "(default true). Set false to only return the text."
                    ),
                },
            },
        },
    }
]


def flt_closure(dag: DAG, root: str) -> dict[str, list[str]]:
    """Return every FLT module transitively imported by *root* (inclusive).

    Only edges into ``FLT.*`` modules are followed; Mathlib (and any other
    non-FLT) imports are ignored.  The result maps each reached FLT module to
    the sorted list of FLT modules it directly imports (empty list => a leaf
    whose remaining imports are all Mathlib).
    """
    if root not in dag.modules:
        raise KeyError(
            f"{root!r} is not an FLT module in the DAG "
            f"(expected e.g. FLT.NumberField.AdeleRing)"
        )

    reached: dict[str, list[str]] = {}
    queue: deque[str] = deque([root])
    while queue:
        name = queue.popleft()
        if name in reached:
            continue
        flt_imports = sorted(
            imp
            for imp in dag.modules[name].imports
            if imp.startswith("FLT.") and imp in dag.modules
        )
        reached[name] = flt_imports
        for imp in flt_imports:
            if imp not in reached:
                queue.append(imp)
    return reached


def _render(root: str, reached: dict[str, list[str]], leaves_only: bool, as_json: bool) -> str:
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


def _run_closure(root: str, leaves_only: bool, as_json: bool, write_output: bool) -> str:
    dag = DAG.from_directories(_PROJECT_ROOT, ["FLT"])
    reached = flt_closure(dag, root)
    text = _render(root, reached, leaves_only, as_json)

    if not write_output:
        return text

    _CACHE_DIR.mkdir(parents=True, exist_ok=True)
    out_path = _CACHE_DIR / ("flt_import_closure.json" if as_json else "flt_import_closure.txt")
    out_path.write_text(text + "\n")
    return f"{text}\n\n(written to {out_path.relative_to(_PROJECT_ROOT)})"


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
                write_output=bool(args.get("write_output", True)),
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
