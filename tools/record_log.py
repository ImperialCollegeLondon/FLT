#!/usr/bin/env python3
"""
Zero-dependency stdio MCP server exposing the pass-note logger.

Speaks JSON-RPC 2.0 over newline-delimited stdio (MCP stdio transport), so it
needs no third-party packages -- only the Python standard library.

Exposed tool:
    record_pass_note(note, log)
        Append a pass note to a jsonl log WITHOUT running Lean. Writes the same
        log envelope shape as `call_repl` (with `file` and `result` null) so the
        log stays uniform for any consumer reading the `pass_note` field.

Run standalone for a quick protocol smoke test:
    echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | tools/record_log.py
"""

import datetime
import json
import os
import sys

PROTOCOL_VERSION = "2024-11-05"
SERVER_INFO = {"name": "record-log", "version": "1.0.0"}

TOOLS = [
    {
        "name": "record_pass_note",
        "description": (
            "Record a pass note to the log WITHOUT running Lean. Use this at the "
            "end of a pass that produced no compilable `.lean` change -- in "
            "particular a BLUEPRINT pass, which writes only `.tex` and therefore "
            "has nothing for `call_repl` to compile. It writes the SAME log "
            "envelope shape as `call_repl` (with `file` and `result` null), so "
            "`log.jsonl` stays uniform and any consumer can read the `pass_note` "
            "field the same way regardless of which tool wrote it."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "note": {
                    "type": "string",
                    "description": (
                        "Non-empty. The agent's decision / rationale / handoff "
                        "for this pass -- what was done, persistent failure "
                        "modes, and what the next pass should prioritise."
                    ),
                },
                "log": {
                    "type": "string",
                    "description": "Absolute path to the log jsonl file.",
                },
            },
            "required": ["note", "log"],
        },
    }
]


def _record_pass_note(note: str, log: str) -> str:
    """Append the pass-note envelope to `log`, or return an error string."""
    if not note or not note.strip():
        return "Error: `note` must be a non-empty string."
    if not os.path.isabs(log):
        return f"Error: `log` must be an absolute path. Received: '{log}'"
    if not os.path.isfile(log):
        return f"Error: the path '{log}' does not exist. Please check the `log` parameter."

    entry = {
        "ts": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "file": None,
        "result": None,
        "pass_note": note,
    }
    with open(log, "a") as f:
        f.write(json.dumps(entry) + "\n")
    return "pass_note recorded to log."


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
        if name != "record_pass_note":
            return _err(msg_id, -32602, f"Unknown tool: {name}")
        try:
            text = _record_pass_note(
                note=args.get("note", ""),
                log=args.get("log", ""),
            )
            return _ok(msg_id, {"content": [{"type": "text", "text": text}]})
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
