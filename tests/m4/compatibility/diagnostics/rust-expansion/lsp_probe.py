#!/usr/bin/env python3
"""Bounded rust-analyzer exact-range probe for the malformed M4 attribute."""

from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from support import GateError  # noqa: E402
from support.lsp import Client, version  # noqa: E402


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "src/lib.rs"
TEXT = SOURCE.read_text(encoding="utf-8")
TOKEN = "syntax"


def token_range() -> dict[str, dict[str, int]]:
    offset = TEXT.index(TOKEN, TEXT.index("#[k::constructor"))
    line = TEXT.count("\n", 0, offset)
    character = offset - TEXT.rfind("\n", 0, offset) - 1
    return {
        "start": {"line": line, "character": character},
        "end": {"line": line, "character": character + len(TOKEN)},
    }


def main() -> None:
    analyzer = version()
    client = Client(ROOT, {"CARGO_TARGET_DIR": "/tmp/krs-m4-diagnostics-ra-target"})
    try:
        client.request("initialize", {
            "processId": None, "rootUri": ROOT.as_uri(),
            "capabilities": {
                "workspace": {"configuration": True},
                "window": {"workDoneProgress": True},
                "textDocument": {"diagnostic": {}},
            },
        })
        client.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
        client.wait_for_priming()
        client.send({
            "jsonrpc": "2.0", "method": "textDocument/didOpen",
            "params": {"textDocument": {
                "uri": SOURCE.as_uri(), "languageId": "rust", "version": 1, "text": TEXT,
            }},
        })
        report = client.request(
            "textDocument/diagnostic", {"textDocument": {"uri": SOURCE.as_uri()}}, timeout=90
        )
        diagnostics = report.get("items", []) if report else []
        matching = [
            diagnostic for diagnostic in diagnostics
            if "missing required argument `sort = ...`" in diagnostic.get("message", "")
        ]
        expected = token_range()
        if len(matching) != 1 or matching[0].get("range") != expected:
            raise GateError(f"expected one exact authored `{TOKEN}` range {expected}, got {matching!r}")
        print(json.dumps({"rust_analyzer": analyzer, "range": expected, "token": TOKEN}, sort_keys=True))
    finally:
        client.close()


if __name__ == "__main__":
    main()
