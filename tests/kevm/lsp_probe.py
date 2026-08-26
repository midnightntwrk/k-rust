#!/usr/bin/env python3
"""Focused rust-analyzer qualification for the readable KEVM slice."""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys

KWASM_TOOLS = Path(__file__).resolve().parents[1] / "kwasm"
sys.path.insert(0, os.fspath(KWASM_TOOLS))
import lsp_probe as support  # noqa: E402


ROOT = Path(__file__).resolve().parents[2] / "semantics/kevm"
SOURCE = ROOT / "src/lib.rs"
TEXT = SOURCE.read_text(encoding="utf-8")
LINES = TEXT.splitlines()
support.ROOT = ROOT
support.SOURCE = SOURCE
support.TEXT = TEXT
support.LINES = LINES


def main() -> None:
    version = subprocess.run(
        ["rust-analyzer", "--version"],
        check=True,
        text=True,
        capture_output=True,
        timeout=10,
        env={**os.environ, "RUSTUP_TOOLCHAIN": "stable"},
    ).stdout.strip()
    client = support.Client()
    try:
        client.request(
            "initialize",
            {
                "processId": None,
                "rootUri": ROOT.as_uri(),
                "capabilities": {
                    "workspace": {"configuration": True},
                    "window": {"workDoneProgress": True},
                    "textDocument": {
                        "definition": {"linkSupport": True},
                        "hover": {"contentFormat": ["markdown", "plaintext"]},
                        "diagnostic": {},
                    },
                },
            },
        )
        client.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
        client.wait_for_priming()
        client.send(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": SOURCE.as_uri(),
                        "languageId": "rust",
                        "version": 1,
                        "text": TEXT,
                    }
                },
            }
        )
        report = client.request(
            "textDocument/diagnostic",
            {"textDocument": {"uri": SOURCE.as_uri()}},
            timeout=90,
        )
        diagnostics = report.get("items", []) if report else []
        assert not diagnostics, diagnostics

        probes = [
            (
                "program constructor",
                "program: Program::ProgramCons(Operation::Push { width, value }, tail)",
                "ProgramCons",
                "    ProgramCons { head: OpCode, tail: EvmProgram },",
                0,
            ),
            (
                "stack result constructor",
                "word_stack: Stack::StackCons(crate::Chop(value), stack)",
                "StackCons",
                "    StackCons { head: Int, tail: WordStack },",
                0,
            ),
            (
                "gas function",
                "k: [crate::Charge(Operation::Push { width, value }, gas), ..]",
                "Charge",
                "pub struct Charge {",
                0,
            ),
            (
                "configuration target",
                "    for Machine;",
                "Machine",
                "pub struct Machine {",
                0,
            ),
            (
                "width binding",
                "pc: int::add(pc, int::add(width, 1))",
                "width",
                "program: Program::ProgramCons(Operation::Push { width, value }, tail)",
                2,
            ),
            (
                "exception constructor",
                "status_code: Status::OutOfGas()",
                "OutOfGas",
                "    OutOfGas(),",
                0,
            ),
        ]
        counts: dict[str, int] = {}
        for name, fragment, needle, target_fragment, target_occurrence in probes:
            at = support.position(fragment, needle)
            found = support.locations(
                client.request("textDocument/definition", support.params(at))
            )
            counts[name] = len(found)
            assert found, (name, at, found)
            expected_line = [
                index for index, line in enumerate(LINES) if target_fragment in line
            ][target_occurrence]
            assert any(
                uri == SOURCE.as_uri() and target["start"]["line"] == expected_line
                for uri, target in found
            ), (name, found, expected_line)
            hover = client.request("textDocument/hover", support.params(at))
            assert support.meaningful_hover(hover), (name, at, hover)

        print(
            json.dumps(
                {
                    "rust_analyzer": version,
                    "diagnostics": 0,
                    "definitions_and_hovers": counts,
                },
                sort_keys=True,
            )
        )
    finally:
        client.close()


if __name__ == "__main__":
    main()
