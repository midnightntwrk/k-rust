#!/usr/bin/env python3
"""Bounded rust-analyzer probe for the production macro surface."""

from __future__ import annotations

import json
import os
import pathlib
import select
import subprocess
import time
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parent / "fixtures" / "positive"
SOURCE = ROOT / "src" / "main.rs"
TEXT = SOURCE.read_text(encoding="utf-8")
LINES = TEXT.splitlines()


class Client:
    def __init__(self) -> None:
        self.server = subprocess.Popen(
            ["rust-analyzer"],
            cwd=ROOT,
            env={**os.environ, "RUSTUP_TOOLCHAIN": "stable"},
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self.next_id = 1

    def send(self, message: dict[str, Any]) -> None:
        assert self.server.stdin is not None
        data = json.dumps(message, separators=(",", ":")).encode()
        self.server.stdin.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
        self.server.stdin.flush()

    def receive(self, timeout: float) -> dict[str, Any] | None:
        assert self.server.stdout is not None
        if timeout <= 0 or not select.select([self.server.stdout], [], [], timeout)[0]:
            return None
        headers: dict[str, str] = {}
        while True:
            line = self.server.stdout.readline()
            if line == b"\r\n":
                break
            if not line:
                raise AssertionError("rust-analyzer closed stdout")
            key, value = line.decode().split(":", 1)
            headers[key.lower()] = value.strip()
        return json.loads(self.server.stdout.read(int(headers["content-length"])))

    def handle(self, message: dict[str, Any]) -> None:
        if "method" not in message or "id" not in message:
            return
        count = len(message.get("params", {}).get("items", []))
        result: Any = (
            [{} for _ in range(count)]
            if message["method"] == "workspace/configuration"
            else None
        )
        self.send({"jsonrpc": "2.0", "id": message["id"], "result": result})

    def request(self, method: str, params: Any, timeout: float = 45) -> Any:
        request_id = self.next_id
        self.next_id += 1
        self.send(
            {
                "jsonrpc": "2.0",
                "id": request_id,
                "method": method,
                "params": params,
            }
        )
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            message = self.receive(deadline - time.monotonic())
            if message is None:
                break
            if message.get("id") == request_id and "method" not in message:
                if "error" in message:
                    raise AssertionError(f"{method} failed: {message['error']}")
                return message.get("result")
            self.handle(message)
        raise AssertionError(f"timed out waiting for {method}")

    def wait_for_priming(self) -> None:
        deadline = time.monotonic() + 120
        while time.monotonic() < deadline:
            message = self.receive(deadline - time.monotonic())
            if message is None:
                break
            self.handle(message)
            if (
                message.get("method") == "$/progress"
                and message.get("params", {}).get("token")
                == "rustAnalyzer/cachePriming"
                and message.get("params", {}).get("value", {}).get("kind") == "end"
            ):
                return
        raise AssertionError("rust-analyzer did not finish cache priming")

    def shutdown(self) -> None:
        if self.server.poll() is not None:
            stderr = (
                self.server.stderr.read().decode(errors="replace")
                if self.server.stderr
                else ""
            )
            raise AssertionError(f"rust-analyzer exited early:\n{stderr}")
        try:
            self.request("shutdown", None, timeout=10)
            self.send({"jsonrpc": "2.0", "method": "exit", "params": None})
            self.server.wait(timeout=10)
        except Exception:
            self.server.kill()
            raise


def position(fragment: str, needle: str, occurrence: int = 0) -> dict[str, int]:
    matches = [index for index, line in enumerate(LINES) if fragment in line]
    assert len(matches) > occurrence, (fragment, matches, occurrence)
    line = matches[occurrence]
    column = LINES[line].index(needle, LINES[line].index(fragment)) + 1
    return {"line": line, "character": column}


def params(at: dict[str, int]) -> dict[str, Any]:
    return {"textDocument": {"uri": SOURCE.as_uri()}, "position": at}


def locations(result: Any) -> list[dict[str, Any]]:
    if result is None:
        return []
    entries = result if isinstance(result, list) else [result]
    return [entry.get("targetSelectionRange", entry.get("range")) for entry in entries]


def edit_lines(edit: dict[str, Any]) -> set[int]:
    lines: set[int] = set()
    for uri, edits in edit.get("changes", {}).items():
        if uri == SOURCE.as_uri():
            lines.update(item["range"]["start"]["line"] for item in edits)
    for change in edit.get("documentChanges", []):
        if change.get("textDocument", {}).get("uri") == SOURCE.as_uri():
            lines.update(
                item["range"]["start"]["line"] for item in change.get("edits", [])
            )
    return lines


def meaningful_hover(value: Any) -> bool:
    return bool(value and str(value.get("contents", "")).strip())


def rename_with_retry(client: Client, at: dict[str, int], new_name: str) -> Any:
    for attempt in range(4):
        try:
            return client.request(
                "textDocument/rename", {**params(at), "newName": new_name}
            )
        except AssertionError as error:
            if "content modified" not in str(error).lower() or attempt == 3:
                raise
            time.sleep(0.5)
    raise AssertionError("unreachable rename retry state")


def main() -> None:
    version = subprocess.run(
        ["rust-analyzer", "--version"],
        check=True,
        text=True,
        capture_output=True,
        timeout=10,
        env={**os.environ, "RUSTUP_TOOLCHAIN": "stable"},
    ).stdout.strip()
    client = Client()
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
                        "rename": {"prepareSupport": True},
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
                "initializer_constructor",
                position("k: instrumented::KCell::new(k![Halt])", "Halt"),
                position("pub struct Halt", "Halt")["line"],
            ),
            (
                "initializer_bound_variable",
                position("KCell::new(k![program])", "program"),
                position("program: Term<dyn KItem>", "program")["line"],
            ),
            (
                "preserved_associated_method",
                position("let _: fn() -> Machine = Machine::init", "init"),
                position("pub fn init() -> Self", "init")["line"],
            ),
        ]
        definitions: dict[str, int] = {}
        hovers: dict[str, bool] = {}
        for name, at, expected_line in probes:
            targets = locations(client.request("textDocument/definition", params(at)))
            assert len(targets) == 1 and targets[0]["start"]["line"] == expected_line, (
                name,
                targets,
                expected_line,
            )
            definitions[name] = len(targets)
            hovers[name] = meaningful_hover(
                client.request("textDocument/hover", params(at))
            )
            assert hovers[name], name

        halt_decl = position("pub struct Halt", "Halt")
        halt_rename = rename_with_retry(client, halt_decl, "Halted")
        halt_lines = edit_lines(halt_rename)
        assert position("k: instrumented::KCell::new(k![Halt])", "Halt")["line"] in halt_lines

        program_decl = position("program: Term<dyn KItem>", "program")
        program_rename = rename_with_retry(client, program_decl, "program_term")
        program_lines = edit_lines(program_rename)
        expected_program_lines = {
            program_decl["line"],
            position("KCell::new(k![program])", "program")["line"],
        }
        assert expected_program_lines <= program_lines, (
            expected_program_lines,
            program_lines,
        )

        print(
            json.dumps(
                {
                    "rust_analyzer": version,
                    "diagnostics": len(diagnostics),
                    "definitions": definitions,
                    "hovers": hovers,
                    "rename_authored_lines": {
                        "initializer_constructor": len(halt_lines),
                        "initializer_bound_variable": len(program_lines),
                    },
                },
                sort_keys=True,
            )
        )
    finally:
        client.shutdown()


if __name__ == "__main__":
    main()
