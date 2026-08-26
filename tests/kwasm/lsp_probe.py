#!/usr/bin/env python3
"""Focused rust-analyzer qualification for the readable KWasm slice."""

from __future__ import annotations

import json
import os
from pathlib import Path
import select
import subprocess
import time
from typing import Any


ROOT = Path(__file__).resolve().parent / "rust-definition"
SOURCE = ROOT / "src/lib.rs"
TEXT = SOURCE.read_text(encoding="utf-8")
LINES = TEXT.splitlines()


class Client:
    def __init__(self) -> None:
        self.process = subprocess.Popen(
            ["rust-analyzer"],
            cwd=ROOT,
            env={**os.environ, "RUSTUP_TOOLCHAIN": "stable"},
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self.next_id = 1

    def send(self, message: dict[str, Any]) -> None:
        assert self.process.stdin is not None
        body = json.dumps(message, separators=(",", ":")).encode()
        self.process.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)
        self.process.stdin.flush()

    def receive(self, timeout: float) -> dict[str, Any] | None:
        assert self.process.stdout is not None
        if timeout <= 0 or not select.select([self.process.stdout], [], [], timeout)[0]:
            return None
        headers: dict[str, str] = {}
        while True:
            line = self.process.stdout.readline()
            if line == b"\r\n":
                break
            if not line:
                raise AssertionError("rust-analyzer closed stdout")
            key, value = line.decode().split(":", 1)
            headers[key.lower()] = value.strip()
        return json.loads(self.process.stdout.read(int(headers["content-length"])))

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

    def request(self, method: str, params: Any, timeout: float = 60) -> Any:
        request_id = self.next_id
        self.next_id += 1
        self.send(
            {"jsonrpc": "2.0", "id": request_id, "method": method, "params": params}
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

    def close(self) -> None:
        if self.process.poll() is not None:
            stderr = (
                self.process.stderr.read().decode(errors="replace")
                if self.process.stderr
                else ""
            )
            raise AssertionError(f"rust-analyzer exited early:\n{stderr}")
        try:
            self.request("shutdown", None, timeout=10)
            self.send({"jsonrpc": "2.0", "method": "exit", "params": None})
            self.process.wait(timeout=10)
        except BaseException:
            self.process.kill()
            raise


def position(
    fragment: str,
    needle: str,
    *,
    occurrence: int = 0,
    needle_occurrence: int = 0,
    offset: int = 1,
) -> dict[str, int]:
    matches = [index for index, line in enumerate(LINES) if fragment in line]
    assert len(matches) > occurrence, (fragment, matches, occurrence)
    line = matches[occurrence]
    column = LINES[line].index(fragment)
    for _ in range(needle_occurrence + 1):
        column = LINES[line].index(needle, column) + len(needle)
    column -= len(needle)
    return {
        "line": line,
        "character": len(LINES[line][:column].encode("utf-16-le")) // 2 + offset,
    }


def params(at: dict[str, int]) -> dict[str, Any]:
    return {"textDocument": {"uri": SOURCE.as_uri()}, "position": at}


def locations(result: Any) -> list[tuple[str, dict[str, Any]]]:
    if result is None:
        return []
    entries = result if isinstance(result, list) else [result]
    output = []
    for entry in entries:
        if "targetUri" in entry:
            output.append((entry["targetUri"], entry["targetSelectionRange"]))
        else:
            output.append((entry["uri"], entry["range"]))
    return output


def meaningful_hover(result: Any) -> bool:
    if not result:
        return False
    contents = result.get("contents")
    if isinstance(contents, str):
        return bool(contents.strip())
    if isinstance(contents, dict):
        return bool(str(contents.get("value", "")).strip())
    if isinstance(contents, list):
        return any(meaningful_hover({"contents": item}) for item in contents)
    return False


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
                "ordinary cell constructor",
                "valstack: Stack::Cons(Value::Integer(IntegerType::I32, rhs)",
                "Cons",
                "    Cons { head: Val, tail: ValStack },",
            ),
            (
                "ordinary cell result constructor",
                "valstack: Stack::Cons(Value::Integer(ty, value), stack)",
                "Cons",
                "    Cons { head: Val, tail: ValStack },",
            ),
            (
                "function application",
                "instrs: [crate::IntBinOp(IntegerType::I32, op, lhs, rhs), ..]",
                "IntBinOp",
                "pub struct IntBinOp {",
            ),
            (
                "configuration target",
                "    for Machine;",
                "Machine",
                "pub struct Machine {",
            ),
            (
                "binding reference",
                "instrs: [crate::IntBinOp(IntegerType::I32, op, lhs, rhs), ..]",
                "rhs",
                "valstack: Stack::Cons(Value::Integer(IntegerType::I32, rhs)",
            ),
            (
                "trap constructor",
                "instrs: [Trap(), ..]",
                "Trap",
                "    Trap(),",
            ),
        ]
        counts: dict[str, int] = {}
        for name, fragment, needle, target_fragment in probes:
            at = position(fragment, needle)
            found = locations(client.request("textDocument/definition", params(at)))
            counts[name] = len(found)
            assert found, (name, at, found)
            expected_line = next(
                index for index, line in enumerate(LINES) if target_fragment in line
            )
            assert any(
                uri == SOURCE.as_uri() and target["start"]["line"] == expected_line
                for uri, target in found
            ), (name, found, expected_line)
            hover = client.request("textDocument/hover", params(at))
            assert meaningful_hover(hover), (name, at, hover)

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
