#!/usr/bin/env python3
"""Bounded rust-analyzer exact-range probe for the malformed M4 attribute."""

from __future__ import annotations

import json
import os
from pathlib import Path
import select
import subprocess
import time
from typing import Any


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "src/lib.rs"
TEXT = SOURCE.read_text(encoding="utf-8")
TOKEN = "syntax"


class Client:
    def __init__(self) -> None:
        self.process = subprocess.Popen(
            ["rust-analyzer"], cwd=ROOT,
            env={
                **os.environ,
                "RUSTUP_TOOLCHAIN": "stable",
                "CARGO_TARGET_DIR": "/tmp/krs-m4-diagnostics-ra-target",
            },
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
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
        headers = {}
        while True:
            line = self.process.stdout.readline()
            if line == b"\r\n":
                break
            if not line:
                raise RuntimeError("rust-analyzer closed stdout")
            key, value = line.decode().split(":", 1)
            headers[key.lower()] = value.strip()
        return json.loads(self.process.stdout.read(int(headers["content-length"])))

    def handle(self, message: dict[str, Any]) -> None:
        if "method" not in message or "id" not in message:
            return
        count = len(message.get("params", {}).get("items", []))
        result = [{} for _ in range(count)] if message["method"] == "workspace/configuration" else None
        self.send({"jsonrpc": "2.0", "id": message["id"], "result": result})

    def request(self, method: str, params: Any, timeout: float = 60) -> Any:
        request_id = self.next_id
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": request_id, "method": method, "params": params})
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            message = self.receive(deadline - time.monotonic())
            if message is None:
                break
            if message.get("id") == request_id and "method" not in message:
                if "error" in message:
                    raise RuntimeError(f"{method} failed: {message['error']}")
                return message.get("result")
            self.handle(message)
        raise RuntimeError(f"timed out waiting for {method}")

    def prime(self) -> None:
        deadline = time.monotonic() + 120
        while time.monotonic() < deadline:
            message = self.receive(deadline - time.monotonic())
            if message is None:
                break
            self.handle(message)
            if (message.get("method") == "$/progress"
                    and message.get("params", {}).get("token") == "rustAnalyzer/cachePriming"
                    and message.get("params", {}).get("value", {}).get("kind") == "end"):
                return
        raise RuntimeError("rust-analyzer did not finish cache priming")

    def close(self) -> None:
        if self.process.poll() is not None:
            stderr = self.process.stderr.read().decode(errors="replace") if self.process.stderr else ""
            raise RuntimeError(f"rust-analyzer exited early: {stderr}")
        try:
            self.request("shutdown", None, timeout=10)
            self.send({"jsonrpc": "2.0", "method": "exit", "params": None})
            self.process.wait(timeout=10)
        except BaseException:
            self.process.kill()
            raise


def token_range() -> dict[str, dict[str, int]]:
    offset = TEXT.index(TOKEN, TEXT.index("#[k::constructor"))
    line = TEXT.count("\n", 0, offset)
    character = offset - TEXT.rfind("\n", 0, offset) - 1
    return {
        "start": {"line": line, "character": character},
        "end": {"line": line, "character": character + len(TOKEN)},
    }


def main() -> None:
    version = subprocess.run(
        ["rust-analyzer", "--version"], check=True, text=True, capture_output=True,
        timeout=10, env={**os.environ, "RUSTUP_TOOLCHAIN": "stable"},
    ).stdout.strip()
    client = Client()
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
        client.prime()
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
            raise RuntimeError(f"expected one exact authored `{TOKEN}` range {expected}, got {matching!r}")
        print(json.dumps({"rust_analyzer": version, "range": expected, "token": TOKEN}, sort_keys=True))
    finally:
        client.close()


if __name__ == "__main__":
    main()
