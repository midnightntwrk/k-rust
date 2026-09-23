"""The rust-analyzer probe the readable semantics gates run over their crate.

A gate's `lsp_probe.py` names its crate and a table of
`(name, fragment, needle, target_fragment)` probes and calls `probe`. Each probe
places the cursor on `needle` inside the first source line containing
`fragment`, and requires go-to-definition to land on the first line containing
`target_fragment` and hover to return content. The source must also carry no
diagnostics.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import select
import subprocess
import time
from typing import Any, Sequence

from support import GateError


Probe = tuple[str, str, str, str]
ENVIRONMENT = {**os.environ, "RUSTUP_TOOLCHAIN": "stable"}


class Client:
    """A minimal JSON-RPC client over one rust-analyzer process."""

    def __init__(self, root: Path) -> None:
        self.process = subprocess.Popen(
            ["rust-analyzer"],
            cwd=root,
            env=ENVIRONMENT,
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
                raise GateError("rust-analyzer closed stdout")
            key, value = line.decode().split(":", 1)
            headers[key.lower()] = value.strip()
        return json.loads(self.process.stdout.read(int(headers["content-length"])))

    def handle(self, message: dict[str, Any]) -> None:
        if "method" not in message or "id" not in message:
            return
        count = len(message.get("params", {}).get("items", []))
        result: Any = (
            [{} for _ in range(count)] if message["method"] == "workspace/configuration" else None
        )
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
                    raise GateError(f"{method} failed: {message['error']}")
                return message.get("result")
            self.handle(message)
        raise GateError(f"timed out waiting for {method}")

    def wait_for_priming(self) -> None:
        deadline = time.monotonic() + 120
        while time.monotonic() < deadline:
            message = self.receive(deadline - time.monotonic())
            if message is None:
                break
            self.handle(message)
            params = message.get("params", {})
            if (
                message.get("method") == "$/progress"
                and params.get("token") == "rustAnalyzer/cachePriming"
                and params.get("value", {}).get("kind") == "end"
            ):
                return
        raise GateError("rust-analyzer did not finish cache priming")

    def close(self) -> None:
        if self.process.poll() is not None:
            stderr = self.process.stderr.read().decode(errors="replace") if self.process.stderr else ""
            raise GateError(f"rust-analyzer exited early:\n{stderr}")
        try:
            self.request("shutdown", None, timeout=10)
            self.send({"jsonrpc": "2.0", "method": "exit", "params": None})
            self.process.wait(timeout=10)
        except BaseException:
            self.process.kill()
            raise


def position(lines: Sequence[str], fragment: str, needle: str) -> dict[str, int]:
    """The LSP position one character into `needle` on the first line containing `fragment`."""

    matches = [index for index, line in enumerate(lines) if fragment in line]
    if not matches:
        raise GateError(f"probe fragment is absent from the source: {fragment!r}")
    line = matches[0]
    column = lines[line].index(needle, lines[line].index(fragment))
    return {"line": line, "character": len(lines[line][:column].encode("utf-16-le")) // 2 + 1}


def locations(result: Any) -> list[tuple[str, dict[str, Any]]]:
    if result is None:
        return []
    entries = result if isinstance(result, list) else [result]
    return [
        (entry["targetUri"], entry["targetSelectionRange"])
        if "targetUri" in entry
        else (entry["uri"], entry["range"])
        for entry in entries
    ]


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


def probe(root: Path, probes: Sequence[Probe], *, diagnostic_timeout: float) -> None:
    """Run the probes over `root/src/lib.rs` and print the JSON summary."""

    source = root / "src/lib.rs"
    text = source.read_text(encoding="utf-8")
    lines = text.splitlines()
    uri = source.as_uri()
    version = subprocess.run(
        ["rust-analyzer", "--version"],
        check=True,
        text=True,
        capture_output=True,
        timeout=10,
        env=ENVIRONMENT,
    ).stdout.strip()
    client = Client(root)
    try:
        client.request(
            "initialize",
            {
                "processId": None,
                "rootUri": root.as_uri(),
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
                    "textDocument": {"uri": uri, "languageId": "rust", "version": 1, "text": text}
                },
            }
        )
        report = client.request(
            "textDocument/diagnostic", {"textDocument": {"uri": uri}}, timeout=diagnostic_timeout
        )
        diagnostics = report.get("items", []) if report else []
        if diagnostics:
            raise GateError(f"rust-analyzer reported diagnostics: {diagnostics}")

        counts: dict[str, int] = {}
        for name, fragment, needle, target_fragment in probes:
            at = {"textDocument": {"uri": uri}, "position": position(lines, fragment, needle)}
            found = locations(client.request("textDocument/definition", at))
            counts[name] = len(found)
            if not found:
                raise GateError(f"{name}: no definition at {at['position']}")
            expected_line = next(
                (index for index, line in enumerate(lines) if target_fragment in line), None
            )
            if expected_line is None:
                raise GateError(f"{name}: definition fragment is absent: {target_fragment!r}")
            if not any(
                target_uri == uri and target["start"]["line"] == expected_line
                for target_uri, target in found
            ):
                raise GateError(f"{name}: definition {found} is not line {expected_line}")
            hover = client.request("textDocument/hover", at)
            if not meaningful_hover(hover):
                raise GateError(f"{name}: empty hover at {at['position']}: {hover}")

        print(
            json.dumps(
                {"rust_analyzer": version, "diagnostics": 0, "definitions_and_hovers": counts},
                sort_keys=True,
            )
        )
    finally:
        client.close()
