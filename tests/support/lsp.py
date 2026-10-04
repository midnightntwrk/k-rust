"""The rust-analyzer client and LSP probes shared by the gates.

`Client` drives one rust-analyzer process over JSON-RPC.
`Session` owns the handshake and opened source files.
A semantics port names a table of `(name, fragment, needle, target_fragment)` probes.
Each probe places the cursor on `needle` inside the first source line containing `fragment`.
Go-to-definition must land on the first line containing `target_fragment`, and hover must return content.
The source must also carry no diagnostics.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import select
import subprocess
import time
from typing import Any, Mapping, Sequence

from support import GateError
from support.process import BASE_ENVIRONMENT


Probe = tuple[str, str, str, str]
ENVIRONMENT = {**os.environ, **BASE_ENVIRONMENT, "RUSTUP_TOOLCHAIN": "stable"}


class Client:
    """A minimal JSON-RPC client over one rust-analyzer process."""

    def __init__(self, root: Path, environment: Mapping[str, str] | None = None) -> None:
        self.process = subprocess.Popen(
            ["rust-analyzer"],
            cwd=root,
            env={**ENVIRONMENT, **(environment or {})},
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

    def wait_for_priming(self, timeout: float = 120) -> None:
        deadline = time.monotonic() + timeout
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


def position(
    lines: Sequence[str], fragment: str, needle: str, *,
    occurrence: int = 0, needle_occurrence: int = 0, offset: int = 1,
) -> dict[str, int]:
    """Find a needle after a fragment and return its UTF-16 LSP position."""

    if occurrence < 0 or needle_occurrence < 0:
        raise GateError("LSP probe occurrences must be nonnegative")
    matches = [index for index, line in enumerate(lines) if fragment in line]
    if len(matches) <= occurrence:
        raise GateError(f"probe fragment is absent at occurrence {occurrence}: {fragment!r}")
    line = matches[occurrence]
    column = lines[line].index(fragment)
    try:
        for index in range(needle_occurrence + 1):
            column = lines[line].index(needle, column)
            if index < needle_occurrence:
                column += len(needle)
    except ValueError as error:
        raise GateError(f"probe needle occurrence {needle_occurrence} is absent: {needle!r}") from error
    return {
        "line": line,
        "character": len(lines[line][:column].encode("utf-16-le")) // 2 + offset,
    }


def token_range(text: str, token: str, *, after: str) -> dict[str, dict[str, int]]:
    """Return the UTF-16 LSP range of the first token after a marker."""

    try:
        start = text.index(token, text.index(after))
    except ValueError as error:
        raise GateError(f"token {token!r} after {after!r} is absent") from error
    line = text.count("\n", 0, start)
    line_start = text.rfind("\n", 0, start) + 1
    character = len(text[line_start:start].encode("utf-16-le")) // 2
    return {
        "start": {"line": line, "character": character},
        "end": {"line": line, "character": character + len(token.encode("utf-16-le")) // 2},
    }


DEFAULT_CAPABILITIES: dict[str, Any] = {
    "workspace": {"configuration": True},
    "window": {"workDoneProgress": True},
    "textDocument": {
        "definition": {"linkSupport": True},
        "hover": {"contentFormat": ["markdown", "plaintext"]},
        "diagnostic": {},
    },
}


class Session:
    """Own one rust-analyzer handshake, its opened files, and shutdown."""

    def __init__(
        self, root: Path, files: Mapping[Path, str], *,
        capabilities: Mapping[str, Any] | None = None,
        environment: Mapping[str, str] | None = None,
        timeout: float | None = None,
    ) -> None:
        self.root = root
        self.files = files
        self.capabilities = capabilities if capabilities is not None else DEFAULT_CAPABILITIES
        self.environment = environment
        self.deadline = time.monotonic() + timeout if timeout is not None else None
        self.client: Client | None = None

    def _remaining(self, timeout: float) -> float:
        if self.deadline is None:
            return timeout
        remaining = min(timeout, self.deadline - time.monotonic())
        if remaining <= 0:
            raise GateError("rust-analyzer session timed out")
        return remaining

    def request(self, method: str, params: Any, timeout: float = 60) -> Any:
        assert self.client is not None
        return self.client.request(method, params, timeout=self._remaining(timeout))

    def diagnostics(self, path: Path, timeout: float = 60) -> list[Any]:
        report = self.request(
            "textDocument/diagnostic", {"textDocument": {"uri": path.as_uri()}}, timeout=timeout
        )
        return report.get("items", []) if report else []

    def __enter__(self) -> Session:
        self.client = Client(self.root, self.environment)
        try:
            self.request(
                "initialize",
                {"processId": None, "rootUri": self.root.as_uri(), "capabilities": self.capabilities},
            )
            self.client.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
            self.client.wait_for_priming(self._remaining(120))
            for path, content in self.files.items():
                self.client.send({
                    "jsonrpc": "2.0", "method": "textDocument/didOpen",
                    "params": {"textDocument": {
                        "uri": path.as_uri(), "languageId": "rust", "version": 1, "text": content,
                    }},
                })
        except BaseException:
            try:
                self.client.close()
            except Exception:
                pass
            raise
        return self

    def __exit__(self, exc_type: Any, *_: Any) -> None:
        assert self.client is not None
        try:
            self.client.close()
        except Exception:
            if exc_type is None:
                raise


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


def version(environment: Mapping[str, str] | None = None) -> str:
    """The `rust-analyzer --version` line under the stable toolchain."""

    return subprocess.run(
        ["rust-analyzer", "--version"],
        check=True,
        text=True,
        capture_output=True,
        timeout=10,
        env={**ENVIRONMENT, **(environment or {})},
    ).stdout.strip()


def probe(
    root: Path, probes: Sequence[Probe], *, diagnostic_timeout: float,
    environment: Mapping[str, str] | None = None, timeout: float = 900,
) -> None:
    """Probe `root/src/lib.rs` and print JSON.

    `timeout` bounds handshake, priming, diagnostics, and probe requests.
    The version check and shutdown have their own 10-second limits.
    """

    source = root / "src/lib.rs"
    text = source.read_text(encoding="utf-8")
    lines = text.splitlines()
    uri = source.as_uri()
    analyzer = version(environment)
    with Session(root, {source: text}, environment=environment, timeout=timeout) as client:
        diagnostics = client.diagnostics(source, timeout=diagnostic_timeout)
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
                {"rust_analyzer": analyzer, "diagnostics": 0, "definitions_and_hovers": counts},
                sort_keys=True,
            )
        )
