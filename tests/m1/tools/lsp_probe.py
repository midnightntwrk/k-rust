#!/usr/bin/env python3
"""Production rust-analyzer oracle for the external M1 author workspace."""

from __future__ import annotations

import json
import pathlib
import select
import subprocess
import sys
import time
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1] / "workspace"
ROOT_SOURCE = ROOT / "packages" / "root-semantics" / "src" / "lib.rs"
BASE_SOURCE = ROOT / "packages" / "base-semantics" / "src" / "lib.rs"
SOURCES = (ROOT_SOURCE, BASE_SOURCE)
TEXT = {path: path.read_text(encoding="utf-8") for path in SOURCES}
LINES = {path: text.splitlines() for path, text in TEXT.items()}


class Client:
    def __init__(self) -> None:
        self.server = subprocess.Popen(
            ["rust-analyzer"],
            cwd=ROOT,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self.next_id = 1
        self.notifications: list[dict[str, Any]] = []

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
        if "method" in message and "id" in message:
            if message["method"] == "workspace/configuration":
                count = len(message.get("params", {}).get("items", []))
                result: Any = [{} for _ in range(count)]
            else:
                result = None
            self.send({"jsonrpc": "2.0", "id": message["id"], "result": result})
        elif "method" in message:
            self.notifications.append(message)

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

    def wait_for_priming(self, timeout: float = 90) -> None:
        deadline = time.monotonic() + timeout
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
        try:
            self.request("shutdown", None, timeout=10)
            self.send({"jsonrpc": "2.0", "method": "exit", "params": None})
            self.server.wait(timeout=10)
        except Exception:
            self.server.kill()
            raise


def utf16_length(text: str) -> int:
    return len(text.encode("utf-16-le")) // 2


def position(path: pathlib.Path, fragment: str, needle: str) -> dict[str, int]:
    lines = LINES[path]
    matches = [index for index, line in enumerate(lines) if fragment in line]
    assert len(matches) == 1, f"fragment must identify one line: {fragment!r}"
    line = matches[0]
    byte_column = lines[line].index(needle, lines[line].index(fragment))
    return {"line": line, "character": utf16_length(lines[line][:byte_column]) + 1}


def document_params(path: pathlib.Path, at: dict[str, int]) -> dict[str, Any]:
    return {"textDocument": {"uri": path.as_uri()}, "position": at}


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


def edit_locations(edit: dict[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    output: list[tuple[str, dict[str, Any]]] = []
    for uri, edits in edit.get("changes", {}).items():
        output.extend((uri, item["range"]) for item in edits)
    for change in edit.get("documentChanges", []):
        if "textDocument" not in change:
            continue
        uri = change["textDocument"]["uri"]
        output.extend((uri, item["range"]) for item in change.get("edits", []))
    return output


def main() -> None:
    version = subprocess.run(
        ["rust-analyzer", "--version"],
        check=True,
        text=True,
        capture_output=True,
        timeout=10,
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
                        "publishDiagnostics": {},
                        "diagnostic": {},
                    },
                },
            },
        )
        client.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
        client.wait_for_priming()

        for path in SOURCES:
            client.send(
                {
                    "jsonrpc": "2.0",
                    "method": "textDocument/didOpen",
                    "params": {
                        "textDocument": {
                            "uri": path.as_uri(),
                            "languageId": "rust",
                            "version": 1,
                            "text": TEXT[path],
                        }
                    },
                }
            )

        diagnostics: dict[str, list[Any]] = {}
        deadline = time.monotonic() + 30
        while len(diagnostics) < len(SOURCES) and time.monotonic() < deadline:
            message = client.receive(deadline - time.monotonic())
            if message is None:
                break
            client.handle(message)
            if message.get("method") == "textDocument/publishDiagnostics":
                params = message.get("params", {})
                if params.get("uri") in {path.as_uri() for path in SOURCES}:
                    diagnostics[params["uri"]] = params.get("diagnostics", [])
        for path in SOURCES:
            if path.as_uri() in diagnostics:
                continue
            report = client.request(
                "textDocument/diagnostic",
                {"textDocument": {"uri": path.as_uri()}},
            )
            assert report and report.get("kind") == "full", (
                f"no diagnostics report for {path}"
            )
            diagnostics[path.as_uri()] = report.get("items", [])
        assert not any(diagnostics.values()), f"unexpected authored diagnostics: {diagnostics}"

        definition_probes = [
            (
                "attribute sort",
                ROOT_SOURCE,
                '#[k::constructor(sort = Value, syntax = "value-node")]',
                "Value",
                ROOT_SOURCE,
                "pub trait Value: Expr + KResult {}",
            ),
            (
                "native rule constructor",
                ROOT_SOURCE,
                "pub fn native_swap(Pair { first, second }",
                "Pair",
                ROOT_SOURCE,
                "pub struct Pair {",
            ),
            (
                "term payload constructor",
                ROOT_SOURCE,
                "pub fn macro_swap(k::term![Pair { first, second }]",
                "Pair",
                ROOT_SOURCE,
                "pub struct Pair {",
            ),
            (
                "cross-package constructor",
                ROOT_SOURCE,
                "semantic_base::Same: Term<dyn semantic_base::Common>",
                "Same",
                BASE_SOURCE,
                "pub struct Same;",
            ),
        ]
        definition_summary: dict[str, int] = {}
        hover_summary: dict[str, bool] = {}
        probe_failures: list[str] = []
        for name, path, fragment, needle, target_path, target_fragment in definition_probes:
            at = position(path, fragment, needle)
            result = client.request("textDocument/definition", document_params(path, at))
            targets = locations(result)
            definition_summary[name] = len(targets)
            if len(targets) != 1:
                probe_failures.append(f"{name}: expected one target, got {targets}")
            else:
                target_uri, target_range = targets[0]
                expected_line = next(
                    index
                    for index, line in enumerate(LINES[target_path])
                    if target_fragment in line
                )
                if target_uri != target_path.as_uri():
                    probe_failures.append(f"{name}: wrong file {target_uri}")
                if target_range["start"]["line"] != expected_line:
                    probe_failures.append(f"{name}: wrong line {target_range}")
            hover = client.request("textDocument/hover", document_params(path, at))
            hover_summary[name] = meaningful_hover(hover)
            if not hover_summary[name]:
                probe_failures.append(f"{name}: empty hover")

        pair_definition = position(ROOT_SOURCE, "pub struct Pair {", "Pair")
        edits: list[tuple[str, dict[str, Any]]] = []
        try:
            prepare = client.request(
                "textDocument/prepareRename", document_params(ROOT_SOURCE, pair_definition)
            )
            if not prepare:
                probe_failures.append("Pair is not renameable")
            else:
                rename_params = document_params(ROOT_SOURCE, pair_definition)
                rename_params["newName"] = "PairRenamed"
                rename = client.request("textDocument/rename", rename_params)
                if not rename:
                    probe_failures.append("rename returned no WorkspaceEdit")
                else:
                    edits = edit_locations(rename)
        except AssertionError as error:
            probe_failures.append(str(error))
        root_edit_lines = {
            item_range["start"]["line"]
            for uri, item_range in edits
            if uri == ROOT_SOURCE.as_uri()
        }
        expected_rename_lines = {
            next(index for index, line in enumerate(LINES[ROOT_SOURCE]) if fragment in line)
            for fragment in (
                "pub struct Pair {",
                "pub fn native_swap(Pair { first, second }",
                "pub fn macro_swap(k::term![Pair { first, second }]",
                "k::term![Pair {",
            )
        }
        if not expected_rename_lines <= root_edit_lines:
            probe_failures.append(
                f"rename missed authored Pair locations: expected {expected_rename_lines}, "
                f"got {root_edit_lines}"
            )

        print(
            json.dumps(
                {
                    "rust_analyzer": version,
                    "diagnostics": {
                        "root-semantics/src/lib.rs": 0,
                        "base-semantics/src/lib.rs": 0,
                    },
                    "definitions": definition_summary,
                    "hovers": hover_summary,
                    "rename_authored_edits": sum(
                        uri == ROOT_SOURCE.as_uri() for uri, _ in edits
                    ),
                },
                sort_keys=True,
            )
        )
        assert not probe_failures, "; ".join(probe_failures)
    finally:
        client.shutdown()


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"LSP oracle failed: {error}", file=sys.stderr)
        raise
