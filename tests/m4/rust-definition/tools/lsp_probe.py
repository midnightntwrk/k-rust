#!/usr/bin/env python3
"""Live rust-analyzer oracle for the production readable IMP surface."""

from __future__ import annotations

import json
import os
from pathlib import Path
import select
import subprocess
import time
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
IMP = ROOT / "src/imp.rs"
LIB = ROOT / "src/lib.rs"
SOURCES = (IMP, LIB)
TEXT = {path: path.read_text(encoding="utf-8") for path in SOURCES}
LINES = {path: text.splitlines() for path, text in TEXT.items()}


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
                and message.get("params", {}).get("token") == "rustAnalyzer/cachePriming"
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


def utf16_length(value: str) -> int:
    return len(value.encode("utf-16-le")) // 2


def position(
    path: Path,
    fragment: str,
    needle: str,
    *,
    occurrence: int = 0,
    needle_occurrence: int = 0,
    offset: int = 1,
) -> dict[str, int]:
    matches = [index for index, line in enumerate(LINES[path]) if fragment in line]
    assert len(matches) > occurrence, (path, fragment, matches, occurrence)
    line = matches[occurrence]
    start = LINES[path][line].index(fragment)
    column = start
    for _ in range(needle_occurrence + 1):
        column = LINES[path][line].index(needle, column)
        column += len(needle)
    column -= len(needle)
    return {
        "line": line,
        "character": utf16_length(LINES[path][line][:column]) + offset,
    }


def params(path: Path, at: dict[str, int]) -> dict[str, Any]:
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
        return any(meaningful_hover({"contents": child}) for child in contents)
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


def rename(client: Client, path: Path, at: dict[str, int], new_name: str) -> Any:
    for attempt in range(4):
        try:
            return client.request(
                "textDocument/rename", {**params(path, at), "newName": new_name}
            )
        except AssertionError as error:
            if "content modified" not in str(error).lower() or attempt == 3:
                raise
            time.sleep(0.5)
    raise AssertionError("unreachable")


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
                        "completion": {"completionItem": {}},
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
        for path in SOURCES:
            report = client.request(
                "textDocument/diagnostic",
                {"textDocument": {"uri": path.as_uri()}},
                timeout=90,
            )
            diagnostics[path.name] = report.get("items", []) if report else []
        assert not any(diagnostics.values()), diagnostics

        probes = [
            (
                "sorts macro",
                IMP,
                "k::sorts! {",
                "sorts",
                None,
                None,
            ),
            (
                "sort membership target",
                IMP,
                "    impl Expr for Id;",
                "Expr",
                IMP,
                "    Expr;",
            ),
            (
                "sort membership member",
                IMP,
                "    impl Expr for Id;",
                "Id",
                None,
                None,
            ),
            (
                "sort parent",
                IMP,
                "    Value: Expr + KResult;",
                "Expr",
                IMP,
                "    Expr;",
            ),
            (
                "framework sort parent",
                IMP,
                "    Value: Expr + KResult;",
                "KResult",
                None,
                None,
            ),
            (
                "readable sort alias",
                IMP,
                "Neg { value: Expr }",
                "Expr",
                IMP,
                "    Expr;",
            ),
            (
                "constructors attribute",
                IMP,
                "#[k::constructors(sort = Expr, result = KResult)]",
                "constructors",
                None,
                None,
            ),
            (
                "precedence attribute",
                IMP,
                "#[k::precedence(",
                "precedence",
                None,
                None,
            ),
            ("constructor variant", IMP, "eval_neg:     Neg { value }", "Neg", IMP, "    Neg { value: Expr },"),
            (
                "rule binder",
                IMP,
                "eval_neg:     Neg { value }",
                "value",
                IMP,
                "eval_neg:     Neg { value }",
                {"needle_occurrence": 1},
            ),
            ("glob family", IMP, "    use Op::*;", "Op", IMP, "pub enum Op"),
            (
                "rules macro",
                IMP,
                "k::rules! {",
                "rules",
                None,
                None,
            ),
            (
                "block-local variant import",
                IMP,
                "    use StmtSyntax::Assign;",
                "Assign",
                IMP,
                "    Assign { name: Id, value: Expr },",
            ),
            ("configuration type", IMP, "    for Machine;", "Machine", IMP, "pub struct Machine"),
            (
                "configuration attribute",
                IMP,
                "#[k::configuration]",
                "configuration",
                None,
                None,
            ),
            (
                "initializer attribute",
                IMP,
                "    #[k::init]",
                "init",
                None,
                None,
            ),
            ("initializer parameter", IMP, "Self { k: k::k![pgm], env }", "pgm", IMP, "pub fn init(pgm:"),
            (
                "initializer cell field",
                IMP,
                "Self { k: k::k![pgm], env }",
                "env",
                IMP,
                "pub env: Map<Id, Value>",
            ),
            (
                "where narrowing sort",
                IMP,
                "where lhs: Bool, rhs: Bool",
                "Bool",
                None,
                None,
            ),
            (
                "splice binder",
                IMP,
                "step:     Sequence(s1, s2) => k::k![s1, s2];",
                "s1",
                IMP,
                "step:     Sequence(s1, s2) => k::k![s1, s2];",
                {"needle_occurrence": 1},
            ),
            (
                "erase constructor",
                IMP,
                "done:     EmptyBlock() => ();",
                "EmptyBlock",
                IMP,
                "    EmptyBlock(),",
            ),
            (
                "machine narrowing sort",
                IMP,
                "    where value: Value;",
                "Value",
                IMP,
                "    Value: Expr + KResult;",
            ),
            ("builtin map update", IMP, "env: map::update(e, name, value)", "update", None, None),
            (
                "public generated sort",
                LIB,
                "pub use imp::{Expr, ExprSort",
                "ExprSort",
                IMP,
                "k::sorts! {",
            ),
        ]
        definition_counts: dict[str, int] = {}
        for probe in probes:
            name, path, fragment, needle, target_path, target_fragment, *options = probe
            at = position(path, fragment, needle, **(options[0] if options else {}))
            found = locations(client.request("textDocument/definition", params(path, at)))
            definition_counts[name] = len(found)
            assert found, (name, at, found)
            if target_path is not None and target_fragment is not None:
                expected_line = next(
                    index
                    for index, line in enumerate(LINES[target_path])
                    if target_fragment in line
                )
                assert any(
                    uri == target_path.as_uri() and target["start"]["line"] == expected_line
                    for uri, target in found
                ), (name, found, target_path, expected_line)
            hover = client.request("textDocument/hover", params(path, at))
            assert meaningful_hover(hover), (name, at, hover)

        completion_at = position(
            IMP,
            "env: map::update(e, name, value)",
            "update",
            offset=0,
        )
        completion = client.request(
            "textDocument/completion", params(IMP, completion_at)
        )
        completion_items = completion.get("items", []) if isinstance(completion, dict) else completion
        assert completion_items and any(
            item.get("label") == "update" for item in completion_items
        ), completion_items

        rename_probes = [
            (
                "Expr sort",
                IMP,
                position(IMP, "    Expr;", "Expr"),
                "Expression",
                [
                    (IMP, "    Expr;"),
                    (IMP, "    impl Expr for Id;"),
                    (IMP, "#[k::constructors(sort = Expr"),
                    (IMP, "    for Expr;"),
                    (LIB, "pub use imp::{Expr, ExprSort"),
                ],
            ),
            (
                "Machine",
                IMP,
                position(IMP, "pub struct Machine", "Machine"),
                "MachineRenamed",
                [
                    (IMP, "pub struct Machine"),
                    (IMP, "impl Machine"),
                    (IMP, "    for Machine;"),
                    (LIB, "ExprSort, Machine, Op"),
                ],
            ),
            (
                "Op",
                IMP,
                position(IMP, "pub enum Op", "Op"),
                "OperatorFamily",
                [
                    (IMP, "pub enum Op"),
                    (IMP, "    use Op::*;"),
                    (LIB, "Machine, Op, Stmt"),
                ],
            ),
            (
                "rule binder",
                IMP,
                position(
                    IMP,
                    "eval_neg:     Neg { value }",
                    "value",
                ),
                "operand",
                [
                    (IMP, "eval_neg:     Neg { value }"),
                ],
            ),
            (
                "initializer binder",
                IMP,
                position(IMP, "pub fn init(pgm:", "pgm"),
                "program",
                [
                    (IMP, "pub fn init(pgm:"),
                    (IMP, "Self { k: k::k![pgm], env }"),
                ],
            ),
        ]
        rename_counts: dict[str, int] = {}
        for name, path, at, new_name, expected in rename_probes:
            edit = rename(client, path, at, new_name)
            edits = edit_locations(edit)
            rename_counts[name] = len(edits)
            distinct_edits = {
                (
                    uri,
                    item_range["start"]["line"],
                    item_range["start"]["character"],
                    item_range["end"]["line"],
                    item_range["end"]["character"],
                )
                for uri, item_range in edits
            }
            minimum_edits = 2 if name == "rule binder" else len(expected)
            assert len(distinct_edits) >= minimum_edits, (
                name,
                minimum_edits,
                distinct_edits,
            )
            actual = {
                (uri, item_range["start"]["line"])
                for uri, item_range in edits
            }
            wanted = {
                (
                    expected_path.as_uri(),
                    next(
                        index
                        for index, line in enumerate(LINES[expected_path])
                        if fragment in line
                    ),
                )
                for expected_path, fragment in expected
            }
            assert wanted <= actual, (name, wanted, actual)

        print(
            json.dumps(
                {
                    "rust_analyzer": version,
                    "diagnostics": {name: 0 for name in diagnostics},
                    "definitions_and_hovers": definition_counts,
                    "completion": "map::update",
                    "rename_edits": rename_counts,
                    "compiler_owned_lsp": {
                        "bracket delimiters": "checked string literals",
                        "syntax placeholders": "checked string-template contents",
                        "strictness fields": "constructors-macro input",
                        "precedence members": "constructors-macro input",
                        "anonymous cell records": "intentionally unavailable per E7",
                    },
                },
                sort_keys=True,
            )
        )
    finally:
        client.close()


if __name__ == "__main__":
    main()
