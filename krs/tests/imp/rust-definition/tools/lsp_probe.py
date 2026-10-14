#!/usr/bin/env python3
"""Live rust-analyzer oracle for the production readable IMP surface."""

from __future__ import annotations

import json
from pathlib import Path
import sys
import time
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from support import GateError  # noqa: E402
from support.lsp import Session, locations, meaningful_hover, position, version  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
IMP = ROOT / "src/imp.rs"
LIB = ROOT / "src/lib.rs"
SOURCES = (IMP, LIB)
TEXT = {path: path.read_text(encoding="utf-8") for path in SOURCES}
LINES = {path: text.splitlines() for path, text in TEXT.items()}


def params(path: Path, at: dict[str, int]) -> dict[str, Any]:
    return {"textDocument": {"uri": path.as_uri()}, "position": at}


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


def rename(client: Session, path: Path, at: dict[str, int], new_name: str) -> Any:
    for attempt in range(4):
        try:
            return client.request(
                "textDocument/rename", {**params(path, at), "newName": new_name}
            )
        except GateError as error:
            if "content modified" not in str(error).lower() or attempt == 3:
                raise
            time.sleep(0.5)
    raise AssertionError("unreachable")


def main() -> None:
    analyzer = version()
    capabilities = {
        "workspace": {"configuration": True},
        "window": {"workDoneProgress": True},
        "textDocument": {
            "definition": {"linkSupport": True},
            "hover": {"contentFormat": ["markdown", "plaintext"]},
            "rename": {"prepareSupport": True},
            "completion": {"completionItem": {}},
            "diagnostic": {},
        },
    }
    with Session(ROOT, TEXT, capabilities=capabilities) as client:
        diagnostics: dict[str, list[Any]] = {}
        for path in SOURCES:
            diagnostics[path.name] = client.diagnostics(path, timeout=90)
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
            ("constructor variant", IMP, "eval_neg    : Neg { value }", "Neg", IMP, "    Neg { value: Expr },"),
            (
                "rule binder",
                IMP,
                "eval_neg    : Neg { value }",
                "value",
                IMP,
                "eval_neg    : Neg { value }",
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
                "step    : Sequence(s1, s2)         => k::k![s1, s2];",
                "s1",
                IMP,
                "step    : Sequence(s1, s2)         => k::k![s1, s2];",
                {"needle_occurrence": 1},
            ),
            (
                "erase constructor",
                IMP,
                "done    : EmptyBlock()             => ();",
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
            at = position(LINES[path], fragment, needle, **(options[0] if options else {}))
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
            LINES[IMP],
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
                position(LINES[IMP], "    Expr;", "Expr"),
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
                position(LINES[IMP], "pub struct Machine", "Machine"),
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
                position(LINES[IMP], "pub enum Op", "Op"),
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
                    LINES[IMP],
                    "eval_neg    : Neg { value }",
                    "value",
                ),
                "operand",
                [
                    (IMP, "eval_neg    : Neg { value }"),
                ],
            ),
            (
                "initializer binder",
                IMP,
                position(LINES[IMP], "pub fn init(pgm:", "pgm"),
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
                    "rust_analyzer": analyzer,
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


if __name__ == "__main__":
    main()
