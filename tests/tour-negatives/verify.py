#!/usr/bin/env python3
"""Pin the tour's focused negative diagnostics to exact authored tokens."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry  # noqa: E402
from support.diagnostics import cargo_primary_span, envelopes, krs_diagnostics  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.process import compact, render, run  # noqa: E402
from support.tools import checkout_scratch, executable, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MACRO_NEGATIVES = ROOT / "crates" / "krs-macros" / "tests" / "fixtures" / "negative"
FRESH_PLACEMENT = (
    "fresh values are drawn from the generated counter only by a transition step of the "
    "configuration; `#[k::fresh]` is not allowed on an equation, simplification, alias, claim, "
    "context alias, or anywhere rule"
)


def run_failing(command: list[str | Path]) -> subprocess.CompletedProcess[str]:
    """Run a command the negative case requires to fail."""

    result = run(command, environment=z3_environment(), check=False)
    if result.returncode == 0:
        raise GateError(f"command should fail: {render(command)}\n{compact(result)}")
    return result


UNBOUND_VARIABLES_OUTSIDE_DESUGAR = (
    "unbound_variables applies only to desugar clauses: write it in the `#[k::desugar(..)]` of "
    "a clause fn, `#[k::desugar(unbound_variables = [x, _])]`"
)


def check_rust_negative(binary: str, message: str, token: str) -> None:
    result = run_failing(
        [
            executable("cargo"),
            "+stable",
            "check",
            "--locked",
            "--offline",
            "--manifest-path",
            MACRO_NEGATIVES / "Cargo.toml",
            "--bin",
            binary,
            "--message-format=json",
        ],
    )
    span = cargo_primary_span(result.stdout)
    if span.message != message:
        raise GateError(f"{binary}: diagnostic changed: {span.message!r}")
    source = MACRO_NEGATIVES / span.file_name
    selected = source.read_bytes()[span.byte_start:span.byte_end].decode()
    if selected != token:
        raise GateError(f"{binary}: expected authored token {token!r}, got {selected!r}")


def check_overlap(binary: Path) -> None:
    result = run_failing(
        Invocation(binary, HERE / "Cargo.toml", "krs-tour-negatives", "main").argv(
            "check", "--message-format=json"
        ),
    )
    diagnostics = envelopes(result.stderr)
    if len(diagnostics) != 1:
        raise GateError(f"overlap: expected one JSON diagnostic line, got {len(diagnostics)}")
    typed = krs_diagnostics(result.stderr)
    if len(typed) != 1:
        raise GateError(f"overlap: expected one KRS diagnostic, got {len(typed)}")
    diagnostic = typed[0]
    expected = {
        "schema_version": 1,
        "stage": "analysis",
        "code": "krs::analysis::overlapping-rule-heads",
        "severity": "error",
    }
    for field, value in expected.items():
        if getattr(diagnostic, field) != value:
            raise GateError(f"overlap: {field} changed: {getattr(diagnostic, field)!r}")
    selected = diagnostic.selected_bytes(HERE).decode()
    if selected != "Foo":
        raise GateError(f"overlap: second authored head span changed: {selected!r}")
    if "second_foo" not in diagnostic.message:
        raise GateError("overlap diagnostic does not identify the second stable rule")

    human = run_failing(
        Invocation(binary, HERE / "Cargo.toml", "krs-tour-negatives", "main").argv("check"),
    )
    if "error[krs::analysis::overlapping-rule-heads]" not in human.stderr:
        raise GateError("default overlap diagnostic lacks the human error title")
    source_path = (HERE / "src/lib.rs").relative_to(ROOT)
    if f"--> {source_path}:" not in human.stderr:
        raise GateError("default overlap diagnostic lacks the cwd-relative source path")
    source_line = next(
        line for line in (HERE / "src/lib.rs").read_text(encoding="utf-8").splitlines()
        if "second_foo:" in line
    )
    if source_line.strip() not in human.stderr:
        raise GateError("default overlap diagnostic lacks the authored Foo snippet line")


def main() -> None:
    target = checkout_scratch() / "tour-negatives-root-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target)}
    binary = build(environment)
    check_packages("tour-negatives", krs=binary, env=environment, target_dir=target)
    check_overlap(binary)
    print("PASS overlap: structured analysis code, exact second Foo head, and default human snippet")
    cases = (
        (
            "readable_missing_cell",
            "unsupported fixed configuration field: wrapper-free configurations require `#[k::cell]` on every plain field",
            "renamed_krs",
        ),
        (
            "initializer_control_flow",
            "unsupported declarative initializer body: statements, semicolons, control flow, mutation, and early return are forbidden",
            "if",
        ),
        (
            "malformed_readable_family",
            "invalid enum precedence chain: enum variant `Other` is missing from the exhaustive chain",
            "Other",
        ),
        (
            "readable_rule_bad_update",
            "the update base must be the cell `env`",
            "other",
        ),
        (
            "prefer_with_avoid",
            "`prefer` must be omitted: a production is either preferred or avoided, not both",
            "prefer",
        ),
        (
            "overload_unknown_target",
            "no variant named `Missing` found for enum `ExpSyntax`",
            "Missing",
        ),
        (
            "overload_private_target",
            "enum `ExpSyntax` is private",
            "ExpSyntax",
        ),
        (
            "readable_rule_empty_record",
            "a machine rule selects at least one cell",
            "{}",
        ),
        (
            "sort_test_in_pattern",
            "unsupported term expression: `k::is!` and `k::project!` are function calls and cannot be matched; restrict the binder with a typed parameter or `where x: S`",
            "is",
        ),
        (
            "rule_fresh_in_pattern",
            "a fresh value cannot be matched: it does not exist until the step happens, so it cannot also be a pattern binding; rename it",
            "value",
        ),
        (
            "rule_fresh_in_requires",
            "a fresh value cannot occur in `requires`: the step allocates it only after deciding to apply",
            "n",
        ),
        (
            "rule_fresh_unused",
            "a fresh binder must occur in the rule's result or ensures condition",
            "n",
        ),
        ("rule_fresh_equation", FRESH_PLACEMENT, "n"),
        ("rule_fresh_claim", FRESH_PLACEMENT, "fresh"),
        ("rule_fresh_anywhere", FRESH_PLACEMENT, "n"),
        (
            "desugar_clause_recursive",
            "recursion is a property of the production: write `recursive` on the production's "
            "`#[k::alias]` or `#[k::desugar]` marker, and a plain marker on its clauses",
            "recursive",
        ),
        (
            "desugar_requires",
            "a desugar clause has no `#[k::requires]`: K rewrites the definition and the program "
            "with it once, before anything runs, so there is nothing to test a condition against",
            "requires",
        ),
        (
            "alias_and_desugar",
            "a production is an alias or a desugar, not both: `alias` also prints backwards, "
            "`desugar` only expands",
            "desugar",
        ),
        (
            "desugar_unbound_bound",
            "`body` is bound by the pattern; `unbound_variables` lists only result names the "
            "pattern does not bind",
            "body",
        ),
        (
            "desugar_unbound_unused",
            "`_` is listed in `unbound_variables`, but the result has no `_`; list `_` only for "
            "a result with wildcards",
            "_",
        ),
        (
            "alias_unbound_variables",
            UNBOUND_VARIABLES_OUTSIDE_DESUGAR,
            "unbound_variables",
        ),
        (
            "desugar_production_payload",
            UNBOUND_VARIABLES_OUTSIDE_DESUGAR,
            "unbound_variables",
        ),
        (
            "spec_module_not_a_module",
            "`#[k::spec_module]` applies to an inline `mod name { .. }`, which holds the spec module's claims, lemmas, and tokens",
            "fn",
        ),
        (
            "spec_module_syntax_name",
            "`ORG-SYNTAX` ends in `-SYNTAX`, which KRS reserves for program-syntax modules; choose another spec-module name",
            '"ORG-SYNTAX"',
        ),
        (
            "spec_module_nested",
            "spec modules do not nest: declare this spec module beside its parent and list the parent in its `imports`",
            "#",
        ),
    )
    for binary, message, token in cases:
        check_rust_negative(binary, message, token)
        print(f"PASS {binary}: pinned message and authored token {token!r}")


if __name__ == "__main__":
    entry("tour-negatives", main, errors=(OSError, KeyError, TypeError, ValueError))
