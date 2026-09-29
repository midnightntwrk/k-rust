"""Shared native and Java case checks through retained gate states."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

from support import GateError, krs_gate


@dataclass(frozen=True)
class Expectation:
    """One surface-text, collection-size, or K-sequence-head assertion."""

    cell: str
    text: str | None = None
    size: int | None = None
    head: str | None = None


@dataclass(frozen=True)
class Specification:
    """Port data needed to configure, check, and report one behavior case."""

    variables: Callable[[Mapping[str, Any]], dict[str, str]]
    expectations: Callable[[Mapping[str, Any]], list[Expectation]]
    outcome: Callable[[Mapping[str, Any]], dict[str, Any]]


def check_case(session: krs_gate.Session, case: Mapping[str, Any], spec: Specification) -> dict[str, Any]:
    """Check the retained state and return the port's pinned outcome shape."""

    for item in spec.expectations(case):
        try:
            session.expect("case", item.cell, text=item.text, size=item.size, head=item.head)
        except GateError as error:
            raise GateError(f"{case['id']}: {error}") from error
    return spec.outcome(case)


def native_case(session: krs_gate.Session, case: Mapping[str, Any], spec: Specification) -> dict[str, Any]:
    """Configure, execute, retain, and check one native case."""

    pattern = session.configure(spec.variables(case))["pattern"]
    session.execute(pattern, keep="case")
    return check_case(session, case, spec)


def native_corpus(
    gate: Path, definition_ir: Path, module: str,
    cases: list[Mapping[str, Any]], spec: Specification,
) -> list[dict[str, Any]]:
    """Run all selected native cases in one loaded session."""

    with krs_gate.Session(gate) as session:
        session.load(definition_ir, module)
        return [native_case(session, case, spec) for case in cases]


def java_case(
    session: krs_gate.Session, case: Mapping[str, Any], spec: Specification, kore: str,
) -> dict[str, Any]:
    """Retain Java KORE and run the same expectations and outcome builder."""

    session.read(kore, "case")
    return check_case(session, case, spec)
