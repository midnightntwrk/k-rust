"""Shared native and Java case checks through retained gate states."""

from __future__ import annotations

from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor
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
    reason: str | None = None


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
    result = session.execute(pattern, keep="case")
    if spec.reason is not None:
        leaves = result.get("leaves")
        if not isinstance(leaves, list) or len(leaves) != 1 or leaves[0].get("reason") != spec.reason:
            raise GateError(f"{case['id']}: expected execution reason {spec.reason}, got {leaves}")
    return check_case(session, case, spec)


def native_corpus(
    gate: Path, definition_ir: Path, module: str,
    cases: list[Mapping[str, Any]], spec: Specification, jobs: int = 1,
) -> list[dict[str, Any]]:
    """Run selected native cases with one loaded session per worker."""

    if jobs < 1:
        raise GateError("jobs must be at least one")

    def run_batch(batch: list[tuple[int, Mapping[str, Any]]]) -> list[tuple[int, dict[str, Any]]]:
        with krs_gate.Session(gate) as session:
            session.load(definition_ir, module)
            return [(index, native_case(session, case, spec)) for index, case in batch]

    indexed = list(enumerate(cases))
    batches = [indexed[offset::jobs] for offset in range(min(jobs, len(indexed)))]
    if len(batches) == 1:
        return [outcome for _, outcome in run_batch(batches[0])]
    with ThreadPoolExecutor(max_workers=len(batches)) as pool:
        completed = pool.map(run_batch, batches)
        ordered = sorted((item for batch in completed for item in batch), key=lambda item: item[0])
    return [outcome for _, outcome in ordered]


def java_case(
    session: krs_gate.Session, case: Mapping[str, Any], spec: Specification, kore: str,
) -> dict[str, Any]:
    """Retain Java KORE and run the same expectations and outcome builder."""

    session.read(kore, "case")
    return check_case(session, case, spec)
