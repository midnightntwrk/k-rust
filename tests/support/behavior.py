"""Shared native and Java case checks through retained gate states.

A behavior corpus declares its checks as data.
Top-level `observe` lists the cells every case checks, and `[expect]` gives default expectations.
A case lists further cells in `observe` and declares its own expectations as `expect.<cell>`.
A case checks the top-level cells, its own `observe` cells, and its expectation keys, in first-seen order,
and every checked cell must have a case or default expectation.
A string expectation is surface text compared structurally;
`{ size = N }` checks a collection size and `{ head = "text" }` the head of a K sequence.
Top-level `reason`, when present, is the required stop reason of the single execution leaf.
Top-level `[report]` maps a checked cell to the field that reports its expected value in the pinned outcome;
a port's outcome hook may refine that record.
"""

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
    """Port configuration and optional outcome refinement."""

    variables: Callable[[Mapping[str, Any]], dict[str, str]]
    outcome: Callable[[Mapping[str, Any], dict[str, Any]], dict[str, Any]] | None = None


def _expectation(case: Mapping[str, Any], cell: str, value: Any) -> Expectation:
    if isinstance(value, str):
        return Expectation(cell, text=value)
    if isinstance(value, Mapping) and len(value) == 1:
        if "size" in value and type(value["size"]) is int and value["size"] >= 0:
            return Expectation(cell, size=value["size"])
        if "head" in value and isinstance(value["head"], str):
            return Expectation(cell, head=value["head"])
    raise GateError(f"{case['id']}: malformed expectation for cell {cell}: {value!r}")


def expectations(corpus: Mapping[str, Any], case: Mapping[str, Any]) -> list[Expectation]:
    """Resolve corpus defaults and case declarations in first-seen cell order."""

    declarations = []
    for source in (corpus, case):
        values = source.get("expect", {})
        if not isinstance(values, Mapping):
            raise GateError(f"{case['id']}: expect must be a table")
        declarations.append({cell: _expectation(case, cell, value) for cell, value in values.items()})
    defaults, overrides = declarations
    cells = []
    for source in (corpus, case):
        observed = source.get("observe", [])
        if not isinstance(observed, list) or any(not isinstance(cell, str) for cell in observed):
            raise GateError(f"{case['id']}: observe must be a list of cell names")
        cells.extend(observed)
    cells.extend(overrides)
    resolved = []
    for cell in dict.fromkeys(cells):
        item = overrides.get(cell, defaults.get(cell))
        if item is None:
            raise GateError(f"{case['id']}: missing expectation for cell {cell}")
        resolved.append(item)
    return resolved


def outcome_record(
    corpus: Mapping[str, Any], case: Mapping[str, Any], spec: Specification,
) -> dict[str, Any]:
    """Report declared expectation values and apply the port's optional hook."""

    report = corpus.get("report", {})
    if not isinstance(report, Mapping) or any(not isinstance(field, str) for field in report.values()):
        raise GateError(f"{case['id']}: report must map cells to field names")
    record = {"id": case["id"]}
    for item in expectations(corpus, case):
        if item.cell in report:
            record[report[item.cell]] = next(value for value in (item.text, item.size, item.head) if value is not None)
    return record if spec.outcome is None else spec.outcome(case, record)


def check_case(
    session: krs_gate.Session, case: Mapping[str, Any], spec: Specification, corpus: Mapping[str, Any],
) -> dict[str, Any]:
    """Check the retained state and return the port's pinned outcome shape."""

    for item in expectations(corpus, case):
        try:
            session.expect("case", item.cell, text=item.text, size=item.size, head=item.head)
        except GateError as error:
            raise GateError(f"{case['id']}: {error}") from error
    return outcome_record(corpus, case, spec)


def native_case(
    session: krs_gate.Session, case: Mapping[str, Any], spec: Specification, corpus: Mapping[str, Any],
) -> dict[str, Any]:
    """Configure, execute, retain, and check one native case."""

    pattern = session.configure(spec.variables(case))["pattern"]
    result = session.execute(pattern, keep="case")
    reason = corpus.get("reason")
    if reason is not None:
        leaves = result.get("leaves")
        if not isinstance(leaves, list) or len(leaves) != 1 or leaves[0].get("reason") != reason:
            raise GateError(f"{case['id']}: expected execution reason {reason}, got {leaves}")
    return check_case(session, case, spec, corpus)


def native_corpus(
    gate: Path, definition_ir: Path, module: str,
    cases: list[Mapping[str, Any]], spec: Specification, corpus: Mapping[str, Any], *,
    definition_kore_sha256: str, jobs: int = 1,
) -> list[dict[str, Any]]:
    """Run selected native cases with one loaded session per worker."""

    if jobs < 1:
        raise GateError("jobs must be at least one")

    def run_batch(batch: list[tuple[int, Mapping[str, Any]]]) -> list[tuple[int, dict[str, Any]]]:
        with krs_gate.Session(gate) as session:
            session.load(definition_ir, module, definition_kore_sha256=definition_kore_sha256)
            return [(index, native_case(session, case, spec, corpus)) for index, case in batch]

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
    corpus: Mapping[str, Any],
) -> dict[str, Any]:
    """Retain Java KORE and run the same expectations and outcome builder."""

    session.read(kore, "case")
    return check_case(session, case, spec, corpus)
