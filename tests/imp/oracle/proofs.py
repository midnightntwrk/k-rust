"""Native bounded-proof evidence and pin comparisons for complete IMP.

Proof evidence must include explicit semantic bounds and a native termination classification.
The caller must own each proof process group and terminate its descendants on timeout.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from support import GateError, krs_gate
from support.hashing import canonical_json, json_sha256, sha256_text


@dataclass(frozen=True)
class ProofBounds:
    depth: int
    branching_allowed: int

    def __post_init__(self) -> None:
        if type(self.depth) is not int or self.depth < 0:
            raise GateError("proof depth must be a non-negative integer")
        if type(self.branching_allowed) is not int or self.branching_allowed <= 0:
            raise GateError("branching_allowed must be a positive integer")


@dataclass(frozen=True)
class ProofCase:
    name: str
    spec: Path
    spec_module: str
    claim: str
    bounds: ProofBounds
    include_directories: tuple[Path, ...] = ()


@dataclass(frozen=True)
class ProofEvidence:
    schema: int
    name: str
    claim_label: str
    status: str
    bounds: ProofBounds
    frontier_count: int
    frontier: tuple[str, ...]
    user_labels: tuple[str, ...]
    normalized_result: Mapping[str, Any]
    normalized_claim: Mapping[str, Any]
    result_sha256: str
    claim_sha256: str

    def pin(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "bounds": {
                "depth": self.bounds.depth,
                "branching_allowed": self.bounds.branching_allowed,
            },
            "frontier_count": self.frontier_count,
            "frontier_sha256": sha256_text("\n".join(self.frontier)),
            "user_labels": list(self.user_labels),
            "result_sha256": self.result_sha256,
            "claim_sha256": self.claim_sha256,
        }


def evidence_from_inputs(
    *,
    session: krs_gate.Session,
    case: ProofCase,
    result: Mapping[str, Any],
    claim: Mapping[str, Any],
    returncode: int,
    stderr: str,
    user_labels: Sequence[str],
    policy: Mapping[str, Any],
    constraint_labels: Sequence[str],
) -> ProofEvidence:
    """Normalize opaque proof inputs and classify their bounded native evidence."""

    normalized_result = session.kast_normalize("proof_result", **result, policy=policy)
    normalized_claim = session.kast_normalize("proof_claim", **claim, label=case.claim, policy=policy)
    normalized_label = policy.get("label_map", {}).get(case.claim, case.claim)
    evidence = session.kast_frontier(
        "proof", normalized_result, returncode=returncode, stderr=stderr,
        constraint_labels=constraint_labels,
    )
    frontier = tuple(evidence["frontier"])
    labels = tuple(sorted(set(user_labels)))
    if any(not isinstance(label, str) or not label for label in labels):
        raise GateError("applied user labels must be non-empty strings")
    return ProofEvidence(
        schema=1,
        name=case.name,
        claim_label=normalized_label,
        status=evidence["status"],
        bounds=case.bounds,
        frontier_count=len(frontier),
        frontier=frontier,
        user_labels=labels,
        normalized_result=normalized_result,
        normalized_claim=normalized_claim,
        result_sha256=json_sha256(normalized_result),
        claim_sha256=json_sha256(normalized_claim),
    )


def compare_proof_evidence(
    reference: Mapping[str, ProofEvidence],
    actual: Mapping[str, ProofEvidence],
    expected_pins: Mapping[str, Any],
) -> Mapping[str, dict[str, Any]]:
    """Require identical claim, status, frontier/constraints, and user labels."""

    if set(reference) != set(actual) or set(reference) != set(expected_pins):
        raise GateError(
            "proof case sets differ: "
            f"reference={sorted(reference)}, actual={sorted(actual)}, pins={sorted(expected_pins)}"
        )
    observed: dict[str, dict[str, Any]] = {}
    for name in sorted(reference):
        left = reference[name]
        right = actual[name]
        if left.name != name or right.name != name:
            raise GateError(f"proof evidence name mismatch for {name}")
        if left.claim_label != right.claim_label:
            raise GateError(f"claim label differs for {name}")
        semantic_left = (
            left.status,
            left.bounds,
            left.frontier,
            left.user_labels,
            left.normalized_result,
            left.normalized_claim,
        )
        semantic_right = (
            right.status,
            right.bounds,
            right.frontier,
            right.user_labels,
            right.normalized_result,
            right.normalized_claim,
        )
        if semantic_left != semantic_right:
            raise GateError(f"semantic proof evidence differs for {name}")
        pin = right.pin()
        if set(expected_pins[name]) != set(pin):
            raise GateError(f"unknown or missing pin fields for {name}")
        if expected_pins[name] != pin:
            raise GateError(f"proof pin differs for {name}: observed={canonical_json(pin)}")
        observed[name] = pin
    return observed

