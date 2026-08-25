"""Bounded, evidence-first proof comparison for complete IMP.

This module never treats an arbitrary exit status as proof evidence.  Every
run has explicit semantic bounds and owns a new process session, so a timeout
terminates Java, kore-exec, Z3, and other descendants as one group.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
from typing import Any, Mapping, Sequence

try:
    from .source_definition import DEFAULT_METADATA_ATTRIBUTES, NODE_FIELDS, canonical, digest
except ImportError:  # Direct loading by tests/m4/verify.py.
    from source_definition import DEFAULT_METADATA_ATTRIBUTES, NODE_FIELDS, canonical, digest


M3D_HELPER_SHA256 = "2ed14f41b39cf95fdfd132d1fa675c3d550375c75499d78711a2c901d023bc9f"
M3D_SELECTED_CASES = frozenset(
    {
        "addition-1",
        "addition-var",
        "branching",
        "sum-loop",
        "sum-spec",
        "addition-depth-zero",
    }
)


class ProofError(RuntimeError):
    """Proof evidence is incomplete, malformed, unbounded, or different."""


CLAIM_NODE_FIELDS: Mapping[str, frozenset[frozenset[str]]] = {
    **NODE_FIELDS,
    "KFlatModuleList": frozenset({frozenset({"node", "mainModule", "term"})}),
}


@dataclass(frozen=True)
class ProofPolicy:
    label_map: Mapping[str, str] = field(default_factory=dict)
    identity_labels: frozenset[str] = frozenset()
    sort_map: Mapping[str, str] = field(default_factory=dict)
    identity_sorts: frozenset[str] = frozenset()
    known_attributes: frozenset[str] = DEFAULT_METADATA_ATTRIBUTES
    metadata_attributes: frozenset[str] = DEFAULT_METADATA_ATTRIBUTES
    constraint_labels: frozenset[str] = frozenset(
        {"#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"}
    )

    def __post_init__(self) -> None:
        if not self.metadata_attributes <= self.known_attributes:
            raise ProofError("every removable proof metadata attribute must be known")


@dataclass(frozen=True)
class ProofBounds:
    depth: int
    branching_allowed: int

    def __post_init__(self) -> None:
        if type(self.depth) is not int or self.depth < 0:
            raise ProofError("proof depth must be a non-negative integer")
        if type(self.branching_allowed) is not int or self.branching_allowed <= 0:
            raise ProofError("branching_allowed must be a positive integer")


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
            "frontier_sha256": hashlib.sha256(
                "\n".join(self.frontier).encode()
            ).hexdigest(),
            "user_labels": list(self.user_labels),
            "result_sha256": self.result_sha256,
            "claim_sha256": self.claim_sha256,
        }


def _fields(node: Mapping[str, Any], schemas: Mapping[str, frozenset[frozenset[str]]]) -> str:
    kind = node.get("node")
    if not isinstance(kind, str) or kind not in schemas:
        raise ProofError(f"unclassified proof KAST node {kind!r}")
    if frozenset(node) not in schemas[kind]:
        raise ProofError(f"unknown {kind} fields: {sorted(node)}")
    return kind


class _Normalizer:
    def __init__(self, policy: ProofPolicy, *, claim: bool) -> None:
        self.policy = policy
        self.claim = claim
        self.variables: dict[tuple[str, str, str], str] = {}

    def _mapped(self, raw: Any, mapping: Mapping[str, str], identities: frozenset[str], kind: str) -> str:
        if not isinstance(raw, str):
            raise ProofError(f"{kind} is not a string")
        if raw in mapping:
            return mapping[raw]
        if raw in identities:
            return raw
        raise ProofError(f"unknown proof {kind} {raw!r}")

    def visit(self, value: Any, *, attribute_payload: bool = False) -> Any:
        if isinstance(value, list):
            return [self.visit(child, attribute_payload=attribute_payload) for child in value]
        if not isinstance(value, dict):
            if isinstance(value, (str, int, bool)) or value is None:
                return value
            raise ProofError(f"unsupported proof scalar {value!r}")
        if "node" not in value:
            if not attribute_payload:
                raise ProofError(f"unclassified proof object fields: {sorted(value)}")
            return {
                key: self.visit(child, attribute_payload=True)
                for key, child in sorted(value.items())
            }
        schemas = CLAIM_NODE_FIELDS if self.claim else NODE_FIELDS
        kind = _fields(value, schemas)
        if not self.claim and kind not in {
            "KApply", "KLabel", "KSort", "KToken", "KVariable", "KSequence", "KRewrite"
        }:
            raise ProofError(f"node {kind} is not valid in a proof result")
        if kind == "KVariable":
            name = value["name"]
            raw_sort = value.get("sort")
            sort = "<unsorted>"
            if raw_sort is not None:
                sort = self._mapped(
                    raw_sort.get("name"),
                    self.policy.sort_map,
                    self.policy.identity_sorts,
                    "sort",
                )
            variable_kind = (
                "existential" if str(name).startswith("?") else
                "anonymous" if str(name).startswith("_") else "ordinary"
            )
            key = (str(name), variable_kind, sort)
            self.variables.setdefault(key, f"{variable_kind[0].upper()}{len(self.variables)}")
            result: dict[str, Any] = {"node": kind, "name": self.variables[key]}
            if raw_sort is not None:
                result["sort"] = self.visit(raw_sort)
            return result

        result: dict[str, Any] = {}
        for key, child in value.items():
            if kind == "KAtt" and key == "att":
                if not isinstance(child, dict):
                    raise ProofError("KAtt.att is not an object")
                unknown = set(child) - self.policy.known_attributes
                if unknown:
                    raise ProofError(f"unknown proof attributes: {sorted(unknown)}")
                result[key] = {}
                for name, item in child.items():
                    if name in self.policy.metadata_attributes:
                        continue
                    if name == "label" and isinstance(item, str):
                        result[key][name] = self._mapped(
                            item,
                            self.policy.label_map,
                            self.policy.identity_labels,
                            "label",
                        )
                    else:
                        result[key][name] = self.visit(item, attribute_payload=True)
            elif kind == "KLabel" and key == "name":
                result[key] = self._mapped(
                    child, self.policy.label_map, self.policy.identity_labels, "label"
                )
            elif kind == "KSort" and key == "name":
                result[key] = self._mapped(
                    child, self.policy.sort_map, self.policy.identity_sorts, "sort"
                )
            else:
                result[key] = self.visit(child, attribute_payload=attribute_payload)
        if kind in {"KApply", "KSequence"}:
            children = result["args"] if kind == "KApply" else result["items"]
            if result["arity"] != len(children):
                raise ProofError(f"invalid {kind} arity")
        if kind == "KFlatModule":
            result["imports"].sort(key=canonical)
            result["localSentences"].sort(key=canonical)
        return result


def _envelope(value: Mapping[str, Any]) -> Mapping[str, Any]:
    if (
        set(value) != {"format", "version", "term"}
        or value.get("format") != "KAST"
        or value.get("version") != 4
    ):
        raise ProofError("proof evidence is not exactly a KAST v4 envelope")
    return value


def normalize_result(value: Mapping[str, Any], policy: ProofPolicy) -> dict[str, Any]:
    envelope = _envelope(value)
    return {
        "format": "KAST",
        "version": 4,
        "term": _Normalizer(policy, claim=False).visit(copy.deepcopy(envelope["term"])),
    }


def _claim_label(claim: Mapping[str, Any]) -> str | None:
    att = claim.get("att")
    if not isinstance(att, dict) or att.get("node") != "KAtt":
        raise ProofError("claim has no exact KAtt")
    attributes = att.get("att")
    if not isinstance(attributes, dict):
        raise ProofError("claim attributes are not an object")
    label = attributes.get("label")
    return label if isinstance(label, str) else None


def extract_claim(value: Mapping[str, Any], label: str) -> Mapping[str, Any]:
    """Select exactly one labeled KClaim without normalizing away its structure."""

    _envelope(value)
    claims: list[Mapping[str, Any]] = []

    def visit(node: Any) -> None:
        if isinstance(node, list):
            for child in node:
                visit(child)
        elif isinstance(node, dict):
            if "node" in node:
                _fields(node, CLAIM_NODE_FIELDS)
                if node["node"] == "KClaim" and _claim_label(node) == label:
                    claims.append(node)
            for child in node.values():
                visit(child)

    visit(value["term"])
    if len(claims) != 1:
        raise ProofError(f"expected exactly one KClaim {label!r}, found {len(claims)}")
    return claims[0]


def normalize_claim(value: Mapping[str, Any], label: str, policy: ProofPolicy) -> dict[str, Any]:
    claim = extract_claim(value, label)
    normalized = _Normalizer(policy, claim=True).visit(copy.deepcopy(claim))
    attributes = normalized["att"]["att"]
    if "priority" in attributes:
        raise ProofError("claims must not carry rule/equation priority")
    return {"format": "KRS-M4-CLAIM", "version": 1, "term": normalized}


def _root_label(result: Mapping[str, Any]) -> str | None:
    term = result["term"]
    if not isinstance(term, dict):
        raise ProofError("normalized result term is not an object")
    label = term.get("label")
    if label is None:
        return None
    if not isinstance(label, dict) or label.get("node") != "KLabel":
        raise ProofError("proof result has malformed root label")
    name = label.get("name")
    if not isinstance(name, str):
        raise ProofError("proof root label has no string name")
    return name


def classify(returncode: int, root: str | None, stderr: str) -> str:
    if returncode == 0 and root == "#Top":
        return "proved"
    stalled = re.search(r"configuration cannot be\s+rewritten further", stderr) is not None
    if returncode == 1 and root == "#Bottom":
        return "failed"
    if returncode == 1 and root not in {"#Top", "#Bottom"} and stalled:
        return "incomplete"
    raise ProofError(f"unclassified proof termination: rc={returncode}, root={root!r}")


def _flatten(root: Any, label: str) -> list[Any]:
    if (
        isinstance(root, dict)
        and root.get("node") == "KApply"
        and root.get("label", {}).get("name") == label
    ):
        result: list[Any] = []
        for child in root["args"]:
            result.extend(_flatten(child, label))
        return result
    return [root]


def _frontier(result: Mapping[str, Any], policy: ProofPolicy) -> tuple[str, ...]:
    term = result["term"]
    root = _root_label(result)
    if root in {"#Top", "#Bottom"}:
        return ()
    branches = _flatten(term, "#Or")
    normalized: list[str] = []
    for branch in branches:
        conjuncts = _flatten(branch, "#And")
        constraints: list[Any] = []
        states: list[Any] = []
        for conjunct in conjuncts:
            name = (
                conjunct.get("label", {}).get("name")
                if isinstance(conjunct, dict)
                else None
            )
            (constraints if name in policy.constraint_labels else states).append(conjunct)
        normalized.append(
            canonical(
                {
                    "states": sorted(states, key=canonical),
                    "constraints": sorted(constraints, key=canonical),
                }
            )
        )
    return tuple(sorted(normalized))


def evidence_from_values(
    *,
    case: ProofCase,
    result_value: Mapping[str, Any],
    claim_value: Mapping[str, Any],
    returncode: int,
    stderr: str,
    user_labels: Sequence[str],
    policy: ProofPolicy,
) -> ProofEvidence:
    normalized_result = normalize_result(result_value, policy)
    normalized_claim = normalize_claim(claim_value, case.claim, policy)
    normalized_label = _claim_label(normalized_claim["term"])
    if normalized_label is None:
        raise ProofError("normalized claim has no explicit label")
    root = _root_label(normalized_result)
    status = classify(returncode, root, stderr)
    frontier = _frontier(normalized_result, policy)
    labels = tuple(sorted(set(user_labels)))
    if any(not isinstance(label, str) or not label for label in labels):
        raise ProofError("applied user labels must be non-empty strings")
    return ProofEvidence(
        schema=1,
        name=case.name,
        claim_label=normalized_label,
        status=status,
        bounds=case.bounds,
        frontier_count=len(frontier),
        frontier=frontier,
        user_labels=labels,
        normalized_result=normalized_result,
        normalized_claim=normalized_claim,
        result_sha256=digest(normalized_result),
        claim_sha256=digest(normalized_claim),
    )


def _run_session(command: Sequence[str], *, timeout: int) -> subprocess.CompletedProcess[str]:
    if timeout <= 0:
        raise ProofError("proof wall-clock safety timeout must be positive")
    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C"})
    process = subprocess.Popen(
        list(command),
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as error:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            stdout, stderr = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
        raise ProofError(
            "proof exceeded its wall-clock safety timeout; no semantic status was pinned "
            "and the complete process group was terminated"
        ) from error
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        raise
    return subprocess.CompletedProcess(list(command), process.returncode, stdout, stderr)


def run_bounded_source_proof(
    *,
    kprove: str,
    definition: Path,
    case: ProofCase,
    spec_json: Path,
    policy: ProofPolicy,
    timeout_seconds: int,
    user_labels: Sequence[str] = (),
) -> ProofEvidence:
    """Run one explicitly depth/branch bounded emitted-source proof."""

    command = [
        kprove,
        str(case.spec),
        "-d",
        str(definition),
        "--spec-module",
        case.spec_module,
        "--claims",
        case.claim,
        "--output",
        "json",
        "--emit-json-spec",
        str(spec_json),
        "--depth",
        str(case.bounds.depth),
        "--branching-allowed",
        str(case.bounds.branching_allowed),
    ]
    for include in case.include_directories:
        command.extend(["-I", str(include)])
    process = _run_session(command, timeout=timeout_seconds)
    try:
        result = json.loads(process.stdout)
        claim = json.loads(spec_json.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as error:
        raise ProofError(f"proof did not emit complete JSON evidence: {error}") from error
    return evidence_from_values(
        case=case,
        result_value=result,
        claim_value=claim,
        returncode=process.returncode,
        stderr=process.stderr,
        user_labels=user_labels,
        policy=policy,
    )


def compare_proof_evidence(
    reference: Mapping[str, ProofEvidence],
    actual: Mapping[str, ProofEvidence],
    expected_pins: Mapping[str, Any],
) -> Mapping[str, dict[str, Any]]:
    """Require identical claim, status, frontier/constraints, and user labels."""

    if set(reference) != set(actual) or set(reference) != set(expected_pins):
        raise ProofError(
            "proof case sets differ: "
            f"reference={sorted(reference)}, actual={sorted(actual)}, pins={sorted(expected_pins)}"
        )
    observed: dict[str, dict[str, Any]] = {}
    for name in sorted(reference):
        left = reference[name]
        right = actual[name]
        if left.name != name or right.name != name:
            raise ProofError(f"proof evidence name mismatch for {name}")
        if left.claim_label != right.claim_label:
            raise ProofError(f"claim label differs for {name}")
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
            raise ProofError(f"semantic proof evidence differs for {name}")
        pin = right.pin()
        if set(expected_pins[name]) != set(pin):
            raise ProofError(f"unknown or missing pin fields for {name}")
        if expected_pins[name] != pin:
            raise ProofError(f"proof pin differs for {name}: observed={canonical(pin)}")
        observed[name] = pin
    return observed


def verify_m3d_selected_pins(
    root: Path,
    evidence: Mapping[str, ProofEvidence],
    legacy_outcomes: Mapping[str, Mapping[str, str]],
) -> None:
    """Check the six individually frozen M3D invocations.

    The legacy ``static-adjunct`` pin covers a five-claim module as one run, so
    it cannot validate M4's five individually selectable adjunct claims.  Root
    must provide new per-claim M4 pins for those cases.
    """

    helper = root / "tests" / "m3d" / "verify.py"
    if hashlib.sha256(helper.read_bytes()).hexdigest() != M3D_HELPER_SHA256:
        raise ProofError("frozen M3D proof normalizer hash differs")
    pins_path = root / "tests" / "m3d" / "pins.json"
    pins = json.loads(pins_path.read_text(encoding="utf-8")).get("proof_outcomes")
    if not isinstance(pins, dict):
        raise ProofError("M3D proof pins are absent")
    if set(evidence) != M3D_SELECTED_CASES:
        raise ProofError(
            f"M3D selected evidence must be exactly {sorted(M3D_SELECTED_CASES)}"
        )
    if set(legacy_outcomes) != M3D_SELECTED_CASES:
        raise ProofError("legacy M3D outcomes must cover exactly the selected invocations")
    for name, item in evidence.items():
        legacy = pins.get(name)
        if not isinstance(legacy, dict) or set(legacy) != {
            "status", "result_sha256", "claim_sha256"
        }:
            raise ProofError(f"legacy M3D pin shape differs for {name}")
        if legacy_outcomes[name] != legacy:
            raise ProofError(f"frozen M3D hash evidence differs for {name}")
        legacy_status = "incomplete" if legacy["status"] == "frontier" else legacy["status"]
        if item.status != legacy_status:
            raise ProofError(f"M4 status differs from M3D for {name}")
