#!/usr/bin/env python3
"""Fail-closed qualification for the functionally reconstructed M3D oracle."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
import tempfile
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from m3d.normalize import envelope, normalize_claim_spec, normalize_proof  # noqa: E402
from support import ROOT, GateError  # noqa: E402
from support.checkouts import verify_checkout  # noqa: E402
from support.lock import k_commit, k_version  # noqa: E402
from support.hashing import canonical_json, json_sha256, sha256_file, sha256_text  # noqa: E402
from support.pins import load_json  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool  # noqa: E402


HERE = Path(__file__).resolve().parent
WORKSPACE_ROOT = ROOT.parent
IMP = WORKSPACE_ROOT / "inspirations/runtimeverification/imp-semantics"
K = WORKSPACE_ROOT / "inspirations/runtimeverification/k"
IMP_DEFINITION = IMP / "src/kimp/kdist/imp-semantics"
IMP_SPECS = IMP / "examples/specs"
FIXTURE = HERE / "fixtures/static-adjunct.k"
STATIC_SPEC = HERE / "claims/static-spec.k"
STATIC_PROGRAM = HERE / "corpus/static-evaluation.imp"
PINS = HERE / "pins.json"
CONSTRAINT_LABELS = frozenset({"#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"})


def root_label(normalized: dict[str, Any]) -> str | None:
    term = normalized.get("term")
    if not isinstance(term, dict):
        raise GateError("normalized proof has no object term")
    label = term.get("label")
    if label is None:
        return None
    if not isinstance(label, dict) or not isinstance(label.get("name"), str):
        raise GateError("normalized proof root label is malformed")
    return label["name"]


def flatten(root: Any, label: str) -> list[Any]:
    if (
        isinstance(root, dict)
        and root.get("node") == "KApply"
        and root.get("label", {}).get("name") == label
    ):
        result: list[Any] = []
        for child in root["args"]:
            result.extend(flatten(child, label))
        return result
    return [root]


def normalized_frontier(normalized: dict[str, Any]) -> tuple[str, ...]:
    term = normalized["term"]
    if root_label(normalized) in {"#Top", "#Bottom"}:
        return ()
    frontier: list[str] = []
    for branch in flatten(term, "#Or"):
        states: list[Any] = []
        constraints: list[Any] = []
        for conjunct in flatten(branch, "#And"):
            name = conjunct.get("label", {}).get("name") if isinstance(conjunct, dict) else None
            (constraints if name in CONSTRAINT_LABELS else states).append(conjunct)
        frontier.append(
            canonical_json(
                {
                    "states": sorted(states, key=canonical_json),
                    "constraints": sorted(constraints, key=canonical_json),
                }
            )
        )
    return tuple(sorted(frontier))


def classify(returncode: int, root: str | None, stderr: str) -> str:
    if returncode == 0 and root == "#Top":
        return "proved"
    if returncode == 1 and root == "#Bottom":
        return "failed"
    stalled = re.search(r"configuration cannot be\s+rewritten further", stderr) is not None
    if returncode == 1 and root not in {"#Top", "#Bottom"} and stalled:
        return "incomplete"
    raise GateError(
        f"unclassified bounded proof termination: rc={returncode}, root={root!r}"
    )


def unique_claim(value: dict[str, Any]) -> dict[str, Any]:
    found: list[dict[str, Any]] = []

    def visit(node: Any) -> None:
        if isinstance(node, list):
            for child in node:
                visit(child)
        elif isinstance(node, dict):
            if node.get("node") == "KClaim":
                found.append(node)
            for child in node.values():
                visit(child)

    visit(value)
    if len(found) != 1:
        raise GateError(f"expected one selected KClaim, found {len(found)}")
    return found[0]


def proof_cases() -> tuple[dict[str, Any], ...]:
    selected = (
        ("addition-1", "imp-simple-spec.k", "IMP-SIMPLE-SPEC", "addition-1", 100),
        ("addition-var", "imp-simple-spec.k", "IMP-SIMPLE-SPEC", "addition-var", 100),
        ("branching", "imp-simple-spec.k", "IMP-SIMPLE-SPEC", "branching", 100),
        ("sum-loop", "imp-simple-spec.k", "IMP-SIMPLE-SPEC", "sum-loop", 100),
        ("sum-spec", "imp-sum-spec.k", "IMP-SUM-SPEC", "sum-spec", 100),
        ("addition-depth-zero", "imp-simple-spec.k", "IMP-SIMPLE-SPEC", "addition-1", 0),
    )
    adjunct = tuple(
        (name, STATIC_SPEC, "KRS-M3D-STATIC-SPEC", name, 100)
        for name in (
            "total-equation",
            "partial-equation",
            "explicit-priority",
            "static-alias",
            "context-alias",
        )
    )
    return tuple(
        {
            "name": name,
            "spec": IMP_SPECS / spec if isinstance(spec, str) else spec,
            "module": module,
            "claim": f"{module}.{claim}",
            "depth": depth,
        }
        for name, spec, module, claim, depth in selected + adjunct
    )


def prove(
    case: dict[str, Any],
    *,
    kprove: str,
    definition: Path,
    workspace: Path,
    timeout: int,
) -> dict[str, Any]:
    spec_json = workspace / f"{case['name']}-spec.json"
    process = run(
        [
            kprove,
            case["spec"],
            "-d",
            definition,
            "-I",
            IMP_DEFINITION,
            "-I",
            FIXTURE.parent,
            "--spec-module",
            case["module"],
            "--claims",
            case["claim"],
            "--output",
            "json",
            "--emit-json-spec",
            spec_json,
            "--depth",
            str(case["depth"]),
            "--branching-allowed",
            "64",
        ],
        timeout=timeout,
        check=False,
    )
    try:
        normalized_result = normalize_proof(envelope(process.stdout))
        claim_value = json.loads(spec_json.read_text(encoding="utf-8"))
        selected = unique_claim(claim_value)
        if selected.get("att", {}).get("att", {}).get("label") != case["claim"]:
            raise GateError(f"selected claim differs for {case['name']}")
        normalized_claim = normalize_claim_spec(claim_value)
    except (OSError, json.JSONDecodeError, ValueError) as error:
        raise GateError(f"incomplete proof evidence for {case['name']}: {error}") from error
    frontier = normalized_frontier(normalized_result)
    return {
        "status": classify(process.returncode, root_label(normalized_result), process.stderr),
        "bounds": {"depth": case["depth"], "branching_allowed": 64},
        "frontier_count": len(frontier),
        "frontier_sha256": sha256_text("\n".join(frontier)),
        "user_labels": [],
        "result_sha256": json_sha256(normalized_result),
        "claim_sha256": json_sha256(normalized_claim),
    }


def corpus_paths() -> dict[str, Path]:
    """The corpus and fixtures the oracle runs; KRS source is deliberately absent."""

    return {
        "claims/static-spec.k": STATIC_SPEC,
        "corpus/static-evaluation.imp": STATIC_PROGRAM,
        "fixtures/induced-definition-error.k": HERE / "fixtures/induced-definition-error.k",
        "fixtures/induced-source-error.k": HERE / "fixtures/induced-source-error.k",
        "fixtures/static-adjunct.k": FIXTURE,
    }


def observed_ledger(outcomes: dict[str, dict[str, Any]], upstream_commit: str) -> dict[str, Any]:
    selected_names = {
        "addition-1",
        "addition-var",
        "branching",
        "sum-loop",
        "sum-spec",
        "addition-depth-zero",
    }
    legacy = {
        name: {
            "status": "frontier" if outcome["status"] == "incomplete" else outcome["status"],
            "result_sha256": outcome["result_sha256"],
            "claim_sha256": outcome["claim_sha256"],
        }
        for name, outcome in outcomes.items()
        if name in selected_names
    }
    return {
        "schema": 1,
        "milestone": "M3D-reconstructed",
        "upstream_imp": {"commit": upstream_commit},
        "reconstruction": {
            "original_verify_sha256": "2ed14f41b39cf95fdfd132d1fa675c3d550375c75499d78711a2c901d023bc9f",
            "original_pins_sha256": "2a27f0efead1c233f59f81d4e7c4fe37b56d8b1dcba203ff52e63d7769ecc085",
            "original_fixture_sha256": "ffbe89ef33ad062c0d1e58f6fc77f52ec0063365155b3042cae8a247a328a462",
            "original_spec_sha256": "2b32479b9e982cac3c8ebb0b6e423662219c9d1ed1d387be80050732a522d444",
            "claim": "functional reconstruction; original blobs unavailable",
        },
        "corpus_sha256": {name: sha256_file(path) for name, path in corpus_paths().items()},
        "static_execution": {
            "program": "corpus/static-evaluation.imp",
            "environment": {"x": 6, "y": 0},
        },
        "proof_outcomes": legacy,
        "qualified_proof_outcomes": outcomes,
    }


def verify_diagnostic(
    *, kompile: str, fixture: Path, module: str, workspace: Path, timeout: int
) -> None:
    process = run(
        [
            kompile,
            fixture,
            "-I",
            IMP_DEFINITION,
            "-I",
            FIXTURE.parent,
            "--backend",
            "haskell",
            "--main-module",
            module,
            "--syntax-module",
            module,
            "--output-definition",
            workspace / module.lower(),
        ],
        timeout=timeout,
        check=False,
    )
    if process.returncode == 0 or "[Error]" not in process.stderr:
        raise GateError(f"induced diagnostic unexpectedly accepted: {fixture}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--write-proposal", type=Path)
    options = parser.parse_args()
    if options.timeout <= 0:
        raise GateError("--timeout must be positive")

    kompile = k_tool("kompile", k_version())
    kprove = k_tool("kprove", k_version())
    krun = k_tool("krun", k_version())
    verify_checkout(K, k_commit(), label="K")
    upstream_commit = str(load_json(PINS).get("upstream_imp", {}).get("commit"))
    verify_checkout(IMP, upstream_commit, label="IMP")

    with tempfile.TemporaryDirectory(prefix="krs-m3d-reconstructed-") as temporary:
        workspace = Path(temporary)
        definition = workspace / "static-kompiled"
        compiled = run(
            [
                kompile,
                FIXTURE,
                "-I",
                IMP_DEFINITION,
                "--backend",
                "haskell",
                "--main-module",
                "KRS-M3D-STATIC",
                "--syntax-module",
                "KRS-M3D-STATIC-SYNTAX",
                "--emit-json",
                "--output-definition",
                definition,
            ],
            timeout=options.timeout,
            check=False,
        )
        if compiled.returncode != 0:
            raise GateError(f"M3D compilation failed:\n{compiled.stderr}")
        print("PASS M3D compile: reconstructed static definition")

        executed = run(
            [krun, STATIC_PROGRAM, "-cENV=.Map", "-d", definition, "--output", "pretty", "--color", "off"],
            timeout=options.timeout,
            check=False,
        )
        compact = re.sub(r"\s+", " ", executed.stdout)
        if executed.returncode != 0 or "x |-> 6" not in compact or "y |-> zeroAlias" not in compact:
            raise GateError(f"static execution differs:\n{executed.stdout}\n{executed.stderr}")
        print("PASS M3D execution: x=6, y=0 (reversible zeroAlias unparse)")

        verify_diagnostic(
            kompile=kompile,
            fixture=HERE / "fixtures/induced-definition-error.k",
            module="KRS-M3D-INDUCED-DEFINITION-ERROR",
            workspace=workspace,
            timeout=options.timeout,
        )
        verify_diagnostic(
            kompile=kompile,
            fixture=HERE / "fixtures/induced-source-error.k",
            module="KRS-M3D-INDUCED-SOURCE-ERROR",
            workspace=workspace,
            timeout=options.timeout,
        )
        print("PASS M3D diagnostics: outer and semantic failures remain fail-closed")

        outcomes: dict[str, dict[str, Any]] = {}
        for case in proof_cases():
            outcome = prove(
                case,
                kprove=kprove,
                definition=definition,
                workspace=workspace,
                timeout=options.timeout,
            )
            outcomes[case["name"]] = outcome
            print(
                f"PASS M3D proof {case['name']}: {outcome['status']}, "
                f"frontier={outcome['frontier_count']}"
            )

    observed = observed_ledger(outcomes, upstream_commit)
    if options.write_proposal is not None:
        destination = options.write_proposal.resolve()
        if destination.exists():
            raise GateError(f"proposal destination exists: {destination}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(observed, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"PASS M3D proposal: {destination}")
        return 0
    if not PINS.is_file():
        raise GateError("reconstructed pins are absent; use --write-proposal")
    expected = json.loads(PINS.read_text(encoding="utf-8"))
    if expected != observed:
        raise GateError("M3D reconstructed pins differ from live evidence")
    print(f"PASS M3D reconstructed oracle: evidence={json_sha256(observed)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, GateError, ValueError) as error:
        print(f"FAIL M3D: {error}", file=sys.stderr)
        raise SystemExit(1) from error
