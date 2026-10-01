#!/usr/bin/env python3
"""Fail-closed qualification for the functionally reconstructed IMP static semantics oracle."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
import tempfile
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry, krs_gate  # noqa: E402
from support.checkouts import verify_checkout  # noqa: E402
from support.lock import k_commit, k_version  # noqa: E402
from support.hashing import json_sha256, sha256_file, sha256_text  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import checkout_scratch, k_tool, z3_environment  # noqa: E402


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
INPUT_PIN_KEYS = frozenset({"schema", "oracle", "upstream_imp", "reconstruction", "corpus_sha256"})
OUTPUT_PIN_KEYS = frozenset({"static_execution", "proof_outcomes", "qualified_proof_outcomes"})
CONSTRAINT_LABELS = frozenset({"#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"})


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
        (name, STATIC_SPEC, "KRS-IMP-STATIC-SPEC", name, 100)
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
    session: krs_gate.Session,
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
        normalized_result = session.kast_normalize("static_proof", text=process.stdout)
        normalized_claim = session.kast_normalize(
            "static_claim", path=spec_json, label=case["claim"]
        )
        evidence = session.kast_frontier(
            "proof", normalized_result, returncode=process.returncode, stderr=process.stderr,
            constraint_labels=sorted(CONSTRAINT_LABELS),
        )
    except (OSError, ValueError, GateError) as error:
        raise GateError(f"incomplete proof evidence for {case['name']}: {error}") from error
    frontier = evidence["frontier"]
    return {
        "status": evidence["status"],
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
        "oracle": "imp-static-semantics-reconstructed",
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
    parser.add_argument("--record", action="store_true")
    options = parser.parse_args()
    if options.timeout <= 0:
        raise GateError("--timeout must be positive")
    pins = Ledger(PINS, record=options.record)

    kompile = k_tool("kompile", k_version())
    kprove = k_tool("kprove", k_version())
    krun = k_tool("krun", k_version())
    verify_checkout(K, k_commit(), label="K")
    upstream_commit = str(pins.table("upstream_imp").get("commit"))
    verify_checkout(IMP, upstream_commit, label="IMP")

    gate = krs_gate.configured_or_build(checkout_scratch() / "imp-static-semantics-root-target")
    with (
        krs_gate.Session(gate, environment=z3_environment()) as session,
        tempfile.TemporaryDirectory(prefix="krs-imp-static-reconstructed-") as temporary,
    ):
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
                "KRS-IMP-STATIC",
                "--syntax-module",
                "KRS-IMP-STATIC-SYNTAX",
                "--emit-json",
                "--output-definition",
                definition,
            ],
            timeout=options.timeout,
            check=False,
        )
        if compiled.returncode != 0:
            raise GateError(f"IMP static semantics compilation failed:\n{compiled.stderr}")
        print("PASS IMP static semantics compile: reconstructed static definition")

        executed = run(
            [krun, STATIC_PROGRAM, "-cENV=.Map", "-d", definition, "--output", "pretty", "--color", "off"],
            timeout=options.timeout,
            check=False,
        )
        compact = re.sub(r"\s+", " ", executed.stdout)
        if executed.returncode != 0 or "x |-> 6" not in compact or "y |-> zeroAlias" not in compact:
            raise GateError(f"static execution differs:\n{executed.stdout}\n{executed.stderr}")
        print("PASS IMP static semantics execution: x=6, y=0 (reversible zeroAlias unparse)")

        verify_diagnostic(
            kompile=kompile,
            fixture=HERE / "fixtures/induced-definition-error.k",
            module="KRS-IMP-STATIC-INDUCED-DEFINITION-ERROR",
            workspace=workspace,
            timeout=options.timeout,
        )
        verify_diagnostic(
            kompile=kompile,
            fixture=HERE / "fixtures/induced-source-error.k",
            module="KRS-IMP-STATIC-INDUCED-SOURCE-ERROR",
            workspace=workspace,
            timeout=options.timeout,
        )
        print("PASS IMP static semantics diagnostics: outer and semantic failures remain fail-closed")

        outcomes: dict[str, dict[str, Any]] = {}
        for case in proof_cases():
            outcome = prove(
                case,
                kprove=kprove,
                session=session,
                definition=definition,
                workspace=workspace,
                timeout=options.timeout,
            )
            outcomes[case["name"]] = outcome
            print(
                f"PASS IMP static semantics proof {case['name']}: {outcome['status']}, "
                f"frontier={outcome['frontier_count']}"
            )

    observed = observed_ledger(outcomes, upstream_commit)
    observed_keys = set(observed)
    pin_keys = set(pins.data)
    missing_keys = observed_keys - pin_keys
    if (
        observed_keys != INPUT_PIN_KEYS | OUTPUT_PIN_KEYS
        or pin_keys - observed_keys
        or missing_keys - (OUTPUT_PIN_KEYS if pins.record else set())
    ):
        raise GateError("IMP static semantics reconstructed pin keys differ from live evidence")
    for key in INPUT_PIN_KEYS:
        if pins.get(key) != observed[key]:
            raise GateError(f"IMP static semantics input pin {key} differs from live evidence")
    for key in OUTPUT_PIN_KEYS:
        pins.expect(key, observed[key])
    print(f"PASS IMP static semantics reconstructed oracle: evidence={json_sha256(observed)}")
    pins.finish("IMP static semantics")
    return 0


if __name__ == "__main__":
    entry("IMP static semantics", main, errors=(OSError, ValueError))
