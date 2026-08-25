#!/usr/bin/env python3
"""Freeze five individually selected M3D static-adjunct reference proofs."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Sequence


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
UPSTREAM_ROOT = ROOT.parent / "inspirations/runtimeverification"
K = UPSTREAM_ROOT / "k"
IMP = UPSTREAM_ROOT / "imp-semantics"
UPSTREAM_DEFINITION = IMP / "src/kimp/kdist/imp-semantics"
FIXTURE = ROOT / "tests/m3d/fixtures/static-adjunct.k"
SPEC = ROOT / "tests/m3d/claims/static-spec.k"
FIXTURES = FIXTURE.parent
CASES = HERE / "cases.json"
PINS = HERE / "pins.json"
SPEC_MODULE = "KRS-M3D-STATIC-SPEC"
MAIN_MODULE = "KRS-M3D-STATIC"
SYNTAX_MODULE = "KRS-M3D-STATIC-SYNTAX"
EVIDENCE_SCHEMA = 1
TERMINATION_GRACE_SECONDS = 5
CLAIM_PATTERN = re.compile(r"\bclaim\s*\[([^\]]+)\]\s*:")
CONSTRAINT_LABELS = frozenset({"#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"})


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-proposal",
        type=Path,
        help="write observed pins to a new path instead of checking pins.json",
    )
    parser.add_argument(
        "--artifacts",
        type=Path,
        help="retain complete normalized evidence beneath this absent/empty directory",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="wall-clock watchdog seconds per tool call; never a proof status",
    )
    return parser.parse_args()


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic_json(path: Path, value: Any) -> None:
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def terminate_session(process: subprocess.Popen[str]) -> tuple[str, str]:
    """Terminate and reap every descendant in the process's owned session."""

    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        return process.communicate(timeout=TERMINATION_GRACE_SECONDS)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        return process.communicate()


def run_session(
    command: Sequence[str], *, timeout: int, cwd: Path = ROOT
) -> subprocess.CompletedProcess[str]:
    """Run one external command in a newly owned, leak-safe process session."""

    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C", "PYTHONDONTWRITEBYTECODE": "1"})
    process = subprocess.Popen(
        list(command),
        cwd=cwd,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as error:
        stdout, stderr = terminate_session(process)
        raise RuntimeError(
            "tool exceeded its wall-clock watchdog; no semantic status was recorded "
            "and its complete process session was terminated\n"
            f"command={list(command)!r}\nstdout={stdout}\nstderr={stderr}"
        ) from error
    except BaseException:
        terminate_session(process)
        raise
    return subprocess.CompletedProcess(list(command), process.returncode, stdout, stderr)


def exact_revision(checkout: Path, expected: str, timeout: int) -> None:
    process = run_session(["git", "rev-parse", "HEAD"], cwd=checkout, timeout=timeout)
    actual = process.stdout.strip()
    if process.returncode != 0 or actual != expected:
        raise RuntimeError(f"revision mismatch for {checkout}: expected {expected}, got {actual}")


def required_tool(name: str, expected_version: str, timeout: int) -> str:
    executable = shutil.which(name)
    if executable is None:
        raise RuntimeError(f"required tool {name!r} is not on PATH")
    version = run_session([executable, "--version"], timeout=timeout)
    output = version.stdout + version.stderr
    if version.returncode != 0 or f"v{expected_version}" not in output:
        raise RuntimeError(f"{name} version mismatch: {output}")
    return executable


def load_normalizer(contract: dict[str, Any]) -> Any:
    path = ROOT / contract["normalizer_path"]
    actual = sha256(path)
    if actual != contract["normalizer_sha256"]:
        raise RuntimeError(
            f"M3D normalizer hash mismatch: expected {contract['normalizer_sha256']}, got {actual}"
        )
    spec = importlib.util.spec_from_file_location("frozen_m3d_verify", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import frozen M3D normalizer {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source_paths() -> dict[str, Path]:
    return {
        "tests/m3d/fixtures/static-adjunct.k": FIXTURE,
        "tests/m3d/claims/static-spec.k": SPEC,
        "upstream/definition/expr.k": UPSTREAM_DEFINITION / "expr.k",
        "upstream/definition/calc.k": UPSTREAM_DEFINITION / "calc.k",
        "upstream/definition/imp.k": UPSTREAM_DEFINITION / "imp.k",
        "upstream/definition/imp-verification.k": UPSTREAM_DEFINITION / "imp-verification.k",
    }


def validate_manifest(pins: dict[str, Any], manifest: dict[str, Any], timeout: int) -> tuple[Any, str, str, dict[str, int]]:
    expected_pin_fields = {
        "reference_k",
        "upstream_imp",
        "m3d_contract",
        "proof_policy",
        "source_sha256",
        "proof_outcomes",
    }
    if set(pins) != expected_pin_fields:
        raise RuntimeError(f"unknown or missing pin fields: {sorted(pins)}")
    if set(manifest) != {"proof_bounds", "cases"}:
        raise RuntimeError(f"unknown case-manifest fields: {sorted(manifest)}")
    bounds = manifest["proof_bounds"]
    if (
        not isinstance(bounds, dict)
        or set(bounds) != {"depth", "branching_allowed"}
        or any(type(bounds[name]) is not int or bounds[name] <= 0 for name in bounds)
    ):
        raise RuntimeError("proof bounds must be exactly two positive integers")
    if bounds != {"depth": 100, "branching_allowed": 64}:
        raise RuntimeError(f"static-adjunct proof bounds changed: {bounds}")
    expected_policy = {"evidence_schema": EVIDENCE_SCHEMA, **bounds}
    if pins.get("proof_policy") != expected_policy:
        raise RuntimeError(f"proof policy mismatch: expected {expected_policy}")

    cases = manifest["cases"]
    expected_names = {
        "total-equation",
        "partial-equation",
        "explicit-priority",
        "static-alias",
        "context-alias",
    }
    if not isinstance(cases, list) or len(cases) != len(expected_names):
        raise RuntimeError("case manifest must contain exactly five cases")
    names: set[str] = set()
    claims: set[str] = set()
    for case in cases:
        if not isinstance(case, dict) or set(case) != {"name", "claim"}:
            raise RuntimeError(f"invalid proof case: {case!r}")
        name = case["name"]
        claim = case["claim"]
        if name not in expected_names or claim != f"{SPEC_MODULE}.{name}":
            raise RuntimeError(f"case source/label mismatch: {case!r}")
        names.add(name)
        claims.add(claim)
    if names != expected_names or len(claims) != len(expected_names):
        raise RuntimeError("case manifest names/labels are not an exact unique partition")
    source_labels = CLAIM_PATTERN.findall(SPEC.read_text(encoding="utf-8"))
    if len(source_labels) != len(set(source_labels)) or set(source_labels) != expected_names:
        raise RuntimeError(f"static spec claim labels differ: {source_labels}")

    contract = pins["m3d_contract"]
    if set(contract) != {
        "pins_path",
        "pins_sha256",
        "normalizer_path",
        "normalizer_sha256",
    }:
        raise RuntimeError(f"unknown or missing M3D contract fields: {sorted(contract)}")
    m3d_pins_path = ROOT / contract["pins_path"]
    if sha256(m3d_pins_path) != contract["pins_sha256"]:
        raise RuntimeError("frozen M3D pin-ledger hash differs")
    m3d_pins = json.loads(m3d_pins_path.read_text(encoding="utf-8"))
    if pins["reference_k"] != m3d_pins["reference_k"]:
        raise RuntimeError("reference K identity does not reuse the M3D pin")
    if pins["upstream_imp"] != m3d_pins["upstream_imp"]:
        raise RuntimeError("upstream IMP identity does not reuse the M3D pin")
    expected_sources = {name: sha256(path) for name, path in source_paths().items()}
    if expected_sources != pins["source_sha256"]:
        raise RuntimeError(f"source hash mismatch: {expected_sources}")
    if pins["source_sha256"]["tests/m3d/fixtures/static-adjunct.k"] != m3d_pins["source_sha256"]["fixtures/static-adjunct.k"]:
        raise RuntimeError("fixture hash does not reuse the M3D pin")
    if pins["source_sha256"]["tests/m3d/claims/static-spec.k"] != m3d_pins["source_sha256"]["claims/static-spec.k"]:
        raise RuntimeError("claim-spec hash does not reuse the M3D pin")
    for filename in ("expr.k", "calc.k", "imp.k", "imp-verification.k"):
        ours = pins["source_sha256"][f"upstream/definition/{filename}"]
        if ours != m3d_pins["upstream_sha256"][f"definition/{filename}"]:
            raise RuntimeError(f"upstream {filename} hash does not reuse the M3D pin")

    exact_revision(K, pins["reference_k"]["commit"], timeout)
    exact_revision(IMP, pins["upstream_imp"]["commit"], timeout)
    normalizer = load_normalizer(contract)
    kompile = required_tool("kompile", pins["reference_k"]["version"], timeout)
    kprove = required_tool("kprove", pins["reference_k"]["version"], timeout)
    return normalizer, kompile, kprove, bounds


def unique_emitted_claim(value: dict[str, Any]) -> dict[str, Any]:
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
        raise RuntimeError(f"expected exactly one emitted KClaim, found {len(found)}")
    return found[0]


def root_label(normalized: dict[str, Any]) -> str | None:
    term = normalized.get("term")
    if not isinstance(term, dict):
        raise RuntimeError("normalized result has no object term")
    label = term.get("label")
    if label is None:
        return None
    if not isinstance(label, dict) or label.get("node") != "KLabel":
        raise RuntimeError("normalized result has a malformed root label")
    name = label.get("name")
    if not isinstance(name, str):
        raise RuntimeError("normalized result root label is not a string")
    return name


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
            canonical(
                {
                    "states": sorted(states, key=canonical),
                    "constraints": sorted(constraints, key=canonical),
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
    raise RuntimeError(f"unclassified proof termination: rc={returncode}, root={root!r}")


def prove_case(
    case: dict[str, str],
    *,
    pins: dict[str, Any],
    kprove: str,
    definition: Path,
    workspace: Path,
    normalizer: Any,
    bounds: dict[str, int],
    timeout: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    emitted_spec = workspace / f"{case['name']}-spec.json"
    command = [
        kprove,
        str(SPEC),
        "-d",
        str(definition),
        "-I",
        str(UPSTREAM_DEFINITION),
        "-I",
        str(FIXTURES),
        "--spec-module",
        SPEC_MODULE,
        "--claims",
        case["claim"],
        "--output",
        "json",
        "--emit-json-spec",
        str(emitted_spec),
        "--depth",
        str(bounds["depth"]),
        "--branching-allowed",
        str(bounds["branching_allowed"]),
    ]
    process = run_session(command, timeout=timeout)
    try:
        result_value = normalizer.envelope(process.stdout)
        claim_value = json.loads(emitted_spec.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError, ValueError) as error:
        raise RuntimeError(f"{case['name']}: incomplete JSON proof evidence: {error}") from error
    emitted_claim = unique_emitted_claim(claim_value)
    actual_label = emitted_claim.get("att", {}).get("att", {}).get("label")
    if actual_label != case["claim"]:
        raise RuntimeError(
            f"{case['name']}: selected claim mismatch: expected {case['claim']}, got {actual_label}"
        )
    normalized_result = normalizer.normalize_proof(result_value)
    normalized_claim = normalizer.normalize_claim_spec(claim_value)
    root = root_label(normalized_result)
    status = classify(process.returncode, root, process.stderr)
    frontier = normalized_frontier(normalized_result)
    outcome = {
        "status": status,
        "bounds": dict(bounds),
        "frontier_count": len(frontier),
        "frontier_sha256": hashlib.sha256("\n".join(frontier).encode()).hexdigest(),
        # KAST JSON output exposes the residual/proved term, not an applied-rule trace.
        # stderr is a diagnostic stream. No user label is inferred from either channel.
        "user_labels": [],
        "result_sha256": digest(normalized_result),
        "claim_sha256": digest(normalized_claim),
    }
    evidence = {
        "evidence_schema": EVIDENCE_SCHEMA,
        "identity": {
            "reference_k": pins["reference_k"],
            "upstream_imp": pins["upstream_imp"],
            "m3d_contract": pins["m3d_contract"],
            "proof_policy": pins["proof_policy"],
            "source_sha256": pins["source_sha256"],
        },
        "case": case,
        "invocation": {
            "backend": "haskell",
            "output": "json",
            "spec_module": SPEC_MODULE,
            "selected_claim": case["claim"],
            "bounds": dict(bounds),
        },
        "observable_channels": {
            "stdout": "KAST-v4 residual/proved term",
            "emitted_spec": "KAST-v4 module containing exactly one selected KClaim",
            "stderr": "diagnostics only; no applied-rule trace was requested or exposed",
        },
        "termination": {"returncode": process.returncode, "root_label": root},
        "normalized_result": normalized_result,
        "normalized_claim": normalized_claim,
        "outcome": outcome,
    }
    return outcome, evidence


def prepare_artifacts(path: Path | None) -> Path | None:
    if path is None:
        return None
    path = path.resolve()
    if path.exists() and any(path.iterdir()):
        raise RuntimeError(f"artifact directory must be absent or empty: {path}")
    path.mkdir(parents=True, exist_ok=True)
    return path


def main() -> int:
    options = arguments()
    if options.timeout <= 0:
        raise RuntimeError("--timeout must be positive")
    if options.write_proposal is not None and options.write_proposal.resolve() == PINS.resolve():
        raise RuntimeError("refusing to overwrite the reviewed pin ledger directly")
    artifacts = prepare_artifacts(options.artifacts)
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    manifest = json.loads(CASES.read_text(encoding="utf-8"))
    normalizer, kompile, kprove, bounds = validate_manifest(pins, manifest, options.timeout)
    print("PASS preflight: exact M3D K/IMP/source/normalizer contract")
    print(f"PASS bounds: depth={bounds['depth']}, branching_allowed={bounds['branching_allowed']}")

    outcomes: dict[str, dict[str, Any]] = {}
    with tempfile.TemporaryDirectory(prefix="krs-m4-adjunct-pins-", dir="/tmp") as temporary:
        workspace = Path(temporary)
        definition = workspace / "static-kompiled"
        compiled = run_session(
            [
                kompile,
                str(FIXTURE),
                "-I",
                str(UPSTREAM_DEFINITION),
                "--backend",
                "haskell",
                "--main-module",
                MAIN_MODULE,
                "--syntax-module",
                SYNTAX_MODULE,
                "--emit-json",
                "--output-definition",
                str(definition),
            ],
            timeout=options.timeout,
        )
        if compiled.returncode != 0:
            raise RuntimeError(f"reference static-adjunct kompile failed:\n{compiled.stderr}")
        print("PASS compile: fresh reference Haskell static-adjunct definition")
        for case in manifest["cases"]:
            outcome, evidence = prove_case(
                case,
                pins=pins,
                kprove=kprove,
                definition=definition,
                workspace=workspace,
                normalizer=normalizer,
                bounds=bounds,
                timeout=options.timeout,
            )
            outcomes[case["name"]] = outcome
            if artifacts is not None:
                atomic_json(artifacts / f"{case['name']}.evidence.json", evidence)
            print(
                f"PASS {case['name']}: {outcome['status']}, "
                f"frontier={outcome['frontier_count']}, labels={outcome['user_labels']}"
            )

    if set(outcomes) != {case["name"] for case in manifest["cases"]}:
        raise RuntimeError("proof outcome ledger is incomplete")
    observed = {**pins, "proof_outcomes": outcomes}
    if options.write_proposal is not None:
        destination = options.write_proposal.resolve()
        if destination.exists():
            raise RuntimeError(f"proposal destination already exists: {destination}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        atomic_json(destination, observed)
        print(f"PASS proposal: wrote {destination}")
    elif pins != observed:
        raise RuntimeError(
            "reviewed proof pins differ; regenerate a proposal with --write-proposal\n"
            f"observed={canonical(outcomes)}"
        )
    else:
        print("PASS pins: all five individually selected outcomes match")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, KeyError, TypeError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
