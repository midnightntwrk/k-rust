#!/usr/bin/env python3
"""Freeze bounded M4 evidence for the six M3D-selected IMP invocations."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from typing import Any


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
IMP = ROOT.parent / "inspirations/runtimeverification/imp-semantics"
K = ROOT.parent / "inspirations/runtimeverification/k"
DEFINITION = IMP / "src/kimp/kdist/imp-semantics"
SPECS = IMP / "examples/specs"
CASES = HERE / "cases.json"
PINS = HERE / "pins.json"
TERMINATION_GRACE_SECONDS = 5
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
CONSTRAINT_LABELS = frozenset({"#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"})


class VerificationError(RuntimeError):
    """The inputs, execution evidence, or checked-in pins are not exact."""


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-proposal",
        type=Path,
        help="write observed pins here instead of comparing proof_outcomes",
    )
    parser.add_argument(
        "--artifacts",
        type=Path,
        help="retain normalized claim/result JSON in this absent or empty directory",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="per-command watchdog seconds; timeout is always an error",
    )
    return parser.parse_args()


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def terminate_session(process: subprocess.Popen[str]) -> tuple[str, str]:
    """Terminate and reap the complete process session owned by this verifier."""

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


def run(
    command: list[str],
    *,
    timeout: int,
    cwd: Path = ROOT,
) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C", "PYTHONDONTWRITEBYTECODE": "1"})
    process = subprocess.Popen(
        command,
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
        raise VerificationError(
            f"watchdog expired after {timeout}s; no proof status was produced; "
            f"the process session was terminated and reaped: {' '.join(command)}\n{stderr}"
        ) from error
    except BaseException:
        terminate_session(process)
        raise
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def exact_revision(checkout: Path, expected: str, timeout: int) -> None:
    process = run(["git", "rev-parse", "HEAD"], cwd=checkout, timeout=timeout)
    actual = process.stdout.strip()
    if process.returncode != 0 or actual != expected:
        raise VerificationError(f"revision mismatch for {checkout}: expected {expected}, got {actual}")


def required_tool(name: str, timeout: int) -> str:
    executable = shutil.which(name)
    if executable is None:
        raise VerificationError(f"required tool {name!r} is not on PATH")
    process = run([executable, "--version"], timeout=timeout)
    if process.returncode != 0:
        raise VerificationError(f"{name} --version failed: {process.stderr}")
    return executable


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise VerificationError(f"expected a JSON object in {path}")
    return value


def load_normalizer(pins: dict[str, Any]) -> Any:
    descriptor = pins.get("m3d")
    if not isinstance(descriptor, dict) or set(descriptor) != {
        "normalizer_path", "normalizer_sha256", "pins_path", "pins_sha256"
    }:
        raise VerificationError("M3D descriptor has unknown or missing fields")
    path = ROOT / descriptor["normalizer_path"]
    actual = file_sha256(path)
    if actual != descriptor["normalizer_sha256"]:
        raise VerificationError(
            f"M3D normalizer hash mismatch: expected {descriptor['normalizer_sha256']}, got {actual}"
        )
    spec = importlib.util.spec_from_file_location("frozen_m3d_verify", path)
    if spec is None or spec.loader is None:
        raise VerificationError(f"cannot load frozen M3D normalizer {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source_paths() -> dict[str, Path]:
    return {
        "definition/imp-verification.k": DEFINITION / "imp-verification.k",
        "specs/imp-simple-spec.k": SPECS / "imp-simple-spec.k",
        "specs/imp-sum-spec.k": SPECS / "imp-sum-spec.k",
    }


def load_cases() -> list[dict[str, Any]]:
    manifest = load_json(CASES)
    if set(manifest) != {"cases"} or not isinstance(manifest["cases"], list):
        raise VerificationError("cases.json must contain exactly one cases array")
    expected_fields = {"name", "spec", "module", "claim", "bounds"}
    cases = manifest["cases"]
    expected_names = {
        "addition-1", "addition-var", "branching", "sum-loop", "sum-spec",
        "addition-depth-zero",
    }
    if len(cases) != 6 or {case.get("name") for case in cases} != expected_names:
        raise VerificationError("cases.json must contain exactly the six M3D-selected invocations")
    for case in cases:
        if not isinstance(case, dict) or set(case) != expected_fields:
            raise VerificationError(f"invalid case shape: {case}")
        expected_spec = {
            "IMP-SIMPLE-SPEC": "imp-simple-spec.k",
            "IMP-SUM-SPEC": "imp-sum-spec.k",
        }.get(case["module"])
        if expected_spec != case["spec"] or not case["claim"].startswith(f"{case['module']}."):
            raise VerificationError(f"inconsistent source/module/claim selection: {case}")
        bounds = case["bounds"]
        if not isinstance(bounds, dict) or set(bounds) != {"depth", "branching_allowed"}:
            raise VerificationError(f"invalid proof bounds: {bounds}")
        if type(bounds["depth"]) is not int or bounds["depth"] < 0:
            raise VerificationError("proof depth must be a non-negative integer")
        if type(bounds["branching_allowed"]) is not int or bounds["branching_allowed"] <= 0:
            raise VerificationError("branching_allowed must be a positive integer")
        expected_depth = 0 if case["name"] == "addition-depth-zero" else 100
        if bounds != {"depth": expected_depth, "branching_allowed": 64}:
            raise VerificationError(f"unexpected reviewed bounds for {case['name']}: {bounds}")
    depth_zero = next(case for case in cases if case["name"] == "addition-depth-zero")
    addition = next(case for case in cases if case["name"] == "addition-1")
    if depth_zero["claim"] != addition["claim"]:
        raise VerificationError("addition-depth-zero must invoke the exact addition-1 claim")
    return cases


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
        raise VerificationError(f"expected exactly one emitted KClaim, found {len(found)}")
    return found[0]


def root_label(normalized: dict[str, Any]) -> str | None:
    term = normalized.get("term")
    if not isinstance(term, dict):
        raise VerificationError("normalized proof has no object term")
    label = term.get("label")
    if label is None:
        return None
    if not isinstance(label, dict):
        raise VerificationError("normalized proof root label is malformed")
    name = label.get("name")
    if not isinstance(name, str):
        raise VerificationError("normalized proof root label has no name")
    return name


def flatten_term(root: Any, label: str) -> list[Any]:
    if (
        isinstance(root, dict)
        and root.get("node") == "KApply"
        and root.get("label", {}).get("name") == label
    ):
        flattened: list[Any] = []
        for child in root["args"]:
            flattened.extend(flatten_term(child, label))
        return flattened
    return [root]


def normalized_frontier(normalized: dict[str, Any]) -> tuple[str, ...]:
    term = normalized.get("term")
    if not isinstance(term, dict):
        raise VerificationError("normalized proof has no object term")
    if root_label(normalized) in {"#Top", "#Bottom"}:
        return ()
    frontier: list[str] = []
    for branch in flatten_term(term, "#Or"):
        constraints: list[Any] = []
        states: list[Any] = []
        for conjunct in flatten_term(branch, "#And"):
            name = conjunct.get("label", {}).get("name") if isinstance(conjunct, dict) else None
            (constraints if name in CONSTRAINT_LABELS else states).append(conjunct)
        frontier.append(canonical({
            "states": sorted(states, key=canonical),
            "constraints": sorted(constraints, key=canonical),
        }))
    return tuple(sorted(frontier))


def classify(returncode: int, root: str | None, stderr: str) -> str:
    if returncode == 0 and root == "#Top":
        return "proved"
    stalled = re.search(r"configuration cannot be\s+rewritten further", stderr) is not None
    if returncode == 1 and root == "#Bottom":
        return "failed"
    if returncode == 1 and root not in {"#Top", "#Bottom"} and stalled:
        return "incomplete"
    raise VerificationError(
        f"unclassified bounded proof termination: rc={returncode}, root={root!r}"
    )


def proof_pin(
    normalized_result: dict[str, Any],
    normalized_claim: dict[str, Any],
    bounds: dict[str, int],
    returncode: int,
    stderr: str,
) -> dict[str, Any]:
    frontier = normalized_frontier(normalized_result)
    return {
        "status": classify(returncode, root_label(normalized_result), stderr),
        "bounds": dict(bounds),
        "frontier_count": len(frontier),
        "frontier_sha256": hashlib.sha256("\n".join(frontier).encode()).hexdigest(),
        "user_labels": [],
        "result_sha256": digest(normalized_result),
        "claim_sha256": digest(normalized_claim),
    }


def verify_legacy(
    name: str,
    observed: dict[str, Any],
    m3d_outcomes: dict[str, Any],
) -> None:
    legacy = m3d_outcomes.get(name)
    if not isinstance(legacy, dict) or set(legacy) != {
        "status", "result_sha256", "claim_sha256"
    }:
        raise VerificationError(f"missing or malformed legacy M3D outcome for {name}")
    expected_status = "incomplete" if legacy["status"] == "frontier" else legacy["status"]
    if observed["status"] != expected_status:
        raise VerificationError(
            f"{name}: bounded status {observed['status']} differs from legacy {legacy['status']}"
        )
    for field in ("result_sha256", "claim_sha256"):
        if observed[field] != legacy[field]:
            raise VerificationError(
                f"{name}: {field} {observed[field]} differs from legacy {legacy[field]}"
            )


def prepare_artifacts(path: Path | None) -> Path | None:
    if path is None:
        return None
    resolved = path.resolve()
    if resolved.exists() and any(resolved.iterdir()):
        raise VerificationError(f"artifact directory must be absent or empty: {resolved}")
    resolved.mkdir(parents=True, exist_ok=True)
    return resolved


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    options = arguments()
    if options.timeout <= 0:
        raise VerificationError("--timeout must be positive")
    artifacts = prepare_artifacts(options.artifacts)
    pins = load_json(PINS)
    cases = load_cases()
    expected_pin_fields = {"reference_k", "upstream_imp", "m3d", "source_sha256", "proof_outcomes"}
    if set(pins) != expected_pin_fields:
        raise VerificationError("pins.json has unknown or missing top-level fields")
    actual_sources = {name: file_sha256(path) for name, path in source_paths().items()}
    if actual_sources != pins["source_sha256"]:
        raise VerificationError(f"upstream source hashes differ: {actual_sources}")
    exact_revision(K, pins["reference_k"]["commit"], options.timeout)
    exact_revision(IMP, pins["upstream_imp"]["commit"], options.timeout)
    kompile = required_tool("kompile", options.timeout)
    kprove = required_tool("kprove", options.timeout)
    version = run([kompile, "--version"], timeout=options.timeout)
    if f"v{pins['reference_k']['version']}" not in version.stdout + version.stderr:
        raise VerificationError("reference K version differs from pins.json")
    normalizer = load_normalizer(pins)
    m3d_pins_path = ROOT / pins["m3d"]["pins_path"]
    actual_m3d_pins_hash = file_sha256(m3d_pins_path)
    if actual_m3d_pins_hash != pins["m3d"]["pins_sha256"]:
        raise VerificationError(
            "legacy M3D pins hash mismatch: "
            f"expected {pins['m3d']['pins_sha256']}, got {actual_m3d_pins_hash}"
        )
    m3d_outcomes = load_json(m3d_pins_path).get("proof_outcomes")
    if not isinstance(m3d_outcomes, dict):
        raise VerificationError("legacy M3D proof outcomes are absent")

    with tempfile.TemporaryDirectory(prefix="krs-m4-selected-proof-pins-", dir="/tmp") as temporary:
        workspace = Path(temporary)
        definition = workspace / "imp-kompiled"
        compile_process = run(
            [
                kompile,
                str(DEFINITION / "imp-verification.k"),
                "--backend", "haskell",
                "--main-module", "IMP-VERIFICATION",
                "--syntax-module", "IMP-SYNTAX",
                "--emit-json",
                "--output-definition", str(definition),
            ],
            timeout=options.timeout,
        )
        if compile_process.returncode != 0:
            raise VerificationError(f"reference kompile failed:\n{compile_process.stderr}")
        print("PASS compile: exact upstream IMP-VERIFICATION")

        observed: dict[str, dict[str, Any]] = {}
        for case in cases:
            spec_json = workspace / f"{case['name']}-spec.json"
            process = run(
                [
                    kprove,
                    str(SPECS / case["spec"]),
                    "-d", str(definition),
                    "-I", str(DEFINITION),
                    "--spec-module", case["module"],
                    "--claims", case["claim"],
                    "--output", "json",
                    "--emit-json-spec", str(spec_json),
                    "--depth", str(case["bounds"]["depth"]),
                    "--branching-allowed", str(case["bounds"]["branching_allowed"]),
                ],
                timeout=options.timeout,
            )
            result_value = normalizer.envelope(process.stdout)
            claim_value = load_json(spec_json)
            selected = unique_emitted_claim(claim_value)
            actual_label = selected.get("att", {}).get("att", {}).get("label")
            if actual_label != case["claim"]:
                raise VerificationError(
                    f"{case['name']}: selected {actual_label!r}, expected exactly {case['claim']!r}"
                )
            normalized_result = normalizer.normalize_proof(result_value)
            normalized_claim = normalizer.normalize_claim_spec(claim_value)
            item = proof_pin(
                normalized_result,
                normalized_claim,
                case["bounds"],
                process.returncode,
                process.stderr,
            )
            verify_legacy(case["name"], item, m3d_outcomes)
            if case["name"] == "addition-depth-zero":
                if item["frontier_count"] == 0 or item["frontier_sha256"] == EMPTY_SHA256:
                    raise VerificationError("addition-depth-zero lost its exact residual frontier")
            elif item["frontier_count"] != 0 or item["frontier_sha256"] != EMPTY_SHA256:
                raise VerificationError(f"proved case {case['name']} unexpectedly retained a frontier")
            observed[case["name"]] = item
            if artifacts is not None:
                write_json(artifacts / f"{case['name']}.result.normalized.json", normalized_result)
                write_json(artifacts / f"{case['name']}.claim.normalized.json", normalized_claim)
            print(
                f"PASS {case['name']}: {item['status']}, "
                f"frontier={item['frontier_count']}, result={item['result_sha256']}"
            )

    proposal = {**{key: pins[key] for key in expected_pin_fields - {"proof_outcomes"}}, "proof_outcomes": observed}
    # Preserve a readable, intentional top-level ordering.
    proposal = {
        "reference_k": proposal["reference_k"],
        "upstream_imp": proposal["upstream_imp"],
        "m3d": proposal["m3d"],
        "source_sha256": proposal["source_sha256"],
        "proof_outcomes": proposal["proof_outcomes"],
    }
    if options.write_proposal is not None:
        destination = options.write_proposal.resolve()
        if destination == PINS.resolve():
            raise VerificationError("proposal output must not overwrite checked-in pins.json")
        write_json(destination, proposal)
        print(f"PASS proposal: {destination}")
    elif pins["proof_outcomes"] != observed:
        raise VerificationError(
            "checked-in proof pins differ; regenerate with --write-proposal and review the diff"
        )
    else:
        print("PASS pins: all six bounded outcomes equal pins.json")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, json.JSONDecodeError, VerificationError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
