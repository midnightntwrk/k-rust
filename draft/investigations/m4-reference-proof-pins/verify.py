#!/usr/bin/env python3
"""Freeze the ten M4-only upstream IMP reference proof outcomes."""

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
import time
from typing import Any


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
IMP = ROOT.parent / "inspirations/runtimeverification/imp-semantics"
K = ROOT.parent / "inspirations/runtimeverification/k"
DEFINITION = IMP / "src/kimp/kdist/imp-semantics"
SPECS = IMP / "examples/specs"
PINS = HERE / "pins.json"
CASES = HERE / "cases.json"
LONG_SECONDS = 60.0
CLAIM_PATTERN = re.compile(r"\bclaim\s*\[([^\]]+)\]\s*:")
EVIDENCE_SCHEMA = 2
TERMINATION_GRACE_SECONDS = 3.0
CONSTRAINT_LABELS = frozenset({"#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"})


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-proposal",
        type=Path,
        help="write observed pins to this path instead of requiring pins.json equality",
    )
    parser.add_argument(
        "--artifacts",
        type=Path,
        help="retain normalized proof and claim JSON beneath this new/empty directory",
    )
    parser.add_argument(
        "--reuse-artifacts",
        action="store_true",
        help="reuse exact-identity evidence in --artifacts and run only missing cases",
    )
    parser.add_argument(
        "--case",
        action="append",
        metavar="NAME",
        help="run only this case and retain a partial evidence ledger; may be repeated",
    )
    parser.add_argument(
        "--timeout", type=int, default=900, help="seconds allowed per tool invocation"
    )
    return parser.parse_args()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def terminate_session(process: subprocess.Popen[str]) -> tuple[str, str]:
    """Terminate the process session and reap the session leader started by run()."""

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
    cwd: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C", "PYTHONDONTWRITEBYTECODE": "1"})
    process = subprocess.Popen(
        command,
        cwd=cwd or ROOT,
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
        raise subprocess.TimeoutExpired(
            command,
            timeout,
            output=stdout,
            stderr=stderr,
        ) from error
    except BaseException:
        terminate_session(process)
        raise
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def required_tool(name: str, timeout: int) -> str:
    executable = shutil.which(name)
    if executable is None:
        raise RuntimeError(f"required tool {name!r} is not on PATH")
    version = run([executable, "--version"], timeout=timeout)
    if version.returncode != 0:
        raise RuntimeError(f"{name} --version failed: {version.stderr}")
    return executable


def exact_revision(checkout: Path, expected: str, timeout: int) -> None:
    process = run(["git", "rev-parse", "HEAD"], cwd=checkout, timeout=timeout)
    actual = process.stdout.strip()
    if process.returncode != 0 or actual != expected:
        raise RuntimeError(f"revision mismatch for {checkout}: expected {expected}, got {actual}")


def load_normalizer(pins: dict[str, Any]) -> Any:
    relative = pins["normalizer"]["path"]
    path = ROOT / relative
    actual = sha256(path)
    expected = pins["normalizer"]["sha256"]
    if actual != expected:
        raise RuntimeError(f"normalizer hash mismatch: expected {expected}, got {actual}")
    spec = importlib.util.spec_from_file_location("frozen_m3d_verify", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import frozen normalizer {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source_paths() -> dict[str, Path]:
    return {
        "definition/imp-verification.k": DEFINITION / "imp-verification.k",
        "specs/imp-simple-spec.k": SPECS / "imp-simple-spec.k",
        "specs/imp-sum-spec.k": SPECS / "imp-sum-spec.k",
    }


def proof_bounds(cases: dict[str, Any]) -> dict[str, int]:
    if set(cases) != {"proof_bounds", "already_frozen", "cases"}:
        raise RuntimeError(f"unknown case-manifest fields: {sorted(cases)}")
    bounds = cases["proof_bounds"]
    if not isinstance(bounds, dict) or set(bounds) != {"depth", "branching_allowed"}:
        raise RuntimeError("proof_bounds must contain exactly depth and branching_allowed")
    if any(type(bounds[name]) is not int or bounds[name] <= 0 for name in bounds):
        raise RuntimeError("proof bounds must be positive integers")
    return bounds


def preflight(
    pins: dict[str, Any], cases: dict[str, Any], timeout: int
) -> tuple[str, str, Any, dict[str, int]]:
    bounds = proof_bounds(cases)
    expected_policy = {"evidence_schema": EVIDENCE_SCHEMA, **bounds}
    if pins.get("proof_policy") != expected_policy:
        raise RuntimeError(
            f"proof policy mismatch: expected {expected_policy}, got {pins.get('proof_policy')}"
        )
    actual_sources = {name: sha256(path) for name, path in source_paths().items()}
    if actual_sources != pins["source_sha256"]:
        raise RuntimeError(f"source hash mismatch: {actual_sources}")
    exact_revision(K, pins["reference_k"]["commit"], timeout)
    exact_revision(IMP, pins["upstream_imp"]["commit"], timeout)
    kompile = required_tool("kompile", timeout)
    kprove = required_tool("kprove", timeout)
    version = run([kompile, "--version"], timeout=timeout)
    expected_version = f"v{pins['reference_k']['version']}"
    if expected_version not in version.stdout + version.stderr:
        raise RuntimeError(
            f"K version mismatch: expected {expected_version}, "
            f"got {version.stdout}{version.stderr}"
        )

    enumerated: set[str] = set()
    spec_modules = (
        ("IMP-SIMPLE-SPEC", "imp-simple-spec.k"),
        ("IMP-SUM-SPEC", "imp-sum-spec.k"),
    )
    for module, filename in spec_modules:
        labels = CLAIM_PATTERN.findall((SPECS / filename).read_text(encoding="utf-8"))
        qualified = {f"{module}.{label}" for label in labels}
        if len(qualified) != len(labels):
            raise RuntimeError(f"duplicate claim label in {filename}")
        enumerated.update(qualified)
    frozen = set(cases["already_frozen"])
    expected_case_fields = {"name", "spec", "module", "claim"}
    for case in cases["cases"]:
        if not isinstance(case, dict) or set(case) != expected_case_fields:
            raise RuntimeError(f"invalid proof case shape: {case}")
        if re.fullmatch(r"[A-Za-z0-9-]+", case["name"]) is None:
            raise RuntimeError(f"invalid proof artifact name: {case['name']!r}")
        expected_spec = {
            "IMP-SIMPLE-SPEC": "imp-simple-spec.k",
            "IMP-SUM-SPEC": "imp-sum-spec.k",
        }.get(case["module"])
        if expected_spec != case["spec"] or not case["claim"].startswith(
            f"{case['module']}."
        ):
            raise RuntimeError(f"proof case has inconsistent source/module/label: {case}")
    pending = {case["claim"] for case in cases["cases"]}
    names = {case["name"] for case in cases["cases"]}
    if len(cases["cases"]) != 10 or len(pending) != 10:
        raise RuntimeError("case manifest must contain exactly ten unique pending claims")
    if len(names) != 10:
        raise RuntimeError("case manifest must contain exactly ten unique artifact names")
    if frozen & pending or enumerated != frozen | pending:
        raise RuntimeError(
            f"claim partition mismatch: enumerated={sorted(enumerated)}, "
            f"frozen={sorted(frozen)}, pending={sorted(pending)}"
        )
    print(f"PASS labels: 15 upstream = 5 frozen + 10 pending ({', '.join(sorted(pending))})")
    print(
        "PASS bounds: "
        f"depth={bounds['depth']}, branching_allowed={bounds['branching_allowed']}"
    )
    return kompile, kprove, load_normalizer(pins), bounds


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
        raise ValueError(f"expected exactly one emitted KClaim, found {len(found)}")
    return found[0]


def root_label(normalized: dict[str, Any]) -> str | None:
    term = normalized.get("term")
    if not isinstance(term, dict):
        raise ValueError("normalized proof has no object term")
    label = term.get("label")
    if label is None:
        return None
    if not isinstance(label, dict) or set(label) - {"node", "name", "params"}:
        raise ValueError("normalized proof has an unclassified root label")
    name = label.get("name")
    if not isinstance(name, str):
        raise ValueError("normalized proof root label has no name")
    return name


def flatten_term(root: Any, label: str) -> list[Any]:
    if (
        isinstance(root, dict)
        and root.get("node") == "KApply"
        and root.get("label", {}).get("name") == label
    ):
        result: list[Any] = []
        for child in root["args"]:
            result.extend(flatten_term(child, label))
        return result
    return [root]


def normalized_frontier(normalized: dict[str, Any]) -> tuple[str, ...]:
    term = normalized.get("term")
    if not isinstance(term, dict):
        raise ValueError("normalized proof has no object term")
    if root_label(normalized) in {"#Top", "#Bottom"}:
        return ()
    branches = flatten_term(term, "#Or")
    frontier: list[str] = []
    for branch in branches:
        constraints: list[Any] = []
        states: list[Any] = []
        for conjunct in flatten_term(branch, "#And"):
            name = (
                conjunct.get("label", {}).get("name")
                if isinstance(conjunct, dict)
                else None
            )
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
    stalled = re.search(r"configuration cannot be\s+rewritten further", stderr) is not None
    if returncode == 1 and root == "#Bottom":
        return "failed"
    if returncode == 1 and root not in {"#Top", "#Bottom"} and stalled:
        return "incomplete"
    raise ValueError(f"unclassified proof termination: rc={returncode}, root={root!r}")


def outcome_from_evidence(
    normalized_proof: dict[str, Any],
    normalized_claim: dict[str, Any],
    termination: dict[str, Any],
    bounds: dict[str, int],
) -> dict[str, Any]:
    if set(termination) != {"returncode", "root_label", "stalled"}:
        raise ValueError("evidence termination has unknown fields")
    returncode = termination["returncode"]
    root = termination["root_label"]
    stalled = termination["stalled"]
    if type(returncode) is not int or (root is not None and not isinstance(root, str)):
        raise ValueError("evidence termination has invalid types")
    if type(stalled) is not bool:
        raise ValueError("evidence stalled marker is not boolean")
    observed_stalled = "configuration cannot be rewritten further" if stalled else ""
    status = classify(returncode, root, observed_stalled)
    actual_root = root_label(normalized_proof)
    if actual_root != root:
        raise ValueError(f"evidence root mismatch: termination={root!r}, result={actual_root!r}")
    frontier = normalized_frontier(normalized_proof)
    return {
        "status": status,
        "bounds": dict(bounds),
        "frontier_count": len(frontier),
        "frontier_sha256": hashlib.sha256("\n".join(frontier).encode()).hexdigest(),
        "user_labels": [],
        "result_sha256": digest(normalized_proof),
        "claim_sha256": digest(normalized_claim),
    }


def evidence_identity(
    pins: dict[str, Any], case: dict[str, str], bounds: dict[str, int]
) -> dict[str, Any]:
    return {
        "schema": EVIDENCE_SCHEMA,
        "reference_k": pins["reference_k"],
        "upstream_imp": pins["upstream_imp"],
        "normalizer": pins["normalizer"],
        "proof_policy": pins["proof_policy"],
        "source_sha256": pins["source_sha256"],
        "case": case,
        "bounds": bounds,
        "invocation": {
            "backend": "haskell",
            "output": "json",
            "definition_module": "IMP-VERIFICATION",
            "syntax_module": "IMP-SYNTAX",
        },
    }


def atomic_json(path: Path, value: Any) -> None:
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def load_evidence(
    case: dict[str, str],
    *,
    artifacts: Path | None,
    identity: dict[str, Any],
    normalizer: Any,
    bounds: dict[str, int],
) -> dict[str, Any] | None:
    if artifacts is None:
        return None
    path = artifacts / f"{case['name']}.evidence.json"
    if not path.is_file():
        return None
    value = json.loads(path.read_text(encoding="utf-8"))
    expected_fields = {
        "evidence_schema",
        "identity_sha256",
        "identity",
        "termination",
        "normalized_result",
        "normalized_claim",
        "outcome",
    }
    if not isinstance(value, dict) or set(value) != expected_fields:
        raise ValueError(f"{case['name']}: cached evidence has unknown fields")
    if value["evidence_schema"] != EVIDENCE_SCHEMA:
        raise ValueError(f"{case['name']}: cached evidence schema changed")
    if value["identity"] != identity or value["identity_sha256"] != digest(identity):
        raise ValueError(f"{case['name']}: cached evidence identity mismatch")
    normalized_proof = value["normalized_result"]
    normalized_claim = value["normalized_claim"]
    if normalizer.normalize_proof(normalized_proof) != normalized_proof:
        raise ValueError(f"{case['name']}: cached proof is not canonically normalized")
    if normalizer.normalize_claim_spec(normalized_claim) != normalized_claim:
        raise ValueError(f"{case['name']}: cached claim is not canonically normalized")
    selected = unique_emitted_claim(normalized_claim)
    actual_label = selected.get("att", {}).get("att", {}).get("label")
    if actual_label != case["claim"]:
        raise ValueError(
            f"{case['name']}: cached selected claim mismatch: "
            f"expected {case['claim']}, got {actual_label}"
        )
    outcome = outcome_from_evidence(
        normalized_proof, normalized_claim, value["termination"], bounds
    )
    if value["outcome"] != outcome:
        raise ValueError(f"{case['name']}: cached outcome does not match its evidence")
    for suffix, expected in (
        ("result.normalized.json", normalized_proof),
        ("claim.normalized.json", normalized_claim),
    ):
        sidecar = artifacts / f"{case['name']}.{suffix}"
        if sidecar.is_file() and json.loads(sidecar.read_text(encoding="utf-8")) != expected:
            raise ValueError(f"{case['name']}: cached normalized sidecar disagrees with evidence")
    return outcome


def prove_case(
    case: dict[str, str],
    *,
    kprove: str,
    definition: Path,
    workspace: Path,
    normalizer: Any,
    timeout: int,
    artifacts: Path | None,
    bounds: dict[str, int],
    identity: dict[str, Any],
) -> tuple[dict[str, Any], float]:
    spec_json = workspace / f"{case['name']}-spec.json"
    command = [
        kprove,
        str(SPECS / case["spec"]),
        "-d",
        str(definition),
        "-I",
        str(DEFINITION),
        "--spec-module",
        case["module"],
        "--claims",
        case["claim"],
        "--output",
        "json",
        "--emit-json-spec",
        str(spec_json),
        "--depth",
        str(bounds["depth"]),
        "--branching-allowed",
        str(bounds["branching_allowed"]),
    ]
    started = time.monotonic()
    process = run(command, timeout=timeout)
    elapsed = time.monotonic() - started
    proof_value = normalizer.envelope(process.stdout)
    claim_value = json.loads(spec_json.read_text(encoding="utf-8"))
    selected = unique_emitted_claim(claim_value)
    actual_label = selected.get("att", {}).get("att", {}).get("label")
    if actual_label != case["claim"]:
        raise ValueError(f"selected claim mismatch: expected {case['claim']}, got {actual_label}")
    normalized_proof = normalizer.normalize_proof(proof_value)
    normalized_claim = normalizer.normalize_claim_spec(claim_value)
    termination = {
        "returncode": process.returncode,
        "root_label": root_label(normalized_proof),
        "stalled": re.search(
            r"configuration cannot be\s+rewritten further", process.stderr
        )
        is not None,
    }
    outcome = outcome_from_evidence(
        normalized_proof, normalized_claim, termination, bounds
    )
    if artifacts is not None:
        atomic_json(
            artifacts / f"{case['name']}.result.normalized.json", normalized_proof
        )
        atomic_json(
            artifacts / f"{case['name']}.claim.normalized.json", normalized_claim
        )
        evidence = {
            "evidence_schema": EVIDENCE_SCHEMA,
            "identity_sha256": digest(identity),
            "identity": identity,
            "termination": termination,
            "normalized_result": normalized_proof,
            "normalized_claim": normalized_claim,
            "outcome": outcome,
        }
        atomic_json(artifacts / f"{case['name']}.evidence.json", evidence)
    return outcome, elapsed


def prepare_artifacts(path: Path | None, reuse: bool) -> Path | None:
    if path is None:
        if reuse:
            raise RuntimeError("--reuse-artifacts requires --artifacts")
        return None
    path = path.resolve()
    if path.exists() and any(path.iterdir()) and not reuse:
        raise RuntimeError(f"artifact directory must be absent or empty: {path}")
    path.mkdir(parents=True, exist_ok=True)
    return path


def main() -> int:
    options = arguments()
    if options.timeout <= 0:
        raise RuntimeError("--timeout must be a positive integer")
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    cases = json.loads(CASES.read_text(encoding="utf-8"))
    if options.case and options.artifacts is None:
        raise RuntimeError("--case requires --artifacts so partial evidence is retained")
    artifacts = prepare_artifacts(options.artifacts, options.reuse_artifacts)
    kompile, kprove, normalizer, bounds = preflight(pins, cases, options.timeout)
    case_names = {case["name"] for case in cases["cases"]}
    selected_names = set(options.case) if options.case else case_names
    unknown_names = selected_names - case_names
    if unknown_names:
        raise RuntimeError(f"unknown --case names: {sorted(unknown_names)}")
    outcomes: dict[str, dict[str, Any]] = {}
    identities: dict[str, dict[str, Any]] = {}
    pending: list[dict[str, str]] = []
    for case in cases["cases"]:
        identity = evidence_identity(pins, case, bounds)
        identities[case["name"]] = identity
        cached = (
            load_evidence(
                case,
                artifacts=artifacts,
                identity=identity,
                normalizer=normalizer,
                bounds=bounds,
            )
            if options.reuse_artifacts
            else None
        )
        if cached is None:
            if case["name"] in selected_names:
                pending.append(case)
        else:
            outcomes[case["name"]] = cached
            print(f"PASS reuse {case['name']}: {cached['status']}")

    temp_parent = Path(tempfile.gettempdir())
    print(f"PASS workspace: temporary proof definition under {temp_parent}")
    with tempfile.TemporaryDirectory(prefix="krs-m4-reference-pins-", dir=temp_parent) as temporary:
        workspace = Path(temporary)
        definition = workspace / "imp-kompiled"
        if pending:
            compile_process = run(
                [
                    kompile,
                    str(DEFINITION / "imp-verification.k"),
                    "--backend",
                    "haskell",
                    "--main-module",
                    "IMP-VERIFICATION",
                    "--syntax-module",
                    "IMP-SYNTAX",
                    "--emit-json",
                    "--output-definition",
                    str(definition),
                ],
                timeout=options.timeout,
            )
            if compile_process.returncode != 0:
                raise RuntimeError(f"reference kompile failed:\n{compile_process.stderr}")
            print("PASS compile: fresh pinned Haskell IMP definition")
        else:
            print("PASS compile: skipped; every proof has exact-identity cached evidence")
        failures: list[str] = []
        timings: dict[str, float] = {}
        for case in pending:
            try:
                outcome, elapsed = prove_case(
                    case,
                    kprove=kprove,
                    definition=definition,
                    workspace=workspace,
                    normalizer=normalizer,
                    timeout=options.timeout,
                    artifacts=artifacts,
                    bounds=bounds,
                    identity=identities[case["name"]],
                )
                outcomes[case["name"]] = outcome
                timings[case["name"]] = elapsed
                qualifier = " LONG" if elapsed >= LONG_SECONDS else ""
                print(
                    f"PASS proof {case['name']}: {outcome['status']} "
                    f"in {elapsed:.2f}s{qualifier}"
                )
            except subprocess.TimeoutExpired as error:
                print(f"FAIL proof {case['name']}: watchdog timeout after {error.timeout}s")
                raise RuntimeError(
                    f"proof {case['name']} exceeded the operational watchdog; "
                    "completed evidence was retained and bounds were not changed"
                ) from error
            except (json.JSONDecodeError, OSError, ValueError) as error:
                failures.append(f"{case['name']}: {error}")
                print(f"FAIL proof {case['name']}: {error}")
        missing = [case["name"] for case in cases["cases"] if case["name"] not in outcomes]
        if failures:
            raise RuntimeError(f"proof corpus incomplete; missing={missing}; failures={failures}")
        if missing:
            if options.case:
                print(
                    "PASS partial evidence: "
                    f"selected={sorted(selected_names)}, remaining={missing}"
                )
                return 0
            raise RuntimeError(f"proof corpus incomplete; missing={missing}; failures=[]")

    proposal = dict(pins)
    proposal["proof_outcomes"] = outcomes
    if options.write_proposal is not None:
        destination = options.write_proposal.resolve()
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(proposal, indent=2) + "\n", encoding="utf-8")
        print(f"PASS proposal: wrote {destination}")
    elif outcomes != pins["proof_outcomes"]:
        raise RuntimeError(f"proof pins differ; observed={json.dumps(outcomes, sort_keys=True)}")
    else:
        print("PASS pins: all ten exact reference outcomes match")
    long_cases = {name: seconds for name, seconds in timings.items() if seconds >= LONG_SECONDS}
    print(f"PASS timing: unusually long (>= {LONG_SECONDS:.0f}s) = {long_cases}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (
        json.JSONDecodeError,
        KeyError,
        OSError,
        RuntimeError,
        TypeError,
        ValueError,
        subprocess.TimeoutExpired,
    ) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
