#!/usr/bin/env python3
"""Fail-closed qualification for the functionally reconstructed M3D oracle."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from typing import Any, Sequence


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WORKSPACE_ROOT = ROOT.parent
IMP = WORKSPACE_ROOT / "inspirations/runtimeverification/imp-semantics"
K = WORKSPACE_ROOT / "inspirations/runtimeverification/k"
IMP_DEFINITION = IMP / "src/kimp/kdist/imp-semantics"
IMP_SPECS = IMP / "examples/specs"
FIXTURE = HERE / "fixtures/static-adjunct.k"
STATIC_SPEC = HERE / "claims/static-spec.k"
STATIC_PROGRAM = HERE / "corpus/static-evaluation.imp"
PINS = HERE / "pins.json"
K_VERSION = "7.1.337"
TERMINATION_GRACE_SECONDS = 5
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
CONSTRAINT_LABELS = frozenset({"#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"})

# This is the exact closed metadata set copied from the lost M3D normalizer.
METADATA = {
    "org.kframework.attributes.Source",
    "org.kframework.attributes.Location",
    "org.kframework.definition.Production",
    "contentStartLine",
    "contentStartColumn",
    "digest",
    "productionID",
    "UNIQUE_ID",
}


class VerificationError(RuntimeError):
    """One recovered input or observed semantic result is not qualified."""


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def envelope(stdout: str) -> dict[str, Any]:
    value = json.loads(stdout)
    if (
        set(value) != {"format", "version", "term"}
        or value["format"] != "KAST"
        or value["version"] != 4
    ):
        raise ValueError("proof/execution output is not exactly a KAST v4 envelope")
    return value


def normalize_proof(value: dict[str, Any]) -> dict[str, Any]:
    """Exact recovered M3D proof normalizer, with a closed KAST node set."""

    value = copy.deepcopy(value)
    variables: dict[tuple[str, str], str] = {}

    def visit(node: Any) -> Any:
        if isinstance(node, list):
            return [visit(item) for item in node]
        if not isinstance(node, dict):
            return node
        kind = node.get("node")
        if kind == "KVariable":
            if set(node) != {"node", "name", "sort"}:
                raise ValueError(f"unknown KVariable fields: {sorted(node)}")
            sort = node["sort"].get("name")
            if not isinstance(sort, str):
                raise ValueError("proof variable has no concrete sort name")
            key = (node["name"], sort)
            variables.setdefault(key, f"V{len(variables)}")
            node["name"] = variables[key]
        elif kind not in {None, "KApply", "KLabel", "KSort", "KToken", "KSequence"}:
            raise ValueError(f"unclassified proof KAST node {kind!r}")
        return {key: visit(child) for key, child in node.items()}

    return visit(value)


def normalize_claim_spec(value: dict[str, Any]) -> dict[str, Any]:
    """Exact recovered M3D claim normalizer, including metadata erasure."""

    value = copy.deepcopy(value)
    variables: dict[tuple[str, str], str] = {}
    allowed = {
        None,
        "KFlatModuleList",
        "KFlatModule",
        "KImport",
        "KClaim",
        "KRewrite",
        "KApply",
        "KLabel",
        "KSort",
        "KToken",
        "KSequence",
        "KVariable",
        "KAtt",
    }

    def visit(node: Any) -> Any:
        if isinstance(node, list):
            return [visit(item) for item in node]
        if not isinstance(node, dict):
            return node
        kind = node.get("node")
        if kind not in allowed:
            raise ValueError(f"unclassified claim KAST node {kind!r}")
        result: dict[str, Any] = {}
        for key, child in node.items():
            if kind == "KAtt" and key == "att":
                child = {name: item for name, item in child.items() if name not in METADATA}
            result[key] = visit(child)
        if kind == "KVariable":
            sort = result.get("sort", {}).get("name")
            if not isinstance(sort, str):
                raise ValueError("claim variable has no concrete sort")
            variable_key = (result["name"], sort)
            variables.setdefault(variable_key, f"V{len(variables)}")
            result["name"] = variables[variable_key]
        if isinstance(result.get("imports"), list):
            result["imports"].sort(key=canonical)
        if isinstance(result.get("localSentences"), list):
            result["localSentences"].sort(key=canonical)
        return result

    return visit(value)


def terminate_session(process: subprocess.Popen[str]) -> tuple[str, str]:
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
    command: Sequence[str | Path],
    *,
    timeout: int,
    cwd: Path = ROOT,
) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C", "PYTHONDONTWRITEBYTECODE": "1"})
    process = subprocess.Popen(
        [str(part) for part in command],
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
            f"watchdog expired after {timeout}s; process session was reaped: "
            f"{list(command)!r}\nstdout={stdout}\nstderr={stderr}"
        ) from error
    except BaseException:
        terminate_session(process)
        raise
    return subprocess.CompletedProcess(list(command), process.returncode, stdout, stderr)


def required_tool(name: str, timeout: int) -> str:
    executable = shutil.which(name)
    if executable is None:
        raise VerificationError(f"required tool {name!r} is unavailable")
    version = run([executable, "--version"], timeout=timeout)
    if version.returncode != 0 or f"v{K_VERSION}" not in version.stdout + version.stderr:
        raise VerificationError(f"{name} is not pinned to K v{K_VERSION}")
    return executable


def exact_revision(path: Path, expected: str, timeout: int) -> None:
    process = run(["git", "rev-parse", "HEAD"], cwd=path, timeout=timeout)
    if process.returncode != 0 or process.stdout.strip() != expected:
        raise VerificationError(
            f"revision mismatch for {path}: expected={expected}, observed={process.stdout.strip()}"
        )


def root_label(normalized: dict[str, Any]) -> str | None:
    term = normalized.get("term")
    if not isinstance(term, dict):
        raise VerificationError("normalized proof has no object term")
    label = term.get("label")
    if label is None:
        return None
    if not isinstance(label, dict) or not isinstance(label.get("name"), str):
        raise VerificationError("normalized proof root label is malformed")
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
    raise VerificationError(
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
        raise VerificationError(f"expected one selected KClaim, found {len(found)}")
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
    )
    try:
        normalized_result = normalize_proof(envelope(process.stdout))
        claim_value = json.loads(spec_json.read_text(encoding="utf-8"))
        selected = unique_claim(claim_value)
        if selected.get("att", {}).get("att", {}).get("label") != case["claim"]:
            raise VerificationError(f"selected claim differs for {case['name']}")
        normalized_claim = normalize_claim_spec(claim_value)
    except (OSError, json.JSONDecodeError, ValueError) as error:
        raise VerificationError(f"incomplete proof evidence for {case['name']}: {error}") from error
    frontier = normalized_frontier(normalized_result)
    return {
        "status": classify(process.returncode, root_label(normalized_result), process.stderr),
        "bounds": {"depth": case["depth"], "branching_allowed": 64},
        "frontier_count": len(frontier),
        "frontier_sha256": hashlib.sha256("\n".join(frontier).encode()).hexdigest(),
        "user_labels": [],
        "result_sha256": digest(normalized_result),
        "claim_sha256": digest(normalized_claim),
    }


def source_paths() -> dict[str, Path]:
    return {
        "README.md": HERE / "README.md",
        "claims/static-spec.k": STATIC_SPEC,
        "corpus/static-evaluation.imp": STATIC_PROGRAM,
        "fixtures/induced-definition-error.k": HERE / "fixtures/induced-definition-error.k",
        "fixtures/induced-source-error.k": HERE / "fixtures/induced-source-error.k",
        "fixtures/static-adjunct.k": FIXTURE,
        "verify.py": HERE / "verify.py",
    }


def upstream_paths() -> dict[str, Path]:
    return {
        f"definition/{name}": IMP_DEFINITION / name
        for name in ("expr.k", "calc.k", "imp.k", "imp-verification.k")
    } | {
        f"specs/{name}": IMP_SPECS / name
        for name in ("imp-simple-spec.k", "imp-sum-spec.k")
    }


def observed_ledger(outcomes: dict[str, dict[str, Any]]) -> dict[str, Any]:
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
        "reference_k": {
            "version": K_VERSION,
            "commit": "4a46d1231473b599c699160132fd6e76a5c46406",
        },
        "upstream_imp": {"commit": "683a773418add3bcae8ded47c2b24e94494e1988"},
        "reconstruction": {
            "original_verify_sha256": "2ed14f41b39cf95fdfd132d1fa675c3d550375c75499d78711a2c901d023bc9f",
            "original_pins_sha256": "2a27f0efead1c233f59f81d4e7c4fe37b56d8b1dcba203ff52e63d7769ecc085",
            "original_fixture_sha256": "ffbe89ef33ad062c0d1e58f6fc77f52ec0063365155b3042cae8a247a328a462",
            "original_spec_sha256": "2b32479b9e982cac3c8ebb0b6e423662219c9d1ed1d387be80050732a522d444",
            "claim": "functional reconstruction; original blobs unavailable",
        },
        "source_sha256": {name: sha256(path) for name, path in source_paths().items()},
        "upstream_sha256": {name: sha256(path) for name, path in upstream_paths().items()},
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
    )
    if process.returncode == 0 or "[Error]" not in process.stderr:
        raise VerificationError(f"induced diagnostic unexpectedly accepted: {fixture}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--write-proposal", type=Path)
    options = parser.parse_args()
    if options.timeout <= 0:
        raise VerificationError("--timeout must be positive")

    kompile = required_tool("kompile", options.timeout)
    kprove = required_tool("kprove", options.timeout)
    krun = required_tool("krun", options.timeout)
    exact_revision(K, "4a46d1231473b599c699160132fd6e76a5c46406", options.timeout)
    exact_revision(IMP, "683a773418add3bcae8ded47c2b24e94494e1988", options.timeout)

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
        )
        if compiled.returncode != 0:
            raise VerificationError(f"M3D compilation failed:\n{compiled.stderr}")
        print("PASS M3D compile: reconstructed static definition")

        executed = run(
            [krun, STATIC_PROGRAM, "-cENV=.Map", "-d", definition, "--output", "pretty", "--color", "off"],
            timeout=options.timeout,
        )
        compact = re.sub(r"\s+", " ", executed.stdout)
        if executed.returncode != 0 or "x |-> 6" not in compact or "y |-> m3dZero" not in compact:
            raise VerificationError(f"static execution differs:\n{executed.stdout}\n{executed.stderr}")
        print("PASS M3D execution: x=6, y=0 (reversible m3dZero unparse)")

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

    observed = observed_ledger(outcomes)
    if options.write_proposal is not None:
        destination = options.write_proposal.resolve()
        if destination.exists():
            raise VerificationError(f"proposal destination exists: {destination}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(observed, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"PASS M3D proposal: {destination}")
        return 0
    if not PINS.is_file():
        raise VerificationError("reconstructed pins are absent; use --write-proposal")
    expected = json.loads(PINS.read_text(encoding="utf-8"))
    if expected != observed:
        raise VerificationError("M3D reconstructed pins differ from live evidence")
    print(f"PASS M3D reconstructed oracle: evidence={digest(observed)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, VerificationError, ValueError, json.JSONDecodeError) as error:
        print(f"FAIL M3D: {error}", file=sys.stderr)
        raise SystemExit(1) from error
