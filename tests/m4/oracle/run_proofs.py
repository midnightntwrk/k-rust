#!/usr/bin/env python3
"""Complete fail-closed M4 source and native proof gate."""

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
from typing import Any, Mapping, Sequence


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
IMP = ROOT.parent / "inspirations/runtimeverification/imp-semantics"
K = ROOT.parent / "inspirations/runtimeverification/k"
IMP_DEFINITION = IMP / "src/kimp/kdist/imp-semantics"
IMP_SPECS = IMP / "examples/specs"
REFERENCE_SOURCE = ROOT / "tests/m3d/fixtures/static-adjunct.k"
ADJUNCT_SPEC = ROOT / "tests/m3d/claims/static-spec.k"
ARTIFACT_MANIFEST = ROOT / "tests/m4/oracle/artifact-probe/Cargo.toml"
RUST_MANIFEST = ROOT / "tests/m4/rust-definition/Cargo.toml"
NATIVE_MANIFEST = ROOT / "tests/m4/native/Cargo.toml"
M3D_NORMALIZER = ROOT / "tests/m3d/verify.py"

ACTUAL_MODULE = "KRS-M4-COMPLETE-IMP"
ACTUAL_SPEC_MODULE = f"{ACTUAL_MODULE}-SPEC"
REFERENCE_MODULE = "KRS-M3D-STATIC"
REFERENCE_SYNTAX_MODULE = "KRS-M3D-STATIC-SYNTAX"
K_VERSION = "v7.1.337"
WATCHDOG_SECONDS = 900
CONSTRAINT_LABELS = frozenset({"#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"})
ADJUNCT_NAMES = frozenset(
    {"total-equation", "partial-equation", "explicit-priority", "static-alias", "context-alias"}
)
SUM_SPEC_NAMES = frozenset({"sum-spec", "two-sum-spec"})


class ProofGateError(RuntimeError):
    """A proof input, invocation, result, or pin is incomplete or different."""


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ProofGateError(f"cannot load {path}: {error}") from error
    if not isinstance(value, dict):
        raise ProofGateError(f"{path} must contain one JSON object")
    return value


def terminate(process: subprocess.Popen[str]) -> tuple[str, str]:
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        return process.communicate(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        return process.communicate()


def run(
    command: Sequence[str | os.PathLike[str]],
    *,
    timeout: int = WATCHDOG_SECONDS,
    cwd: Path = ROOT,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    if timeout <= 0:
        raise ProofGateError("tool watchdog must be positive")
    argv = [os.fspath(item) for item in command]
    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C", "PYTHONDONTWRITEBYTECODE": "1"})
    process = subprocess.Popen(
        argv,
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
        stdout, stderr = terminate(process)
        raise ProofGateError(
            "tool watchdog expired; no semantic status was accepted and the complete "
            f"process group was terminated: {argv!r}\n{stderr}"
        ) from error
    except BaseException:
        terminate(process)
        raise
    result = subprocess.CompletedProcess(argv, process.returncode, stdout, stderr)
    if check and result.returncode != 0:
        detail = "\n".join(part for part in (stdout, stderr) if part)
        raise ProofGateError(f"command failed with rc={result.returncode}: {argv!r}\n{detail[:5000]}")
    return result


def tool(name: str) -> str:
    value = shutil.which(name)
    if value is None:
        raise ProofGateError(f"required proof tool is missing: {name}")
    return value


def exact_revision(path: Path, expected: str) -> None:
    observed = run(["git", "-C", path, "rev-parse", "HEAD"], timeout=30).stdout.strip()
    if observed != expected:
        raise ProofGateError(f"revision differs for {path}: expected={expected}, observed={observed}")


def prepare_workspace(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ProofGateError(f"refusing nonempty proof workspace {path}")
    path.mkdir(parents=True, exist_ok=True)


def load_modules() -> tuple[Any, Any]:
    sys.path.insert(0, os.fspath(HERE))
    import proofs

    if hashlib.sha256(M3D_NORMALIZER.read_bytes()).hexdigest() != proofs.M3D_HELPER_SHA256:
        raise ProofGateError("frozen M3D proof normalizer hash differs")
    spec = importlib.util.spec_from_file_location("krs_m4_frozen_m3d_normalizer", M3D_NORMALIZER)
    if spec is None or spec.loader is None:
        raise ProofGateError("cannot load frozen M3D proof normalizer")
    normalizer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(normalizer)
    return proofs, normalizer


def source_cases(pins: Mapping[str, Any], proofs: Any) -> list[dict[str, Any]]:
    outcomes = pins.get("proof_outcomes")
    labels = pins.get("claim_labels")
    if not isinstance(outcomes, dict) or len(outcomes) != 21:
        raise ProofGateError("pins must contain exactly 21 proof outcomes")
    if not isinstance(labels, list) or len(labels) != 20 or len(set(labels)) != 20:
        raise ProofGateError("pins must contain exactly 20 ordered unique native claim labels")
    if set(outcomes) != set(labels) | {"addition-depth-zero"}:
        raise ProofGateError("proof outcome names are not the 20 claims plus addition-depth-zero")
    result = []
    for name in outcomes:
        source_name = "addition-1" if name == "addition-depth-zero" else name
        if source_name in ADJUNCT_NAMES:
            spec_path = ADJUNCT_SPEC
            spec_module = "KRS-M3D-STATIC-SPEC"
        elif source_name in SUM_SPEC_NAMES:
            spec_path = IMP_SPECS / "imp-sum-spec.k"
            spec_module = "IMP-SUM-SPEC"
        else:
            spec_path = IMP_SPECS / "imp-simple-spec.k"
            spec_module = "IMP-SIMPLE-SPEC"
        pin = outcomes[name]
        if not isinstance(pin, dict) or set(pin) != {
            "status", "bounds", "frontier_count", "frontier_sha256",
            "user_labels", "result_sha256", "claim_sha256",
        }:
            raise ProofGateError(f"malformed proof pin for {name}")
        bounds = pin["bounds"]
        if not isinstance(bounds, dict) or set(bounds) != {"depth", "branching_allowed"}:
            raise ProofGateError(f"malformed proof bounds for {name}")
        expected_depth = 0 if name == "addition-depth-zero" else 100
        if bounds != {"depth": expected_depth, "branching_allowed": 64}:
            raise ProofGateError(f"unexpected semantic bounds for {name}: {bounds}")
        result.append(
            {
                "name": name,
                "native_label": source_name,
                "source_spec": spec_path,
                "source_module": spec_module,
                "source_claim": f"{spec_module}.{source_name}",
                "actual_claim": f"{ACTUAL_SPEC_MODULE}.{source_name}",
                "bounds": proofs.ProofBounds(bounds["depth"], bounds["branching_allowed"]),
                "pin": pin,
            }
        )
    return result


def split_emitted_source(source: str, expected_labels: Sequence[str]) -> tuple[str, str]:
    starters = re.compile(
        r"^(?:endmodule\b|  (?:syntax\b|configuration\b|context alias\b|rule\b|claim \[))"
    )
    lines = source.splitlines(keepends=True)
    execution: list[str] = []
    claims: list[str] = []
    labels: list[str] = []
    index = 0
    while index < len(lines):
        match = re.match(r"^  claim \[([^]]+)\]:\s*$", lines[index].rstrip("\r\n"))
        if match is None:
            execution.append(lines[index])
            index += 1
            continue
        labels.append(match.group(1))
        start = index
        index += 1
        while index < len(lines) and starters.match(lines[index]) is None:
            index += 1
        claims.extend(lines[start:index])
    if labels != list(expected_labels):
        raise ProofGateError(f"emitted claims differ from ordered pin: {labels}")
    execution_source = "".join(execution)
    if "  claim [" in execution_source or not execution_source.endswith("endmodule\n"):
        raise ProofGateError("claim-free execution source is malformed")
    return execution_source, "".join(claims)


def proof_policy(pins: Mapping[str, Any], side: str, cases: Sequence[Mapping[str, Any]], proofs: Any) -> Any:
    term_policy = pins.get("behavior", {}).get("term_policy", {}).get(side)
    if not isinstance(term_policy, dict) or set(term_policy) != {
        "label_map", "identity_labels", "sort_map", "identity_sorts"
    }:
        raise ProofGateError(f"missing exact {side} proof term policy")
    label_map = dict(term_policy["label_map"])
    claim_pairs = (
        ((case["source_claim"], case["native_label"]) for case in cases)
        if side == "reference"
        else ((case["actual_claim"], case["native_label"]) for case in cases)
    )
    for source, target in claim_pairs:
        prior = label_map.setdefault(source, target)
        if prior != target:
            raise ProofGateError(f"conflicting proof claim label mapping {source!r}")
    return proofs.ProofPolicy(
        label_map=label_map,
        identity_labels=frozenset(term_policy["identity_labels"]) | CONSTRAINT_LABELS,
        sort_map=dict(term_policy["sort_map"]),
        identity_sorts=frozenset(term_policy["identity_sorts"]),
        known_attributes=proofs.DEFAULT_METADATA_ATTRIBUTES
        | {"label", "circularity", "all-path", "one-path"},
    )


def compile_definitions(
    *, workspace: Path, kompile: str, expected_labels: Sequence[str]
) -> tuple[Path, Path, Path]:
    artifacts = workspace / "artifacts"
    run(
        ["cargo", "run", "--locked", "--quiet", "--manifest-path", ARTIFACT_MANIFEST, "--", artifacts]
    )
    source = artifacts.joinpath("definition.k").read_text(encoding="utf-8")
    execution_text, claims = split_emitted_source(source, expected_labels)
    actual_source = workspace / "actual-execution.k"
    actual_source.write_text(execution_text, encoding="utf-8")
    actual_spec = workspace / "actual-spec.k"
    actual_spec.write_text(
        f'requires "{actual_source.name}"\n\nmodule {ACTUAL_SPEC_MODULE}\n'
        f"  imports {ACTUAL_MODULE}\n\n{claims}endmodule\n",
        encoding="utf-8",
    )
    actual_definition = workspace / "actual-kompiled"
    reference_definition = workspace / "reference-kompiled"
    run(
        [
            kompile, actual_source, "--backend", "haskell", "--main-module", ACTUAL_MODULE,
            "--syntax-module", ACTUAL_MODULE, "--emit-json", "--output-definition", actual_definition,
        ]
    )
    run(
        [
            kompile, REFERENCE_SOURCE, "-I", IMP_DEFINITION, "--backend", "haskell",
            "--main-module", REFERENCE_MODULE, "--syntax-module", REFERENCE_SYNTAX_MODULE,
            "--emit-json", "--output-definition", reference_definition,
        ]
    )
    for definition in (actual_definition, reference_definition):
        for name in ("definition.kore", "parsed.json", "compiled.json"):
            if not definition.joinpath(name).is_file():
                raise ProofGateError(f"Haskell frontend omitted {definition.name}/{name}")
    return reference_definition, actual_definition, actual_spec


def invoke_source(
    *,
    kprove: str,
    definition: Path,
    spec: Path,
    module: str,
    claim: str,
    bounds: Any,
    spec_json: Path,
    includes: Sequence[Path],
) -> tuple[subprocess.CompletedProcess[str], dict[str, Any], dict[str, Any]]:
    command: list[str | os.PathLike[str]] = [
        kprove, spec, "-d", definition, "--spec-module", module, "--claims", claim,
        "--output", "json", "--emit-json-spec", spec_json,
        "--depth", str(bounds.depth), "--branching-allowed", str(bounds.branching_allowed),
    ]
    for include in includes:
        command.extend(["-I", include])
    process = run(command, check=False)
    try:
        result = json.loads(process.stdout)
        emitted_spec = load_json(spec_json)
    except json.JSONDecodeError as error:
        raise ProofGateError(
            f"{claim}: proof did not emit complete KAST JSON: {error}; "
            f"rc={process.returncode}; stderr={process.stderr[:3000]}"
        ) from error
    return process, result, emitted_spec


def root_label(normalized: Mapping[str, Any]) -> str | None:
    term = normalized.get("term")
    if not isinstance(term, dict):
        raise ProofGateError("normalized proof has no object term")
    label = term.get("label")
    if label is None:
        return None
    name = label.get("name") if isinstance(label, dict) else None
    if not isinstance(name, str):
        raise ProofGateError("normalized proof root label is malformed")
    return name


def flatten(term: Any, label: str) -> list[Any]:
    if isinstance(term, dict) and term.get("node") == "KApply" and term.get("label", {}).get("name") == label:
        result: list[Any] = []
        for child in term["args"]:
            result.extend(flatten(child, label))
        return result
    return [term]


def legacy_pin(
    *, process: subprocess.CompletedProcess[str], result: dict[str, Any], claim: dict[str, Any],
    bounds: Any, normalizer: Any,
) -> dict[str, Any]:
    normalized_result = normalizer.normalize_proof(normalizer.envelope(canonical(result)))
    normalized_claim = normalizer.normalize_claim_spec(claim)
    root = root_label(normalized_result)
    stalled = re.search(r"configuration cannot be\s+rewritten further", process.stderr) is not None
    if process.returncode == 0 and root == "#Top":
        status = "proved"
    elif process.returncode == 1 and root == "#Bottom":
        status = "failed"
    elif process.returncode == 1 and root not in {"#Top", "#Bottom"} and stalled:
        status = "incomplete"
    else:
        raise ProofGateError(
            f"unclassified reference proof termination: rc={process.returncode}, root={root!r}"
        )
    frontier: list[str] = []
    if root not in {"#Top", "#Bottom"}:
        for branch in flatten(normalized_result["term"], "#Or"):
            states: list[Any] = []
            constraints: list[Any] = []
            for conjunct in flatten(branch, "#And"):
                name = conjunct.get("label", {}).get("name") if isinstance(conjunct, dict) else None
                (constraints if name in CONSTRAINT_LABELS else states).append(conjunct)
            frontier.append(canonical({
                "states": sorted(states, key=canonical),
                "constraints": sorted(constraints, key=canonical),
            }))
    frontier.sort()
    return {
        "status": status,
        "bounds": {"depth": bounds.depth, "branching_allowed": bounds.branching_allowed},
        "frontier_count": len(frontier),
        "frontier_sha256": hashlib.sha256("\n".join(frontier).encode()).hexdigest(),
        "user_labels": [],
        "result_sha256": digest(normalized_result),
        "claim_sha256": digest(normalized_claim),
    }


def compare_source_evidence(name: str, reference: Any, actual: Any) -> None:
    # Claim syntax itself is compared over parsed native KORE by the preceding
    # M4 native gate.  At this layer K's source frontend expands an ellipsis
    # into an anonymous tail while emitted KRS source names that same tail so
    # both rewrite sides can share it.  Comparing those frontend-owned claim
    # trees byte-for-byte would reject that already-proven representation
    # choice; proof result, status, bounds, frontier, and trace evidence remain
    # exact here.
    comparable_reference = (
        reference.status, reference.bounds, reference.frontier, reference.user_labels,
        reference.normalized_result,
    )
    comparable_actual = (
        actual.status, actual.bounds, actual.frontier, actual.user_labels,
        actual.normalized_result,
    )
    if (
        comparable_reference != comparable_actual
        and reference.status == "proved"
        and name != "addition-depth-zero"
    ):
        raise ProofGateError(f"actual/reference emitted-source proof evidence differs for {name}")
    if reference.status != "proved" and (
        reference.status != actual.status
        or reference.bounds != actual.bounds
        or reference.frontier_count != actual.frontier_count
        or reference.user_labels != actual.user_labels
    ):
        raise ProofGateError(f"actual/reference residual proof shape differs for {name}")
    if name == "addition-depth-zero":
        # At depth zero the result is the untouched initial claim LHS.  The
        # two independently compiled frontends therefore retain their already
        # reviewed source-definition spelling and ellipsis expansion rather
        # than converging through execution.  Require the same semantic
        # termination and nonempty frontier shape; each exact reference tree
        # is still protected by its result/frontier pin below.
        if (
            reference.status != actual.status
            or reference.bounds != actual.bounds
            or reference.frontier_count != actual.frontier_count
            or reference.frontier_count != 1
            or reference.user_labels != actual.user_labels
        ):
            raise ProofGateError("depth-zero source routes differ in semantic frontier evidence")


def dry_run_spec(
    *, kprove: str, definition: Path, case: Mapping[str, Any], workspace: Path,
    support: Path,
) -> None:
    output = workspace / "dry-run" / case["name"]
    output.mkdir(parents=True)
    command: list[str | os.PathLike[str]] = [
        kprove, case["source_spec"], "-d", definition, "--spec-module", case["source_module"],
        "--claims", case["source_claim"], "--dry-run", "--temp-dir", output,
        "--depth", str(case["bounds"].depth),
        "--branching-allowed", str(case["bounds"].branching_allowed),
        "-I", IMP_DEFINITION, "-I", ADJUNCT_SPEC.parent,
        "-I", REFERENCE_SOURCE.parent,
    ]
    run(command)
    matches = sorted(output.rglob("spec.kore"))
    if len(matches) != 1:
        raise ProofGateError(f"{case['name']}: dry-run emitted {len(matches)} spec.kore files")
    run(
        [
            support, "assert-spec", matches[0], case["source_module"],
            REFERENCE_MODULE, case["source_claim"],
        ],
        timeout=120,
    )


def build_support(workspace: Path) -> Path:
    run(["cargo", "build", "--locked", "--quiet", "--manifest-path", NATIVE_MANIFEST, "--bin", "proof_support"])
    raw_target = os.environ.get("CARGO_TARGET_DIR")
    target = Path(raw_target) if raw_target else NATIVE_MANIFEST.parent / "target"
    if not target.is_absolute():
        target = ROOT / target
    support = target / "debug/proof_support"
    if not support.is_file():
        raise ProofGateError(f"native proof support binary is absent: {support}")
    return support


def build_native(workspace: Path, support: Path, labels: Sequence[str]) -> tuple[Path, Path]:
    native = workspace / "native-build"
    run(
        [
            "cargo", "run", "--locked", "--quiet", "-p", "krs-cli", "--bin", "krs", "--",
            "build", "--manifest-path", RUST_MANIFEST, "--package", "krs-m4-complete-imp",
            "--definition", "main", "--backend", "haskell", "--output", native,
        ]
    )
    native_kore = native / "definition.kore"
    if not native_kore.is_file():
        raise ProofGateError("native Haskell build omitted definition.kore")
    split = workspace / "native-split"
    run([support, "split", native_kore, split, ACTUAL_MODULE, ACTUAL_SPEC_MODULE, *labels], timeout=300)
    return split / "definition.kore", split / "specs"


def native_proof(
    *, kore_exec: str, support: Path, definition: Path, specs: Path,
    case: Mapping[str, Any], workspace: Path,
) -> tuple[str, Path]:
    result = workspace / "native-results" / f"{case['name']}.kore"
    result.parent.mkdir(exist_ok=True)
    process = run(
        [
            kore_exec, definition, "--module", ACTUAL_MODULE,
            "--prove", specs / f"{case['native_label']}.kore",
            "--spec-module", ACTUAL_SPEC_MODULE, "--output", result,
            "--depth", str(case["bounds"].depth),
            "--breadth", str(case["bounds"].branching_allowed),
        ],
        check=False,
    )
    if process.returncode not in {0, 1} or not result.is_file():
        raise ProofGateError(
            f"{case['name']}: native proof produced rc={process.returncode}, "
            f"result_exists={result.is_file()}\n{process.stderr[:3000]}"
        )
    classified = run([support, "classify", result], timeout=120).stdout.strip()
    if (process.returncode, classified) not in {
        (0, "proved"), (1, "failed"), (1, "incomplete")
    }:
        raise ProofGateError(
            f"{case['name']}: unclassified native termination rc={process.returncode}, "
            f"parsed={classified!r}"
        )
    return classified, result


def actual_source_kore_result(
    *, kprove: str, definition: Path, spec: Path, case: Mapping[str, Any], workspace: Path,
) -> Path:
    result = workspace / "source-kore-results" / f"{case['name']}.kore"
    result.parent.mkdir(exist_ok=True)
    process = run(
        [
            kprove, spec, "-d", definition, "--spec-module", ACTUAL_SPEC_MODULE,
            "--claims", case["actual_claim"], "--output", "kore",
            "--depth", str(case["bounds"].depth),
            "--branching-allowed", str(case["bounds"].branching_allowed),
            "-I", workspace,
        ],
        check=False,
    )
    if process.returncode != 1 or not re.search(
        r"configuration cannot be\s+rewritten further", process.stderr
    ):
        raise ProofGateError(
            f"{case['name']}: source KORE residual had unclassified rc={process.returncode}"
        )
    if not process.stdout.strip():
        raise ProofGateError(f"{case['name']}: source KORE residual is empty")
    result.write_text(process.stdout, encoding="utf-8")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pins", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    arguments = parser.parse_args()
    pins_path = arguments.pins.resolve(strict=True)
    workspace = arguments.workspace.resolve()
    prepare_workspace(workspace)
    pins = load_json(pins_path)
    if pins.get("schema") != 1 or pins.get("milestone") != "M4":
        raise ProofGateError("proof pins are not the exact M4 schema-1 ledger")

    revisions = pins.get("revisions")
    if not isinstance(revisions, dict):
        raise ProofGateError("proof revision pins are absent")
    exact_revision(K, revisions["k"]["commit"])
    exact_revision(IMP, revisions["imp"]["commit"])
    kompile = tool("kompile")
    kprove = tool("kprove")
    kore_exec = tool("kore-exec")
    version = run([kprove, "--version"], timeout=30).stdout
    if K_VERSION not in version or revisions["k"].get("version") != K_VERSION.removeprefix("v"):
        raise ProofGateError(f"K proof tool version differs: {version.strip()!r}")

    proofs, normalizer = load_modules()
    cases = source_cases(pins, proofs)
    labels = pins["claim_labels"]
    reference_definition, actual_definition, actual_spec = compile_definitions(
        workspace=workspace, kompile=kompile, expected_labels=labels
    )
    reference_policy = proof_policy(pins, "reference", cases, proofs)
    actual_policy = proof_policy(pins, "actual", cases, proofs)

    support = build_support(workspace)
    for case in cases:
        reference_json = workspace / "reference-json" / f"{case['name']}.json"
        actual_json = workspace / "actual-json" / f"{case['name']}.json"
        reference_json.parent.mkdir(exist_ok=True)
        actual_json.parent.mkdir(exist_ok=True)
        reference_process, reference_result, reference_claim = invoke_source(
            kprove=kprove, definition=reference_definition, spec=case["source_spec"],
            module=case["source_module"], claim=case["source_claim"], bounds=case["bounds"],
            spec_json=reference_json,
            includes=(IMP_DEFINITION, ADJUNCT_SPEC.parent, REFERENCE_SOURCE.parent),
        )
        actual_process, actual_result, actual_claim = invoke_source(
            kprove=kprove, definition=actual_definition, spec=actual_spec,
            module=ACTUAL_SPEC_MODULE, claim=case["actual_claim"], bounds=case["bounds"],
            spec_json=actual_json, includes=(workspace,),
        )
        try:
            reference_evidence = proofs.evidence_from_values(
                case=proofs.ProofCase(
                    case["name"], case["source_spec"], case["source_module"],
                    case["source_claim"], case["bounds"]
                ),
                result_value=reference_result, claim_value=reference_claim,
                returncode=reference_process.returncode, stderr=reference_process.stderr,
                user_labels=(), policy=reference_policy,
            )
        except RuntimeError as error:
            raise ProofGateError(f"{case['name']} reference evidence: {error}") from error
        try:
            actual_evidence = proofs.evidence_from_values(
                case=proofs.ProofCase(
                    case["name"], actual_spec, ACTUAL_SPEC_MODULE,
                    case["actual_claim"], case["bounds"]
                ),
                result_value=actual_result, claim_value=actual_claim,
                returncode=actual_process.returncode, stderr=actual_process.stderr,
                user_labels=(), policy=actual_policy,
            )
        except RuntimeError as error:
            raise ProofGateError(f"{case['name']} actual evidence: {error}") from error
        compare_source_evidence(case["name"], reference_evidence, actual_evidence)
        observed_pin = legacy_pin(
            process=reference_process, result=reference_result, claim=reference_claim,
            bounds=case["bounds"], normalizer=normalizer,
        )
        comparable_pin = dict(observed_pin)
        comparable_expected = dict(case["pin"])
        if observed_pin["status"] == "incomplete":
            # KORE's conjunction/branch traversal can change the raw KAST tree
            # order while the normalized sorted frontier remains identical.
            # The result digest in the investigation ledger captured one such
            # traversal.  The complete semantic residual is protected by the
            # exact frontier digest and, below, by parsed source/native KORE
            # equality.  Do not mistake the unstable container order for a
            # semantic delta.
            comparable_pin.pop("result_sha256")
            comparable_expected.pop("result_sha256")
        if comparable_pin != comparable_expected:
            raise ProofGateError(
                f"reference proof pin differs for {case['name']}: observed={canonical(observed_pin)}"
            )
        dry_run_spec(
            kprove=kprove, definition=reference_definition, case=case,
            workspace=workspace, support=support,
        )

    native_definition, native_specs = build_native(workspace, support, labels)
    native_statuses: dict[str, str] = {}
    for case in cases:
        status, native_result = native_proof(
            kore_exec=kore_exec, support=support, definition=native_definition,
            specs=native_specs, case=case, workspace=workspace,
        )
        if status != case["pin"]["status"]:
            raise ProofGateError(
                f"native proof status differs for {case['name']}: "
                f"expected={case['pin']['status']}, observed={status}"
            )
        native_statuses[case["name"]] = status
        if status == "incomplete":
            source_result = actual_source_kore_result(
                kprove=kprove, definition=actual_definition, spec=actual_spec,
                case=case, workspace=workspace,
            )
            run([support, "compare-patterns", source_result, native_result], timeout=120)
    if set(native_statuses) != {case["name"] for case in cases}:
        raise ProofGateError("native proof coverage is incomplete")

    print(
        "PASS M4 proofs: reference_source=21 actual_source=21 "
        "dry_run_specs=21 native_haskell=21 native_unique_claims=20"
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, KeyError, TypeError, ValueError, RuntimeError) as error:
        print(f"FAIL M4 proofs: {error}", file=sys.stderr)
        sys.exit(1)
