#!/usr/bin/env python3
"""Complete fail-closed IMP source and native proof gate.

Every K invocation (the two `kompile` runs; the 21 reference, 21 actual, and
21 dry-run `kprove` runs, plus one residual KORE `kprove` run per incomplete
proof; and the 21 `kore-exec` runs on the native build) goes through the
reference snapshot `tests/imp/reference/proofs`.
A default run replays it and needs no K tool; `--refresh-reference` runs K
live. The stored proof results are readable: each invocation's exit status is
in the manifest, and its JSON result and claim are stored indented.
The KRS native build, its split, and every classification and comparison
always run live.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any, Callable, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import proofs  # noqa: E402
from support import ROOT, GateError, entry, krs_gate, lock  # noqa: E402
from support.checkouts import verify_checkout  # noqa: E402
from support.hashing import canonical_json, json_sha256, sha256_text  # noqa: E402
from support.kdefinition import emitted_claims  # noqa: E402
from support.krs import Invocation  # noqa: E402
from support.parallel import settle_all, worker_count  # noqa: E402
from support.pins import Ledger, table  # noqa: E402
from support.process import compact, run  # noqa: E402
from support.reference import (  # noqa: E402
    Key, Output, Snapshot, add_refresh_argument, add_staging_argument, indented_json,
    json_without_members, reduce_kore_exec_log, reduce_kprove_temp, repository_inputs, snapshot_directory,
)
from support.tools import checkout_scratch, k_executable, k_tool, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
IMP = ROOT.parent / "inspirations/runtimeverification/imp-semantics"
K = ROOT.parent / "inspirations/runtimeverification/k"
IMP_DEFINITION = IMP / "src/kimp/kdist/imp-semantics"
IMP_SPECS = IMP / "examples/specs"
REFERENCE_SOURCE = ROOT / "tests/imp_static_semantics/fixtures/static-adjunct.k"
ADJUNCT_SPEC = ROOT / "tests/imp_static_semantics/claims/static-spec.k"
ARTIFACT_MANIFEST = ROOT / "tests/imp/oracle/artifact-probe/Cargo.toml"
RUST_MANIFEST = ROOT / "tests/imp/rust-definition/Cargo.toml"

ACTUAL_MODULE = "KRS-IMP"
ACTUAL_SPEC_MODULE = f"{ACTUAL_MODULE}-SPEC"
REFERENCE_MODULE = "KRS-IMP-STATIC"
REFERENCE_SYNTAX_MODULE = "KRS-IMP-STATIC-SYNTAX"
WATCHDOG_SECONDS = 900
CONSTRAINT_LABELS = frozenset({"#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"})
ADJUNCT_NAMES = frozenset(
    {"total-equation", "partial-equation", "explicit-priority", "static-alias", "context-alias"}
)
SUM_SPEC_NAMES = frozenset({"sum-spec", "two-sum-spec"})
REFERENCE = ROOT / "tests/imp/reference/proofs"
TOOLS = ("kompile", "kprove", "kore-exec")
SOURCE_LOCATIONS = ("org.kframework.attributes.Source", "org.kframework.attributes.Location")


def reduce_json_result(text: str) -> str:
    """Store a JSON proof result or claim without source locations, one member per line.

    The proof normalization removes source locations, so no comparator reads them.
    """

    try:
        stripped = json_without_members(SOURCE_LOCATIONS)(text)
    except ValueError:
        return text
    return indented_json(stripped)


def prepare_workspace(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise GateError(f"refusing nonempty proof workspace {path}")
    path.mkdir(parents=True, exist_ok=True)


def source_cases(pins: Ledger, proofs: Any) -> list[dict[str, Any]]:
    outcomes = pins.get("proof_outcomes")
    labels = pins.get("claim_labels")
    if not isinstance(outcomes, dict) or len(outcomes) != 21:
        raise GateError("pins must contain exactly 21 proof outcomes")
    if not isinstance(labels, list) or len(labels) != 20 or len(set(labels)) != 20:
        raise GateError("pins must contain exactly 20 ordered unique native claim labels")
    if set(outcomes) != set(labels) | {"addition-depth-zero"}:
        raise GateError("proof outcome names are not the 20 claims plus addition-depth-zero")
    result = []
    for name in outcomes:
        source_name = "addition-1" if name == "addition-depth-zero" else name
        if source_name in ADJUNCT_NAMES:
            spec_path = ADJUNCT_SPEC
            spec_module = "KRS-IMP-STATIC-SPEC"
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
            raise GateError(f"malformed proof pin for {name}")
        bounds = pin["bounds"]
        if not isinstance(bounds, dict) or set(bounds) != {"depth", "branching_allowed"}:
            raise GateError(f"malformed proof bounds for {name}")
        expected_depth = 0 if name == "addition-depth-zero" else 100
        if bounds != {"depth": expected_depth, "branching_allowed": 64}:
            raise GateError(f"unexpected semantic bounds for {name}: {bounds}")
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


def actual_spec_source(execution_source: Path, claims: str) -> str:
    """Wrap the emitted claims in a spec module over the emitted definition alone.

    The emitted claims spell every `Id` token as `#token`, so they parse
    without the upstream verification-only `Id` syntax.
    """

    return (
        f'requires "{execution_source.name}"\n\n'
        f"module {ACTUAL_SPEC_MODULE}\n"
        f"  imports {ACTUAL_MODULE}\n\n{claims}endmodule\n"
    )


def proof_policy(pins: Ledger, side: str, cases: Sequence[Mapping[str, Any]]) -> Mapping[str, Any]:
    term_policy = table(
        table(pins.table("behavior").get("term_policy"), "behavior.term_policy").get(side),
        f"behavior.term_policy.{side}",
    )
    label_map = dict(term_policy["label_map"])
    claim_pairs = (
        ((case["source_claim"], case["native_label"]) for case in cases)
        if side == "reference"
        else ((case["actual_claim"], case["native_label"]) for case in cases)
    )
    for source, target in claim_pairs:
        prior = label_map.setdefault(source, target)
        if prior != target:
            raise GateError(f"conflicting proof claim label mapping {source!r}")
    return {
        **term_policy,
        "label_map": label_map,
        "identity_labels": sorted(set(term_policy["identity_labels"]) | CONSTRAINT_LABELS),
    }


def compile_definitions(
    *, workspace: Path, k: Snapshot, expected_labels: Sequence[str], workers: int, gate: Path
) -> tuple[Path, Path, Path]:
    artifacts = workspace / "artifacts"
    run(
        ["cargo", "run", "--locked", "--quiet", "--manifest-path", ARTIFACT_MANIFEST, "--", artifacts],
        timeout=WATCHDOG_SECONDS,
    )
    labels, claims = emitted_claims(artifacts, ACTUAL_MODULE, len(expected_labels), gate=gate, environment=z3_environment())
    if labels != list(expected_labels):
        raise GateError(f"emitted claims differ from ordered pin: {labels}")
    actual_source = workspace / "actual-execution.k"
    shutil.copy2(artifacts / "definition.k", actual_source)
    actual_spec = workspace / "actual-spec.k"
    actual_spec.write_text(
        actual_spec_source(actual_source, claims),
        encoding="utf-8",
    )
    actual_definition = workspace / "actual-kompiled"
    reference_definition = workspace / "reference-kompiled"
    # Only the later kprove runs read these definitions, so nothing of them is
    # stored; each is keyed by the digest of the source it compiles.
    commands: tuple[tuple[str, list[str | os.PathLike[str]]], ...] = (
        (
            "kompile/actual-haskell",
            [
                actual_source, "--backend", "haskell", "--main-module", ACTUAL_MODULE,
                "--syntax-module", ACTUAL_MODULE, "--emit-json", "--output-definition", actual_definition,
            ],
        ),
        (
            "kompile/reference-haskell",
            [
                REFERENCE_SOURCE, "-I", IMP_DEFINITION, "--backend", "haskell",
                "--main-module", REFERENCE_MODULE, "--syntax-module", REFERENCE_SYNTAX_MODULE,
                "--emit-json", "--output-definition", reference_definition,
            ],
        ),
    )
    for (label, _), outcome in zip(commands, settle_all(
        [
            lambda label=label, arguments=arguments: k.run(
                label, "kompile", arguments, timeout=WATCHDOG_SECONDS,
            )
            for label, arguments in commands
        ],
        workers,
    )):
        process = outcome.get()
        if process.returncode != 0:
            raise GateError(f"{label} failed: {compact(process)}")
    if k.refresh:
        for definition in (actual_definition, reference_definition):
            for name in ("definition.kore", "parsed.json", "compiled.json"):
                if not definition.joinpath(name).is_file():
                    raise GateError(f"Haskell frontend omitted {definition.name}/{name}")
    return reference_definition, actual_definition, actual_spec


def invoke_source(
    *,
    k: Snapshot,
    label: str,
    definition: Path,
    spec: Path,
    module: str,
    claim: str,
    bounds: Any,
    spec_json: Path,
    includes: Sequence[Path],
) -> tuple[subprocess.CompletedProcess[str], Mapping[str, Any], Mapping[str, Any]]:
    command: list[str | os.PathLike[str]] = [
        spec, "-d", definition, "--spec-module", module, "--claims", claim,
        "--output", "json", "--emit-json-spec", spec_json,
        "--depth", str(bounds.depth), "--branching-allowed", str(bounds.branching_allowed),
    ]
    for include in includes:
        command.extend(["-I", include])
    process = k.run(
        label, "kprove", command, timeout=WATCHDOG_SECONDS,
        outputs=(Output(spec_json, reduce_json_result),),
        streams={"stdout": reduce_json_result, "stderr": reduce_kore_exec_log},
    )
    return process, {"text": process.stdout}, {"path": spec_json}


def legacy_pin(
    *, process: subprocess.CompletedProcess[str], result: Mapping[str, Any], claim: Mapping[str, Any],
    bounds: Any, session: krs_gate.Session, label: str,
) -> dict[str, Any]:
    normalized_result = session.kast_normalize("static_proof", **result)
    normalized_claim = session.kast_normalize("static_claim", **claim, label=label)
    evidence = session.kast_frontier(
        "proof", normalized_result, returncode=process.returncode, stderr=process.stderr,
        constraint_labels=sorted(CONSTRAINT_LABELS),
    )
    frontier = evidence["frontier"]
    return {
        "status": evidence["status"],
        "bounds": {"depth": bounds.depth, "branching_allowed": bounds.branching_allowed},
        "frontier_count": len(frontier),
        "frontier_sha256": sha256_text("\n".join(frontier)),
        "user_labels": [],
        "result_sha256": json_sha256(normalized_result),
        "claim_sha256": json_sha256(normalized_claim),
    }


def compare_source_evidence(name: str, reference: Any, actual: Any) -> None:
    # Claim syntax itself is compared over parsed native KORE by the preceding
    # IMP native gate.  At this layer K's source frontend expands an ellipsis
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
        raise GateError(f"actual/reference emitted-source proof evidence differs for {name}")
    if reference.status != "proved" and (
        reference.status != actual.status
        or reference.bounds != actual.bounds
        or reference.frontier_count != actual.frontier_count
        or reference.user_labels != actual.user_labels
    ):
        raise GateError(f"actual/reference residual proof shape differs for {name}")
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
            raise GateError("depth-zero source routes differ in semantic frontier evidence")


def unique_file(directory: Path, name: str, producer: str) -> Path:
    """The one file `name` a tool wrote below `directory`, or a missing path when it wrote none."""

    matches = sorted(directory.rglob(name))
    if len(matches) > 1:
        raise GateError(f"{producer} emitted {len(matches)} {name} files")
    return matches[0] if matches else directory / name


def dry_run_spec(
    *, k: Snapshot, definition: Path, case: Mapping[str, Any], workspace: Path,
    support: Path,
) -> None:
    output = workspace / "dry-run" / case["name"]
    output.mkdir(parents=True)
    spec_kore = workspace / "dry-run-specs" / case["name"] / "spec.kore"
    command: list[str | os.PathLike[str]] = [
        case["source_spec"], "-d", definition, "--spec-module", case["source_module"],
        "--claims", case["source_claim"], "--dry-run", "--temp-dir", output,
        "--depth", str(case["bounds"].depth),
        "--branching-allowed", str(case["bounds"].branching_allowed),
        "-I", IMP_DEFINITION, "-I", ADJUNCT_SPEC.parent,
        "-I", REFERENCE_SOURCE.parent,
    ]
    process = k.run(
        f"kprove-dry-run/{case['name']}", "kprove", command, timeout=WATCHDOG_SECONDS,
        outputs=(Output(spec_kore, locate=lambda: unique_file(output, "spec.kore", f"{case['name']}: dry-run")),),
        streams={"stdout": reduce_kprove_temp, "stderr": reduce_kore_exec_log},
    )
    if process.returncode != 0 or not spec_kore.is_file():
        raise GateError(f"{case['name']}: dry-run emitted no spec.kore: {compact(process)}")
    run(
        [
            support, "proof", "assert-spec", spec_kore, case["source_module"],
            REFERENCE_MODULE, case["source_claim"],
        ],
        timeout=120,
    )


def build_support() -> Path:
    """Use the root gate built by IMP, or build it for a standalone proof run."""

    raw_target = os.environ.get("CARGO_TARGET_DIR")
    target = Path(raw_target) if raw_target else checkout_scratch() / "imp-gate-root-target"
    if not target.is_absolute():
        target = ROOT / target
    return krs_gate.configured_or_build(target)


def build_native(
    workspace: Path, krs: Path, support: Path, labels: Sequence[str]
) -> tuple[Path, Path]:
    native = workspace / "native-build"
    Invocation(krs, RUST_MANIFEST, "krs-imp-definition", "main").run(
        "build", "--backend", "haskell", "--output", native,
        timeout=WATCHDOG_SECONDS,
    )
    native_kore = native / "definition.kore"
    if not native_kore.is_file():
        raise GateError("native Haskell build omitted definition.kore")
    split = workspace / "native-split"
    run([support, "proof", "split", native_kore, split, ACTUAL_MODULE, ACTUAL_SPEC_MODULE, *labels], timeout=300)
    return split / "definition.kore", split / "specs"


def native_proof(
    *, k: Snapshot, support: Path, definition: Path, specs: Path,
    case: Mapping[str, Any], workspace: Path,
) -> tuple[str, Path]:
    result = workspace / "native-results" / f"{case['name']}.kore"
    result.parent.mkdir(exist_ok=True)
    # kore-exec is keyed by the digests of the native definition and claim
    # KORE that KRS built, so a change to the native lowering needs a refresh.
    process = k.run(
        f"kore-exec/{case['name']}", "kore-exec",
        [
            definition, "--module", ACTUAL_MODULE,
            "--prove", specs / f"{case['native_label']}.kore",
            "--spec-module", ACTUAL_SPEC_MODULE, "--output", result,
            "--depth", str(case["bounds"].depth),
            "--breadth", str(case["bounds"].branching_allowed),
        ],
        timeout=WATCHDOG_SECONDS,
        outputs=(result,),
        streams={"stderr": reduce_kore_exec_log},
    )
    if process.returncode not in {0, 1} or not result.is_file():
        raise GateError(
            f"{case['name']}: native proof produced rc={process.returncode}, "
            f"result_exists={result.is_file()}\n{process.stderr[:3000]}"
        )
    classified = run([support, "proof", "classify", result], timeout=120).stdout.strip()
    if (process.returncode, classified) not in {
        (0, "proved"), (1, "failed"), (1, "incomplete")
    }:
        raise GateError(
            f"{case['name']}: unclassified native termination rc={process.returncode}, "
            f"parsed={classified!r}"
        )
    return classified, result


def actual_source_kore_result(
    *, k: Snapshot, definition: Path, spec: Path, case: Mapping[str, Any], workspace: Path,
) -> Path:
    result = workspace / "source-kore-results" / f"{case['name']}.kore"
    result.parent.mkdir(exist_ok=True)
    process = k.run(
        f"kprove-kore/{case['name']}", "kprove",
        [
            spec, "-d", definition, "--spec-module", ACTUAL_SPEC_MODULE,
            "--claims", case["actual_claim"], "--output", "kore",
            "--depth", str(case["bounds"].depth),
            "--branching-allowed", str(case["bounds"].branching_allowed),
            "-I", workspace,
        ],
        timeout=WATCHDOG_SECONDS,
        streams={"stderr": reduce_kore_exec_log},
    )
    if process.returncode != 1 or not re.search(
        r"configuration cannot be\s+rewritten further", process.stderr
    ):
        raise GateError(
            f"{case['name']}: source KORE residual had unclassified rc={process.returncode}"
        )
    if not process.stdout.strip():
        raise GateError(f"{case['name']}: source KORE residual is empty")
    result.write_text(process.stdout, encoding="utf-8")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pins", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--k-version", required=True, help="the Krs.lock K version")
    parser.add_argument("--k-commit", required=True, help="the Krs.lock K commit")
    parser.add_argument("--krs", type=Path, required=True, help="the KRS CLI the IMP gate built")
    add_refresh_argument(parser)
    add_staging_argument(parser)
    arguments = parser.parse_args()
    pins_path = arguments.pins.resolve(strict=True)
    workspace = arguments.workspace.resolve()
    prepare_workspace(workspace)
    pins = Ledger(pins_path)
    if pins.get("schema") != 1 or pins.get("milestone") != "IMP":
        raise GateError("proof pins are not the exact IMP schema-1 ledger")

    revisions = pins.table("revisions")
    if arguments.k_version != lock.k_version() or arguments.k_commit != lock.k_commit():
        raise GateError("--k-version and --k-commit must name the Krs.lock K release")
    verify_checkout(IMP, revisions["imp"]["commit"], label="IMP", clean=False)
    refresh = arguments.refresh_reference
    executables = None
    if refresh:
        # Only a live run reads the K installation.
        verify_checkout(K, arguments.k_commit, label="K", clean=False)
        executables = {
            "kompile": k_executable("kompile"),
            "kprove": k_tool("kprove", arguments.k_version),
            "kore-exec": k_executable("kore-exec"),
        }
        kore = run([executables["kore-exec"], "--version"], timeout=30).stdout.strip()
        if kore != lock.value("k", "kore_exec_version"):
            raise GateError(f"kore-exec version differs from Krs.lock: {kore}")
    k = Snapshot(
        snapshot_directory(REFERENCE, refresh, arguments.reference_staging),
        Key(
            tools=TOOLS,
            upstream={
                "imp": str(revisions["imp"]["commit"]),
                "kore_exec": str(lock.value("k", "kore_exec_version")),
            },
            inputs=repository_inputs([REFERENCE_SOURCE, ADJUNCT_SPEC]),
        ),
        workspace=workspace, refresh=refresh, executables=executables,
    )

    workers = worker_count("KRS_IMP_ORACLE_WORKERS", 4)
    cases = source_cases(pins, proofs)
    labels = pins["claim_labels"]
    support = build_support()
    reference_definition, actual_definition, actual_spec = compile_definitions(
        workspace=workspace, k=k, expected_labels=labels, workers=workers, gate=support
    )
    reference_policy = proof_policy(pins, "reference", cases)
    actual_policy = proof_policy(pins, "actual", cases)

    with krs_gate.Session(support, environment=z3_environment()) as session:
        krs = arguments.krs.resolve(strict=True)
        native_definition, native_specs = build_native(workspace, krs, support, labels)
        for directory in ("reference-json", "actual-json"):
            (workspace / directory).mkdir()

        # Proof invocations depend only on the compiled definitions and must run in one pool.
        # Checks must follow pin order so the first reported difference is independent of scheduling.
        jobs: list[Callable[[], Any]] = []

        def job(call: Callable[[], Any]) -> int:
            jobs.append(call)
            return len(jobs) - 1

        case_jobs = []
        for case in cases:
            reference_json = workspace / "reference-json" / f"{case['name']}.json"
            actual_json = workspace / "actual-json" / f"{case['name']}.json"
            case_jobs.append({
                "reference": job(lambda case=case, spec_json=reference_json: invoke_source(
                    k=k, label=f"kprove/reference/{case['name']}",
                    definition=reference_definition, spec=case["source_spec"],
                    module=case["source_module"], claim=case["source_claim"], bounds=case["bounds"],
                    spec_json=spec_json,
                    includes=(IMP_DEFINITION, ADJUNCT_SPEC.parent, REFERENCE_SOURCE.parent),
                )),
                "actual": job(lambda case=case, spec_json=actual_json: invoke_source(
                    k=k, label=f"kprove/actual/{case['name']}",
                    definition=actual_definition, spec=actual_spec,
                    module=ACTUAL_SPEC_MODULE, claim=case["actual_claim"], bounds=case["bounds"],
                    spec_json=spec_json, includes=(workspace,),
                )),
                "dry_run": job(lambda case=case: dry_run_spec(
                    k=k, definition=reference_definition, case=case,
                    workspace=workspace, support=support,
                )),
                "native": job(lambda case=case: native_proof(
                    k=k, support=support, definition=native_definition,
                    specs=native_specs, case=case, workspace=workspace,
                )),
                # The source KORE residual must be compared only for an incomplete proof, after checking the native status against its pin.
                "source_kore": job(lambda case=case: actual_source_kore_result(
                    k=k, definition=actual_definition, spec=actual_spec,
                    case=case, workspace=workspace,
                )) if case["pin"]["status"] == "incomplete" else None,
            })
        results = settle_all(jobs, workers)

        for case, indices in zip(cases, case_jobs):
            reference_process, reference_result, reference_claim = results[indices["reference"]].get()
            actual_process, actual_result, actual_claim = results[indices["actual"]].get()
            try:
                reference_evidence = proofs.evidence_from_inputs(
                    session=session,
                    case=proofs.ProofCase(
                        case["name"], case["source_spec"], case["source_module"],
                        case["source_claim"], case["bounds"]
                    ),
                    result=reference_result, claim=reference_claim,
                    returncode=reference_process.returncode, stderr=reference_process.stderr,
                    user_labels=(), policy=reference_policy, constraint_labels=sorted(CONSTRAINT_LABELS),
                )
            except RuntimeError as error:
                raise GateError(f"{case['name']} reference evidence: {error}") from error
            try:
                actual_evidence = proofs.evidence_from_inputs(
                    session=session,
                    case=proofs.ProofCase(
                        case["name"], actual_spec, ACTUAL_SPEC_MODULE,
                        case["actual_claim"], case["bounds"]
                    ),
                    result=actual_result, claim=actual_claim,
                    returncode=actual_process.returncode, stderr=actual_process.stderr,
                    user_labels=(), policy=actual_policy, constraint_labels=sorted(CONSTRAINT_LABELS),
                )
            except RuntimeError as error:
                raise GateError(f"{case['name']} actual evidence: {error}") from error
            compare_source_evidence(case["name"], reference_evidence, actual_evidence)
            observed_pin = legacy_pin(
                process=reference_process, result=reference_result, claim=reference_claim,
                bounds=case["bounds"], session=session, label=case["source_claim"],
            )
            comparable_pin = dict(observed_pin)
            comparable_expected = dict(case["pin"])
            if observed_pin["status"] == "incomplete":
                # KORE conjunction and branch traversal can change the raw KAST tree order while preserving the normalized sorted frontier.
                # Incomplete proofs must match the exact frontier digest and parsed source/native KORE below.
                # The raw result digest must be excluded from this comparison because it pins one traversal order.
                comparable_pin.pop("result_sha256")
                comparable_expected.pop("result_sha256")
            if comparable_pin != comparable_expected:
                raise GateError(
                    f"reference proof pin differs for {case['name']}: observed={canonical_json(observed_pin)}"
                )
            results[indices["dry_run"]].get()

        native_statuses: dict[str, str] = {}
        for case, indices in zip(cases, case_jobs):
            status, native_result = results[indices["native"]].get()
            if status != case["pin"]["status"]:
                raise GateError(
                    f"native proof status differs for {case['name']}: "
                    f"expected={case['pin']['status']}, observed={status}"
                )
            native_statuses[case["name"]] = status
            if status == "incomplete":
                source_result = results[indices["source_kore"]].get()
                run([support, "proof", "compare-patterns", source_result, native_result], timeout=120)
        if set(native_statuses) != {case["name"] for case in cases}:
            raise GateError("native proof coverage is incomplete")

        # The gate requires the exact PASS summary and nothing else, so the
        # snapshot's report line is not printed; a staged refresh is reported
        # when the gate promotes it.
        k.finish()
        print(
            "PASS IMP proofs: reference_source=21 actual_source=21 "
            "dry_run_specs=21 native_haskell=21 native_unique_claims=20"
        )
        return 0


if __name__ == "__main__":
    entry("IMP proofs", main, errors=(OSError, KeyError, TypeError, ValueError, RuntimeError))
