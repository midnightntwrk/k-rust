#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KWasm integer slice."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from support.checkouts import verify_checkout  # noqa: E402
from support.hashing import canonical_json, exact_directory, json_sha256, sha256_file, sha256_text  # noqa: E402
from support.kdefinition import EMITTED_ARTIFACTS, normalized_kore_sha256, split_claims  # noqa: E402
from support.pins import load_toml, table  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool, rust_analyzer, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = ROOT / "semantics/kwasm/Cargo.toml"
SOURCE = ROOT / "semantics/kwasm/src/lib.rs"
LOCK = ROOT / "semantics/Cargo.lock"
CORPUS_PATH = HERE / "corpus.toml"
PINS_PATH = HERE / "pins.toml"
KWASM = ROOT.parent / "inspirations/runtimeverification/wasm-semantics"
PACKAGE = "krs-kwasm-semantics"
DEFINITION = "main"
MODULE = "KRS-KWASM"
SPEC_MODULE = f"{MODULE}-SPEC"
SOURCE_LEDGER_PATHS = (
    "crates/krs-compiler/src/collect.rs",
    "crates/krs-compiler/src/emit.rs",
    "crates/krs-compiler/src/lowering.rs",
    "crates/krs-compiler/src/overlap.rs",
    "crates/krs-compiler/src/reference.rs",
    "crates/krs-compiler/src/semantic.rs",
    "crates/krs-compiler/src/sidecar.rs",
    "crates/krs-ir/src/definition.rs",
    "crates/krs-ir/src/grammar.rs",
    "crates/krs-ir/src/head_rule.rs",
    "crates/krs-ir/src/ir.rs",
    "crates/krs-ir/src/lib.rs",
    "crates/krs-ir/src/protocol_v6.rs",
    "crates/krs-ir/src/protocol_v7_rule.rs",
    "crates/krs-ir/src/semantic.rs",
    "crates/krs-ir/src/state.rs",
    "crates/krs-k-rust/src/lib.rs",
    "crates/krs-k-rust/src/bin/krs-native-compile.rs",
    "crates/krs-k-rust/src/bin/krs-native-runner.rs",
    "crates/krs-expand/src/environment.rs",
    "crates/krs-expand/src/expand.rs",
    "crates/krs-expand/src/islands.rs",
    "crates/krs-expand/src/lib.rs",
    "crates/krs-expand/src/provenance.rs",
    "crates/krs-macros/src/environment.rs",
    "crates/krs-macros/src/lib.rs",
    "crates/krs-syntax/src/provenance.rs",
    "crates/krs-syntax/src/rule.rs",
    "crates/krs-syntax/src/state_rule.rs",
    "crates/krs-syntax/src/term.rs",
    "crates/krs-syntax/tests/rule_blocks.rs",
    "crates/krs/src/lib.rs",
    "tests/kwasm/source-map.md",
    "tests/kwasm/corpus.toml",
    "tests/kwasm/lsp_probe.py",
    "tests/kwasm/native.py",
    "semantics/Cargo.lock",
    "semantics/Cargo.toml",
    "semantics/README.md",
    "semantics/coverage.toml",
    "semantics/kwasm/Cargo.toml",
    "semantics/kwasm/src/lib.rs",
    "tests/kwasm/verify.py",
)


def preflight(pins: Mapping[str, Any], corpus: Mapping[str, Any]) -> dict[str, str]:
    if pins.get("schema") != 1 or corpus.get("schema") != 1:
        raise GateError("KWasm gate schema differs from 1")
    if sha256_file(CORPUS_PATH) != pins.get("corpus_sha256"):
        raise GateError("corpus.toml differs from its pin")
    kwasm_pin = table(pins.get("kwasm"), "pins.kwasm")
    verify_checkout(KWASM, str(kwasm_pin.get("commit")), label="KWasm evidence")
    version_path = KWASM / "deps/k_release"
    if version_path.read_text(encoding="utf-8").strip() != kwasm_pin.get("version"):
        raise GateError("KWasm K release differs")

    schemas = table(pins.get("schemas"), "pins.schemas")
    protocol = (ROOT / "crates/krs-ir/src/lib.rs").read_text(encoding="utf-8")
    ir = (ROOT / "crates/krs-ir/src/ir.rs").read_text(encoding="utf-8")
    if (
        f"pub const CURRENT: Self = Self({schemas.get('descriptor_protocol')});"
        not in protocol
    ):
        raise GateError("descriptor protocol differs")
    if f"pub const CURRENT: Self = Self({schemas.get('definition_ir')});" not in ir:
        raise GateError("Definition IR schema differs")

    expected_sources = table(pins.get("source_sha256"), "pins.source_sha256")
    if set(expected_sources) != set(SOURCE_LEDGER_PATHS):
        raise GateError("KWasm source-ledger path set differs")
    for relative in SOURCE_LEDGER_PATHS:
        if sha256_file(ROOT / relative) != expected_sources[relative]:
            raise GateError(f"KWasm source ledger differs: {relative}")

    expected_external = table(pins.get("external_sha256"), "pins.external_sha256")
    evidence = corpus.get("source_evidence")
    if not isinstance(evidence, list) or not evidence:
        raise GateError("source evidence is empty")
    evidence_paths = {str(entry["path"]) for entry in evidence}
    if set(expected_external) != evidence_paths:
        raise GateError("external evidence-ledger path set differs")
    for relative in evidence_paths:
        if sha256_file(KWASM / relative) != expected_external[relative]:
            raise GateError(f"external KWasm evidence differs: {relative}")

    return {**z3_environment(), "CARGO_NET_OFFLINE": "true"}


def rust_gate(workspace: Path, environment: Mapping[str, str]) -> tuple[Path, Path, Path]:
    root_target = Path(
        os.environ.get("KRS_KWASM_ROOT_TARGET", "/var/tmp/krs-kwasm-gate-root-target")
    )
    fixture_target = Path(
        os.environ.get("KRS_KWASM_FIXTURE_TARGET", "/var/tmp/krs-kwasm-gate-fixture-target")
    )
    run(
        ["cargo", "build", "--locked", "--offline", "-p", "krs-cli", "--bin", "krs"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(root_target)},
    )
    run(
        ["cargo", "build", "--locked", "--offline", "--release", "-p", "krs-k-rust", "--bins"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(root_target)},
        timeout=900,
    )
    common = ["--manifest-path", MANIFEST, "--locked", "--offline"]
    fixture_env = {**environment, "CARGO_TARGET_DIR": os.fspath(fixture_target)}
    run(["cargo", "check", *common, "--all-targets"], environment=fixture_env)
    run(["cargo", "test", *common], environment=fixture_env, timeout=900)
    run(
        ["cargo", "clippy", *common, "--all-targets", "--", "-D", "warnings"],
        environment=fixture_env,
        timeout=900,
    )
    run(["cargo", "fmt", "--all", "--", "--check"])
    run(
        [
            root_target / "debug/krs",
            "fmt",
            "--check",
            "--manifest-path",
            MANIFEST,
            SOURCE,
        ],
        environment=environment,
    )
    run(
        ["cargo", "+1.88.0", "check", *common, "--all-targets"],
        environment=fixture_env,
        timeout=900,
    )
    analyzer = rust_analyzer()
    lsp_env = {
        **environment,
        "PATH": os.pathsep.join([os.fspath(analyzer.parent), os.environ["PATH"]]),
    }
    run([sys.executable, HERE / "lsp_probe.py"], environment=lsp_env, timeout=240)
    return (
        root_target / "debug/krs",
        root_target / "release/krs-native-compile",
        root_target / "release/krs-native-runner",
    )


def artifact_gate(
    workspace: Path,
    krs: Path,
    pins: Mapping[str, Any],
    environment: Mapping[str, str],
) -> Path:
    base = [
        "--manifest-path",
        MANIFEST,
        "--package",
        PACKAGE,
        "--definition",
        DEFINITION,
    ]
    check = run([krs, "check", *base], environment=environment)
    if "60 descriptors" not in check.stdout:
        raise GateError(f"unexpected descriptor count: {check.stdout.strip()}")
    expansions = [run([krs, "expand", *base], environment=environment).stdout for _ in range(2)]
    if expansions[0] != expansions[1]:
        raise GateError("readable expansion is nondeterministic")
    expansion_hash = sha256_text(expansions[0])
    if expansion_hash != pins.get("expansion_sha256"):
        raise GateError(f"expansion hash differs: {expansion_hash}")

    expanded = workspace / "expanded"
    expanded.joinpath("src").mkdir(parents=True)
    manifest = MANIFEST.read_text(encoding="utf-8")
    for relative, absolute in {
        "../../crates/krs": ROOT / "crates/krs",
        "../../crates/krs-compiler": ROOT / "crates/krs-compiler",
        "../../crates/krs-ir": ROOT / "crates/krs-ir",
        "../../../crates/krs-k-rust": ROOT / "crates/krs-k-rust",
    }.items():
        manifest = manifest.replace(relative, os.fspath(absolute))
    expanded.joinpath("Cargo.toml").write_text(manifest, encoding="utf-8")
    shutil.copy2(LOCK, expanded / "Cargo.lock")
    expanded.joinpath("src/lib.rs").write_text(expansions[0], encoding="utf-8")
    expanded_target = workspace / "expanded-target"
    run(
        ["cargo", "check", "--manifest-path", expanded / "Cargo.toml", "--locked", "--offline"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(expanded_target)},
        timeout=900,
    )

    outputs = [workspace / "emit-a", workspace / "emit-b"]
    for output in outputs:
        run([krs, "emit-k", *base, "--output", output], environment=environment)
    hashes = exact_directory(outputs[0], outputs[1], EMITTED_ARTIFACTS)
    if hashes != dict(table(pins.get("artifact_sha256"), "pins.artifact_sha256")):
        raise GateError(f"emitted artifact hashes differ: {canonical_json(hashes)}")

    expanded_output = workspace / "expanded-emit"
    run(
        [
            krs,
            "emit-k",
            "--manifest-path",
            expanded / "Cargo.toml",
            "--package",
            PACKAGE,
            "--definition",
            DEFINITION,
            "--output",
            expanded_output,
        ],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(expanded_target)},
        timeout=900,
    )
    readable_k = (outputs[0] / "definition.k").read_text(encoding="utf-8")
    expanded_k = (expanded_output / "definition.k").read_text(encoding="utf-8")
    readable_prefix = readable_k.split("\n  rule ", 1)[0]
    expanded_prefix = expanded_k.split("\n  rule ", 1)[0]
    if readable_prefix != expanded_prefix:
        raise GateError("independently compiled expansion changed syntax or configuration")
    sentence_pattern = re.compile(r"^  (rule|claim)(?: \[([^]]+)\])?", re.MULTILINE)
    readable_sentences = sentence_pattern.findall(readable_k)
    expanded_sentences = sentence_pattern.findall(expanded_k)
    if readable_sentences != expanded_sentences:
        raise GateError(
            "independently compiled expansion changed rule or claim identity transport"
        )
    return outputs[0]


def compile_native_definition(
    workspace: Path,
    artifacts: Path,
    compiler: Path,
    pins: Mapping[str, Any],
    environment: Mapping[str, str],
) -> Path:
    definition = workspace / "native-definition.kore"
    run(
        [compiler, artifacts / "definition-ir.json", definition],
        environment=environment,
        timeout=900,
    )
    kore_hash = sha256_file(definition)
    if kore_hash != pins.get("native_definition_kore_sha256"):
        raise GateError(f"native K-Rust definition.kore hash differs: {kore_hash}")
    return definition


def k_rust_gate(
    runner: Path,
    definition: Path,
    pins: Mapping[str, Any],
    corpus: Mapping[str, Any],
    environment: Mapping[str, str],
) -> int:
    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    result = run(
        [sys.executable, HERE / "native.py", runner, definition, MODULE, CORPUS_PATH],
        environment=environment,
        timeout=900,
    )
    expected = f"PASS native KWasm behavior: {len(behavior)} executions; sha256={pins.get('behavior_sha256')}"
    if result.stdout.strip() != expected:
        raise GateError(f"K-Rust behavior evidence differs: {result.stdout.strip()}")
    return len(behavior)


def java_reference_gate(
    workspace: Path,
    artifacts: Path,
    k: Mapping[str, str],
    pins: Mapping[str, Any],
    corpus: Mapping[str, Any],
) -> tuple[int, int]:
    claim_free, _, claims = split_claims(
        (artifacts / "definition.k").read_text(encoding="utf-8"), 1
    )
    semantics = workspace / "semantics.k"
    semantics.write_text(claim_free, encoding="utf-8")
    definition = workspace / "semantics-kompiled"
    run(
        [
            k["kompile"],
            semantics,
            "--backend",
            "haskell",
            "--main-module",
            MODULE,
            "--syntax-module",
            MODULE,
            "--emit-json",
            "--output-definition",
            definition,
        ],
        timeout=900,
    )
    kore_hash = normalized_kore_sha256(definition / "definition.kore", semantics)
    if kore_hash != pins.get("definition_kore_sha256"):
        raise GateError(f"native definition.kore hash differs: {kore_hash}")

    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    outcomes: list[dict[str, str]] = []
    for case in behavior:
        case_id = str(case["id"])
        expected_outcome = str(case.get("expected_outcome", "value"))
        if expected_outcome not in {"trap", "value"}:
            raise GateError(f"{case_id} has an unsupported expected outcome")
        result = run(
            [
                k["krun"],
                "--definition",
                definition,
                f"-cPGM={case['program']}",
                "-cSTACK=.ValStack",
                "--output",
                "pretty",
            ],
            timeout=120,
        ).stdout
        if expected_outcome == "trap":
            if not re.search(
                r"<instrs>\s*trap\s*~>\s*\.Instrs\s*~>\s*\.K\s*</instrs>",
                result,
            ):
                raise GateError(f"{case_id} did not finish with a trap: {result}")
            if not re.search(r"<valstack>\s*\.ValStack\s*</valstack>", result):
                raise GateError(f"{case_id} trapped with an unexpected stack: {result}")
            observed = {"id": case_id, "outcome": "trap"}
            expected = {"id": case_id, "outcome": "trap"}
        else:
            if not re.search(r"<instrs>\s*\.K\s*</instrs>", result):
                raise GateError(
                    f"{case_id} did not finish its instruction stream: {result}"
                )
            match = re.search(
                r"<valstack>\s*<\s*(i32|i64)\s*>\s*(-?[0-9]+)\s*:\s*\.ValStack\s*</valstack>",
                result,
            )
            if match is None:
                raise GateError(f"{case_id} has an unexpected value stack: {result}")
            observed = {
                "id": case_id,
                "outcome": "value",
                "type": match.group(1),
                "value": match.group(2),
            }
            expected = {
                "id": case_id,
                "outcome": "value",
                "type": str(case["expected_type"]),
                "value": str(case["expected_value"]),
            }
        if observed != expected:
            raise GateError(f"{case_id} differs: expected={expected}, actual={observed}")
        outcomes.append(observed)
    behavior_hash = json_sha256(outcomes)
    if behavior_hash != pins.get("behavior_sha256"):
        raise GateError(f"behavior hash differs: {behavior_hash}")

    spec = workspace / "spec.k"
    spec.write_text(
        f'requires "{semantics.name}"\n\nmodule {SPEC_MODULE}\n'
        f"  imports {MODULE}\n\n{claims}endmodule\n",
        encoding="utf-8",
    )
    dry = run(
        [
            k["kprove"],
            spec,
            "--definition",
            definition,
            "--spec-module",
            SPEC_MODULE,
            "--dry-run",
        ],
        timeout=180,
    )
    if "kore-exec" not in dry.stdout or "--prove" not in dry.stdout:
        raise GateError("proof dry run did not select the native Haskell prover")
    proof = run(
        [
            k["kprove"],
            spec,
            "--definition",
            definition,
            "--spec-module",
            SPEC_MODULE,
        ],
        timeout=300,
    )
    if proof.stdout.strip() != "#Top":
        raise GateError(f"KWasm claim did not close: {proof.stdout.strip()}")
    return len(outcomes), 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--show-observed", action="store_true")
    parser.add_argument(
        "--java-reference",
        action="store_true",
        help="run the deferred K toolchain behavior comparison and proof",
    )
    arguments = parser.parse_args()
    pins = load_toml(PINS_PATH)
    corpus = load_toml(CORPUS_PATH)
    environment = preflight(pins, corpus)
    with tempfile.TemporaryDirectory(prefix="krs-kwasm-gate-", dir="/var/tmp") as temporary:
        workspace = Path(temporary)
        krs, compiler, runner = rust_gate(workspace, environment)
        artifacts = artifact_gate(workspace, krs, pins, environment)
        definition = compile_native_definition(
            workspace, artifacts, compiler, pins, environment
        )
        behavior_count = k_rust_gate(runner, definition, pins, corpus, environment)
        proof_count = 0
        if arguments.java_reference:
            k_version = str(table(pins.get("k"), "pins.k")["version"])
            k = {name: k_tool(name, k_version) for name in ("kompile", "krun", "kprove")}
            reference_behavior, proof_count = java_reference_gate(
                workspace, artifacts, k, pins, corpus
            )
            if reference_behavior != behavior_count:
                raise GateError("K-Rust and reference execution counts differ")
    if arguments.show_observed:
        print("all observed values matched their pins")
    proof_status = (
        f"{proof_count} reference proof" if arguments.java_reference else "1 reference proof deferred to --java-reference"
    )
    print(
        "PASS readable KWasm integer slice: "
        f"60 descriptors; {behavior_count} K-Rust executions; {proof_status}; "
        f"protocol {pins['schemas']['descriptor_protocol']}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (GateError, OSError) as error:
        print(f"FAIL readable KWasm integer slice: {error}", file=sys.stderr)
        raise SystemExit(1)
