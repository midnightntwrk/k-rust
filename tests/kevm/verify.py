#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KEVM operational slice."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from typing import Any, Mapping


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = HERE / "rust-definition/Cargo.toml"
SOURCE = HERE / "rust-definition/src/lib.rs"
LOCK = HERE / "rust-definition/Cargo.lock"
CORPUS_PATH = HERE / "corpus.toml"
PINS_PATH = HERE / "pins.toml"
KEVM = ROOT.parent / "inspirations/runtimeverification/evm-semantics"
PACKAGE = "krs-kevm-operational-slice"
DEFINITION = "main"
MODULE = "KRS-KEVM-OPERATIONAL-SLICE"
SPEC_MODULE = f"{MODULE}-SPEC"
ARTIFACTS = (
    ".krs-artifacts",
    "definition-ir.json",
    "definition.k",
    "descriptor-bundle.json",
    "semantic-ir.json",
    "sources.json",
    "symbols.json",
)
SOURCE_LEDGER_PATHS = (
    "crates/krs-compiler/src/collect.rs",
    "crates/krs-compiler/src/reference.rs",
    "crates/krs-compiler/src/semantic.rs",
    "crates/krs-ir/src/head_rule.rs",
    "crates/krs-ir/src/lib.rs",
    "crates/krs-macros/src/expand.rs",
    "crates/krs-syntax/src/rule.rs",
    "draft/readability/kevm/README.md",
    "tests/kevm/corpus.toml",
    "tests/kevm/lsp_probe.py",
    "tests/kevm/rust-definition/Cargo.lock",
    "tests/kevm/rust-definition/Cargo.toml",
    "tests/kevm/rust-definition/src/lib.rs",
    "tests/kevm/verify.py",
)

spec = importlib.util.spec_from_file_location("kwasm_gate_support", ROOT / "tests/kwasm/verify.py")
assert spec is not None and spec.loader is not None
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
GateError = support.GateError


def sha256(path: Path) -> str:
    return support.sha256(path)


def mapping(value: Any, name: str) -> Mapping[str, Any]:
    return support.mapping(value, name)


def run(*args: Any, **kwargs: Any) -> subprocess.CompletedProcess[str]:
    return support.run(*args, **kwargs)


def preflight(pins: Mapping[str, Any], corpus: Mapping[str, Any]) -> tuple[Path, dict[str, str]]:
    if pins.get("schema") != 1 or corpus.get("schema") != 1:
        raise GateError("KEVM gate schema differs from 1")
    if sha256(CORPUS_PATH) != pins.get("corpus_sha256"):
        raise GateError("corpus.toml differs from its pin")
    k_pin = mapping(pins.get("k"), "pins.k")
    kevm_pin = mapping(pins.get("kevm"), "pins.kevm")
    if support.git_revision(KEVM) != kevm_pin.get("commit"):
        raise GateError("KEVM checkout revision differs")
    if run(["git", "status", "--porcelain"], cwd=KEVM, timeout=30).stdout:
        raise GateError("KEVM evidence checkout is dirty")
    if (KEVM / "deps/k_release").read_text(encoding="utf-8").strip() != kevm_pin.get("version"):
        raise GateError("KEVM K release differs")

    schemas = mapping(pins.get("schemas"), "pins.schemas")
    protocol = (ROOT / "crates/krs-ir/src/lib.rs").read_text(encoding="utf-8")
    ir = (ROOT / "crates/krs-ir/src/ir.rs").read_text(encoding="utf-8")
    if f"pub const CURRENT: Self = Self({schemas.get('descriptor_protocol')});" not in protocol:
        raise GateError("descriptor protocol differs")
    if f"pub const CURRENT: Self = Self({schemas.get('definition_ir')});" not in ir:
        raise GateError("Definition IR schema differs")

    expected_sources = mapping(pins.get("source_sha256"), "pins.source_sha256")
    if set(expected_sources) != set(SOURCE_LEDGER_PATHS):
        raise GateError("KEVM source-ledger path set differs")
    for relative in SOURCE_LEDGER_PATHS:
        if sha256(ROOT / relative) != expected_sources[relative]:
            raise GateError(f"KEVM source ledger differs: {relative}")

    expected_external = mapping(pins.get("external_sha256"), "pins.external_sha256")
    evidence = corpus.get("source_evidence")
    if not isinstance(evidence, list) or not evidence:
        raise GateError("source evidence is empty")
    evidence_paths = {str(entry["path"]) for entry in evidence}
    if set(expected_external) != evidence_paths:
        raise GateError("external evidence-ledger path set differs")
    for relative in evidence_paths:
        if sha256(KEVM / relative) != expected_external[relative]:
            raise GateError(f"external KEVM evidence differs: {relative}")

    k_bin = support.find_k_bin(str(k_pin["version"]), str(k_pin["commit"]))
    observed = run([k_bin / "kompile", "--version"], timeout=30)
    if f"v{k_pin['version']}" not in observed.stdout + observed.stderr:
        raise GateError("K executable version differs")
    z3 = support.find_z3_lib()
    environment = {
        "LIBRARY_PATH": os.pathsep.join([os.fspath(z3), os.environ.get("LIBRARY_PATH", "")]).rstrip(os.pathsep),
        "LD_LIBRARY_PATH": os.pathsep.join([os.fspath(z3), os.environ.get("LD_LIBRARY_PATH", "")]).rstrip(os.pathsep),
        "CARGO_NET_OFFLINE": "true",
    }
    return k_bin, environment


def rust_gate(environment: Mapping[str, str]) -> Path:
    root_target = Path(os.environ.get("KRS_KEVM_ROOT_TARGET", "/var/tmp/krs-kevm-gate-root-target"))
    fixture_target = Path(os.environ.get("KRS_KEVM_FIXTURE_TARGET", "/var/tmp/krs-kevm-gate-fixture-target"))
    run(
        ["cargo", "build", "--locked", "--offline", "-p", "krs-cli", "--bin", "krs"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(root_target)},
    )
    common = ["--manifest-path", MANIFEST, "--locked", "--offline"]
    fixture_env = {**environment, "CARGO_TARGET_DIR": os.fspath(fixture_target)}
    run(["cargo", "check", *common, "--all-targets"], environment=fixture_env)
    run(["cargo", "test", *common], environment=fixture_env, timeout=900)
    run(["cargo", "clippy", *common, "--all-targets", "--", "-D", "warnings"], environment=fixture_env, timeout=900)
    run(["cargo", "fmt", "--all", "--", "--check"])
    run([root_target / "debug/krs", "fmt", "--check", "--manifest-path", MANIFEST, SOURCE], environment=environment)
    run(["cargo", "+1.88.0", "check", *common, "--all-targets"], environment=fixture_env, timeout=900)
    analyzer = support.find_rust_analyzer()
    lsp_env = {**environment, "PATH": os.pathsep.join([os.fspath(analyzer.parent), os.environ["PATH"]])}
    run([sys.executable, HERE / "lsp_probe.py"], environment=lsp_env, timeout=240)
    return root_target / "debug/krs"


def exact_directory(first: Path, second: Path) -> dict[str, str]:
    names_a = sorted(path.name for path in first.iterdir() if path.is_file())
    names_b = sorted(path.name for path in second.iterdir() if path.is_file())
    if names_a != list(ARTIFACTS) or names_b != list(ARTIFACTS):
        raise GateError(f"artifact set differs: first={names_a}, second={names_b}")
    hashes = {name: sha256(first / name) for name in ARTIFACTS}
    for name, digest in hashes.items():
        if sha256(second / name) != digest:
            raise GateError(f"repeated emission differs: {name}")
    return hashes


def artifact_gate(workspace: Path, krs: Path, pins: Mapping[str, Any], environment: Mapping[str, str]) -> Path:
    base = ["--manifest-path", MANIFEST, "--package", PACKAGE, "--definition", DEFINITION]
    check = run([krs, "check", *base], environment=environment)
    if "69 descriptors" not in check.stdout:
        raise GateError(f"unexpected descriptor count: {check.stdout.strip()}")
    expansions = [run([krs, "expand", *base], environment=environment).stdout for _ in range(2)]
    if expansions[0] != expansions[1]:
        raise GateError("readable expansion is nondeterministic")
    digest = hashlib.sha256(expansions[0].encode()).hexdigest()
    if digest != pins.get("expansion_sha256"):
        raise GateError(f"expansion hash differs: {digest}")

    expanded = workspace / "expanded"
    expanded.joinpath("src").mkdir(parents=True)
    manifest = MANIFEST.read_text(encoding="utf-8")
    for relative, absolute in {
        "../../../crates/krs": ROOT / "crates/krs",
        "../../../crates/krs-compiler": ROOT / "crates/krs-compiler",
        "../../../crates/krs-ir": ROOT / "crates/krs-ir",
    }.items():
        manifest = manifest.replace(relative, os.fspath(absolute))
    expanded.joinpath("Cargo.toml").write_text(manifest, encoding="utf-8")
    shutil.copy2(LOCK, expanded / "Cargo.lock")
    expanded.joinpath("src/lib.rs").write_text(expansions[0], encoding="utf-8")
    expanded_target = workspace / "expanded-target"
    run(["cargo", "check", "--manifest-path", expanded / "Cargo.toml", "--locked", "--offline"], environment={**environment, "CARGO_TARGET_DIR": os.fspath(expanded_target)}, timeout=900)

    outputs = [workspace / "emit-a", workspace / "emit-b"]
    for output in outputs:
        run([krs, "emit-k", *base, "--output", output], environment=environment)
    hashes = exact_directory(outputs[0], outputs[1])
    if hashes != dict(mapping(pins.get("artifact_sha256"), "pins.artifact_sha256")):
        raise GateError(f"emitted artifact hashes differ: {support.canonical(hashes)}")

    expanded_output = workspace / "expanded-emit"
    run(
        [krs, "emit-k", "--manifest-path", expanded / "Cargo.toml", "--package", PACKAGE, "--definition", DEFINITION, "--output", expanded_output],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(expanded_target)},
        timeout=900,
    )
    readable = (outputs[0] / "definition.k").read_text(encoding="utf-8")
    expanded_k = (expanded_output / "definition.k").read_text(encoding="utf-8")
    sentence = re.compile(r"^  (rule|claim)(?: \[([^]]+)\])?", re.MULTILINE)
    if readable.split("\n  rule ", 1)[0] != expanded_k.split("\n  rule ", 1)[0]:
        raise GateError("independent expansion changed syntax or configuration")
    if sentence.findall(readable) != sentence.findall(expanded_k):
        raise GateError("independent expansion changed rule or claim identities")
    return outputs[0]


def normalize_term(value: str) -> str:
    value = re.sub(r"\s+", " ", value.strip())
    value = re.sub(r"\s*([(),;:])\s*", r"\1", value)
    value = re.sub(r"\.\s+", ".", value)
    return value


def observed_cell(result: str, name: str) -> str:
    match = re.search(rf"<{name}>\s*(.*?)\s*</{name}>", result, re.DOTALL)
    if match is None:
        raise GateError(f"native output omitted <{name}>: {result}")
    return normalize_term(match.group(1))


def native_gate(workspace: Path, artifacts: Path, k_bin: Path, pins: Mapping[str, Any], corpus: Mapping[str, Any]) -> tuple[int, int]:
    claim_free, claims = support.split_claims((artifacts / "definition.k").read_text(encoding="utf-8"))
    semantics = workspace / "semantics.k"
    semantics.write_text(claim_free, encoding="utf-8")
    definition = workspace / "semantics-kompiled"
    run([k_bin / "kompile", semantics, "--backend", "haskell", "--main-module", MODULE, "--syntax-module", MODULE, "--emit-json", "--output-definition", definition], timeout=900)
    kore_hash = support.normalized_kore_sha256(definition / "definition.kore", semantics)
    if kore_hash != pins.get("definition_kore_sha256"):
        raise GateError(f"native definition.kore hash differs: {kore_hash}")

    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    outcomes: list[dict[str, str]] = []
    for case in behavior:
        result = run(
            [
                k_bin / "krun", "--definition", definition,
                "-cPGM=run", f"-cPROGRAM={case['program']}", f"-cSTACK={case['stack']}",
                f"-cPC={case['pc']}", f"-cGAS={case['gas']}", "-cSTATUS=.StatusCode",
                "--output", "pretty",
            ],
            timeout=120,
        ).stdout
        if observed_cell(result, "k") != ".K":
            raise GateError(f"{case['id']} did not halt: {result}")
        observed = {
            "id": str(case["id"]),
            "program": observed_cell(result, "program"),
            "stack": observed_cell(result, "wordStack"),
            "pc": observed_cell(result, "pc"),
            "gas": observed_cell(result, "gas"),
            "status": observed_cell(result, "statusCode"),
        }
        expected = {
            "id": str(case["id"]),
            "program": normalize_term(str(case["expected_program"])),
            "stack": normalize_term(str(case["expected_stack"])),
            "pc": str(case["expected_pc"]),
            "gas": str(case["expected_gas"]),
            "status": str(case["expected_status"]),
        }
        if observed != expected:
            raise GateError(f"{case['id']} differs: expected={expected}, actual={observed}")
        outcomes.append(observed)
    behavior_hash = hashlib.sha256(support.canonical(outcomes).encode()).hexdigest()
    if behavior_hash != pins.get("behavior_sha256"):
        raise GateError(f"behavior hash differs: {behavior_hash}; outcomes={support.canonical(outcomes)}")

    spec_path = workspace / "spec.k"
    spec_path.write_text(
        f'requires "{semantics.name}"\n\nmodule {SPEC_MODULE}\n  imports {MODULE}\n\n{"".join(claims)}endmodule\n',
        encoding="utf-8",
    )
    dry = run([k_bin / "kprove", spec_path, "--definition", definition, "--spec-module", SPEC_MODULE, "--dry-run"], timeout=180)
    if "kore-exec" not in dry.stdout or "--prove" not in dry.stdout:
        raise GateError("proof dry run did not select the native Haskell prover")
    proof = run([k_bin / "kprove", spec_path, "--definition", definition, "--spec-module", SPEC_MODULE], timeout=300)
    if proof.stdout.strip() != "#Top":
        raise GateError(f"KEVM claim did not close: {proof.stdout.strip()}")
    return len(outcomes), 1


def main() -> int:
    try:
        with PINS_PATH.open("rb") as stream:
            pins = tomllib.load(stream)
        with CORPUS_PATH.open("rb") as stream:
            corpus = tomllib.load(stream)
        k_bin, environment = preflight(pins, corpus)
        krs = rust_gate(environment)
        with tempfile.TemporaryDirectory(prefix="krs-kevm-", dir="/var/tmp") as temporary:
            workspace = Path(temporary)
            artifacts = artifact_gate(workspace, krs, pins, environment)
            executions, proofs = native_gate(workspace, artifacts, k_bin, pins, corpus)
        print(
            f"PASS readable KEVM operational slice: 69 descriptors; {executions} executions; "
            f"{proofs} native proof; protocol {pins['schemas']['descriptor_protocol']}; K {pins['k']['version']}"
        )
        return 0
    except (GateError, OSError, subprocess.TimeoutExpired, AssertionError) as error:
        print(f"FAIL readable KEVM operational slice: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
