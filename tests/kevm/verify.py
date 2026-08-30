#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KEVM operational slice."""

from __future__ import annotations

import argparse
import ast
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
MANIFEST = ROOT / "semantics/kevm/Cargo.toml"
SOURCE = ROOT / "semantics/kevm/src/lib.rs"
LOCK = ROOT / "semantics/Cargo.lock"
CORPUS_PATH = HERE / "corpus.toml"
PINS_PATH = HERE / "pins.toml"
KEVM = ROOT.parent / "inspirations/runtimeverification/evm-semantics"
PACKAGE = "krs-kevm-semantics"
DEFINITION = "main"
MODULE = "KRS-KEVM"
SPEC_MODULE = f"{MODULE}-SPEC"
DESCRIPTOR_COUNT = 1100
CLAIM_COUNT = 8
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
    "Cargo.lock",
    "Krs.lock",
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
    "crates/krs-ir/src/protocol_v7.rs",
    "crates/krs-ir/src/protocol_v7_rule.rs",
    "crates/krs-ir/src/semantic.rs",
    "crates/krs-ir/src/state.rs",
    "crates/krs-k-rust/Cargo.toml",
    "crates/krs-k-rust/src/lib.rs",
    "crates/krs-k-rust/src/bin/krs-native-compile.rs",
    "crates/krs-k-rust/src/bin/krs-native-runner.rs",
    "crates/krs-macros/src/expand.rs",
    "crates/krs-macros/src/lib.rs",
    "crates/krs-syntax/src/attribute.rs",
    "crates/krs-syntax/src/configuration.rs",
    "crates/krs-syntax/src/provenance.rs",
    "crates/krs-syntax/src/rule.rs",
    "crates/krs-syntax/src/state_macro.rs",
    "crates/krs-syntax/src/state_rule.rs",
    "crates/krs-syntax/src/term.rs",
    "crates/krs/src/lib.rs",
    "draft/readability/kevm/README.md",
    "tests/kevm/corpus.toml",
    "tests/kevm/lsp_probe.py",
    "tests/kevm/native.py",
    "semantics/Cargo.lock",
    "semantics/Cargo.toml",
    "semantics/README.md",
    "semantics/coverage.toml",
    "semantics/kevm/Cargo.toml",
    "semantics/kevm/src/lib.rs",
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


def preflight(pins: Mapping[str, Any], corpus: Mapping[str, Any]) -> dict[str, str]:
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

    z3 = support.find_z3_lib()
    environment = {
        "LIBRARY_PATH": os.pathsep.join([os.fspath(z3), os.environ.get("LIBRARY_PATH", "")]).rstrip(os.pathsep),
        "LD_LIBRARY_PATH": os.pathsep.join([os.fspath(z3), os.environ.get("LD_LIBRARY_PATH", "")]).rstrip(os.pathsep),
        "CARGO_NET_OFFLINE": "true",
    }
    return environment


def rust_gate(environment: Mapping[str, str]) -> tuple[Path, Path, Path]:
    root_target = Path(os.environ.get("KRS_KEVM_ROOT_TARGET", "/var/tmp/krs-kevm-gate-root-target"))
    fixture_target = Path(os.environ.get("KRS_KEVM_FIXTURE_TARGET", "/var/tmp/krs-kevm-gate-fixture-target"))
    run(
        ["cargo", "build", "--locked", "--offline", "-p", "krs-cli", "--bin", "krs"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(root_target)},
    )
    run(
        [
            "cargo", "build", "--release", "--locked", "--offline",
            "-p", "krs-k-rust", "--bins",
        ],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(root_target)},
    )
    common = ["--manifest-path", MANIFEST, "--locked", "--offline"]
    fixture_env = {**environment, "CARGO_TARGET_DIR": os.fspath(fixture_target)}
    run(["cargo", "check", *common, "--all-targets"], environment=fixture_env)
    run(["cargo", "test", *common], environment=fixture_env, timeout=900)
    run(
        [
            "cargo", "clippy", *common, "--all-targets", "--",
            "-D", "warnings", "-A", "clippy::too_many_arguments",
        ],
        environment=fixture_env,
        timeout=900,
    )
    run(["cargo", "fmt", "--all", "--", "--check"])
    run([root_target / "debug/krs", "fmt", "--check", "--manifest-path", MANIFEST, SOURCE], environment=environment)
    run(["cargo", "+1.88.0", "check", *common, "--all-targets"], environment=fixture_env, timeout=900)
    analyzer = support.find_rust_analyzer()
    lsp_env = {**environment, "PATH": os.pathsep.join([os.fspath(analyzer.parent), os.environ["PATH"]])}
    run([sys.executable, HERE / "lsp_probe.py"], environment=lsp_env)
    return (
        root_target / "debug/krs",
        root_target / "release/krs-native-compile",
        root_target / "release/krs-native-runner",
    )


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


def split_claims(source: str) -> tuple[str, list[str]]:
    lines = source.splitlines(keepends=True)
    starters = re.compile(
        r"^(?:endmodule\b|  (?:syntax\b|configuration\b|context alias\b|rule\b|claim \[))"
    )
    semantics: list[str] = []
    claims: list[str] = []
    index = 0
    while index < len(lines):
        if not lines[index].startswith("  claim ["):
            semantics.append(lines[index])
            index += 1
            continue
        start = index
        index += 1
        while index < len(lines) and starters.match(lines[index]) is None:
            index += 1
        claims.extend(lines[start:index])
    value = "".join(semantics)
    if sum(line.startswith("  claim [") for line in claims) != CLAIM_COUNT:
        raise GateError(f"expected exactly {CLAIM_COUNT} emitted KEVM claims")
    if "  claim [" in value or not value.endswith("endmodule\n"):
        raise GateError("claim stripping did not preserve a claim-free module")
    return value, claims


def artifact_gate(workspace: Path, krs: Path, pins: Mapping[str, Any], environment: Mapping[str, str]) -> Path:
    base = ["--manifest-path", MANIFEST, "--package", PACKAGE, "--definition", DEFINITION]
    check = run([krs, "check", *base], environment=environment)
    if f"{DESCRIPTOR_COUNT} descriptors" not in check.stdout:
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
        "../../crates/krs": ROOT / "crates/krs",
        "../../crates/krs-compiler": ROOT / "crates/krs-compiler",
        "../../crates/krs-ir": ROOT / "crates/krs-ir",
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
    if "  imports BYTES\n" not in readable:
        raise GateError("emitted KEVM definition does not import pinned BYTES")
    if "lengthBytes(" not in readable:
        raise GateError("emitted KEVM definition omits functional lengthBytes syntax")
    if re.search(r"V[0-9A-F]+:Bytes \[ V[0-9A-F]+:Int \]", readable) is None:
        raise GateError("emitted KEVM definition omits builtin byte lookup syntax")
    if "EvmProgram" in readable:
        raise GateError("emitted KEVM definition retained the structured program adapter")
    sentence = re.compile(r"^  (rule|claim)(?: \[([^]]+)\])?", re.MULTILINE)
    if readable.split("\n  rule ", 1)[0] != expanded_k.split("\n  rule ", 1)[0]:
        raise GateError("independent expansion changed syntax or configuration")
    if sentence.findall(readable) != sentence.findall(expanded_k):
        raise GateError("independent expansion changed rule or claim identities")
    return outputs[0]


def normalize_term(value: str) -> str:
    def normalize_bytes(match: re.Match[str]) -> str:
        decoded = ast.literal_eval(match.group(0))
        if not isinstance(decoded, bytes):
            raise GateError(f"invalid Bytes token: {match.group(0)}")
        return 'b"' + "".join(f"\\x{byte:02x}" for byte in decoded) + '"'

    value = re.sub(r'b"(?:\\.|[^"\\])*"', normalize_bytes, value)
    value = re.sub(r"\s+", " ", value.strip())
    value = re.sub(r"\s*([(),;:])\s*", r"\1", value)
    value = re.sub(r"\.\s+", ".", value)
    return value


def observed_cell(result: str, name: str) -> str:
    match = re.search(rf"<{name}>\s*(.*?)\s*</{name}>", result, re.DOTALL)
    if match is None:
        raise GateError(f"native output omitted <{name}>: {result}")
    return normalize_term(match.group(1))


def block_hashes_term(values: Any) -> str:
    if not isinstance(values, list) or not all(isinstance(value, str) for value in values):
        raise GateError(f"block_hashes is not a list of concrete Int strings: {values}")
    if not values:
        return ".List"
    return " ".join(f"ListItem({value})" for value in values)


def int_map_term(values: Any) -> str:
    if not isinstance(values, dict) or not all(isinstance(key, str) for key in values):
        raise GateError(f"storage Map is not a string-keyed table: {values}")
    if not values:
        return ".Map"
    return " ".join(f"{key} |-> {values[key]}" for key in sorted(values, key=int))


def accessed_storage_term(values: Any) -> str:
    if not isinstance(values, dict) or not all(isinstance(key, str) for key in values):
        raise GateError(f"accessed_storage is not a string-keyed table: {values}")
    if not values:
        return ".Map"
    entries = []
    for key in sorted(values, key=int):
        slots = values[key]
        if not isinstance(slots, list):
            raise GateError(f"accessed_storage[{key}] is not an array: {slots}")
        value = ".Set" if not slots else " ".join(
            f"SetItem({slot})" for slot in sorted((str(slot) for slot in slots), key=int)
        )
        entries.append(f"{key} |-> ({value})")
    return " ".join(entries)


def int_set_term(values: Any) -> str:
    if not isinstance(values, list):
        raise GateError(f"concrete Set is not an array: {values}")
    items = [f"SetItem({value})" for value in sorted((str(value) for value in values), key=int)]
    return ".Set" if not items else " ".join(items)


def logs_term(values: Any) -> str:
    if not isinstance(values, list):
        raise GateError(f"concrete logs is not an array: {values}")
    items = []
    for index, value in enumerate(values):
        if not isinstance(value, dict):
            raise GateError(f"concrete logs[{index}] is not a table: {value}")
        topics = value.get("topics", [])
        if not isinstance(topics, list):
            raise GateError(f"concrete logs[{index}].topics is not an array: {topics}")
        topic_term = ".List" if not topics else " ".join(
            f"ListItem({topic})" for topic in topics
        )
        data = value.get("data", 'b""')
        items.append(
            f"ListItem(logEntry({value.get('address', '0')}, {topic_term}, {data}))"
        )
    return ".List" if not items else " ".join(items)


def observed_int_map(result: str, name: str) -> str:
    value = observed_cell(result, name)
    return ".Map" if value == ".Map" else ",".join(
        f"{key}:{entry}" for key, entry in re.findall(r"(-?\d+)\s*\|->\s*(-?\d+)", value)
    )


def observed_int_set(result: str, name: str) -> str:
    value = observed_cell(result, name)
    if value == ".Set":
        return ".Set"
    items = sorted(re.findall(r"SetItem\((-?\d+)\)", value), key=int)
    return ",".join(items)


def observed_accessed_storage(result: str) -> str:
    value = observed_cell(result, "accessedStorage")
    if value == ".Map":
        return value
    entries = []
    for key, body in re.findall(r"(-?\d+)\s*\|->\s*\((.*?)\)(?=\s+-?\d+\s*\|->|$)", value):
        slots = sorted(re.findall(r"SetItem\((-?\d+)\)", body), key=int)
        entries.append(f"{key}:[{','.join(slots)}]")
    return ",".join(entries)


def rendered_int_map(values: Any) -> str:
    if not isinstance(values, dict) or not all(isinstance(key, str) for key in values):
        raise GateError(f"expected storage Map is not a string-keyed table: {values}")
    return ".Map" if not values else ",".join(
        f"{key}:{values[key]}" for key in sorted(values, key=int)
    )


def rendered_accessed_storage(values: Any) -> str:
    if not isinstance(values, dict) or not all(isinstance(key, str) for key in values):
        raise GateError(f"expected accessed_storage is not a string-keyed table: {values}")
    return ".Map" if not values else ",".join(
        f"{key}:[{','.join(sorted((str(slot) for slot in values[key]), key=int))}]"
        for key in sorted(values, key=int)
    )


def compile_java_definition(
    workspace: Path,
    artifacts: Path,
    k_bin: Path,
    pins: Mapping[str, Any],
) -> tuple[Path, list[str]]:
    claim_free, claims = split_claims((artifacts / "definition.k").read_text(encoding="utf-8"))
    semantics = workspace / "semantics.k"
    semantics.write_text(claim_free, encoding="utf-8")
    definition = workspace / "semantics-kompiled"
    run([k_bin / "kompile", semantics, "--backend", "haskell", "--main-module", MODULE, "--syntax-module", MODULE, "--emit-json", "--output-definition", definition], timeout=900)
    kore_hash = support.normalized_kore_sha256(definition / "definition.kore", semantics)
    if kore_hash != pins.get("definition_kore_sha256"):
        raise GateError(f"native definition.kore hash differs: {kore_hash}")
    return definition, claims


def compile_native_definition(
    workspace: Path,
    artifacts: Path,
    compiler: Path,
    pins: Mapping[str, Any],
    environment: Mapping[str, str],
) -> tuple[Path, list[str]]:
    definition = workspace / "native-definition.kore"
    run(
        [compiler, artifacts / "definition-ir.json", definition],
        environment=environment,
        timeout=900,
    )
    kore_hash = sha256(definition)
    if kore_hash != pins.get("native_definition_kore_sha256"):
        raise GateError(f"native K-Rust definition.kore hash differs: {kore_hash}")
    _, claims = split_claims((artifacts / "definition.k").read_text(encoding="utf-8"))
    return definition, claims


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
        [
            sys.executable,
            HERE / "native.py",
            runner,
            definition,
            MODULE,
            CORPUS_PATH,
        ],
        environment=environment,
        timeout=900,
    )
    expected = f"PASS native KEVM behavior: {len(behavior)} executions; sha256={pins.get('behavior_sha256')}"
    if result.stdout.strip() != expected:
        raise GateError(f"K-Rust behavior evidence differs: {result.stdout.strip()}")
    return len(behavior)


def java_reference_gate(
    workspace: Path,
    definition: Path,
    claims: list[str],
    k_bin: Path,
    pins: Mapping[str, Any],
    corpus: Mapping[str, Any],
) -> tuple[int, int]:
    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    outcomes: list[dict[str, str]] = []
    for case in behavior:
        empty_bytes = 'b""'
        context = [
            f"-cADDRESS={case.get('address', '0')}",
            f"-cACCOUNTID={case.get('account_id', case.get('address', '0'))}",
            f"-cBALANCE={case.get('balance', '0')}",
            f"-cCODE={case.get('code', empty_bytes)}",
            f"-cNONCE={case.get('nonce', '0')}",
            f"-cORIGIN={case.get('origin', '0')}",
            f"-cCALLER={case.get('caller', '0')}",
            f"-cCALLVALUE={case.get('call_value', '0')}",
            f"-cCALLDATA={case.get('call_data', empty_bytes)}",
            f"-cGASPRICE={case.get('gas_price', '0')}",
            f"-cRETURNDATA={case.get('return_data', empty_bytes)}",
            f"-cLOCALMEM={case.get('local_mem', empty_bytes)}",
            f"-cMEMORYUSED={case.get('memory_used', '0')}",
            f"-cSTORAGE={int_map_term(case.get('storage', {}))}",
            f"-cORIGSTORAGE={int_map_term(case.get('original_storage', case.get('storage', {})))}",
            f"-cACCESSEDSTORAGE={accessed_storage_term(case.get('accessed_storage', {}))}",
            f"-cACCESSEDACCOUNTS={int_set_term(case.get('accessed_accounts', []))}",
            f"-cLOGS={logs_term(case.get('logs', []))}",
            f"-cREFUND={case.get('refund', '0')}",
            f"-cSTATIC={str(case.get('static', False)).lower()}",
            f"-cBLOCKHASHES={block_hashes_term(case.get('block_hashes', []))}",
            f"-cCOINBASE={case.get('coinbase', '0')}",
            f"-cTIMESTAMP={case.get('timestamp', '0')}",
            f"-cNUMBER={case.get('number', '0')}",
            f"-cPREVRANDAO={case.get('prev_randao', '0')}",
            f"-cGASLIMIT={case.get('gas_limit', '0')}",
            f"-cCHAINID={case.get('chain_id', '0')}",
            f"-cBASEFEE={case.get('base_fee', '0')}",
        ]
        result = run(
            [
                k_bin / "krun", "--definition", definition,
                "-cPGM=run", f"-cPROGRAM={case['program']}", f"-cSTACK={case['stack']}",
                f"-cPC={case['pc']}", f"-cGAS={case['gas']}", "-cSTATUS=.StatusCode",
                *context, "--output", "pretty",
            ],
            timeout=120,
        ).stdout
        expected_k = "SLOAD" if case.get("expected_stuck_operation") == "storageLoad" else ".K"
        if observed_cell(result, "k") != expected_k:
            raise GateError(f"{case['id']} did not halt: {result}")
        observed = {
            "id": str(case["id"]),
            "program": observed_cell(result, "program"),
            "stack": observed_cell(result, "wordStack"),
            "pc": observed_cell(result, "pc"),
            "gas": observed_cell(result, "gas"),
            "output": observed_cell(result, "output"),
            "local_mem": observed_cell(result, "localMem"),
            "memory_used": observed_cell(result, "memoryUsed"),
            "status": observed_cell(result, "statusCode"),
        }
        expected = {
            "id": str(case["id"]),
            "program": normalize_term(str(case["expected_program"])),
            "stack": normalize_term(str(case["expected_stack"])),
            "pc": str(case["expected_pc"]),
            "gas": str(case["expected_gas"]),
            "output": normalize_term(
                str(case.get("expected_output", case.get("return_data", empty_bytes)))
            ),
            "local_mem": normalize_term(
                str(case.get("expected_local_mem", case.get("local_mem", empty_bytes)))
            ),
            "memory_used": str(case.get("expected_memory_used", case.get("memory_used", "0"))),
            "status": str(case["expected_status"]),
        }
        if case.get("observe_storage", False):
            observed.update({
                "storage": observed_int_map(result, "storage"),
                "accessed_storage": observed_accessed_storage(result),
                "refund": observed_cell(result, "refund"),
            })
            expected.update({
                "storage": rendered_int_map(
                    case.get("expected_storage", case.get("storage", {}))
                ),
                "accessed_storage": rendered_accessed_storage(
                    case.get("expected_accessed_storage", case.get("accessed_storage", {}))
                ),
                "refund": str(case.get("expected_refund", case.get("refund", "0"))),
            })
        if case.get("observe_accounts", False):
            observed["accessed_accounts"] = observed_int_set(result, "accessedAccounts")
            values = sorted(
                (
                    str(value)
                    for value in case.get(
                        "expected_accessed_accounts", case.get("accessed_accounts", [])
                    )
                ),
                key=int,
            )
            expected["accessed_accounts"] = ".Set" if not values else ",".join(values)
        if case.get("observe_logs", False):
            observed["logs"] = observed_cell(result, "log")
            expected["logs"] = normalize_term(
                logs_term(case.get("expected_logs", case.get("logs", [])))
            )
        if case.get("observe_state_stacks", False):
            observed.update({
                "call_stack": observed_cell(result, "callStack"),
                "interim_states": observed_cell(result, "interimStates"),
            })
            expected.update({
                "call_stack": ".List",
                "interim_states": ".List",
            })
        if observed != expected:
            raise GateError(f"{case['id']} differs: expected={expected}, actual={observed}")
        outcomes.append(observed)
    behavior_hash = hashlib.sha256(support.canonical(outcomes).encode()).hexdigest()
    if behavior_hash != pins.get("behavior_sha256"):
        raise GateError(f"behavior hash differs: {behavior_hash}; outcomes={support.canonical(outcomes)}")

    spec_path = workspace / "spec.k"
    spec_path.write_text(
        f'requires "semantics.k"\n\nmodule {SPEC_MODULE}\n  imports {MODULE}\n\n'
        f'{"".join(claims)}endmodule\n',
        encoding="utf-8",
    )
    dry = run([k_bin / "kprove", spec_path, "--definition", definition, "--spec-module", SPEC_MODULE, "--dry-run"], timeout=180)
    if "kore-exec" not in dry.stdout or "--prove" not in dry.stdout:
        raise GateError("proof dry run did not select the native Haskell prover")
    proof = run([k_bin / "kprove", spec_path, "--definition", definition, "--spec-module", SPEC_MODULE], timeout=300)
    if proof.stdout.strip() != "#Top":
        raise GateError(f"KEVM claim did not close: {proof.stdout.strip()}")
    return len(outcomes), sum(line.startswith("  claim [") for line in claims)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--java-reference",
        action="store_true",
        help="run the expensive pinned Java behavior and proof authority gate",
    )
    arguments = parser.parse_args()
    try:
        with PINS_PATH.open("rb") as stream:
            pins = tomllib.load(stream)
        with CORPUS_PATH.open("rb") as stream:
            corpus = tomllib.load(stream)
        environment = preflight(pins, corpus)
        krs, compiler, runner = rust_gate(environment)
        with tempfile.TemporaryDirectory(prefix="krs-kevm-", dir="/var/tmp") as temporary:
            workspace = Path(temporary)
            artifacts = artifact_gate(workspace, krs, pins, environment)
            if arguments.java_reference:
                k_pin = mapping(pins.get("k"), "pins.k")
                k_bin = support.find_k_bin(str(k_pin["version"]), str(k_pin["commit"]))
                observed = run([k_bin / "kompile", "--version"], timeout=30)
                if f"v{k_pin['version']}" not in observed.stdout + observed.stderr:
                    raise GateError("K executable version differs")
                definition, claims = compile_java_definition(
                    workspace, artifacts, k_bin, pins
                )
                executions, proofs = java_reference_gate(
                    workspace, definition, claims, k_bin, pins, corpus
                )
                qualification = f"{executions} Java reference executions; {proofs} Java reference proofs"
            else:
                definition, claims = compile_native_definition(
                    workspace, artifacts, compiler, pins, environment
                )
                executions = k_rust_gate(runner, definition, pins, corpus, environment)
                deferred_proofs = sum(line.startswith("  claim [") for line in claims)
                qualification = (
                    f"{executions} K-Rust executions; "
                    f"{deferred_proofs} Java reference proofs deferred to --java-reference"
                )
        print(
            f"PASS readable KEVM operational slice: {DESCRIPTOR_COUNT} descriptors; {qualification}; "
            f"protocol {pins['schemas']['descriptor_protocol']}; K {pins['k']['version']}"
        )
        return 0
    except (GateError, OSError, subprocess.TimeoutExpired, AssertionError) as error:
        print(f"FAIL readable KEVM operational slice: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
