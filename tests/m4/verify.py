#!/usr/bin/env python3
"""Ordered, fail-closed M4 complete-IMP release gate.

The default mode stops on the first failed evidence layer.  ``--audit-all``
continues only with layers whose prerequisites are independently available;
it never turns missing evidence into a skip or a pass.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field
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
from typing import Any, Callable, Mapping, Sequence


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS_PATH = HERE / "pins.json"
CORPUS_PATH = HERE / "corpus.json"
RUST_MANIFEST = HERE / "rust-definition/Cargo.toml"
EXPANSION_GOLDEN = HERE / "goldens/imp.expanded.rs"
EXPANDED_MANIFEST = HERE / "expanded-definition/Cargo.toml"
EXPANDED_SOURCE = HERE / "expanded-definition/src/imp.rs"
PROBE_MANIFEST = HERE / "oracle/artifact-probe/Cargo.toml"
NATIVE_MANIFEST = HERE / "native/Cargo.toml"
PACKAGE = "krs-m4-complete-imp"
DEFINITION = "main"
MODULE = "KRS-M4-COMPLETE-IMP"
REFERENCE_MODULE = "KRS-M3D-STATIC"
REFERENCE_SYNTAX_MODULE = "KRS-M3D-STATIC-SYNTAX"
EXPANDED_PACKAGE = "krs-m4-expanded-imp"
IMP_RULE_LABELS = {
    "and_false": "and-false",
    "and_true": "and-true",
    "assign": "assign",
    "block": "block",
    "done": "done",
    "eval_add": "eval-add",
    "eval_bool_eq": "eval-bool-eq",
    "eval_bool_ne": "eval-bool-ne",
    "eval_div": "eval-div",
    "eval_ge": "eval-ge",
    "eval_gt": "eval-gt",
    "eval_int_eq": "eval-int-eq",
    "eval_int_ne": "eval-int-ne",
    "eval_le": "eval-le",
    "eval_lt": "eval-lt",
    "eval_mul": "eval-mul",
    "eval_neg": "eval-neg",
    "eval_not": "eval-not",
    "eval_sub": "eval-sub",
    "if_else": "if-else",
    "if_false": "if-false",
    "if_true": "if-true",
    "or_false": "or-false",
    "or_true": "or-true",
    "step": "step",
    "var": "var",
    "while": "while",
}


class GateError(RuntimeError):
    """One M4 evidence layer is absent, malformed, or different."""


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def sha256(path: Path) -> str:
    if not path.is_file():
        raise GateError(f"required file is missing: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise GateError(f"cannot load {path}: {error}") from error
    if not isinstance(value, dict):
        raise GateError(f"{path} must contain one JSON object")
    return value


def compact(process: subprocess.CompletedProcess[str], limit: int = 2400) -> str:
    value = "\n".join(
        part.strip() for part in (process.stdout, process.stderr) if part.strip()
    )
    return value[:limit] + ("…" if len(value) > limit else "")


def require_exact_summary(
    process: subprocess.CompletedProcess[str], expected: str, phase: str
) -> None:
    """Reject a nominal PASS accompanied by missing, extra, or stderr output."""

    if process.stdout != expected or process.stderr:
        raise GateError(f"{phase} did not report its exact PASS summary: {compact(process)}")


def run(
    command: Sequence[str | os.PathLike[str]],
    *,
    timeout: int,
    cwd: Path = ROOT,
    environment: Mapping[str, str] | None = None,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env.update(
        {
            "LC_ALL": "C",
            "LANG": "C",
            "PYTHONDONTWRITEBYTECODE": "1",
        }
    )
    if environment:
        env.update(environment)
    argv = [os.fspath(item) for item in command]
    process = subprocess.Popen(
        argv,
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as error:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            stdout, stderr = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
        raise GateError(
            f"command timed out after {timeout}s; complete process group terminated: {argv!r}"
        ) from error
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        raise
    result = subprocess.CompletedProcess(argv, process.returncode, stdout, stderr)
    if check and result.returncode != 0:
        raise GateError(f"command failed ({result.returncode}): {argv!r}\n{compact(result)}")
    return result


def executable(name: str) -> str:
    value = shutil.which(name)
    if value is None:
        raise GateError(f"required executable is missing: {name}")
    return value


def exact_directory(left: Path, right: Path, names: Sequence[str]) -> dict[str, str]:
    left_names = sorted(path.name for path in left.iterdir() if path.is_file())
    right_names = sorted(path.name for path in right.iterdir() if path.is_file())
    expected = sorted(names)
    if left_names != expected or right_names != expected:
        raise GateError(
            f"artifact set differs: expected={expected}, left={left_names}, right={right_names}"
        )
    hashes: dict[str, str] = {}
    for name in names:
        if left.joinpath(name).read_bytes() != right.joinpath(name).read_bytes():
            raise GateError(f"repeated artifact differs byte-for-byte: {name}")
        hashes[name] = sha256(left / name)
    return hashes


def _normalize_imp_identity(value: Any, alpha_names: Mapping[str, str]) -> Any:
    """Normalize only package and span-derived identity differences."""

    if isinstance(value, str):
        return alpha_names.get(value, value)
    if isinstance(value, list):
        return [_normalize_imp_identity(child, alpha_names) for child in value]
    if not isinstance(value, dict):
        return value
    if value.get("k_namespace") == MODULE and {
        "cargo_name", "cargo_version", "cargo_source"
    } <= set(value):
        return {
            "k_namespace": MODULE,
            "cargo_name": "normalized-imp-package",
            "cargo_version": "0.0.0",
            "cargo_source": "workspace",
        }
    return {
        key: _normalize_imp_identity(child, alpha_names)
        for key, child in value.items()
    }


def _subsort_alpha_names(bundle: Mapping[str, Any]) -> dict[str, str]:
    """Name generated and stable readable subsorts by semantic relation."""

    descriptors = bundle.get("descriptors")
    if not isinstance(descriptors, list):
        raise GateError("replacement parity descriptor bundle lacks a descriptor array")
    relations: list[tuple[str, str]] = []
    for descriptor in descriptors:
        if not isinstance(descriptor, dict):
            raise GateError("replacement parity descriptor entry is not an object")
        identity = descriptor.get("id", {})
        payload = descriptor.get("descriptor", {})
        if not isinstance(identity, dict) or not isinstance(payload, dict):
            raise GateError("replacement parity descriptor identity or payload is malformed")
        name = identity.get("item_name")
        if (
            identity.get("module_path") == ["imp"]
            and descriptor.get("descriptor_kind") == "grammar"
            and payload.get("grammar_kind") == "subsort"
            and isinstance(name, str)
        ):
            grammar = _normalize_imp_identity(payload.get("grammar"), {})
            relations.append((canonical(grammar), name))
    if len(relations) != 3 or len({relation for relation, _ in relations}) != 3:
        raise GateError(
            "replacement parity requires exactly three distinct IMP subsorts"
        )
    return {
        name: f"__krs_grammar_subsort_alpha_{ordinal}"
        for ordinal, (_, name) in enumerate(sorted(relations))
    }


def _normalized_imp_non_rules(
    bundle: Mapping[str, Any], rule_kind: str
) -> tuple[list[Any], list[Any]]:
    """Project the 54 IMP declarations unaffected by rule transport."""

    descriptors = bundle.get("descriptors")
    declarations = bundle.get("declarations")
    if not isinstance(descriptors, list) or not isinstance(declarations, list):
        raise GateError("replacement parity bundle arrays are malformed")
    alpha_names = _subsort_alpha_names(bundle)
    selected = [
        descriptor
        for descriptor in descriptors
        if isinstance(descriptor, dict)
        and descriptor.get("id", {}).get("module_path") == ["imp"]
        and descriptor.get("descriptor_kind") != rule_kind
    ]
    expected_kinds = {
        "constructor": 21,
        "fixed_configuration": 1,
        "grammar": 29,
        "sort": 3,
    }
    observed_kinds = Counter(
        descriptor.get("descriptor_kind") for descriptor in selected
    )
    if observed_kinds != expected_kinds:
        raise GateError(
            f"replacement parity non-rule descriptor kinds differ: {observed_kinds}"
        )

    normalized_descriptors = []
    normalized_ids = set()
    for descriptor in selected:
        normalized = _normalize_imp_identity(descriptor, alpha_names)
        normalized.pop("provenance", None)
        normalized_descriptors.append(normalized)
        normalized_ids.add(canonical(normalized.get("id")))
    if len(normalized_ids) != 54:
        raise GateError("replacement parity non-rule identities are not 54 unique items")

    normalized_declarations = []
    for declaration in declarations:
        if not isinstance(declaration, dict):
            raise GateError("replacement parity declaration entry is not an object")
        normalized = _normalize_imp_identity(declaration, alpha_names)
        if canonical(normalized.get("id")) in normalized_ids:
            normalized_declarations.append(normalized)
    if len(normalized_declarations) != 54:
        raise GateError(
            "replacement parity does not contain exactly 54 non-rule declaration records"
        )
    return (
        sorted(normalized_descriptors, key=canonical),
        sorted(normalized_declarations, key=canonical),
    )


def _imp_rule_transport(bundle: Mapping[str, Any], rule_kind: str) -> dict[str, str]:
    """Return the exact Rust-item to K-label mapping for one rule surface."""

    descriptors = bundle.get("descriptors")
    if not isinstance(descriptors, list):
        raise GateError("replacement rule transport lacks a descriptor array")
    transport: dict[str, str] = {}
    for descriptor in descriptors:
        if not isinstance(descriptor, dict):
            raise GateError("replacement rule transport descriptor is malformed")
        identity = descriptor.get("id", {})
        payload = descriptor.get("descriptor", {})
        if (
            identity.get("module_path") != ["imp"]
            or descriptor.get("descriptor_kind") != rule_kind
        ):
            continue
        if payload.get("sentence_kind") != "transition":
            raise GateError("replacement IMP rule transport is not a transition")
        name = identity.get("item_name")
        label = payload.get("label", {}).get("name")
        if not isinstance(name, str) or not isinstance(label, str):
            raise GateError("replacement IMP rule name or label is malformed")
        name = name.removeprefix("r#")
        if name in transport:
            raise GateError(f"replacement IMP rule identity is duplicated: {name}")
        transport[name] = label
    return transport


def _module_sentences(source: str, module: str) -> list[str]:
    """Split one emitted K module into source-level sentence blocks."""

    lines = source.splitlines()
    starts = [index for index, line in enumerate(lines) if line == f"module {module}"]
    if len(starts) != 1:
        raise GateError(f"emitted K must contain exactly one `{module}` module")
    start = starts[0] + 1
    try:
        end = lines.index("endmodule", start)
    except ValueError as error:
        raise GateError(f"emitted K module `{module}` lacks `endmodule`") from error
    starter = re.compile(
        r"^  (?:imports\b|syntax\b|configuration\b|context alias\b|rule\b|claim\b)"
    )
    sentences: list[str] = []
    current: list[str] = []
    for line in lines[start:end]:
        if starter.match(line):
            if current:
                sentences.append("\n".join(current).rstrip())
            current = [line]
        elif current:
            current.append(line)
        elif line.strip():
            raise GateError(f"unclassified emitted K module content: {line!r}")
    if current:
        sentences.append("\n".join(current).rstrip())
    return sentences


def _normalize_head_rule_sentence(sentence: str) -> str:
    """Normalize explicit frame transport to the readable head-rule spelling."""

    if not sentence.startswith("  rule ["):
        return sentence
    sentence = re.sub(
        r"^    <k> (.*) ~> (V[0-9A-F]+:K) => (.*) ~> \2 </k>$",
        r"    <k> \1 => \3 ... </k>",
        sentence,
        flags=re.MULTILINE,
    )
    return re.sub(
        r"^(    <env> .*) V[0-9A-F]+:Map </env>$",
        r"\1 ... </env>",
        sentence,
        flags=re.MULTILINE,
    )


def _verify_replacement_parity(authored: Path, replacement: Path) -> None:
    """Require declaration, rule-transport, and emitted-K replacement parity."""

    authored_bundle = load_json(authored / "descriptor-bundle.json")
    replacement_bundle = load_json(replacement / "descriptor-bundle.json")
    authored_non_rules = _normalized_imp_non_rules(authored_bundle, "head_rule")
    replacement_non_rules = _normalized_imp_non_rules(
        replacement_bundle, "configuration_rule"
    )
    if authored_non_rules != replacement_non_rules:
        raise GateError(
            "expanded replacement differs across normalized non-rule descriptors or metadata"
        )

    authored_rules = _imp_rule_transport(authored_bundle, "head_rule")
    replacement_rules = _imp_rule_transport(replacement_bundle, "configuration_rule")
    if authored_rules != IMP_RULE_LABELS or replacement_rules != IMP_RULE_LABELS:
        raise GateError(
            "expanded replacement does not preserve the exact 27-rule name/label transport"
        )

    authored_sentences = Counter(
        _normalize_head_rule_sentence(sentence)
        for sentence in _module_sentences(
            (authored / "definition.k").read_text(encoding="utf-8"), MODULE
        )
    )
    replacement_sentence_list = [
        _normalize_head_rule_sentence(sentence)
        for sentence in _module_sentences(
            (replacement / "definition.k").read_text(encoding="utf-8"), MODULE
        )
    ]
    if len(replacement_sentence_list) != 77:
        raise GateError(
            "expanded replacement must emit exactly 77 IMP imports and sentences"
        )
    replacement_sentences = Counter(replacement_sentence_list)
    missing = replacement_sentences - authored_sentences
    if missing:
        raise GateError(
            f"expanded replacement emitted K sentence multiset differs: {missing}"
        )


def git_revision(path: Path) -> str:
    process = run(["git", "-C", path, "rev-parse", "HEAD"], timeout=30)
    return process.stdout.strip()


def relevant_untracked(paths: Sequence[str]) -> list[str]:
    """Remove only interpreter-generated Python cache entries."""

    return sorted(
        relative
        for relative in paths
        if "__pycache__" not in Path(relative).parts
        and Path(relative).suffix != ".pyc"
    )


def tracked_tree_digest(
    checkout: Path, prefix: str, *, reject_untracked: bool = False
) -> str:
    process = run(
        ["git", "-C", checkout, "ls-files", prefix], timeout=60
    )
    paths = sorted(line for line in process.stdout.splitlines() if line)
    if not paths:
        raise GateError(f"tracked tree is empty: {checkout}/{prefix}")
    if reject_untracked:
        untracked = run(
            ["git", "-C", checkout, "ls-files", "--others", prefix],
            timeout=60,
        ).stdout.splitlines()
        untracked = relevant_untracked(untracked)
        if untracked:
            raise GateError(
                f"untracked files can affect pinned source tree {checkout}/{prefix}: "
                f"{sorted(untracked)}"
            )
    digest = hashlib.sha256()
    for relative in paths:
        path = checkout / relative
        digest.update(relative.encode())
        digest.update(b"\0")
        digest.update(sha256(path).encode())
        digest.update(b"\n")
    return digest.hexdigest()


def is_crate_source(path: Path) -> bool:
    """Whether one crate-tree file can affect a build, test, or live probe."""

    return (
        "target" not in path.parts
        and "__pycache__" not in path.parts
        and path.suffix != ".pyc"
    )


def expected_source_ledger_paths() -> set[str]:
    """Return the complete, deterministic set of source paths guarded by M4.

    The ledger deliberately excludes its own ``pins.json`` entry (which would
    be self-referential) and generated Cargo/Python output.  Comparing this
    set before checking hashes makes addition of an unreviewed production or
    M4 gate source fail closed, not merely edits to already-known files.
    """

    paths = {"Cargo.toml", "Cargo.lock", "Krs.lock", "rust-analyzer.toml"}
    crates = ROOT / "crates"
    for path in crates.rglob("*"):
        if not path.is_file() or not is_crate_source(path):
            continue
        paths.add(path.relative_to(ROOT).as_posix())

    for path in HERE.rglob("*"):
        if not path.is_file():
            continue
        relative_parts = path.relative_to(HERE).parts
        if "target" in relative_parts or "__pycache__" in relative_parts:
            continue
        if path.name == "pins.json" or path.suffix == ".pyc":
            continue
        paths.add(path.relative_to(ROOT).as_posix())

    paths.update(
        {
            "../inspirations/midnightntwrk/k-rust-krs/Cargo.lock",
            "../inspirations/midnightntwrk/k-rust-krs/Cargo.toml",
            "../inspirations/midnightntwrk/k-rust-krs/crates/k-rust/Cargo.toml",
            "../inspirations/midnightntwrk/k-rust-krs/crates/k-rust/src/kompile/compile.rs",
            "../inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics/calc.k",
            "../inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics/expr.k",
            "../inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics/imp-verification.k",
            "../inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics/imp.k",
            "tests/m3d/fixtures/static-adjunct.k",
        }
    )
    return paths


def _split_emitted_source(source: str) -> tuple[str, list[str], str]:
    """Split exact top-level claims from one emitted module."""

    starters = re.compile(
        r"^(?:endmodule\b|  (?:syntax\b|configuration\b|context alias\b|rule\b|claim \[))"
    )
    lines = source.splitlines(keepends=True)
    output: list[str] = []
    labels: list[str] = []
    claims: list[str] = []
    index = 0
    while index < len(lines):
        match = re.match(r"^  claim \[([^]]+)\]:\s*$", lines[index].rstrip("\r\n"))
        if match is None:
            output.append(lines[index])
            index += 1
            continue
        labels.append(match.group(1))
        start = index
        index += 1
        while index < len(lines) and starters.match(lines[index]) is None:
            index += 1
        claims.extend(lines[start:index])
    if len(labels) != 20 or len(set(labels)) != 20:
        raise GateError(f"expected 20 unique emitted claims, found {labels!r}")
    value = "".join(output)
    if "  claim [" in value:
        raise GateError("claim stripping left a top-level claim sentence")
    if not value.endswith("endmodule\n"):
        raise GateError("claim-free emitted definition lost its exact module terminator")
    return value, labels, "".join(claims)


def _claim_free_source(source: str) -> tuple[str, list[str]]:
    """Remove only top-level emitted claim sentences, preserving all other bytes."""

    value, labels, _ = _split_emitted_source(source)
    return value, labels


@dataclass
class Context:
    pins: dict[str, Any]
    corpus: dict[str, Any]
    workspace: Path
    target: Path
    tools: dict[str, str] = field(default_factory=dict)
    krs: Path | None = None
    artifacts: Path | None = None
    reference_definition: Path | None = None
    actual_definition: Path | None = None
    reference_failure_definition: Path | None = None
    actual_failure_definition: Path | None = None
    artifact_hashes: dict[str, str] = field(default_factory=dict)


def require_mapping(value: Any, name: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise GateError(f"{name} must be an object")
    return value


def phase_preflight(context: Context) -> str:
    pins = context.pins
    corpus = context.corpus
    if pins.get("schema") != 1 or pins.get("milestone") != "M4":
        raise GateError("pins.json is not the exact M4 schema-1 ledger")
    if corpus.get("schema") != 2:
        raise GateError("corpus.json is not schema 2")
    if sha256(CORPUS_PATH) != pins.get("corpus_sha256"):
        raise GateError("corpus.json hash differs from pins.json")

    ledgers = require_mapping(corpus.get("input_ledgers"), "corpus.input_ledgers")
    if set(ledgers) != {"m3a", "m3b", "m3c", "m3d"}:
        raise GateError("corpus must name exactly the M3A--M3D input ledgers")
    for name, raw in ledgers.items():
        entry = require_mapping(raw, f"input ledger {name}")
        path = ROOT / str(entry.get("path"))
        if sha256(path) != entry.get("sha256"):
            raise GateError(f"{name} pin-ledger hash differs")
        ledger = load_json(path)
        base = path.parent
        for relative, expected in require_mapping(
            ledger.get("source_sha256"), f"{name}.source_sha256"
        ).items():
            if sha256(base / relative) != expected:
                raise GateError(f"{name} corpus hash differs: {relative}")

    source_ledger = require_mapping(pins.get("source_sha256"), "pins.source_sha256")
    expected_paths = expected_source_ledger_paths()
    if set(source_ledger) != expected_paths:
        missing = sorted(expected_paths - set(source_ledger))
        extra = sorted(set(source_ledger) - expected_paths)
        raise GateError(f"M4 source ledger path set differs: missing={missing}, extra={extra}")
    for relative, expected in source_ledger.items():
        if sha256(ROOT / relative) != expected:
            raise GateError(f"M4 source hash differs: {relative}")

    for name, entry_raw in require_mapping(
        pins.get("proof_ledgers"), "pins.proof_ledgers"
    ).items():
        entry = require_mapping(entry_raw, f"proof ledger {name}")
        path = ROOT / str(entry.get("path"))
        if sha256(path) != entry.get("sha256"):
            raise GateError(f"proof ledger hash differs: {name}")
        proof_ledger = load_json(path)
        declared = proof_ledger.get("proof_outcomes")
        if not isinstance(declared, dict) or not declared:
            raise GateError(f"proof ledger is empty: {name}")

    revisions = require_mapping(pins.get("revisions"), "pins.revisions")
    imp = ROOT.parent / "inspirations/runtimeverification/imp-semantics"
    k_checkout = ROOT.parent / "inspirations/runtimeverification/k"
    native = ROOT.parent / "inspirations/midnightntwrk/k-rust-krs"
    observed = {
        "k": git_revision(k_checkout),
        "imp": git_revision(imp),
        "k_rust": git_revision(native),
    }
    expected = {
        "k": require_mapping(revisions.get("k"), "revisions.k").get("commit"),
        "imp": require_mapping(revisions.get("imp"), "revisions.imp").get("commit"),
        "k_rust": require_mapping(revisions.get("k_rust"), "revisions.k_rust").get("commit"),
    }
    if observed != expected:
        raise GateError(f"checkout revision differs: expected={expected}, actual={observed}")

    tools = (
        "cargo", "rustc", "rustfmt", "clippy-driver", "rust-analyzer", "git",
        "kompile", "kast", "krun", "kprove", "kore-exec", "llvm-kompile", "z3",
    )
    context.tools = {name: executable(name) for name in tools}
    version = run([context.tools["kompile"], "--version"], timeout=30)
    k_version = require_mapping(revisions.get("k"), "revisions.k").get("version")
    if f"v{k_version}" not in version.stdout + version.stderr:
        raise GateError(f"K tool version differs: {compact(version)}")

    protocol = (ROOT / "crates/krs-ir/src/lib.rs").read_text(encoding="utf-8")
    ir = (ROOT / "crates/krs-ir/src/ir.rs").read_text(encoding="utf-8")
    schemas = require_mapping(pins.get("schemas"), "pins.schemas")
    if f"pub const CURRENT: Self = Self({schemas.get('protocol')});" not in protocol:
        raise GateError("ProtocolVersion::CURRENT differs from its M4 pin")
    if f"pub const CURRENT: Self = Self({schemas.get('ir')});" not in ir:
        raise GateError("IrSchemaVersion::CURRENT differs from its M4 pin")
    toolchain = require_mapping(
        pins.get("toolchain_compatibility"), "pins.toolchain_compatibility"
    )
    expected_toolchain = {
        "schema": 1,
        "backends": ["haskell", "llvm"],
        "msrv": "1.88.0",
        "builtin_sorts": ["KSequence", "Int", "Bool", "Map", "Id", "Bytes", "List"],
        "descriptor_protocol": 20,
        "definition_ir_schema": 13,
        "k_commit": expected["k"],
        "k_rust_commit": expected["k_rust"],
        "llvm_existential_policy": "typed-backend-capability-error",
        "native_haskell_policy": "exact-kore-comparison",
    }
    if toolchain != expected_toolchain:
        raise GateError("supplemental K/k-rust/backend/builtin toolchain unit differs")
    lock_path = ROOT / "Krs.lock"
    expected_lock = {
        "schema": 1,
        "schemas": {"descriptor_protocol": 20, "definition_ir": 13, "kast_json": 4},
        "cargo": {"lock_sha256": sha256(ROOT / "Cargo.lock"), "msrv": "1.88.0"},
        "k": {
            "version": "7.1.337",
            "commit": expected["k"],
            "pyk_version": "7.1.337",
            "kore_exec_version": "0.1.155",
            "llvm_backend_version": "0.1.140",
            "pyk_source_sha256": tracked_tree_digest(
                k_checkout, "pyk/src", reject_untracked=True
            ),
        },
        "k_rust": {
            "version": "0.4.0",
            "commit": expected["k_rust"],
            "tracked_crate_sha256": tracked_tree_digest(native, "crates/k-rust"),
            "backend_version": "0.3.0",
            "tracked_backend_sha256": tracked_tree_digest(native, "crates/k-rust-backend"),
            "kore_version": "0.3.0",
            "tracked_kore_sha256": tracked_tree_digest(native, "crates/k-rust-kore"),
        },
        "builtin_registry": {
            "source_sha256": sha256(ROOT / "crates/krs/src/lib.rs"),
            "sorts": ["KSequence", "Int", "Bool", "Map", "Id", "Bytes"],
        },
        "solver": {"profile": "z3-inference", "version": "4.12.5"},
        "backend_policy": {
            "haskell": "exact-kore-comparison",
            "llvm_existential_claims": "typed-backend-capability-error",
        },
    }
    expected_lock_text = '''schema = 1

[schemas]
descriptor_protocol = 20
definition_ir = 13
kast_json = 4

[cargo]
lock_sha256 = "95bb513588c314f07e3b4298036037537c46a371a9e2515a619d97bcae12d7c6"
msrv = "1.88.0"

[k]
version = "7.1.337"
commit = "4a46d1231473b599c699160132fd6e76a5c46406"
pyk_version = "7.1.337"
kore_exec_version = "0.1.155"
llvm_backend_version = "0.1.140"
pyk_source_sha256 = "2b6ebc05e7c110927d2cab7d1bd08e0a1f80c9090a621ee541e82665147d88d4"

[k_rust]
version = "0.4.0"
commit = "3cce7a47941c4dc0664e6e870d4e0529d74753c6"
tracked_crate_sha256 = "90585786b420471f1876f6a6d22fb9c13bab89e0420b579c94d690f1834b5535"
backend_version = "0.3.0"
tracked_backend_sha256 = "539816715fdca02419b9d8632075c0e324e900706ca2cd7f321e9c04ba505fef"
kore_version = "0.3.0"
tracked_kore_sha256 = "64e8e0088d13f76b266cff9237378fba100347a13c30e700cd85bf38130b7be7"

[builtin_registry]
source_sha256 = "39569777f5766d94f1881124b1a1176eba3baad0c4d369c065c160ff15b71674"
sorts = ["KSequence", "Int", "Bool", "Map", "Id", "Bytes"]

[solver]
profile = "z3-inference"
version = "4.12.5"

[backend_policy]
haskell = "exact-kore-comparison"
llvm_existential_claims = "typed-backend-capability-error"
'''
    if lock_path.read_text(encoding="utf-8") != expected_lock_text:
        raise GateError("Krs.lock differs from the exact v0.1 compatibility unit")
    lock = expected_lock

    pyk_python = k_checkout / "pyk/.venv/bin/python"
    if not pyk_python.is_file():
        raise GateError("pinned K checkout pyk virtualenv is missing")
    pyk = run(
        [
            pyk_python, "-c",
            "import importlib.metadata; print(importlib.metadata.version('kframework'))",
        ],
        timeout=30,
    ).stdout.strip()
    if pyk != lock["k"]["pyk_version"]:
        raise GateError(f"pinned checkout pyk version differs: {pyk}")
    kore = run([context.tools["kore-exec"], "--version"], timeout=30).stdout.strip()
    if kore != lock["k"]["kore_exec_version"]:
        raise GateError(f"kore-exec version differs: {kore}")
    llvm = run([context.tools["llvm-kompile"], "--version"], timeout=30, check=False)
    if f"llvm-backend-{lock['k']['llvm_backend_version']}" not in llvm.stdout + llvm.stderr:
        raise GateError("LLVM backend version differs from Krs.lock")
    z3 = run([context.tools["z3"], "--version"], timeout=30).stdout.strip()
    if z3 != f"Z3 version {lock['solver']['version']} - 64 bit":
        raise GateError(f"Z3 version differs from Krs.lock: {z3}")
    context.tools["pyk_python"] = os.fspath(pyk_python)
    context.tools["python"] = os.fspath(pyk_python)
    msrv = run(["rustc", "+1.88.0", "--version"], timeout=30).stdout.strip()
    if not msrv.startswith("rustc 1.88.0 "):
        raise GateError(f"MSRV toolchain differs from Krs.lock: {msrv}")
    return "exact sources, ledgers, tools, revisions, protocol 20, and IR schema 13"


def phase_rust(context: Context) -> str:
    env = {"CARGO_TARGET_DIR": os.fspath(context.target)}
    # Rust 1.98 added these style lints after the project's 1.88 MSRV gate.
    # Keep every other warning denied without rewriting recovered test logic.
    clippy_lints = [
        "--", "-D", "warnings",
        "-A", "clippy::too_many_lines",
        "-A", "clippy::disallowed_names",
        "-A", "clippy::struct_excessive_bools",
        "-A", "clippy::items_after_test_module",
    ]
    commands = [
        ["cargo", "fmt", "--all", "--check"],
        ["cargo", "check", "--workspace", "--all-targets", "--locked"],
        ["cargo", "clippy", "--workspace", "--all-targets", "--locked", *clippy_lints],
        ["cargo", "test", "--workspace", "--locked"],
        ["cargo", "fmt", "--manifest-path", os.fspath(RUST_MANIFEST), "--all", "--check"],
        ["cargo", "check", "--manifest-path", os.fspath(RUST_MANIFEST), "--all-targets", "--locked"],
        ["cargo", "clippy", "--manifest-path", os.fspath(RUST_MANIFEST), "--all-targets", "--locked", *clippy_lints],
        ["cargo", "test", "--manifest-path", os.fspath(RUST_MANIFEST), "--locked"],
        ["cargo", "check", "--manifest-path", os.fspath(EXPANDED_MANIFEST), "--all-targets", "--locked"],
        ["cargo", "clippy", "--manifest-path", os.fspath(EXPANDED_MANIFEST), "--all-targets", "--locked", *clippy_lints],
        ["cargo", "test", "--manifest-path", os.fspath(EXPANDED_MANIFEST), "--locked"],
        ["cargo", "fmt", "--manifest-path", os.fspath(NATIVE_MANIFEST), "--all", "--check"],
        ["cargo", "check", "--manifest-path", os.fspath(NATIVE_MANIFEST), "--all-targets", "--locked"],
        ["cargo", "clippy", "--manifest-path", os.fspath(NATIVE_MANIFEST), "--all-targets", "--locked", *clippy_lints],
        ["cargo", "test", "--manifest-path", os.fspath(NATIVE_MANIFEST), "--locked"],
    ]
    for command in commands:
        run(command, timeout=900, environment=env)
    for manifest in (
        ROOT / "Cargo.toml",
        RUST_MANIFEST,
        EXPANDED_MANIFEST,
        NATIVE_MANIFEST,
    ):
        run(
            [
                "cargo", "+1.88.0", "check", "--manifest-path", manifest,
                "--all-targets", "--locked",
            ],
            timeout=900,
            environment=env,
        )
    # Supplemental v0.1 toolchain unit: the closed host builtin registry and
    # IR alias-safety contract are selected by name in addition to the full
    # workspace suite.  Native Haskell and LLVM evidence is exercised below.
    run(
        [
            "cargo", "test", "--locked", "-p", "krs", "--lib",
            "tests::builtin_registry_is_complete_and_exact", "--", "--exact",
        ],
        timeout=300,
        environment=env,
    )
    run(
        [
            "cargo", "test", "--locked", "-p", "krs-ir", "--test",
            "protocol_v6", "builtin_registry_is_complete_exact_and_alias_safe",
            "--", "--exact",
        ],
        timeout=300,
        environment=env,
    )
    doc_env = {**env, "RUSTDOCFLAGS": "-D warnings"}
    run(
        ["cargo", "doc", "--workspace", "--no-deps", "--locked"],
        timeout=900,
        environment=doc_env,
    )
    run(
        [
            "cargo", "doc", "--manifest-path", RUST_MANIFEST,
            "--no-deps", "--locked",
        ],
        timeout=900,
        environment=doc_env,
    )
    run(
        [
            "cargo", "doc", "--manifest-path", NATIVE_MANIFEST,
            "--no-deps", "--locked",
        ],
        timeout=900,
        environment=doc_env,
    )
    for suite in (
        HERE / "test_gate.py",
        HERE / "oracle/test_oracle.py",
        HERE / "compatibility/test_probes.py",
    ):
        run([context.tools["python"], suite], timeout=300, environment=env)

    run(
        ["cargo", "build", "--workspace", "--locked", "-p", "krs-cli", "--bin", "krs"],
        timeout=600,
        environment=env,
    )
    context.krs = context.target / "debug/krs"
    if not context.krs.is_file():
        raise GateError("workspace build did not produce the KRS CLI")
    # These live LSP probes select authored tokens. A mere rust-analyzer
    # --version check is deliberately insufficient evidence.
    run(
        [context.tools["python"], HERE / "compatibility/diagnostics/rust-expansion/lsp_probe.py"],
        timeout=240,
        environment={"CARGO_TARGET_DIR": os.fspath(context.target / "lsp")},
    )
    run(
        [context.tools["python"], HERE / "rust-definition/tools/lsp_probe.py"],
        timeout=240,
        environment={"CARGO_TARGET_DIR": os.fspath(context.target / "readable-lsp")},
    )
    return "workspace/package fmt, check, Clippy, tests, docs, diagnostic and readable IMP LSP"


ARTIFACT_NAMES = (
    "definition-ir.json",
    "definition.k",
    "descriptor-bundle.json",
    "native-source.txt",
    "semantic-ir.json",
    "sources.json",
    "symbols.json",
)


def krs_base(krs: Path) -> list[str]:
    return [
        os.fspath(krs),
        "--manifest-path", os.fspath(RUST_MANIFEST),
        "--package", PACKAGE,
        "--definition", DEFINITION,
    ]


def phase_artifacts(context: Context) -> str:
    if context.krs is None:
        raise GateError("artifact phase lacks the phase-2 KRS binary")
    env = {"CARGO_TARGET_DIR": os.fspath(context.target)}
    check = run([context.krs, "check", *krs_base(context.krs)[1:]], timeout=300, environment=env)
    if "KRS check passed: 124 descriptors, 2 semantic modules" not in check.stdout:
        raise GateError(f"KRS check summary differs: {compact(check)}")

    expands = [
        run([context.krs, "expand", *krs_base(context.krs)[1:]], timeout=300, environment=env).stdout
        for _ in range(2)
    ]
    if expands[0] != expands[1]:
        raise GateError("repeated KRS expansion differs byte-for-byte")
    golden = EXPANSION_GOLDEN.read_text(encoding="utf-8")
    if expands[0] != golden:
        raise GateError("live KRS expansion differs from goldens/imp.expanded.rs")
    if EXPANDED_SOURCE.read_text(encoding="utf-8") != golden:
        raise GateError("replacement crate source differs from the reviewed expansion golden")

    emit_a = context.workspace / "emit-a"
    emit_b = context.workspace / "emit-b"
    for output in (emit_a, emit_b):
        run(
            [context.krs, "emit-k", *krs_base(context.krs)[1:], "--backend", "haskell", "--output", output],
            timeout=300,
            environment=env,
        )
    replacement_check = run(
        [
            context.krs,
            "check",
            "--manifest-path",
            EXPANDED_MANIFEST,
            "--package",
            EXPANDED_PACKAGE,
            "--definition",
            DEFINITION,
        ],
        timeout=300,
        environment=env,
    )
    if "KRS check passed: 83 descriptors, 2 semantic modules" not in replacement_check.stdout:
        raise GateError(f"replacement KRS check summary differs: {compact(replacement_check)}")
    replacement = context.workspace / "expanded-replacement"
    run(
        [
            context.krs,
            "emit-k",
            "--manifest-path",
            EXPANDED_MANIFEST,
            "--package",
            EXPANDED_PACKAGE,
            "--definition",
            DEFINITION,
            "--backend",
            "haskell",
            "--output",
            replacement,
        ],
        timeout=300,
        environment=env,
    )
    _verify_replacement_parity(emit_a, replacement)
    emitted_names = (
        ".krs-artifacts",
        "definition-ir.json",
        "definition.k",
        "descriptor-bundle.json",
        "semantic-ir.json",
        "sources.json",
        "symbols.json",
    )
    emitted_hashes = exact_directory(emit_a, emit_b, emitted_names)
    expected_artifacts = require_mapping(
        context.pins.get("artifact_sha256"), "pins.artifact_sha256"
    )
    expected_native = require_mapping(
        context.pins.get("native_artifact_sha256"), "pins.native_artifact_sha256"
    )
    expected_emitted = {
        ".krs-artifacts": expected_native.get(".krs-artifacts"),
        **{
            name: expected_artifacts.get(name)
            for name in emitted_names
            if name != ".krs-artifacts"
        },
    }
    if emitted_hashes != expected_emitted:
        raise GateError(
            f"emitted artifact hashes differ: expected={expected_emitted}, "
            f"actual={emitted_hashes}"
        )

    probes: list[Path] = []
    for name in ("probe-a", "probe-b"):
        output = context.workspace / name
        run(
            ["cargo", "run", "--locked", "--quiet", "--manifest-path", PROBE_MANIFEST, "--", output],
            timeout=600,
            environment=env,
        )
        probes.append(output)
    probe_hashes = exact_directory(probes[0], probes[1], ARTIFACT_NAMES)
    for name in (
        "definition-ir.json",
        "definition.k",
        "descriptor-bundle.json",
        "semantic-ir.json",
        "sources.json",
        "symbols.json",
    ):
        if emit_a.joinpath(name).read_bytes() != probes[0].joinpath(name).read_bytes():
            raise GateError(f"CLI and production API probe differ: {name}")

    expected = expected_artifacts
    if probe_hashes != expected:
        raise GateError(f"artifact pins differ: expected={expected}, actual={probe_hashes}")
    context.artifacts = probes[0]
    context.artifact_hashes = probe_hashes
    return f"124 descriptors; deterministic reviewed Rust expansion; 83-descriptor replacement parity; six repeated CLI/API source artifacts; sha256={hashlib.sha256(canonical(probe_hashes).encode()).hexdigest()}"


def compile_source_definitions(context: Context) -> None:
    if context.artifacts is None:
        raise GateError("source compilation lacks deterministic artifacts")
    definition_source = context.artifacts / "definition.k"
    claim_free, labels = _claim_free_source(definition_source.read_text(encoding="utf-8"))
    actual_source = context.workspace / "actual-execution.k"
    actual_source.write_text(claim_free, encoding="utf-8")
    if labels != context.pins.get("claim_labels"):
        raise GateError("emitted claim order differs from its exact pin")

    actual = context.workspace / "actual-execution-kompiled"
    reference = context.workspace / "reference-execution-kompiled"
    actual_failure = context.workspace / "actual-execution-llvm-kompiled"
    reference_failure = context.workspace / "reference-execution-llvm-kompiled"
    upstream = (
        ROOT.parent
        / "inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics"
    )
    run(
        [
            context.tools["kompile"], actual_source,
            "--backend", "haskell", "--main-module", MODULE,
            "--syntax-module", MODULE, "--emit-json",
            "--output-definition", actual,
        ],
        timeout=600,
    )
    run(
        [
            context.tools["kompile"], actual_source,
            "--backend", "llvm", "--main-module", MODULE,
            "--syntax-module", MODULE, "--emit-json",
            "--output-definition", actual_failure,
        ],
        timeout=900,
    )
    run(
        [
            context.tools["kompile"], HERE / "../m3d/fixtures/static-adjunct.k",
            "-I", upstream, "--backend", "llvm",
            "--main-module", REFERENCE_MODULE,
            "--syntax-module", REFERENCE_SYNTAX_MODULE, "--emit-json",
            "--output-definition", reference_failure,
        ],
        timeout=900,
    )
    run(
        [
            context.tools["kompile"], HERE / "../m3d/fixtures/static-adjunct.k",
            "-I", upstream, "--backend", "haskell",
            "--main-module", REFERENCE_MODULE,
            "--syntax-module", REFERENCE_SYNTAX_MODULE, "--emit-json",
            "--output-definition", reference,
        ],
        timeout=600,
    )
    for directory in (actual, reference):
        for name in ("parsed.json", "compiled.json", "definition.kore"):
            if not directory.joinpath(name).is_file():
                raise GateError(f"source frontend omitted {directory.name}/{name}")
    context.actual_definition = actual
    context.reference_definition = reference
    context.actual_failure_definition = actual_failure
    context.reference_failure_definition = reference_failure


def _projection_policy(raw: Any):
    sys.path.insert(0, os.fspath(HERE / "oracle"))
    from source_definition import ProjectionPolicy

    value = dict(require_mapping(raw, "projection policy"))
    for key in (
        "identity_labels", "identity_sorts", "identity_names",
        "known_attributes", "metadata_attributes",
        "closed_module_prefixes",
    ):
        if key in value:
            value[key] = frozenset(value[key])
    for field in ("imports_by_origin", "supplemental_imports_by_origin"):
        if field in value:
            value[field] = {
                key: tuple(child) for key, child in value[field].items()
            }
    return ProjectionPolicy(**value)


def phase_source_definition(context: Context) -> str:
    compile_source_definitions(context)
    assert context.reference_definition is not None
    assert context.actual_definition is not None
    sys.path.insert(0, os.fspath(HERE / "oracle"))
    from source_definition import compare_definitions, load_definition

    policies = require_mapping(context.pins.get("source_definition"), "pins.source_definition")
    if policies.get("status") != "ready":
        raise GateError(str(policies.get("blocker", "source-definition policy is not ready")))
    files = require_mapping(policies.get("files"), "source_definition.files")
    if set(files) != {"parsed.json", "compiled.json"}:
        raise GateError("source-definition policies must cover parsed.json and compiled.json")
    comparison = {}
    for filename in ("parsed.json", "compiled.json"):
        file_policy = require_mapping(files[filename], f"source_definition.files.{filename}")
        if set(file_policy) != {
            "reference_ignored_sha256", "actual_ignored_sha256",
            "reference_supplemental_sha256", "actual_supplemental_sha256",
            "compatible_sentence_pairs",
        }:
            raise GateError(f"{filename} source compatibility policy has unknown fields")
        reference_raw = dict(require_mapping(policies.get("reference"), "source_definition.reference"))
        actual_raw = dict(require_mapping(policies.get("actual"), "source_definition.actual"))
        reference_raw["ignored_sentence_sha256"] = require_mapping(
            file_policy["reference_ignored_sha256"],
            f"source_definition.files.{filename}.reference_ignored_sha256",
        )
        actual_raw["ignored_sentence_sha256"] = require_mapping(
            file_policy["actual_ignored_sha256"],
            f"source_definition.files.{filename}.actual_ignored_sha256",
        )
        reference_raw["supplemental_sentence_sha256"] = require_mapping(
            file_policy["reference_supplemental_sha256"],
            f"source_definition.files.{filename}.reference_supplemental_sha256",
        )
        actual_raw["supplemental_sentence_sha256"] = require_mapping(
            file_policy["actual_supplemental_sha256"],
            f"source_definition.files.{filename}.actual_supplemental_sha256",
        )
        comparison[filename] = compare_definitions(
            load_definition(context.reference_definition / filename),
            load_definition(context.actual_definition / filename),
            _projection_policy(reference_raw),
            _projection_policy(actual_raw),
            file_policy["compatible_sentence_pairs"],
        )
    expected = require_mapping(policies.get("expected"), "source_definition.expected")
    observed = {
        "parsed_reference_sha256": comparison["parsed.json"].baseline_sha256,
        "parsed_actual_sha256": comparison["parsed.json"].actual_sha256,
        "compiled_reference_sha256": comparison["compiled.json"].baseline_sha256,
        "compiled_actual_sha256": comparison["compiled.json"].actual_sha256,
        "parsed_sentence_count": comparison["parsed.json"].sentence_count,
        "compiled_sentence_count": comparison["compiled.json"].sentence_count,
    }
    if observed != expected:
        raise GateError(f"source-definition evidence pin differs: {observed}")
    return f"parsed/compiled fail-closed projection: {observed}"


def phase_native(context: Context) -> str:
    if context.krs is None or context.artifacts is None or context.actual_definition is None:
        raise GateError("native phase lacks CLI, artifacts, or source definition")
    env = {"CARGO_TARGET_DIR": os.fspath(context.target)}
    llvm_evidence: list[subprocess.CompletedProcess[str]] = []
    for name in ("llvm-failure-a", "llvm-failure-b"):
        output = context.workspace / name
        process = run(
            [
                context.krs, "build", *krs_base(context.krs)[1:],
                "--backend", "llvm", "--output", output,
            ],
            timeout=900,
            environment=env,
            check=False,
        )
        if process.returncode != 1 or output.exists():
            raise GateError(
                f"LLVM existential capability boundary differs: rc={process.returncode}, "
                f"output_exists={output.exists()}"
            )
        llvm_evidence.append(process)
    if (
        llvm_evidence[0].stdout != llvm_evidence[1].stdout
        or llvm_evidence[0].stderr != llvm_evidence[1].stderr
    ):
        raise GateError("repeated LLVM capability diagnostics differ byte-for-byte")
    diagnostic_text = llvm_evidence[0].stdout + llvm_evidence[0].stderr
    envelopes = []
    for line in diagnostic_text.splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise GateError(f"LLVM capability boundary emitted non-JSON: {line!r}") from error
        if not isinstance(value, dict) or (
            value.get("schema_version") != 1
            or value.get("stage") != "backend-capability"
            or value.get("code") != "UnsupportedExistentialVariable"
            or value.get("severity") != "error"
        ):
            raise GateError("LLVM capability diagnostic lost its typed classification")
        envelopes.append(value)
    if len(envelopes) != 6:
        raise GateError(f"expected six deduplicated LLVM diagnostics, found {len(envelopes)}")
    llvm_digest = hashlib.sha256(diagnostic_text.encode()).hexdigest()
    expected_llvm = context.pins.get("native_comparison", {}).get("llvm_failure_sha256")
    if llvm_digest != expected_llvm:
        raise GateError(
            f"LLVM capability diagnostic hash differs: expected={expected_llvm}, actual={llvm_digest}"
        )

    builds: list[Path] = []
    for name in ("native-a", "native-b"):
        output = context.workspace / name
        run(
            [context.krs, "build", *krs_base(context.krs)[1:], "--backend", "haskell", "--output", output],
            timeout=900,
            environment=env,
        )
        builds.append(output)
    native_files = tuple(context.pins.get("native_artifact_sha256", {}).keys())
    if not native_files:
        raise GateError("native artifact set is absent from pins.json")
    observed = exact_directory(builds[0], builds[1], native_files)
    if observed != context.pins.get("native_artifact_sha256"):
        raise GateError(f"native artifact hashes differ: {observed}")

    native_kore = builds[0] / "definition.kore"
    reference_kore = context.actual_definition / "definition.kore"
    comparator = [
        "cargo", "run", "--locked", "--quiet", "--manifest-path", NATIVE_MANIFEST,
        "--bin", "krs-m4-native-comparator", "--",
        reference_kore, native_kore, MODULE,
    ]
    native_policy = require_mapping(context.pins.get("native_comparison"), "pins.native_comparison")
    expected_native_policy_fields = {
        "status", "label_map", "reference_claims_module", "llvm_failure_sha256"
    }
    if set(native_policy) != expected_native_policy_fields or native_policy.get("status") != "ready":
        raise GateError("native comparison policy is not the exact ready schema")
    # K's frontend rejects claims in an executable definition.  Compile the
    # exact emitted claims as a supplemental spec through the supported
    # kprove --dry-run route, then require the comparator to merge only that
    # one-import/claims-only KORE module.
    execution_source = context.workspace / "actual-execution.k"
    _, labels, claim_source = _split_emitted_source(
        context.artifacts.joinpath("definition.k").read_text(encoding="utf-8")
    )
    if labels != context.pins.get("claim_labels"):
        raise GateError("native supplemental claim order differs")
    spec_module = str(native_policy.get("reference_claims_module"))
    if spec_module != f"{MODULE}-SPEC":
        raise GateError("native supplemental spec module pin differs")
    expected_label_map = {
        f"{spec_module}.{label}": f"{MODULE}.{label}"
        for label in context.pins.get("claim_labels", [])
    }
    if native_policy.get("label_map") != expected_label_map:
        raise GateError("native label map is not the exact 20-claim mapping")
    spec_path = context.workspace / "actual-claims-spec.k"
    spec_path.write_text(
        f'requires "{execution_source.name}"\n'
        'requires "imp-verification.k"\n\n'
        f'module {spec_module}\n'
        f'  imports {MODULE}\n'
        f'  imports IMP-VERIFICATION-SYNTAX\n\n{claim_source}endmodule\n',
        encoding="utf-8",
    )
    upstream = (
        ROOT.parent
        / "inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics"
    )
    spec_temp = context.workspace / "native-spec-temp"
    spec_temp.mkdir()
    run(
        [
            context.tools["kprove"], spec_path, "-I", upstream,
            "-d", context.actual_definition,
            "--spec-module", spec_module, "--dry-run", "--temp-dir", spec_temp,
        ],
        timeout=900,
    )
    spec_matches = sorted(spec_temp.rglob("spec.kore"))
    if len(spec_matches) != 1:
        raise GateError(f"kprove --dry-run emitted {len(spec_matches)} spec.kore files")
    comparator.extend(["--reference-claims", spec_matches[0], spec_module])
    for source, target in require_mapping(native_policy.get("label_map", {}), "native label map").items():
        comparator.extend(["--label", f"{source}={target}"])
    result = run(comparator, timeout=600, environment=env)
    expected_summary = (
        "PASS native KORE: reference=1206 native=1206 "
        "reference_projector_pairs=0 native_projector_pairs=40\n"
    )
    require_exact_summary(result, expected_summary, "native comparator")
    return result.stdout.strip()


def phase_behavior(context: Context) -> str:
    if (
        context.reference_definition is None
        or context.actual_definition is None
        or context.reference_failure_definition is None
        or context.actual_failure_definition is None
    ):
        raise GateError("behavior phase lacks compiled source routes")
    # The complete plan is deliberately constructed from corpus.json by a
    # separately tested fail-closed adapter.  Importing it here keeps the root
    # runner's ordered process ownership while retaining a small oracle API.
    sys.path.insert(0, os.fspath(HERE / "oracle"))
    import behavior
    adapter = getattr(behavior, "plan_from_manifest", None)
    policy_adapter = getattr(behavior, "term_policies", None)
    if adapter is None or policy_adapter is None:
        raise GateError("oracle behavior manifest adapter is missing")
    reference_policy, actual_policy = policy_adapter(context.pins["behavior"])
    plan = adapter(ROOT, context.corpus, context.pins["behavior"])
    summary = behavior.compare_behavior(
        kast=context.tools["kast"], krun=context.tools["krun"],
        reference=behavior.Route(
            context.reference_definition,
            reference_policy,
            context.reference_failure_definition,
        ),
        actual=behavior.Route(
            context.actual_definition,
            actual_policy,
            context.actual_failure_definition,
        ),
        plan=plan,
    )
    expected = require_mapping(context.pins["behavior"].get("expected"), "behavior.expected")
    observed = {
        "parse_count": summary.parse_count,
        "execution_count": summary.execution_count,
        "depth_state_count": summary.depth_state_count,
        "search_count": summary.search_count,
        "rejection_count": summary.rejection_count,
        "failure_count": summary.failure_count,
        "evidence_sha256": summary.evidence_sha256,
    }
    if observed != expected:
        raise GateError(f"behavior summary differs from pins: {observed}")
    return canonical(observed)


def phase_proofs(context: Context) -> str:
    proof_pins = require_mapping(context.pins.get("proof_outcomes"), "pins.proof_outcomes")
    if len(proof_pins) != 21:
        raise GateError(f"expected 21 proof invocations, found {len(proof_pins)}")
    harness = HERE / "oracle/run_proofs.py"
    if not harness.is_file():
        raise GateError("complete source/native proof harness is missing")
    result = run(
        [context.tools["python"], harness, "--pins", PINS_PATH, "--workspace", context.workspace / "proofs"],
        timeout=7200,
        environment={"CARGO_TARGET_DIR": os.fspath(context.target)},
    )
    expected_summary = (
        "PASS M4 proofs: reference_source=21 actual_source=21 "
        "dry_run_specs=21 native_haskell=21 native_unique_claims=20\n"
    )
    require_exact_summary(result, expected_summary, "proof harness")
    return result.stdout.strip()


def phase_compatibility(context: Context) -> str:
    if context.krs is None or context.artifacts is None:
        raise GateError("compatibility phase lacks CLI and deterministic artifacts")
    env = {"CARGO_TARGET_DIR": os.fspath(context.target)}
    commands = [
        [context.tools["python"], HERE / "compatibility/stable-names/probe.py", "--krs", context.krs],
        [context.tools["python"], HERE / "compatibility/diagnostics/rust-expansion/probe.py"],
        [context.tools["python"], HERE / "compatibility/diagnostics/rust-expansion/lsp_probe.py"],
        [context.tools["python"], HERE / "compatibility/diagnostics/krs-analysis/probe.py", "--krs", context.krs],
        [
            context.tools["python"], HERE / "compatibility/diagnostics/k-frontend/probe.py",
            "--definition", context.artifacts / "definition.k",
            "--sources", context.artifacts / "sources.json",
            "--authored", HERE / "rust-definition/src/claims.rs",
            "--source-relative-path", "src/claims.rs", "--token", "bool::and",
            "--kompile", context.tools["kompile"], "--module", MODULE,
            "--verification-definition", ROOT.parent
            / "inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics",
        ],
        [context.tools["python"], HERE / "compatibility/diagnostics/backend-capability/probe.py", "--krs", context.krs],
        [context.tools["python"], HERE / "compatibility/diagnostics/probe.py"],
    ]
    reports = []
    for command in commands:
        reports.append(run(command, timeout=900, environment=env).stdout.strip())
    digest = hashlib.sha256("\n".join(reports).encode()).hexdigest()
    expected = require_mapping(context.pins.get("compatibility"), "pins.compatibility")
    if expected.get("policy_version") != 1 or digest != expected.get("report_sha256"):
        raise GateError(f"live compatibility report hash differs: {digest}")
    return f"seven live compatibility probes; policy=1; sha256={digest}"


PHASES: tuple[tuple[str, Callable[[Context], str]], ...] = (
    ("preflight", phase_preflight),
    ("rust-and-lsp", phase_rust),
    ("deterministic-artifacts", phase_artifacts),
    ("source-definition", phase_source_definition),
    ("native-kore", phase_native),
    ("parser-execution-search", phase_behavior),
    ("bounded-proofs", phase_proofs),
    ("compatibility-reproduction", phase_compatibility),
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--audit-all", action="store_true")
    parser.add_argument(
        "--target-dir",
        type=Path,
        default=Path(
            os.environ.get(
                "KRS_M4_TARGET_DIR",
                os.fspath(Path(tempfile.gettempdir()) / "krs-m4-root-target"),
            )
        ),
    )
    arguments = parser.parse_args()
    pins = load_json(PINS_PATH)
    corpus = load_json(CORPUS_PATH)
    failures: list[tuple[str, str]] = []
    with tempfile.TemporaryDirectory(prefix="krs-m4-root-") as temporary:
        context = Context(pins, corpus, Path(temporary), arguments.target_dir.resolve())
        context.target.mkdir(parents=True, exist_ok=True)
        for index, (name, function) in enumerate(PHASES, start=1):
            try:
                detail = function(context)
            except Exception as error:
                failures.append((name, str(error)))
                print(f"FAIL M4.{index} {name}: {error}", file=sys.stderr, flush=True)
                if not arguments.audit_all:
                    break
            else:
                print(f"PASS M4.{index} {name}: {detail}", flush=True)
    if failures:
        if arguments.audit_all:
            print("M4 audit blockers:", file=sys.stderr)
            for name, error in failures:
                print(f"- {name}: {error}", file=sys.stderr)
        return 1
    summary = {
        "protocol": pins["schemas"]["protocol"],
        "ir_schema": pins["schemas"]["ir"],
        "k": pins["revisions"]["k"],
        "k_rust": pins["revisions"]["k_rust"],
        "proof_bounds": pins["proof_policy"],
        "artifacts": context.artifact_hashes,
        "compatibility_policy": pins["compatibility"]["policy_version"],
    }
    print(f"PASS M4 complete IMP: {canonical(summary)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except GateError as error:
        print(f"FAIL M4 setup: {error}", file=sys.stderr)
        raise SystemExit(1)
