#!/usr/bin/env python3
"""Ordered, fail-closed IMP complete-IMP release gate.

The default mode stops on the first failed evidence layer.  ``--audit-all``
continues only with layers whose prerequisites are independently available;
it never turns missing evidence into a skip or a pass.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field, replace
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Callable, Mapping, TypeVar, cast

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry  # noqa: E402
from support import lock  # noqa: E402
from support.checkouts import verify_checkout  # noqa: E402
from support.hashing import (  # noqa: E402
    canonical_json,
    exact_directory,
    json_sha256,
    sha256_file,
    sha256_text,
)
from support.kdefinition import emitted_claims  # noqa: E402
from support.krs import Invocation, build, fresh_deterministic_emissions  # noqa: E402
from support.parallel import settle_all, worker_count  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger, load_json, load_toml, table  # noqa: E402
from support.process import compact, run  # noqa: E402
from support.tools import checkout_scratch, executable, k_version_matches, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
PINS_PATH = HERE / "pins.json"
CORPUS_PATH = HERE / "corpus.json"
RUST_MANIFEST = HERE / "rust-definition/Cargo.toml"
EXPANSION_GOLDEN = HERE / "goldens/imp.expanded.rs"
EXPANDED_MANIFEST = HERE / "expanded-definition/Cargo.toml"
EXPANDED_SOURCE = HERE / "expanded-definition/src/imp.rs"
PROBE_MANIFEST = HERE / "oracle/artifact-probe/Cargo.toml"
NATIVE_MANIFEST = HERE / "native/Cargo.toml"
PACKAGE = "krs-imp-definition"
DEFINITION = "main"
MODULE = "KRS-IMP"
REFERENCE_MODULE = "KRS-IMP-STATIC"
REFERENCE_SYNTAX_MODULE = "KRS-IMP-STATIC-SYNTAX"
EXPANDED_PACKAGE = "krs-imp-expanded"
CLAIM_COUNT = 20
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


def require_exact_summary(
    process: subprocess.CompletedProcess[str], expected: str, phase: str
) -> None:
    """Reject a nominal PASS accompanied by missing, extra, or stderr output."""

    if process.stdout != expected or process.stderr:
        raise GateError(f"{phase} did not report its exact PASS summary: {compact(process)}")


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
            relations.append((canonical_json(grammar), name))
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
        normalized_ids.add(canonical_json(normalized.get("id")))
    if len(normalized_ids) != 54:
        raise GateError("replacement parity non-rule identities are not 54 unique items")

    normalized_declarations = []
    for declaration in declarations:
        if not isinstance(declaration, dict):
            raise GateError("replacement parity declaration entry is not an object")
        normalized = _normalize_imp_identity(declaration, alpha_names)
        if canonical_json(normalized.get("id")) in normalized_ids:
            normalized_declarations.append(normalized)
    if len(normalized_declarations) != 54:
        raise GateError(
            "replacement parity does not contain exactly 54 non-rule declaration records"
        )
    return (
        sorted(normalized_descriptors, key=canonical_json),
        sorted(normalized_declarations, key=canonical_json),
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


@dataclass
class Context:
    pins: Ledger
    corpus: dict[str, Any]
    workspace: Path
    target: Path
    tools: dict[str, str] = field(default_factory=dict)
    environment: dict[str, str] = field(default_factory=dict)


@dataclass(frozen=True)
class RustBuild:
    krs: Path

    @property
    def detail(self) -> str:
        return (
            "workspace/package fmt, check, Clippy, tests, docs, authored IMP MSRV, "
            "stable native frontend, diagnostic and readable IMP LSP"
        )


@dataclass(frozen=True)
class Artifacts:
    paths: Path
    hashes: Mapping[str, str]
    native_build: Path

    @property
    def detail(self) -> str:
        return (
            "124 descriptors; deterministic reviewed Rust expansion; 83-descriptor replacement parity; "
            "seven repeated CLI/API source artifacts; repeated claim-free LLVM and Haskell native builds; "
            f"sha256={json_sha256(self.hashes)}"
        )


@dataclass(frozen=True)
class SourceDefinitions:
    actual: Path
    reference: Path
    actual_failure: Path
    reference_failure: Path
    actual_execution_k: Path
    comparison: Mapping[str, Any]

    @property
    def detail(self) -> str:
        return f"parsed/compiled fail-closed projection: {self.comparison}"


def phase_preflight(context: Context) -> str:
    """Check the input pins: external checkouts, their files, the corpus, and tools.

    KRS source is deliberately not pinned; the later phases pin what KRS
    produces. Toolchain and schema versions come from `Krs.lock`.
    """

    pins = context.pins
    corpus = context.corpus
    if pins.get("schema") != 1 or pins.get("milestone") != "IMP":
        raise GateError("pins.json is not the exact IMP schema-1 ledger")
    if corpus.get("schema") != 2:
        raise GateError("corpus.json is not schema 2")
    if sha256_file(CORPUS_PATH) != pins.get("corpus_sha256"):
        raise GateError("corpus.json hash differs from pins.json")

    # IMP reuses the IMP state, IMP control flow, and IMP static semantics corpora; each is pinned in its own gate ledger.
    ledgers = table(corpus.get("input_ledgers"), "corpus.input_ledgers")
    if set(ledgers) != {"imp-state", "imp-control-flow", "imp-static-semantics"}:
        raise GateError("corpus must name exactly the IMP state, IMP control flow, and IMP static semantics input ledgers")
    for name, raw in ledgers.items():
        path = ROOT / str(table(raw, f"input ledger {name}").get("path"))
        ledger = Ledger(path)
        for relative, expected in ledger.table("corpus_sha256").items():
            if sha256_file(path.parent / relative) != expected:
                raise GateError(f"{name} corpus hash differs: {relative}")

    checkouts = {
        "k": ROOT.parent / "inspirations/runtimeverification/k",
        "imp": ROOT.parent / "inspirations/runtimeverification/imp-semantics",
        "k_rust": ROOT.parent / "inspirations/midnightntwrk/k-rust-krs-main",
    }
    expected = {
        "k": lock.k_commit(),
        "imp": table(table(pins.get("revisions"), "pins.revisions").get("imp"), "revisions.imp").get("commit"),
        "k_rust": str(lock.value("k_rust", "commit")),
    }
    # A clean checkout at the pinned commit fixes every input file; the gate
    # does not digest external files separately.
    for name, path in checkouts.items():
        verify_checkout(path, str(expected[name]), label=name)
    for crate, key in (
        ("k-rust", "version"), ("k-rust-backend", "backend_version"), ("k-rust-kore", "kore_version")
    ):
        manifest = load_toml(checkouts["k_rust"] / "crates" / crate / "Cargo.toml")
        if table(manifest.get("package"), f"{crate} package").get("version") != lock.value("k_rust", key):
            raise GateError(f"{crate} version differs from Krs.lock [k_rust] {key}")

    tools = (
        "cargo", "rustc", "rustfmt", "clippy-driver", "rust-analyzer", "git",
        "kompile", "kast", "krun", "kprove", "kore-exec", "llvm-kompile", "z3",
    )
    context.tools = {name: executable(name) for name in tools}
    version = run([context.tools["kompile"], "--version"], timeout=30)
    if not k_version_matches(version, lock.k_version()):
        raise GateError(f"K tool version differs from Krs.lock: {compact(version)}")
    pyk_python = checkouts["k"] / "pyk/.venv/bin/python"
    if not pyk_python.is_file():
        raise GateError("pinned K checkout pyk virtualenv is missing")
    pyk = run(
        [
            pyk_python, "-c",
            "import importlib.metadata; print(importlib.metadata.version('kframework'))",
        ],
        timeout=30,
    ).stdout.strip()
    if pyk != lock.value("k", "pyk_version"):
        raise GateError(f"pinned checkout pyk version differs from Krs.lock: {pyk}")
    kore = run([context.tools["kore-exec"], "--version"], timeout=30).stdout.strip()
    if kore != lock.value("k", "kore_exec_version"):
        raise GateError(f"kore-exec version differs from Krs.lock: {kore}")
    llvm = Path(context.tools["llvm-kompile"]).resolve()
    if f"llvm-backend-{lock.value('k', 'llvm_backend_version')}" not in llvm.as_posix():
        raise GateError("LLVM backend version differs from Krs.lock")
    z3 = run([context.tools["z3"], "--version"], timeout=30).stdout.strip()
    if z3 != f"Z3 version {lock.z3_version()} - 64 bit":
        raise GateError(f"Z3 version differs from Krs.lock: {z3}")
    context.environment = z3_environment()
    context.tools["pyk_python"] = os.fspath(pyk_python)
    context.tools["python"] = os.fspath(pyk_python)
    msrv = run(["rustc", f"+{lock.msrv()}", "--version"], timeout=30).stdout.strip()
    if not msrv.startswith(f"rustc {lock.msrv()} "):
        raise GateError(f"MSRV toolchain differs from Krs.lock: {msrv}")
    native_rust = run(["rustc", "+stable", "--version"], timeout=30).stdout.strip()
    lock.require_stable_at_least_msrv(native_rust)
    return (
        f"external checkouts and files, corpus, tools, KRS schema {lock.krs_ir_schema()}, "
        f"MSRV {lock.msrv()}, and {native_rust}"
    )


def phase_rust(context: Context) -> RustBuild:
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
    commands = [
        ["cargo", "fmt", "--all", "--check"],
        ["cargo", "check", "--workspace", "--all-targets", "--locked"],
        ["cargo", "clippy", "--workspace", "--all-targets", "--locked", "--", "-D", "warnings"],
        ["cargo", "test", "--workspace", "--locked"],
        ["cargo", "test", "--manifest-path", os.fspath(RUST_MANIFEST), "--locked"],
        ["cargo", "test", "--manifest-path", os.fspath(EXPANDED_MANIFEST), "--locked"],
        ["cargo", "test", "--manifest-path", os.fspath(NATIVE_MANIFEST), "--locked"],
    ]
    for command in commands:
        run(command, timeout=900, environment=env)
    # Clean k-rust enforces MSRV 1.88 since 758a3a9, so the exact-MSRV check
    # now covers the workspace and every helper beside the stable-toolchain
    # qualification above. Earlier k-rust used if-let guards, which 1.88 rejects.
    run(
        [
            "cargo", f"+{lock.msrv()}", "check", "--workspace",
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
            "transport_grammar", "builtin_registry_is_complete_exact_and_alias_safe",
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

    krs = build(env, target=context.target, timeout=600)
    check_packages("imp", env=env, target_dir=context.target)
    # These live LSP probes select authored tokens. A mere rust-analyzer
    # --version check is deliberately insufficient evidence.
    run(
        [context.tools["python"], HERE / "compatibility/diagnostics/rust-expansion/lsp_probe.py"],
        timeout=240,
        environment={
            **context.environment,
            "CARGO_TARGET_DIR": os.fspath(context.target / "lsp"),
        },
    )
    run(
        [context.tools["python"], HERE / "rust-definition/tools/lsp_probe.py"],
        timeout=240,
        environment={
            **context.environment,
            "CARGO_TARGET_DIR": os.fspath(context.target / "readable-lsp"),
        },
    )
    return RustBuild(krs)


ARTIFACT_NAMES = (
    "definition-ir.json",
    "definition.k",
    "descriptor-bundle.json",
    "native-source.txt",
    "semantic-ir.json",
    "sources.json",
    "spec.k",
    "symbols.json",
)
NATIVE_ARTIFACTS = (".krs-artifacts", "definition.kore", "macros.kore", "syntaxDefinition.kore")


def krs_invocation(krs: Path) -> Invocation:
    return Invocation(krs, RUST_MANIFEST, PACKAGE, DEFINITION)


def native_artifacts(context: Context, krs: Path, env: Mapping[str, str]) -> Path:
    """Build the native definition twice per backend and pin both.

    The concrete LLVM backend does not prove, so its build omits every claim.
    """

    llvm_builds: list[Path] = []
    for name in ("llvm-a", "llvm-b"):
        output = context.workspace / name
        process = run(
            krs_invocation(krs).argv("build", "--backend", "llvm", "--output", output),
            timeout=900,
            environment=env,
        )
        omitted = f"omitted {CLAIM_COUNT} claims: the llvm backend executes but does not prove\n"
        if not process.stdout.endswith(omitted):
            raise GateError(f"LLVM build did not report its omitted claims: {process.stdout!r}")
        llvm_builds.append(output)
    for name, digest in exact_directory(llvm_builds[0], llvm_builds[1], NATIVE_ARTIFACTS).items():
        context.pins.expect(("llvm_artifact_sha256", name), digest)

    builds: list[Path] = []
    for name in ("native-a", "native-b"):
        output = context.workspace / name
        run(
            krs_invocation(krs).argv("build", "--backend", "haskell", "--output", output),
            timeout=900,
            environment=env,
        )
        builds.append(output)
    native_files = tuple(context.pins.get("native_artifact_sha256", {}).keys())
    if not native_files:
        raise GateError("native artifact set is absent from pins.json")
    for name, digest in exact_directory(builds[0], builds[1], native_files).items():
        context.pins.expect(("native_artifact_sha256", name), digest)
    return builds[0]


def phase_artifacts(context: Context, rust_build: RustBuild) -> Artifacts:
    krs = rust_build.krs
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
    check = run(krs_invocation(krs).argv("check"), timeout=300, environment=env)
    if "KRS check passed: 124 descriptors, 2 semantic modules" not in check.stdout:
        raise GateError(f"KRS check summary differs: {compact(check)}")

    expands = [
        run(krs_invocation(krs).argv("expand"), timeout=300, environment=env).stdout
        for _ in range(2)
    ]
    if expands[0] != expands[1]:
        raise GateError("repeated KRS expansion differs byte-for-byte")
    golden = EXPANSION_GOLDEN.read_text(encoding="utf-8")
    if expands[0] != golden:
        raise GateError("live KRS expansion differs from goldens/imp.expanded.rs")
    if EXPANDED_SOURCE.read_text(encoding="utf-8") != golden:
        raise GateError("replacement crate source differs from the reviewed expansion golden")

    emit_a, emit_b = fresh_deterministic_emissions(
        krs_invocation(krs), context.workspace,
        extra=("--backend", "haskell"), environment=env, timeout=300,
    )
    replacement_invocation = Invocation(krs, EXPANDED_MANIFEST, EXPANDED_PACKAGE, DEFINITION)
    replacement_check = replacement_invocation.run("check", timeout=300, environment=env)
    if "KRS check passed: 83 descriptors, 2 semantic modules" not in replacement_check.stdout:
        raise GateError(f"replacement KRS check summary differs: {compact(replacement_check)}")
    replacement = context.workspace / "expanded-replacement"
    replacement_invocation.run(
        "emit-k", "--backend", "haskell", "--output", replacement,
        timeout=300, environment=env,
    )
    _verify_replacement_parity(emit_a, replacement)
    emitted_names = (
        ".krs-artifacts",
        "definition-ir.json",
        "definition.k",
        "descriptor-bundle.json",
        "semantic-ir.json",
        "sources.json",
        "spec.k",
        "symbols.json",
    )
    for name, digest in exact_directory(emit_a, emit_b, emitted_names).items():
        # The ownership marker is the same file `krs build` writes natively.
        table_name = "native_artifact_sha256" if name == ".krs-artifacts" else "artifact_sha256"
        context.pins.expect((table_name, name), digest)

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
        "spec.k",
        "symbols.json",
    ):
        if emit_a.joinpath(name).read_bytes() != probes[0].joinpath(name).read_bytes():
            raise GateError(f"CLI and production API probe differ: {name}")

    for name, digest in probe_hashes.items():
        context.pins.expect(("artifact_sha256", name), digest)
    native_build = native_artifacts(context, krs, env)
    return Artifacts(probes[0], probe_hashes, native_build)


def compile_source_definitions(context: Context, artifacts: Artifacts) -> SourceDefinitions:
    labels, _ = emitted_claims(artifacts.paths, MODULE, CLAIM_COUNT)
    actual_source = context.workspace / "actual-execution.k"
    shutil.copy2(artifacts.paths / "definition.k", actual_source)
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
            context.tools["kompile"], HERE / "../imp_static_semantics/fixtures/static-adjunct.k",
            "-I", upstream, "--backend", "llvm",
            "--main-module", REFERENCE_MODULE,
            "--syntax-module", REFERENCE_SYNTAX_MODULE, "--emit-json",
            "--output-definition", reference_failure,
        ],
        timeout=900,
    )
    run(
        [
            context.tools["kompile"], HERE / "../imp_static_semantics/fixtures/static-adjunct.k",
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
    return SourceDefinitions(actual, reference, actual_failure, reference_failure, actual_source, {})


def _projection_policy(raw: Any):
    sys.path.insert(0, os.fspath(HERE / "oracle"))
    from source_definition import ProjectionPolicy

    value = dict(table(raw, "projection policy"))
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


def phase_source_definition(context: Context, artifacts: Artifacts) -> SourceDefinitions:
    definitions = compile_source_definitions(context, artifacts)
    sys.path.insert(0, os.fspath(HERE / "oracle"))
    from source_definition import compare_definitions, load_definition

    policies = table(context.pins.get("source_definition"), "pins.source_definition")
    if policies.get("status") != "ready":
        raise GateError(str(policies.get("blocker", "source-definition policy is not ready")))
    files = table(policies.get("files"), "source_definition.files")
    if set(files) != {"parsed.json", "compiled.json"}:
        raise GateError("source-definition policies must cover parsed.json and compiled.json")
    comparison = {}
    for filename in ("parsed.json", "compiled.json"):
        file_policy = table(files[filename], f"source_definition.files.{filename}")
        if set(file_policy) != {
            "reference_ignored_sha256", "actual_ignored_sha256",
            "reference_supplemental_sha256", "actual_supplemental_sha256",
            "compatible_sentence_pairs",
        }:
            raise GateError(f"{filename} source compatibility policy has unknown fields")
        reference_raw = dict(table(policies.get("reference"), "source_definition.reference"))
        actual_raw = dict(table(policies.get("actual"), "source_definition.actual"))
        reference_raw["ignored_sentence_sha256"] = table(
            file_policy["reference_ignored_sha256"],
            f"source_definition.files.{filename}.reference_ignored_sha256",
        )
        actual_raw["ignored_sentence_sha256"] = table(
            file_policy["actual_ignored_sha256"],
            f"source_definition.files.{filename}.actual_ignored_sha256",
        )
        reference_raw["supplemental_sentence_sha256"] = table(
            file_policy["reference_supplemental_sha256"],
            f"source_definition.files.{filename}.reference_supplemental_sha256",
        )
        actual_raw["supplemental_sentence_sha256"] = table(
            file_policy["actual_supplemental_sha256"],
            f"source_definition.files.{filename}.actual_supplemental_sha256",
        )
        comparison[filename] = compare_definitions(
            load_definition(definitions.reference / filename),
            load_definition(definitions.actual / filename),
            _projection_policy(reference_raw),
            _projection_policy(actual_raw),
            file_policy["compatible_sentence_pairs"],
        )
    observed = {
        "parsed_reference_sha256": comparison["parsed.json"].baseline_sha256,
        "parsed_actual_sha256": comparison["parsed.json"].actual_sha256,
        "compiled_reference_sha256": comparison["compiled.json"].baseline_sha256,
        "compiled_actual_sha256": comparison["compiled.json"].actual_sha256,
        "parsed_sentence_count": comparison["parsed.json"].sentence_count,
        "compiled_sentence_count": comparison["compiled.json"].sentence_count,
    }
    context.pins.expect(("source_definition", "expected"), observed)
    return replace(definitions, comparison=observed)


def phase_native(context: Context, artifacts: Artifacts, definitions: SourceDefinitions) -> str:
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
    native_kore = artifacts.native_build / "definition.kore"
    reference_kore = definitions.actual / "definition.kore"
    comparator = [
        "cargo", "run", "--locked", "--quiet", "--manifest-path", NATIVE_MANIFEST,
        "--bin", "krs-imp-native-comparator", "--",
        reference_kore, native_kore, MODULE,
    ]
    native_policy = table(context.pins.get("native_comparison"), "pins.native_comparison")
    expected_native_policy_fields = {"status", "label_map", "reference_claims_module"}
    if set(native_policy) != expected_native_policy_fields or native_policy.get("status") != "ready":
        raise GateError("native comparison policy is not the exact ready schema")
    # K's frontend rejects claims in an executable definition, so emit-k
    # writes them to spec.k.  Compile the exact emitted claims as a
    # supplemental spec through the supported kprove --dry-run route, then
    # require the comparator to merge only that one-import/claims-only KORE
    # module.
    execution_source = definitions.actual_execution_k
    labels, claim_source = emitted_claims(artifacts.paths, MODULE, CLAIM_COUNT)
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
            "-d", definitions.actual,
            "--spec-module", spec_module, "--dry-run", "--temp-dir", spec_temp,
        ],
        timeout=900,
    )
    spec_matches = sorted(spec_temp.rglob("spec.kore"))
    if len(spec_matches) != 1:
        raise GateError(f"kprove --dry-run emitted {len(spec_matches)} spec.kore files")
    comparator.extend(["--reference-claims", spec_matches[0], spec_module])
    for source, target in table(native_policy.get("label_map", {}), "native label map").items():
        comparator.extend(["--label", f"{source}={target}"])
    result = run(comparator, timeout=600, environment=env)
    expected_summary = (
        "PASS native KORE: reference=1188 native=1188 "
        "reference_projector_pairs=0 native_projector_pairs=39\n"
    )
    require_exact_summary(result, expected_summary, "native comparator")
    return result.stdout.strip()


def phase_behavior(context: Context, definitions: SourceDefinitions) -> str:
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
            definitions.reference,
            reference_policy,
            definitions.reference_failure,
        ),
        actual=behavior.Route(
            definitions.actual,
            actual_policy,
            definitions.actual_failure,
        ),
        plan=plan,
    )
    observed = {
        "parse_count": summary.parse_count,
        "execution_count": summary.execution_count,
        "depth_state_count": summary.depth_state_count,
        "search_count": summary.search_count,
        "rejection_count": summary.rejection_count,
        "failure_count": summary.failure_count,
        "evidence_sha256": summary.evidence_sha256,
    }
    context.pins.expect(("behavior", "expected"), observed)
    return canonical_json(observed)


def phase_proofs(context: Context, rust_build: RustBuild) -> str:
    proof_pins = table(context.pins.get("proof_outcomes"), "pins.proof_outcomes")
    if len(proof_pins) != 21:
        raise GateError(f"expected 21 proof invocations, found {len(proof_pins)}")
    harness = HERE / "oracle/run_proofs.py"
    if not harness.is_file():
        raise GateError("complete source/native proof harness is missing")
    result = run(
        [
            context.tools["python"], harness, "--pins", PINS_PATH,
            "--workspace", context.workspace / "proofs",
            "--k-version", lock.k_version(), "--k-commit", lock.k_commit(),
            "--krs", rust_build.krs,
        ],
        timeout=7200,
        environment={
            **context.environment,
            "CARGO_TARGET_DIR": os.fspath(context.target),
        },
    )
    expected_summary = (
        "PASS IMP proofs: reference_source=21 actual_source=21 "
        "dry_run_specs=21 native_haskell=21 native_unique_claims=20\n"
    )
    require_exact_summary(result, expected_summary, "proof harness")
    return result.stdout.strip()


def phase_compatibility(context: Context, rust_build: RustBuild, artifacts: Artifacts) -> str:
    env = {
        **context.environment,
        "CARGO_TARGET_DIR": os.fspath(context.target),
        "KRS_IMP_PROBE_TARGET_ROOT": os.fspath(context.target / "probes"),
    }
    commands = [
        [context.tools["python"], HERE / "compatibility/stable-names/probe.py", "--krs", rust_build.krs],
        [context.tools["python"], HERE / "compatibility/diagnostics/rust-expansion/probe.py"],
        [context.tools["python"], HERE / "compatibility/diagnostics/rust-expansion/lsp_probe.py"],
        [context.tools["python"], HERE / "compatibility/diagnostics/krs-analysis/probe.py", "--krs", rust_build.krs],
        [
            context.tools["python"], HERE / "compatibility/diagnostics/k-frontend/probe.py",
            "--spec", artifacts.paths / "spec.k",
            "--sources", artifacts.paths / "sources.json",
            "--authored", HERE / "rust-definition/src/claims.rs",
            "--source-relative-path", "src/claims.rs", "--token", "bool::and",
            "--kompile", context.tools["kompile"], "--module", MODULE,
            "--verification-definition", ROOT.parent
            / "inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics",
        ],
    ]
    # Each probe owns its Cargo target and scratch directories. Reports keep
    # this order.
    groups = [[command] for command in commands]

    def run_group(group: list[list[Any]]) -> list[str]:
        return [run(command, timeout=900, environment=env).stdout.strip() for command in group]

    outcomes = settle_all(
        [lambda group=group: run_group(group) for group in groups],
        worker_count("KRS_IMP_ORACLE_WORKERS", 4),
    )
    reports = [report for outcome in outcomes for report in outcome.get()]
    digest = sha256_text("\n".join(reports))
    if table(context.pins.get("compatibility"), "pins.compatibility").get("policy_version") != 1:
        raise GateError("compatibility policy version differs from 1")
    context.pins.expect(("compatibility", "report_sha256"), digest)
    return f"five live compatibility probes; policy=1; sha256={digest}"


PHASES = (
    "preflight",
    "rust-and-lsp",
    "deterministic-artifacts",
    "source-definition",
    "native-kore",
    "parser-execution-search",
    "bounded-proofs",
    "compatibility-reproduction",
)
ARTIFACT_PHASES = 3
"""Preflight, the Rust checks, and every emitted artifact; `--artifacts-only` stops here."""


class StopPhases(Exception):
    """End the default gate after its first failed phase."""


PhaseResult = str | RustBuild | Artifacts | SourceDefinitions
T = TypeVar("T", bound=PhaseResult)


def run_phase(
    index: int,
    name: str,
    requires: tuple[str, ...],
    passed: set[str],
    failures: list[tuple[str, str]],
    audit_all: bool,
    function: Callable[[], T],
) -> T | None:
    for dependency in requires:
        if dependency not in passed:
            print(f"SKIP {name}: requires {dependency}", flush=True)
            return None
    try:
        result = function()
    except Exception as error:
        failures.append((name, str(error)))
        print(f"FAIL IMP.{index} {name}: {error}", file=sys.stderr, flush=True)
        if not audit_all:
            raise StopPhases from error
        return None
    passed.add(name)
    detail = result if isinstance(result, str) else result.detail
    print(f"PASS IMP.{index} {name}: {detail}", flush=True)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--audit-all", action="store_true")
    parser.add_argument(
        "--record",
        action="store_true",
        help="run every phase and rewrite the output pins it measured",
    )
    parser.add_argument(
        "--target-dir",
        type=Path,
        default=Path(
            os.environ.get(
                "KRS_IMP_TARGET_DIR",
                os.fspath(checkout_scratch() / "imp-root-target"),
            )
        ),
    )
    parser.add_argument(
        "--artifacts-only",
        action="store_true",
        help=(
            f"stop after IMP.{ARTIFACT_PHASES}, with every emitted artifact compared to its pin; "
            "skip the source, native KORE, behavior, proof, and compatibility comparisons"
        ),
    )
    arguments = parser.parse_args()
    if arguments.artifacts_only and (arguments.record or arguments.audit_all):
        parser.error("--artifacts-only cannot be combined with --record or --audit-all")
    pins = Ledger(PINS_PATH, record=arguments.record, artifacts_only=arguments.artifacts_only)
    corpus = load_json(CORPUS_PATH)
    failures: list[tuple[str, str]] = []
    passed: set[str] = set()
    artifacts: Artifacts | None = None
    with tempfile.TemporaryDirectory(prefix="krs-imp-root-") as temporary:
        context = Context(pins, corpus, Path(temporary), arguments.target_dir.resolve())
        context.target.mkdir(parents=True, exist_ok=True)
        try:
            run_phase(1, PHASES[0], (), passed, failures, arguments.audit_all,
                      lambda: phase_preflight(context))
            rust_build = run_phase(2, PHASES[1], (PHASES[0],), passed, failures,
                                   arguments.audit_all, lambda: phase_rust(context))
            artifacts = run_phase(3, PHASES[2], (PHASES[1],), passed, failures,
                                  arguments.audit_all,
                                  lambda: phase_artifacts(context, cast(RustBuild, rust_build)))
            if not arguments.artifacts_only:
                definitions = run_phase(
                    4, PHASES[3], (PHASES[2],), passed, failures, arguments.audit_all,
                    lambda: phase_source_definition(context, cast(Artifacts, artifacts)),
                )
                run_phase(
                    5, PHASES[4], (PHASES[2], PHASES[3]), passed, failures,
                    arguments.audit_all,
                    lambda: phase_native(context, cast(Artifacts, artifacts),
                                         cast(SourceDefinitions, definitions)),
                )
                run_phase(
                    6, PHASES[5], (PHASES[3],), passed, failures, arguments.audit_all,
                    lambda: phase_behavior(context, cast(SourceDefinitions, definitions)),
                )
                run_phase(7, PHASES[6], (PHASES[1],), passed, failures, arguments.audit_all,
                          lambda: phase_proofs(context, cast(RustBuild, rust_build)))
                run_phase(
                    8, PHASES[7], (PHASES[1], PHASES[2]), passed, failures,
                    arguments.audit_all,
                    lambda: phase_compatibility(context, cast(RustBuild, rust_build),
                                                cast(Artifacts, artifacts)),
                )
        except StopPhases:
            pass
    if failures:
        if arguments.audit_all:
            print("IMP audit blockers:", file=sys.stderr)
            for name, error in failures:
                print(f"- {name}: {error}", file=sys.stderr)
        return 1
    if arguments.artifacts_only:
        print(
            f"PASS IMP artifacts only: IMP.1-IMP.{ARTIFACT_PHASES} passed and every emitted artifact "
            f"matches its pin; comparison layers IMP.{ARTIFACT_PHASES + 1}-IMP.{len(PHASES)} skipped"
        )
        return 0
    pins.finish("IMP complete IMP")
    summary = {
        "krs_schema": lock.krs_ir_schema(),
        "k": {"version": lock.k_version(), "commit": lock.k_commit()},
        "k_rust": {
            "version": lock.value("k_rust", "version"),
            "commit": lock.value("k_rust", "commit"),
        },
        "proof_bounds": pins["proof_policy"],
        "artifacts": cast(Artifacts, artifacts).hashes,
        "compatibility_policy": pins["compatibility"]["policy_version"],
    }
    print(f"PASS IMP complete IMP: {canonical_json(summary)}")
    return 0


if __name__ == "__main__":
    entry("IMP setup", main)
