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
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any, Callable, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from support import lock  # noqa: E402
from support.checkouts import git_revision  # noqa: E402
from support.hashing import (  # noqa: E402
    canonical_json,
    exact_directory,
    json_sha256,
    sha256_file,
    sha256_text,
    tracked_tree_sha256,
)
from support.kdefinition import split_claims  # noqa: E402
from support.parallel import settle_all, worker_count  # noqa: E402
from support.pins import Ledger, load_json, load_toml, table  # noqa: E402
from support.process import compact, run  # noqa: E402
from support.tools import executable, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
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
    krs: Path | None = None
    artifacts: Path | None = None
    reference_definition: Path | None = None
    actual_definition: Path | None = None
    reference_failure_definition: Path | None = None
    actual_failure_definition: Path | None = None
    native_build: Path | None = None
    artifact_hashes: dict[str, str] = field(default_factory=dict)


KRS_LOCK_EXTERNAL_TREES = (
    ("k", "pyk_source_sha256", "k", "pyk/src", True),
    ("k_rust", "tracked_crate_sha256", "k_rust", "crates/k-rust", False),
    ("k_rust", "tracked_backend_sha256", "k_rust", "crates/k-rust-backend", False),
    ("k_rust", "tracked_kore_sha256", "k_rust", "crates/k-rust-kore", False),
)
"""`Krs.lock` digests of external source trees: (section, key, checkout, prefix, reject untracked)."""


def phase_preflight(context: Context) -> str:
    """Check the input pins: external checkouts, their files, the corpus, and tools.

    KRS source is deliberately not pinned; the later phases pin what KRS
    produces. Toolchain and schema versions come from `Krs.lock`.
    """

    pins = context.pins
    corpus = context.corpus
    if pins.get("schema") != 1 or pins.get("milestone") != "M4":
        raise GateError("pins.json is not the exact M4 schema-1 ledger")
    if corpus.get("schema") != 2:
        raise GateError("corpus.json is not schema 2")
    if sha256_file(CORPUS_PATH) != pins.get("corpus_sha256"):
        raise GateError("corpus.json hash differs from pins.json")

    # M4 reuses the M3B--M3D corpora; each is pinned in its own gate ledger.
    ledgers = table(corpus.get("input_ledgers"), "corpus.input_ledgers")
    if set(ledgers) != {"m3b", "m3c", "m3d"}:
        raise GateError("corpus must name exactly the M3B--M3D input ledgers")
    for name, raw in ledgers.items():
        path = ROOT / str(table(raw, f"input ledger {name}").get("path"))
        ledger = load_json(path)
        for relative, expected in table(
            ledger.get("corpus_sha256"), f"{name}.corpus_sha256"
        ).items():
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
    observed = {name: git_revision(path) for name, path in checkouts.items()}
    if observed != expected:
        raise GateError(f"checkout revision differs: expected={expected}, actual={observed}")
    for relative, digest in table(pins.get("external_sha256"), "pins.external_sha256").items():
        if sha256_file(ROOT / relative) != digest:
            raise GateError(f"external input differs from its pin: {relative}")
    for section, key, checkout, prefix, reject_untracked in KRS_LOCK_EXTERNAL_TREES:
        digest = tracked_tree_sha256(
            checkouts[checkout], prefix, reject_untracked=reject_untracked
        )
        if digest != lock.value(section, key):
            raise GateError(f"{checkout} {prefix} differs from Krs.lock [{section}] {key}")
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
    if f"v{lock.k_version()}" not in version.stdout + version.stderr:
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


def phase_rust(context: Context) -> str:
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
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
    for manifest in (RUST_MANIFEST, EXPANDED_MANIFEST, NATIVE_MANIFEST):
        run(
            [
                "cargo", f"+{lock.msrv()}", "check", "--manifest-path", manifest,
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
    return (
        "workspace/package fmt, check, Clippy, tests, docs, authored IMP MSRV, "
        "stable native frontend, diagnostic and readable IMP LSP"
    )


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


def native_artifacts(context: Context, env: Mapping[str, str]) -> None:
    """Build the native definition twice and pin it, with the LLVM capability boundary."""

    assert context.krs is not None
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
    context.pins.expect(("native_comparison", "llvm_failure_sha256"), sha256_text(diagnostic_text))

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
    for name, digest in exact_directory(builds[0], builds[1], native_files).items():
        context.pins.expect(("native_artifact_sha256", name), digest)
    context.native_build = builds[0]


def phase_artifacts(context: Context) -> str:
    if context.krs is None:
        raise GateError("artifact phase lacks the phase-2 KRS binary")
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
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
        "symbols.json",
    ):
        if emit_a.joinpath(name).read_bytes() != probes[0].joinpath(name).read_bytes():
            raise GateError(f"CLI and production API probe differ: {name}")

    for name, digest in probe_hashes.items():
        context.pins.expect(("artifact_sha256", name), digest)
    context.artifacts = probes[0]
    context.artifact_hashes = probe_hashes
    native_artifacts(context, env)
    return (
        "124 descriptors; deterministic reviewed Rust expansion; 83-descriptor replacement parity; "
        "six repeated CLI/API source artifacts; repeated native build and LLVM capability boundary; "
        f"sha256={json_sha256(probe_hashes)}"
    )


def compile_source_definitions(context: Context) -> None:
    if context.artifacts is None:
        raise GateError("source compilation lacks deterministic artifacts")
    definition_source = context.artifacts / "definition.k"
    claim_free, labels, _ = split_claims(definition_source.read_text(encoding="utf-8"), CLAIM_COUNT)
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


def phase_source_definition(context: Context) -> str:
    compile_source_definitions(context)
    assert context.reference_definition is not None
    assert context.actual_definition is not None
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
            load_definition(context.reference_definition / filename),
            load_definition(context.actual_definition / filename),
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
    return f"parsed/compiled fail-closed projection: {observed}"


def phase_native(context: Context) -> str:
    if context.artifacts is None or context.actual_definition is None:
        raise GateError("native phase lacks artifacts or source definition")
    if context.native_build is None:
        raise GateError("native phase lacks the phase-3 native build")
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
    native_kore = context.native_build / "definition.kore"
    reference_kore = context.actual_definition / "definition.kore"
    comparator = [
        "cargo", "run", "--locked", "--quiet", "--manifest-path", NATIVE_MANIFEST,
        "--bin", "krs-m4-native-comparator", "--",
        reference_kore, native_kore, MODULE,
    ]
    native_policy = table(context.pins.get("native_comparison"), "pins.native_comparison")
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
    _, labels, claim_source = split_claims(
        context.artifacts.joinpath("definition.k").read_text(encoding="utf-8"), CLAIM_COUNT
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
    for source, target in table(native_policy.get("label_map", {}), "native label map").items():
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


def phase_proofs(context: Context) -> str:
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
        ],
        timeout=7200,
        environment={
            **context.environment,
            "CARGO_TARGET_DIR": os.fspath(context.target),
        },
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
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
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
    # Each probe owns its Cargo target and scratch directories, except that the
    # aggregate audit (last) re-runs the backend-capability probe (sixth) in
    # the same target, so those two run in sequence. Reports keep this order.
    groups = [[command] for command in commands[:5]] + [commands[5:]]

    def run_group(group: list[list[Any]]) -> list[str]:
        return [run(command, timeout=900, environment=env).stdout.strip() for command in group]

    outcomes = settle_all(
        [lambda group=group: run_group(group) for group in groups],
        worker_count("KRS_M4_ORACLE_WORKERS", 4),
    )
    reports = [report for outcome in outcomes for report in outcome.get()]
    digest = sha256_text("\n".join(reports))
    if table(context.pins.get("compatibility"), "pins.compatibility").get("policy_version") != 1:
        raise GateError("compatibility policy version differs from 1")
    context.pins.expect(("compatibility", "report_sha256"), digest)
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
ARTIFACT_PHASES = 3
"""Preflight, the Rust checks, and every emitted artifact; `--artifacts-only` stops here."""


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
                "KRS_M4_TARGET_DIR",
                os.fspath(Path(tempfile.gettempdir()) / "krs-m4-root-target"),
            )
        ),
    )
    parser.add_argument(
        "--artifacts-only",
        action="store_true",
        help=(
            f"stop after M4.{ARTIFACT_PHASES}, with every emitted artifact compared to its pin; "
            "skip the source, native KORE, behavior, proof, and compatibility comparisons"
        ),
    )
    arguments = parser.parse_args()
    if arguments.artifacts_only and (arguments.record or arguments.audit_all):
        parser.error("--artifacts-only cannot be combined with --record or --audit-all")
    pins = Ledger(PINS_PATH, record=arguments.record, artifacts_only=arguments.artifacts_only)
    phases = PHASES[:ARTIFACT_PHASES] if arguments.artifacts_only else PHASES
    corpus = load_json(CORPUS_PATH)
    failures: list[tuple[str, str]] = []
    with tempfile.TemporaryDirectory(prefix="krs-m4-root-") as temporary:
        context = Context(pins, corpus, Path(temporary), arguments.target_dir.resolve())
        context.target.mkdir(parents=True, exist_ok=True)
        for index, (name, function) in enumerate(phases, start=1):
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
    if arguments.artifacts_only:
        print(
            f"PASS M4 artifacts only: M4.1-M4.{ARTIFACT_PHASES} passed and every emitted artifact "
            f"matches its pin; comparison layers M4.{ARTIFACT_PHASES + 1}-M4.{len(PHASES)} skipped"
        )
        return 0
    pins.finish("M4 complete IMP")
    summary = {
        "krs_schema": lock.krs_ir_schema(),
        "k": {"version": lock.k_version(), "commit": lock.k_commit()},
        "k_rust": {
            "version": lock.value("k_rust", "version"),
            "commit": lock.value("k_rust", "commit"),
        },
        "proof_bounds": pins["proof_policy"],
        "artifacts": context.artifact_hashes,
        "compatibility_policy": pins["compatibility"]["policy_version"],
    }
    print(f"PASS M4 complete IMP: {canonical_json(summary)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except GateError as error:
        print(f"FAIL M4 setup: {error}", file=sys.stderr)
        raise SystemExit(1)
