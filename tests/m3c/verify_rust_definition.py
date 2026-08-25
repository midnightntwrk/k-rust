#!/usr/bin/env python3
"""External acceptance verifier for the Rust-authored M3C definition.

The production route is always the ``krs`` CLI.  The handwritten M3C theory
is compiled only as the frozen differential oracle and is never supplied to
KRS.
"""

from __future__ import annotations

from collections import Counter
import copy
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
from typing import Any


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
FIXTURE = HERE / "rust-definition"
MANIFEST = FIXTURE / "Cargo.toml"
SOURCE = FIXTURE / "src" / "lib.rs"
PACKAGE = "krs-m3c-rust-definition"
MODULE = "KRS-M3C-IMP"
K_VERSION = "v7.1.337"
ARTIFACT_MARKER = b"KRS artifact directory schema 1; safe to update.\n"
EXPECTED_KIND_COUNTS = {
    "sort": 5,
    "constructor": 21,
    "grammar": 29,
    "configuration": 1,
    "rule": 27,
}


def load_frozen_oracle() -> Any:
    spec = importlib.util.spec_from_file_location("krs_m3c_frozen_oracle", HERE / "verify.py")
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load tests/m3c/verify.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FROZEN = load_frozen_oracle()
FROZEN_RUN = FROZEN.run


def patient_oracle_run(
    command: list[str],
    *,
    timeout: int = 180,
    cwd: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    """Preserve the oracle runner while tolerating a contended K toolchain."""
    return FROZEN_RUN(command, timeout=max(timeout, 180), cwd=cwd)


FROZEN.run = patient_oracle_run


class Results:
    def __init__(self) -> None:
        self.failed = False
        self.unavailable = False

    def add(self, name: str, status: str, detail: str) -> None:
        print(f"{status:12} {name}: {detail}")
        if status == "UNAVAILABLE":
            self.unavailable = True
        elif status not in {"PASS", "MATCH"}:
            self.failed = True


def run(
    command: list[str | Path],
    *,
    cwd: Path = ROOT,
    env: dict[str, str] | None = None,
    timeout: int = 300,
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        [str(part) for part in command],
        cwd=cwd,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )


def compact(process: subprocess.CompletedProcess[bytes], limit: int = 1800) -> str:
    output = b"\n".join(part.strip() for part in (process.stdout, process.stderr) if part.strip())
    text = output.decode("utf-8", errors="replace")
    text = re.sub(r"/[A-Za-z0-9_.+@%/=-]+", "<PATH>", text)
    return text[:limit] + ("…" if len(text) > limit else "")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def source_contract(results: Results) -> None:
    source = SOURCE.read_text(encoding="utf-8")
    counts = {
        "constructors": source.count("#[k::constructor("),
        "rules": source.count("#[k::rule"),
        "explicit_rule_labels": source.count("#[k::rule(label ="),
        "explicit_subsorts": source.count("#[k::subsort]"),
        "strict": source.count("#[k::strict("),
        "seqstrict": source.count("#[k::seqstrict("),
        "configuration": source.count("#[k::configuration]"),
        "cells": source.count("#[k::cell("),
        "initializers": source.count("#[k::init]"),
    }
    expected = {
        "constructors": 21,
        "rules": 27,
        "explicit_rule_labels": 6,
        "explicit_subsorts": 3,
        "strict": 6,
        "seqstrict": 10,
        "configuration": 1,
        "cells": 2,
        "initializers": 1,
    }
    required = (
        'syntax = "if ({condition}) {then_branch} else {else_branch}"',
        "avoid = true",
        "#[k::strict(sequence = [condition], result = KResult)]",
        'syntax = "while ({condition}) {body}"',
        'syntax = "{{{body}}}"',
        'syntax = "{{}}"',
        '#[k::rule(label = "if-true")]',
        '#[k::rule(label = "if-false")]',
        '#[k::rule(label = "if-else")]',
        '#[k::rule(label = "while")]',
        '#[k::rule(label = "block")]',
        '#[k::rule(label = "done")]',
        "IfThenElse(false, _, else_branch)",
        "IfThen(condition,",
        "Block(Sequence(body, While(condition, body)))",
    )
    valid = counts == expected and all(fragment in source for fragment in required)
    results.add(
        "authored_surface",
        "PASS" if valid else "FAIL",
        "complete M3B plus five control productions and six exact labeled rewrites; "
        f"counts={counts}",
    )

    forbidden = ("include_str!", "include_bytes!", "raw_k!", "std::fs", "Command::new")
    package_files = {
        path.relative_to(FIXTURE).as_posix()
        for path in FIXTURE.rglob("*")
        if path.is_file() and "target" not in path.relative_to(FIXTURE).parts
    }
    expected_files = {".gitignore", "Cargo.lock", "Cargo.toml", "README.md", "src/lib.rs"}
    no_fallback = not any(fragment in source for fragment in forbidden)
    results.add(
        "no_handwritten_fallback",
        "PASS" if no_fallback and package_files == expected_files else "FAIL",
        f"source has no handwritten-K/artifact fallback; package files={sorted(package_files)}",
    )


def rust_gates(results: Results) -> None:
    rustfmt = shutil.which("rustfmt")
    if rustfmt is None:
        results.add("rustfmt", "FAIL", "rustfmt is unavailable")
    else:
        formatted = run([rustfmt, "--edition", "2024", "--check", SOURCE], cwd=FIXTURE)
        results.add(
            "rustfmt",
            "PASS" if formatted.returncode == 0 else "FAIL",
            "fixture source is formatted" if formatted.returncode == 0 else compact(formatted),
        )

    checked = run(["cargo", "check", "--locked", "--manifest-path", MANIFEST], timeout=600)
    results.add(
        "cargo_check",
        "PASS" if checked.returncode == 0 else "FAIL",
        "ordinary rustc check passes" if checked.returncode == 0 else compact(checked),
    )
    if checked.returncode != 0:
        return
    clippy = run(
        [
            "cargo", "clippy", "--locked", "--manifest-path", MANIFEST,
            "--all-targets", "--no-deps", "--", "-D", "warnings",
        ],
        timeout=600,
    )
    results.add(
        "clippy",
        "PASS" if clippy.returncode == 0 else "FAIL",
        "fixture-owned targets are warning-free" if clippy.returncode == 0 else compact(clippy),
    )
    documented = run(
        ["cargo", "doc", "--locked", "--manifest-path", MANIFEST, "--no-deps"],
        env={**os.environ, "RUSTDOCFLAGS": "-D warnings"},
        timeout=600,
    )
    tested = run(["cargo", "test", "--locked", "--manifest-path", MANIFEST], timeout=600)
    ok = documented.returncode == 0 and tested.returncode == 0
    results.add(
        "rustdoc_tests",
        "PASS" if ok else "FAIL",
        "strict rustdoc and fixture tests pass"
        if ok
        else compact(documented if documented.returncode != 0 else tested),
    )


def build_cli(results: Results, target: Path) -> Path | None:
    existing = ROOT / "target" / "debug" / "krs"
    if existing.is_file():
        probe = run([existing, "--help"], timeout=30)
        if probe.returncode == 0:
            results.add(
                "cli_build",
                "PASS",
                "existing workspace production krs CLI is executable",
            )
            return existing

    process = run(
        ["cargo", "build", "--locked", "-p", "krs-cli", "--bin", "krs"],
        env={**os.environ, "CARGO_TARGET_DIR": str(target)},
        timeout=900,
    )
    binary = target / "debug" / "krs"
    valid = process.returncode == 0 and binary.is_file()
    results.add(
        "cli_build",
        "PASS" if valid else "FAIL",
        "production krs CLI built" if valid else compact(process),
    )
    return binary if valid else None


def cli_command(
    binary: Path,
    command: str,
    _target: Path,
    *,
    output: Path | None = None,
) -> subprocess.CompletedProcess[bytes]:
    arguments: list[str | Path] = [
        binary, command, "--manifest-path", MANIFEST, "--package", PACKAGE,
        "--definition", "main",
    ]
    if output is not None:
        arguments.extend(["--output", output])
    # The standalone definition has a Cargo-owned target shared by the Rust
    # gates above.  Reuse it instead of duplicating several gigabytes in the
    # temporary K workspace.
    return run(arguments, env=dict(os.environ), timeout=900)


def descriptor_kind(descriptor: dict[str, Any]) -> str:
    identity = descriptor.get("id")
    if not isinstance(identity, dict) or not isinstance(identity.get("item_kind"), str):
        raise ValueError("descriptor has no typed id.item_kind")
    return identity["item_kind"]


def bundle_contract(raw: bytes) -> None:
    bundle = json.loads(raw)
    if bundle.get("protocol_version") != 11:
        raise ValueError(f"expected protocol v11, got {bundle.get('protocol_version')!r}")
    descriptors = bundle.get("descriptors")
    if not isinstance(descriptors, list):
        raise ValueError("bundle descriptors are not an array")
    counts = Counter(descriptor_kind(item) for item in descriptors)
    if dict(counts) != EXPECTED_KIND_COUNTS:
        raise ValueError(f"descriptor counts differ: {dict(counts)}")
    labels = {
        item.get("descriptor", {}).get("label", {}).get("name")
        for item in descriptors
        if item.get("id", {}).get("item_kind") == "rule"
        and item.get("descriptor", {}).get("label") is not None
    }
    expected_labels = {"if-true", "if-false", "if-else", "while", "block", "done"}
    if labels != expected_labels:
        raise ValueError(f"stable explicit labels differ: {labels}")
    serialized = json.dumps(bundle, sort_keys=True)
    for label in expected_labels:
        if f'"name": "{label}"' not in serialized:
            raise ValueError(f"stable bundle omits explicit label {label!r}")
    for forbidden in (str(ROOT), "TypeId", "HostTypeKey"):
        if forbidden in serialized:
            raise ValueError(f"stable bundle leaks host-only value {forbidden!r}")


def emitted_source_contract(source: str) -> None:
    productions = [
        line for line in source.splitlines() if line.strip().startswith("syntax ") and "::=" in line
    ]
    rules = [line for line in source.splitlines() if line.strip().startswith("rule ")]
    if (len(productions), len(rules)) != (27, 27):
        raise ValueError(f"expected 27 productions/rules, found {len(productions)}/{len(rules)}")
    required = (
        "module KRS-M3C-IMP",
        'syntax Stmt ::= "if" "(" Expr ")" Stmt "else" Stmt',
        "strict(1)",
        "avoid",
        'syntax Stmt ::= "while" "(" Expr ")" Stmt',
        'syntax Stmt ::= "{" Stmt "}"',
        'syntax Stmt ::= "{" "}"',
        "rule [if-true]:",
        "rule [if-false]:",
        "rule [if-else]:",
        "rule [while]:",
        "rule [block]:",
        "rule [done]:",
    )
    for fragment in required:
        if fragment not in source:
            raise ValueError(f"emitted K omits {fragment!r}")
    while_line = next(line for line in productions if "[symbol(while)" in line)
    if "strict" in while_line:
        raise ValueError("emitted while production is unexpectedly strict")


def sidecar_contract(directory: Path) -> str:
    expected = {
        ".krs-artifacts",
        "definition-ir.json",
        "definition.k",
        "descriptor-bundle.json",
        "semantic-ir.json",
        "symbols.json",
        "sources.json",
    }
    actual = {path.name for path in directory.iterdir()}
    if actual != expected:
        raise ValueError(f"artifact set differs: {sorted(actual)}")
    if (directory / ".krs-artifacts").read_bytes() != ARTIFACT_MARKER:
        raise ValueError("artifact ownership marker differs")
    source = (directory / "definition.k").read_text(encoding="utf-8")
    emitted_source_contract(source)
    symbols = json.loads((directory / "symbols.json").read_text(encoding="utf-8"))
    sources = json.loads((directory / "sources.json").read_text(encoding="utf-8"))
    symbol_entries = symbols.get("entries")
    source_entries = sources.get("entries")
    if symbols.get("schema_version") != 2 or sources.get("schema_version") != 2:
        raise ValueError("sidecar schema version differs")
    if not isinstance(symbol_entries, list) or len(symbol_entries) != 57:
        raise ValueError("symbol sidecar does not have exactly 57 rows")
    if not isinstance(source_entries, list) or len(source_entries) != 471:
        raise ValueError("source sidecar does not have exactly 471 rows")
    names = Counter(entry.get("emitted_name") for entry in symbol_entries)
    required_names = {
        MODULE, "ifThen", "ifThenElse", "while", "block", "emptyBlock",
        "if-true", "if-false", "if-else", "done",
    }
    if not required_names.issubset(names) or names["while"] != 2 or names["block"] != 2:
        raise ValueError(f"symbol sidecar omits or duplicates control identities: {names}")
    node_counts = Counter(entry.get("node_kind") for entry in source_entries)
    expected_counts = {
        "module": 1,
        "syntax_sort": 5,
        "subsort": 5,
        "production": 22,
        "production_item": 71,
        "production_attribute": 90,
        "production_group": 9,
        "associativity": 7,
        "precedence": 7,
        "configuration": 1,
        "cell": 2,
        "cell_attribute": 2,
        "configuration_variable": 2,
        "initializer": 1,
        "initializer_cell": 2,
        "rule": 27,
        "configuration_rewrite": 9,
        "cell_clause": 11,
        "cell_frame": 10,
        "term": 187,
    }
    if node_counts != Counter(expected_counts):
        raise ValueError(f"source-map structural counts differ: {node_counts}")
    keys = [entry.get("key") for entry in source_entries]
    if len(keys) != len(set(keys)) or any(not isinstance(key, str) for key in keys):
        raise ValueError("source-map keys are absent or non-unique")
    source_keys = set(keys)
    source_size = len(source.encode("utf-8"))
    for entry in symbol_entries:
        if entry.get("source_map_key") not in source_keys:
            raise ValueError(f"symbol has dangling source-map key: {entry!r}")
    for entry in source_entries:
        origin = entry.get("origin")
        if not isinstance(origin, list) or not origin:
            raise ValueError(f"source-map entry lacks provenance: {entry!r}")
        if origin[0].get("frame_type") != "ranged" or origin[0].get("kind") != "authored":
            raise ValueError(f"source-map entry does not begin at authored provenance: {entry!r}")
        if origin[-1].get("frame_type") != "transformation" or origin[-1].get("kind") != "definition_ir":
            raise ValueError(f"source-map entry does not end at Definition IR: {entry!r}")
        generated = entry.get("generated")
        if generated is not None:
            start = generated.get("start_byte")
            end = generated.get("end_byte")
            if generated.get("artifact") != "definition.k" or not (
                isinstance(start, int) and isinstance(end, int) and 0 <= start <= end <= source_size
            ):
                raise ValueError(f"generated range is invalid: {entry!r}")
    serialized = json.dumps({"symbols": symbols, "sources": sources}, sort_keys=True)
    for forbidden in (str(ROOT), "TypeId", "HostTypeKey"):
        if forbidden in serialized:
            raise ValueError(f"sidecars leak host-only value {forbidden!r}")
    return source


def artifact_bytes(directory: Path) -> dict[str, bytes]:
    return {path.name: path.read_bytes() for path in sorted(directory.iterdir()) if path.is_file()}


def cli_gates(results: Results, binary: Path, target: Path, workspace: Path) -> Path | None:
    checks = [cli_command(binary, "check", target) for _ in range(2)]
    expected = b"KRS check passed: 83 descriptors, 1 semantic modules\n"
    if any(item.returncode != 0 or item.stdout != expected for item in checks):
        bad = next(item for item in checks if item.returncode != 0 or item.stdout != expected)
        results.add("semantic_definition_pipeline", "FAIL", compact(bad))
        return None
    results.add(
        "semantic_definition_pipeline",
        "PASS",
        "two production CLI passes collect 83 descriptors and validate one semantic module",
    )

    expansions = [cli_command(binary, "expand", target) for _ in range(2)]
    try:
        if any(item.returncode != 0 for item in expansions):
            raise ValueError(compact(next(item for item in expansions if item.returncode != 0)))
        if expansions[0].stdout != expansions[1].stdout:
            raise ValueError("two descriptor expansions are not byte-identical")
        bundle_contract(expansions[0].stdout)
        results.add(
            "descriptor_bundle",
            "PASS",
            f"protocol-v11 5/21/29/1/27 bundle is deterministic; sha256={sha256_bytes(expansions[0].stdout)}",
        )
    except (ValueError, json.JSONDecodeError) as error:
        results.add("descriptor_bundle", "FAIL", str(error))
        return None

    directories = [workspace / "emitted-a", workspace / "emitted-b"]
    emissions = [
        cli_command(binary, "emit-k", target, output=directory) for directory in directories
    ]
    expected_emit = (
        b"emitted descriptor-bundle.json, semantic-ir.json, definition-ir.json, "
        b"definition.k, symbols.json, sources.json\n"
    )
    try:
        if any(item.returncode != 0 or item.stdout != expected_emit for item in emissions):
            bad = next(item for item in emissions if item.returncode != 0 or item.stdout != expected_emit)
            raise ValueError(compact(bad))
        source = sidecar_contract(directories[0])
        sidecar_contract(directories[1])
        first = artifact_bytes(directories[0])
        second = artifact_bytes(directories[1])
        if first != second:
            raise ValueError("repeated canonical artifact bytes differ")
        hashes = {name: sha256_bytes(value) for name, value in first.items()}
        results.add(
            "canonical_artifacts",
            "PASS",
            f"27 productions/rules and complete sidecars are byte-deterministic; sha256={hashes}",
        )
        return directories[0] / "definition.k"
    except (OSError, ValueError, json.JSONDecodeError) as error:
        results.add("canonical_artifacts", "FAIL", str(error))
        return None


def k_tools(results: Results) -> dict[str, str] | None:
    tools: dict[str, str] = {}
    missing: list[str] = []
    for name in ("kompile", "kast", "kparse", "krun"):
        executable = shutil.which(name)
        if executable is None:
            missing.append(name)
            continue
        version = run([executable, "--version"], timeout=30)
        text = (version.stdout + version.stderr).decode("utf-8", errors="replace")
        if version.returncode != 0 or K_VERSION not in text:
            results.add("pinned_k_tools", "FAIL", f"{name} is not pinned to {K_VERSION}")
            return None
        tools[name] = executable
    if missing:
        results.add("pinned_k_tools", "UNAVAILABLE", f"missing K commands: {', '.join(missing)}")
        return None
    results.add("pinned_k_tools", "PASS", f"kompile/kast/kparse/krun are pinned to {K_VERSION}")
    return tools


REFERENCE_LABELS = {
    "neg": "-__KRS-M3B-EXPR-SYNTAX_Expr_Expr",
    "not": "!__KRS-M3B-EXPR-SYNTAX_Expr_Expr",
    "mul": "_*__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "div": "_/__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "add": "_+__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "sub": "_-__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "ge": "_>=__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "gt": "_>__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "le": "_<=__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "lt": "_<__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "eq": "_==__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "ne": "_!=__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "and": "_&&__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "or": "_||__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr",
    "assign": "_=_;_KRS-M3B-CALC-SYNTAX_Stmt_Id_Expr",
    "sequence": "___KRS-M3B-CALC-SYNTAX_Stmt_Stmt_Stmt",
    "ifThenElse": "if(_)_else__KRS-M3C-IMP-SYNTAX_Stmt_Expr_Stmt_Stmt",
    "ifThen": "if(_)__KRS-M3C-IMP-SYNTAX_Stmt_Expr_Stmt",
    "while": "while(_)__KRS-M3C-IMP-SYNTAX_Stmt_Expr_Stmt",
    "block": "{_}_KRS-M3C-IMP-SYNTAX_Stmt_Stmt",
    "emptyBlock": "{}_KRS-M3C-IMP-SYNTAX_Stmt",
}
LOGICAL_LABELS = {
    generated: f"production:{generated}" for generated in REFERENCE_LABELS
} | {
    reference: f"production:{generated}" for generated, reference in REFERENCE_LABELS.items()
}
GENERATED_PRODUCTION_LABELS = set(REFERENCE_LABELS)
REFERENCE_PRODUCTION_LABELS = set(REFERENCE_LABELS.values())
FIXED_LABELS = {"<generatedTop>", "<generatedCounter>", "<k>", "<env>", ".Map", "_Map_", "_|->_"}


def normalize_label(name: str) -> str:
    direct = LOGICAL_LABELS.get(name)
    if direct is not None:
        return direct
    if name.startswith("#freezer"):
        match = re.search(r"(\d+)_$", name)
        if match is None:
            raise ValueError(f"unknown freezer label shape {name!r}")
        body = name[len("#freezer") : match.start()]
        logical = LOGICAL_LABELS.get(body)
        if logical is None:
            raise ValueError(f"unrecognized M3C freezer label {name!r}")
        return f"freezer:{logical}:{match.group(1)}"
    if "KRS-M3B-" in name or "KRS-M3C-" in name:
        raise ValueError(f"unrecognized project KLabel {name!r}")
    return name


def normalize_term(term: Any) -> Any:
    if isinstance(term, list):
        return [normalize_term(item) for item in term]
    if not isinstance(term, dict):
        return term
    value = copy.deepcopy(term)
    if value.get("node") == "KApply":
        label = value.get("label")
        if not isinstance(label, dict) or not isinstance(label.get("name"), str):
            raise ValueError(f"KApply has malformed label: {value!r}")
        label["name"] = normalize_label(label["name"])
    return {key: normalize_term(child) for key, child in value.items()}


def validate_generated_term(term: Any, *, search: bool = False) -> None:
    if not isinstance(term, dict) or not isinstance(term.get("node"), str):
        raise ValueError(f"unsupported generated KAST term {term!r}")
    node = term["node"]
    if node == "KApply":
        if set(term) != {"node", "label", "arity", "args"}:
            raise ValueError(f"unexpected generated KApply keys {sorted(term)}")
        label = term["label"]
        if not isinstance(label, dict) or set(label) != {"node", "name", "params"}:
            raise ValueError(f"unsupported generated label shape {label!r}")
        if label["node"] != "KLabel" or not isinstance(label["name"], str):
            raise ValueError(f"unsupported generated label {label!r}")
        name = label["name"]
        top_sort = {"node": "KSort", "name": "GeneratedTopCell", "params": []}
        expected_params = [top_sort, top_sort] if search and name == "#Equals" else []
        if label["params"] != expected_params:
            raise ValueError(f"unsupported generated label parameters {label!r}")
        accepted = name in FIXED_LABELS or name in GENERATED_PRODUCTION_LABELS
        if search and name == "#Equals":
            accepted = True
        if name.startswith("#freezer"):
            normalize_label(name)
            accepted = True
        if not accepted:
            raise ValueError(f"unrecognized generated KLabel {name!r}")
        if term["arity"] != len(term["args"]):
            raise ValueError("generated KApply arity differs from args")
        for argument in term["args"]:
            validate_generated_term(argument, search=search)
    elif node == "KToken":
        if set(term) != {"node", "sort", "token"} or not isinstance(term["token"], str):
            raise ValueError(f"unsupported generated KToken {term!r}")
        FROZEN.validate_sort(term["sort"])
    elif node == "KSequence":
        if set(term) != {"node", "arity", "items"} or term["arity"] != len(term["items"]):
            raise ValueError(f"unsupported generated KSequence {term!r}")
        for item in term["items"]:
            validate_generated_term(item, search=search)
    elif node == "KVariable" and search:
        if set(term) != {"node", "name", "sort"} or not isinstance(term["name"], str):
            raise ValueError(f"unsupported generated KVariable {term!r}")
        FROZEN.validate_sort(term["sort"])
    else:
        raise ValueError(f"unsupported generated KAST node {node!r}")


def generated_envelope(output: str, *, search: bool = False) -> dict[str, Any]:
    start = output.find("{")
    if start < 0:
        raise ValueError("generated KAST output has no JSON envelope")
    value = json.loads(output[start:])
    if set(value) != {"format", "version", "term"}:
        raise ValueError(f"unexpected generated KAST envelope keys {sorted(value)}")
    if value["format"] != "KAST" or value["version"] != 4:
        raise ValueError("generated output is not KAST v4")
    validate_generated_term(value["term"], search=search)
    return value


def reference_compatible_term(term: Any) -> Any:
    """Translate validated generated symbols for frozen helper invariants."""
    if isinstance(term, list):
        return [reference_compatible_term(item) for item in term]
    if not isinstance(term, dict):
        return term
    value = copy.deepcopy(term)
    if value.get("node") == "KApply":
        label = value.get("label")
        if not isinstance(label, dict) or not isinstance(label.get("name"), str):
            raise ValueError(f"KApply has malformed label: {value!r}")
        name = label["name"]
        if name in REFERENCE_LABELS:
            label["name"] = REFERENCE_LABELS[name]
        elif name.startswith("#freezer"):
            match = re.search(r"(\d+)_$", name)
            if match is None:
                raise ValueError(f"unknown freezer label shape {name!r}")
            body = name[len("#freezer") : match.start()]
            reference = REFERENCE_LABELS.get(body)
            if reference is None:
                raise ValueError(f"unrecognized M3C freezer label {name!r}")
            label["name"] = f"#freezer{reference}{match.group(1)}_"
    return {key: reference_compatible_term(child) for key, child in value.items()}


def reference_compatible_generated_envelope(
    output: str, *, search: bool = False
) -> dict[str, Any]:
    value = generated_envelope(output, search=search)
    value["term"] = reference_compatible_term(value["term"])
    return value


def generated_oracle_call(function: Any, *arguments: Any) -> Any:
    original = FROZEN.envelope
    FROZEN.envelope = reference_compatible_generated_envelope
    try:
        return function(*arguments)
    finally:
        FROZEN.envelope = original


def assert_term_maps_equal(generated: dict[str, Any], reference: dict[str, Any], contract: str) -> None:
    if set(generated) != set(reference):
        raise ValueError(f"{contract} case names differ")
    for name in sorted(generated):
        left = FROZEN.canonical(normalize_term(generated[name]))
        right = FROZEN.canonical(normalize_term(reference[name]))
        if left != right:
            raise ValueError(f"{contract} differs at {name}")


def generated_parse(
    tools: dict[str, str], definition: Path, workspace: Path
) -> tuple[dict[str, Any], dict[str, str]]:
    trees: dict[str, Any] = {}
    unparsed: dict[str, str] = {}
    for path in sorted(FROZEN.ACCEPTED.glob("*.imp")):
        command = [
            tools["kast"], "--definition", str(definition), "--module", MODULE,
            "--sort", "Stmt", "--output", "json", str(path),
        ]
        process = FROZEN.run(command, timeout=60)
        if process.returncode != 0:
            raise RuntimeError(f"generated parse failed for {path.name}: {FROZEN.compact(process)}")
        term = generated_envelope(process.stdout)["term"]
        trees[path.name] = term
        portable = FROZEN.run(
            [tools["kparse"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", str(path)],
            timeout=60,
        )
        if portable.returncode != 0 or "Lbl" not in portable.stdout:
            raise RuntimeError(f"generated kparse failed for {path.name}: {FROZEN.compact(portable)}")
        pretty = FROZEN.run(command[:-2] + ["program", str(path)], timeout=60)
        if pretty.returncode != 0:
            raise RuntimeError(f"generated unparse failed for {path.name}: {FROZEN.compact(pretty)}")
        roundtrip = workspace / f"generated-roundtrip-{path.name}"
        roundtrip.write_text(pretty.stdout, encoding="utf-8")
        reparsed = FROZEN.run(command[:-1] + [str(roundtrip)], timeout=60)
        if reparsed.returncode != 0:
            raise RuntimeError(f"generated reparse failed for {path.name}: {FROZEN.compact(reparsed)}")
        if FROZEN.canonical(term) != FROZEN.canonical(generated_envelope(reparsed.stdout)["term"]):
            raise RuntimeError(f"generated parse/unparse/parse changed {path.name}")
        unparsed[path.name] = pretty.stdout.strip()
    return trees, unparsed


def compile_generated(kompile: str, source: Path, output: Path) -> subprocess.CompletedProcess[bytes]:
    return run(
        [
            kompile, source, "--main-module", MODULE, "--syntax-module", MODULE,
            "--backend", "llvm", "--enable-search", "--emit-json",
            "--output-definition", output,
        ],
        timeout=600,
    )


def verify_frozen_definition(pins: dict[str, Any], definition: Path) -> None:
    parsed = json.loads((definition / "parsed.json").read_text(encoding="utf-8"))
    compiled = json.loads((definition / "compiled.json").read_text(encoding="utf-8"))
    FROZEN.verify_definition_structure(parsed, compiled)
    hashes = {
        "parsed": hashlib.sha256(FROZEN.canonical(FROZEN.normalized_definition(parsed)).encode()).hexdigest(),
        "compiled": hashlib.sha256(FROZEN.canonical(FROZEN.normalized_definition(compiled)).encode()).hexdigest(),
    }
    if hashes != pins.get("normalized_definition_sha256"):
        raise ValueError(f"frozen reference definition hashes differ: {hashes}")


def verify_generated_definition(definition: Path) -> dict[str, str]:
    parsed = json.loads((definition / "parsed.json").read_text(encoding="utf-8"))
    compiled = json.loads((definition / "compiled.json").read_text(encoding="utf-8"))
    module = FROZEN.find_module(parsed, MODULE)
    counts = Counter(sentence.get("node") for sentence in module["localSentences"])
    expected = Counter({
        "KProduction": 38,
        "KRule": 30,
        "KSyntaxAssociativity": 7,
        "KSyntaxPriority": 7,
        "KSyntaxSort": 5,
    })
    if counts != expected:
        raise ValueError(f"generated parsed definition counts differ: {counts}")
    productions = {
        sentence.get("klabel", {}).get("name"): sentence.get("att", {}).get("att", {})
        for sentence in module["localSentences"]
        if sentence.get("node") == "KProduction" and sentence.get("klabel")
    }
    if_else = productions.get("ifThenElse", {})
    while_attrs = productions.get("while", {})
    if "avoid" not in if_else or if_else.get("strict") != "1" or "strict" in while_attrs:
        raise ValueError("generated avoid/strict/non-strict-while structure differs")
    labels = {
        sentence.get("att", {}).get("att", {}).get("label")
        for sentence in module["localSentences"]
        if sentence.get("node") == "KRule"
        and sentence.get("att", {}).get("att", {}).get("label") is not None
    }
    explicit = {f"{MODULE}.{name}" for name in (
        "assign", "step", "var", "if-true", "if-false", "if-else", "while", "block", "done",
    )}
    opaque = {name for name in labels if isinstance(name, str) and name.startswith("krsRule_")}
    if labels != explicit | opaque or len(opaque) != 18:
        raise ValueError(f"generated parsed rule labels differ: {labels}")
    compiled_module = FROZEN.find_module(compiled, MODULE)
    compiled_rules = [
        sentence for sentence in compiled_module["localSentences"] if sentence.get("node") == "KRule"
    ]
    heat = sum("heat" in sentence.get("att", {}).get("att", {}) for sentence in compiled_rules)
    cool = sum("cool" in sentence.get("att", {}).get("att", {}) for sentence in compiled_rules)
    if len(compiled_rules) != 117 or (heat, cool) != (26, 26):
        raise ValueError(
            f"expected 117 flattened generated rules and 26 heat/cool pairs, got "
            f"{len(compiled_rules)} and {(heat, cool)}"
        )
    return {
        "parsed": hashlib.sha256(FROZEN.canonical(FROZEN.normalized_definition(parsed)).encode()).hexdigest(),
        "compiled": hashlib.sha256(FROZEN.canonical(FROZEN.normalized_definition(compiled)).encode()).hexdigest(),
    }


def differential_oracle(
    results: Results,
    tools: dict[str, str],
    generated_source: Path,
    workspace: Path,
) -> None:
    pins = json.loads(FROZEN.PINS.read_text(encoding="utf-8"))
    actual_sources = {
        str(path.relative_to(HERE)): FROZEN.sha256(path) for path in FROZEN.fixture_files()
    }
    if actual_sources != pins.get("source_sha256"):
        results.add("frozen_corpus", "FAIL", "frozen M3C handwritten/corpus source hashes drifted")
        return
    results.add("frozen_corpus", "PASS", f"all {len(actual_sources)} frozen source hashes are exact")

    reference_definition = workspace / "reference-kompiled"
    generated_definition = workspace / "generated-kompiled"
    reference_compile = FROZEN.compile_reference(tools["kompile"], reference_definition)
    if reference_compile.returncode != 0:
        results.add("reference_compile", "FAIL", FROZEN.compact(reference_compile))
        return
    generated_compile = compile_generated(tools["kompile"], generated_source, generated_definition)
    if generated_compile.returncode != 0:
        results.add("generated_compile", "FAIL", compact(generated_compile))
        return
    try:
        verify_frozen_definition(pins, reference_definition)
        definition_hashes = verify_generated_definition(generated_definition)
        results.add(
            "generated_compile_structure",
            "PASS",
            "generated source compiles with exact control attributes, labels and 26 heat/cool pairs; "
            f"hashes={definition_hashes}",
        )

        reference_trees, reference_unparsed = FROZEN.parse_accepted(tools, reference_definition, workspace)
        if FROZEN.aggregate(reference_trees) != pins.get("accepted_tree_aggregate_sha256"):
            raise ValueError("frozen accepted-tree aggregate differs")
        if FROZEN.aggregate(reference_unparsed) != pins.get("unparse_aggregate_sha256"):
            raise ValueError("frozen unparse aggregate differs")
        generated_trees, generated_unparsed = generated_parse(tools, generated_definition, workspace)
        assert_term_maps_equal(generated_trees, reference_trees, "accepted parse tree")
        if generated_unparsed != reference_unparsed:
            raise ValueError("generated concrete unparse output differs from frozen oracle")
        results.add(
            "parse_unparse",
            "MATCH",
            "eight full trees and concrete unparse round trips match modulo declared production symbols",
        )

        reference_finals, reference_trace = FROZEN.execute_accepted(tools["krun"], reference_definition)
        if FROZEN.aggregate(reference_finals) != pins.get("final_state_aggregate_sha256"):
            raise ValueError("frozen final-state aggregate differs")
        if FROZEN.aggregate(reference_trace) != pins.get("llvm_trace_aggregate_sha256"):
            raise ValueError("frozen trace aggregate differs")
        generated_finals, generated_trace = generated_oracle_call(
            FROZEN.execute_accepted, tools["krun"], generated_definition
        )
        assert_term_maps_equal(generated_finals, reference_finals, "final state")
        assert_term_maps_equal(generated_trace, reference_trace, "LLVM trace state")
        if len(generated_trace) != 187:
            raise ValueError(f"expected 187 generated states, found {len(generated_trace)}")
        results.add(
            "execution_traces",
            "MATCH",
            "eight rewrite counts/final maps and all 187 LLVM states match under closed production/freezer identities",
        )

        reference_searches, reference_bounded = FROZEN.verify_search(
            tools["krun"], reference_definition
        )
        search_pins = pins.get("bounded_search_sha256", {})
        if FROZEN.aggregate(reference_searches) != search_pins.get("frontiers"):
            raise ValueError("frozen bounded-search aggregate differs")
        if FROZEN.aggregate(reference_bounded) != search_pins.get("nontermination"):
            raise ValueError("frozen nontermination aggregate differs")
        generated_searches, generated_bounded = generated_oracle_call(
            FROZEN.verify_search, tools["krun"], generated_definition
        )
        assert_term_maps_equal(generated_searches, reference_searches, "bounded search")
        assert_term_maps_equal(generated_bounded, reference_bounded, "bounded nontermination")
        results.add(
            "bounded_search",
            "MATCH",
            "16 search frontiers match direct execution and all eight infinite-loop depths remain live",
        )

        reference_stuck, reference_diagnostics = FROZEN.verify_rejections(tools, reference_definition)
        rejection_pins = pins.get("rejection_sha256", {})
        if FROZEN.aggregate(reference_stuck) != rejection_pins.get("stuck_states"):
            raise ValueError("frozen stuck-state aggregate differs")
        if FROZEN.aggregate(reference_diagnostics) != rejection_pins.get("syntax_diagnostics"):
            raise ValueError("frozen syntax-diagnostic aggregate differs")
        generated_stuck, generated_diagnostics = generated_oracle_call(
            FROZEN.verify_rejections, tools, generated_definition
        )
        assert_term_maps_equal(generated_stuck, reference_stuck, "stuck state")
        if generated_diagnostics != reference_diagnostics:
            raise ValueError("generated syntax diagnostics differ from frozen oracle")
        induced = FROZEN.verify_induced_diagnostic(tools["kompile"], workspace)
        if hashlib.sha256(induced.encode()).hexdigest() != pins.get("induced_diagnostic_sha256"):
            raise ValueError("frozen induced diagnostic hash differs")
        results.add(
            "rejections_diagnostics",
            "MATCH",
            "four syntax diagnostics, three stuck states and the exact induced source location match",
        )
    except (
        OSError,
        ValueError,
        RuntimeError,
        json.JSONDecodeError,
        subprocess.TimeoutExpired,
    ) as error:
        results.add("differential_oracle", "FAIL", str(error))


def main() -> int:
    results = Results()
    source_contract(results)
    rust_gates(results)
    shared_memory = Path("/dev/shm")
    temporary_root = shared_memory if shared_memory.is_dir() and os.access(shared_memory, os.W_OK) else None
    if temporary_root is not None:
        # K's parser compiles tiny configuration-variable scanners under
        # TMPDIR on every invocation.  Keep those alongside the large fresh
        # definitions instead of consuming a disk-constrained system /tmp.
        os.environ.setdefault("TMPDIR", str(temporary_root))
    with tempfile.TemporaryDirectory(
        prefix="krs-m3c-rust-definition-", dir=temporary_root
    ) as temporary:
        workspace = Path(temporary)
        # This target is used only if no workspace CLI is available.  The
        # standalone definition's collector keeps using its Cargo-owned
        # target; emitted artifacts and K definitions remain per-run here.
        target = (
            shared_memory / "krs-m3c-cli-target"
            if temporary_root is not None
            else workspace / "cargo-target"
        )
        binary = build_cli(results, target)
        generated_source = (
            cli_gates(results, binary, target, workspace) if binary is not None else None
        )
        if generated_source is not None:
            tools = k_tools(results)
            if tools is not None:
                differential_oracle(results, tools, generated_source, workspace)

    if results.failed:
        print("\nRust-authored M3C acceptance: FAIL")
        return 1
    if results.unavailable:
        print("\nRust-authored M3C acceptance: UNAVAILABLE")
        return 0
    print("\nRust-authored M3C acceptance: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
