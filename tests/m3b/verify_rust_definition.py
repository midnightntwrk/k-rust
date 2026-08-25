#!/usr/bin/env python3
"""External acceptance verifier for the explicit Rust-authored M3B definition.

The production route is always the ``krs`` CLI.  The handwritten M3B theory is
compiled only as a frozen differential oracle; it is never supplied to KRS.
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
PACKAGE = "krs-m3b-rust-definition"
MODULE = "KRS-M3B-CALC"
K_VERSION = "v7.1.337"
ARTIFACT_MARKER = b"KRS artifact directory schema 1; safe to update.\n"
EXPECTED_KIND_COUNTS = {
    "sort": 5,
    "constructor": 16,
    # Twenty-two production descriptors plus standalone precedence and
    # associativity descriptors for the calculation layer.
    "grammar": 24,
    "configuration": 1,
    "rule": 21,
}


def load_frozen_oracle() -> Any:
    spec = importlib.util.spec_from_file_location("krs_m3b_frozen_oracle", HERE / "verify.py")
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load tests/m3b/verify.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FROZEN = load_frozen_oracle()


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
    return text[:limit] + ("\u2026" if len(text) > limit else "")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def source_contract(results: Results) -> None:
    source = SOURCE.read_text(encoding="utf-8")
    counts = {
        "constructors": source.count("#[k::constructor("),
        "rules": source.count("#[k::rule]"),
        "explicit_subsorts": source.count("#[k::subsort]"),
        "strict": source.count("#[k::strict("),
        "seqstrict": source.count("#[k::seqstrict("),
        "left_associativity": source.count("left:"),
        "right_associativity": source.count("right:"),
        "configuration": source.count("#[k::configuration]"),
        "cells": source.count("#[k::cell("),
        "initializers": source.count("#[k::init]"),
    }
    expected = {
        "constructors": 16,
        "rules": 21,
        "explicit_subsorts": 3,
        "strict": 5,
        "seqstrict": 10,
        "left_associativity": 6,
        "right_associativity": 1,
        "configuration": 1,
        "cells": 2,
        "initializers": 1,
    }
    required = (
        "impl Expr for Id",
        "stmt > seq_stmt",
        "right: seq_stmt",
        "#[k::strict(sequence = [value], result = KResult)]\npub struct Assign",
        "KCell<k::builtin::KSequence>",
        "Cell<Map<Id, Term<dyn Value>>>",
        "config_var(name = \"PGM\", main)",
        "config_var(name = \"ENV\")",
        "k::k![program]",
        "cells! {",
        "map![name => value, rest @ ..]",
        "map![environment [ name <- value ]]",
        "pub fn step(",
        "pub fn var(",
        "pub fn assign(",
    )
    valid = counts == expected and all(fragment in source for fragment in required)
    results.add(
        "authored_surface",
        "PASS" if valid else "FAIL",
        f"19+3 productions, 18+3 rules, Id/Map/KSequence, strictness, grammar relations, and two cells; counts={counts}",
    )

    forbidden = (
        "include_str!",
        "include_bytes!",
        "raw_k!",
        "std::fs",
        "fs::read",
        "Command::new",
    )
    no_fallback = not any(fragment in source for fragment in forbidden)
    package_files = {
        path.relative_to(FIXTURE).as_posix()
        for path in FIXTURE.rglob("*")
        if path.is_file() and "target" not in path.relative_to(FIXTURE).parts
    }
    expected_files = {".gitignore", "Cargo.lock", "Cargo.toml", "README.md", "src/lib.rs"}
    results.add(
        "no_handwritten_fallback",
        "PASS" if no_fallback and package_files == expected_files else "FAIL",
        f"source has no executable handwritten-K/artifact path; package files={sorted(package_files)}",
    )


def rust_gates(results: Results) -> None:
    rustfmt = shutil.which("rustfmt")
    if rustfmt is None:
        results.add("rustfmt", "FAIL", "production authoring tool rustfmt is unavailable")
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
            "cargo",
            "clippy",
            "--locked",
            "--manifest-path",
            MANIFEST,
            "--all-targets",
            "--no-deps",
            "--",
            "-D",
            "warnings",
        ],
        timeout=600,
    )
    results.add(
        "clippy",
        "PASS" if clippy.returncode == 0 else "FAIL",
        "fixture-owned targets are warning-free" if clippy.returncode == 0 else compact(clippy),
    )


def build_cli(results: Results, target: Path) -> Path | None:
    environment = {**os.environ, "CARGO_TARGET_DIR": str(target)}
    process = run(
        ["cargo", "build", "--locked", "-p", "krs-cli", "--bin", "krs"],
        env=environment,
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
    target: Path,
    *,
    output: Path | None = None,
) -> subprocess.CompletedProcess[bytes]:
    arguments: list[str | Path] = [
        binary,
        command,
        "--manifest-path",
        MANIFEST,
        "--package",
        PACKAGE,
        "--definition",
        "main",
    ]
    if output is not None:
        arguments.extend(["--output", output])
    # Do not override the selected standalone package's Cargo-owned target;
    # its generated collector is intentionally planned beneath that target.
    return run(arguments, env=dict(os.environ), timeout=900)


def descriptor_kind(descriptor: dict[str, Any]) -> str:
    identity = descriptor.get("id")
    if not isinstance(identity, dict) or not isinstance(identity.get("item_kind"), str):
        raise ValueError("descriptor has no typed id.item_kind")
    return identity["item_kind"]


def bundle_contract(raw: bytes) -> dict[str, Any]:
    bundle = json.loads(raw)
    if bundle.get("protocol_version") != 7:
        raise ValueError(f"expected protocol v7, got {bundle.get('protocol_version')!r}")
    descriptors = bundle.get("descriptors")
    if not isinstance(descriptors, list):
        raise ValueError("bundle descriptors are not an array")
    counts = Counter(descriptor_kind(item) for item in descriptors)
    if dict(counts) != EXPECTED_KIND_COUNTS:
        raise ValueError(f"descriptor counts differ: {dict(counts)}")
    serialized = json.dumps(bundle, sort_keys=True)
    required = (
        '"sort": "id"',
        '"sort": "map"',
        '"sort": "k_sequence"',
        '"external_name": "PGM"',
        '"external_name": "ENV"',
        '"item_name": "step"',
        '"item_name": "var"',
        '"item_name": "assign"',
        '"map_kind": "update"',
    )
    missing = [fragment for fragment in required if fragment not in serialized]
    if missing:
        raise ValueError(f"bundle omits stable M3B identities/shapes: {missing}")
    for forbidden in (str(ROOT), "TypeId", "HostTypeKey"):
        if forbidden in serialized:
            raise ValueError(f"stable bundle leaks host-only value {forbidden!r}")
    return bundle


def emitted_source_contract(source: str) -> None:
    productions = [
        line for line in source.splitlines() if line.strip().startswith("syntax ") and "::=" in line
    ]
    rules = [line for line in source.splitlines() if line.strip().startswith("rule ")]
    if len(productions) != 22:
        raise ValueError(f"expected exact 19+3 productions, found {len(productions)}")
    if len(rules) != 21:
        raise ValueError(f"expected exact 18+3 rules, found {len(rules)}")
    if source.count("seqstrict") != 10:
        raise ValueError(f"expected ten seqstrict attributes, found {source.count('seqstrict')}")
    strict = len(re.findall(r"(?<!seq)strict(?:\(|\b)", source))
    if strict != 5:
        raise ValueError(f"expected five strict attributes including assignment, found {strict}")
    if len(re.findall(r"(?m)^\s*syntax left ", source)) != 6:
        raise ValueError("expected six expression left-associativity sentences")
    if len(re.findall(r"(?m)^\s*syntax right ", source)) != 1:
        raise ValueError("expected one statement right-associativity sentence")
    if len(re.findall(r"(?m)^\s*syntax priority ", source)) != 7:
        raise ValueError("expected six expression priorities plus stmt > sequence")
    required = (
        "module KRS-M3B-CALC",
        "imports BOOL",
        "imports ID-SYNTAX",
        "imports INT",
        "imports MAP",
        "syntax Expr ::= Id",
        'Id "=" Expr ";"',
        "strict(2)",
        "configuration\n    <k color=\"green\"> $PGM:Stmt </k>\n    <env color=\"yellow\"> $ENV:Map </env>",
        "rule [assign]:",
        "rule [step]:",
        "rule [var]:",
        "~>",
        ".K",
        "|->",
        " <- ",
    )
    for fragment in required:
        if fragment not in source:
            raise ValueError(f"emitted K omits {fragment!r}")


def sidecar_contract(directory: Path) -> str:
    expected = {".krs-artifacts", "definition.k", "symbols.json", "sources.json"}
    actual = {path.name for path in directory.iterdir()}
    if actual != expected:
        raise ValueError(f"artifact set differs: {sorted(actual)}")
    if (directory / ".krs-artifacts").read_bytes() != ARTIFACT_MARKER:
        raise ValueError("artifact ownership marker differs")
    source = (directory / "definition.k").read_text(encoding="utf-8")
    emitted_source_contract(source)

    symbols = json.loads((directory / "symbols.json").read_text(encoding="utf-8"))
    sources = json.loads((directory / "sources.json").read_text(encoding="utf-8"))
    if symbols.get("schema_version") != 1 or sources.get("schema_version") != 1:
        raise ValueError("sidecar schema version differs from 1")
    symbol_entries = symbols.get("entries")
    source_entries = sources.get("entries")
    if not isinstance(symbol_entries, list) or not isinstance(source_entries, list):
        raise ValueError("sidecar entries are not arrays")
    if len(symbol_entries) != 46:
        raise ValueError(f"expected 46 complete symbol entries, found {len(symbol_entries)}")
    names = Counter(entry.get("emitted_name") for entry in symbol_entries)
    required_names = {
        MODULE,
        "Expr",
        "KItem",
        "KResult",
        "Stmt",
        "Value",
        "k",
        "env",
        "add",
        "and",
        "assign",
        "div",
        "eq",
        "ge",
        "gt",
        "le",
        "lt",
        "mul",
        "ne",
        "neg",
        "not",
        "or",
        "sequence",
        "step",
        "sub",
        "var",
    }
    if not required_names.issubset(names) or names["assign"] != 2:
        raise ValueError(f"symbol sidecar omits or duplicates exact authored names: {names}")
    generated_productions = [name for name in names if isinstance(name, str) and name.startswith("krsGenerated_")]
    generated_rules = [name for name in names if isinstance(name, str) and name.startswith("krsRule_")]
    if len(generated_productions) != 1 or len(generated_rules) != 18:
        raise ValueError("expected one generated bracket symbol and 18 generated expression-rule labels")

    keys = [entry.get("key") for entry in source_entries]
    if not keys or len(keys) != len(set(keys)) or any(not isinstance(key, str) for key in keys):
        raise ValueError("source-map keys are absent or non-unique")
    source_keys = set(keys)
    for entry in symbol_entries:
        if entry.get("source_map_key") not in source_keys:
            raise ValueError(f"symbol has dangling source-map key: {entry!r}")
    node_counts = Counter(entry.get("node_kind") for entry in source_entries)
    exact_counts = {
        "module": 1,
        "syntax_sort": 5,
        "subsort": 5,
        "production": 17,
        "production_item": 49,
        "production_attribute": 36,
        "production_group": 9,
        "associativity": 7,
        "precedence": 7,
        "configuration": 1,
        "cell": 2,
        "cell_attribute": 2,
        "configuration_variable": 2,
        "initializer": 1,
        "initializer_cell": 2,
        "rule": 21,
        "configuration_rewrite": 3,
        "cell_clause": 5,
        "cell_frame": 4,
        "term": 142,
    }
    differences = {
        kind: (expected_count, node_counts.get(kind, 0))
        for kind, expected_count in exact_counts.items()
        if node_counts.get(kind, 0) != expected_count
    }
    if differences:
        raise ValueError(f"source-map structural counts differ: {differences}; all={node_counts}")
    source_size = len(source.encode("utf-8"))
    for entry in source_entries:
        origin = entry.get("origin")
        if not isinstance(origin, list) or not origin:
            raise ValueError(f"source-map entry lacks provenance stack: {entry!r}")
        if origin[0].get("frame_type") != "ranged" or origin[0].get("kind") != "authored":
            raise ValueError(f"source-map entry does not begin at authored provenance: {entry!r}")
        if origin[-1].get("frame_type") != "transformation" or origin[-1].get("kind") != "definition_ir":
            raise ValueError(f"source-map entry does not end at Definition IR: {entry!r}")
        generated = entry.get("generated")
        if generated is not None:
            if generated.get("artifact") != "definition.k":
                raise ValueError(f"generated range names another artifact: {entry!r}")
            start = generated.get("start_byte")
            end = generated.get("end_byte")
            if not isinstance(start, int) or not isinstance(end, int) or not 0 <= start <= end <= source_size:
                raise ValueError(f"generated byte range is invalid: {entry!r}")
    serialized = json.dumps({"symbols": symbols, "sources": sources}, sort_keys=True)
    for forbidden in (str(ROOT), "TypeId", "HostTypeKey"):
        if forbidden in serialized:
            raise ValueError(f"sidecars leak host-only value {forbidden!r}")
    return source


def artifact_bytes(directory: Path) -> dict[str, bytes]:
    return {path.name: path.read_bytes() for path in sorted(directory.iterdir()) if path.is_file()}


def cli_gates(
    results: Results,
    binary: Path,
    target: Path,
    workspace: Path,
) -> tuple[str, Path] | None:
    checks = [cli_command(binary, "check", target) for _ in range(2)]
    expected_check = b"KRS check passed: 67 descriptors, 1 semantic modules\n"
    check_ok = all(item.returncode == 0 and item.stdout == expected_check for item in checks)
    results.add(
        "semantic_definition_pipeline",
        "PASS" if check_ok else "FAIL",
        "two production CLI passes collect 67 descriptors and deterministically validate one semantic/Definition module"
        if check_ok
        else compact(next(item for item in checks if item.returncode != 0 or item.stdout != expected_check)),
    )
    if not check_ok:
        return None

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
            f"protocol-v7 5/16/24/1/21 descriptors are exact and deterministic; sha256={sha256_bytes(expansions[0].stdout)}",
        )
    except (ValueError, json.JSONDecodeError) as error:
        results.add("descriptor_bundle", "FAIL", str(error))
        return None

    directories = [workspace / "emitted-a", workspace / "emitted-b"]
    emissions = [cli_command(binary, "emit-k", target, output=directory) for directory in directories]
    expected_emit = b"emitted definition.k, symbols.json, sources.json\n"
    try:
        if any(item.returncode != 0 or item.stdout != expected_emit for item in emissions):
            bad = next(item for item in emissions if item.returncode != 0 or item.stdout != expected_emit)
            raise ValueError(compact(bad))
        source = sidecar_contract(directories[0])
        sidecar_contract(directories[1])
        first = artifact_bytes(directories[0])
        second = artifact_bytes(directories[1])
        if first != second:
            differing = sorted(name for name in first.keys() | second.keys() if first.get(name) != second.get(name))
            raise ValueError(f"repeated canonical artifact bytes differ: {differing}")
        hashes = {name: sha256_bytes(value) for name, value in first.items()}
        results.add(
            "canonical_artifacts",
            "PASS",
            f"exact 19+3 productions, 18+3 rules, configuration, .k and complete sidecars are byte-deterministic; sha256={hashes}",
        )
        return source, directories[0]
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
            results.add("pinned_k_tools", "FAIL", f"{name} is present but is not pinned to {K_VERSION}")
            return None
        tools[name] = executable
    if missing:
        results.add("pinned_k_tools", "UNAVAILABLE", f"missing pinned external K commands: {', '.join(missing)}")
        return None
    timeout = shutil.which("timeout")
    if timeout is None:
        results.add("pinned_k_tools", "UNAVAILABLE", "GNU timeout is missing; LLVM hook abort cannot be contained")
        return None
    results.add("pinned_k_tools", "PASS", f"kompile/kast/kparse/krun are pinned to {K_VERSION}")
    return tools


DIRECT_LABELS = {
    "sequence": "sequence",
    "___KRS-M3B-CALC-SYNTAX_Stmt_Stmt_Stmt": "sequence",
    "assign": "assign",
    "_=_;_KRS-M3B-CALC-SYNTAX_Stmt_Id_Expr": "assign",
    "add": "add",
    "_+__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr": "add",
    "mul": "mul",
    "_*__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr": "mul",
}

GENERATED_PRODUCTION_LABELS = {
    "add",
    "and",
    "assign",
    "div",
    "eq",
    "ge",
    "gt",
    "le",
    "lt",
    "mul",
    "ne",
    "neg",
    "not",
    "or",
    "sequence",
    "sub",
}


def normalize_label(name: str) -> str:
    direct = DIRECT_LABELS.get(name)
    if direct is not None:
        return f"m3b:{direct}"
    if name.startswith("#freezer"):
        match = re.search(r"(\d+)_$", name)
        if match is None:
            raise ValueError(f"unknown freezer label shape {name!r}")
        body = name[len("#freezer") : match.start()]
        aliases = {
            "add": ("add", "_+__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr"),
            "mul": ("mul", "_*__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr"),
            "assign": ("assign", "_=_;_KRS-M3B-CALC-SYNTAX_Stmt_Id_Expr"),
        }
        matches = [logical for logical, values in aliases.items() if body in values]
        if len(matches) != 1:
            raise ValueError(f"unrecognized M3B freezer label {name!r}")
        return f"m3b:freezer:{matches[0]}:{match.group(1)}"
    if "KRS-M3B-" in name:
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


def validate_generated_term(term: Any) -> None:
    if not isinstance(term, dict) or not isinstance(term.get("node"), str):
        raise ValueError(f"unsupported generated KAST term {term!r}")
    node = term["node"]
    if node == "KApply":
        if set(term) != {"node", "label", "arity", "args"}:
            raise ValueError(f"unexpected generated KApply keys {sorted(term)}")
        label = term["label"]
        if not isinstance(label, dict) or set(label) != {"node", "name", "params"}:
            raise ValueError(f"unsupported generated label shape {label!r}")
        if label["node"] != "KLabel" or label["params"] != [] or not isinstance(label["name"], str):
            raise ValueError(f"unsupported generated label {label!r}")
        name = label["name"]
        fixed = {"<generatedTop>", "<generatedCounter>", "<k>", "<env>", ".Map", "_Map_", "_|->_"}
        if name not in fixed and name not in GENERATED_PRODUCTION_LABELS and not name.startswith("#freezer"):
            raise ValueError(f"unrecognized generated KLabel {name!r}")
        if name.startswith("#freezer"):
            normalize_label(name)
        if term["arity"] != len(term["args"]):
            raise ValueError("generated KApply arity differs from args")
        for argument in term["args"]:
            validate_generated_term(argument)
    elif node == "KToken":
        if set(term) != {"node", "sort", "token"} or not isinstance(term["token"], str):
            raise ValueError(f"unsupported generated KToken {term!r}")
        FROZEN.validate_sort(term["sort"])
    elif node == "KSequence":
        if set(term) != {"node", "arity", "items"} or term["arity"] != len(term["items"]):
            raise ValueError(f"unsupported generated KSequence {term!r}")
        for item in term["items"]:
            validate_generated_term(item)
    else:
        raise ValueError(f"unsupported generated KAST node {node!r}")


def generated_envelope(output: str) -> dict[str, Any]:
    start = output.find("{")
    if start < 0:
        raise ValueError("generated KAST output has no JSON envelope")
    value = json.loads(output[start:])
    if set(value) != {"format", "version", "term"}:
        raise ValueError(f"unexpected generated KAST envelope keys {sorted(value)}")
    if value["format"] != "KAST" or value["version"] != 4:
        raise ValueError(
            f"expected generated KAST v4, got {value.get('format')} v{value.get('version')}"
        )
    validate_generated_term(value["term"])
    return value


def generated_oracle_call(function: Any, *arguments: Any) -> Any:
    """Run one frozen helper with the generated-label envelope validator."""
    original = FROZEN.envelope
    FROZEN.envelope = generated_envelope
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
    for path in sorted(FROZEN.ACCEPTED.glob("*.calc")):
        parsed = FROZEN.run(
            [tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", "--output", "json", str(path)],
            timeout=60,
        )
        if parsed.returncode != 0:
            raise RuntimeError(f"generated parse failed for {path.name}: {FROZEN.compact(parsed)}")
        term = generated_envelope(parsed.stdout)["term"]
        trees[path.name] = term
        portable = FROZEN.run(
            [tools["kparse"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", str(path)],
            timeout=60,
        )
        if portable.returncode != 0 or "Lbl" not in portable.stdout:
            raise RuntimeError(f"generated kparse failed for {path.name}: {FROZEN.compact(portable)}")
        pretty = FROZEN.run(
            [tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", "--output", "program", str(path)],
            timeout=60,
        )
        if pretty.returncode != 0:
            raise RuntimeError(f"generated unparse failed for {path.name}: {FROZEN.compact(pretty)}")
        roundtrip = workspace / f"generated-roundtrip-{path.name}"
        roundtrip.write_text(pretty.stdout, encoding="utf-8")
        reparsed = FROZEN.run(
            [tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", "--output", "json", str(roundtrip)],
            timeout=60,
        )
        if reparsed.returncode != 0:
            raise RuntimeError(f"generated reparse failed for {path.name}: {FROZEN.compact(reparsed)}")
        reparsed_term = generated_envelope(reparsed.stdout)["term"]
        if FROZEN.canonical(term) != FROZEN.canonical(reparsed_term):
            raise RuntimeError(f"generated parse/unparse/parse changed {path.name}")
        unparsed[path.name] = pretty.stdout.strip()
    return trees, unparsed


def compile_generated(kompile: str, source: Path, output: Path) -> subprocess.CompletedProcess[bytes]:
    return run(
        [
            kompile,
            source,
            "--main-module",
            MODULE,
            "--syntax-module",
            MODULE,
            "--backend",
            "llvm",
            "--emit-json",
            "--output-definition",
            output,
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
        results.add("frozen_corpus", "FAIL", "frozen M3B handwritten/corpus source hashes drifted")
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
        results.add("generated_compile", "PASS", "production-emitted .k compiles with pinned K 7.1.337")

        reference_trees, reference_unparsed = FROZEN.parse_accepted(
            tools, reference_definition, workspace
        )
        if FROZEN.aggregate(reference_trees) != pins.get("accepted_tree_aggregate_sha256"):
            raise ValueError("frozen accepted-tree aggregate differs")
        if FROZEN.aggregate(reference_unparsed) != pins.get("unparse_aggregate_sha256"):
            raise ValueError("frozen unparse aggregate differs")
        generated_trees, generated_unparsed = generated_parse(
            tools, generated_definition, workspace
        )
        assert_term_maps_equal(generated_trees, reference_trees, "accepted parse tree")
        if generated_unparsed != reference_unparsed:
            raise ValueError("generated concrete unparse output differs from frozen oracle")
        results.add(
            "parse_unparse",
            "MATCH",
            "five full KAST v4 trees match modulo declared production symbols and round-trip to exact frozen programs",
        )

        reference_finals, reference_trace = FROZEN.execute_accepted(
            tools["krun"], reference_definition
        )
        if FROZEN.aggregate(reference_finals) != pins.get("final_state_aggregate_sha256"):
            raise ValueError("frozen final-state aggregate differs")
        if FROZEN.aggregate(reference_trace) != pins.get("llvm_trace_aggregate_sha256"):
            raise ValueError("frozen trace aggregate differs")
        generated_finals, generated_trace = generated_oracle_call(
            FROZEN.execute_accepted, tools["krun"], generated_definition
        )
        assert_term_maps_equal(generated_finals, reference_finals, "final state")
        assert_term_maps_equal(generated_trace, reference_trace, "LLVM trace state")
        if len(generated_trace) != 51:
            raise ValueError(f"expected 51 depth-indexed generated states, found {len(generated_trace)}")
        results.add(
            "execution_traces",
            "MATCH",
            "five exact rewrite counts/final maps and all 51 LLVM states match the frozen oracle modulo declared production/freezer labels",
        )

        reference_stuck, reference_division = FROZEN.verify_rejections(
            tools, reference_definition
        )
        rejection_pins = pins.get("rejection_sha256", {})
        if FROZEN.aggregate(reference_stuck) != rejection_pins.get("stuck_state_aggregate"):
            raise ValueError("frozen stuck-state aggregate differs")
        if hashlib.sha256(reference_division.encode()).hexdigest() != rejection_pins.get("division_error"):
            raise ValueError("frozen division diagnostic differs")
        generated_stuck, generated_division = generated_oracle_call(
            FROZEN.verify_rejections, tools, generated_definition
        )
        assert_term_maps_equal(generated_stuck, reference_stuck, "stuck state")
        if generated_division != reference_division:
            raise ValueError("generated division-by-zero hook diagnostic differs")
        FROZEN.verify_induced_diagnostic(tools["kompile"], workspace)
        results.add(
            "rejections_diagnostics",
            "MATCH",
            "two syntax locations, two exact stuck states, division hook error, and frozen induced-token diagnostic are exact",
        )
    except (OSError, ValueError, RuntimeError, json.JSONDecodeError) as error:
        results.add("differential_oracle", "FAIL", str(error))


def main() -> int:
    results = Results()
    source_contract(results)
    rust_gates(results)
    with tempfile.TemporaryDirectory(prefix="krs-m3b-rust-definition-") as temporary:
        workspace = Path(temporary)
        # Reuse the workspace Cargo target.  The selected standalone package
        # still receives its own Cargo-owned collector target through metadata;
        # allocating another complete workspace target here can require several
        # gigabytes without adding acceptance coverage.
        target = ROOT / "target"
        binary = build_cli(results, target)
        emitted: tuple[str, Path] | None = None
        if binary is not None:
            emitted = cli_gates(results, binary, target, workspace)
        if emitted is not None:
            tools = k_tools(results)
            if tools is not None:
                _, directory = emitted
                differential_oracle(results, tools, directory / "definition.k", workspace)

    if results.failed:
        print("\nRust-authored M3B acceptance: FAIL")
        return 1
    if results.unavailable:
        print("\nRust-authored M3B acceptance: UNAVAILABLE")
        return 0
    print("\nRust-authored M3B acceptance: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
