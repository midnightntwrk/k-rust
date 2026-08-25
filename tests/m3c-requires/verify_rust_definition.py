#!/usr/bin/env python3
"""Production acceptance for the Rust-authored protocol-v11 guarded rules."""

from __future__ import annotations

from collections import Counter
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
FIXTURE = HERE / "rust-definition"
MANIFEST = FIXTURE / "Cargo.toml"
SOURCE = FIXTURE / "src" / "lib.rs"
PACKAGE = "krs-m3c-requires-rust-definition"
ARTIFACT_MARKER = b"KRS artifact directory schema 1; safe to update.\n"


class Results:
    def __init__(self) -> None:
        self.failed = False

    def add(self, name: str, passed: bool, detail: str) -> None:
        print(f"{'PASS' if passed else 'FAIL':12} {name}: {detail}")
        self.failed |= not passed


def run(
    command: list[str | Path],
    *,
    cwd: Path = ROOT,
    timeout: int = 900,
) -> subprocess.CompletedProcess[bytes]:
    environment = os.environ.copy()
    environment.setdefault("TMPDIR", "/dev/shm")
    environment.setdefault("Z3_SYS_Z3_VERSION", "4.12.2")
    environment["LC_ALL"] = "C"
    environment["LANG"] = "C"
    return subprocess.run(
        [str(part) for part in command],
        cwd=cwd,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )


def detail(process: subprocess.CompletedProcess[bytes], limit: int = 1600) -> str:
    output = b"\n".join(part.strip() for part in (process.stdout, process.stderr) if part.strip())
    text = output.decode("utf-8", errors="replace")
    return text[:limit] + ("…" if len(text) > limit else "")


def cli(binary: Path, command: str, output: Path | None = None) -> subprocess.CompletedProcess[bytes]:
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
    return run(arguments)


def source_contract(results: Results) -> None:
    source = SOURCE.read_text(encoding="utf-8")
    required = (
        '#[k::rule(label = "ordinary-positive")]',
        "#[k::requires(int::gt(value, 0))]",
        '#[k::rule(label = "configuration-within")]',
        "#[k::requires(int::le(value, limit))]",
        "cells! {",
        "tail @ ..",
    )
    valid = source.count("#[k::requires(") == 2 and all(item in source for item in required)
    results.add(
        "authored_surface",
        valid,
        "one ordinary and one fixed-configuration rule have typed nontrivial guards",
    )


def cargo_gates(results: Results) -> None:
    commands = [
        ["cargo", "fmt", "--manifest-path", MANIFEST, "--", "--check"],
        ["cargo", "check", "--locked", "--manifest-path", MANIFEST],
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
        ["cargo", "test", "--locked", "--manifest-path", MANIFEST],
    ]
    processes = [run(command) for command in commands]
    documented = run(
        ["cargo", "doc", "--locked", "--manifest-path", MANIFEST, "--no-deps"]
    )
    passed = all(process.returncode == 0 for process in [*processes, documented])
    failed = next(
        (process for process in [*processes, documented] if process.returncode != 0),
        None,
    )
    results.add(
        "cargo_gates",
        passed,
        "fmt/check/clippy/test/doc pass" if failed is None else detail(failed),
    )


def descriptor_contract(raw: bytes) -> None:
    bundle = json.loads(raw)
    if bundle.get("protocol_version") != 11:
        raise ValueError("collector output is not protocol v11")
    descriptors = bundle.get("descriptors")
    if not isinstance(descriptors, list):
        raise ValueError("descriptors are not an array")
    counts = Counter(item.get("id", {}).get("item_kind") for item in descriptors)
    if counts != Counter({"sort": 1, "constructor": 1, "grammar": 2, "configuration": 1, "rule": 2}):
        raise ValueError(f"descriptor kinds differ: {counts}")
    rules = {
        item.get("descriptor", {}).get("label", {}).get("name"): item
        for item in descriptors
        if item.get("id", {}).get("item_kind") == "rule"
    }
    expected = {
        "ordinary-positive": "int_greater",
        "configuration-within": "int_less_equal",
    }
    if set(rules) != set(expected):
        raise ValueError(f"guarded labels differ: {set(rules)}")
    for label, operation in expected.items():
        condition = rules[label].get("descriptor", {}).get("requires")
        application = (
            condition.get("term", {})
            .get("reference", {})
            .get("application", {})
            if isinstance(condition, dict)
            else None
        )
        if application != {"application_source": "builtin", "application": operation}:
            raise ValueError(f"{label} has the wrong typed condition head: {application}")
        roles = {
            origin.get("key", {}).get("role")
            for origin in rules[label].get("provenance", {}).get("origins", [])
        }
        required_roles = {
            "rule_requires",
            "rule_requires_path",
            "rule_requires_application_head",
            "rule_requires_reference",
        }
        if label == "ordinary-positive":
            required_roles.add("rule_requires_literal")
        if not required_roles <= roles:
            raise ValueError(f"{label} omits condition provenance roles: {required_roles - roles}")


def artifact_bytes(directory: Path) -> dict[str, bytes]:
    return {
        path.name: path.read_bytes()
        for path in sorted(directory.iterdir())
        if path.is_file()
    }


def emitted_contract(directory: Path) -> None:
    expected = {
        ".krs-artifacts",
        "definition-ir.json",
        "definition.k",
        "descriptor-bundle.json",
        "semantic-ir.json",
        "symbols.json",
        "sources.json",
    }
    if {path.name for path in directory.iterdir()} != expected:
        raise ValueError("emit-k artifact set differs")
    if (directory / ".krs-artifacts").read_bytes() != ARTIFACT_MARKER:
        raise ValueError("emit-k ownership marker differs")
    source = (directory / "definition.k").read_text(encoding="utf-8")
    required = (
        "rule [configuration-within]:",
        "requires V76616C7565:Int <=Int V6C696D6974:Int",
        "requires V76616C7565:Int >Int 0 [label(ordinary-positive)]",
    )
    if not all(fragment in source for fragment in required) or "requires true" in source:
        raise ValueError("canonical K does not retain both nontrivial conditions")
    sources = json.loads((directory / "sources.json").read_text(encoding="utf-8"))
    entries = sources.get("entries")
    if sources.get("schema_version") != 2 or not isinstance(entries, list):
        raise ValueError("source sidecar is not schema v2")
    counts = Counter(entry.get("node_kind") for entry in entries)
    if counts["rule_condition"] != 2 or counts["rule"] != 2:
        raise ValueError(f"source sidecar guarded-node counts differ: {counts}")


def built_contract(directory: Path) -> None:
    expected = {".krs-artifacts", "definition.kore", "syntaxDefinition.kore", "macros.kore"}
    if {path.name for path in directory.iterdir()} != expected:
        raise ValueError("build artifact set differs")
    if (directory / ".krs-artifacts").read_bytes() != ARTIFACT_MARKER:
        raise ValueError("build ownership marker differs")
    definition = (directory / "definition.kore").read_text(encoding="utf-8")
    if "ordinary-positive" not in definition or "configuration-within" not in definition:
        raise ValueError("compiled KORE omits guarded rule identities")
    if not (directory / "syntaxDefinition.kore").read_bytes():
        raise ValueError("syntaxDefinition.kore is empty")


def production_gates(results: Results, workspace: Path) -> None:
    binary = ROOT / "target" / "debug" / "krs"
    built_cli = run(["cargo", "build", "--locked", "-p", "krs-cli", "--bin", "krs"])
    if built_cli.returncode != 0 or not binary.is_file():
        results.add("cli_build", False, detail(built_cli))
        return
    results.add("cli_build", True, "production workspace CLI built")

    checks = [cli(binary, "check") for _ in range(2)]
    expected_check = b"KRS check passed: 7 descriptors, 1 semantic modules\n"
    checks_ok = all(item.returncode == 0 and item.stdout == expected_check for item in checks)
    results.add(
        "cli_check",
        checks_ok,
        "two semantic/Definition passes agree"
        if checks_ok
        else detail(next(item for item in checks if item.returncode != 0 or item.stdout != expected_check)),
    )

    expansions = [cli(binary, "expand") for _ in range(2)]
    try:
        if any(item.returncode != 0 for item in expansions):
            raise ValueError(detail(next(item for item in expansions if item.returncode != 0)))
        if expansions[0].stdout != expansions[1].stdout:
            raise ValueError("repeated protocol bytes differ")
        descriptor_contract(expansions[0].stdout)
        results.add("cli_expand", True, "deterministic protocol-v11 conditions and provenance")
    except (ValueError, json.JSONDecodeError) as error:
        results.add("cli_expand", False, str(error))

    emitted = [workspace / "emitted-a", workspace / "emitted-b"]
    emissions = [cli(binary, "emit-k", output) for output in emitted]
    try:
        if any(item.returncode != 0 for item in emissions):
            raise ValueError(detail(next(item for item in emissions if item.returncode != 0)))
        for directory in emitted:
            emitted_contract(directory)
        if artifact_bytes(emitted[0]) != artifact_bytes(emitted[1]):
            raise ValueError("repeated emitted artifact bytes differ")
        results.add("cli_emit_k", True, "canonical guarded K and schema-v2 sidecars are deterministic")
    except (OSError, ValueError, json.JSONDecodeError) as error:
        results.add("cli_emit_k", False, str(error))

    built = workspace / "built"
    build = cli(binary, "build", built)
    try:
        expected_stdout = b"built definition.kore, syntaxDefinition.kore, macros.kore\n"
        if build.returncode != 0 or build.stdout != expected_stdout:
            raise ValueError(detail(build))
        built_contract(built)
        results.add("cli_native_build", True, "both guarded rule families compile to reparsable KORE")
    except (OSError, ValueError) as error:
        results.add("cli_native_build", False, str(error))


def main() -> int:
    results = Results()
    source_contract(results)
    cargo_gates(results)
    shared = Path("/dev/shm")
    temporary_root = shared if shared.is_dir() and os.access(shared, os.W_OK) else None
    with tempfile.TemporaryDirectory(prefix="krs-m3c-requires-rust-", dir=temporary_root) as value:
        production_gates(results, Path(value))

    oracle = run([sys.executable, HERE / "verify.py"], cwd=HERE)
    oracle_ok = oracle.returncode == 0 and b"M3C requires adjunct PASSED" in oracle.stdout
    results.add(
        "independent_oracle",
        oracle_ok,
        "frozen K structure, execution, and diagnostics remain exact"
        if oracle_ok
        else detail(oracle),
    )

    if results.failed:
        print("\nRust-authored M3C requires acceptance: FAIL")
        return 1
    print("\nRust-authored M3C requires acceptance: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
