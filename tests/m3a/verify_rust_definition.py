#!/usr/bin/env python3
"""End-to-end acceptance checks for the explicit Rust-authored M3A definition."""

from __future__ import annotations

from collections import Counter
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
PACKAGE = "krs-m3a-rust-definition"
MODULE = "KRS-M3A-EXPR"
K_VERSION = "v7.1.337"
ACCEPTED = HERE / "corpus" / "accepted"
SYNTAX_REJECTED = HERE / "corpus" / "rejected" / "syntax"
TYPE_REJECTED = HERE / "corpus" / "rejected" / "semantic-type"

EXPECTED_KIND_COUNTS = {
    "sort": 4,
    "constructor": 14,
    "grammar": 19,
    "configuration": 1,
    "rule": 18,
}

EXPECTED_RESULTS = {
    "arithmetic-precedence.expr": "7",
    "parentheses-override.expr": "9",
    "subtraction-left.expr": "3",
    "division-left.expr": "1",
    "division-parenthesized.expr": "4",
    "unary-binding.expr": "1",
    "comparison-equality.expr": "true",
    "boolean-precedence.expr": "true",
    "short-circuit-precedence.expr": "true",
}


class Results:
    def __init__(self) -> None:
        self.failed = False

    def add(self, name: str, status: str, detail: str, *, required: bool = True) -> None:
        print(f"{status:12} {name}: {detail}")
        if required and status not in {"PASS", "MATCH", "SKIP"}:
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


def compact(process: subprocess.CompletedProcess[bytes], limit: int = 1600) -> str:
    output = b"\n".join(part.strip() for part in (process.stdout, process.stderr) if part.strip())
    text = output.decode("utf-8", errors="replace")
    text = re.sub(r"/[A-Za-z0-9_.+@%/=-]+", "<PATH>", text)
    return text[:limit] + ("…" if len(text) > limit else "")


def source_contract(results: Results) -> None:
    source = SOURCE.read_text(encoding="utf-8")
    checks = {
        "constructors": source.count("#[k::constructor("),
        "rules": source.count("#[k::rule]"),
        "explicit_subsorts": source.count("#[k::subsort]"),
        "strict": source.count("#[k::strict("),
        "seqstrict": source.count("#[k::seqstrict("),
        "left_associativity_sentences": source.count("left:"),
    }
    expected = {
        "constructors": 14,
        "rules": 18,
        "explicit_subsorts": 2,
        "strict": 4,
        "seqstrict": 10,
        "left_associativity_sentences": 6,
    }
    required = (
        "impl Value for Int",
        "impl Value for Bool",
        "prefix > multiplicative > additive > comparison > equality > conjunction > disjunction",
        "k::configuration::KCell<k::builtin::KSequence>",
        "int::div(lhs, rhs)",
        "bool::not(value)",
        "And { lhs: false, rhs: _ }",
        "Or { lhs: true, rhs: _ }",
    )
    valid = checks == expected and all(fragment in source for fragment in required)
    results.add(
        "authored_surface",
        "PASS" if valid else "FAIL",
        f"counts={checks}; exact builtin injections, precedence, short-circuit patterns, and configuration",
    )
    executable_fallbacks = (
        "include_str!",
        "include_bytes!",
        "raw_k!",
        "std::fs",
        "fs::read",
    )
    no_fallback = not any(fragment in source for fragment in executable_fallbacks)
    results.add(
        "no_semantic_fallback",
        "PASS" if no_fallback else "FAIL",
        "authored Rust contains no executable handwritten-K fallback",
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

    checked = run(["cargo", "check", "--locked", "--manifest-path", MANIFEST])
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
        ]
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
        timeout=600,
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
    return run(arguments, env={**os.environ, "CARGO_TARGET_DIR": str(target)}, timeout=600)


def descriptor_kind(descriptor: dict[str, Any]) -> str:
    identity = descriptor.get("id")
    if not isinstance(identity, dict) or not isinstance(identity.get("item_kind"), str):
        raise ValueError("descriptor has no typed id.item_kind")
    return identity["item_kind"]


def bundle_contract(raw: bytes) -> dict[str, Any]:
    bundle = json.loads(raw)
    if bundle.get("protocol_version") != 6:
        raise ValueError(f"expected protocol v6, got {bundle.get('protocol_version')!r}")
    descriptors = bundle.get("descriptors")
    if not isinstance(descriptors, list):
        raise ValueError("bundle descriptors are not an array")
    counts = Counter(descriptor_kind(item) for item in descriptors)
    if dict(counts) != EXPECTED_KIND_COUNTS:
        raise ValueError(f"descriptor counts differ: {dict(counts)}")
    serialized = json.dumps(bundle, sort_keys=True)
    for builtin in ("int_add", "int_t_div", "bool_not", "bool_equal"):
        if builtin not in serialized:
            raise ValueError(f"bundle does not retain builtin identity {builtin!r}")
    for forbidden in (str(ROOT), "TypeId", "HostTypeKey"):
        if forbidden in serialized:
            raise ValueError(f"stable bundle leaks host-only value {forbidden!r}")
    return bundle


def emitted_contract(directory: Path) -> str:
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
    source = (directory / "definition.k").read_text(encoding="utf-8")
    productions = [line for line in source.splitlines() if line.strip().startswith("syntax ") and "::=" in line]
    rules = [line for line in source.splitlines() if line.strip().startswith("rule ")]
    if len(productions) != 19:
        raise ValueError(f"expected 19 productions, found {len(productions)}")
    if len(rules) != 18:
        raise ValueError(f"expected 18 rules, found {len(rules)}")
    for terminal in ('"-"', '"!"', '"*"', '"/"', '"+"', '">="', '"=="', '"&&"', '"||"'):
        if terminal not in source:
            raise ValueError(f"emitted grammar omits terminal {terminal}")
    if source.count("seqstrict") != 10:
        raise ValueError(f"expected 10 seqstrict attributes, found {source.count('seqstrict')}")
    strict_only = len(re.findall(r"(?<!seq)strict(?:\(|\b)", source))
    if strict_only != 4:
        raise ValueError(f"expected four strict attributes, found {strict_only}")
    for required in ("imports INT", "imports BOOL", "configuration <k>"):
        if required not in source:
            raise ValueError(f"emitted K omits {required!r}")
    for name in ("symbols.json", "sources.json"):
        payload = json.loads((directory / name).read_text(encoding="utf-8"))
        serialized = json.dumps(payload)
        if str(ROOT) in serialized or "TypeId" in serialized:
            raise ValueError(f"{name} leaks host-only data")
    return source


def cli_gates(results: Results, binary: Path, target: Path, workspace: Path) -> None:
    checked = cli_command(binary, "check", target)
    expected = b"KRS check passed: 56 descriptors, 1 semantic modules\n"
    results.add(
        "krs_check",
        "PASS" if checked.returncode == 0 and checked.stdout == expected else "FAIL",
        "56-descriptor structured expression theory validated"
        if checked.returncode == 0 and checked.stdout == expected
        else compact(checked),
    )
    if checked.returncode != 0:
        return

    expanded = cli_command(binary, "expand", target)
    try:
        if expanded.returncode != 0:
            raise ValueError(compact(expanded))
        bundle_contract(expanded.stdout)
        results.add("krs_expand", "PASS", "protocol-v6 descriptor kinds and builtin identities are exact")
    except (ValueError, json.JSONDecodeError) as error:
        results.add("krs_expand", "FAIL", str(error))
        return

    emitted = workspace / "emitted"
    process = cli_command(binary, "emit-k", target, output=emitted)
    try:
        if process.returncode != 0:
            raise ValueError(compact(process))
        source = emitted_contract(emitted)
        results.add("krs_emit", "PASS", "19 productions, 18 rules, exact strictness, and builtin imports emitted")
    except (OSError, ValueError, json.JSONDecodeError) as error:
        results.add("krs_emit", "FAIL", str(error))
        return
    reference_execution(results, source, workspace)


def k_tools(results: Results) -> dict[str, str] | None:
    tools: dict[str, str] = {}
    for name in ("kompile", "kast", "krun"):
        executable = shutil.which(name)
        if executable is None:
            results.add("reference_tools", "SKIP", f"{name} is unavailable", required=False)
            return None
        version = run([executable, "--version"], timeout=30)
        text = (version.stdout + version.stderr).decode("utf-8", errors="replace")
        if version.returncode != 0 or K_VERSION not in text:
            results.add("reference_tools", "FAIL", f"{name} is not pinned to {K_VERSION}")
            return None
        tools[name] = executable
    results.add("reference_tools", "PASS", f"kompile/kast/krun are pinned to {K_VERSION}")
    return tools


def reference_execution(results: Results, source: str, workspace: Path) -> None:
    tools = k_tools(results)
    if tools is None:
        return
    source_path = workspace / "definition.k"
    source_path.write_text(source, encoding="utf-8")
    modules = re.findall(r"(?m)^module\s+([A-Za-z0-9-]+)\s*$", source)
    module = MODULE if MODULE in modules else (modules[-1] if len(modules) == 1 else None)
    if module is None:
        results.add("reference_compile", "FAIL", f"cannot select emitted module from {modules}")
        return
    definition = workspace / "compiled-definition"
    compiled = run(
        [
            tools["kompile"],
            source_path,
            "--main-module",
            module,
            "--syntax-module",
            module,
            "--backend",
            "llvm",
            "--output-definition",
            definition,
        ],
        timeout=600,
    )
    if compiled.returncode != 0:
        results.add("reference_compile", "FAIL", compact(compiled))
        return
    results.add("reference_compile", "PASS", f"emitted K compiled with module {module}")

    for path in sorted(ACCEPTED.glob("*.expr")):
        parsed = run(
            [tools["kast"], "--definition", definition, "--module", module, "--sort", "Expr", "--output", "json", path],
            timeout=60,
        )
        if parsed.returncode != 0:
            results.add("accepted_programs", "FAIL", f"{path.name}: {compact(parsed)}")
            return
        executed = run([tools["krun"], "--definition", definition, "--output", "pretty", path], timeout=60)
        normalized = re.sub(r"\s+", " ", executed.stdout.decode("utf-8", errors="replace")).strip()
        expected = f"<k> {EXPECTED_RESULTS[path.name]} ~> .K </k>"
        if executed.returncode != 0 or normalized != expected:
            results.add("accepted_programs", "FAIL", f"{path.name}: {compact(executed)}")
            return
    results.add("accepted_programs", "PASS", "all nine programs parse and reach exact normal forms")

    for path in sorted(SYNTAX_REJECTED.glob("*.expr")):
        rejected = run(
            [tools["kast"], "--definition", definition, "--module", module, "--sort", "Expr", "--output", "json", path],
            timeout=60,
        )
        if rejected.returncode == 0:
            results.add("syntax_rejections", "FAIL", f"{path.name} unexpectedly parsed")
            return
    results.add("syntax_rejections", "PASS", "both malformed programs are rejected")

    for path in sorted(TYPE_REJECTED.glob("*.expr")):
        executed = run([tools["krun"], "--definition", definition, "--output", "pretty", path], timeout=60)
        normalized = re.sub(r"\s+", "", executed.stdout.decode("utf-8", errors="replace"))
        expected_fragment = "true+1~>.K" if path.name == "bool-plus-int.expr" else "!0~>.K"
        if executed.returncode != 0 or expected_fragment not in normalized:
            results.add("semantic_type_rejections", "FAIL", f"{path.name}: {compact(executed)}")
            return
    results.add("semantic_type_rejections", "PASS", "ill-typed expressions remain parsed but stuck")


def main() -> int:
    results = Results()
    source_contract(results)
    rust_gates(results)
    with tempfile.TemporaryDirectory(prefix="krs-m3a-rust-definition-") as temporary:
        workspace = Path(temporary)
        target = workspace / "target"
        binary = build_cli(results, target)
        if binary is not None:
            cli_gates(results, binary, target, workspace)
    print("\nRust-authored M3A acceptance:", "FAIL" if results.failed else "PASS")
    return int(results.failed)


if __name__ == "__main__":
    sys.exit(main())
