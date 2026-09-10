#!/usr/bin/env python3
"""Strict external acceptance oracle for the production KRS CLI."""

from __future__ import annotations

import hashlib
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
FIXTURE = HERE / "fixtures" / "m2"
AMBIGUOUS = HERE / "fixtures" / "ambiguous"
PINS = HERE / "pins.json"
K_VERSION = "v7.1.337"
PACKAGE = "krs-cli-oracle-semantics"
EXPECTED_K_FILES = {
    ".krs-artifacts",
    "definition-ir.json",
    "definition.k",
    "descriptor-bundle.json",
    "semantic-ir.json",
    "sources.json",
    "symbols.json",
}


class Results:
    def __init__(self) -> None:
        self.failed = False

    def add(self, name: str, status: str, detail: str, *, required: bool = True) -> None:
        print(f"{status:11} {name}: {detail}")
        if required and status not in {"PASS", "MATCH"}:
            self.failed = True


def run(
    command: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 300,
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        command,
        cwd=cwd,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )


def compact(process: subprocess.CompletedProcess[bytes], limit: int = 1000) -> str:
    output = b"\n".join(part.strip() for part in (process.stdout, process.stderr) if part.strip())
    text = output.decode("utf-8", errors="replace")
    for path in (ROOT, HERE, Path(tempfile.gettempdir())):
        text = text.replace(str(path), "<PATH>")
    return text[:limit] + ("..." if len(text) > limit else "")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def build_cli(results: Results) -> Path | None:
    cargo = shutil.which("cargo")
    if cargo is None:
        results.add("tool_cargo", "FAIL", "cargo is not available on PATH")
        return None
    process = run(
        [
            cargo,
            "build",
            "--locked",
            "--manifest-path",
            str(ROOT / "Cargo.toml"),
            "-p",
            "krs-cli",
            "--bin",
            "krs",
        ],
        cwd=ROOT,
    )
    binary = ROOT / "target" / "debug" / ("krs.exe" if os.name == "nt" else "krs")
    ok = process.returncode == 0 and binary.is_file()
    results.add(
        "cli_binary",
        "PASS" if ok else "FAIL",
        f"built real CLI executable {binary}" if ok else compact(process),
    )
    return binary if ok else None


def materialize(destination: Path) -> Path:
    shutil.copytree(FIXTURE, destination)
    template = destination / "Cargo.toml.in"
    manifest = template.read_text(encoding="utf-8").replace(
        "@KRS_CRATE_PATH@",
        json.dumps(str((ROOT / "crates" / "krs").resolve())),
    )
    (destination / "Cargo.toml").write_text(manifest, encoding="utf-8")
    template.unlink()
    return destination / "Cargo.toml"


def cli_command(
    binary: Path,
    command: str,
    manifest: Path,
    target: Path,
    *,
    package: str = PACKAGE,
    definition: str | None = "main",
    output: Path | None = None,
) -> subprocess.CompletedProcess[bytes]:
    arguments = [
        str(binary),
        command,
        "--manifest-path",
        str(manifest),
        "--package",
        package,
    ]
    if definition is not None:
        arguments.extend(["--definition", definition])
    if output is not None:
        arguments.extend(["--output", str(output)])
    environment = os.environ.copy()
    environment["CARGO_TARGET_DIR"] = str(target)
    environment["CARGO_NET_OFFLINE"] = "true"
    environment["CARGO_TERM_COLOR"] = "never"
    return run(arguments, cwd=manifest.parent, env=environment)


def assert_no_leaks(name: str, document: Any, raw: bytes, forbidden_paths: list[Path]) -> None:
    text = raw.decode("utf-8")
    forbidden_tokens = ("TypeId", "KCell::new")
    for token in forbidden_tokens:
        if token in text:
            raise ValueError(f"{name} leaks forbidden host token {token!r}")
    if re.search(r"\bSelf\b", text):
        raise ValueError(f"{name} leaks the Rust-only `Self` spelling")
    if re.search(r"(?<![A-Za-z])KCell(?![A-Za-z])", text):
        raise ValueError(f"{name} leaks the Rust wrapper `KCell` spelling")
    if re.search(r"\b0x[0-9a-fA-F]{6,}\b", text):
        raise ValueError(f"{name} appears to contain a pointer address")
    for path in forbidden_paths:
        if str(path) in text:
            raise ValueError(f"{name} leaks absolute path {path}")

    def visit(value: Any) -> None:
        if isinstance(value, dict):
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)
        elif isinstance(value, str) and Path(value).is_absolute():
            raise ValueError(f"{name} contains absolute JSON path {value!r}")

    visit(document)


def verify_expanded_source(raw: bytes, forbidden_paths: list[Path]) -> None:
    source = raw.decode("utf-8")
    required = (
        "// @generated by `krs expand`; deterministic layer-2 reference surface.",
        "#[krs::sort]\npub trait M2Obj: KResult {}",
        '#[krs::constructor(sort = M2Obj, syntax = "foo")]\npub struct Foo;',
        '#[krs::configuration(root = "machine")]\npub struct Machine {',
        "krs::configuration::KCell::new(krs::k![Foo])",
        "pub fn foo_to_bar(Foo: krs::Term<dyn M2Obj>) -> krs::Term<dyn M2Obj>",
    )
    missing = [fragment for fragment in required if fragment not in source]
    if missing:
        raise ValueError(f"expanded Rust source omits expected fragments: {missing}")
    for path in forbidden_paths:
        if str(path) in source:
            raise ValueError(f"expand.rs leaks absolute path {path}")


def verify_k_artifacts(directory: Path, forbidden_paths: list[Path]) -> dict[str, bytes]:
    names = {path.name for path in directory.iterdir()}
    if names != EXPECTED_K_FILES:
        raise ValueError(f"emit-k wrote {sorted(names)}, expected {sorted(EXPECTED_K_FILES)}")
    marker = (directory / ".krs-artifacts").read_text(encoding="utf-8")
    if marker != "KRS artifact directory schema 1; safe to update.\n":
        raise ValueError(f"unexpected artifact ownership marker: {marker!r}")
    artifacts = {
        name: (directory / name).read_bytes()
        for name in sorted(EXPECTED_K_FILES - {".krs-artifacts"})
    }
    source = artifacts["definition.k"].decode("utf-8")
    required = (
        'syntax M2Obj ::= "bar" [symbol(bar)]',
        'syntax M2Obj ::= "foo" [symbol(foo)]',
        "syntax KItem ::= KResult",
        "syntax KResult ::= M2Obj",
        "<k> foo </k>",
        "rule foo => bar",
    )
    missing = [line for line in required if line not in source]
    if missing:
        raise ValueError(f"canonical K omits expected theory lines: {missing}")
    for name in (
        "definition-ir.json",
        "descriptor-bundle.json",
        "semantic-ir.json",
        "symbols.json",
        "sources.json",
    ):
        document = json.loads(artifacts[name])
        assert_no_leaks(name, document, artifacts[name], forbidden_paths)
    for path in forbidden_paths:
        if str(path) in source:
            raise ValueError(f"definition.k leaks absolute path {path}")
    return artifacts


def positive_run(binary: Path, workspace: Path, results: Results) -> dict[str, bytes] | None:
    language = workspace / "language"
    manifest = materialize(language)
    target = workspace / "target"
    emitted = workspace / "emitted"
    native = workspace / "native"

    check = cli_command(binary, "check", manifest, target)
    expected_check = b"KRS check passed: 9 descriptors, 1 semantic modules\n"
    results.add(
        f"{workspace.name}_check",
        "PASS" if check.returncode == 0 and check.stdout == expected_check else "FAIL",
        "complete nine-descriptor theory validated" if check.returncode == 0 and check.stdout == expected_check else compact(check),
    )
    if check.returncode != 0:
        return None

    expand = cli_command(binary, "expand", manifest, target)
    try:
        if expand.returncode != 0:
            raise ValueError(compact(expand))
        verify_expanded_source(expand.stdout, [ROOT, workspace, language, target])
        results.add(f"{workspace.name}_expand", "PASS", f"canonical expanded Rust sha256={sha256(expand.stdout)}")
    except ValueError as error:
        results.add(f"{workspace.name}_expand", "FAIL", str(error))
        return None

    emit = cli_command(binary, "emit-k", manifest, target, output=emitted)
    expected_emit = b"emitted descriptor-bundle.json, semantic-ir.json, definition-ir.json, definition.k, symbols.json, sources.json\n"
    try:
        if emit.returncode != 0 or emit.stdout != expected_emit:
            raise ValueError(compact(emit))
        artifacts = verify_k_artifacts(emitted, [ROOT, workspace, language, target])
        results.add(f"{workspace.name}_emit_k", "PASS", "exact owned canonical K artifact set")
    except (OSError, ValueError, json.JSONDecodeError) as error:
        results.add(f"{workspace.name}_emit_k", "FAIL", str(error))
        return None

    build = cli_command(binary, "build", manifest, target, output=native)
    expected_build = b"built definition.kore, syntaxDefinition.kore, macros.kore\n"
    native_names = {
        ".krs-artifacts",
        "definition.kore",
        "macros.kore",
        "syntaxDefinition.kore",
    }
    observed_names = {path.name for path in native.iterdir()} if native.is_dir() else set()
    build_ok = (
        build.returncode == 0
        and build.stdout == expected_build
        and observed_names == native_names
        and all((native / name).stat().st_size > 0 for name in native_names)
    )
    results.add(
        f"{workspace.name}_build",
        "PASS" if build_ok else "FAIL",
        "structured k-rust compilation produced the exact native artifact set"
        if build_ok else compact(build),
    )
    if not build_ok:
        return None
    for name in sorted(native_names):
        artifacts[f"native/{name}"] = (native / name).read_bytes()
    artifacts["expand.rs"] = expand.stdout
    return artifacts


def verify_pins(results: Results, artifacts: dict[str, bytes]) -> None:
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    fixture_actual = {
        "Cargo.toml.in": sha256((FIXTURE / "Cargo.toml.in").read_bytes()),
        "src/lib.rs": sha256((FIXTURE / "src" / "lib.rs").read_bytes()),
    }
    results.add(
        "fixture_pins",
        "PASS" if fixture_actual == pins["fixture_sha256"] else "FAIL",
        f"sha256={fixture_actual}",
    )
    actual = {name: sha256(data) for name, data in sorted(artifacts.items())}
    results.add(
        "artifact_pins",
        "PASS" if actual == pins["artifacts_sha256"] else "FAIL",
        f"sha256={actual}",
    )


def verify_relocation(results: Results, left: dict[str, bytes], right: dict[str, bytes]) -> None:
    names = sorted(set(left) | set(right))
    differences = [name for name in names if left.get(name) != right.get(name)]
    results.add(
        "clean_relocation",
        "MATCH" if not differences else "FAIL",
        "two clean, differently located workspaces produced byte-identical bundle/K/sidecars"
        if not differences else f"different artifacts: {differences}",
    )


def negative_cases(binary: Path, workspace: Path, results: Results) -> None:
    manifest = materialize(workspace / "missing-language")
    target = workspace / "negative-target"

    missing_option = cli_command(binary, "check", manifest, target, definition=None)
    option_ok = missing_option.returncode == 2 and b"missing --definition" in missing_option.stderr
    results.add("missing_facet_option", "PASS" if option_ok else "FAIL", "CLI rejects implicit facet selection" if option_ok else compact(missing_option))

    missing_facet = cli_command(binary, "check", manifest, target, definition="absent")
    facet_ok = missing_facet.returncode != 0 and b"declares no KRS definition facet `absent`" in missing_facet.stderr
    results.add("missing_facet", "PASS" if facet_ok else "FAIL", "planner rejects nonexistent explicit facet" if facet_ok else compact(missing_facet))

    ambiguous = workspace / "ambiguous"
    shutil.copytree(AMBIGUOUS, ambiguous)
    ambiguous_process = cli_command(
        binary,
        "expand",
        ambiguous / "Cargo.toml",
        workspace / "ambiguous-target",
        package="duplicated-semantics",
    )
    ambiguity_ok = ambiguous_process.returncode != 0 and b"matches 2 resolved packages" in ambiguous_process.stderr
    results.add("ambiguous_package", "PASS" if ambiguity_ok else "FAIL", "name selector rejects two resolved package identities" if ambiguity_ok else compact(ambiguous_process))

    broken_manifest = materialize(workspace / "broken-language")
    broken_source = broken_manifest.parent / "src" / "lib.rs"
    with broken_source.open("a", encoding="utf-8") as output:
        output.write('\ncompile_error!("KRS CLI oracle induced Cargo failure");\n')
    broken = cli_command(binary, "check", broken_manifest, workspace / "broken-target")
    broken_ok = (
        broken.returncode != 0
        and b'"stage":"rust-expansion"' in broken.stderr
        and b"KRS CLI oracle induced Cargo failure" in broken.stderr
    )
    results.add("cargo_check_failure", "PASS" if broken_ok else "FAIL", "krs check fails at Rust expansion with an authored diagnostic" if broken_ok else compact(broken))

    safe_manifest = materialize(workspace / "safe-language")
    unsafe_output = workspace / "unsafe-output"
    unsafe_output.mkdir()
    sentinel = b"do not overwrite\n"
    (unsafe_output / "definition.k").write_bytes(sentinel)
    (unsafe_output / "unrelated.txt").write_bytes(sentinel)
    unsafe = cli_command(binary, "emit-k", safe_manifest, workspace / "safe-target", output=unsafe_output)
    preserved = (
        unsafe.returncode != 0
        and b"refusing to replace non-KRS artifact directory" in unsafe.stderr
        and (unsafe_output / "definition.k").read_bytes() == sentinel
        and (unsafe_output / "unrelated.txt").read_bytes() == sentinel
        and {item.name for item in unsafe_output.iterdir()} == {"definition.k", "unrelated.txt"}
    )
    results.add("unsafe_output", "PASS" if preserved else "FAIL", "nonempty unowned output rejected without changing bytes" if preserved else compact(unsafe))


def reference_execution(results: Results, artifacts: dict[str, bytes], workspace: Path) -> None:
    executables = {name: shutil.which(name) for name in ("kompile", "krun")}
    missing = [name for name, executable in executables.items() if executable is None]
    if missing:
        results.add("reference_execution", "UNAVAILABLE", f"missing {', '.join(missing)}; K compile/execution did not run", required=False)
        return
    versions = {}
    for name, executable in executables.items():
        assert executable is not None
        process = run([executable, "--version"], timeout=30)
        versions[name] = b"\n".join((process.stdout, process.stderr)).decode("utf-8", errors="replace")
    mismatched = [name for name, version in versions.items() if K_VERSION not in version]
    if mismatched:
        results.add("reference_execution", "MISMATCH", f"present tools {mismatched} are not pinned {K_VERSION}; execution was refused")
        return

    workspace.mkdir(parents=True)
    source = workspace / "definition.k"
    source.write_bytes(artifacts["definition.k"])
    match = re.search(r"(?m)^module\s+([A-Za-z0-9-]+)\s*$", source.read_text(encoding="utf-8"))
    if match is None:
        results.add("reference_execution", "FAIL", "canonical K has no module declaration")
        return
    module = match.group(1)
    definition = workspace / "compiled-definition"
    compile_process = run(
        [
            executables["kompile"],
            str(source),
            "--main-module",
            module,
            "--syntax-module",
            module,
            "--backend",
            "llvm",
            "--emit-json",
            "--output-definition",
            str(definition),
        ],
        timeout=240,
    )
    if compile_process.returncode != 0:
        results.add("reference_execution", "FAIL", compact(compile_process))
        return
    initial = run([executables["krun"], "--definition", str(definition), "--depth", "0", "--output", "kore"], timeout=60)
    final = run([executables["krun"], "--definition", str(definition), "--output", "kore"], timeout=60)
    ok = (
        initial.returncode == 0
        and final.returncode == 0
        and b"Lblfoo" in initial.stdout
        and b"Lblbar" not in initial.stdout
        and b"Lblbar" in final.stdout
        and b"Lblfoo" not in final.stdout
    )
    results.add("reference_execution", "PASS" if ok else "FAIL", f"K {K_VERSION} compiled canonical output and executed foo -> bar" if ok else compact(final))


def main() -> int:
    results = Results()
    binary = build_cli(results)
    if binary is None:
        return 1
    with tempfile.TemporaryDirectory(prefix="krs-cli-oracle-a-") as first_raw, tempfile.TemporaryDirectory(prefix="krs-cli-oracle-relocated-b-") as second_raw:
        first_root = Path(first_raw)
        second_root = Path(second_raw) / "different" / "depth"
        second_root.mkdir(parents=True)
        first = positive_run(binary, first_root / "run-a", results)
        second = positive_run(binary, second_root / "run-b", results)
        if first is not None and second is not None:
            verify_relocation(results, first, second)
            verify_pins(results, first)
            reference_execution(results, first, first_root / "reference")
        else:
            results.add("clean_relocation", "FAIL", "positive command run did not complete")
        negative_cases(binary, first_root / "negative", results)
    print("\nCLI acceptance oracle:", "FAIL" if results.failed else "PASS")
    return int(results.failed)


if __name__ == "__main__":
    sys.exit(main())
