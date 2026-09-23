#!/usr/bin/env python3
"""Bounded acceptance gate for the language tour's smallest KRS theory."""

from __future__ import annotations

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from support.hashing import sha256_file  # noqa: E402
from support.kdefinition import EMITTED_ARTIFACTS  # noqa: E402
from support.lock import msrv  # noqa: E402
from support.process import compact, run  # noqa: E402
from support.tools import executable, rustfmt_dir, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
SOURCE = HERE / "src" / "lib.rs"
REFERENCE_SOURCE = HERE / "foo-bar.k"
PACKAGE = "krs-tour-minimal"
DEFINITION = "main"
MODULE = "KRS-TOUR-MINIMAL"


def cli_environment() -> dict[str, str]:
    return {**z3_environment(), "CARGO_TERM_COLOR": "never"}


def production_binary(override: Path | None, environment: dict[str, str]) -> Path:
    if override is not None:
        binary = override.resolve()
        if not binary.is_file():
            raise GateError(f"requested KRS binary does not exist: {binary}")
        return binary

    run(
        [
            executable("cargo"),
            "+stable",
            "build",
            "--locked",
            "-p",
            "krs-cli",
            "--bin",
            "krs",
        ],
        environment=environment,
    )
    binary = ROOT / "target" / "debug" / ("krs.exe" if os.name == "nt" else "krs")
    if not binary.is_file():
        raise GateError(f"Cargo did not produce the KRS binary at {binary}")
    return binary


def cli_command(binary: Path, operation: str, *extra: Path | str) -> list[Path | str]:
    return [
        binary,
        operation,
        "--manifest-path",
        MANIFEST,
        "--package",
        PACKAGE,
        "--definition",
        DEFINITION,
        *extra,
    ]


def verify_source_region() -> None:
    source = SOURCE.read_text(encoding="utf-8")
    opening = "// [!region definition]"
    closing = "// [!endregion definition]"
    if source.count(opening) != 1 or source.count(closing) != 1:
        raise GateError("source must contain exactly one stable `definition` Vocs region")
    if source.index(opening) >= source.index(closing):
        raise GateError("the `definition` Vocs region markers are reversed")


def verify_expansion(source: str) -> None:
    required = (
        "#[k::sort(alias = M2Obj, parents = [k::KResult])]",
        "#[k::constructors(sort = M2Obj, reference)]",
        '#[k::syntax("foo", group = "object_tier0", format = "foo")]',
        '#[k::syntax("bar", group = "object_tier0", format = "bar")]',
        "k::configuration::KCell::new(k::k![Object::Foo()])",
        '#[k::rule(label = "foo-to-bar")]',
        "crate ::Object::Foo(), tail @ ..",
        "crate ::Object::Bar(), ..tail",
    )
    missing = [fragment for fragment in required if fragment not in source]
    if missing:
        raise GateError(f"expanded reference surface omits: {missing}")
    if source.count("#[k::rule(") != 1:
        raise GateError("expanded reference surface must contain exactly one rule")


def load_json(artifacts: dict[str, bytes], name: str) -> Any:
    try:
        return json.loads(artifacts[name])
    except (KeyError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateError(f"{name} is not a valid emitted JSON artifact: {error}") from error


def verify_artifacts(directory: Path) -> dict[str, bytes]:
    names = tuple(sorted(path.name for path in directory.iterdir() if path.is_file()))
    if names != tuple(sorted(EMITTED_ARTIFACTS)):
        raise GateError(f"emit-k wrote {names}, expected {tuple(sorted(EMITTED_ARTIFACTS))}")
    artifacts = {name: (directory / name).read_bytes() for name in EMITTED_ARTIFACTS}

    marker = artifacts[".krs-artifacts"].decode("utf-8")
    if marker != "KRS artifact directory schema 1; safe to update.\n":
        raise GateError(f"unexpected artifact ownership marker: {marker!r}")

    bundle = load_json(artifacts, "descriptor-bundle.json")
    descriptors = bundle.get("descriptors")
    if bundle.get("protocol_version") != 35 or not isinstance(descriptors, list):
        raise GateError("descriptor bundle is not the expected protocol-v35 document")
    counts = Counter(
        descriptor.get("id", {}).get("item_kind") for descriptor in descriptors
    )
    expected = Counter(
        {"sort": 3, "constructor": 2, "grammar": 2, "configuration": 1, "rule": 1}
    )
    if counts != expected:
        raise GateError(f"descriptor theory differs: {counts}")

    semantic = load_json(artifacts, "semantic-ir.json")
    modules = {module.get("id"): module for module in semantic.get("modules", [])}
    tour = modules.get(MODULE)
    if tour is None or set(modules) != {"KRS-FRAMEWORK", MODULE}:
        raise GateError(f"unexpected semantic modules: {sorted(modules)}")
    if len(tour.get("productions", [])) != 2 or len(tour.get("rules", [])) != 1:
        raise GateError("tour semantic IR must contain two productions and one rule")
    if not isinstance(tour.get("configuration"), dict):
        raise GateError("tour semantic IR has no configuration")

    symbols = load_json(artifacts, "symbols.json").get("entries", [])
    emitted_productions = {
        item.get("emitted_name")
        for item in symbols
        if item.get("symbol_kind") == "production"
    }
    labels = {
        item.get("emitted_name")
        for item in symbols
        if item.get("identity", {}).get("identity_kind") == "label"
    }
    if emitted_productions != {"foo", "bar"} or labels != {"foo-to-bar"}:
        raise GateError(
            f"unexpected emitted productions/labels: {emitted_productions}, {labels}"
        )

    theory = artifacts["definition.k"].decode("utf-8")
    productions = re.findall(
        r'^\s*syntax M2Obj ::= "([^"]+)" \[[^\n]+\]$', theory, re.MULTILINE
    )
    if sorted(productions) != ["bar", "foo"]:
        raise GateError(f"emitted M2Obj productions differ: {productions}")
    required_lines = (
        "syntax KItem ::= KResult",
        "syntax KResult ::= M2Obj",
        "imports KRS-FRAMEWORK",
    )
    if any(theory.count(line) != 1 for line in required_lines):
        raise GateError("emitted theory changed its framework import or sort chain")
    if len(re.findall(r"^\s*rule \[", theory, re.MULTILINE)) != 1:
        raise GateError("emitted theory must contain exactly one transition")
    if re.search(r"configuration\s+<k>\s+foo\s+</k>", theory) is None:
        raise GateError("emitted theory does not initialize the computation with foo")
    if re.search(
        r"rule \[foo-to-bar\]:\s+<k>\s+foo => bar \.\.\.\s+</k>", theory
    ) is None:
        raise GateError("emitted theory does not contain the foo-to-bar transition")

    reference = REFERENCE_SOURCE.read_text(encoding="utf-8")
    for source_name, source in (("tour-minimal", theory), ("reference theory", reference)):
        if source.count('"foo"') != 1 or source.count('"bar"') != 1:
            raise GateError(f"{source_name} does not define exactly one foo/bar terminal pair")
        for edge in ("syntax KItem ::= KResult", "syntax KResult ::= M2Obj"):
            if source.count(edge) != 1:
                raise GateError(f"{source_name} does not contain exactly one {edge!r} edge")
        if len(re.findall(r"configuration\s+<k>\s+foo\s+</k>", source)) != 1:
            raise GateError(f"{source_name} does not contain exactly one foo initializer")
    if len(re.findall(r"^\s*rule foo => bar\s*$", reference, re.MULTILINE)) != 1:
        raise GateError("reference theory does not contain exactly one bare foo-to-bar transition")

    sources = load_json(artifacts, "sources.json")
    expected_digest = sha256_file(SOURCE)
    attributed_kinds: set[str] = set()
    for entry in sources.get("entries", []):
        for frame in entry.get("origin", []):
            file = frame.get("range", {}).get("file", {})
            package = file.get("package", {})
            if package.get("k_namespace") != MODULE:
                continue
            if package.get("cargo_name") != PACKAGE:
                raise GateError("tour source map attributes a range to the wrong Cargo package")
            if file.get("package_relative_path") != "src/lib.rs":
                raise GateError("tour source map attributes a range outside the authored fixture")
            if file.get("content_sha256") != expected_digest:
                raise GateError("tour source map carries a stale authored-source digest")
            attributed_kinds.add(entry.get("node_kind"))
    required_attribution = {
        "syntax_sort",
        "production",
        "configuration",
        "initializer",
        "rule",
        "term",
    }
    if not required_attribution.issubset(attributed_kinds):
        missing = sorted(required_attribution - attributed_kinds)
        raise GateError(f"tour source map omits authored attribution for {missing}")

    checkout = os.fsencode(ROOT)
    for name, contents in artifacts.items():
        if checkout in contents:
            raise GateError(f"{name} leaks the absolute checkout path")
    return artifacts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--krs",
        type=Path,
        help="use an existing production KRS binary instead of building one",
    )
    arguments = parser.parse_args()

    verify_source_region()
    print("PASS source: stable Vocs definition region")

    cargo = executable("cargo")
    run(
        [
            cargo,
            f"+{msrv()}",
            "check",
            "--locked",
            "--offline",
            "--manifest-path",
            MANIFEST,
        ]
    )
    print(f"PASS authored: Rust {msrv()} locked/offline check")

    environment = cli_environment()
    binary = production_binary(arguments.krs, environment)

    before = SOURCE.read_bytes()
    format_environment = {
        **environment,
        "PATH": os.pathsep.join((os.fspath(rustfmt_dir()), os.environ.get("PATH", ""))),
    }
    run(
        [binary, "fmt", "--check", "--manifest-path", MANIFEST, SOURCE],
        environment=format_environment,
    )
    if SOURCE.read_bytes() != before:
        raise GateError("krs fmt --check unexpectedly changed the tour source")
    print("PASS format: krs fmt --check preserved source and region markers")

    checked = run(cli_command(binary, "check"), environment=environment)
    if checked.stdout != "KRS check passed: 9 descriptors, 2 semantic modules\n":
        raise GateError(f"unexpected krs check result: {compact(checked)}")
    print("PASS check: complete nine-descriptor theory")

    first_expansion = run(cli_command(binary, "expand"), environment=environment).stdout
    second_expansion = run(cli_command(binary, "expand"), environment=environment).stdout
    if first_expansion != second_expansion:
        raise GateError("repeated krs expand output differs byte-for-byte")
    verify_expansion(first_expansion)
    print("PASS expand: deterministic explicit foo-to-bar reference surface")

    with tempfile.TemporaryDirectory(prefix="krs-tour-minimal-") as temporary:
        workspace = Path(temporary)
        first = workspace / "first"
        second = workspace / "second"
        run(cli_command(binary, "emit-k", "--output", first), environment=environment)
        run(cli_command(binary, "emit-k", "--output", second), environment=environment)
        first_artifacts = verify_artifacts(first)
        second_artifacts = verify_artifacts(second)
        if first_artifacts != second_artifacts:
            changed = sorted(
                name
                for name in EMITTED_ARTIFACTS
                if first_artifacts[name] != second_artifacts[name]
            )
            raise GateError(f"repeated emission differs byte-for-byte: {changed}")
    print("PASS emit-k: deterministic M2 projection with authored source mapping")
    print("PASS tour-minimal")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (GateError, OSError) as error:
        print(f"FAIL tour-minimal: {error}", file=sys.stderr)
        raise SystemExit(1) from error
