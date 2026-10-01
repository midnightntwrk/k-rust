#!/usr/bin/env python3
"""Bounded acceptance gate for the language tour's smallest KRS theory."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry, krs_gate  # noqa: E402
from support.hashing import sha256_file  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.process import compact, run  # noqa: E402
from support.tools import checkout_scratch, rustfmt_dir, z3_environment  # noqa: E402


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

    return build(environment)


def cli_command(binary: Path, operation: str, *extra: Path | str) -> list[Path | str]:
    return Invocation(binary, MANIFEST, PACKAGE, DEFINITION).argv(operation, *extra)


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
        "#[k::sort(alias = ObjectTerm, parents = [k::KResult])]",
        "#[k::constructors(sort = ObjectTerm, reference)]",
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


def verify_reference_theory() -> None:
    reference = REFERENCE_SOURCE.read_text(encoding="utf-8")
    if reference.count('"foo"') != 1 or reference.count('"bar"') != 1:
        raise GateError("reference theory does not define exactly one foo/bar terminal pair")
    for edge in ("syntax KItem ::= KResult", "syntax KResult ::= ObjectTerm"):
        if reference.count(edge) != 1:
            raise GateError(f"reference theory does not contain exactly one {edge!r} edge")
    if len(re.findall(r"configuration\s+<k>\s+foo\s+</k>", reference)) != 1:
        raise GateError("reference theory does not contain exactly one foo initializer")
    if len(re.findall(r"^\s*rule foo => bar\s*$", reference, re.MULTILINE)) != 1:
        raise GateError("reference theory does not contain exactly one bare foo-to-bar transition")


def verify_artifacts(directory: Path, gate: Path, environment: dict[str, str]) -> dict[str, bytes]:
    expected = json.loads((HERE / "definition-checks.json").read_bytes())
    with krs_gate.Session(gate, environment=environment) as session:
        files = session.ir_query(directory, {"kind": "files"})
        if files["actual"] != files["expected"] or not files["owned"] or files["has_claims"]:
            raise GateError(f"unexpected emitted artifact directory: {files}")
        descriptors = session.ir_query(directory, {"kind": "descriptors"})
        if descriptors["counts"]["item_kind"] != expected["descriptor_item_counts"]:
            raise GateError(f"descriptor theory differs: {descriptors['counts']}")
        modules = session.ir_query(directory, {"kind": "modules"})
        if modules["main_module"] != MODULE or sorted(row["name"] for row in modules["rows"]) != expected["modules"]:
            raise GateError(f"unexpected definition modules: {modules}")
        tour = [row for row in modules["rows"] if row["name"] == MODULE][0]
        if tour["imports"] != expected["imports"]:
            raise GateError(f"unexpected framework imports: {tour}")
        semantic = session.ir_query(directory, {"kind": "semantic_modules"})["rows"]
        if sorted(row["name"] for row in semantic) != expected["modules"]:
            raise GateError(f"unexpected semantic modules: {semantic}")
        tour_semantic = [row for row in semantic if row["name"] == MODULE][0]
        if tour_semantic["production_count"] != 2 or tour_semantic["rule_count"] != 1 or not tour_semantic["has_configuration"]:
            raise GateError(f"unexpected tour semantic theory: {tour_semantic}")
        configurations = session.ir_query(directory, {"kind": "sentences", "module": MODULE, "sentence_kind": "configuration"})["rows"]
        if len(configurations) != 1 or configurations[0]["initializers"] != expected["initializer"]:
            raise GateError(f"unexpected foo initializer: {configurations}")
        productions = session.ir_query(directory, {"kind": "productions", "sort": "ObjectTerm"})["rows"]
        facts = [{"symbol": row["symbol"], "terminals": row["terminals"]} for row in productions]
        if sorted(facts, key=lambda row: row["symbol"]) != expected["productions"]:
            raise GateError(f"unexpected ObjectTerm productions: {facts}")
        rules = session.ir_query(directory, {"kind": "sentences", "module": MODULE, "sentence_kind": "rule"})["rows"]
        if [row["label"] for row in rules] != expected["labels"] or rules[0]["body"] != expected["rule_body"]:
            raise GateError(f"unexpected transition labels: {rules}")
        vocabulary = session.ir_query(directory, {"kind": "vocabulary"})
        for edge in expected["subsorts"]:
            if vocabulary["subsorts"].count(edge) != 1:
                raise GateError(f"unexpected subsort edge: {edge}")
        production_symbols = session.ir_query(directory, {"kind": "symbols", "symbol_kind": "production"})["rows"]
        label_symbols = session.ir_query(directory, {"kind": "symbols", "identity_kind": "label"})["rows"]
        production_names = {row["emitted_name"] for row in production_symbols}
        labels = {row["emitted_name"] for row in label_symbols}
        if production_names != {row["symbol"] for row in expected["productions"]} or labels != set(expected["labels"]):
            raise GateError(f"unexpected symbol-map productions/labels: {production_names}, {labels}")
        sources = session.ir_query(directory, {"kind": "sources"})["rows"]
        expected_digest = sha256_file(SOURCE)
        attributed_kinds = set()
        for row in sources:
            ranged = [frame for frame in row["ranged"] if frame["k_namespace"] == MODULE]
            for frame in ranged:
                if frame["cargo_name"] != PACKAGE or frame["package_relative_path"] != "src/lib.rs" or frame["content_sha256"] != expected_digest:
                    raise GateError(f"unexpected tour source attribution: {frame}")
                attributed_kinds.add(row["node_kind"])
        if not set(expected["attributed_kinds"]).issubset(attributed_kinds):
            raise GateError(f"tour source map omits authored attribution: {attributed_kinds}")
    artifacts = {name: (directory / name).read_bytes() for name in files["expected"]}
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
    verify_reference_theory()
    print("PASS source: stable Vocs definition region")

    target = checkout_scratch() / "tour-minimal-root-target"
    environment = {**cli_environment(), "CARGO_TARGET_DIR": os.fspath(target)}
    binary = production_binary(arguments.krs, environment)
    gate = krs_gate.configured_or_build(target)

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
    check_packages("tour-minimal", env=environment, target_dir=target)

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
        first_artifacts = verify_artifacts(first, gate, environment)
        second_artifacts = verify_artifacts(second, gate, environment)
        if first_artifacts != second_artifacts:
            changed = sorted(
                name
                for name in first_artifacts
                if first_artifacts[name] != second_artifacts[name]
            )
            raise GateError(f"repeated emission differs byte-for-byte: {changed}")
    print("PASS emit-k: deterministic foo-to-bar projection with authored source mapping")
    print("PASS tour-minimal")
    return 0


if __name__ == "__main__":
    entry("tour-minimal", main, errors=(OSError,))
