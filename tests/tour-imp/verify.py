#!/usr/bin/env python3
"""Acceptance gate for the complete, documentation-owned IMP capstone."""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys
import tempfile

import sync

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry  # noqa: E402
from support.hashing import sha256_file  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import executable, rustfmt_dir, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
SOURCE = HERE / "src" / "lib.rs"
PACKAGE = "krs-tour-imp"
DEFINITION = "main"
GENERATED = HERE / "generated"


def cli_environment() -> dict[str, str]:
    return {
        **z3_environment(),
        "CARGO_TERM_COLOR": "never",
        "PATH": os.pathsep.join((os.fspath(rustfmt_dir()), os.environ.get("PATH", ""))),
    }


def cli(binary: Path, operation: str, *extra: os.PathLike[str] | str) -> list[os.PathLike[str] | str]:
    return Invocation(binary, MANIFEST, PACKAGE, DEFINITION).argv(operation, *extra)


def artifact_bytes(directory: Path) -> dict[str, bytes]:
    return {
        path.name: path.read_bytes()
        for path in sorted(directory.iterdir())
        if path.is_file()
    }


def walkthrough_artifacts(expansion: str, emitted: dict[str, bytes]) -> dict[Path, str]:
    source = SOURCE.read_text(encoding="utf-8")
    readable_line = next(
        line for line in source.splitlines() if "eval_add" in line
    )
    readable = f"k::rules! {{\n    in Machine.k;\n\n{readable_line}\n}}\n"

    expansion_start = expansion.index('#[k::rule(label = "eval-add")]')
    expansion_end = expansion.index("\n#[k::rule", expansion_start + 1)
    expanded = expansion[expansion_start:expansion_end].rstrip() + "\n"

    definition = emitted["definition.k"].decode("utf-8")
    k_start = definition.index("  rule [eval-add]:")
    k_end = definition.index("\n  rule [", k_start + 1)
    emitted_rule = definition[k_start:k_end].strip() + "\n"

    bundle = json.loads(emitted["descriptor-bundle.json"])
    descriptor = next(
        item
        for item in bundle["descriptors"]
        if item.get("id", {}).get("item_name") == "eval_add"
        and item.get("id", {}).get("item_kind") == "rule"
    )
    rule = descriptor["descriptor"]
    subject = rule["subject"]
    result = rule["result"]["head_result"]
    projection = {
        "id": descriptor["id"]["item_name"],
        "kind": descriptor["descriptor_kind"],
        "sentence_kind": rule["sentence_kind"],
        "label": rule["label"]["name"],
        "configuration": rule["configuration"]["item_name"],
        "cell": rule["computation_cell"]["cell"]["field"],
        "bindings": [binding["name"] for binding in rule["bindings"]],
        "subject": {
            "application": subject["reference"]["application"]["application"]["item_name"],
            "arguments": [argument["field"] for argument in subject["arguments"]],
        },
        "result": {
            "application": f'builtin:{result["reference"]["application"]["application"]}',
            "arguments": [
                argument["value"]["name"] for argument in result["arguments"]
            ],
        },
    }
    descriptor_json = json.dumps(projection, ensure_ascii=False, indent=2) + "\n"
    return {
        GENERATED / "eval-add-readable.txt": readable,
        GENERATED / "eval-add-expanded.txt": expanded,
        GENERATED / "eval-add-descriptor.json": descriptor_json,
        GENERATED / "eval-add.k": emitted_rule,
    }


def verify_walkthrough(expected: dict[Path, str]) -> None:
    write = "--write-generated" in sys.argv
    stale: list[Path] = []
    for path, content in expected.items():
        if write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
            print(f"updated {path.relative_to(ROOT)}")
        elif not path.is_file() or path.read_text(encoding="utf-8") != content:
            stale.append(path)
    if stale:
        names = ", ".join(str(path.relative_to(ROOT)) for path in stale)
        raise GateError(
            f"generated lowering walkthrough is stale: {names}; "
            "run tests/tour-imp/verify.py --write-generated"
        )


def main() -> None:
    sync.main()
    authority = sync.AUTHORITY.read_bytes()
    if SOURCE.read_bytes() != authority:
        raise GateError("tour-imp capstone is not byte-identical to the IMP operational authority")
    print("PASS source: capstone and chapter slices match IMP exactly")

    cargo = executable("cargo")
    run([cargo, "check", "--locked", "--offline", "--manifest-path", MANIFEST])
    print("PASS authored: locked/offline Cargo check")

    env = cli_environment()
    binary = build(env)

    # The chapter slices lie outside every target's source directory, so they are named explicitly.
    run([binary, "fmt", "--check", "--manifest-path", MANIFEST, SOURCE, sync.CHAPTERS], environment=env)
    run(cli(binary, "check"), environment=env)
    first_expansion = run(cli(binary, "expand"), environment=env).stdout
    second_expansion = run(cli(binary, "expand"), environment=env).stdout
    if first_expansion != second_expansion:
        raise GateError("expanded IMP reference surface is nondeterministic")
    print("PASS KRS: format, check, and deterministic expansion")

    with tempfile.TemporaryDirectory(prefix="krs-tour-imp-a-") as first_name, tempfile.TemporaryDirectory(prefix="krs-tour-imp-b-") as second_name:
        first = Path(first_name)
        second = Path(second_name)
        run(cli(binary, "emit-k", "--output", first), environment=env)
        run(cli(binary, "emit-k", "--output", second), environment=env)
        first_artifacts = artifact_bytes(first)
        if first_artifacts != artifact_bytes(second):
            raise GateError("emitted IMP artifacts are nondeterministic")
        bundle = json.loads(first_artifacts["descriptor-bundle.json"])
        descriptors = bundle.get("descriptors", [])
        if len(descriptors) != 83:
            raise GateError(f"complete operational IMP must collect 83 descriptors, got {len(descriptors)}")
        sources = json.loads(first_artifacts["sources.json"])
        digest = sha256_file(SOURCE)
        authored_frames = [
            frame["range"]["file"]
            for entry in sources.get("entries", [])
            for frame in entry.get("origin", [])
            if frame.get("range", {}).get("file", {}).get("package", {}).get("cargo_name") == PACKAGE
        ]
        if not authored_frames:
            raise GateError("emitted source map has no tour-imp attribution")
        if any(frame.get("package_relative_path") != "src/lib.rs" or frame.get("content_sha256") != digest for frame in authored_frames):
            raise GateError("emitted source map does not identify the exact capstone bytes")
        verify_walkthrough(walkthrough_artifacts(first_expansion, first_artifacts))
    print("PASS emission: deterministic complete IMP artifacts and authored source maps")
    print("PASS walkthrough: readable, explicit, descriptor, and K views are current")


if __name__ == "__main__":
    entry("tour-imp", main, errors=(OSError, ValueError, KeyError))
