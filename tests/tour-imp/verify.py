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
from support import ROOT, GateError, entry, krs_gate  # noqa: E402
from support.hashing import sha256_file  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import checkout_scratch, rustfmt_dir, z3_environment  # noqa: E402


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


def walkthrough_artifacts(expansion: str, artifacts: Path, gate: Path, environment: dict[str, str]) -> dict[Path, str]:
    source = SOURCE.read_text(encoding="utf-8")
    readable_line = next(line for line in source.splitlines() if "eval_add" in line)
    readable = f"k::rules! {{\n    in Machine.k;\n\n{readable_line}\n}}\n"
    expansion_start = expansion.index('#[k::rule(label = "eval-add")]')
    expansion_end = expansion.index("\n#[k::rule", expansion_start + 1)
    expanded = expansion[expansion_start:expansion_end].rstrip() + "\n"
    descriptor, sentences = krs_gate.ir_queries(gate, artifacts, [
        {"kind": "head_rule_walkthrough", "item_name": "eval_add"},
        {"kind": "sentences", "label": "eval-add", "sentence_kind": "rule"},
    ], environment=environment)
    rows = sentences["rows"]
    if len(rows) != 1 or rows[0]["generated"]["artifact"] != "definition.k":
        raise GateError("walkthrough needs one generated eval-add rule")
    generated = rows[0]["generated"]
    emitted_rule = (artifacts / "definition.k").read_bytes()[generated["start_byte"]:generated["end_byte"]].decode().strip() + "\n"
    # The walkthrough's presentation order is a checked documentation contract.
    projection = {key: descriptor[key] for key in (
        "id", "kind", "sentence_kind", "label", "configuration", "cell", "bindings",
    )}
    for key in ("subject", "result"):
        projection[key] = {field: descriptor[key][field] for field in ("application", "arguments")}
    return {
        GENERATED / "eval-add-readable.txt": readable,
        GENERATED / "eval-add-expanded.txt": expanded,
        GENERATED / "eval-add-descriptor.json": json.dumps(projection, ensure_ascii=False, indent=2) + "\n",
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

    target = checkout_scratch() / "tour-imp-root-target"
    env = {**cli_environment(), "CARGO_TARGET_DIR": os.fspath(target)}
    binary = build(env)
    gate = krs_gate.build(target, environment=env)
    check_packages("tour-imp", env=env, target_dir=target)

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
        digest = sha256_file(SOURCE)
        details, attribution = krs_gate.ir_queries(gate, first, [
            {"kind": "descriptors"}, {"kind": "sources"},
        ], environment=env)
        if len(details["rows"]) != 83:
            raise GateError("complete operational IMP must collect 83 descriptors")
        frames = [frame for row in attribution["rows"] for frame in row["ranged"] if frame["cargo_name"] == PACKAGE]
        if not frames or any(frame["package_relative_path"] != "src/lib.rs" or frame["content_sha256"] != digest for frame in frames):
            raise GateError("source map must identify the exact capstone bytes")
        expected = walkthrough_artifacts(first_expansion, first, gate, env)
        verify_walkthrough(expected)
    print("PASS emission: deterministic complete IMP artifacts and authored source maps")
    print("PASS walkthrough: readable, explicit, descriptor, and K views are current")


if __name__ == "__main__":
    entry("tour-imp", main, errors=(OSError, ValueError, KeyError))
