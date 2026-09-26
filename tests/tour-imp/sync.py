#!/usr/bin/env python3
"""Synchronize the documentation-owned IMP capstone and chapter slices."""

from __future__ import annotations

import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
AUTHORITY = ROOT / "tests" / "imp" / "rust-definition" / "src" / "imp.rs"
CAPSTONE = HERE / "src" / "lib.rs"
CHAPTERS = HERE / "chapters"

SLICES = (
    ("01-sorts.rs", None, "#[k::constructors(sort = Expr, result = KResult)]"),
    (
        "02-concrete-grammar.rs",
        "#[k::constructors(sort = Expr, result = KResult)]",
        "#[k::constructors(sort = Stmt, result = KResult)]",
    ),
    (
        "03-evaluation.rs",
        "k::rules! {\n    for Expr;",
        "k::rules! {\n    for Stmt;",
    ),
    (
        "04-configuration-and-state.rs",
        "#[k::constructors(sort = Stmt, result = KResult)]",
        "k::rules! {\n    for Expr;",
    ),
    (
        "05-control-flow.rs",
        "k::rules! {\n    for Stmt;",
        "k::rules! {\n    for Machine;",
    ),
    ("06-machine-rules.rs", "k::rules! {\n    for Machine;", None),
)


def extract(source: str, start_anchor: str | None, end_anchor: str | None) -> str:
    start = source.index(start_anchor) if start_anchor else 0
    end = source.index(end_anchor, start) if end_anchor else len(source)
    return source[start:end].strip() + "\n"


def expected_files() -> dict[Path, str]:
    source = AUTHORITY.read_text(encoding="utf-8")
    files = {CAPSTONE: source}
    for name, start, end in SLICES:
        files[CHAPTERS / name] = extract(source, start, end)
    return files


def main() -> None:
    write = "--write" in sys.argv
    stale: list[Path] = []
    for path, expected in expected_files().items():
        if write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected, encoding="utf-8")
            print(f"updated {path.relative_to(ROOT)}")
        elif not path.is_file() or path.read_text(encoding="utf-8") != expected:
            stale.append(path)
    if stale:
        relative = ", ".join(str(path.relative_to(ROOT)) for path in stale)
        raise SystemExit(f"tour-imp generated sources are stale: {relative}; run sync.py --write")
    if not write:
        print(f"tour-imp sources current: capstone plus {len(SLICES)} chapter slices")


if __name__ == "__main__":
    main()
