#!/usr/bin/env python3
"""Canonicalize backend-generated _GenN binders within individual Kore blocks.

The pinned backend iterates a set when choosing fresh names for generated sort
predicate axioms. Separate JVMs can therefore select _Gen0 versus _Gen1 while
emitting alpha-equivalent axioms. This projection renames only those binders,
scoped by blank-line-delimited top-level Kore blocks.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


GEN = re.compile(r"(?P<prefix>Var'Unds'Gen|_Gen)(?P<number>[0-9]+)")


def normalize_block(lines: list[str]) -> list[str]:
    names: dict[str, int] = {}

    def replace(match: re.Match[str]) -> str:
        number = match.group("number")
        if number not in names:
            names[number] = len(names)
        return f"{match.group('prefix')}{names[number]}"

    return [GEN.sub(replace, line) for line in lines]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    result: list[str] = []
    block: list[str] = []
    for line in args.input.read_text(encoding="utf-8").splitlines():
        if line:
            block.append(line)
        else:
            result.extend(normalize_block(block))
            result.append("")
            block = []
    result.extend(normalize_block(block))
    args.output.write_text("\n".join(result) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
