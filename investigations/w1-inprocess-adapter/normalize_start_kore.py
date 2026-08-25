#!/usr/bin/env python3
"""Extract P3's start-program Kore axiom and normalize only sentence numbering."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


HEX_ID = r"[0-9a-f]{64}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    lines = args.input.read_text(encoding="utf-8").splitlines()
    starts = [
        index
        for index, line in enumerate(lines)
        if line.startswith("// rule ") and "label(start-program)" in line
    ]
    if len(starts) != 1:
        raise ValueError(f"expected one start-program Kore rule, found {len(starts)}")
    start = starts[0]
    end = next(
        (index for index in range(start + 1, len(lines)) if lines[index].startswith("// rule ")),
        len(lines),
    )
    projection = "\n".join(lines[start:end]).rstrip() + "\n"
    projection = re.sub(rf"UNIQUE_ID\({HEX_ID}\)", "UNIQUE_ID(<normalized>)", projection)
    projection = re.sub(
        rf"UNIQUE'Unds'ID\{{\}}\(\"{HEX_ID}\"\)",
        "UNIQUE'Unds'ID{}(\"<normalized>\")",
        projection,
    )
    args.output.write_text(projection, encoding="utf-8")


if __name__ == "__main__":
    main()
