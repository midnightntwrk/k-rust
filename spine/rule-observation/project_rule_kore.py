#!/usr/bin/env python3
"""Project one labeled Kore rule and normalize only generated rule identity."""

import argparse
import re
from pathlib import Path

HEX = r"[0-9a-f]{64}"
parser = argparse.ArgumentParser()
parser.add_argument("input", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--label", required=True)
args = parser.parse_args()
lines = args.input.read_text(encoding="utf-8").splitlines()
starts = [i for i, line in enumerate(lines) if line.startswith("// rule ") and f"label({args.label})" in line]
if len(starts) != 1:
    raise ValueError(f"expected one {args.label} Kore rule, found {len(starts)}")
start = starts[0]
end = next((i for i in range(start + 1, len(lines)) if lines[i].startswith("// rule ")), len(lines))
value = "\n".join(lines[start:end]).rstrip() + "\n"
value = re.sub(rf"UNIQUE_ID\({HEX}\)", "UNIQUE_ID(<normalized>)", value)
value = re.sub(rf"UNIQUE'Unds'ID\{{\}}\(\"{HEX}\"\)", "UNIQUE'Unds'ID{}(\"<normalized>\")", value)
args.output.write_text(value, encoding="utf-8")
