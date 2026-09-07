#!/usr/bin/env python3
"""Parse the program with K and place it in the declared initial configuration."""

import os
import subprocess


program = subprocess.check_output(
    [
        os.environ["K_KAST"],
        "start.pgm",
        "--definition", "ref",
        "--module", "BR-SYNTAX",
        "--sort", "Pgm",
        "--output", "kore",
    ],
    text=True,
).strip()

# This fixture declares one k cell; the generated counter starts at zero.
# Keep the configuration explicit: krun --depth 0 leaves its initializer unevaluated.
print(
    "Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}("
    "inj{SortPgm{}, SortKItem{}}(" + program + "), dotk{}())), "
    "Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"0\")))"
)
