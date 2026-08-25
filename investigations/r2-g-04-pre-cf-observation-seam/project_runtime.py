#!/usr/bin/env python3
"""Project terminal P3 runtime output to branch-local program state."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


def cell(text: str, name: str) -> str | None:
    match = re.search(rf"<{name}>\s*(.*?)\s*</{name}>", text, re.DOTALL)
    if match is None:
        return None
    value = re.sub(r"\s+", " ", match.group(1)).strip()
    return re.sub(r"\s*~>\s*\.K$", "", value).strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    text = args.input.read_text(encoding="utf-8")
    projection = {"k": cell(text, "k"), "state": cell(text, "state")}
    observation = cell(text, "observation")
    if observation is not None:
        projection["observation"] = observation
    args.output.write_text(
        json.dumps(projection, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
