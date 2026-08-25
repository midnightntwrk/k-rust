#!/usr/bin/env python3
"""Produce a focused structural projection of officially generated observation Kore."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


MARKERS = {
    "observationCellSort": r"SortObservationCell",
    "observationCellLabel": r"observation'-GT-'",
    "observationInitializer": r"initObservationCell",
    "observationUnit": r"Lbl'-LT-'observation'-GT-'",
}


def normalize_source(value: str | None) -> str | None:
    if value is None:
        return None
    for anchor in ("/p3/fixtures/", "/investigations/w1-egress/fixtures/"):
        if anchor in value:
            return value[value.index(anchor) :]
    return value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    text = args.input.read_text(encoding="utf-8")
    observation_symbol = next(
        (line for line in text.splitlines() if "symbol Lbl'-LT-'observation'-GT-'" in line),
        "",
    )
    location = re.search(r"Location\(([^)]*)\)", observation_symbol)
    source = re.search(r"Source\(([^)]*)\)", observation_symbol)
    projection = {
        "markers": {name: len(re.findall(pattern, text)) for name, pattern in MARKERS.items()},
        "provenance": {
            "location": location.group(1) if location else None,
            "source": normalize_source(source.group(1) if source else None),
        },
    }
    args.output.write_text(json.dumps(projection, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
