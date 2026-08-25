#!/usr/bin/env python3
"""Normalize fixture identity and only the classified trace-shell provenance."""

import argparse
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("input", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--source", required=True)
parser.add_argument("--trace-location", required=True)
args = parser.parse_args()

text = args.input.read_text(encoding="utf-8")
if args.source not in text and args.input.name != "macros.kore":
    raise ValueError("fixture source was absent from semantic artifact")
source_range = "repo://trace-configuration-semantic-oracle.k"
location_range = "Location(<classified-trace-shell>)"
domains = [args.source, args.trace_location]
ranges = [source_range, location_range]
if len(set(domains)) != 2 or len(set(ranges)) != 2:
    raise ValueError("semantic provenance projection collided")
if any(domain in target for domain in domains for target in ranges):
    raise ValueError("semantic projection range contained a raw domain")
source_hits = text.count(args.source)
if source_hits == 0 and args.input.name != "macros.kore":
    raise ValueError("semantic source domain had no occurrences")
text = text.replace(args.source, source_range)
if args.source in text:
    raise ValueError("semantic artifact retained fixture source")
lines: list[str] = []
hits = 0
for line in text.splitlines():
    if "Lbl'-LT-'trace'-GT-'" in line and args.trace_location in line:
        if line.count(args.trace_location) != 1:
            raise ValueError("trace-shell location domain did not occur exactly once")
        line = line.replace(args.trace_location, location_range)
        if args.trace_location in line:
            raise ValueError("trace-shell line retained raw location")
        hits += 1
    lines.append(line)
if args.input.name == "syntaxDefinition.kore" and hits != 1:
    raise ValueError(f"expected one classified trace-shell location, found {hits}")
if args.input.name == "macros.kore" and hits not in (0, 1):
    raise ValueError(f"unexpected macro trace-shell locations: {hits}")
args.output.write_text("\n".join(lines) + "\n", encoding="utf-8")
