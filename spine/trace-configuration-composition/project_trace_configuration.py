#!/usr/bin/env python3
"""Project the generated trace-cell production and classify shell provenance."""

import argparse
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("input", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--source", required=True)
parser.add_argument("--expected-location", required=True)
args = parser.parse_args()

lines = [line for line in args.input.read_text(encoding="utf-8").splitlines()
         if line.lstrip().startswith("symbol Lbl'-LT-'trace'-GT-'")]
if len(lines) != 1:
    raise ValueError(f"expected one generated trace-cell symbol, found {len(lines)}")
line = lines[0]
sources = re.findall(r"Source\(([^)]*)\)", line)
locations = re.findall(r"Location\([^)]*\)", line)
if sources != [args.source]:
    raise ValueError(f"unexpected trace-shell source: {sources}")
if locations != [args.expected_location]:
    raise ValueError(f"unexpected trace-shell location: {locations}")
domains = [f"Source({args.source})", args.expected_location]
ranges = ["Source(<classified-trace-shell>)", "Location(<classified-trace-shell>)"]
if len(set(domains)) != 2 or len(set(ranges)) != 2:
    raise ValueError("trace-shell provenance projection collided")
if any(domain in target for domain in domains for target in ranges):
    raise ValueError("trace-shell projection range contained a raw domain")
if any(line.count(domain) != 1 for domain in domains):
    raise ValueError("trace-shell provenance domain did not occur exactly once")
pattern = re.compile("|".join(map(re.escape, domains)))
mapping = dict(zip(domains, ranges))
semantic = pattern.sub(lambda match: mapping[match.group(0)], line)
if any(domain in semantic for domain in domains):
    raise ValueError("trace-shell semantic projection retained raw provenance")
result = {
    "source": args.source,
    "location": args.expected_location,
    "semanticSha256": hashlib.sha256(semantic.encode()).hexdigest(),
    "sort": "TraceCell",
    "bodySort": "List",
}
args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8")
