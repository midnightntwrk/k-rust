#!/usr/bin/env python3
"""Render raw and portable source oracles from explicit marker/field maps."""

import argparse
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("template", type=Path)
parser.add_argument("record", type=Path)
parser.add_argument("raw_output", type=Path)
parser.add_argument("portable_output", type=Path)
args = parser.parse_args()

template = args.template.read_text(encoding="utf-8")
record = json.loads(args.record.read_text(encoding="utf-8"))
fields = (
    ("@ID@", "ruleTargetLineage", "portableRuleTargetLineage"),
    ("@LABEL@", "ruleTargetLabel", "portableRuleTargetLabel"),
    ("@MODULE@", "ruleTargetModule", "portableRuleTargetModule"),
    ("@SOURCE@", "ruleTargetSource", "portableRuleTargetSource"),
    ("@LOCATION@", "ruleTargetLocation", "portableRuleTargetLocation"),
)
markers = [marker for marker, _, _ in fields]
if len(set(markers)) != len(markers):
    raise SystemExit("oracle marker domains were not unique")
for marker in markers:
    if template.count(marker) != 1:
        raise SystemExit(f"oracle marker {marker} did not occur exactly once")

raw_map = {marker: json.dumps(record[raw]) for marker, raw, _ in fields}
portable_map = {marker: json.dumps(record[portable]) for marker, _, portable in fields}
raw_domains = [record["ruleTargetLineage"], record["ruleTargetSource"]]
portable_ranges = [record["portableRuleTargetLineage"], record["portableRuleTargetSource"]]
if len(set(raw_domains)) != len(raw_domains):
    raise SystemExit("raw identity domains were not unique")
if len(set(portable_ranges)) != len(portable_ranges):
    raise SystemExit("portable identity ranges were not unique")
if any(domain == target for domain in raw_domains for target in portable_ranges):
    raise SystemExit("raw and portable identity sets collided")
if any(domain in target for domain in raw_domains for target in portable_ranges):
    raise SystemExit("portable identity range contained a raw domain")

pattern = re.compile("|".join(map(re.escape, markers)))

def render(values: dict[str, str]) -> str:
    result = pattern.sub(lambda match: values[match.group(0)], template)
    if pattern.search(result) or re.search(r"@[A-Z]+@", result):
        raise SystemExit("rendered oracle retained a marker")
    return result

raw = render(raw_map)
portable = render(portable_map)
for domain in raw_domains:
    if domain not in raw:
        raise SystemExit("raw oracle omitted an exact raw identity")
    if domain in portable:
        raise SystemExit("portable oracle retained a raw identity")
for target in portable_ranges:
    if target not in portable:
        raise SystemExit("portable oracle omitted a portable identity")

args.raw_output.write_text(raw, encoding="utf-8")
args.portable_output.write_text(portable, encoding="utf-8")
