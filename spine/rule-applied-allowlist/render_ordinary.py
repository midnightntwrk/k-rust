#!/usr/bin/env python3
"""Render the independent ordinary-source oracle from validated raw targets."""

import json
import sys
from pathlib import Path

template, record_path, output = (Path(value) for value in sys.argv[1:])
record = json.loads(record_path.read_text(encoding="utf-8"))
fields = {
    "id": record["ruleTargetLineage"].split("|"),
    "label": record["ruleTargetLabel"].split("|"),
    "module": record["ruleTargetModule"].split("|"),
    "source": record["ruleTargetSource"].split("|"),
    "location": record["ruleTargetLocation"].split("|"),
}
if any(len(values) != 2 for values in fields.values()):
    raise SystemExit("raw driver record does not contain an exact pair")
members = [{name: values[index] for name, values in fields.items()} for index in range(2)]
by_label = {member["label"]: member for member in members}
if set(by_label) != {"bump-state", "drop-state"}:
    raise SystemExit("raw driver targets are not bump-state/drop-state")
text = template.read_text(encoding="utf-8")
for prefix, label in (("BUMP", "bump-state"), ("DROP", "drop-state")):
    for name, value in by_label[label].items():
        text = text.replace(f"@@{prefix}_{name.upper()}@@", json.dumps(value))
if "@@" in text:
    raise SystemExit("ordinary-source template retained a placeholder")
output.write_text(text, encoding="utf-8")
