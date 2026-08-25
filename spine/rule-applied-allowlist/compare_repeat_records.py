#!/usr/bin/env python3
"""Compare stable fields across two fresh task-local driver compilations."""

import json
import sys
from pathlib import Path

left, right = (json.loads(Path(value).read_text(encoding="utf-8")) for value in sys.argv[1:])
ignored = {"mode", "error"}
for mapping in (left, right):
    for key in ignored:
        mapping.pop(key, None)
if left != right:
    raise SystemExit("fresh compilation driver records differ beyond invocation mode")
