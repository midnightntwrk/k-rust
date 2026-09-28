"""Extract JSON object envelopes from Cargo and KRS diagnostic streams."""

from __future__ import annotations

import json


def envelopes(stderr: str | bytes) -> list[dict]:
    """Return each line that parses as a JSON object, in stream order."""

    found: list[dict] = []
    for line in stderr.splitlines():
        try:
            value = json.loads(line)
        except (json.JSONDecodeError, UnicodeDecodeError):
            continue
        if isinstance(value, dict):
            found.append(value)
    return found
