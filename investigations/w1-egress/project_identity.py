#!/usr/bin/env python3
"""Project stable sentence identity/provenance from official compiled KAST."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


SOURCE = "org.kframework.attributes.Source"
LOCATION = "org.kframework.attributes.Location"


def digest(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("source_suffix")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    envelope = json.loads(args.input.read_text(encoding="utf-8"))
    modules = envelope["term"]["modules"]
    projected: list[dict[str, Any]] = []
    for module in modules:
        for sentence in module["localSentences"]:
            attrs = sentence.get("att", {}).get("att", {})
            source = attrs.get(SOURCE)
            if not isinstance(source, str) or not source.endswith(args.source_suffix):
                continue
            if sentence.get("node") not in ("KRule", "KClaim", "KContext", "KContextAlias"):
                continue
            projected.append(
                {
                    "module": module["name"],
                    "node": sentence["node"],
                    "label": attrs.get("label"),
                    "uniqueId": attrs.get("UNIQUE_ID"),
                    "source": source,
                    "location": attrs.get(LOCATION),
                    "bodySha256": digest(sentence.get("body")),
                    "requiresSha256": digest(sentence.get("requires")),
                    "ensuresSha256": digest(sentence.get("ensures")),
                }
            )

    projected.sort(
        key=lambda item: (
            item["module"],
            item["node"],
            item["label"] or "",
            item["uniqueId"] or "",
            json.dumps(item["location"]),
            item["bodySha256"],
        )
    )
    result = {
        "schemaVersion": 1,
        "input": str(args.input),
        "sourceSuffix": args.source_suffix,
        "sentenceCount": len(projected),
        "sentences": projected,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
