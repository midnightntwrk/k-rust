#!/usr/bin/env python3
"""Map one induced K frontend Location through sources.json, without guessing."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


LOCATION = re.compile(r"Location\((\d+),(\d+),(\d+),(\d+)\)")


class FrontendProbeError(RuntimeError):
    pass


def ranged_origins(entry: dict[str, object]) -> list[dict[str, object]]:
    result = []
    for frame in entry.get("origin", []):
        if isinstance(frame, dict) and frame.get("frame_type") == "ranged" and frame.get("kind") == "authored":
            value = frame.get("range")
            if isinstance(value, dict):
                result.append(value)
    return result


def exact_mapping(
    definition: bytes, sidecar: dict[str, object], source: bytes, source_relative_path: str, token: str
) -> tuple[dict[str, object], dict[str, object]]:
    matches = []
    for entry in sidecar.get("entries", []):
        if not isinstance(entry, dict) or not isinstance(entry.get("generated"), dict):
            continue
        generated = entry["generated"]
        origins = ranged_origins(entry)
        if len(origins) != 1:
            continue
        origin = origins[0]
        file = origin.get("file", {})
        if not isinstance(file, dict) or file.get("package_relative_path") != source_relative_path:
            continue
        if file.get("content_sha256") != hashlib.sha256(source).hexdigest():
            continue
        start, end = int(origin["start_byte"]), int(origin["end_byte"])
        generated_start, generated_end = int(generated["start_byte"]), int(generated["end_byte"])
        if (
            0 <= start < end <= len(source)
            and 0 <= generated_start < generated_end <= len(definition)
            and generated.get("artifact") == "definition.k"
            and source[start:end].decode() == token
            and definition[generated_start:generated_end]
        ):
            matches.append((origin, generated))
    if len(matches) != 1:
        raise FrontendProbeError(f"expected one exact sidecar mapping for {token!r}, got {len(matches)}")
    return matches[0]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--definition", type=Path, required=True)
    parser.add_argument("--sources", type=Path, required=True)
    parser.add_argument("--authored", type=Path, required=True)
    parser.add_argument("--source-relative-path", required=True)
    parser.add_argument("--token", required=True)
    parser.add_argument("--kompile")
    parser.add_argument("--module")
    arguments = parser.parse_args()
    definition = arguments.definition.read_bytes()
    source = arguments.authored.read_bytes()
    sidecar = json.loads(arguments.sources.read_text(encoding="utf-8"))
    origin, generated = exact_mapping(
        definition, sidecar, source, arguments.source_relative_path, arguments.token
    )
    start, end = int(generated["start_byte"]), int(generated["end_byte"])
    broken = definition[:start] + b"+" + definition[end:]
    line = broken[:start].count(b"\n") + 1
    column = start - broken.rfind(b"\n", 0, start)
    if not arguments.kompile:
        print(json.dumps({"generated_location": [line, column], "authored_range": origin}, sort_keys=True))
        return 0
    if not arguments.module:
        raise FrontendProbeError("--module is required with --kompile")
    with tempfile.TemporaryDirectory(prefix="krs-m4-frontend-diagnostic-") as temporary:
        temporary = Path(temporary)
        broken_path = temporary / "definition.k"
        broken_path.write_bytes(broken)
        process = subprocess.run(
            [arguments.kompile, str(broken_path), "--main-module", arguments.module,
             "--syntax-module", arguments.module, "--backend", "llvm",
             "--output-definition", str(temporary / "out")],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180, check=False
        )
    locations = [tuple(map(int, match.groups())) for match in LOCATION.finditer(process.stderr)]
    if process.returncode == 0 or not any(location[:2] == (line, column) for location in locations):
        raise FrontendProbeError("K frontend failure did not select the exact induced generated range")
    print(json.dumps({"generated_location": [line, column], "authored_range": origin}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
