#!/usr/bin/env python3
"""Secure marker transitions for the R3-G-05 raw wrapper."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from secure_io import durable_unlink, publish_raw_failure, replace_progress_json


def previous_stage(output: Path, fallback: str) -> str:
    for name, schema in (("raw-failure.json", "R3-G-05-raw-failure-v1"),
                         ("raw-stage.json", "R3-G-05-raw-stage-v1")):
        path = output / name
        if not path.is_file() or path.is_symlink():
            continue
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if value.get("schema") == schema and isinstance(value.get("stage"), str):
            return value["stage"]
    return fallback


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("stage", "failure", "unlink"))
    parser.add_argument("output", type=Path)
    parser.add_argument("value", nargs="?")
    parser.add_argument("status", nargs="?", type=int)
    parser.add_argument("--preserve-stage", action="store_true")
    args = parser.parse_args()
    output = args.output.absolute()
    if args.action == "stage":
        if not args.value:
            parser.error("stage requires a nonempty value")
        replace_progress_json(output / "raw-stage.json", {
            "schema": "R3-G-05-raw-stage-v1", "stage": args.value, "active": True,
        })
    elif args.action == "failure":
        if not args.value or args.status is None:
            parser.error("failure requires stage and status")
        stage = previous_stage(output, args.value) if args.preserve_stage else args.value
        publish_raw_failure(output, {
            "schema": "R3-G-05-raw-failure-v1", "stage": stage,
            "exitStatus": args.status,
        })
    else:
        if not args.value or "/" in args.value:
            parser.error("unlink requires one marker basename")
        durable_unlink(output / args.value, missing_ok=True)


if __name__ == "__main__":
    main()
