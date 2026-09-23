#!/usr/bin/env python3
"""Refresh or check the mechanically derived portions of the M4 pin ledger."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import verify
from support import ROOT
from support.hashing import sha256_file


HERE = Path(__file__).resolve().parent
PINS = HERE / "pins.json"
CORPUS = HERE / "corpus.json"


def refreshed() -> dict[str, object]:
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    pins["corpus_sha256"] = sha256_file(CORPUS)
    pins["source_sha256"] = {
        relative: sha256_file(ROOT / relative)
        for relative in sorted(verify.expected_source_ledger_paths())
    }
    for entry in pins["proof_ledgers"].values():
        entry["sha256"] = sha256_file(ROOT / entry["path"])
    return pins


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write",
        action="store_true",
        help="replace pins.json; without this flag, only check it",
    )
    arguments = parser.parse_args()
    expected = json.dumps(refreshed(), indent=2, ensure_ascii=False) + "\n"
    observed = PINS.read_text(encoding="utf-8")
    if arguments.write:
        PINS.write_text(expected, encoding="utf-8")
        print(f"updated {PINS.relative_to(ROOT)}")
        return 0
    if observed != expected:
        print(
            "M4 mechanically derived pin ledger is stale; run "
            "tests/m4/refresh_source_ledger.py --write",
            file=sys.stderr,
        )
        return 1
    print("PASS M4 source ledger is current")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
