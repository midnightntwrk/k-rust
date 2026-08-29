#!/usr/bin/env python3
"""Render the differential TOML as JSON after expanding checkout placeholders."""

from __future__ import annotations

import json
import os
from pathlib import Path
from string import Template
import sys
import tomllib


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = Path(__file__).with_name("reference-differential.toml")
VARIABLES = {
    "workspace": os.environ.get("WORKSPACE", str(ROOT)),
    "k": os.environ.get("K_CHECKOUT", str(ROOT / "k")),
    "imp": os.environ.get("IMP_SEMANTICS_CHECKOUT", str(ROOT / "imp-semantics")),
    "wasm": os.environ.get("WASM_SEMANTICS_CHECKOUT", str(ROOT / "wasm-semantics")),
    "evm": os.environ.get("EVM_SEMANTICS_CHECKOUT", str(ROOT / "evm-semantics")),
    "evm_equivalence": os.environ.get(
        "EVM_EQUIVALENCE_CHECKOUT", str(ROOT / "evm-equivalence")
    ),
    "mir": os.environ.get("MIR_SEMANTICS_CHECKOUT", str(ROOT / "mir-semantics")),
}


def expand(value: object) -> object:
    if isinstance(value, str):
        return Template(value).substitute(VARIABLES)
    if isinstance(value, list):
        return [expand(item) for item in value]
    if isinstance(value, dict):
        return {key: expand(item) for key, item in value.items()}
    return value


def main() -> int:
    try:
        with MANIFEST.open("rb") as source:
            manifest = expand(tomllib.load(source))
    except (OSError, tomllib.TOMLDecodeError, KeyError, ValueError) as error:
        print(f"error: invalid differential manifest: {error}", file=sys.stderr)
        return 2
    if sys.argv[1:] == ["--validate"]:
        return 0
    if sys.argv[1:]:
        print("usage: reference-manifest.py [--validate]", file=sys.stderr)
        return 2
    json.dump(manifest, sys.stdout, separators=(",", ":"))
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
