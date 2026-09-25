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


def validate_requirements(manifest: dict) -> None:
    """Reject prerequisites the gates cannot enforce."""
    allowed = {"reference-toolchain", "semantics-support"}
    for section in ("compile", "kast", "execution", "proof", "rpc", "symbolic"):
        for case in manifest.get(section, []):
            requirements = case.get("requires")
            if not isinstance(requirements, list) or not requirements:
                raise ValueError(f"{section} case {case.get('name')} needs a requires array")
            for requirement in requirements:
                if not isinstance(requirement, str) or requirement not in allowed:
                    raise ValueError(
                        f"unknown requirement {requirement!r} on {section} case {case.get('name')}"
                    )


COMPILE_OUTCOMES = {"accept", "reject", "port-accepts"}


def validate_compile_outcomes(manifest: dict) -> None:
    """Every compile outcome is one the gate enforces; a divergence carries its reason and
    the reference diagnostic it pins."""
    for case in manifest.get("compile", []):
        name = case.get("name")
        expect = case.get("expect", "accept")
        if expect not in COMPILE_OUTCOMES:
            raise ValueError(f"unknown expect {expect!r} on compile case {name}")
        reason = case.get("reason")
        reference_error = case.get("reference-error")
        if expect == "port-accepts":
            if not isinstance(reason, str) or not reason.strip():
                raise ValueError(f"port-accepts compile case {name} needs a written reason")
            if not isinstance(reference_error, str) or not reference_error.strip():
                raise ValueError(
                    f"port-accepts compile case {name} needs the reference-error it pins"
                )
            if case.get("comparisons"):
                raise ValueError(
                    f"port-accepts compile case {name} has no reference artifact to compare"
                )
        else:
            if reason is not None:
                raise ValueError(f"reason on compile case {name} is only read for port-accepts")
            if reference_error is not None:
                raise ValueError(
                    f"reference-error on compile case {name} is only read for port-accepts"
                )


def main() -> int:
    try:
        with MANIFEST.open("rb") as source:
            manifest = expand(tomllib.load(source))
        validate_requirements(manifest)
        validate_compile_outcomes(manifest)
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
