#!/usr/bin/env python3
"""Render the differential TOML as JSON after expanding checkout placeholders."""

from __future__ import annotations

import json
import os
import re
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


def validate_reference_kompile_options(manifest: dict) -> None:
    """Options that change the reference definition an execution case compares against are read
    only by the execution gate, and each case that carries them states why its programs cannot
    reach what they change."""
    for section in ("compile", "kast", "proof", "rpc", "symbolic"):
        for case in manifest.get(section, []):
            for key in ("reference-kompile-options", "reference-kompile-options-reason"):
                if key in case:
                    raise ValueError(
                        f"{key} on {section} case {case.get('name')} is only read for execution"
                    )
    for case in manifest.get("execution", []):
        name = case.get("name")
        options = case.get("reference-kompile-options")
        reason = case.get("reference-kompile-options-reason")
        if options is None:
            if reason is not None:
                raise ValueError(
                    f"reference-kompile-options-reason on execution case {name} has no options"
                )
            continue
        if (
            not isinstance(options, list)
            or not options
            or not all(isinstance(option, str) and option.startswith("--") for option in options)
        ):
            raise ValueError(
                f"reference-kompile-options on execution case {name} must be a non-empty array of options"
            )
        if not isinstance(reason, str) or not reason.strip():
            raise ValueError(
                f"reference-kompile-options on execution case {name} need a written reason"
            )


def validate_reference_result_simplification(manifest: dict) -> None:
    """N41: the execution gate compares a case's program results against the reference result as
    the reference's own simplifier rewrites it only when the case says why
    (reference-result-simplification-reason). The step is defined for program results, so a case
    with search or any runs, or with an oracle exception, cannot carry it."""
    key = "reference-result-simplification-reason"
    for section in ("compile", "kast", "proof", "rpc", "symbolic"):
        for case in manifest.get(section, []):
            if key in case:
                raise ValueError(
                    f"{key} on {section} case {case.get('name')} is only read for execution"
                )
    for case in manifest.get("execution", []):
        if key not in case:
            continue
        name = case.get("name")
        reason = case[key]
        if not isinstance(reason, str) or not reason.strip():
            raise ValueError(f"{key} on execution case {name} must be a written reason")
        if not case.get("programs"):
            raise ValueError(f"{key} on execution case {name} needs programs")
        for other in ("search", "any", "oracle-exception"):
            if other in case:
                raise ValueError(f"{key} on execution case {name} cannot be combined with {other}")


LIFTED_CELL_NAME = re.compile(r"[A-Za-z][A-Za-z0-9]*")


def validate_lifted_cells(manifest: dict) -> None:
    """N45: an accepted [[compile]] case lists the axioms whose rule writes a cell inside a cell
    that does not contain it in the configuration (lifted-cells, one {rule, cell} table per
    axiom: the KORE label of the rule and the cell's name without its angle brackets), and says
    why in lifted-cells-reason. The semantic KORE comparison reads nothing else."""
    keys = ("lifted-cells", "lifted-cells-reason")
    for section in ("kast", "execution", "proof", "rpc", "symbolic"):
        for case in manifest.get(section, []):
            for key in keys:
                if key in case:
                    raise ValueError(
                        f"{key} on {section} case {case.get('name')} is only read for compile"
                    )
    for case in manifest.get("compile", []):
        name = case.get("name")
        entries = case.get("lifted-cells")
        reason = case.get("lifted-cells-reason")
        if entries is None:
            if reason is not None:
                raise ValueError(f"lifted-cells-reason on compile case {name} has no lifted-cells")
            continue
        if case.get("expect", "accept") != "accept":
            raise ValueError(f"lifted-cells on compile case {name} needs an accept case")
        if not isinstance(entries, list) or not entries:
            raise ValueError(f"lifted-cells on compile case {name} must be a non-empty array")
        seen = set()
        for entry in entries:
            if (
                not isinstance(entry, dict)
                or set(entry) != {"rule", "cell"}
                or not isinstance(entry["rule"], str)
                or not entry["rule"].strip()
                or not isinstance(entry["cell"], str)
                or not LIFTED_CELL_NAME.fullmatch(entry["cell"])
            ):
                raise ValueError(
                    f"lifted-cells entry {entry!r} on compile case {name} must be "
                    "{rule = <label>, cell = <alphanumeric cell name>}"
                )
            if (entry["rule"], entry["cell"]) in seen:
                raise ValueError(f"lifted-cells entry {entry!r} on compile case {name} is repeated")
            seen.add((entry["rule"], entry["cell"]))
        if not isinstance(reason, str) or not reason.strip():
            raise ValueError(f"lifted-cells on compile case {name} need a written lifted-cells-reason")


def main() -> int:
    try:
        with MANIFEST.open("rb") as source:
            manifest = expand(tomllib.load(source))
        validate_requirements(manifest)
        validate_compile_outcomes(manifest)
        validate_reference_kompile_options(manifest)
        validate_reference_result_simplification(manifest)
        validate_lifted_cells(manifest)
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
