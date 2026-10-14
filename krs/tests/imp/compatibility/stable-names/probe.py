#!/usr/bin/env python3
"""Fail-closed stable-name move probe through ``krs emit-k``."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from support import GateError, krs_gate  # noqa: E402
from support.krs import Invocation  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import checkout_scratch  # noqa: E402


HERE = Path(__file__).resolve().parent
PROBE_TARGET = {
    "CARGO_TARGET_DIR": os.fspath(
        Path(os.environ.get("KRS_IMP_PROBE_TARGET_ROOT", checkout_scratch())) / "stable-names"
    )
}


def capability_report() -> dict[str, object]:
    fixtures = {
        name: (HERE / name / "src/lib.rs").is_file()
        for name in ("baseline", "private-move", "public-move", "public-move-pinned")
    }
    return {
        "schema": 1,
        "fixtures": fixtures,
    }


FIXTURE_PACKAGES = {
    "baseline": "krs-imp-stable-baseline",
    "private-move": "krs-imp-stable-private-move",
    "public-move": "krs-imp-stable-public-move",
    "public-move-pinned": "krs-imp-stable-public-move-pinned",
}


def move_evidence(krs: Path) -> dict[str, object]:
    gate = krs_gate.configured_or_build()
    with tempfile.TemporaryDirectory(prefix="krs-imp-stable-") as temporary:
        temporary = Path(temporary)
        details = {}
        public = {}
        projections = {}
        source_keys = {}
        sidecars = {}
        for name in FIXTURE_PACKAGES:
            output = temporary / f"{name}-llvm"
            run(Invocation(krs, HERE / name / "Cargo.toml", FIXTURE_PACKAGES[name], "main").argv(
                "emit-k", "--backend", "llvm", "--output", output,
            ), environment=PROBE_TARGET, timeout=180)
            rows, public_rows, symbols, sidecar = krs_gate.ir_queries(gate, output, [
                {"kind": "descriptor_details"},
                {"kind": "descriptor_details", "public_only": True},
                {"kind": "symbol_projection", "emitted_names": ["Expr", "publicValue"]},
                {"kind": "symbols"},
            ])
            details[name] = rows["rows"]
            public[name] = sorted((r["normalized"] for r in public_rows["rows"]), key=lambda r: json.dumps(r, sort_keys=True))
            projections[name] = symbols["rows"]
            source_keys[name] = symbols["source_keys"]
            sidecars[name] = sidecar
            if len(projections[name]) != 2 or len(source_keys[name]) != 2:
                raise GateError("stable-name projection needs exactly two public symbols and source keys")
        output = temporary / "baseline-haskell"
        run(Invocation(krs, HERE / "baseline/Cargo.toml", FIXTURE_PACKAGES["baseline"], "main").argv(
            "emit-k", "--backend", "haskell", "--output", output,
        ), environment=PROBE_TARGET, timeout=180)
        baseline_haskell = krs_gate.ir_query(gate, output, {"kind": "symbols"})

    def keys(name: str, path: str) -> set[tuple[tuple[str, ...], str, str]]:
        return {(tuple(r["module_path"]), r["item_name"], r["item_kind"]) for r in details[name] if r["module_path"] == [path]}

    baseline_private = keys("baseline", "internal_old")
    moved_private = keys("private-move", "internal_new")
    baseline_public = keys("baseline", "api")
    moved_public = keys("public-move", "moved_api")
    pinned_public = keys("public-move-pinned", "moved_api")
    # Paths are part of descriptor identity even when item names stay the same.
    report = {
        "baseline_descriptors": len(details["baseline"]),
        "exact_public_visibility_recovered": len(public["baseline"]) == 3,
        "private_move_public_projection_equal": public["baseline"] == public["private-move"],
        "private_internal_identity_changed": bool(baseline_private and moved_private) and baseline_private != moved_private,
        "public_identity_change_detected": bool(baseline_public and moved_public) and baseline_public != moved_public,
        "pinned_descriptor_provenance_moved": bool(baseline_public and pinned_public) and baseline_public != pinned_public,
        "pinned_exact_symbols_recovered": {r["explicit_symbol"] for r in details["public-move-pinned"] if r["module_path"] == ["moved_api"] and r["explicit_symbol"] is not None} == {"api::Expr", "api::PublicValue"},
        "package_version_and_fixture_path_do_not_change_public_symbol": projections["baseline"] == projections["private-move"],
        "unpinned_public_move_changes_symbol_identity": projections["baseline"] != projections["public-move"],
        "pinned_reordered_public_move_preserves_symbol_identity": projections["baseline"] == projections["public-move-pinned"],
        "pinned_move_preserves_distinct_provenance": source_keys["baseline"] != source_keys["public-move-pinned"],
        "backend_selection_does_not_change_symbols": sidecars["baseline"] == baseline_haskell,
    }
    return report


def verify(report: dict[str, object]) -> None:
    fixtures = report.get("fixtures")
    if not isinstance(fixtures, dict) or set(fixtures) != set(FIXTURE_PACKAGES) or not all(
        value is True for value in fixtures.values()
    ):
        raise GateError("all four stable-name move fixtures are required")
    evidence = report.get("move_evidence")
    if not isinstance(evidence, dict):
        raise GateError("move evidence is absent or has an unknown shape")
    failed = sorted(
        key for key, value in evidence.items()
        if key != "baseline_descriptors" and value is not True
    )
    if evidence.get("baseline_descriptors") != 6 or failed:
        raise GateError(f"stable-name move evidence failed: {failed}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--krs", type=Path, required=True)
    arguments = parser.parse_args()
    report = capability_report()
    report["move_evidence"] = move_evidence(arguments.krs.resolve())
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    verify(report)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except GateError as error:
        print(f"BLOCKED stable names: {error}", file=sys.stderr)
        raise SystemExit(1)
