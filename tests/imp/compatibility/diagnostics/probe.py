#!/usr/bin/env python3
"""Aggregate fail-closed capability audit for all four IMP boundaries."""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def report() -> dict[str, object]:
    rust_source = (HERE / "rust-expansion/src/lib.rs").read_text(encoding="utf-8")
    analysis_source = (HERE / "krs-analysis/src/lib.rs").read_text(encoding="utf-8")
    command = (ROOT / "crates/krs-cli/src/command.rs").read_text(encoding="utf-8")
    diagnostic = (ROOT / "crates/krs-cli/src/diagnostic.rs").read_text(encoding="utf-8")
    main = (ROOT / "crates/krs-cli/src/main.rs").read_text(encoding="utf-8")
    backend = load(HERE / "backend-capability/probe.py", "imp_backend_probe").report()
    return {
        "schema": 1,
        "rust_expansion_fixture": '#[k::constructor(syntax = "broken")]' in rust_source,
        "rust_analyzer_exact_range_wired": (HERE / "rust-expansion/lsp_probe.py").is_file(),
        "krs_analysis_cross_item_fixture": len(re.findall(r"pub struct Collision", analysis_source)) == 2,
        "krs_cli_structured_analysis_range": all(token in diagnostic for token in (
            "pub struct DiagnosticEnvelope", "pub authored_range: SourceRange",
            "pub stage: DiagnosticStage", "pub code: String",
        )) and "Diagnostics(Vec<DiagnosticEnvelope>)" in command
            and ".diagnostics()" in main and "to_json_line()" in main,
        "k_frontend_exact_sidecar_probe": (HERE / "k-frontend/probe.py").is_file(),
        "backend": backend,
    }


def verify(value: dict[str, object]) -> None:
    missing = []
    for key in (
        "rust_expansion_fixture", "rust_analyzer_exact_range_wired",
        "krs_analysis_cross_item_fixture", "krs_cli_structured_analysis_range",
        "k_frontend_exact_sidecar_probe",
    ):
        if value.get(key) is not True:
            missing.append(key)
    backend = value.get("backend")
    if not isinstance(backend, dict) or not all(backend.get(key) is True for key in (
        "adapter_structured_diagnostic", "cli_structured_diagnostic_envelope",
        "cli_authored_origin_translation", "cli_structured_diagnostic_rendering",
    )):
        missing.append("backend_structured_authored_translation")
    if missing:
        raise RuntimeError(f"diagnostic release boundaries incomplete: {missing}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report-only", action="store_true")
    arguments = parser.parse_args()
    value = report()
    print(json.dumps(value, sort_keys=True, separators=(",", ":")))
    if not arguments.report_only:
        verify(value)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RuntimeError as error:
        print(f"BLOCKED diagnostics: {error}", file=sys.stderr)
        raise SystemExit(1)
