#!/usr/bin/env python3
"""Audit the structured native diagnostic seam and CLI authored-origin translation."""

from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from support import ROOT, GateError  # noqa: E402


def report() -> dict[str, object]:
    adapter = (ROOT / "crates/krs-k-rust/src/lib.rs").read_text(encoding="utf-8")
    diagnostic = (ROOT / "crates/krs-cli/src/diagnostic.rs").read_text(encoding="utf-8")
    main = (ROOT / "crates/krs-cli/src/main.rs").read_text(encoding="utf-8")
    return {
        "schema": 1,
        "adapter_structured_diagnostic": all(
            token in adapter for token in (
                "pub struct FrontendDiagnostic", "pub code: String",
                "pub severity: DiagnosticSeverity", "pub location: Option<SourceLocation>",
            )
        ),
        "cli_structured_diagnostic_envelope": all(token in diagnostic for token in (
            "pub struct DiagnosticEnvelope", "pub schema_version: u32",
            "pub stage: DiagnosticStage", "pub code: String",
            "pub severity: DiagnosticSeverity", "pub authored_range: SourceRange",
            "pub generated_range: Option<DiagnosticGeneratedRange>",
        )),
        "cli_authored_origin_translation": all(token in diagnostic for token in (
            "pub fn exact_authored_range(", "pub fn translate_native_diagnostic(",
            "pub fn translate_k_frontend_diagnostic(",
        )),
        "cli_structured_diagnostic_rendering": (
            ".diagnostics()" in main and "to_json_line()" in main
        ),
    }


def main() -> int:
    value = report()
    print(json.dumps(value, sort_keys=True, separators=(",", ":")))
    if not all(value[key] is True for key in (
        "adapter_structured_diagnostic", "cli_structured_diagnostic_envelope",
        "cli_authored_origin_translation", "cli_structured_diagnostic_rendering",
    )):
        print("BLOCKED native diagnostic: structured translation is not rendered end-to-end", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except GateError as error:
        print(f"BLOCKED native diagnostic: {error}", file=sys.stderr)
        raise SystemExit(1)
