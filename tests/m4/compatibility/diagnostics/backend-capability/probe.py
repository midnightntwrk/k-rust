#!/usr/bin/env python3
"""Audit structured native diagnostics and CLI authored-origin translation."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
M4_MANIFEST = ROOT / "tests/m4/rust-definition/Cargo.toml"
M4_CLAIMS = ROOT / "tests/m4/rust-definition/src/claims.rs"
EXPECTED_LABELS = {
    '"branching"',
    '"branching-program"',
    '"branching-deadcode"',
    '"while-cut-rule-delayed"',
    '"bmc-loop-concrete"',
    '"bmc-loop-symbolic"',
}


class BackendDiagnosticError(RuntimeError):
    pass


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


def dynamic_report(krs: Path) -> dict[str, object]:
    environment = os.environ.copy()
    environment["CARGO_TARGET_DIR"] = "/tmp/krs-m4-backend-diagnostic-target"
    with tempfile.TemporaryDirectory(prefix="krs-m4-backend-diag-", dir="/tmp") as directory:
        output_directory = Path(directory)
        process = subprocess.run(
            [
                str(krs), "build", "--manifest-path", str(M4_MANIFEST),
                "--package", "krs-m4-complete-imp", "--definition", "main",
                "--backend", "llvm", "--output", str(output_directory),
            ],
            cwd=ROOT, env=environment, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=300, check=False,
        )
        artifacts_absent = not any(output_directory.iterdir())
    output = "\n".join(part for part in (process.stdout, process.stderr) if part)
    if process.returncode == 0:
        raise BackendDiagnosticError("full M4 LLVM unexpectedly accepted existential claims")
    if "/collectors/" in output or "target/krs/collectors" in output:
        raise BackendDiagnosticError("backend diagnostic leaked a generated collector path")

    envelopes = []
    for line in output.splitlines():
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise BackendDiagnosticError(f"backend emitted non-JSON diagnostic text: {line[:240]}") from error
        if not isinstance(value, dict):
            raise BackendDiagnosticError("backend diagnostic envelope is not an object")
        envelopes.append(value)

    source = M4_CLAIMS.read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    labels = set()
    for envelope in envelopes:
        expected_fields = {
            "schema_version", "stage", "code", "severity", "message", "authored_range",
        }
        if set(envelope) != expected_fields:
            raise BackendDiagnosticError(f"backend diagnostic has unknown fields: {sorted(envelope)}")
        if (
            envelope.get("schema_version") != 1
            or envelope.get("stage") != "backend-capability"
            or envelope.get("code") != "UnsupportedExistentialVariable"
            or envelope.get("severity") != "error"
        ):
            raise BackendDiagnosticError("backend diagnostic lost its stable classification")
        authored = envelope.get("authored_range")
        if not isinstance(authored, dict) or set(authored) != {"file", "start_byte", "end_byte"}:
            raise BackendDiagnosticError("backend diagnostic lacks one exact authored byte range")
        file = authored["file"]
        if not isinstance(file, dict) or (
            file.get("package_relative_path") != "src/claims.rs"
            or file.get("content_sha256") != digest
        ):
            raise BackendDiagnosticError("backend diagnostic does not identify the exact authored file")
        start = authored["start_byte"]
        end = authored["end_byte"]
        if not isinstance(start, int) or not isinstance(end, int) or not 0 <= start < end <= len(source):
            raise BackendDiagnosticError("backend diagnostic authored bounds are invalid")
        labels.add(source[start:end].decode("utf-8"))

    return {
        "exit_is_capability_failure": process.returncode == 1,
        "diagnostic_count": len(envelopes),
        "exact_authored_claim_labels": labels == EXPECTED_LABELS,
        "generated_paths_absent": True,
        "partial_artifacts_absent": artifacts_absent,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--krs", type=Path)
    arguments = parser.parse_args()
    value = report()
    if arguments.krs:
        value["full_m4_llvm"] = dynamic_report(arguments.krs.resolve())
    print(json.dumps(value, sort_keys=True, separators=(",", ":")))
    if not all(value[key] is True for key in (
        "adapter_structured_diagnostic", "cli_structured_diagnostic_envelope",
        "cli_authored_origin_translation", "cli_structured_diagnostic_rendering",
    )):
        print("BLOCKED backend diagnostic: structured translation is not rendered end-to-end", file=sys.stderr)
        return 1
    dynamic = value.get("full_m4_llvm")
    if dynamic is not None:
        if not isinstance(dynamic, dict):
            print("BLOCKED backend diagnostic: dynamic report has an unknown shape", file=sys.stderr)
            return 1
        if dynamic.get("diagnostic_count") != len(EXPECTED_LABELS) or not all(
            child is True for key, child in dynamic.items() if key != "diagnostic_count"
        ):
            print("BLOCKED backend diagnostic: full M4 exact ranges are incomplete", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BackendDiagnosticError, subprocess.TimeoutExpired) as error:
        print(f"BLOCKED backend diagnostic: {error}", file=sys.stderr)
        raise SystemExit(1)
