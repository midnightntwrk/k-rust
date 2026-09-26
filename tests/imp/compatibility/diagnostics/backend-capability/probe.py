#!/usr/bin/env python3
"""Audit structured native diagnostics and CLI authored-origin translation."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from support import ROOT, GateError  # noqa: E402
from support.hashing import sha256_bytes  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import checkout_scratch  # noqa: E402


HERE = Path(__file__).resolve().parent
IMP_MANIFEST = ROOT / "tests/imp/rust-definition/Cargo.toml"
IMP_CLAIMS = ROOT / "tests/imp/rust-definition/src/claims.rs"
EXPECTED_LABELS = {
    '"branching"',
    '"branching-program"',
    '"branching-deadcode"',
    '"while-cut-rule-delayed"',
    '"bmc-loop-concrete"',
    '"bmc-loop-symbolic"',
}


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
    target = Path(os.environ.get("KRS_IMP_PROBE_TARGET_ROOT", checkout_scratch())) / "backend-capability"
    environment = {"CARGO_TARGET_DIR": os.fspath(target)}
    with tempfile.TemporaryDirectory(prefix="krs-imp-backend-diag-") as directory:
        output_directory = Path(directory)
        process = run(
            [
                krs, "build", "--manifest-path", IMP_MANIFEST,
                "--package", "krs-imp-definition", "--definition", "main",
                "--backend", "llvm", "--output", output_directory,
            ],
            environment=environment,
            timeout=300,
            check=False,
        )
        artifacts_absent = not any(output_directory.iterdir())
    output = "\n".join(part for part in (process.stdout, process.stderr) if part)
    if process.returncode == 0:
        raise GateError("full IMP LLVM unexpectedly accepted existential claims")
    if "/collectors/" in output or "target/krs/collectors" in output:
        raise GateError("backend diagnostic leaked a generated collector path")

    envelopes = []
    for line in output.splitlines():
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise GateError(f"backend emitted non-JSON diagnostic text: {line[:240]}") from error
        if not isinstance(value, dict):
            raise GateError("backend diagnostic envelope is not an object")
        envelopes.append(value)

    source = IMP_CLAIMS.read_bytes()
    digest = sha256_bytes(source)
    labels = set()
    for envelope in envelopes:
        expected_fields = {
            "schema_version", "stage", "code", "severity", "message", "authored_range",
        }
        if set(envelope) != expected_fields:
            raise GateError(f"backend diagnostic has unknown fields: {sorted(envelope)}")
        if (
            envelope.get("schema_version") != 1
            or envelope.get("stage") != "backend-capability"
            or envelope.get("code") != "UnsupportedExistentialVariable"
            or envelope.get("severity") != "error"
        ):
            raise GateError("backend diagnostic lost its stable classification")
        authored = envelope.get("authored_range")
        if not isinstance(authored, dict) or set(authored) != {"file", "start_byte", "end_byte"}:
            raise GateError("backend diagnostic lacks one exact authored byte range")
        file = authored["file"]
        if not isinstance(file, dict) or (
            file.get("package_relative_path") != "src/claims.rs"
            or file.get("content_sha256") != digest
        ):
            raise GateError("backend diagnostic does not identify the exact authored file")
        start = authored["start_byte"]
        end = authored["end_byte"]
        if not isinstance(start, int) or not isinstance(end, int) or not 0 <= start < end <= len(source):
            raise GateError("backend diagnostic authored bounds are invalid")
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
        value["full_imp_llvm"] = dynamic_report(arguments.krs.resolve())
    print(json.dumps(value, sort_keys=True, separators=(",", ":")))
    if not all(value[key] is True for key in (
        "adapter_structured_diagnostic", "cli_structured_diagnostic_envelope",
        "cli_authored_origin_translation", "cli_structured_diagnostic_rendering",
    )):
        print("BLOCKED backend diagnostic: structured translation is not rendered end-to-end", file=sys.stderr)
        return 1
    dynamic = value.get("full_imp_llvm")
    if dynamic is not None:
        if not isinstance(dynamic, dict):
            print("BLOCKED backend diagnostic: dynamic report has an unknown shape", file=sys.stderr)
            return 1
        if dynamic.get("diagnostic_count") != len(EXPECTED_LABELS) or not all(
            child is True for key, child in dynamic.items() if key != "diagnostic_count"
        ):
            print("BLOCKED backend diagnostic: full IMP exact ranges are incomplete", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except GateError as error:
        print(f"BLOCKED backend diagnostic: {error}", file=sys.stderr)
        raise SystemExit(1)
