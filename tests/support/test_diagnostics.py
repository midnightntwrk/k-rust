"""Tests for diagnostic envelope extraction."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest

from support import GateError
from support.diagnostics import (
    AuthoredRange,
    KrsDiagnostic,
    cargo_primary_span,
    envelopes,
    krs_diagnostics,
)


class DiagnosticEnvelopeTests(unittest.TestCase):
    def test_extracts_objects_in_order_from_mixed_text(self) -> None:
        stream = 'building\n{"code":"first"}\n[1, 2]\nnot JSON\n {"code":"second"} \n'
        self.assertEqual(envelopes(stream), [{"code": "first"}, {"code": "second"}])

    def test_accepts_bytes_and_ignores_invalid_utf8(self) -> None:
        stream = b'\xff\n{"reason":"compiler-message"}\n{"incomplete":\n'
        self.assertEqual(envelopes(stream), [{"reason": "compiler-message"}])

    def test_ignores_non_object_json_values(self) -> None:
        self.assertEqual(envelopes('null\n42\n"message"\ntrue\n'), [])


class TypedDiagnosticTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.package_root = Path(self.temporary.name)
        (self.package_root / "src").mkdir()
        (self.package_root / "src/lib.rs").write_bytes(b"a\xf0\x9f\x92\xa1b")

    def envelope(self) -> dict:
        return {
            "schema_version": 1,
            "stage": "analysis",
            "code": "example",
            "severity": "error",
            "message": "example diagnostic",
            "authored_range": {
                "file": {
                    "package": {
                        "k_namespace": "test",
                        "cargo_name": "test-package",
                        "cargo_version": "0.1.0",
                        "cargo_source": "workspace",
                    },
                    "package_relative_path": "src/lib.rs",
                    "content_sha256": "0" * 64,
                },
                "start_byte": 1,
                "end_byte": 5,
            },
            "notes": ["one", "two"],
        }

    def test_parses_krs_and_skips_cargo(self) -> None:
        stream = '\n'.join((
            json.dumps({"reason": "compiler-message", "message": {"level": "error"}}),
            json.dumps(self.envelope()),
        ))
        diagnostics = krs_diagnostics(stream)
        self.assertEqual(len(diagnostics), 1)
        diagnostic = diagnostics[0]
        self.assertEqual(diagnostic.stage, "analysis")
        self.assertEqual(diagnostic.notes, ("one", "two"))
        self.assertEqual(diagnostic.authored_range.cargo_name, "test-package")
        self.assertEqual(diagnostic.selected_bytes(self.package_root), "💡".encode())
        self.assertEqual(json.loads(diagnostic.raw_json), self.envelope())

    def test_rejects_malformed_krs_envelopes(self) -> None:
        broken_values = []
        for field in ("schema_version", "stage", "code", "severity", "message", "authored_range"):
            value = self.envelope()
            del value[field]
            broken_values.append(value)
        for key, bad in (("start_byte", -1), ("end_byte", True), ("file", [])):
            value = self.envelope()
            value["authored_range"][key] = bad
            broken_values.append(value)
        value = self.envelope()
        value["authored_range"]["end_byte"] = 0
        broken_values.append(value)
        value = self.envelope()
        value["authored_range"]["file"]["content_sha256"] = "not-a-digest"
        broken_values.append(value)
        for value in broken_values:
            with self.subTest(value=value), self.assertRaises(GateError):
                krs_diagnostics(json.dumps(value))

    def test_optional_range_and_generated_fields(self) -> None:
        value = self.envelope()
        value["authored_range"] = None
        value["generated_range"] = {
            "artifact": "definition.k", "start_line": 2, "start_column": 3,
            "end_line": 2, "end_column": 8,
        }
        value.pop("notes")
        diagnostic, = krs_diagnostics(json.dumps(value).encode())
        self.assertIsNone(diagnostic.authored_range)
        self.assertEqual(diagnostic.generated_range.artifact, "definition.k")
        self.assertEqual(diagnostic.notes, ())

    def test_rejects_out_of_bounds_and_absent_authored_range(self) -> None:
        with self.assertRaises(GateError):
            AuthoredRange("name", "src/lib.rs", "0" * 64, 1, 7).selected_bytes(self.package_root)
        with self.assertRaises(GateError):
            KrsDiagnostic(1, "analysis", "code", "error", "message", None).selected_bytes(self.package_root)


class CargoSpanTests(unittest.TestCase):
    def envelope(self, message: str, spans: list[dict], level: str = "error") -> dict:
        return {"reason": "compiler-message", "message": {
            "level": level, "message": message, "spans": spans,
        }}

    def span(self, *, primary: bool = True) -> dict:
        return {
            "file_name": "src/lib.rs", "byte_start": 2, "byte_end": 7,
            "line_start": 3, "column_start": 4, "column_end": 9,
            "is_primary": primary,
        }

    def test_first_error_and_filtered_messages(self) -> None:
        stream = '\n'.join(json.dumps(value) for value in (
            self.envelope("warning", [self.span()], "warning"),
            self.envelope("first error", [self.span(), self.span(primary=False)]),
            self.envelope("target error", [self.span()]),
        ))
        first = cargo_primary_span(stream)
        self.assertEqual((first.message, first.byte_start, first.column_end), ("first error", 2, 9))
        self.assertEqual(cargo_primary_span(stream, message_contains="target").message, "target error")

    def test_filter_counts_primary_spans_across_messages(self) -> None:
        stream = "\n".join(json.dumps(self.envelope("target error", [self.span()])) for _ in range(2))
        with self.assertRaises(GateError):
            cargo_primary_span(stream, message_contains="target")

    def test_zero_or_multiple_primary_spans_fail(self) -> None:
        for spans in ([], [self.span(), self.span()]):
            with self.subTest(spans=spans), self.assertRaises(GateError):
                cargo_primary_span(json.dumps(self.envelope("error", spans)))
        with self.assertRaises(GateError):
            cargo_primary_span(json.dumps(self.envelope("warning", [self.span()], "warning")))
