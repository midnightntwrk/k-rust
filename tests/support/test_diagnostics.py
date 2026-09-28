"""Tests for diagnostic envelope extraction."""

from __future__ import annotations

import unittest

from support.diagnostics import envelopes


class DiagnosticEnvelopeTests(unittest.TestCase):
    def test_extracts_objects_in_order_from_mixed_text(self) -> None:
        stream = 'building\n{"code":"first"}\n[1, 2]\nnot JSON\n {"code":"second"} \n'
        self.assertEqual(envelopes(stream), [{"code": "first"}, {"code": "second"}])

    def test_accepts_bytes_and_ignores_invalid_utf8(self) -> None:
        stream = b'\xff\n{"reason":"compiler-message"}\n{"incomplete":\n'
        self.assertEqual(envelopes(stream), [{"reason": "compiler-message"}])

    def test_ignores_non_object_json_values(self) -> None:
        self.assertEqual(envelopes('null\n42\n"message"\ntrue\n'), [])
