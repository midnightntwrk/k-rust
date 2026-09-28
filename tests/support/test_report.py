"""Tests for shared gate result reporting."""

from __future__ import annotations

from contextlib import redirect_stdout
import io
import unittest

from support.report import Results


class ResultsTests(unittest.TestCase):
    def test_status_lines_preserve_imp_and_cli_columns(self) -> None:
        output = io.StringIO()
        with redirect_stdout(output):
            Results().add("oracle", "PASS", "exact")
            Results(width=11).add("cli", "MATCH", "same bytes")
        self.assertEqual(output.getvalue(), "PASS         oracle: exact\nMATCH       cli: same bytes\n")

    def test_required_and_optional_statuses(self) -> None:
        results = Results()
        output = io.StringIO()
        with redirect_stdout(output):
            for status in ("PASS", "MATCH"):
                results.add(status, status, "ok")
            for status in ("SKIP", "UNAVAILABLE", "FAIL", "MISMATCH", "RECORDED"):
                results.add(status, status, "optional", required=False)
        self.assertFalse(results.failed)
        with redirect_stdout(output):
            results.add("required", "UNAVAILABLE", "missing")
        self.assertTrue(results.failed)
        for status in ("FAIL", "SKIP", "MISMATCH", "RECORDED"):
            with self.subTest(status=status), redirect_stdout(output):
                required = Results()
                required.add("required", status, "failed")
                self.assertTrue(required.failed)

    def test_rejects_unknown_status_without_printing(self) -> None:
        output = io.StringIO()
        results = Results()
        with redirect_stdout(output):
            with self.assertRaisesRegex(ValueError, "unknown gate result status 'PAS'"):
                results.add("check", "PAS", "typo")
        self.assertEqual(output.getvalue(), "")
        self.assertFalse(results.failed)
