"""Unit checks for the strict IMP oracle's non-K orchestration."""

from __future__ import annotations

from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import tempfile
import unittest

from support.imp_oracle import aggregate, compare_output
from support.pins import Ledger
from support.report import Results


class AggregateTests(unittest.TestCase):
    def test_key_order_does_not_change_digest(self) -> None:
        self.assertEqual(
            aggregate({"b": {"value": 2}, "a": [1, 2]}),
            aggregate({"a": [1, 2], "b": {"value": 2}}),
        )
        self.assertNotEqual(aggregate({"a": 1}), aggregate({"a": 2}))


class CompareOutputTests(unittest.TestCase):
    def test_check_mode_reports_mismatch_and_continues(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "pins.json"
            path.write_text('{"digest": "old", "other": "old"}\n', encoding="utf-8")
            pins = Ledger(path)
            results = Results()
            output = StringIO()
            with redirect_stdout(output):
                compare_output(results, pins, "first", "digest", "new", "matches")
                compare_output(results, pins, "second", "other", "new", "matches")
            self.assertTrue(results.failed)
            self.assertEqual(output.getvalue().count("FAIL"), 2)
            self.assertIn("pins.json digest differs from its pin", output.getvalue())
            self.assertEqual(path.read_text(encoding="utf-8"), '{"digest": "old", "other": "old"}\n')

    def test_record_mode_waits_for_finish_and_skips_noop_write(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "pins.json"
            original = '{"digest": "old"}\n'
            path.write_text(original, encoding="utf-8")
            pins = Ledger(path, record=True)
            results = Results()
            with redirect_stdout(StringIO()):
                compare_output(results, pins, "digest", "digest", "old", "matches")
            self.assertFalse(results.failed)
            self.assertEqual(path.read_text(encoding="utf-8"), original)
            self.assertEqual(pins.write(), [])
            self.assertEqual(path.read_text(encoding="utf-8"), original)

            pins = Ledger(path, record=True)
            with redirect_stdout(StringIO()):
                compare_output(Results(), pins, "digest", "digest", "new", "matches")
            self.assertEqual(path.read_text(encoding="utf-8"), original)
            self.assertEqual(pins.write(), ["digest"])
            self.assertIn('"new"', path.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
