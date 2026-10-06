"""Submission order of the conformance driver (longest first from earlier measurements)."""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run import longest_first, previous_case_seconds


class ScheduleTests(unittest.TestCase):
    def test_the_latest_measurement_of_each_case_counts(self):
        with tempfile.TemporaryDirectory() as directory:
            older = Path(directory) / "older.toml"
            newer = Path(directory) / "newer.toml"
            older.write_text('[[case]]\nname = "a"\nseconds = 5.0\n\n[[case]]\nname = "b"\nseconds = 1.0\n')
            newer.write_text('[[case]]\nname = "a"\nseconds = 2.0\n')
            missing = Path(directory) / "missing.toml"
            self.assertEqual(previous_case_seconds([older, newer, missing]), {"a": 2.0, "b": 1.0})

    def test_slow_and_unmeasured_cases_start_first(self):
        cases = [("a", "ktest"), ("b", "ktest"), ("c", "fail"), ("d", "ktest")]
        self.assertEqual(
            longest_first(cases, {"a": 3.0, "b": 90.0, "d": 3.0}),
            [("c", "fail"), ("b", "ktest"), ("a", "ktest"), ("d", "ktest")],
        )

    def test_without_measurements_the_order_is_unchanged(self):
        cases = [("b", "ktest"), ("a", "ktest")]
        self.assertEqual(longest_first(cases, {}), cases)


if __name__ == "__main__":
    unittest.main()
