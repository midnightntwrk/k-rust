"""Contract tests for gate entry handling."""

from __future__ import annotations

import contextlib
import io
import unittest

from support import GateError, entry


class EntryTests(unittest.TestCase):
    def run_entry(self, main, **kwargs):
        stdout = io.StringIO()
        stderr = io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            with self.assertRaises(SystemExit) as raised:
                entry("sample", main, **kwargs)
        return raised.exception.code, stdout.getvalue(), stderr.getvalue()

    def test_none_prints_pass(self):
        self.assertEqual(self.run_entry(lambda: None), (0, "PASS sample\n", ""))

    def test_integer_is_exit_code(self):
        self.assertEqual(self.run_entry(lambda: 3), (3, "", ""))

    def test_gate_error_is_expected(self):
        def fail():
            raise GateError("bad evidence")

        self.assertEqual(self.run_entry(fail), (1, "", "FAIL sample: bad evidence\n"))

    def test_other_errors_propagate_by_default(self):
        def fail():
            raise ValueError("bad value")

        with self.assertRaises(ValueError):
            entry("sample", fail)

    def test_extra_expected_failure(self):
        def fail():
            raise KeyError("missing")

        self.assertEqual(
            self.run_entry(fail, errors=(KeyError,)),
            (1, "", "FAIL sample: 'missing'\n"),
        )


if __name__ == "__main__":
    unittest.main()
