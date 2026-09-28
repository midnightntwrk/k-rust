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

    def test_expected_failure(self):
        for error in (GateError("bad evidence"), OSError("missing file"), ValueError("bad value")):
            with self.subTest(error=type(error).__name__):
                def fail():
                    raise error

                self.assertEqual(self.run_entry(fail), (1, "", f"FAIL sample: {error}\n"))

    def test_extra_expected_failure(self):
        def fail():
            raise KeyError("missing")

        self.assertEqual(
            self.run_entry(fail, errors=(KeyError,)),
            (1, "", "FAIL sample: 'missing'\n"),
        )


if __name__ == "__main__":
    unittest.main()
