"""Fast fail-closed contracts for the M4 root release gate."""

from __future__ import annotations

import subprocess
import unittest

import verify
from support.hashing import relevant_untracked
from support.pins import load_json


class InputPinTests(unittest.TestCase):
    def test_ledger_pins_external_inputs_but_no_krs_source(self) -> None:
        pins = load_json(verify.PINS_PATH)
        self.assertNotIn("source_sha256", pins)
        external = pins["external_sha256"]
        self.assertTrue(external)
        for relative in external:
            self.assertTrue(relative.startswith("../inspirations/"), relative)

    def test_ledger_does_not_repeat_krs_lock(self) -> None:
        pins = load_json(verify.PINS_PATH)
        for key in ("schemas", "toolchain_compatibility"):
            self.assertNotIn(key, pins)
        self.assertEqual(set(pins["revisions"]), {"imp"})

    def test_only_python_cache_is_ignored_in_external_source_tree(self) -> None:
        self.assertEqual(
            relevant_untracked(
                [
                    "pyk/src/pyk/__pycache__/cli.cpython-313.pyc",
                    "pyk/src/pyk/injected.py",
                    "pyk/src/pyk/data.json",
                ]
            ),
            ["pyk/src/pyk/data.json", "pyk/src/pyk/injected.py"],
        )


class ExactSummaryTests(unittest.TestCase):
    def process(self, stdout: str, stderr: str = "") -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(["probe"], 0, stdout, stderr)

    def test_exact_summary_accepts_only_the_complete_line(self) -> None:
        verify.require_exact_summary(self.process("PASS exact\n"), "PASS exact\n", "probe")
        for process in (
            self.process("PASS exact"),
            self.process("PASS exact\ntrailing\n"),
            self.process("PASS exact\n", "warning\n"),
        ):
            with self.assertRaisesRegex(verify.GateError, "exact PASS summary"):
                verify.require_exact_summary(process, "PASS exact\n", "probe")


if __name__ == "__main__":
    unittest.main()
