"""Fast fail-closed contracts for the IMP root release gate."""

from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

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


class PhaseDependencyTests(unittest.TestCase):
    def test_audit_skips_consumers_after_rust_failure(self) -> None:
        stdout, stderr = io.StringIO(), io.StringIO()
        with (
            tempfile.TemporaryDirectory() as target,
            patch("sys.argv", ["verify.py", "--audit-all", "--target-dir", target]),
            patch.object(verify, "phase_preflight", return_value="ready"),
            patch.object(verify, "phase_rust", side_effect=verify.GateError("rust failed")),
            patch.object(verify, "phase_artifacts") as artifacts,
            patch.object(verify, "phase_proofs", return_value="proofs passed") as proofs,
            redirect_stdout(stdout),
            redirect_stderr(stderr),
        ):
            self.assertEqual(verify.main(), 1)
        artifacts.assert_not_called()
        proofs.assert_called_once()
        self.assertIn("SKIP deterministic-artifacts: requires rust-and-lsp", stdout.getvalue())
        self.assertIn("SKIP source-definition: requires deterministic-artifacts", stdout.getvalue())
        self.assertIn("PASS IMP.7 bounded-proofs", stdout.getvalue())
        self.assertIn("FAIL IMP.2 rust-and-lsp: rust failed", stderr.getvalue())

    def test_audit_runs_independent_phases_after_source_failure(self) -> None:
        stdout, stderr = io.StringIO(), io.StringIO()
        build = verify.RustBuild(Path("krs"))
        artifacts_result = verify.Artifacts(Path("artifacts"), {}, Path("native"))
        with (
            tempfile.TemporaryDirectory() as target,
            patch("sys.argv", ["verify.py", "--audit-all", "--target-dir", target]),
            patch.object(verify, "phase_preflight", return_value="ready"),
            patch.object(verify, "phase_rust", return_value=build),
            patch.object(verify, "phase_artifacts", return_value=artifacts_result),
            patch.object(verify, "phase_source_definition", side_effect=verify.GateError("source failed")),
            patch.object(verify, "phase_native") as native,
            patch.object(verify, "phase_behavior") as behavior,
            patch.object(verify, "phase_proofs", return_value="proofs passed") as proofs,
            patch.object(verify, "phase_compatibility", return_value="compatible") as compatibility,
            redirect_stdout(stdout),
            redirect_stderr(stderr),
        ):
            self.assertEqual(verify.main(), 1)
        native.assert_not_called()
        behavior.assert_not_called()
        proofs.assert_called_once()
        compatibility.assert_called_once()
        self.assertIn("SKIP native-kore: requires source-definition", stdout.getvalue())
        self.assertIn("SKIP parser-execution-search: requires source-definition", stdout.getvalue())
        self.assertIn("PASS IMP.8 compatibility-reproduction", stdout.getvalue())
        self.assertIn("FAIL IMP.4 source-definition: source failed", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
