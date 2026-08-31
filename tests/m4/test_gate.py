"""Fast fail-closed contracts for the M4 root release gate."""

from __future__ import annotations

import subprocess
from pathlib import Path
import unittest

import verify


class SourceLedgerTests(unittest.TestCase):
    def test_build_and_test_inputs_are_ledger_sources(self) -> None:
        self.assertTrue(verify.is_crate_source(Path("src/lib.rs")))
        self.assertTrue(verify.is_crate_source(Path("tests/golden/value.json")))
        self.assertTrue(verify.is_crate_source(Path("tests/lsp_probe.py")))
        self.assertTrue(verify.is_crate_source(Path("Cargo.lock")))
        self.assertTrue(verify.is_crate_source(Path("tests/fixture.custom")))
        self.assertFalse(verify.is_crate_source(Path("target/output")))
        self.assertFalse(verify.is_crate_source(Path("__pycache__/module.py")))
        self.assertFalse(verify.is_crate_source(Path("module.pyc")))

    def test_complete_path_set_includes_non_rust_inputs_and_external_manifest(self) -> None:
        paths = verify.expected_source_ledger_paths()
        self.assertIn("crates/krs-ir/tests/golden/empty_bundle.json", paths)
        self.assertIn("crates/krs-macros/tests/lsp_probe.py", paths)
        self.assertIn("crates/krs-macros/tests/fixtures/negative/Cargo.lock", paths)
        self.assertIn("tests/m4/rust-definition/tools/lsp_probe.py", paths)
        self.assertIn("tests/m4/goldens/imp.identities.txt", paths)
        self.assertIn("../inspirations/midnightntwrk/k-rust-krs-main/Cargo.toml", paths)

    def test_only_python_cache_is_ignored_in_external_source_tree(self) -> None:
        self.assertEqual(
            verify.relevant_untracked(
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
