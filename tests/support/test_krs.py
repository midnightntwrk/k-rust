"""Contract tests for KRS build and invocation orchestration."""

from __future__ import annotations

from pathlib import Path
import unittest
from unittest.mock import patch

from support import GateError, ROOT
from support import krs


class BuildTests(unittest.TestCase):
    def test_default_target_and_environment(self) -> None:
        binary = ROOT / "target/debug/krs"
        with (
            patch.object(krs.tools, "z3_environment", return_value={"LIBRARY_PATH": "z3"}),
            patch.object(krs.tools, "workspace_debug_binary", return_value=binary),
            patch.object(krs.process, "run") as runner,
            patch.object(Path, "is_file", return_value=True),
        ):
            self.assertEqual(krs.build({"CARGO_NET_OFFLINE": "true"}), binary)
        runner.assert_called_once_with(
            ["cargo", "+stable", "build", "--locked", "-p", "krs-cli", "--bin", "krs"],
            cwd=ROOT,
            environment={"LIBRARY_PATH": "z3", "CARGO_NET_OFFLINE": "true"},
            timeout=600,
        )

    def test_explicit_target_wins_and_missing_binary_fails(self) -> None:
        target = Path("/temporary/cli-target")
        with (
            patch.object(krs.tools, "z3_environment", return_value={"LIBRARY_PATH": "z3"}),
            patch.object(krs.process, "run") as runner,
            patch.object(Path, "is_file", side_effect=(True, False)),
        ):
            self.assertEqual(krs.build(target=target), target / "debug/krs")
            with self.assertRaisesRegex(GateError, "did not produce"):
                krs.build({"LIBRARY_PATH": "caller", "CARGO_TARGET_DIR": "ignored"}, target=target, timeout=27)
        self.assertEqual(
            runner.call_args.kwargs["environment"],
            {"LIBRARY_PATH": "caller", "CARGO_TARGET_DIR": str(target)},
        )
        self.assertEqual(runner.call_args.kwargs["timeout"], 27)

    def test_caller_target_directory_is_honored(self) -> None:
        with (
            patch.object(krs.tools, "z3_environment", return_value={}),
            patch.object(krs.process, "run") as runner,
            patch.object(Path, "is_file", return_value=True),
        ):
            self.assertEqual(
                krs.build({"CARGO_TARGET_DIR": "/temporary/caller"}),
                Path("/temporary/caller/debug/krs"),
            )
        self.assertEqual(runner.call_args.kwargs["environment"], {"CARGO_TARGET_DIR": "/temporary/caller"})

    def test_explicit_target_returns_its_debug_binary(self) -> None:
        target = Path("/temporary/cli-target")
        with (
            patch.object(krs.tools, "z3_environment", return_value={}),
            patch.object(krs.process, "run"),
            patch.object(Path, "is_file", return_value=True),
        ):
            self.assertEqual(krs.build(target=target), target / "debug/krs")


class InvocationTests(unittest.TestCase):
    def test_argv_order_and_optional_definition(self) -> None:
        invocation = krs.Invocation(Path("/bin/krs"), Path("/src/Cargo.toml"), "fixture", "main")
        self.assertEqual(
            invocation.argv("emit-k", "--output", Path("/out")),
            ["/bin/krs", "emit-k", "--manifest-path", "/src/Cargo.toml", "--package", "fixture", "--definition", "main", "--output", "/out"],
        )
        self.assertEqual(
            krs.Invocation(Path("/bin/krs"), Path("/src/Cargo.toml"), "fixture").argv("check"),
            ["/bin/krs", "check", "--manifest-path", "/src/Cargo.toml", "--package", "fixture"],
        )

    def test_run_delegates(self) -> None:
        invocation = krs.Invocation(Path("/bin/krs"), Path("/src/Cargo.toml"), "fixture")
        with patch.object(krs.process, "run", return_value="result") as runner:
            self.assertEqual(invocation.run("check", timeout=19), "result")
        runner.assert_called_once_with(invocation.argv("check"), timeout=19)


if __name__ == "__main__":
    unittest.main()
