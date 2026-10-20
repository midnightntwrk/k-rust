"""Tests for the standalone Rust package inventory and gate helper."""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tomllib
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT  # noqa: E402
from support import packages  # noqa: E402

KRS = Path("/var/tmp/package-helper-test-target/debug/krs")
TARGET = Path("/var/tmp/package-helper-test-target")
RUSTFMT_ENVIRONMENT = {"RUSTFMT": "/var/tmp/package-helper-test-toolchain/bin/rustfmt"}


def tracked_files() -> set[str]:
    output = subprocess.check_output(["git", "-C", str(ROOT), "ls-files", "-z"])
    return set(filter(None, output.decode("utf-8").split("\0")))


class PackageTableTests(unittest.TestCase):
    def test_rows_name_tracked_workspaces_locks_and_owner_gates(self) -> None:
        tracked = tracked_files()
        manifests = [package.manifest for package in packages.PACKAGES]
        self.assertEqual(len(manifests), len(set(manifests)))
        for package in packages.PACKAGES:
            with self.subTest(manifest=package.manifest):
                self.assertIn(package.kind, {"authored", "fixture"})
                self.assertIn(package.manifest, tracked)
                self.assertIn(str(Path(package.manifest).with_name("Cargo.lock")), tracked)
                self.assertIn(f"tests/{package.gate}/verify.py", tracked)
                cargo = tomllib.loads((ROOT / package.manifest).read_text(encoding="utf-8"))
                self.assertIsInstance(cargo.get("workspace"), dict)


class PackageHelperTests(unittest.TestCase):
    def test_checks_only_authored_rows_for_the_owning_gate(self) -> None:
        environment = {"PACKAGE_TEST_MARKER": "original"}
        with mock.patch.object(packages, "run") as runner, mock.patch.object(packages, "rustfmt_environment", return_value=RUSTFMT_ENVIRONMENT):
            packages.check_packages("imp", krs=KRS, env=environment)
        commands = [list(call.args[0]) for call in runner.call_args_list]
        authored = [package for package in packages.PACKAGES if package.gate == "imp" and package.kind == "authored"]
        fixtures = [package for package in packages.PACKAGES if package.gate == "imp" and package.kind == "fixture"]
        for package in authored:
            manifest = str(ROOT / package.manifest)
            with self.subTest(manifest=package.manifest):
                self.assertIn([str(KRS), "fmt", "--check", "--manifest-path", manifest], commands)
                self.assertTrue(any(command[2] == "fmt" and manifest in command for command in commands if command[0] == "cargo"))
        for package in fixtures:
            self.assertFalse(any(str(ROOT / package.manifest) in command for command in commands))
        self.assertEqual(environment, {"PACKAGE_TEST_MARKER": "original"})
        for call in runner.call_args_list:
            self.assertEqual(call.kwargs["environment"]["PACKAGE_TEST_MARKER"], "original")

    def test_gate_checks_format_only(self) -> None:
        with mock.patch.object(packages, "run") as runner, mock.patch.object(packages, "rustfmt_environment", return_value=RUSTFMT_ENVIRONMENT):
            packages.check_packages("imp", krs=KRS, env={})
        commands = [list(call.args[0]) for call in runner.call_args_list]
        self.assertTrue(commands)
        for command in commands:
            with self.subTest(command=command[:3]):
                self.assertIn("fmt", command[:3])
                self.assertIn("--check", command)

    def test_rustfmt_uses_explicit_stable_toolchain(self) -> None:
        with mock.patch.object(packages, "run") as runner, mock.patch.object(packages, "rustfmt_environment", return_value=RUSTFMT_ENVIRONMENT):
            packages.check_packages("tour-minimal", krs=KRS, env={})
        command = list(runner.call_args_list[0].args[0])
        self.assertEqual(command[:4], ["cargo", "+stable", "fmt", "--check"])
        self.assertIn(str(ROOT / "tests/tour-minimal/Cargo.toml"), command)

    def test_krs_fmt_finds_the_working_rustfmt(self) -> None:
        with mock.patch.object(packages, "run") as runner, mock.patch.object(packages, "rustfmt_environment", return_value=RUSTFMT_ENVIRONMENT):
            packages.check_packages("tour-minimal", krs=KRS, env={"PATH": "/usr/bin"})
        krs_fmt = next(call for call in runner.call_args_list if call.args[0][0] == str(KRS))
        self.assertEqual(krs_fmt.kwargs["environment"]["RUSTFMT"], RUSTFMT_ENVIRONMENT["RUSTFMT"])

    def test_no_command_has_an_edited_path_and_cargo_has_no_rustfmt_override(self) -> None:
        with mock.patch.object(packages, "run") as runner, mock.patch.object(packages, "rustfmt_environment", return_value=RUSTFMT_ENVIRONMENT):
            packages.check_packages("tour-minimal", krs=KRS, env={"PATH": "/usr/bin"})
        for call in runner.call_args_list:
            with self.subTest(command=call.args[0][:3]):
                self.assertEqual(call.kwargs["environment"]["PATH"], "/usr/bin")
                if call.args[0][0] == "cargo":
                    self.assertNotIn("RUSTFMT", call.kwargs["environment"])


class PackageLintTests(unittest.TestCase):
    def test_lints_and_msrv_checks_every_authored_row_in_the_given_target(self) -> None:
        environment = {"PACKAGE_TEST_MARKER": "original"}
        with mock.patch.object(packages, "run") as runner, mock.patch.object(packages, "msrv", return_value="1.99.0"):
            checked = packages.lint_packages(env=environment, target_dir=TARGET)
        authored = [package for package in packages.PACKAGES if package.kind == "authored"]
        self.assertEqual(checked, authored)
        commands = [list(call.args[0]) for call in runner.call_args_list]
        for package in packages.PACKAGES:
            manifest = str(ROOT / package.manifest)
            with self.subTest(manifest=package.manifest):
                clippy = [command for command in commands if command[2] == "clippy" and manifest in command]
                check = [command for command in commands if command[2] == "check" and manifest in command]
                if package.kind == "authored":
                    self.assertEqual(len(clippy), 1)
                    self.assertEqual(clippy[0][:2], ["cargo", "+stable"])
                    self.assertEqual(clippy[0][-3:], ["--", "-D", "warnings"])
                    self.assertEqual(len(check), 1)
                    self.assertEqual(check[0][:2], ["cargo", "+1.99.0"])
                    self.assertIn("--all-targets", check[0])
                else:
                    self.assertEqual(clippy + check, [])
        self.assertEqual(environment, {"PACKAGE_TEST_MARKER": "original"})
        for call in runner.call_args_list:
            self.assertEqual(call.kwargs["environment"]["CARGO_TARGET_DIR"], str(TARGET))
            self.assertEqual(call.kwargs["environment"]["PACKAGE_TEST_MARKER"], "original")


if __name__ == "__main__":
    unittest.main()
