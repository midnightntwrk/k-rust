"""Tests for the standalone Rust package inventory and gate helper."""

from __future__ import annotations

import os
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
RUSTFMT = Path("/var/tmp/package-helper-test-rustfmt")


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
        target = Path("/var/tmp/package-helper-test-target")
        with mock.patch.object(packages, "run") as runner, mock.patch.object(packages, "rustfmt_dir", return_value=RUSTFMT):
            packages.check_packages("imp", krs=KRS, env=environment, target_dir=target)
        commands = [list(call.args[0]) for call in runner.call_args_list]
        authored = [package for package in packages.PACKAGES if package.gate == "imp" and package.kind == "authored"]
        fixtures = [package for package in packages.PACKAGES if package.gate == "imp" and package.kind == "fixture"]
        for package in authored:
            manifest = str(ROOT / package.manifest)
            with self.subTest(manifest=package.manifest):
                self.assertIn([str(KRS), "fmt", "--check", "--manifest-path", manifest], commands)
                self.assertTrue(any(command[2] == "clippy" and manifest in command for command in commands))
                self.assertTrue(any(command[2] == "check" and manifest in command for command in commands))
        for package in fixtures:
            self.assertFalse(any(str(ROOT / package.manifest) in command for command in commands))
        self.assertEqual(environment, {"PACKAGE_TEST_MARKER": "original"})
        for call in runner.call_args_list:
            self.assertEqual(call.kwargs["environment"]["CARGO_TARGET_DIR"], str(target))
            self.assertEqual(call.kwargs["environment"]["PACKAGE_TEST_MARKER"], "original")

    def test_rustfmt_uses_explicit_stable_toolchain(self) -> None:
        with mock.patch.object(packages, "run") as runner, mock.patch.object(packages, "rustfmt_dir", return_value=RUSTFMT):
            packages.check_packages(
                "tour-minimal", krs=KRS, env={}, target_dir=Path("/var/tmp/package-helper-test-target")
            )
        command = list(runner.call_args_list[0].args[0])
        self.assertEqual(command[:4], ["cargo", "+stable", "fmt", "--check"])
        self.assertIn(str(ROOT / "tests/tour-minimal/Cargo.toml"), command)

    def test_krs_fmt_finds_the_working_rustfmt(self) -> None:
        with mock.patch.object(packages, "run") as runner, mock.patch.object(packages, "rustfmt_dir", return_value=RUSTFMT):
            packages.check_packages(
                "tour-minimal", krs=KRS, env={"PATH": "/usr/bin"}, target_dir=Path("/var/tmp/package-helper-test-target")
            )
        krs_fmt = next(call for call in runner.call_args_list if call.args[0][0] == str(KRS))
        self.assertEqual(krs_fmt.kwargs["environment"]["PATH"], os.pathsep.join((str(RUSTFMT), "/usr/bin")))


if __name__ == "__main__":
    unittest.main()
