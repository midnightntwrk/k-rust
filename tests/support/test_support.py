"""Unit tests for the shared gate support package."""

from __future__ import annotations

import os
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from support import checkouts, hashing, kdefinition, lsp, pins, process, tools  # noqa: E402


def write_executable(path: Path, body: str) -> Path:
    path.write_text(f"#!/bin/sh\n{body}\n", encoding="utf-8")
    path.chmod(0o755)
    return path


class ProcessTests(unittest.TestCase):
    def test_success_captures_text_in_root_with_c_locale(self) -> None:
        result = process.run(["sh", "-c", 'pwd; printf "%s" "$LC_ALL"'])
        self.assertEqual(result.stdout, f"{ROOT}\nC")

    def test_environment_layers_over_the_base(self) -> None:
        result = process.run(
            ["sh", "-c", 'printf "%s/%s" "$LANG" "$KRS_SUPPORT_TEST"'],
            environment={"LANG": "en_US.UTF-8", "KRS_SUPPORT_TEST": "set"},
        )
        self.assertEqual(result.stdout, "en_US.UTF-8/set")

    def test_failure_raises_with_output_unless_unchecked(self) -> None:
        with self.assertRaisesRegex(GateError, r"command failed \(3\): sh -c .*\nboom"):
            process.run(["sh", "-c", "echo boom >&2; exit 3"])
        result = process.run(["sh", "-c", "exit 3"], check=False)
        self.assertEqual(result.returncode, 3)

    def test_bytes_and_input(self) -> None:
        result = process.run(["cat"], text=False, input=b"\xff\x00")
        self.assertEqual(result.stdout, b"\xff\x00")

    def test_timeout_terminates_the_process_group(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            marker = Path(temporary) / "survived"
            script = f"(sleep 2; touch {marker}) & sleep 30"
            started = time.monotonic()
            with self.assertRaisesRegex(GateError, "timed out after 0.5s"):
                process.run(["sh", "-c", script], timeout=0.5)
            self.assertLess(time.monotonic() - started, 10)
            time.sleep(2.5)
            self.assertFalse(marker.exists())

    def test_sigterm_to_the_verifier_terminates_the_running_command(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            marker = Path(temporary) / "survived"
            verifier = (
                "import sys; sys.path.insert(0, sys.argv[1]); from support.process import run; "
                f"run(['sh', '-c', 'sleep 2; touch {marker}'])"
            )
            child = process.subprocess.Popen([sys.executable, "-c", verifier, str(ROOT / "tests")])
            time.sleep(1)
            child.terminate()
            self.assertEqual(child.wait(timeout=10), 128 + process.signal.SIGTERM)
            time.sleep(2)
            self.assertFalse(marker.exists())

    def test_compact_keeps_both_ends(self) -> None:
        completed = process.subprocess.CompletedProcess([], 1, "a" * 50 + "TAIL", b"")
        output = process.compact(completed, limit=20)
        self.assertTrue(output.startswith("aaaaa\n…\n"))
        self.assertTrue(output.endswith("TAIL"))


class HashingTests(unittest.TestCase):
    def test_canonical_json_and_digests(self) -> None:
        self.assertEqual(hashing.canonical_json({"b": [1, "é"], "a": None}), '{"a":null,"b":[1,"é"]}')
        self.assertEqual(
            hashing.json_sha256({}), "44136fa355b3678a1146ad16f7e8649e94fb4fc21fe77e8310c060f61caaff8a"
        )
        self.assertEqual(hashing.sha256_text("é"), hashing.sha256_bytes("é".encode()))

    def test_missing_file_is_a_gate_error(self) -> None:
        with self.assertRaisesRegex(GateError, "required file is missing"):
            hashing.sha256_file(ROOT / "does-not-exist")

    def test_exact_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            first, second = Path(temporary, "a"), Path(temporary, "b")
            for directory in (first, second):
                directory.mkdir()
                (directory / "x").write_text("same")
            self.assertEqual(
                hashing.exact_directory(first, second, ["x"]), {"x": hashing.sha256_bytes(b"same")}
            )
            (second / "x").write_text("other")
            with self.assertRaisesRegex(GateError, "differs byte-for-byte: x"):
                hashing.exact_directory(first, second, ["x"])
            (second / "y").write_text("extra")
            with self.assertRaisesRegex(GateError, "artifact set differs"):
                hashing.exact_directory(first, second, ["x"])

    def test_tracked_tree_digest_and_untracked_rejection(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            checkout = Path(temporary)
            (checkout / "tree").mkdir()
            (checkout / "tree/a.txt").write_text("a")
            process.run(["git", "init", "-q"], cwd=checkout)
            process.run(["git", "add", "tree"], cwd=checkout)
            digest = hashing.tracked_tree_sha256(checkout, "tree")
            (checkout / "tree/__pycache__").mkdir()
            (checkout / "tree/__pycache__/a.pyc").write_bytes(b"")
            self.assertEqual(hashing.tracked_tree_sha256(checkout, "tree", reject_untracked=True), digest)
            (checkout / "tree/b.txt").write_text("b")
            with self.assertRaisesRegex(GateError, "untracked files"):
                hashing.tracked_tree_sha256(checkout, "tree", reject_untracked=True)
            with self.assertRaisesRegex(GateError, "tracked tree is empty"):
                hashing.tracked_tree_sha256(checkout, "absent")


class PinTests(unittest.TestCase):
    def test_loaders_and_table(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            json_path = Path(temporary, "pins.json")
            json_path.write_text('{"a": 1}')
            self.assertEqual(pins.load_json(json_path), {"a": 1})
            json_path.write_text("[1]")
            with self.assertRaisesRegex(GateError, "must contain one JSON object"):
                pins.load_json(json_path)
            toml_path = Path(temporary, "pins.toml")
            toml_path.write_text('[k]\nversion = "1"\n')
            self.assertEqual(pins.table(pins.load_toml(toml_path)["k"], "k"), {"version": "1"})
            toml_path.write_text("not toml =")
            with self.assertRaisesRegex(GateError, "cannot load"):
                pins.load_toml(toml_path)
        with self.assertRaisesRegex(GateError, "pins.k must be a table"):
            pins.table([], "pins.k")


class ToolTests(unittest.TestCase):
    def test_z3_library_accepts_the_directory_or_its_package_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            library = Path(temporary, "lib")
            library.mkdir()
            (library / "libz3.so").write_bytes(b"")
            for configured in (library, Path(temporary)):
                with mock.patch.dict(os.environ, {"KRS_Z3_LIB": os.fspath(configured)}):
                    self.assertEqual(tools.z3_library_dir(), library)
            with mock.patch.dict(
                os.environ, {"KRS_Z3_LIB": os.fspath(library), "LIBRARY_PATH": "/old"}
            ):
                environment = tools.z3_environment()
            self.assertEqual(environment["LIBRARY_PATH"], f"{library}{os.pathsep}/old")

    def test_k_tools_prefer_krs_k_bin_and_check_the_version(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            write_executable(Path(temporary, "kompile"), 'echo "K version: v7.1.337"')
            write_executable(Path(temporary, "krun"), 'echo "K version: v7.0.0"')
            with mock.patch.dict(os.environ, {"KRS_K_BIN": temporary}):
                self.assertEqual(tools.k_tool("kompile", "7.1.337"), f"{temporary}/kompile")
                with self.assertRaisesRegex(GateError, "krun is not pinned to K v7.1.337"):
                    tools.k_tool("krun", "7.1.337")
                self.assertIsNone(tools.find_k_tool("kast"))
                with self.assertRaisesRegex(GateError, "required K tool 'kast' is unavailable"):
                    tools.k_executable("kast")

    def test_rustfmt_override(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            rustfmt = write_executable(Path(temporary, "rustfmt"), "echo rustfmt 1.0")
            with mock.patch.dict(os.environ, {"KRS_RUSTFMT": os.fspath(rustfmt)}):
                self.assertEqual(tools.rustfmt_dir(), Path(temporary))


class CheckoutTests(unittest.TestCase):
    def test_revision_and_cleanliness(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            checkout = Path(temporary)
            (checkout / "a").write_text("a")
            identity = {
                "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
                "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid",
            }
            process.run(["git", "init", "-q"], cwd=checkout)
            process.run(["git", "add", "a"], cwd=checkout)
            process.run(["git", "commit", "-qm", "a"], cwd=checkout, environment=identity)
            revision = checkouts.git_revision(checkout)
            checkouts.verify_checkout(checkout, revision, label="fixture")
            with self.assertRaisesRegex(GateError, "fixture checkout revision differs"):
                checkouts.verify_checkout(checkout, "0" * 40, label="fixture")
            (checkout / "a").write_text("changed")
            with self.assertRaisesRegex(GateError, "fixture checkout is dirty"):
                checkouts.verify_checkout(checkout, revision, label="fixture")
            checkouts.verify_checkout(checkout, revision, label="fixture", clean=False)


class KDefinitionTests(unittest.TestCase):
    SOURCE = (
        "module M\n"
        "  syntax A ::= \"a\"\n"
        "  claim [one]:\n"
        "    <k> a => a </k>\n"
        "  rule [r]: a => a\n"
        "  claim [two]: <k> a </k>\n"
        "endmodule\n"
    )

    def test_split_claims_preserves_every_other_byte(self) -> None:
        value, labels, claims = kdefinition.split_claims(self.SOURCE, 2)
        self.assertEqual(value, 'module M\n  syntax A ::= "a"\n  rule [r]: a => a\nendmodule\n')
        self.assertEqual(labels, ["one", "two"])
        self.assertEqual(claims, "  claim [one]:\n    <k> a => a </k>\n  claim [two]: <k> a </k>\n")

    def test_split_claims_counts_distinct_labels(self) -> None:
        with self.assertRaisesRegex(GateError, "expected 1 emitted claims"):
            kdefinition.split_claims(self.SOURCE, 1)
        duplicated = self.SOURCE.replace("[two]", "[one]")
        with self.assertRaisesRegex(GateError, "distinct labels"):
            kdefinition.split_claims(duplicated, 2)

    def test_normalized_kore_is_location_and_binder_independent(self) -> None:
        def kore(directory: Path, variable: str) -> str:
            return (
                f'[source("{directory / "semantics.k"}")]\n'
                f"\\exists{{R}} ({variable}:SortInt{{}}, f({variable}:SortInt{{}}) \\bottom{{R}}())\n"
            )

        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            digests = []
            for directory, variable in ((Path(first), "Var'Unds'Gen1"), (Path(second), "Var'Unds'Gen7")):
                (directory / "definition.kore").write_text(kore(directory, variable))
                digests.append(
                    kdefinition.normalized_kore_sha256(
                        directory / "definition.kore", directory / "semantics.k"
                    )
                )
            self.assertEqual(digests[0], digests[1])


class LspTests(unittest.TestCase):
    def test_position_counts_utf16_units_and_lands_inside_the_needle(self) -> None:
        lines = ["", "  é let x = Foo(y);"]
        self.assertEqual(lsp.position(lines, "Foo(y)", "y"), {"line": 1, "character": 17})
        with self.assertRaisesRegex(GateError, "probe fragment is absent"):
            lsp.position(lines, "Bar", "B")


if __name__ == "__main__":
    unittest.main()
