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
from support import checkouts, hashing, kdefinition, lock, lsp, pins, process, tools  # noqa: E402


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
        def kore(directory: Path, variable: str, k_install: str) -> str:
            return (
                f'[source("{directory / "semantics.k"}")]\n'
                f'[Source("Source({k_install}/include/kframework/builtin/domains.md)")]\n'
                f"\\exists{{R}} ({variable}:SortInt{{}}, f({variable}:SortInt{{}}) \\bottom{{R}}())\n"
            )

        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            digests = []
            for directory, variable, k_install in (
                (Path(first), "Var'Unds'Gen1", "/nix/store/aaaa-k-7.1.337"),
                (Path(second), "Var'Unds'Gen7", "/opt/k"),
            ):
                (directory / "definition.kore").write_text(kore(directory, variable, k_install))
                digests.append(
                    kdefinition.normalized_kore_sha256(
                        directory / "definition.kore", directory / "semantics.k"
                    )
                )
            self.assertEqual(digests[0], digests[1])


    def test_parse_kore_pattern_yields_kore_json(self) -> None:
        text = (
            "Lbl'-LT-'k'-GT-'{}(/* InternalList: */ Lbl'Unds'List'Unds'{}(LblListItem{}(inj{SortInt{}, SortKItem{}}"
            '(\\dv{SortInt{}}("-7"))), Lbl\'Stop\'List{}()))\n'
        )
        int_sort = {"tag": "SortApp", "name": "SortInt", "args": []}
        self.assertEqual(
            kdefinition.parse_kore_pattern(text),
            {
                "tag": "App", "name": "Lbl'-LT-'k'-GT-'", "sorts": [], "args": [
                    {"tag": "App", "name": "Lbl'Unds'List'Unds'", "sorts": [], "args": [
                        {"tag": "App", "name": "LblListItem", "sorts": [], "args": [
                            {"tag": "App", "name": "inj", "sorts": [
                                int_sort, {"tag": "SortApp", "name": "SortKItem", "args": []},
                            ], "args": [{"tag": "DV", "sort": int_sort, "value": "-7"}]},
                        ]},
                        {"tag": "App", "name": "Lbl'Stop'List", "sorts": [], "args": []},
                    ]},
                ],
            },
        )

    def test_parse_kore_pattern_decodes_string_escapes_and_rejects_connectives(self) -> None:
        pattern = kdefinition.parse_kore_pattern('\\dv{SortString{}}("a\\"b\\\\\\x41\\u00e9")')
        self.assertEqual(pattern["value"], 'a"b\\A\u00e9')
        with self.assertRaisesRegex(GateError, "unsupported KORE connective"):
            kdefinition.parse_kore_pattern("\\and{SortInt{}}(a{}(), b{}())")
        with self.assertRaisesRegex(GateError, "trailing KORE text"):
            kdefinition.parse_kore_pattern("a{}() b{}()")


class LedgerTests(unittest.TestCase):
    TOML = (
        'schema = 1\n'
        'corpus_sha256 = "input"\n'
        'expansion_sha256 = "old"\n'
        '\n'
        '[checkout]\n'
        'commit = "abc"\n'
        '\n'
        '[artifact_sha256]\n'
        '"definition.k" = "old-k"\n'
        '"sources.json" = "old-s"\n'
    )

    def ledger(self, directory: str, *, record: bool, suffix: str = ".toml") -> pins.Ledger:
        path = Path(directory) / f"pins{suffix}"
        if not path.exists():
            path.write_text(self.TOML, encoding="utf-8")
        return pins.Ledger(path, record=record)

    def test_toml_writer_round_trips_the_ledger_spelling(self) -> None:
        import tomllib

        self.assertEqual(pins.dump_toml(tomllib.loads(self.TOML)), self.TOML)

    def test_check_mode_compares_and_never_writes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            ledger = self.ledger(temporary, record=False)
            ledger.expect("expansion_sha256", "old")
            ledger.expect(("artifact_sha256", "definition.k"), "old-k")
            with self.assertRaisesRegex(GateError, "expansion_sha256 was observed twice"):
                ledger.expect("expansion_sha256", "new")
            with self.assertRaisesRegex(GateError, "artifact_sha256.sources.json differs from its pin"):
                ledger.expect(("artifact_sha256", "sources.json"), "new-s")
            with self.assertRaisesRegex(GateError, "has no pin missing; run the gate with --record"):
                ledger.expect("missing", "value")
            with self.assertRaisesRegex(GateError, "only a record-mode ledger"):
                ledger.write()
            ledger.finish("fixture")
            self.assertEqual(ledger.path.read_text(encoding="utf-8"), self.TOML)

    def test_record_mode_rewrites_only_observed_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            ledger = self.ledger(temporary, record=True)
            ledger.expect("expansion_sha256", "new")
            ledger.expect(("artifact_sha256", "definition.k"), "old-k")
            with self.assertRaisesRegex(GateError, "observed twice"):
                ledger.expect("expansion_sha256", "other")
            self.assertEqual(ledger.write(), ["expansion_sha256"])
            text = ledger.path.read_text(encoding="utf-8")
            self.assertEqual(text, self.TOML.replace('"old"', '"new"'))
            reloaded = pins.Ledger(ledger.path)
            reloaded.expect("expansion_sha256", "new")
            self.assertEqual(reloaded.get("corpus_sha256"), "input")
            self.assertEqual(reloaded.table("checkout"), {"commit": "abc"})

    def test_record_mode_writes_nested_json_tables(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "pins.json"
            path.write_text('{\n  "schema": 1,\n  "behavior": {"expected": {"count": 1}}\n}\n')
            ledger = pins.Ledger(path, record=True)
            ledger.expect(("behavior", "expected"), {"count": 2})
            ledger.expect(("native", "definition.kore"), "digest")
            self.assertEqual(sorted(ledger.write()), ["behavior.expected", "native.definition.kore"])
            self.assertEqual(
                pins.load_json(path),
                {"schema": 1, "behavior": {"expected": {"count": 2}}, "native": {"definition.kore": "digest"}},
            )


class LockTests(unittest.TestCase):
    def test_krs_lock_supplies_the_toolchain_pins(self) -> None:
        self.assertRegex(lock.k_version(), r"^\d+\.\d+\.\d+$")
        self.assertRegex(lock.msrv(), r"^\d+\.\d+\.\d+$")
        self.assertRegex(lock.z3_version(), r"^\d+\.\d+\.\d+$")
        lock.verify_schema_constants()

    def test_stable_rustc_at_or_above_the_msrv(self) -> None:
        with mock.patch.object(lock, "msrv", return_value="1.88.0"):
            lock.require_stable_at_least_msrv("rustc 1.88.0 (6b00bc388 2025-06-23)")
            lock.require_stable_at_least_msrv("rustc 1.98.0 (88d9e12ae 2026-08-18)")
            with self.assertRaisesRegex(GateError, "older than the Krs.lock MSRV"):
                lock.require_stable_at_least_msrv("rustc 1.87.0 (17067e9ac 2025-05-09)")
            with self.assertRaisesRegex(GateError, "not a stable rustc"):
                lock.require_stable_at_least_msrv("rustc 1.99.0-nightly (0123456 2026-09-01)")
            with self.assertRaisesRegex(GateError, "cannot parse"):
                lock.require_stable_at_least_msrv("cargo 1.98.0")


class LspTests(unittest.TestCase):
    def test_position_counts_utf16_units_and_lands_inside_the_needle(self) -> None:
        lines = ["", "  é let x = Foo(y);"]
        self.assertEqual(lsp.position(lines, "Foo(y)", "y"), {"line": 1, "character": 17})
        with self.assertRaisesRegex(GateError, "probe fragment is absent"):
            lsp.position(lines, "Bar", "B")


if __name__ == "__main__":
    unittest.main()
