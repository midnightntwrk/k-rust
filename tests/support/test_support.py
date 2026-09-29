"""Unit tests for the shared gate support package."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from support import checkouts, hashing, kdefinition, lock, lsp, parallel, pins, process, semantics, tools  # noqa: E402


class RouteComparisonTests(unittest.TestCase):
    def test_reports_case_and_first_differing_key(self) -> None:
        with self.assertRaisesRegex(GateError, r"KEVM case one differs at gas: native='3', Java='4'"):
            semantics.compare_routes(
                "KEVM", [{"id": "one", "gas": "3", "pc": "2"}],
                [{"id": "one", "gas": "4", "pc": "9"}], {},
            )

    def test_rejects_skipped_id_absent_from_corpus(self) -> None:
        with self.assertRaisesRegex(GateError, r"skipped id is absent from corpus: \['missing'\]"):
            semantics.compare_routes("KEVM", [{"id": "one"}], [], {"missing": "gap"})

    def test_requires_every_unskipped_case(self) -> None:
        with self.assertRaisesRegex(GateError, "did not compare cases"):
            semantics.compare_routes("KMIR", [{"id": "one"}], [], {})


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


class ParallelTests(unittest.TestCase):
    def test_worker_count_bounds(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=True):
            self.assertEqual(parallel.worker_count("KRS_SUPPORT_WORKERS", 3), 3)
        for raw, expected in (("1", 1), ("32", 32)):
            with mock.patch.dict(os.environ, {"KRS_SUPPORT_WORKERS": raw}):
                self.assertEqual(parallel.worker_count("KRS_SUPPORT_WORKERS", 3), expected)
        for raw in ("0", "33", "many"):
            with mock.patch.dict(os.environ, {"KRS_SUPPORT_WORKERS": raw}):
                with self.assertRaisesRegex(GateError, "KRS_SUPPORT_WORKERS must be"):
                    parallel.worker_count("KRS_SUPPORT_WORKERS", 3)

    def test_ordered_map_keeps_input_order(self) -> None:
        def slow_first(value: int) -> int:
            time.sleep(0.01 * (5 - value))
            return value * value

        for workers in (1, 4):
            self.assertEqual(parallel.ordered_map(slow_first, range(5), workers), [0, 1, 4, 9, 16])

    def test_earliest_failure_in_input_order_is_reported(self) -> None:
        def fail(value: int) -> int:
            # The later failure finishes first when calls run concurrently.
            time.sleep(0.05 if value == 1 else 0)
            if value in (1, 3):
                raise GateError(f"failed {value}")
            return value

        for workers in (1, 4):
            with self.assertRaisesRegex(GateError, "failed 1"):
                parallel.ordered_map(fail, range(5), workers)
            outcomes = parallel.settle_all([lambda value=value: fail(value) for value in range(5)], workers)
            self.assertEqual([outcome.error is None for outcome in outcomes], [True, False, True, False, True])
            self.assertEqual(outcomes[2].get(), 2)
            with self.assertRaisesRegex(GateError, "failed 3"):
                outcomes[3].get()


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
    def test_checkout_scratch_is_stable_and_distinct_by_repository_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            scratch = Path(temporary) / "scratch"
            roots = [Path(temporary) / name / "repo" for name in ("a", "b")]
            for root in roots:
                root.mkdir(parents=True)
            with mock.patch.dict(os.environ, {"KRS_GATE_SCRATCH": os.fspath(scratch)}):
                paths = []
                for root in roots:
                    with mock.patch.object(tools, "ROOT", root):
                        first = tools.checkout_scratch()
                        self.assertEqual(tools.checkout_scratch(), first)
                        self.assertTrue(first.is_dir())
                        paths.append(first)
            self.assertNotEqual(*paths)

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

    def test_k_version_match_requires_success_and_the_pinned_version(self) -> None:
        self.assertTrue(tools.k_version_matches(
            subprocess.CompletedProcess([], 0, "K version: v7.1.337", ""), "7.1.337"
        ))
        self.assertFalse(tools.k_version_matches(
            subprocess.CompletedProcess([], 1, "K version: v7.1.337", ""), "7.1.337"
        ))
        self.assertFalse(tools.k_version_matches(
            subprocess.CompletedProcess([], 0, "K version: v7.0.0", ""), "7.1.337"
        ))

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
    CLAIMS = "  claim [one]:\n    <k> a => a </k>\n  claim [two]: <k> a </k>\n"
    SPEC = f'requires "definition.k"\n\nmodule M-SPEC\n  imports M\n\n{CLAIMS}endmodule\n'

    def emitted(self, spec: str) -> tuple[list[str], str]:
        with tempfile.TemporaryDirectory() as directory:
            Path(directory, "spec.k").write_text(spec, encoding="utf-8")
            return kdefinition.emitted_claims(Path(directory), "M", 2)

    def test_emitted_claims_returns_labels_and_sentences(self) -> None:
        self.assertEqual(self.emitted(self.SPEC), (["one", "two"], self.CLAIMS))

    def test_emitted_claims_counts_distinct_labels(self) -> None:
        with self.assertRaisesRegex(GateError, "distinct labels"):
            self.emitted(self.SPEC.replace("[two]", "[one]"))

    def test_emitted_claims_requires_the_exact_frame(self) -> None:
        with self.assertRaisesRegex(GateError, "exact M-SPEC frame"):
            self.emitted(self.SPEC.replace("imports M", "imports N"))
        with tempfile.TemporaryDirectory() as directory, self.assertRaisesRegex(GateError, "no spec.k"):
            kdefinition.emitted_claims(Path(directory), "M", 2)

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

    def test_artifacts_only_mode_directs_a_difference_to_the_full_gate(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "pins.toml"
            path.write_text(self.TOML, encoding="utf-8")
            with self.assertRaisesRegex(GateError, "cannot be combined with --artifacts-only"):
                pins.Ledger(path, record=True, artifacts_only=True)
            ledger = pins.Ledger(path, artifacts_only=True)
            ledger.expect("expansion_sha256", "old")
            with self.assertRaisesRegex(GateError, "differs from its pin.*run the full gate"):
                ledger.expect(("artifact_sha256", "definition.k"), "new-k")
            with self.assertRaisesRegex(GateError, "has no pin missing; --artifacts-only.*full gate"):
                ledger.expect("missing", "value")

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
        self.assertGreater(lock.krs_ir_schema(), 0)

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
