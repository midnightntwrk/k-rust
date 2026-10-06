"""Tests of the reference-output cache (scripts/reference_cache.py).

Run: python3 -m unittest discover -s scripts/conformance -p 'test_*.py'
"""

import json
import os
import signal
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS))
import reference_cache  # noqa: E402

TOOL = """#!/usr/bin/env bash
# A deterministic stand-in for a reference tool: it reads its input, writes an output tree,
# deletes a stale file, and prints to both streams.
echo "stdout $* $(cat input.txt)"
echo "stderr line" >&2
mkdir -p out
printf 'result %s\\n' "$(cat input.txt)" > out/result.txt
printf '#!/bin/sh\\n' > out/run.sh
chmod +x out/run.sh
rm -f stale.txt
exit ${FAKE_RC:-0}
"""

KDEP = """#!/usr/bin/env bash
# A stand-in for kdep: the source requires the file named in its first line.
source="${@: -1}"
required=$(head -n 1 "$source")
case $required in /*) ;; *) required=$PWD/$required ;; esac
printf 'x-kompiled/timestamp : \\\\\\n    %s \\\\\\n    %s\\n' "$PWD/$source" "$required"
"""


class CacheFixture(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="reference-cache-test.")
        self.root = Path(self.temporary.name)
        self.tool = self.root / "bin" / "tool"
        self.tool.parent.mkdir()
        self.tool.write_text(TOOL)
        self.tool.chmod(0o755)
        self.kdep = self.root / "bin" / "kdep"
        self.kdep.write_text(KDEP)
        self.kdep.chmod(0o755)
        self.store = self.root / "store"
        self.work = self.root / "work-a"
        self.work.mkdir()
        (self.work / "input.txt").write_text("one\n")
        (self.work / "stale.txt").write_text("stale\n")
        self.environment = {"PATH": os.environ["PATH"], "K_OPTS": "-Xmx1g", "GHCRTS": "-N1"}

    def tearDown(self):
        self.temporary.cleanup()

    def cache(self, mode="on", max_age=3600.0, guard="", work=None):
        return reference_cache.ReferenceCache(
            mode, self.store, {"k": {"revision": "pinned"}}, max_age,
            placeholders={"work": str(work or self.work)}, guard_kind=guard)

    def invocation(self, work=None, argv_extra=(), **fields):
        work = work or self.work
        fields.setdefault("roots", [str(work)])
        return reference_cache.Invocation(
            tool="tool",
            argv=[str(self.tool), "input.txt", *argv_extra],
            cwd=str(work),
            tool_path=str(self.tool),
            environment=dict(self.environment),
            label="test",
            **fields,
        )

    def runner(self, work=None, environment=None, calls=None):
        work = work or self.work

        def run():
            if calls is not None:
                calls.append(1)
            started = time.monotonic()
            completed = subprocess.run(
                [str(self.tool), "input.txt"], cwd=work, capture_output=True,
                env=dict(os.environ, **(environment or {})), check=False)
            return (completed.returncode, completed.stdout, completed.stderr,
                    time.monotonic() - started, False)
        return run

    def reset_work(self, work=None):
        work = work or self.work
        subprocess.run(["rm", "-rf", str(work / "out")], check=True)
        (work / "stale.txt").write_text("stale\n")

    def entries(self):
        return sorted((self.store / "entries").glob("*/*"))


class ReplayTests(CacheFixture):
    def test_a_hit_replays_the_status_streams_and_file_changes_byte_for_byte(self):
        calls = []
        first = self.cache().run(self.invocation(), self.runner(calls=calls))
        self.assertEqual(first.status, "miss")
        fresh_result = (self.work / "out" / "result.txt").read_bytes()
        self.reset_work()
        second = self.cache().run(self.invocation(), self.runner(calls=calls))
        self.assertEqual(second.status, "hit")
        self.assertEqual(len(calls), 1, "a hit must not run the tool")
        self.assertEqual((second.rc, second.stdout, second.stderr),
                         (first.rc, first.stdout, first.stderr))
        self.assertEqual((self.work / "out" / "result.txt").read_bytes(), fresh_result)
        self.assertTrue(os.stat(self.work / "out" / "run.sh").st_mode & stat.S_IXUSR)
        self.assertFalse((self.work / "stale.txt").exists(), "a deletion is replayed")

    def test_a_changed_input_misses(self):
        self.cache().run(self.invocation(), self.runner())
        self.reset_work()
        (self.work / "input.txt").write_text("two\n")
        result = self.cache().run(self.invocation(), self.runner())
        self.assertEqual(result.status, "miss")
        self.assertIn(b"two", result.stdout)

    def test_a_different_output_root_state_misses(self):
        self.cache().run(self.invocation(), self.runner())
        # out/ now exists: the pre-state differs, so the earlier entry does not apply.
        result = self.cache().run(self.invocation(), self.runner())
        self.assertEqual(result.status, "miss")

    def test_the_scratch_directory_is_a_placeholder(self):
        self.cache().run(self.invocation(), self.runner())
        other = self.root / "work-b"
        other.mkdir()
        (other / "input.txt").write_text("one\n")
        (other / "stale.txt").write_text("stale\n")
        result = self.cache(work=other).run(self.invocation(work=other), self.runner(work=other))
        self.assertEqual(result.status, "hit")
        self.assertEqual((other / "out" / "result.txt").read_text(), "result one\n")

    def test_semantic_environment_is_keyed_and_resource_settings_are_not(self):
        self.cache().run(self.invocation(), self.runner())
        self.reset_work()
        heap = self.invocation()
        heap.environment["K_OPTS"] = "-Xmx4g -Dscala.concurrent.context.numThreads=2"
        self.assertEqual(self.cache().run(heap, self.runner()).status, "hit")
        self.reset_work()
        threads = self.invocation()
        threads.environment["GHCRTS"] = "-N4"
        self.assertEqual(self.cache().run(threads, self.runner()).status, "miss")
        self.reset_work()
        property_ = self.invocation()
        property_.environment["K_OPTS"] = "-Dfile.encoding=latin1"
        self.assertEqual(self.cache().run(property_, self.runner()).status, "miss")

    def test_an_argument_naming_a_file_keys_on_its_content(self):
        # Outside the output root, so only the argument names it.
        extra = self.root / "program.txt"
        extra.write_text("a\n")
        self.cache().run(self.invocation(argv_extra=[str(extra)]), self.runner())
        self.reset_work()
        extra.write_text("b\n")
        result = self.cache().run(self.invocation(argv_extra=[str(extra)]), self.runner())
        self.assertEqual(result.status, "miss")

    def test_off_runs_the_tool_and_touches_no_store(self):
        result = self.cache("off").run(self.invocation(), self.runner())
        self.assertEqual(result.status, "off")
        self.assertFalse(self.store.exists())

    def test_an_entry_older_than_the_maximum_age_is_recomputed(self):
        self.cache().run(self.invocation(), self.runner())
        self.reset_work()
        meta = self.entries()[0] / "meta.json"
        document = json.loads(meta.read_text())
        document["created"] -= 7200
        meta.write_bytes(reference_cache.canonical(document))
        manifest = self.entries()[0] / "manifest.sha256"
        manifest.write_text("".join(
            f"{reference_cache.file_digest(str(self.entries()[0] / name))}  {name}\n"
            for name in [line.split("  ", 1)[1] for line in manifest.read_text().splitlines()]))
        calls = []
        result = self.cache(max_age=3600.0).run(self.invocation(), self.runner(calls=calls))
        self.assertEqual(result.status, "miss")
        self.assertIn("maximum age", result.detail)
        self.assertEqual(len(calls), 1)


class IntegrityTests(CacheFixture):
    def corrupt_archive(self):
        entry = self.entries()[0]
        archive = next(entry.glob("files.tar.*"))
        data = bytearray(archive.read_bytes())
        data[len(data) // 2] ^= 0xFF
        archive.write_bytes(bytes(data))

    def test_a_corrupted_entry_is_recomputed(self):
        self.cache().run(self.invocation(), self.runner())
        self.reset_work()
        self.corrupt_archive()
        calls = []
        result = self.cache().run(self.invocation(), self.runner(calls=calls))
        self.assertEqual(result.status, "miss")
        self.assertEqual(len(calls), 1)
        self.assertEqual((self.work / "out" / "result.txt").read_text(), "result one\n")
        self.reset_work()
        self.assertEqual(self.cache().run(self.invocation(), self.runner()).status, "hit",
                         "the recomputed entry replaces the corrupted one")

    def test_a_corrupted_stream_is_recomputed(self):
        first = self.cache().run(self.invocation(), self.runner())
        self.reset_work()
        stdout = self.entries()[0] / "stdout"
        stdout.write_bytes(stdout.read_bytes() + b"x")
        result = self.cache().run(self.invocation(), self.runner())
        self.assertEqual(result.status, "miss")
        self.assertEqual(result.stdout, first.stdout)

    def test_a_preimage_that_does_not_match_its_key_is_rejected(self):
        self.cache().run(self.invocation(), self.runner())
        self.reset_work()
        entry = self.entries()[0]
        key = json.loads((entry / "key.json").read_text())
        key["argv"].append("forged")
        (entry / "key.json").write_bytes(reference_cache.canonical(key))
        manifest = entry / "manifest.sha256"
        manifest.write_text("".join(
            f"{reference_cache.file_digest(str(entry / name))}  {name}\n"
            for name in [line.split("  ", 1)[1] for line in manifest.read_text().splitlines()]))
        self.assertEqual(self.cache().run(self.invocation(), self.runner()).status, "miss")

    def hand_edit(self):
        """Edit the stored stdout and re-sign the manifest, as a stale entry would look."""
        entry = self.entries()[0]
        (entry / "stdout").write_bytes(b"edited by hand\n")
        manifest = entry / "manifest.sha256"
        manifest.write_text("".join(
            f"{reference_cache.file_digest(str(entry / name))}  {name}\n"
            for name in [line.split("  ", 1)[1] for line in manifest.read_text().splitlines()]))

    def test_verify_flags_a_hand_edited_entry(self):
        self.cache().run(self.invocation(), self.runner())
        self.reset_work()
        self.hand_edit()
        self.assertEqual(self.cache().run(self.invocation(), self.runner()).stdout,
                         b"edited by hand\n", "a consistent entry is trusted in mode on")
        self.reset_work()
        cache = self.cache("verify")
        result = cache.run(self.invocation(), self.runner())
        self.assertEqual(result.status, "verify-mismatch")
        self.assertIn("stdout", result.detail)
        self.assertEqual(cache.mismatches, ["test: " + result.detail])
        self.assertIn(b"stdout input.txt one", result.stdout, "verify hands the gate the fresh result")
        self.reset_work()
        recomputed = self.cache().run(self.invocation(), self.runner())
        self.assertEqual(recomputed.status, "miss", "verify drops the contradicted entry")
        self.assertEqual(recomputed.stdout, result.stdout)

    def test_verify_accepts_an_unchanged_entry_from_another_scratch_directory(self):
        self.cache().run(self.invocation(), self.runner())
        other = self.root / "work-b"
        other.mkdir()
        (other / "input.txt").write_text("one\n")
        (other / "stale.txt").write_text("stale\n")
        result = self.cache("verify", work=other).run(self.invocation(work=other),
                                                     self.runner(work=other))
        self.assertEqual(result.status, "verify-ok")

    def test_verify_does_not_flag_output_that_varies_between_fresh_runs(self):
        noisy = self.tool.read_text().replace(
            'exit ${FAKE_RC:-0}', 'date +%s%N > out/nonce.txt\nexit ${FAKE_RC:-0}')
        self.tool.write_text(noisy)
        self.cache().run(self.invocation(), self.runner())
        self.reset_work()
        result = self.cache("verify").run(self.invocation(), self.runner())
        self.assertEqual(result.status, "verify-ok")
        self.assertIn("nondeterministic output: r0/out/nonce.txt", result.detail)


class VerifyEquivalenceTests(unittest.TestCase):
    def classify(self, stored, fresh):
        return reference_cache.classify_difference(
            reference_cache.neutral_digest(stored, [], []),
            reference_cache.neutral_digest(fresh, [], []))

    def test_run_dependent_order_and_generated_numbering_are_tolerated(self):
        stored = b"rule A(Var'Unds'Gen2, Var'Unds'Gen3)\nrule B\n"
        fresh = b"rule B\nrule A(Var'Unds'Gen0, Var'Unds'Gen1)\n"
        self.assertEqual(self.classify(stored, fresh), "equivalent")

    def test_a_changed_sentence_is_examined(self):
        self.assertEqual(self.classify(b"rule A\nrule B\n", b"rule A\nrule C\n"), "candidate")
        self.assertEqual(self.classify(b"rule A(Gen0, Gen1)\n", b"rule A(Gen0, Gen0)\n"), "candidate")

    def test_binary_artifacts_count_by_presence(self):
        self.assertEqual(self.classify(b"\x00\x01", b"\x00\x02"), "binary")
        self.assertEqual(reference_cache.classify_difference(
            None, reference_cache.neutral_digest(b"\x00", [], [])), "candidate")


class StorePolicyTests(CacheFixture):
    def run_once(self, runner, **fields):
        return self.cache(**fields.pop("cache", {})).run(self.invocation(**fields), runner)

    def test_timeouts_signals_and_resource_failures_are_not_stored(self):
        outcomes = [
            (lambda: (0, b"", b"", 1.0, True), "timed out"),
            (lambda: (-int(signal.SIGXCPU), b"", b"", 1.0, False), "signal"),
            (lambda: (137, b"", b"", 1.0, False), "signal"),
            (lambda: (1, b"", b"java.lang.OutOfMemoryError: Java heap space", 1.0, False), "resource"),
            (lambda: (1, b"", b"Exception in thread main java.lang.StackOverflowError", 1.0, False), "resource"),
        ]
        for runner, reason in outcomes:
            result = self.run_once(runner)
            self.assertEqual(result.status, "uncacheable", reason)
        self.assertEqual(self.entries(), [])

    def test_a_rejection_is_stored_unless_the_caller_restricts_statuses(self):
        rejected = lambda: (1, b"", b"[Error] Compiler: rejected", 1.0, False)
        self.assertEqual(self.run_once(rejected).status, "miss")
        restricted = self.run_once(rejected, store_statuses=(0,))
        self.assertEqual(restricted.status, "uncacheable",
                         "a caller that retries other statuses never replays one")

    def test_the_address_space_fallback_stores_only_successful_non_llvm_runs(self):
        guard = {"guard": "rlimit-as"}
        rejected = lambda: (1, b"", b"[Error] rejected", 1.0, False)
        self.assertEqual(self.run_once(rejected, cache=guard).status, "uncacheable")
        llvm = self.cache(guard="rlimit-as").run(
            self.invocation(argv_extra=["--backend", "llvm"]), self.runner())
        self.assertEqual(llvm.status, "uncacheable")
        self.assertEqual(self.run_once(self.runner(), cache=guard).status, "miss")


class ClosureTests(CacheFixture):
    def kompile(self):
        return self.invocation(argv_extra=["source.k"], closure="kdep", kdep=str(self.kdep))

    def test_the_requires_closure_is_rechecked_on_lookup(self):
        # The required file lies outside the output root and the argument vector, so only the
        # recorded closure names it.
        required = self.root / "lib" / "required.k"
        required.parent.mkdir()
        (self.work / "source.k").write_text(f"{required}\n")
        required.write_text("module A endmodule\n")
        self.assertEqual(self.cache().run(self.kompile(), self.runner()).status, "miss")
        self.reset_work()
        self.assertEqual(self.cache().run(self.kompile(), self.runner()).status, "hit")
        self.reset_work()
        required.write_text("module B endmodule\n")
        self.assertEqual(self.cache().run(self.kompile(), self.runner()).status, "miss",
                         "a changed required file invalidates the entry")

    def test_a_failing_closure_computation_leaves_the_result_unstored(self):
        (self.work / "source.k").write_text("missing.k\n")
        self.assertEqual(self.cache().run(self.kompile(), self.runner()).status, "uncacheable")

    def test_kdep_output_parsing(self):
        rule = "a-kompiled/timestamp : \\\n    /x/a.k \\\n    /x/b\\ c.md\n"
        self.assertEqual(reference_cache.parse_kdep(rule), ["/x/a.k", "/x/b c.md"])
        self.assertEqual(
            reference_cache.closure_request(
                ["kompile", "--backend", "haskell", "-I", "inc", "a.k", "--md-selector", "k",
                 "--output-definition", "out", "-Iother", "--emit-json"]),
            ("a.k", ["-I", "inc", "--md-selector", "k", "-I", "other"]))


class ModeTests(unittest.TestCase):
    def test_mode_resolution(self):
        self.assertEqual(reference_cache.resolve_mode({})[0], "on")
        self.assertEqual(reference_cache.resolve_mode({"CI": "true"})[0], "off")
        self.assertEqual(reference_cache.resolve_mode({"CI": "true", "REFERENCE_CACHE": "on"})[0], "on")
        self.assertEqual(reference_cache.resolve_mode(
            {"REFERENCE_CACHE": "on", "REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED": "1"})[0], "off")
        with self.assertRaises(ValueError):
            reference_cache.resolve_mode({"REFERENCE_CACHE": "sometimes"})


class CommandLineTests(CacheFixture):
    def cli(self, *extra, stdin=subprocess.DEVNULL, merged=False, mode="on"):
        environment = dict(os.environ, REFERENCE_CACHE=mode, REFERENCE_CACHE_DIR=str(self.store),
                           REFERENCE_CACHE_PINS='{"k":"pinned"}',
                           REFERENCE_CACHE_LOG=str(self.root / "log.jsonl"))
        environment.pop("CI", None)
        return subprocess.run(
            [sys.executable, str(SCRIPTS / "reference_cache.py"), "run", "--tool", "tool",
             "--label", "cli", "--placeholder", f"work={self.work}", "--output-root", ".",
             *extra, "--", str(self.tool), "input.txt"],
            cwd=self.work, env=environment, stdin=stdin, capture_output=not merged,
            stdout=subprocess.PIPE if merged else None,
            stderr=subprocess.STDOUT if merged else None, check=False)

    def statuses(self):
        return [json.loads(line)["status"] for line in (self.root / "log.jsonl").read_text().splitlines()]

    def test_the_command_line_replays_streams_and_status(self):
        first = self.cli()
        self.reset_work()
        second = self.cli()
        self.assertEqual((second.returncode, second.stdout, second.stderr),
                         (first.returncode, first.stdout, first.stderr))
        self.assertEqual(self.statuses(), ["miss", "hit"])

    def test_merged_streams_keep_their_order(self):
        first = self.cli(merged=True)
        self.reset_work()
        second = self.cli(merged=True)
        self.assertEqual(second.stdout, first.stdout)
        self.assertEqual(first.stdout.splitlines()[1], b"stderr line")
        self.assertEqual(self.statuses(), ["miss", "hit"])

    def test_standard_input_is_keyed_when_it_is_finite(self):
        stdin = self.root / "stdin.txt"
        stdin.write_text("first\n")
        with stdin.open("rb") as source:
            self.cli("--stdin", stdin=source)
        self.reset_work()
        stdin.write_text("second\n")
        with stdin.open("rb") as source:
            self.cli("--stdin", stdin=source)
        self.reset_work()
        pipe = subprocess.Popen(["cat"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.cli("--stdin", stdin=pipe.stdout)
        pipe.stdin.close()
        pipe.stdout.close()
        pipe.wait()
        self.assertEqual(self.statuses(), ["miss", "miss", "uncacheable"])

    def test_the_summary_fails_on_a_verify_mismatch(self):
        log = self.root / "summary.jsonl"
        log.write_text(json.dumps({"status": "hit"}) + "\n")
        environment = dict(os.environ, REFERENCE_CACHE="on")
        summary = [sys.executable, str(SCRIPTS / "reference_cache.py"), "summary", "--log", str(log)]
        ok = subprocess.run(summary, env=environment, capture_output=True, text=True, check=False)
        self.assertEqual(ok.returncode, 0)
        self.assertIn("1 hit", ok.stdout)
        with log.open("a") as handle:
            handle.write(json.dumps({"status": "verify-mismatch", "label": "x", "detail": "stdout"}) + "\n")
        failed = subprocess.run(summary, env=environment, capture_output=True, text=True, check=False)
        self.assertEqual(failed.returncode, 1)
        self.assertIn("verify mismatch: x: stdout", failed.stderr)


if __name__ == "__main__":
    unittest.main()
