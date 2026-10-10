"""Unit checks for the reference-K cache, with a stand-in tool."""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys
import tempfile
import textwrap
import time
import tomllib
import unittest
from unittest.mock import patch

from support import ROOT, GateError, reference
from support.hashing import sha256_bytes
from support.lock import k_version
from support.pins import Ledger
from support.reference import (
    Cache, Key, Output, Pin, Placeholders, Promotion, Snapshot, cache_root, child_arguments, dump_manifest,
    indented_json, json_sorted_lists, json_without_members, reduce_k_util_temp, reduce_kprove_temp,
    reduce_lambda_suffixes, reduce_run_dependent_text, reduce_store_paths, renumbered_kore_generated_variables,
    sorted_kore_claims, sorted_kore_imports, substitute,
)


FAKE_TOOL = textwrap.dedent(
    f"""\
    #!{sys.executable}
    import sys
    from pathlib import Path

    arguments = sys.argv[1:]
    source = Path(arguments[0])
    output = Path(arguments[1])
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("compiled " + str(source) + "\\n" + source.read_text(), encoding="utf-8")
    print("read", source)
    if "--fail" in arguments:
        print("rejected", source, file=sys.stderr)
        raise SystemExit(3)
    """
)


def unavailable() -> dict[str, str]:
    raise GateError("required K tool 'kompile' is not on PATH; install K")


class SnapshotTests(unittest.TestCase):
    def setUp(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.base = Path(self._temporary.name)
        tool = self.base / "fake-kompile"
        tool.write_text(FAKE_TOOL, encoding="utf-8")
        tool.chmod(0o755)
        self.executables = {"kompile": str(tool)}
        self.fixture = self.base / "fixture.k"
        self.fixture.write_text("module FIXTURE endmodule\n", encoding="utf-8")
        self.cache = Cache(self.base / "cache")
        self.pins = self.base / "pins.json"
        self.pins.write_text('{"schema": 1}\n', encoding="utf-8")

    def tearDown(self) -> None:
        self._temporary.cleanup()

    def key(self) -> Key:
        return Key(tools=("kompile",), upstream={"imp": "abc"}, inputs={"fixture.k": self.fixture})

    def workspace(self, name: str) -> Path:
        workspace = self.base / name
        workspace.mkdir()
        (workspace / "input.k").write_text("input bytes\n", encoding="utf-8")
        return workspace

    def pin(self, *, record: bool = False) -> Pin:
        return Pin(Ledger(self.pins, record=record), "oracle")

    def open(self, workspace: Path, *, record: bool = False, refresh: bool = False, tools=None, **options) -> Snapshot:
        pin = options.pop("pin", None) or self.pin(record=record)
        return Snapshot(
            "gate/oracle", self.key(), workspace=workspace, refresh=refresh, pin=pin,
            tools=tools or (lambda: self.executables), cache=self.cache, **options,
        )

    def exercise(self, snapshot: Snapshot, workspace: Path, *, fail: bool = False) -> list[tuple[int, str, str, str]]:
        output = workspace / "out" / "parsed.json"
        arguments = [workspace / "input.k", output, *(["--fail"] if fail else [])]
        process = snapshot.run("kompile/definition", "kompile", arguments, timeout=30, outputs=(output,))
        return [(process.returncode, process.stdout, process.stderr, output.read_text(encoding="utf-8"))]

    def record(self, name: str = "live", *, fail: bool = False) -> tuple[str, list[tuple[int, str, str, str]]]:
        """A `--record` run of a miss: it runs live, pins the digest, and stores the entry."""

        workspace = self.workspace(name)
        pin = self.pin(record=True)
        live = self.open(workspace, pin=pin)
        observed = self.exercise(live, workspace, fail=fail)
        report = live.finish()
        pin.ledger.write()
        self.assertIn("ran 1 invocations live (no reference digest is pinned for it)", report)
        return json.loads(self.pins.read_text(encoding="utf-8"))["reference_sha256"]["oracle"], observed

    def entries(self) -> list[Path]:
        return sorted((self.cache.root / "entries").glob("*/*"))

    def test_cache_root_is_per_user_and_overridable_but_never_in_the_repository(self) -> None:
        self.assertEqual(
            cache_root({"HOME": "/home/u", "XDG_CACHE_HOME": "/x/cache"}),
            Path("/x/cache/krs/reference-outputs/v1"),
        )
        with patch.dict(os.environ, {"HOME": "/home/u"}):
            self.assertEqual(cache_root({}), Path("/home/u/.cache/krs/reference-outputs/v1"))
        self.assertEqual(cache_root({"KRS_REFERENCE_CACHE_DIR": "/srv/store"}), Path("/srv/store"))
        with self.assertRaisesRegex(GateError, "inside the repository"):
            cache_root({"KRS_REFERENCE_CACHE_DIR": os.fspath(ROOT / "tests" / "cache")})

    def test_a_miss_runs_live_and_stores_only_at_finish_under_the_manifest_digest(self) -> None:
        workspace = self.workspace("live")
        pin = self.pin(record=True)
        live = self.open(workspace, pin=pin)
        self.assertEqual(live.mode, "miss")
        self.exercise(live, workspace)
        self.assertEqual(self.entries(), [], "a live run stores nothing before finish")
        live.finish()
        pin.ledger.write()
        digest = json.loads(self.pins.read_text(encoding="utf-8"))["reference_sha256"]["oracle"]
        self.assertEqual(self.entries(), [self.cache.entry_path(digest)])
        entry = self.cache.entry_path(digest)
        manifest = (entry / "manifest.toml").read_bytes()
        self.assertEqual(sha256_bytes(manifest), digest)
        self.assertIn(b'"{{work}}/input.k"', manifest)
        self.assertNotIn(os.fsencode(self.base / "live"), manifest)
        self.assertEqual(
            sorted(path.relative_to(entry).as_posix() for path in entry.rglob("*") if path.is_file()),
            ["kompile/definition.out.parsed.json", "kompile/definition.stdout", "manifest.toml"],
        )
        self.assertEqual(list((self.cache.root / "tmp").iterdir()), [], "the temporary directory is renamed away")

    def test_a_hit_replays_at_another_location_without_any_k_tool(self) -> None:
        digest, observed = self.record()
        workspace = self.workspace("elsewhere")
        replay = self.open(workspace, tools=unavailable)
        self.assertEqual(replay.mode, "hit")
        replayed = self.exercise(replay, workspace)
        self.assertEqual(
            replay.finish(), f"gate/oracle: replayed 1 invocations from the reference cache entry {digest[:12]}",
        )
        live_path, replay_path = str(self.base / "live"), str(workspace)
        self.assertEqual(
            replayed,
            [tuple(part.replace(live_path, replay_path) if isinstance(part, str) else part for part in row)
             for row in observed],
        )

    def test_a_miss_without_k_fails_closed_naming_the_tool(self) -> None:
        self.record()
        self.cache = Cache(self.base / "empty-cache")
        workspace = self.workspace("cold")
        cold = self.open(workspace, tools=lambda: reference.live_tools(("kompile",)))
        self.assertEqual(cold.mode, "miss")
        with patch.dict(os.environ, {"PATH": os.fspath(self.base / "no-tools"), "KRS_K_BIN": ""}):
            with self.assertRaisesRegex(
                GateError,
                r"gate/oracle: the reference cache .*empty-cache holds no entry [0-9a-f]{64}, "
                r"so its K invocations must run live: required K tool 'kompile' is not on PATH; "
                rf"install K v{k_version()} .* or set KRS_K_BIN",
            ):
                self.exercise(cold, workspace)
        self.assertFalse((self.base / "empty-cache" / "entries").exists())

    def test_a_partial_tool_set_fails_closed(self) -> None:
        cold = self.open(self.workspace("cold"), tools=lambda: {})
        with self.assertRaisesRegex(GateError, "the K tools kompile are unavailable; install K"):
            self.exercise(cold, self.base / "cold")

    def test_refresh_reruns_live_and_keeps_the_identical_entry(self) -> None:
        digest, _ = self.record()
        before = (self.cache.entry_path(digest) / "manifest.toml").read_bytes()
        workspace = self.workspace("refresh")
        refresh = self.open(workspace, refresh=True)
        self.assertEqual(refresh.mode, "refresh")
        self.exercise(refresh, workspace)
        self.assertIn(f"stored the reference cache entry {digest[:12]}", refresh.finish())
        self.assertEqual((self.cache.entry_path(digest) / "manifest.toml").read_bytes(), before)

    def test_a_failing_run_stores_nothing(self) -> None:
        workspace = self.workspace("live")
        live = self.open(workspace, record=True)
        self.exercise(live, workspace)
        # The gate fails after the K invocation and never calls finish.
        del live
        self.assertFalse((self.cache.root / "entries").exists())

    def test_an_interrupted_store_leaves_no_partial_entry(self) -> None:
        workspace = self.workspace("live")
        live = self.open(workspace, record=True)
        self.exercise(live, workspace)
        original = Path.write_bytes
        calls = []

        def fail_on_second(path: Path, data: bytes) -> int:
            calls.append(path)
            if len(calls) == 2:
                raise OSError("disk full")
            return original(path, data)

        with patch.object(Path, "write_bytes", fail_on_second), self.assertRaisesRegex(OSError, "disk full"):
            live.finish()
        self.assertEqual(self.entries(), [])
        self.assertEqual(list((self.cache.root / "tmp").iterdir()), [])

    def test_a_live_result_that_differs_from_its_pin_fails_and_is_not_stored(self) -> None:
        digest, _ = self.record()
        self.cache = Cache(self.base / "other-cache")
        workspace = self.workspace("changed")
        (workspace / "input.k").write_text("emitted K changed\n", encoding="utf-8")
        live = self.open(workspace)
        self.exercise(live, workspace)
        with self.assertRaisesRegex(
            GateError, rf"differs from its pin pins.json reference_sha256.oracle={digest} "
            r"\(the pinned entry is not in the reference cache.*--record",
        ):
            live.finish()
        self.assertFalse((self.base / "other-cache" / "entries").exists())

    def test_a_refresh_names_the_invocations_that_differ_from_a_cached_pin(self) -> None:
        self.record()
        workspace = self.workspace("changed")
        (workspace / "input.k").write_text("emitted K changed\n", encoding="utf-8")
        refresh = self.open(workspace, refresh=True)
        self.exercise(refresh, workspace)
        with self.assertRaisesRegex(GateError, r"invocations \['kompile/definition'\]\).*nondeterministic"):
            refresh.finish()

    def test_record_accepts_a_new_digest_and_stores_it_beside_the_old_entry(self) -> None:
        old, _ = self.record()
        workspace = self.workspace("changed")
        (workspace / "input.k").write_text("emitted K changed\n", encoding="utf-8")
        pin = self.pin(record=True)
        live = self.open(workspace, refresh=True, pin=pin)
        self.exercise(live, workspace)
        live.finish()
        pin.ledger.write()
        new = json.loads(self.pins.read_text(encoding="utf-8"))["reference_sha256"]["oracle"]
        self.assertNotEqual(new, old)
        self.assertEqual(self.entries(), sorted([self.cache.entry_path(old), self.cache.entry_path(new)]))

    def test_failing_invocations_are_stored_with_their_status(self) -> None:
        self.record(fail=True)
        workspace = self.workspace("replay")
        replay = self.open(workspace, tools=unavailable)
        returncode, _, stderr, _ = self.exercise(replay, workspace, fail=True)[0]
        self.assertEqual(returncode, 3)
        self.assertEqual(stderr, f"rejected {workspace / 'input.k'}\n")

    def test_a_key_difference_on_a_hit_fails_closed(self) -> None:
        self.record()
        self.fixture.write_text("module CHANGED endmodule\n", encoding="utf-8")
        with self.assertRaisesRegex(GateError, r"another key: inputs: .*--refresh-reference --record"):
            self.open(self.workspace("replay"))

    def test_argv_and_argument_file_differences_on_a_hit_fail_closed(self) -> None:
        self.record()
        workspace = self.workspace("replay")
        with self.assertRaisesRegex(GateError, "another argument vector.*--refresh-reference --record"):
            self.exercise(self.open(workspace), workspace, fail=True)
        (workspace / "input.k").write_text("emitted K changed\n", encoding="utf-8")
        with self.assertRaisesRegex(GateError, "input digests differ.*--refresh-reference --record"):
            self.exercise(self.open(workspace), workspace)

    def test_unrequested_and_unrecorded_invocations_fail(self) -> None:
        self.record()
        workspace = self.workspace("replay")
        replay = self.open(workspace)
        with self.assertRaisesRegex(GateError, "has no recorded invocation kompile/other"):
            replay.run("kompile/other", "kompile", [workspace / "input.k"], timeout=30)
        with self.assertRaisesRegex(GateError, r"not requested: \['kompile/definition'\]"):
            replay.finish()

    def test_a_tampered_or_incomplete_entry_is_a_miss(self) -> None:
        digest, _ = self.record()
        entry = self.cache.entry_path(digest)
        (entry / "kompile/definition.stdout").write_text("edited\n", encoding="utf-8")
        self.assertFalse(self.cache.holds(digest))
        self.assertEqual(self.open(self.workspace("tampered")).mode, "miss")
        (entry / "kompile/definition.stdout").unlink()
        self.assertEqual(self.open(self.workspace("incomplete")).mode, "miss")
        workspace = self.workspace("repair")
        live = self.open(workspace)
        self.exercise(live, workspace)
        live.finish()
        self.assertTrue(self.cache.holds(digest), "a live run with the pinned digest replaces the damaged entry")

    def test_stream_reducers_apply_to_live_and_stored_streams(self) -> None:
        workspace = self.workspace("live")
        output = workspace / "out" / "parsed.json"
        live = self.open(workspace)
        process = live.run(
            "kompile/definition", "kompile", [workspace / "input.k", output], timeout=30,
            streams={"stdout": lambda text: text.upper()},
        )
        self.assertEqual(process.stdout, f"READ {str(workspace / 'input.k').upper()}\n")
        with self.assertRaisesRegex(GateError, "unknown streams"):
            live.run("kompile/other", "kompile", [], timeout=30, streams={"stdin": str})

    def test_a_live_run_reduces_run_dependent_tool_text_before_its_own_reducers(self) -> None:
        tool = self.base / "fake-krun"
        tool.write_text(textwrap.dedent(
            f"""\
            #!{sys.executable}
            import random, string, sys
            name = "".join(random.choice(string.ascii_letters) for _ in range(10))
            print(f"kore-exec: [{{random.randrange(1000)}}] Warning")
            print(f"[Error] krun: /tmp/.krun-2026-10-09-07-36-54-{{name}}/result.kore", file=sys.stderr)
            """
        ), encoding="utf-8")
        tool.chmod(0o755)
        self.executables = {"kompile": str(tool)}
        for name in ("first", "second"):
            workspace = self.workspace(name)
            live = self.open(workspace, record=True)
            process = live.run(
                "kompile/definition", "kompile", [], timeout=30,
                streams={"stderr": lambda text: text.replace("TMPDIR", "T")},
            )
            self.assertEqual(process.stdout, "kore-exec: [-] Warning\n")
            self.assertEqual(process.stderr, "[Error] krun: T/.krun-TEMP/result.kore\n")
            live.finish()
        self.assertEqual(len(set(self.entries())), 1, "both runs store one identical entry")

    def test_live_run_needs_declared_tools_and_unique_labels(self) -> None:
        workspace = self.workspace("live")
        live = self.open(workspace)
        with self.assertRaisesRegex(GateError, "does not declare the K tool 'krun'"):
            live.run("krun/case", "krun", [], timeout=30)
        with self.assertRaisesRegex(GateError, "invalid reference invocation label"):
            live.run("../escape", "kompile", [], timeout=30)
        self.exercise(live, workspace)
        with self.assertRaisesRegex(GateError, "used twice"):
            self.exercise(live, workspace)

    def test_a_live_label_is_reserved_before_its_tool_runs(self) -> None:
        workspace = self.workspace("live")
        live = self.open(workspace)
        concurrent: list[str] = []

        def run_while_another_run_requests_the_label(command: list[str], **options: object):
            # A second request for the label while the first tool still runs,
            # as a concurrent job would make it.
            try:
                self.exercise(live, workspace)
            except GateError as error:
                concurrent.append(str(error))
            return original_run(command, **options)

        original_run = reference.run
        with patch.object(reference, "run", run_while_another_run_requests_the_label):
            self.exercise(live, workspace)
        self.assertEqual(concurrent, ["reference invocation label kompile/definition is used twice"])

    def test_reduced_outputs_are_identical_live_and_replayed(self) -> None:
        def reduce(text: str) -> str:
            return text.splitlines()[0] + "\n"

        workspace = self.workspace("live")
        output = workspace / "out" / "parsed.json"
        pin = self.pin(record=True)
        live = self.open(workspace, pin=pin)
        live.run("kompile/definition", "kompile", [workspace / "input.k", output], timeout=30,
                 outputs=(Output(output, reduce),))
        self.assertEqual(output.read_text(encoding="utf-8"), f"compiled {workspace / 'input.k'}\n")
        live.finish()
        pin.ledger.write()
        (entry,) = self.entries()
        self.assertEqual(
            (entry / "kompile/definition.out.parsed.json").read_text(encoding="utf-8"),
            "compiled {{work}}/input.k\n",
        )

    def test_located_outputs_are_left_at_their_declared_path(self) -> None:
        def run(snapshot: Snapshot, workspace: Path) -> tuple[Path, str]:
            # The tool writes below a directory of its own choosing, as kprove
            # does under --temp-dir; comparators read only the declared path.
            chosen = workspace / "temp" / ".kprove-1" / "spec.kore"
            declared = workspace / "spec" / "spec.kore"
            snapshot.run(
                "kompile/dry-run", "kompile", [workspace / "input.k", chosen], timeout=30,
                outputs=(Output(declared, locate=lambda: chosen),),
            )
            return chosen, declared.read_text(encoding="utf-8")

        workspace = self.workspace("live")
        pin = self.pin(record=True)
        live = self.open(workspace, pin=pin)
        chosen, live_text = run(live, workspace)
        self.assertTrue(chosen.is_file())
        live.finish()
        pin.ledger.write()
        (entry,) = self.entries()
        self.assertEqual(
            (entry / "kompile/dry-run.out.spec.kore").read_text(encoding="utf-8"),
            "compiled {{work}}/input.k\ninput bytes\n",
        )
        replay_workspace = self.workspace("replay")
        replay = self.open(replay_workspace, tools=unavailable)
        chosen, replay_text = run(replay, replay_workspace)
        self.assertFalse(chosen.exists(), "replay writes only the declared path")
        self.assertEqual(replay_text, live_text.replace(str(workspace), str(replay_workspace)))
        replay.finish()

    def test_a_child_stages_its_snapshot_until_the_gate_promotes_it(self) -> None:
        digest, _ = self.record()
        staging = self.base / "staging" / "oracle"
        self.assertEqual(
            child_arguments(staging, self.pin(), refresh=True),
            ["--reference-staging", os.fspath(staging), "--reference-sha256", digest, "--refresh-reference"],
        )
        self.cache = Cache(self.base / "child-cache")
        workspace = self.workspace("child")
        child = Snapshot(
            "gate/oracle", self.key(), workspace=workspace, refresh=False, expected=digest,
            staging=staging, tools=lambda: self.executables, cache=self.cache,
        )
        self.assertEqual(child.mode, "miss")
        self.exercise(child, workspace)
        self.assertIn("staged", child.finish())
        self.assertFalse(self.cache.holds(digest), "a child never stores in the cache itself")
        promotion = Promotion(staging, "gate/oracle", self.pin(), cache=self.cache)
        self.assertIn(f"the reference cache holds entry {digest[:12]}", promotion.finish())
        self.assertTrue(self.cache.holds(digest))

        replayed = self.base / "staging" / "replayed"
        workspace = self.workspace("child-hit")
        child = Snapshot(
            "gate/oracle", self.key(), workspace=workspace, refresh=False, expected=digest,
            staging=replayed, tools=unavailable, cache=self.cache,
        )
        self.assertEqual(child.mode, "hit")
        self.exercise(child, workspace)
        child.finish()
        self.assertIn(digest[:12], Promotion(replayed, "gate/oracle", self.pin(), cache=self.cache).finish())
        with self.assertRaisesRegex(GateError, "has no manifest.toml"):
            Promotion(self.base / "never-written", "gate/oracle", self.pin(), cache=self.cache).finish()

    def test_a_promotion_checks_the_staged_snapshot_against_the_pin(self) -> None:
        self.record()
        staging = self.base / "staging"
        workspace = self.workspace("child")
        (workspace / "input.k").write_text("emitted K changed\n", encoding="utf-8")
        child = Snapshot(
            "gate/oracle", self.key(), workspace=workspace, refresh=True, staging=staging,
            tools=lambda: self.executables, cache=self.cache,
        )
        self.exercise(child, workspace)
        child.finish()
        with self.assertRaisesRegex(GateError, r"invocations \['kompile/definition'\]"):
            Promotion(staging, "gate/oracle", self.pin(), cache=self.cache).finish()
        (staging / "kompile/definition.stdout").write_text("edited\n", encoding="utf-8")
        with self.assertRaisesRegex(GateError, "differs from its manifest digest"):
            Promotion(staging, "gate/oracle", self.pin(), cache=self.cache).finish()

    def test_prune_removes_entries_unused_for_the_maximum_age(self) -> None:
        digest, _ = self.record()
        entry = self.cache.entry_path(digest)
        old = time.time() - 31 * 86400
        os.utime(entry, (old, old))
        with patch.dict(os.environ, {"KRS_REFERENCE_CACHE_MAX_UNUSED_DAYS": "40"}):
            self.assertEqual(self.cache.prune(force=True), 0)
        self.assertEqual(self.cache.prune(force=True), 1)
        self.assertFalse(entry.exists())
        self.assertEqual(self.cache.prune(), 0, "a prune runs at most once a day")
        with patch.dict(os.environ, {"KRS_REFERENCE_CACHE_MAX_UNUSED_DAYS": "0"}):
            with self.assertRaisesRegex(GateError, "must be positive"):
                self.cache.prune(force=True)

    def test_a_hit_marks_the_entry_used(self) -> None:
        digest, _ = self.record()
        entry = self.cache.entry_path(digest)
        old = time.time() - 31 * 86400
        os.utime(entry, (old, old))
        self.assertTrue(self.cache.holds(digest))
        self.assertEqual(self.cache.prune(force=True), 0)


class FormatTests(unittest.TestCase):
    def test_json_sorted_lists_order_only_the_named_lists(self) -> None:
        reduce = json_sorted_lists(["localSentences"])
        text = '{"modules":[{"localSentences":[{"b":2},{"a":1}],"imports":["Z","A"]}]}'
        self.assertEqual(reduce(text), '{"modules":[{"imports":["Z","A"],"localSentences":[{"a":1},{"b":2}]}]}\n')

    def test_sorted_kore_claims_keep_every_line_in_one_order(self) -> None:
        head = "[]\nmodule M-SPEC\n// claims\n"
        first = "// claim b\n  claim{} \\implies(b)\n  [label{}(\"b\")]\n"
        second = "// claim a\n  claim{} \\implies(a)\n  [label{}(\"a\")]\n"
        tail = "endmodule []\n"
        self.assertEqual(sorted_kore_claims(head + first + second + tail), head + second + first + tail)
        self.assertEqual(sorted_kore_claims(head + second + first + tail), head + second + first + tail)
        self.assertEqual(sorted_kore_claims("module M\nendmodule\n"), "module M\nendmodule\n")

    def test_sorted_kore_imports_sort_each_run_of_imports(self) -> None:
        text = "module A\n  import Z []\n  import B []\n\n  axiom{} x []\n  import Y []\nendmodule []\n"
        self.assertEqual(
            sorted_kore_imports(text),
            "module A\n  import B []\n  import Z []\n\n  axiom{} x []\n  import Y []\nendmodule []\n",
        )

    def test_renumbered_kore_generated_variables_rename_per_sentence_by_first_occurrence(self) -> None:
        first = (
            "module M\n// rule r\n  axiom{R} f(Var'Unds'Gen3:S{}, Var'Unds'Gen1:S{}, Var'Unds'Gen3:S{})\n"
            "    [label{}(Var'Unds'Gen10'Unds':S{}, Var'Ques'Unds'Gen2:S{})]\n"
            "  axiom{R} g(Var'Unds'Gen1:S{})\nendmodule []\n"
        )
        renamed = (
            "module M\n// rule r\n  axiom{R} f(Var'Unds'Gen0:S{}, Var'Unds'Gen1:S{}, Var'Unds'Gen0:S{})\n"
            "    [label{}(Var'Unds'Gen10'Unds':S{}, Var'Ques'Unds'Gen2:S{})]\n"
            "  axiom{R} g(Var'Unds'Gen0:S{})\nendmodule []\n"
        )
        self.assertEqual(renumbered_kore_generated_variables(first), renamed)
        self.assertEqual(renumbered_kore_generated_variables(renamed), renamed)

    def test_indented_json_keeps_the_value_and_member_order(self) -> None:
        text = '{"node":"KApply","label":{"name":"x"},"args":[1,2]}'
        self.assertEqual(
            indented_json(text),
            '{\n "node": "KApply",\n "label": {\n  "name": "x"\n },\n "args": [\n  1,\n  2\n ]\n}\n',
        )
        self.assertEqual(indented_json(""), "")
        self.assertEqual(indented_json("not json\n"), "not json\n")

    def test_json_member_reduction_is_canonical(self) -> None:
        reduce = json_without_members(["location"])
        text = '{"term": {"location": [1, 2], "b": "", "items": [{"location": [], "a": 1}]}, "format": "X"}'
        self.assertEqual(reduce(text), '{"format":"X","term":{"b":"","items":[{"a":1}]}}\n')

    def test_substitute_rewrites_every_match(self) -> None:
        self.assertEqual(substitute(r"\[\d+\]", "[-]")("a [12] b [3]"), "a [-] b [-]")

    def test_run_dependent_paths_are_reduced(self) -> None:
        self.assertEqual(
            reduce_kprove_temp("--prove /w/.kprove-2026-10-06-20-12-08-516-838284b1-9c0b/spec.kore"),
            "--prove /w/.kprove-TEMP/spec.kore",
        )
        prelude = "/nix/store/" + "a" * 32 + "-k-7.1.337-4a46d123/include/kframework/builtin/domains.md"
        self.assertEqual(
            reduce_store_paths(f'Source{{}}("{prelude}")'),
            'Source{}("NIX-STORE/include/kframework/builtin/domains.md")',
        )

    def test_run_dependent_tool_text_is_reduced(self) -> None:
        krun = (
            "[Error] krun: \n/w/kompiled/casts/interpreter \n"
            "/tmp/.krun-2026-10-09-07-36-54-2rkCSFPOOA/tmp.in.aXIOefeInT -1 \n"
            "/tmp/.krun-2026-10-09-07-36-54-2rkCSFPOOA/result.kore\n"
        )
        self.assertEqual(
            reduce_k_util_temp(krun),
            "[Error] krun: \n/w/kompiled/casts/interpreter \n"
            "TMPDIR/.krun-TEMP/tmp.in.TEMP -1 \nTMPDIR/.krun-TEMP/result.kore\n",
        )
        self.assertEqual(
            reduce_k_util_temp("/var/tmp/x/.krun-2026-10-10-01-02-03-Ab3dEf9hIj/tmp.in.args.Q1w2E3r4T5"),
            "TMPDIR/.krun-TEMP/tmp.in.args.TEMP",
        )
        log = "kore-exec: [59432] Warning (WarnStuckClaimState):\n    kore-exec: [1] is not a log line\n"
        self.assertEqual(
            reduce_run_dependent_text(log),
            "kore-exec: [-] Warning (WarnStuckClaimState):\n    kore-exec: [1] is not a log line\n",
        )
        self.assertEqual(
            reduce_lambda_suffixes(
                "[Warning] Compiler: Non exhaustive match detected: `#lambdaE__3`(swap(_))\n"
                "#lambdaE__ ( 3 ) #lambdaE_2_pair_12 ( x ) #lambdaP__"
            ),
            "[Warning] Compiler: Non exhaustive match detected: `#lambdaE__N`(swap(_))\n"
            "#lambdaE__N ( 3 ) #lambdaE_2_pair_N ( x ) #lambdaP__N",
        )
        unrelated = "/tmp/.krun-notes/tmp.in.short and /w/.kprove-2026-10-06-20-12-08-516-838284b1/spec.kore #lambdas"
        self.assertEqual(reduce_run_dependent_text(unrelated), unrelated)

    def test_placeholders_round_trip_and_reject_collisions(self) -> None:
        placeholders = Placeholders(Path("/nonexistent/work"))
        text = f"{ROOT}/tests/x.k and {ROOT.parent}/inspirations and /nonexistent/work/y"
        stored = placeholders.store(text)
        self.assertEqual(stored, "{{root}}/tests/x.k and {{external}}/inspirations and {{work}}/y")
        self.assertEqual(placeholders.restore(stored), text)
        with self.assertRaisesRegex(GateError, "already contains"):
            placeholders.store("{{root}}")

    def test_manifest_is_valid_sorted_toml(self) -> None:
        manifest = {
            "schema": 1,
            "key": {"k_version": k_version(), "tools": ["kast"], "upstream": {}, "inputs": {"a/b.k": "00"}},
            "invocation": [
                {"label": "kast/x", "argv": ["kast", "{{work}}/x"], "returncode": 0,
                 "stdout": "11", "stderr": "22", "inputs": {}, "outputs": {"{{work}}/o.json": "33"}},
            ],
        }
        self.assertEqual(tomllib.loads(dump_manifest(manifest)), manifest)


if __name__ == "__main__":
    unittest.main()
