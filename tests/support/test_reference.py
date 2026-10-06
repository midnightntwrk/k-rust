"""Unit checks for recorded reference-K snapshots, with a stand-in tool."""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import textwrap
import tomllib
import unittest
from unittest.mock import patch

from support import ROOT, GateError, reference
from support.lock import k_version
from support.reference import (
    Key, Output, Placeholders, Promotion, Snapshot, dump_manifest, indented_json, json_sorted_lists,
    json_without_members, reduce_kprove_temp, reduce_store_paths, snapshot_directory, sorted_kore_claims,
    substitute,
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
        self.directory = self.base / "reference" / "oracle"

    def tearDown(self) -> None:
        self._temporary.cleanup()

    def key(self) -> Key:
        return Key(tools=("kompile",), upstream={"imp": "abc"}, inputs={"fixture.k": self.fixture})

    def workspace(self, name: str) -> Path:
        workspace = self.base / name
        workspace.mkdir()
        (workspace / "input.k").write_text("input bytes\n", encoding="utf-8")
        return workspace

    def exercise(self, snapshot: Snapshot, workspace: Path, *, fail: bool = False) -> list[tuple[int, str, str, str]]:
        observed = []
        output = workspace / "out" / "parsed.json"
        arguments = [workspace / "input.k", output, *(["--fail"] if fail else [])]
        process = snapshot.run("kompile/definition", "kompile", arguments, timeout=30, outputs=(output,))
        observed.append((process.returncode, process.stdout, process.stderr, output.read_text(encoding="utf-8")))
        return observed

    def refresh(self, name: str = "live") -> tuple[Snapshot, list[tuple[int, str, str, str]]]:
        workspace = self.workspace(name)
        snapshot = Snapshot(
            self.directory, self.key(), workspace=workspace, refresh=True, executables=self.executables,
        )
        return snapshot, self.exercise(snapshot, workspace)

    def files(self) -> dict[str, bytes]:
        return {
            path.relative_to(self.directory).as_posix(): path.read_bytes()
            for path in self.directory.rglob("*") if path.is_file()
        }

    def test_replay_restores_streams_and_outputs_at_another_location(self) -> None:
        live, observed = self.refresh()
        self.assertFalse(self.directory.exists(), "a refresh writes only at finish")
        self.assertIn("refreshed 1 invocations; rewrote", live.finish())
        manifest = (self.directory / "manifest.toml").read_text(encoding="utf-8")
        self.assertIn('"{{work}}/input.k"', manifest)
        self.assertNotIn(str(self.base), manifest)
        self.assertEqual(
            sorted(self.files()),
            ["kompile/definition.out.parsed.json", "kompile/definition.stdout", "manifest.toml"],
        )

        workspace = self.workspace("elsewhere")
        replay = Snapshot(self.directory, self.key(), workspace=workspace, refresh=False)
        replayed = self.exercise(replay, workspace)
        self.assertEqual(replay.finish(), f"replayed 1 recorded invocations from {self.directory}")
        live_path, replay_path = str(self.base / "live"), str(workspace)
        self.assertEqual(
            replayed,
            [tuple(part.replace(live_path, replay_path) if isinstance(part, str) else part for part in row)
             for row in observed],
        )

    def test_refresh_is_byte_identical_and_reports_no_change(self) -> None:
        first, _ = self.refresh("first")
        first.finish()
        before = self.files()
        second, _ = self.refresh("second")
        self.assertIn("already matched", second.finish())
        self.assertEqual(self.files(), before)

    def test_failing_invocations_are_recorded_with_their_status(self) -> None:
        workspace = self.workspace("live")
        live = Snapshot(self.directory, self.key(), workspace=workspace, refresh=True, executables=self.executables)
        self.assertEqual(self.exercise(live, workspace, fail=True)[0][0], 3)
        live.finish()
        replay_workspace = self.workspace("replay")
        replay = Snapshot(self.directory, self.key(), workspace=replay_workspace, refresh=False)
        returncode, _, stderr, _ = self.exercise(replay, replay_workspace, fail=True)[0]
        self.assertEqual(returncode, 3)
        self.assertEqual(stderr, f"rejected {replay_workspace / 'input.k'}\n")

    def test_missing_snapshot_fails_closed(self) -> None:
        with self.assertRaisesRegex(GateError, "is missing; run the gate with --refresh-reference"):
            Snapshot(self.directory, self.key(), workspace=self.workspace("replay"), refresh=False)

    def test_key_mismatch_fails_closed(self) -> None:
        live, _ = self.refresh()
        live.finish()
        self.fixture.write_text("module CHANGED endmodule\n", encoding="utf-8")
        with self.assertRaisesRegex(GateError, r"key differs: inputs: .*--refresh-reference"):
            Snapshot(self.directory, self.key(), workspace=self.workspace("replay"), refresh=False)
        upstream = Key(tools=("kompile",), upstream={"imp": "def"}, inputs={"fixture.k": self.fixture})
        with self.assertRaisesRegex(GateError, "key differs: inputs: .*; upstream: "):
            Snapshot(self.directory, upstream, workspace=self.workspace("replay-2"), refresh=False)

    def test_argv_and_argument_file_differences_fail_closed(self) -> None:
        live, _ = self.refresh()
        live.finish()
        workspace = self.workspace("replay")
        replay = Snapshot(self.directory, self.key(), workspace=workspace, refresh=False)
        with self.assertRaisesRegex(GateError, "another argument vector.*--refresh-reference"):
            self.exercise(replay, workspace, fail=True)

        (workspace / "input.k").write_text("emitted K changed\n", encoding="utf-8")
        replay = Snapshot(self.directory, self.key(), workspace=workspace, refresh=False)
        with self.assertRaisesRegex(GateError, "input digests differ.*--refresh-reference"):
            self.exercise(replay, workspace)

    def test_unrequested_and_unrecorded_invocations_fail(self) -> None:
        live, _ = self.refresh()
        live.finish()
        workspace = self.workspace("replay")
        replay = Snapshot(self.directory, self.key(), workspace=workspace, refresh=False)
        with self.assertRaisesRegex(GateError, "has no recorded invocation kompile/other"):
            replay.run("kompile/other", "kompile", [workspace / "input.k"], timeout=30)
        with self.assertRaisesRegex(GateError, r"not requested: \['kompile/definition'\]"):
            replay.finish()

    def test_tampered_and_stray_files_fail(self) -> None:
        live, _ = self.refresh()
        live.finish()
        stdout = self.directory / "kompile/definition.stdout"
        stdout.write_text("edited\n", encoding="utf-8")
        workspace = self.workspace("replay")
        replay = Snapshot(self.directory, self.key(), workspace=workspace, refresh=False)
        with self.assertRaisesRegex(GateError, "differs from its manifest digest"):
            self.exercise(replay, workspace)
        (self.directory / "stray.txt").write_text("", encoding="utf-8")
        with self.assertRaisesRegex(GateError, r"unexpected=\['stray.txt'\]"):
            Snapshot(self.directory, self.key(), workspace=workspace, refresh=False)

    def test_stream_reducers_apply_to_live_and_stored_streams(self) -> None:
        workspace = self.workspace("live")
        output = workspace / "out" / "parsed.json"
        live = Snapshot(self.directory, self.key(), workspace=workspace, refresh=True, executables=self.executables)
        process = live.run(
            "kompile/definition", "kompile", [workspace / "input.k", output], timeout=30,
            streams={"stdout": lambda text: text.upper()},
        )
        self.assertEqual(process.stdout, f"READ {str(workspace / 'input.k').upper()}\n")
        with self.assertRaisesRegex(GateError, "unknown streams"):
            live.run("kompile/other", "kompile", [], timeout=30, streams={"stdin": str})

    def test_live_run_needs_declared_tools_and_unique_labels(self) -> None:
        workspace = self.workspace("live")
        with self.assertRaisesRegex(GateError, "needs the K tools kompile"):
            Snapshot(self.directory, self.key(), workspace=workspace, refresh=True, executables={})
        live = Snapshot(self.directory, self.key(), workspace=workspace, refresh=True, executables=self.executables)
        with self.assertRaisesRegex(GateError, "does not declare the K tool 'krun'"):
            live.run("krun/case", "krun", [], timeout=30)
        with self.assertRaisesRegex(GateError, "invalid reference invocation label"):
            live.run("../escape", "kompile", [], timeout=30)
        self.exercise(live, workspace)
        with self.assertRaisesRegex(GateError, "used twice"):
            self.exercise(live, workspace)

    def test_a_live_label_is_reserved_before_its_tool_runs(self) -> None:
        workspace = self.workspace("live")
        live = Snapshot(self.directory, self.key(), workspace=workspace, refresh=True, executables=self.executables)
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
        live = Snapshot(self.directory, self.key(), workspace=workspace, refresh=True, executables=self.executables)
        live.run("kompile/definition", "kompile", [workspace / "input.k", output], timeout=30,
                 outputs=(Output(output, reduce),))
        live_text = output.read_text(encoding="utf-8")
        self.assertEqual(live_text, f"compiled {workspace / 'input.k'}\n")
        live.finish()
        self.assertEqual(
            (self.directory / "kompile/definition.out.parsed.json").read_text(encoding="utf-8"),
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
        live = Snapshot(self.directory, self.key(), workspace=workspace, refresh=True, executables=self.executables)
        chosen, live_text = run(live, workspace)
        self.assertTrue(chosen.is_file())
        live.finish()
        self.assertEqual(
            (self.directory / "kompile/dry-run.out.spec.kore").read_text(encoding="utf-8"),
            "compiled {{work}}/input.k\ninput bytes\n",
        )
        replay_workspace = self.workspace("replay")
        replay = Snapshot(self.directory, self.key(), workspace=replay_workspace, refresh=False)
        chosen, replay_text = run(replay, replay_workspace)
        self.assertFalse(chosen.exists(), "replay writes only the declared path")
        self.assertEqual(replay_text, live_text.replace(str(workspace), str(replay_workspace)))
        replay.finish()

    def test_child_refresh_is_staged_until_the_gate_promotes_it(self) -> None:
        staging = self.base / "staging" / "oracle"
        self.assertEqual(snapshot_directory(self.directory, False, None), self.directory)
        with self.assertRaisesRegex(GateError, "--reference-staging requires --refresh-reference"):
            snapshot_directory(self.directory, False, staging)
        workspace = self.workspace("live")
        child = Snapshot(
            snapshot_directory(self.directory, True, staging), self.key(), workspace=workspace,
            refresh=True, executables=self.executables,
        )
        self.exercise(child, workspace)
        child.finish()
        self.assertFalse(self.directory.exists(), "a staged refresh leaves the committed snapshot alone")
        promotion = Promotion(staging, self.directory)
        self.assertIn("rewrote", promotion.finish())
        self.assertIn("already matched", promotion.finish())
        replay = Snapshot(self.directory, self.key(), workspace=self.workspace("replay"), refresh=False)
        self.exercise(replay, self.base / "replay")
        replay.finish()
        with self.assertRaisesRegex(GateError, "has no manifest.toml"):
            Promotion(self.base / "never-written", self.directory).finish()


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
