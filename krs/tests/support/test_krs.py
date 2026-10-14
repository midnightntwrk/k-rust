"""Contract tests for KRS build and invocation orchestration."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from support import GateError, ROOT
from support import krs


class BuildTests(unittest.TestCase):
    def test_builds_in_the_tool_target_whatever_the_caller_target(self) -> None:
        binary = Path("/tools/debug/krs")
        with (
            patch.object(krs.tools, "z3_environment", return_value={"LIBRARY_PATH": "z3"}),
            patch.object(krs.tools, "workspace_debug_binary", return_value=binary),
            patch.object(krs.process, "run") as runner,
            patch.object(Path, "is_file", return_value=True),
        ):
            self.assertEqual(krs.build({"CARGO_NET_OFFLINE": "true", "CARGO_TARGET_DIR": "/gate/fixtures"}), binary)
        runner.assert_called_once_with(
            ["cargo", "+stable", "build", "--locked", "-p", "krs-cli", "--bin", "krs"],
            cwd=ROOT,
            environment={"LIBRARY_PATH": "z3", "CARGO_NET_OFFLINE": "true", "CARGO_TARGET_DIR": "/tools"},
            timeout=600,
        )

    def test_caller_environment_layers_over_z3_and_missing_binary_fails(self) -> None:
        with (
            patch.object(krs.tools, "z3_environment", return_value={"LIBRARY_PATH": "z3"}),
            patch.object(krs.tools, "workspace_debug_binary", return_value=Path("/tools/debug/krs")),
            patch.object(krs.process, "run") as runner,
            patch.object(Path, "is_file", return_value=False),
        ):
            with self.assertRaisesRegex(GateError, "did not produce"):
                krs.build({"LIBRARY_PATH": "caller"}, timeout=27)
        self.assertEqual(
            runner.call_args.kwargs["environment"],
            {"LIBRARY_PATH": "caller", "CARGO_TARGET_DIR": "/tools"},
        )
        self.assertEqual(runner.call_args.kwargs["timeout"], 27)


class ToolTargetTests(unittest.TestCase):
    def test_tool_target_prefers_krs_tool_target_then_cargo_target_dir(self) -> None:
        from support import REPOSITORY, tools

        with patch.dict(krs.os.environ, {}, clear=True):
            self.assertEqual(tools.tool_target(), REPOSITORY / "target")
        with patch.dict(krs.os.environ, {"CARGO_TARGET_DIR": "/shared"}, clear=True):
            self.assertEqual(tools.tool_target(), Path("/shared"))
        with patch.dict(krs.os.environ, {"CARGO_TARGET_DIR": "/shared", "KRS_TOOL_TARGET": "/tools"}, clear=True):
            self.assertEqual(tools.tool_target(), Path("/tools"))


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


class FreshEmissionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.workspace = Path(self.temporary.name)
        self.invocation = krs.Invocation(Path("/bin/krs"), Path("/src/Cargo.toml"), "fixture", "main")

    def runner(self, argv: list[str], **_kwargs: object) -> None:
        output = Path(argv[argv.index("--output") + 1])
        output.mkdir()
        (output / ".krs-artifacts").write_bytes(b"marker")
        (output / "definition.k").write_bytes(b"definition")
        counters = {
            "schema": "krs-counters/1",
            "command": "emit-k",
            "status": "ok",
            "counters": {"result.reused": int("--no-reuse" not in argv)},
        }
        Path(argv[argv.index("--counters") + 1]).write_text(json.dumps(counters), encoding="utf-8")

    def test_two_fresh_runs_and_reuse_enabled_replay(self) -> None:
        with patch.object(krs.process, "run", side_effect=self.runner) as runner:
            self.assertEqual(
                krs.fresh_deterministic_emissions(
                    self.invocation, self.workspace,
                    extra=("--backend", "haskell"), environment={"CARGO_TARGET_DIR": "/target"},
                    timeout=300,
                ),
                (self.workspace / "emit-a", self.workspace / "emit-b"),
            )
        self.assertEqual(runner.call_count, 3)
        for index, call in enumerate(runner.call_args_list):
            argv = call.args[0]
            name = ("emit-a", "emit-b", "emit-replay")[index]
            self.assertEqual(argv[:2], ["/bin/krs", "emit-k"])
            self.assertEqual(argv[argv.index("--backend") + 1], "haskell")
            self.assertEqual(argv[argv.index("--output") + 1], str(self.workspace / name))
            self.assertEqual(argv[argv.index("--counters") + 1], str(self.workspace / f"{name}.krs-counters.json"))
            self.assertEqual("--no-reuse" in argv, index < 2)
            self.assertEqual(call.kwargs["timeout"], 300)
            self.assertEqual(call.kwargs["environment"], {"CARGO_TARGET_DIR": "/target", "KRS_NO_REUSE": "0"})

    def test_reused_counter_mismatch_fails(self) -> None:
        def wrong_reuse(argv: list[str], **kwargs: object) -> None:
            self.runner(argv, **kwargs)
            if "emit-replay" in argv[argv.index("--output") + 1]:
                counters = Path(argv[argv.index("--counters") + 1])
                document = json.loads(counters.read_text(encoding="utf-8"))
                document["counters"]["result.reused"] = 0
                counters.write_text(json.dumps(document), encoding="utf-8")

        with patch.object(krs.process, "run", side_effect=wrong_reuse):
            with self.assertRaisesRegex(GateError, r"emit-replay counters.*result\.reused == 1"):
                krs.fresh_deterministic_emissions(self.invocation, self.workspace)

    def test_fresh_counter_mismatch_fails(self) -> None:
        def wrong_fresh(argv: list[str], **kwargs: object) -> None:
            self.runner(argv, **kwargs)
            if "emit-a" in argv[argv.index("--output") + 1]:
                counters = Path(argv[argv.index("--counters") + 1])
                document = json.loads(counters.read_text(encoding="utf-8"))
                document["counters"]["result.reused"] = 1
                counters.write_text(json.dumps(document), encoding="utf-8")

        with patch.object(krs.process, "run", side_effect=wrong_fresh) as runner:
            with self.assertRaisesRegex(GateError, r"emit-a counters.*result\.reused == 0"):
                krs.fresh_deterministic_emissions(self.invocation, self.workspace)
        runner.assert_called_once()

    def test_replay_differing_file_fails(self) -> None:
        def changed_replay(argv: list[str], **kwargs: object) -> None:
            self.runner(argv, **kwargs)
            if "emit-replay" in argv[argv.index("--output") + 1]:
                output = Path(argv[argv.index("--output") + 1])
                (output / ".krs-artifacts").write_bytes(b"changed")

        with patch.object(krs.process, "run", side_effect=changed_replay):
            with self.assertRaisesRegex(GateError, r"cached replay differs byte-for-byte: \.krs-artifacts"):
                krs.fresh_deterministic_emissions(self.invocation, self.workspace)

    def test_replay_file_set_fails(self) -> None:
        def extra_replay_file(argv: list[str], **kwargs: object) -> None:
            self.runner(argv, **kwargs)
            if "emit-replay" in argv[argv.index("--output") + 1]:
                output = Path(argv[argv.index("--output") + 1])
                (output / "extra.json").write_bytes(b"extra")

        with patch.object(krs.process, "run", side_effect=extra_replay_file):
            with self.assertRaisesRegex(GateError, "cached replay differs byte-for-byte: extra.json"):
                krs.fresh_deterministic_emissions(self.invocation, self.workspace)


if __name__ == "__main__":
    unittest.main()
