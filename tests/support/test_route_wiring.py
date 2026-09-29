"""Cheap wiring checks for the three semantics gate entry points."""

from __future__ import annotations

from contextlib import ExitStack, redirect_stdout
from dataclasses import replace
import importlib
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import semantics  # noqa: E402


class RouteWiringTests(unittest.TestCase):
    def test_java_reference_uses_port_hooks(self) -> None:
        verifier = importlib.import_module("kwasm.verify")
        case = {"id": "case", "program": "program"}
        observed = {"id": "case", "value": "result"}
        calls: list[str] = []
        hooks = replace(
            verifier.HOOKS,
            krun_arguments=lambda _: calls.append("arguments") or ["-cPGM=program"],
            observed=lambda _, state: calls.append("observed") or observed,
            checked=lambda _, outcome: calls.append("checked") if outcome is observed else None,
        )
        with ExitStack() as patches:
            patches.enter_context(mock.patch.object(
                semantics, "reference_definition", return_value=(Path("definition"), Path("spec")),
            ))
            run = patches.enter_context(mock.patch.object(
                semantics, "run", return_value=mock.Mock(stdout="term"),
            ))
            patches.enter_context(mock.patch.object(semantics, "parse_kore_pattern", return_value={}))
            patches.enter_context(mock.patch.object(semantics, "compare_routes"))
            proof = patches.enter_context(mock.patch.object(semantics, "reference_proof"))
            self.assertEqual(
                semantics.java_reference_gate(
                    verifier.PORT, hooks, Path("workspace"), Path("artifacts"),
                    {"kompile": "kompile", "krun": "krun", "kprove": "kprove"},
                    mock.Mock(), {"behavior": [case]}, [observed],
                ),
                1,
            )
        self.assertEqual(calls, ["arguments", "observed", "checked"])
        self.assertEqual(
            run.call_args.args[0],
            ["krun", "--definition", Path("definition"), "-cPGM=program", "--output", "kore"],
        )
        proof.assert_called_once()

    def test_native_outcomes_reach_each_java_reference_gate(self) -> None:
        for port in ("kevm", "kmir", "kwasm"):
            verifier = importlib.import_module(f"{port}.verify")
            for java_reference in (False, True):
                with self.subTest(port=port, java_reference=java_reference):
                    with tempfile.TemporaryDirectory() as temporary, ExitStack() as patches:
                        root = Path(temporary)
                        artifacts = root / "artifacts"
                        artifacts.mkdir()
                        (artifacts / "definition.k").write_text("module TEST\nendmodule\n", encoding="utf-8")
                        corpus = {"behavior": [{"id": "case"}]}
                        native_outcomes = [{"id": "case", "value": "result"}]
                        ledger = mock.Mock()
                        phases: list[str] = []
                        patches.enter_context(mock.patch.object(semantics, "Ledger", return_value=ledger))
                        patches.enter_context(mock.patch.object(semantics, "load_toml", return_value=corpus))
                        patches.enter_context(mock.patch.object(semantics, "scratch_root", return_value=root))
                        patches.enter_context(mock.patch.object(semantics, "preflight", side_effect=lambda *_: phases.append("preflight") or {}))
                        patches.enter_context(mock.patch.object(
                            semantics, "rust_gate",
                            side_effect=lambda *_: phases.append("rust") or (root / "krs", root / "krs-gate"),
                        ))
                        patches.enter_context(mock.patch.object(
                            semantics, "artifact_gate", side_effect=lambda *_: phases.append("artifact") or artifacts,
                        ))
                        patches.enter_context(mock.patch.object(
                            semantics, "native_definition", side_effect=lambda *_: phases.append("definition") or root / "definition.kore",
                        ))
                        native_gate = patches.enter_context(mock.patch.object(
                            semantics, "native_behavior",
                            side_effect=lambda *_: phases.append("behavior") or (1, native_outcomes),
                        ))
                        reference_gate = patches.enter_context(mock.patch.object(
                            semantics, "java_reference_gate", autospec=True,
                            side_effect=lambda *_: phases.append("reference") or 1,
                        ))
                        patches.enter_context(mock.patch.object(semantics, "k_tool", side_effect=lambda name, _: name))
                        patches.enter_context(mock.patch.object(semantics, "k_version", return_value="7.1.337"))
                        has_checks = verifier.HOOKS.definition_checks is not None
                        hooks = (
                            replace(verifier.HOOKS, definition_checks=lambda _: phases.append("checks"))
                            if has_checks
                            else verifier.HOOKS
                        )
                        arguments = ["verify.py", *(["--java-reference"] if java_reference else [])]
                        patches.enter_context(mock.patch.object(sys, "argv", arguments))

                        with redirect_stdout(io.StringIO()):
                            self.assertEqual(semantics.run_port(verifier.PORT, hooks), 0)
                        native_gate.assert_called_once()
                        if java_reference:
                            reference_gate.assert_called_once()
                            self.assertIs(reference_gate.call_args.args[-1], native_outcomes)
                        else:
                            reference_gate.assert_not_called()
                        self.assertEqual(has_checks, port != "kwasm")
                        self.assertEqual(
                            phases,
                            [
                                "preflight", "rust", "artifact",
                                *(["checks"] if has_checks else []),
                                "definition", "behavior",
                                *(["reference"] if java_reference else []),
                            ],
                        )
                        ledger.finish.assert_called_once()

    def test_artifacts_only_stops_after_definition(self) -> None:
        verifier = importlib.import_module("kwasm.verify")
        with tempfile.TemporaryDirectory() as temporary, ExitStack() as patches:
            root = Path(temporary)
            ledger = mock.Mock()
            phases: list[str] = []
            patches.enter_context(mock.patch.object(semantics, "Ledger", return_value=ledger))
            patches.enter_context(mock.patch.object(semantics, "load_toml", return_value={}))
            patches.enter_context(mock.patch.object(semantics, "scratch_root", return_value=root))
            patches.enter_context(mock.patch.object(semantics, "preflight", return_value={}))
            patches.enter_context(mock.patch.object(
                semantics, "rust_gate", return_value=(root / "krs", root / "krs-gate"),
            ))
            patches.enter_context(mock.patch.object(
                semantics, "artifact_gate", return_value=root / "artifacts",
            ))
            patches.enter_context(mock.patch.object(
                semantics, "native_definition", side_effect=lambda *_: phases.append("definition") or root / "definition",
            ))
            native_gate = patches.enter_context(mock.patch.object(semantics, "native_behavior"))
            reference_gate = patches.enter_context(mock.patch.object(semantics, "java_reference_gate"))
            patches.enter_context(mock.patch.object(sys, "argv", ["verify.py", "--artifacts-only"]))
            with redirect_stdout(io.StringIO()):
                self.assertEqual(semantics.run_port(verifier.PORT, verifier.HOOKS), 0)
            self.assertEqual(phases, ["definition"])
            native_gate.assert_not_called()
            reference_gate.assert_not_called()
            ledger.finish.assert_not_called()
