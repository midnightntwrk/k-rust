"""Cheap wiring checks for the three semantics gate entry points."""

from __future__ import annotations

from contextlib import ExitStack, redirect_stdout
import importlib
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))


class RouteWiringTests(unittest.TestCase):
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
                        patches.enter_context(mock.patch.object(verifier, "Ledger", return_value=ledger))
                        patches.enter_context(mock.patch.object(verifier, "load_toml", return_value=corpus))
                        patches.enter_context(mock.patch.object(verifier, "scratch_root", return_value=root))
                        patches.enter_context(mock.patch.object(verifier, "krs_ir_schema", return_value=1))
                        patches.enter_context(mock.patch.object(verifier.semantics, "preflight", return_value={}))
                        patches.enter_context(mock.patch.object(
                            verifier.semantics, "rust_gate",
                            return_value=(root / "krs", root / "compiler", root / "runner"),
                        ))
                        patches.enter_context(mock.patch.object(
                            verifier.semantics, "artifact_gate", return_value=artifacts,
                        ))
                        patches.enter_context(mock.patch.object(
                            verifier.semantics, "native_definition", return_value=root / "definition.kore",
                        ))
                        native_gate = patches.enter_context(mock.patch.object(
                            verifier.semantics, "native_behavior", return_value=(1, native_outcomes),
                        ))
                        reference_gate = patches.enter_context(mock.patch.object(
                            verifier, "java_reference_gate", autospec=True, return_value=1,
                        ))
                        patches.enter_context(mock.patch.object(verifier, "k_tool", side_effect=lambda name, _: name))
                        patches.enter_context(mock.patch.object(verifier, "k_version", return_value="7.1.337"))
                        if hasattr(verifier, "definition_checks"):
                            patches.enter_context(mock.patch.object(verifier, "definition_checks"))
                        arguments = ["verify.py", *(["--java-reference"] if java_reference else [])]
                        patches.enter_context(mock.patch.object(sys, "argv", arguments))

                        with redirect_stdout(io.StringIO()):
                            self.assertEqual(verifier.main(), 0)
                        native_gate.assert_called_once()
                        if java_reference:
                            reference_gate.assert_called_once()
                            self.assertIs(reference_gate.call_args.args[-1], native_outcomes)
                        else:
                            reference_gate.assert_not_called()
                        ledger.finish.assert_called_once()
