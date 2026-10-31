"""Cheap wiring checks for the three semantics gate entry points."""

from __future__ import annotations

from contextlib import ExitStack, redirect_stdout
from dataclasses import replace
import importlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import behavior, semantics  # noqa: E402


class RouteWiringTests(unittest.TestCase):
    def test_native_workers_load_with_the_compiled_definition_digest(self) -> None:
        cases = [{"id": "one"}, {"id": "two"}]
        with ExitStack() as patches:
            factory = patches.enter_context(mock.patch.object(behavior.krs_gate, "Session"))
            session = factory.return_value.__enter__.return_value
            session.take_chosen_values.return_value = []
            patches.enter_context(mock.patch.object(
                behavior, "native_case", side_effect=lambda _, case, __, ___: dict(case),
            ))
            outcomes, chosen = behavior.native_corpus(
                Path("gate"), Path("definition-ir.json"), "MAIN", cases, mock.Mock(), {"behavior": cases},
                definition_kore_sha256="digest", jobs=2,
            )
        self.assertEqual(outcomes, cases)
        self.assertEqual(chosen, {"one": [], "two": []})
        self.assertEqual(
            session.load.call_args_list,
            [mock.call(Path("definition-ir.json"), "MAIN", definition_kore_sha256="digest")] * 2,
        )

    def test_native_behavior_pins_each_cases_open_values(self) -> None:
        verifier = importlib.import_module("kwasm.verify")
        cases = [{"id": "two"}, {"id": "one"}]
        outcomes = [{"id": "two"}, {"id": "one"}]
        chosen = {"one": [], "two": ["MAP.keys_list order"]}

        def native(argv: list[object], **_: object) -> mock.Mock:
            arguments = [str(argument) for argument in argv]
            Path(arguments[arguments.index("--outcomes") + 1]).write_text(json.dumps(outcomes), encoding="utf-8")
            Path(arguments[arguments.index("--chosen-values") + 1]).write_text(json.dumps(chosen), encoding="utf-8")
            digest = semantics.json_sha256(outcomes)
            return mock.Mock(stdout=f"PASS native KWasm behavior: 2 executions; sha256={digest}\n")

        with tempfile.TemporaryDirectory() as temporary:
            ledger = Path(temporary) / "pins.toml"
            ledger.write_text(f'schema = 1\nbehavior_sha256 = "{semantics.json_sha256(outcomes)}"\n', encoding="utf-8")

            def behave(pins: semantics.Ledger) -> None:
                with mock.patch.object(semantics, "run", side_effect=native):
                    semantics.native_behavior(
                        verifier.PORT, Path("gate"), Path("ir"), "digest", pins, {"behavior": cases}, {},
                    )

            # A ledger without the table is an error, not an empty set.
            with self.assertRaisesRegex(semantics.GateError, "no pin implementation_chosen"):
                behave(semantics.Ledger(ledger))
            recorded = semantics.Ledger(ledger, record=True)
            behave(recorded)
            recorded.write()
            pinned = semantics.Ledger(ledger)
            self.assertEqual(list(pinned["implementation_chosen"].items()), [("two", ["MAP.keys_list order"]), ("one", [])])
            behave(pinned)
            chosen = {"one": ["MAP.keys_list order"], "two": ["MAP.keys_list order"]}
            with self.assertRaisesRegex(semantics.GateError, "implementation_chosen differs from its pin at one"):
                behave(semantics.Ledger(ledger))
            chosen = {"two": []}
            with self.assertRaisesRegex(semantics.GateError, "do not cover exactly the corpus cases"):
                behave(semantics.Ledger(ledger))

    def test_java_reference_uses_shared_expectations(self) -> None:
        verifier = importlib.import_module("kwasm.verify")
        case = {"id": "case", "program": "program"}
        observed = {"id": "case", "value": "result"}
        with ExitStack() as patches:
            patches.enter_context(mock.patch.object(
                semantics, "reference_definition", return_value=(Path("definition"), Path("spec")),
            ))
            run = patches.enter_context(mock.patch.object(
                semantics, "run", return_value=mock.Mock(stdout="term"),
            ))
            patches.enter_context(mock.patch.object(semantics, "compare_routes"))
            proof = patches.enter_context(mock.patch.object(semantics, "reference_proof"))
            gate_session = patches.enter_context(mock.patch.object(semantics.krs_gate, "Session"))
            checked = patches.enter_context(mock.patch.object(
                semantics.behavior_module, "java_case", return_value=observed,
            ))
            self.assertEqual(
                semantics.java_reference_gate(
                    verifier.PORT, verifier.HOOKS, Path("workspace"), Path("artifacts"),
                    {"kompile": "kompile", "krun": "krun", "kprove": "kprove"},
                    mock.Mock(), {"behavior": [case]}, [observed], Path("gate"), {}, "digest",
                ),
                1,
            )
        session = gate_session.return_value.__enter__.return_value
        session.load.assert_called_once_with(
                Path("artifacts/definition-ir.json"), verifier.PORT.module, definition_kore_sha256="digest",
            )
        checked.assert_called_once_with(session, case, "term", {"behavior": [case]})
        self.assertEqual(
            run.call_args.args[0],
            ["krun", "--definition", Path("definition"), "-cPGM=program", "-cSTACK=.ValStack", "--output", "kore"],
        )
        proof.assert_called_once()

    def test_kevm_java_reference_configures_each_case_in_one_session(self) -> None:
        verifier = importlib.import_module("kevm.verify")
        case = {"id": "case", "program": 'b""', "stack": ".WordStack", "pc": "0", "gas": "0"}
        observed = {"id": "case"}
        with ExitStack() as patches:
            patches.enter_context(mock.patch.object(
                semantics, "reference_definition", return_value=(Path("definition"), Path("spec")),
            ))
            run = patches.enter_context(mock.patch.object(
                semantics, "run", return_value=mock.Mock(stdout="term"),
            ))
            patches.enter_context(mock.patch.object(semantics, "compare_routes"))
            patches.enter_context(mock.patch.object(semantics, "reference_proof"))
            gate_session = patches.enter_context(mock.patch.object(semantics.krs_gate, "Session"))
            session = gate_session.return_value.__enter__.return_value
            session.configure.return_value = {
                "variables": {
                    name: {"kore": f"kore-{name}"}
                    for name in verifier.native.configuration_variables(case)
                }
            }
            checked = patches.enter_context(mock.patch.object(
                semantics.behavior_module, "java_case", return_value=observed,
            ))
            hooks = replace(verifier.HOOKS, java_skips={})
            self.assertEqual(
                semantics.java_reference_gate(
                    verifier.PORT, hooks, Path("workspace"), Path("artifacts"),
                    {"kompile": "kompile", "krun": "krun", "kprove": "kprove"},
                    mock.Mock(), {"behavior": [case]}, [observed], Path("gate"), {"KEY": "VALUE"}, "digest",
                ),
                verifier.CLAIM_COUNT,
            )
        gate_session.assert_called_once_with(Path("gate"), environment={"KEY": "VALUE"})
        session.load.assert_called_once_with(
                Path("artifacts/definition-ir.json"), verifier.PORT.module, definition_kore_sha256="digest",
            )
        session.configure.assert_called_once_with(verifier.native.configuration_variables(case))
        checked.assert_called_once_with(session, case, "term", {"behavior": [case]})
        arguments = run.call_args.args[0]
        self.assertIn("-cPGM=run", arguments)
        self.assertIn("-cPROGRAM=kore-PROGRAM", arguments)
        self.assertIn("-pPROGRAM=cat", arguments)

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
                            semantics, "format_gate", side_effect=lambda *_: phases.append("format"),
                        ))
                        patches.enter_context(mock.patch.object(
                            semantics, "artifact_gate", side_effect=lambda *_: phases.append("artifact") or artifacts,
                        ))
                        patches.enter_context(mock.patch.object(
                            semantics, "native_definition", side_effect=lambda *_: phases.append("definition") or "digest",
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
                        definition_checks = mock.Mock(side_effect=lambda *_: phases.append("checks"))
                        hooks = (
                            replace(verifier.HOOKS, definition_checks=definition_checks)
                            if has_checks
                            else verifier.HOOKS
                        )
                        arguments = ["verify.py", *(["--java-reference"] if java_reference else [])]
                        patches.enter_context(mock.patch.object(sys, "argv", arguments))

                        with redirect_stdout(io.StringIO()):
                            self.assertEqual(semantics.run_port(verifier.PORT, hooks), 0)
                        native_gate.assert_called_once()
                        if has_checks:
                            definition_checks.assert_called_once_with(artifacts, root / "krs-gate", {})
                        self.assertEqual(
                            native_gate.call_args.args[2],
                            artifacts / "definition-ir.json",
                        )
                        self.assertEqual(native_gate.call_args.args[3], "digest")
                        if java_reference:
                            reference_gate.assert_called_once()
                            self.assertIs(reference_gate.call_args.args[7], native_outcomes)
                            self.assertEqual(reference_gate.call_args.args[8], root / "krs-gate")
                            self.assertEqual(reference_gate.call_args.args[10], "digest")
                        else:
                            reference_gate.assert_not_called()
                        self.assertEqual(has_checks, port != "kwasm")
                        self.assertEqual(
                            phases,
                            [
                                "preflight", "rust", "format", "artifact",
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
            patches.enter_context(mock.patch.object(semantics, "format_gate"))
            patches.enter_context(mock.patch.object(
                semantics, "artifact_gate", return_value=root / "artifacts",
            ))
            patches.enter_context(mock.patch.object(
                semantics, "native_definition", side_effect=lambda *_: phases.append("definition") or "digest",
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

    def test_ports_emit_runs_each_gate_emission_against_that_gate_pins(self) -> None:
        imp = importlib.import_module("imp.verify")
        verifiers = {key: importlib.import_module(f"{key}.verify") for key in ("kevm", "kmir", "kwasm")}
        location = Path(__file__).resolve().parents[1] / "ports-emit/verify.py"
        spec = importlib.util.spec_from_file_location("ports_emit_verify", location)
        assert spec is not None and spec.loader is not None
        ports_emit = importlib.util.module_from_spec(spec)
        # A dataclass reads its module from `sys.modules` while the module executes.
        with mock.patch.dict(sys.modules, {spec.name: ports_emit}):
            spec.loader.exec_module(ports_emit)
        calls: list[tuple[str, Path, bool]] = []
        with ExitStack() as patches:
            patches.enter_context(mock.patch.object(
                semantics, "emission",
                side_effect=lambda port, hooks, workspace, krs, pins, gate, environment:
                    calls.append((port.key, pins.path, pins.emit_only)),
            ))
            patches.enter_context(mock.patch.object(
                imp, "emission",
                side_effect=lambda pins, workspace, krs, gate: calls.append(("imp", pins.path, pins.emit_only)),
            ))
            patches.enter_context(mock.patch.object(semantics, "build_environment", return_value={}))
            for port in ports_emit.PORTS:
                port.emission(Path("workspace"), Path("krs"), Path("gate"))
        self.assertEqual(calls, [
            ("imp", imp.PINS_PATH, True),
            *((key, verifier.PORT.pins_path, True) for key, verifier in verifiers.items()),
        ])
        self.assertEqual(ports_emit.module_path("krate", Path("lib.rs")), ["krate"])
        self.assertEqual(ports_emit.module_path("krate", Path("imp.rs")), ["krate", "imp"])
        self.assertEqual(ports_emit.module_path("krate", Path("a/mod.rs")), ["krate", "a"])
        self.assertEqual(ports_emit.module_path("krate", Path("a/b.rs")), ["krate", "a", "b"])
