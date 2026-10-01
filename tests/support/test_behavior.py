"""Declaration resolution and shared retained-state checks."""

from __future__ import annotations

import unittest
from unittest import mock

from support import GateError, behavior


class BehaviorTests(unittest.TestCase):
    def setUp(self) -> None:
        self.spec = behavior.Specification(lambda _: {"PGM": "input"})

    def test_defaults_overrides_and_first_seen_order(self) -> None:
        corpus = {
            "observe": ["first", "second", "first"],
            "expect": {"first": "default", "second": {"size": 0}, "extra": {"head": "head"}},
        }
        case = {
            "id": "sample", "observe": ["extra", "second", "extra"],
            "expect": {"second": {"size": 2}, "last": "last value", "first": "override"},
        }
        self.assertEqual(behavior.expectations(corpus, case), [
            behavior.Expectation("first", text="override"),
            behavior.Expectation("second", size=2),
            behavior.Expectation("extra", head="head"),
            behavior.Expectation("last", text="last value"),
        ])

    def test_defaults_do_not_implicitly_observe_cells(self) -> None:
        self.assertEqual(behavior.expectations({"expect": {"unused": "value"}}, {"id": "sample"}), [])
        self.assertEqual(behavior.outcome_record({}, {"id": "sample"}, self.spec), {"id": "sample"})

    def test_missing_expectation_names_case_and_cell(self) -> None:
        for corpus, case in (
            ({"observe": ["missing"]}, {"id": "sample"}),
            ({}, {"id": "sample", "observe": ["missing"]}),
        ):
            with self.subTest(corpus=corpus), self.assertRaisesRegex(GateError, "sample.*missing"):
                behavior.expectations(corpus, case)

    def test_malformed_expectations(self) -> None:
        for value in ({}, {"text": "value"}, {"head": 1}, {"size": "1"}, {"size": True},
                      {"size": -1}, {"size": 1, "head": "value"}, 1, ["value"]):
            for source in ("corpus", "case"):
                with self.subTest(value=value, source=source), self.assertRaisesRegex(
                    GateError, "sample.*malformed expectation.*cell broken",
                ):
                    declarations = {"expect": {"broken": value}}
                    corpus = declarations if source == "corpus" else {}
                    case = {"id": "sample", **(declarations if source == "case" else {})}
                    behavior.expectations(corpus, case)

    def test_report_values_and_hook(self) -> None:
        corpus = {"report": {"textual": "text", "count": "size", "leading": "head", "unused": "absent"}}
        case = {"id": "sample", "expect": {
            "textual": "surface", "count": {"size": 0}, "leading": {"head": "prefix"}, "silent": "checked",
        }}
        record = {"id": "sample", "text": "surface", "size": 0, "head": "prefix"}
        self.assertEqual(behavior.outcome_record(corpus, case, self.spec), record)
        hook = mock.Mock(side_effect=lambda _, value: {**value, "extra": "refined"})
        spec = behavior.Specification(self.spec.variables, hook)
        self.assertEqual(behavior.outcome_record(corpus, case, spec), {**record, "extra": "refined"})
        hook.assert_called_once_with(case, record)

    def test_native_and_java_check_same_declarations(self) -> None:
        corpus = {"observe": ["cell"], "expect": {"cell": "value"}, "report": {"cell": "field"}, "reason": "stuck"}
        case = {"id": "sample"}
        native, java = mock.Mock(), mock.Mock()
        native.configure.return_value = {"pattern": "opaque"}
        native.execute.return_value = {"leaves": [{"reason": "stuck"}]}
        result = behavior.native_case(native, case, self.spec, corpus)
        self.assertEqual(result, {"id": "sample", "field": "value"})
        self.assertEqual(behavior.java_case(java, case, self.spec, "opaque java", corpus), result)
        native.configure.assert_called_once_with({"PGM": "input"})
        native.execute.assert_called_once_with("opaque", keep="case")
        java.read.assert_called_once_with("opaque java", "case")
        self.assertEqual(native.expect.call_args_list, java.expect.call_args_list)
        native.expect.assert_called_once_with("case", "cell", text="value", size=None, head=None)

    def test_native_reason_requires_one_matching_leaf(self) -> None:
        case = {"id": "sample"}
        session = mock.Mock()
        session.configure.return_value = {"pattern": "opaque"}
        for leaves in ([], [{"reason": "depth-bound"}], [{"reason": "stuck"}] * 2):
            session.execute.return_value = {"leaves": leaves}
            with self.subTest(leaves=leaves), self.assertRaisesRegex(GateError, "sample.*reason stuck"):
                behavior.native_case(session, case, self.spec, {"reason": "stuck"})
        session.expect.assert_not_called()

    def test_structural_failure_names_case(self) -> None:
        session = mock.Mock()
        session.expect.side_effect = GateError("mismatch")
        with self.assertRaisesRegex(GateError, "sample: mismatch"):
            behavior.check_case(session, {"id": "sample", "expect": {"cell": "value"}}, self.spec, {})
