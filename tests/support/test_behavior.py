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

    @staticmethod
    def _search_session(searches: dict[str, list[str]]) -> mock.Mock:
        session = mock.Mock()
        session.configure.return_value = {"pattern": "opaque"}

        def execute(_: str, **options: object) -> dict[str, object]:
            if "keep" in options:
                return {"leaves": [{"reason": "stuck"}]}
            if options.get("max_depth") == 2:
                return {"leaves": [{"state": "bounded", "depth": 2}]}
            return {"leaves": [{"state": "final", "depth": 3}]}

        def search(_: str, **options: object) -> dict[str, object]:
            if "keep" in options:
                return {"states": 1}
            key = ",".join(f"{name}={value}" for name, value in options.items())
            return {"states": [{"state": state} for state in searches.get(key, ["final"])]}

        session.execute.side_effect = execute
        session.search.side_effect = search
        return session

    def test_search_checks_bounds_against_execution_and_rechecks_the_kept_state(self) -> None:
        corpus = {"expect": {"cell": "value"}, "report": {"cell": "field"}}
        case = {"id": "sample", "search": True, "observe": ["cell"]}
        session = self._search_session({"max_results=0": [], "max_depth=2": ["bounded"]})
        self.assertEqual(behavior.native_case(session, case, self.spec, corpus), {"id": "sample", "field": "value"})
        self.assertEqual(session.execute.call_args_list, [
            mock.call("opaque", keep="case"), mock.call("opaque"), mock.call("opaque", max_depth=2),
        ])
        self.assertEqual(session.search.call_args_list, [
            mock.call("opaque"), mock.call("opaque", max_results=1), mock.call("opaque", max_depth=3),
            mock.call("opaque", max_results=0), mock.call("opaque", max_depth=2),
            mock.call("opaque", keep="search"),
        ])
        self.assertEqual(session.expect.call_args_list, [
            mock.call(state, "cell", text="value", size=None, head=None) for state in ("case", "search")
        ])

    def test_search_rejects_ignored_bounds_and_disagreement(self) -> None:
        bounded = {"max_results=0": [], "max_depth=2": ["bounded"]}
        for searches, count in (
            ({**bounded, "": ["other"]}, "1 states other than the 1 expected"),
            ({**bounded, "max_results=1": ["final", "other"]}, "2 states other than the 1 expected"),
            ({"max_depth=2": ["bounded"]}, "1 states other than the 0 expected"),
            ({"max_results=0": []}, "1 states other than the 1 expected"),
        ):
            with self.subTest(searches=searches), self.assertRaisesRegex(GateError, f"sample: search .*{count}"):
                behavior.native_case(self._search_session(searches), {"id": "sample", "search": True}, self.spec, {})

    def test_search_requires_one_leaf_reached_in_a_step(self) -> None:
        session = mock.Mock()
        session.configure.return_value = {"pattern": "opaque"}
        for leaves, message in (
            ([{"state": "a", "depth": 1}, {"state": "b", "depth": 1}], "exactly one execution leaf, got 2"),
            ([{"state": "final", "depth": 0}], "at least one step"),
            ([{"state": "final", "depth": 1}], "depth 0 already reached the final state"),
        ):
            session.execute.return_value = {"leaves": leaves}
            with self.subTest(leaves=leaves), self.assertRaisesRegex(GateError, f"sample: .*{message}"):
                behavior.native_case(session, {"id": "sample", "search": True}, self.spec, {})
        session.search.assert_not_called()

    def test_malformed_search_flag_is_rejected_before_running(self) -> None:
        for route in ("native", "java"):
            session = mock.Mock()
            with self.subTest(route=route), self.assertRaisesRegex(GateError, "sample: search must be a boolean"):
                case = {"id": "sample", "search": "yes"}
                if route == "native":
                    behavior.native_case(session, case, self.spec, {})
                else:
                    behavior.java_case(session, case, self.spec, "opaque java", {})
            self.assertEqual(session.method_calls, [])

    def test_structural_failure_names_case(self) -> None:
        session = mock.Mock()
        session.expect.side_effect = GateError("mismatch")
        with self.assertRaisesRegex(GateError, "sample: mismatch"):
            behavior.check_case(session, {"id": "sample", "expect": {"cell": "value"}}, self.spec, {})
