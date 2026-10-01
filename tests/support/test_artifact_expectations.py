"""Typed artifact expectation comparison and application-pattern forwarding."""

from __future__ import annotations

from contextlib import ExitStack
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError, semantics  # noqa: E402


class ArtifactExpectationTests(unittest.TestCase):
    def check(self, expected: dict, vocabulary: dict, *, applications: list | None = None):
        with ExitStack() as patches:
            patches.enter_context(mock.patch.object(
                semantics, "load_toml", return_value={"check": [{"message": "construct missing", **expected}]},
            ))
            factory = patches.enter_context(mock.patch.object(semantics.krs_gate, "Session"))
            session = factory.return_value.__enter__.return_value
            session.ir_query.side_effect = [vocabulary, {"rows": applications or []}]
            semantics.definition_expectations(Path("artifacts"), Path("gate"), Path("checks.toml"), {})
            return session.ir_query.call_args_list

    @staticmethod
    def vocabulary() -> dict:
        return {
            "sorts": ["Expression"], "production_symbols": ["constructor"],
            "terminals": ["make"], "rule_labels": ["evaluate"], "imports": ["INT"],
            "cells": [{"name": "state", "configuration_variable": "STATE", "sort": "Int"}],
            "subsorts": [{"sort": "Expression", "subsort": "Int"}],
            "applied_operations": [{"operation": "int_add", "result_sort": "Int", "argument_sorts": ["Int", "Int"]}],
        }

    def test_required_and_forbidden_facets(self) -> None:
        self.check({"required": {"sorts": ["Expression"]}, "forbidden": {"cell_names": ["adapter"]}}, self.vocabulary())
        with self.assertRaisesRegex(GateError, "missing sorts.*Unknown"):
            self.check({"required": {"sorts": ["Unknown"]}}, self.vocabulary())
        with self.assertRaisesRegex(GateError, "forbidden rule_labels.*evaluate"):
            self.check({"forbidden": {"rule_labels": ["evaluate"]}}, self.vocabulary())

    def test_typed_rows_require_every_expected_field(self) -> None:
        for facet, row in (
            ("cells", {"name": "state", "sort": "Int"}),
            ("subsorts", {"sort": "Expression", "subsort": "Int"}),
            ("applied_operations", {"operation": "int_add", "argument_sorts": ["Int", "Int"]}),
        ):
            with self.subTest(facet=facet):
                self.check({facet: [row]}, self.vocabulary())
                wrong = {**row, "sort" if facet != "applied_operations" else "argument_sorts": "Wrong"}
                with self.assertRaisesRegex(GateError, "missing.*row"):
                    self.check({facet: [wrong]}, self.vocabulary())

    def test_nested_pattern_is_forwarded_to_rust(self) -> None:
        pattern = {"symbol": "pair", "arguments": [{"token": "1"}, {}]}
        calls = self.check({"applications": [pattern]}, self.vocabulary(), applications=[{"symbol": "pair"}])
        self.assertEqual(calls, [
            mock.call(Path("artifacts"), {"kind": "vocabulary"}),
            mock.call(Path("artifacts"), {"kind": "applications", **pattern}),
        ])
        with self.assertRaisesRegex(GateError, "missing application"):
            self.check({"applications": [pattern]}, self.vocabulary())


if __name__ == "__main__":
    unittest.main()
