"""Depth checks for the KORE observers used by the KEVM reference route."""

from __future__ import annotations

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from kevm import native  # noqa: E402


def app(name: str, *args: dict[str, object]) -> dict[str, object]:
    return {"tag": "App", "name": name, "sorts": [], "args": list(args)}


def integer(value: str) -> dict[str, object]:
    return {"tag": "DV", "sort": {"tag": "SortApp", "name": "SortInt", "args": []}, "value": value}


class KevmWalkerTests(unittest.TestCase):
    def test_collection_walkers_preserve_left_to_right_order(self) -> None:
        list_term = app(
            "Lbl'Unds'List'Unds'",
            app("LblListItem", integer("1")),
            app("LblListItem", integer("2")),
        )
        set_term = app(
            "Lbl'Unds'Set'Unds'",
            app("LblSetItem", integer("1")),
            app("LblSetItem", integer("2")),
        )
        map_term = app(
            "Lbl'Unds'Map'Unds'",
            app("Lbl'UndsPipe'-'-GT-Unds'", integer("1"), integer("3")),
            app("Lbl'UndsPipe'-'-GT-Unds'", integer("2"), integer("4")),
        )
        self.assertEqual(
            [native.domain_value(item, "Int") for item in native.list_values(list_term)],
            ["1", "2"],
        )
        self.assertEqual(native.set_values(set_term), ["1", "2"])
        self.assertEqual(
            [
                (native.domain_value(key, "Int"), native.domain_value(value, "Int"))
                for key, value in native.map_items(map_term)
            ],
            [("1", "3"), ("2", "4")],
        )

    def test_deep_word_stack_and_cell_search(self) -> None:
        stack = app("LblstackEmpty")
        for _ in range(1_024):
            stack = app("LblstackCons", integer("1"), stack)
        self.assertEqual(native.word_stack(stack).count("1:"), 1_024)
        wrapped = app("Lbl'-LT-'wordStack'-GT-'", stack)
        for _ in range(1_024):
            wrapped = app("Lblwrapper", wrapped)
        self.assertIs(native.cell(wrapped, "wordStack"), stack)

    def test_deep_collections_and_injections(self) -> None:
        value = integer("7")
        for _ in range(1_024):
            value = app("inj", value)
        self.assertEqual(native.domain_value(native.unwrap_injection(value), "Int"), "7")

        list_term = app("Lbl'Stop'List")
        set_term = app("Lbl'Stop'Set")
        map_term = app("Lbl'Stop'Map")
        for _ in range(1_500):
            list_term = app("Lbl'Unds'List'Unds'", app("LblListItem", integer("7")), list_term)
            set_term = app("Lbl'Unds'Set'Unds'", app("LblSetItem", integer("7")), set_term)
            map_term = app("Lbl'Unds'Map'Unds'", app("Lbl'UndsPipe'-'-GT-Unds'", integer("7"), integer("8")), map_term)
        self.assertEqual(len(native.list_values(list_term)), 1_500)
        self.assertEqual(len(native.set_values(set_term)), 1_500)
        self.assertEqual(len(native.map_items(map_term)), 1_500)
