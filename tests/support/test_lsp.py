"""Position and range contracts for shared LSP probes."""

from __future__ import annotations

import unittest

from support import GateError
from support.lsp import position, token_range


class PositionTests(unittest.TestCase):
    def test_fragment_and_needle_occurrences(self) -> None:
        lines = ["Foo(x) Foo(y)", "Foo(a) Foo(b)"]
        self.assertEqual(position(lines, "Foo", "Foo", occurrence=1), {"line": 1, "character": 1})
        self.assertEqual(
            position(lines, "Foo", "Foo", occurrence=1, needle_occurrence=1, offset=0),
            {"line": 1, "character": 7},
        )

    def test_non_bmp_prefix_counts_two_utf16_units(self) -> None:
        self.assertEqual(position(["😀 Foo(x)"], "Foo", "x"), {"line": 0, "character": 8})

    def test_missing_occurrence_fails(self) -> None:
        with self.assertRaises(GateError):
            position(["Foo(x)"], "Foo", "x", occurrence=1)
        with self.assertRaises(GateError):
            position(["Foo(x)"], "Foo", "x", needle_occurrence=1)


class TokenRangeTests(unittest.TestCase):
    def test_non_bmp_prefix_and_token(self) -> None:
        self.assertEqual(
            token_range("before\n😀 #[mark] x😀y", "x😀y", after="#[mark]"),
            {
                "start": {"line": 1, "character": 11},
                "end": {"line": 1, "character": 15},
            },
        )

    def test_marker_selects_later_token(self) -> None:
        self.assertEqual(
            token_range("syntax\n#[k::constructor(syntax)]", "syntax", after="#[k::constructor"),
            {"start": {"line": 1, "character": 17}, "end": {"line": 1, "character": 23}},
        )
        with self.assertRaises(GateError):
            token_range("syntax", "syntax", after="constructor")


if __name__ == "__main__":
    unittest.main()
