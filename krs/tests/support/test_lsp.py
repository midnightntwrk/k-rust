"""Position and range contracts for shared LSP probes."""

from __future__ import annotations

from typing import Any
import unittest
from unittest import mock

from support import GateError
from support.lsp import SERVER_CANCELLED, Client, position, retrigger, token_range


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


CANCELLED = {
    "code": SERVER_CANCELLED,
    "message": "server cancelled the request",
    "data": {"retriggerRequest": True},
}


class ScriptedClient(Client):
    """A client whose server answers each request with the next scripted
    error, then with a result."""

    def __init__(self, errors: list[dict[str, Any]]) -> None:
        self.next_id = 1
        self.errors = errors
        self.sent: list[dict[str, Any]] = []
        self.pending: list[dict[str, Any]] = []

    def send(self, message: dict[str, Any]) -> None:
        self.sent.append(message)
        if self.errors:
            self.pending.append({"id": message["id"], "error": self.errors.pop(0)})
        else:
            self.pending.append({"id": message["id"], "result": {"items": []}})

    def receive(self, timeout: float) -> dict[str, Any] | None:
        return self.pending.pop(0) if self.pending else None


@mock.patch("support.lsp.time.sleep")
class RetriggerTests(unittest.TestCase):
    def test_a_cancelled_request_asking_to_be_retriggered_is_sent_again(self, _: Any) -> None:
        client = ScriptedClient([CANCELLED, CANCELLED])
        self.assertEqual(client.request("textDocument/diagnostic", {}), {"items": []})
        self.assertEqual([message["id"] for message in client.sent], [1, 2, 3])

    def test_retriggering_is_bounded(self, _: Any) -> None:
        client = ScriptedClient([CANCELLED] * 10)
        with self.assertRaises(GateError):
            client.request("textDocument/diagnostic", {})
        self.assertEqual(len(client.sent), 6)

    def test_other_errors_fail_at_once(self, _: Any) -> None:
        for error in (
            {"code": SERVER_CANCELLED, "message": "cancelled", "data": {"retriggerRequest": False}},
            {"code": SERVER_CANCELLED, "message": "cancelled"},
            {"code": -32603, "message": "internal error"},
        ):
            client = ScriptedClient([error])
            with self.assertRaises(GateError):
                client.request("textDocument/hover", {})
            self.assertEqual(len(client.sent), 1)
            self.assertFalse(retrigger(error))


if __name__ == "__main__":
    unittest.main()
