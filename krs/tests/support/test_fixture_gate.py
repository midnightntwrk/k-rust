"""Contract tests for the fixture harness's native route: which programs pin their open values."""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest

from support import GateError
from support.fixture_gate import Emitted, Fixture, FixtureGate, Program
from support.pins import Ledger


# Each program text names its behaviour: `reject` fails to parse, `refuse` is refused by
# `execute`, and every other text runs to one leaf; a text with `marked` is marked by each
# run and search (`MAP.keys_list order` by `execute`, `MAP.keys_list order` and
# `STRING.base2string letter-case` by `search`).
FAKE_GATE = """\
import json
import sys

assert sys.argv[1:] == ["session"]
order = {"hook": "MAP.keys_list", "class": "order"}
case = {"hook": "STRING.base2string", "class": "letter-case"}
for line in sys.stdin:
    request = json.loads(line)
    operation, result = request["operation"], {}
    if operation == "configure":
        text = request["variables"]["PGM"]
        if text == "reject":
            print(json.dumps({"id": request["id"], "error": {"message": "parse error"}}), flush=True)
            continue
        result = {"pattern": text}
    elif operation == "execute":
        if request["pattern"] == "refuse":
            print(json.dumps({"id": request["id"], "error": {"message": "refused"}}), flush=True)
            continue
        result = {"leaves": [{"reason": "stuck"}]}
        if "marked" in request["pattern"]:
            result["implementationChosenValues"] = [order]
    elif operation == "search":
        result = {"states": 1}
        if "marked" in request["pattern"]:
            result["implementationChosenValues"] = [order, case]
    elif operation == "expect":
        result = {"met": True}
    print(json.dumps({"id": request["id"], "result": result}), flush=True)
"""


class NativeOutcomeTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.binary = self.directory / "fake-gate"
        self.binary.write_text(f"#!{sys.executable}\n{FAKE_GATE}", encoding="utf-8")
        self.binary.chmod(0o755)
        self.ledger = self.directory / "pins.json"
        self.ledger.write_text("{}\n", encoding="utf-8")
        self.emitted = Emitted(Fixture(self.directory / "Cargo.toml", "pkg"), self.directory, "MAIN")
        self.programs = [
            Program("rejected", "reject", "rejected"),
            Program("parse-only", "parse", "accepted"),
            Program("refused", "refuse", "accepted", run="done"),
            Program("plain", "plain", "accepted", run="done"),
            Program("marked", "marked", "accepted", run="done"),
            Program("searched", "marked search", "accepted", search=("done",)),
        ]

    def outcomes(self, pins: Ledger) -> dict[str, dict]:
        gate = FixtureGate("test", pins, self.directory, Path("krs"), self.binary, {})
        return gate._native_outcomes(self.emitted, self.programs)

    def test_every_program_that_runs_pins_its_own_open_values(self) -> None:
        recorded = Ledger(self.ledger, record=True)
        outcomes = self.outcomes(recorded)
        self.assertEqual(outcomes["rejected"], {"parse": "rejected", "run": None})
        self.assertEqual(outcomes["refused"], {"parse": "accepted", "run": "refused: refused"})
        self.assertEqual(outcomes["searched"], {"parse": "accepted", "run": None, "search": ["done"]})
        recorded.write()
        pinned = Ledger(self.ledger)
        # No entry for a program that does not parse or that only parses; a refused run is an
        # empty set; the marked run's set is not carried into the next program's.
        self.assertEqual(pinned["implementation_chosen"], {"pkg": {
            "refused": [],
            "plain": [],
            "marked": ["MAP.keys_list order"],
            "searched": ["MAP.keys_list order", "STRING.base2string letter-case"],
        }})
        self.outcomes(pinned)

    def test_an_absent_or_changed_table_fails(self) -> None:
        with self.assertRaisesRegex(GateError, "no pin implementation_chosen.pkg"):
            self.outcomes(Ledger(self.ledger))
        recorded = Ledger(self.ledger, record=True)
        self.outcomes(recorded)
        recorded.write()
        self.programs[3] = Program("plain", "plain marked", "accepted", run="done")
        with self.assertRaisesRegex(GateError, "implementation_chosen.pkg differs from its pin at plain"):
            self.outcomes(Ledger(self.ledger))


if __name__ == "__main__":
    unittest.main()
