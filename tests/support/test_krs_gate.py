"""Contract tests for the native gate process client."""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from support import GateError
from support import krs_gate


FAKE_GATE = """\
import json
import os
import sys
import time

assert sys.argv[1:] == ["session"]
mode = os.environ.get("KRS_TEST_GATE_MODE", "normal")
for line in sys.stdin:
    request = json.loads(line)
    if mode == "exit":
        print("deliberate failure", file=sys.stderr, flush=True)
        sys.exit(7)
    if mode == "expect_false" and request["operation"] == "expect":
        response = {"id": request["id"], "result": {
            "met": False, "expected": "wanted", "actual": "found",
        }}
    elif mode == "error":
        response = {"id": request["id"], "error": {"message": "bad request"}}
    elif mode == "wrong_id":
        response = {"id": "other", "result": {}}
    else:
        response = {"id": request["id"], "result": {
            "operation": request["operation"],
            "request_id": request["id"],
            "fields": {key: value for key, value in request.items() if key not in ("id", "operation")},
        }}
    print(json.dumps(response), flush=True)
if mode == "hang":
    time.sleep(60)
"""


class ClientTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.binary = Path(temporary.name) / "fake-gate"
        self.binary.write_text(f"#!{sys.executable}\n{FAKE_GATE}", encoding="utf-8")
        self.binary.chmod(0o755)

    def test_compile_uses_one_shot_command(self) -> None:
        with patch.object(krs_gate.process, "run") as runner:
            krs_gate.compile(
                self.binary,
                Path("definition-ir.json"),
                Path("definition.kore"),
                environment={"A": "b"},
                timings=Path("timings.json"),
            )
        runner.assert_called_once_with(
            [str(self.binary), "compile", "--timings", "timings.json", "definition-ir.json", "definition.kore"],
            environment={"A": "b"},
            timeout=900,
        )

    def test_session_exchanges_matching_ids_in_lockstep(self) -> None:
        with krs_gate.Session(self.binary) as session:
            loaded_ir = session.load(Path("definition-ir.json"), "MAIN")
            configured = session.configure({"PGM": "run"})
            executed = session.execute("opaque pattern", trace=True, max_depth=3)
            proved = session.prove("opaque claim")
        self.assertEqual(
            [loaded_ir["request_id"], configured["request_id"], executed["request_id"], proved["request_id"]],
            ["1", "2", "3", "4"],
        )
        self.assertEqual(loaded_ir["operation"], "definition.load")
        self.assertEqual(loaded_ir["fields"], {"definition_ir": "definition-ir.json", "module": "MAIN"})
        self.assertEqual(configured["fields"], {"variables": {"PGM": "run"}})
        self.assertEqual(executed["fields"], {"pattern": "opaque pattern", "trace": True, "max_depth": 3})
        self.assertEqual(proved["fields"], {"claim": "opaque claim"})

    def test_error_response_reports_request_id_and_message(self) -> None:
        with krs_gate.Session(self.binary, environment={"KRS_TEST_GATE_MODE": "error"}) as session:
            with self.assertRaisesRegex(GateError, "request 1 failed: bad request"):
                session.request("execute", pattern="opaque")

    def test_retained_state_operations_use_lockstep_ids(self) -> None:
        with krs_gate.Session(self.binary) as session:
            executed = session.execute("pattern", keep="state")
            read = session.read("opaque kore", "state")
            observed = session.observe("state", ["k", "locals"])
        self.assertEqual(
            [executed["request_id"], read["request_id"], observed["request_id"]],
            ["1", "2", "3"],
        )
        self.assertEqual(executed["fields"], {"pattern": "pattern", "keep": "state"})
        self.assertEqual(read["fields"], {"text": "opaque kore", "keep": "state"})
        self.assertEqual(observed["fields"], {"state": "state", "cells": ["k", "locals"]})

    def test_failed_expectation_reports_both_terms(self) -> None:
        with krs_gate.Session(self.binary, environment={"KRS_TEST_GATE_MODE": "expect_false"}) as session:
            with self.assertRaisesRegex(GateError, "expected=wanted, actual=found"):
                session.expect("state", "k", text="wanted")

    def test_early_exit_reports_stderr(self) -> None:
        with krs_gate.Session(self.binary, environment={"KRS_TEST_GATE_MODE": "exit"}) as session:
            with self.assertRaisesRegex(GateError, "request 1: deliberate failure"):
                session.request("execute", pattern="opaque")

    def test_mismatched_response_id_fails(self) -> None:
        with krs_gate.Session(self.binary, environment={"KRS_TEST_GATE_MODE": "wrong_id"}) as session:
            with self.assertRaisesRegex(GateError, "response id differs from request 1"):
                session.request("execute", pattern="opaque")

    def test_exit_timeout_terminates_session(self) -> None:
        with patch.object(krs_gate, "SESSION_EXIT_TIMEOUT_SECONDS", 0.1):
            with self.assertRaisesRegex(GateError, "process group was terminated"):
                with krs_gate.Session(self.binary, environment={"KRS_TEST_GATE_MODE": "hang"}):
                    pass


if __name__ == "__main__":
    unittest.main()
