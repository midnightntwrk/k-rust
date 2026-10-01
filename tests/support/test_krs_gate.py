"""Contract tests for the native gate process client."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
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
    if mode == "silent":
        time.sleep(60)
    if mode == "exit":
        print("deliberate failure", file=sys.stderr, flush=True)
        sys.exit(7)
    if mode == "expect_false" and request["operation"] == "expect":
        response = {"id": request["id"], "result": {
            "met": False, "expected": "wanted", "actual": "found",
        }}
    elif mode == "load_digest" and request["operation"] == "definition.load":
        response = {"id": request["id"], "result": {"module": "MAIN", "definition_kore_sha256": "abc123"}}
    elif request["operation"] == "kore.digest" and mode == "normal":
        response = {"id": request["id"], "result": {"sha256": "abc123"}}
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

    def test_digest_needs_no_definition_load(self) -> None:
        with krs_gate.Session(self.binary) as session:
            self.assertEqual(session.digest(Path("definition.kore"), Path("/tmp/semantics.k")), "abc123")
        self.assertEqual(
            krs_gate.digest(self.binary, Path("definition.kore"), Path("/tmp/semantics.k")),
            "abc123",
        )

    def test_ir_queries_need_no_definition_load_and_forward_opaque_queries(self) -> None:
        query = {"kind": "sentences", "sentence_kind": "claim"}
        with krs_gate.Session(self.binary) as session:
            result = session.ir_query(Path("artifacts"), query)
        self.assertEqual(result["operation"], "ir.query")
        self.assertEqual(result["request_id"], "1")
        self.assertEqual(result["fields"], {"artifacts": "artifacts", "query": query})
        self.assertEqual(krs_gate.ir_query(self.binary, Path("artifacts"), query), result)
        batch = krs_gate.ir_queries(self.binary, Path("artifacts"), [query, {"kind": "files"}])
        self.assertEqual([item["request_id"] for item in batch], ["1", "2"])
        self.assertEqual(batch[1]["fields"]["query"], {"kind": "files"})
        with self.assertRaisesRegex(GateError, "bad request"):
            krs_gate.ir_query(self.binary, Path("artifacts"), query, environment={"KRS_TEST_GATE_MODE": "error"})

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

    def test_concurrent_requests_keep_matching_responses(self) -> None:
        with krs_gate.Session(self.binary) as session:
            with ThreadPoolExecutor(max_workers=8) as executor:
                results = list(executor.map(lambda index: session.request("echo", index=index), range(32)))
        self.assertEqual([result["fields"]["index"] for result in results], list(range(32)))
        self.assertEqual({result["request_id"] for result in results}, {str(index) for index in range(1, 33)})

    def test_kast_methods_forward_opaque_inputs_and_policy(self) -> None:
        with krs_gate.Session(self.binary) as session:
            normalized = session.kast_normalize("behavior", text="opaque", allow_prefix=True, policy={"label_map": {}, "sort_map": {}, "identity_labels": [], "identity_sorts": []})
            projected = session.kast_project({"path": "left"}, {"path": "right"}, {}, {})
            frontier = session.kast_frontier("proof", {"opaque": True}, returncode=0, stderr="", constraint_labels=[])
            inspected = session.kast_inspect("module_facts", path=Path("definition.json"), name="MAIN")
        self.assertEqual(normalized["fields"], {
            "variant": "behavior", "text": "opaque", "allow_prefix": True, "policy": {"label_map": {}, "sort_map": {}, "identity_labels": [], "identity_sorts": []},
        })
        self.assertEqual(projected["fields"], {
            "reference": {"path": "left"}, "actual": {"path": "right"},
            "reference_policy": {}, "actual_policy": {}, "compatible_sentence_pairs": [],
        })
        self.assertEqual(frontier["fields"], {"action": "proof", "value": {"opaque": True}, "returncode": 0, "stderr": "", "constraint_labels": []})
        self.assertEqual(inspected["fields"], {"action": "module_facts", "path": "definition.json", "name": "MAIN"})
        with self.assertRaisesRegex(GateError, "exactly one"):
            session.kast_normalize("behavior", text="opaque", path=Path("definition.json"))

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

    def test_search_forwards_optional_limits_and_retained_state(self) -> None:
        with krs_gate.Session(self.binary) as session:
            searched = session.search("opaque pattern", max_depth=3, max_results=1, keep="final")
            observed = session.observe("final", ["k"])
            unbounded = session.search("opaque pattern")
        self.assertEqual(searched["operation"], "search")
        self.assertEqual(searched["fields"], {
            "pattern": "opaque pattern", "max_depth": 3, "max_results": 1, "keep": "final",
        })
        self.assertEqual(observed["fields"], {"state": "final", "cells": ["k"]})
        self.assertEqual(unbounded["fields"], {"pattern": "opaque pattern"})
        self.assertEqual(
            [searched["request_id"], observed["request_id"], unbounded["request_id"]],
            ["1", "2", "3"],
        )

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

    def test_load_requires_the_expected_definition_digest(self) -> None:
        with krs_gate.Session(self.binary, environment={"KRS_TEST_GATE_MODE": "load_digest"}) as session:
            session.load(Path("definition-ir.json"), "MAIN", definition_kore_sha256="abc123")
            with self.assertRaisesRegex(GateError, "sha256 abc123 differs from the compiled definition's def456"):
                session.load(Path("definition-ir.json"), "MAIN", definition_kore_sha256="def456")

    def test_unanswered_request_times_out_and_kills_session(self) -> None:
        with krs_gate.Session(self.binary, environment={"KRS_TEST_GATE_MODE": "silent"}) as session:
            with self.assertRaisesRegex(GateError, r"request 1 \(execute\) exceeded 0.2 seconds"):
                session.request("execute", timeout=0.2, pattern="opaque")


if __name__ == "__main__":
    unittest.main()
