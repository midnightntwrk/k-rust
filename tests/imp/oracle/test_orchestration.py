"""Tool-independent process and comparison contracts for the IMP oracles."""

from __future__ import annotations

import os
from dataclasses import replace
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import behavior  # noqa: E402
import proofs  # noqa: E402
import run_proofs  # noqa: E402
from support import GateError  # noqa: E402


class BehaviorTests(unittest.TestCase):
    def test_llvm_route_lifts_only_the_address_space_limit(self) -> None:
        with patch("support.tools.shutil.which", return_value="/usr/bin/prlimit"):
            self.assertEqual(
                behavior._without_address_space_limit(True), ("prlimit", "--as=unlimited", "--"),
            )

    def test_live_llvm_route_requires_prlimit_and_replay_does_not(self) -> None:
        with patch("support.tools.shutil.which", return_value=None):
            with self.assertRaisesRegex(GateError, "required executable is unavailable: prlimit"):
                behavior._without_address_space_limit(True)
            self.assertEqual(
                behavior._without_address_space_limit(False), ("prlimit", "--as=unlimited", "--"),
            )

    def test_failure_route_wraps_krun_in_timeout_and_prlimit(self) -> None:
        k = Mock(refresh=False)
        route = behavior.Route(Path("/work/failure-kompiled"), {})
        behavior._execute(
            k, "krun-failure/reference/fail.imp", route, Path("/work/fail.imp"), ("ENV=.Map",), 60,
            kill_after=8, unlimited_address_space=True,
        )
        k.run.assert_called_once_with(
            "krun-failure/reference/fail.imp", "krun",
            ["--definition", "/work/failure-kompiled", "--output", "json", "-cENV=.Map", "/work/fail.imp"],
            timeout=15,
            prefix=("timeout", "--signal=KILL", "8s", "prlimit", "--as=unlimited", "--"),
            streams={"stderr": behavior.reduce_kore_exec_log},
        )

    def test_hook_abort_precedes_secondary_wrapper_parse_error(self) -> None:
        stderr = (
            "[hook_INT_tdiv]: Division by zero: 1 / 0\n"
            "Could not parse backend result: parse error"
        )
        self.assertEqual(behavior._diagnostic_class(stderr), "hook")

    def test_unrelated_ambiguous_diagnostic_still_fails_closed(self) -> None:
        with self.assertRaisesRegex(GateError, "ambiguous class"):
            behavior._diagnostic_class("scanner error followed by unexpected token")

    def _fake_behavior(self, workers: int, differing: frozenset[str] = frozenset()) -> str:
        """Run a small plan over fake tools whose latency reverses plan order."""

        policy = {}
        reference = behavior.Route(Path("reference"), policy)
        actual = behavior.Route(Path("actual"), policy)
        calls = iter(range(1000, 0, -1))

        def completed(term: object, returncode: int = 0, stderr: str = ""):
            time.sleep(next(calls) / 200000)
            return subprocess.CompletedProcess([], returncode, term, stderr)

        def fake_parse(_k, _label, route, _module, _sort, path, _timeout):
            if path.name.startswith("reject"):
                return subprocess.CompletedProcess(
                    [], 1, "", "Parse error: unexpected token Location(1,2,1,3)"
                )
            name = path.name.split("-", 1)[-1] if path.parent.name.startswith("krs-imp") else path.name
            side = "actual" if route is actual and name in differing else "same"
            return completed(f"{name}:{side}")

        def fake_unparse(_k, _label, _route, _module, _sort, path, _timeout):
            return subprocess.CompletedProcess([], 0, path.name, "")

        def fake_execute(_k, _label, _route, path, _configurations, _timeout, *, depth=None, search=False, **_options):
            if path.name.startswith("fail"):
                return subprocess.CompletedProcess([], 134, "", "[hook_INT_tdiv]: Division by zero")
            state = f"{path.name}:{depth}"
            return completed(state)

        plan = behavior.BehaviorPlan(
            parse_cases=tuple(
                behavior.ParseCase(name, Path(name), "Stmt", "REF", "ACT")
                for name in ("a.imp", "b.imp", "c.imp")
            ),
            execution_cases=tuple(
                behavior.ExecutionCase(name, Path(name), depths=(0, 1, 2), search_depths=(2,))
                for name in ("x.imp", "y.imp")
            ),
            rejection_cases=(
                behavior.RejectionCase("reject.imp", Path("reject.imp"), "Stmt", "REF", "ACT", "parser", (1, 2, 1, 3)),
            ),
            failure_cases=(
                behavior.FailureCase("fail.imp", Path("fail.imp"), expected_fragment="Division by zero"),
            ),
        )
        session = Mock()
        session.kast_normalize.side_effect = lambda _variant, *, text, **_options: text
        session.kast_frontier.side_effect = lambda _action, value: [value]
        with (
            patch.multiple(behavior, _parse=fake_parse, _unparse=fake_unparse, _execute=fake_execute),
            patch.dict(os.environ, {"KRS_IMP_ORACLE_WORKERS": str(workers)}),
            patch.object(behavior.krs_gate, "Session") as create_session,
            tempfile.TemporaryDirectory() as temporary,
        ):
            create_session.return_value.__enter__.return_value = session
            summary = behavior.compare_behavior(
                k=Mock(), workspace=Path(temporary) / "krs-imp-behavior", gate=Path("gate"),
                reference=reference, actual=actual, plan=plan,
            )
        self.assertEqual(create_session.call_count, 1)
        self.assertEqual(summary.depth_state_count, 6)
        return summary.evidence_sha256

    def test_parallel_evidence_equals_serial_evidence(self) -> None:
        self.assertEqual(self._fake_behavior(1), self._fake_behavior(8))

    def test_parallel_run_reports_the_first_difference_in_plan_order(self) -> None:
        for workers in (1, 8):
            with self.assertRaisesRegex(GateError, "parse tree differs for b.imp"):
                self._fake_behavior(workers, frozenset({"b.imp", "c.imp"}))


class ProofTests(unittest.TestCase):
    def test_proof_comparison_rejects_changed_evidence_and_unknown_pin_fields(self) -> None:
        evidence = proofs.ProofEvidence(
            schema=1, name="claim", claim_label="claim", status="proved",
            bounds=proofs.ProofBounds(100, 64), frontier_count=0, frontier=(),
            user_labels=("step",), normalized_result={"opaque": "result"},
            normalized_claim={"opaque": "claim"}, result_sha256="result", claim_sha256="claim",
        )
        pins = {"claim": evidence.pin()}
        self.assertEqual(
            proofs.compare_proof_evidence({"claim": evidence}, {"claim": evidence}, pins), pins,
        )
        changed = replace(evidence, normalized_claim={"opaque": "changed"})
        with self.assertRaisesRegex(GateError, "semantic proof evidence differs"):
            proofs.compare_proof_evidence({"claim": evidence}, {"claim": changed}, pins)
        pins["claim"]["unreviewed"] = True
        with self.assertRaisesRegex(GateError, "unknown or missing pin fields"):
            proofs.compare_proof_evidence({"claim": evidence}, {"claim": evidence}, pins)

    def test_actual_spec_imports_verification_only_identifier_syntax(self) -> None:
        source = run_proofs.actual_spec_source(Path("actual-execution.k"), "  claim body\n")
        self.assertEqual(
            source,
            'requires "actual-execution.k"\n'
            'requires "imp-verification.k"\n\n'
            "module KRS-IMP-SPEC\n"
            "  imports KRS-IMP\n"
            "  imports IMP-VERIFICATION-SYNTAX\n\n"
            "  claim body\n"
            "endmodule\n",
        )

    def test_bounds_require_explicit_nonnegative_depth_and_positive_breadth(self) -> None:
        for depth, breadth in ((-1, 64), (0, 0), (True, 1), (0, True)):
            with self.subTest(depth=depth, breadth=breadth), self.assertRaises(GateError):
                proofs.ProofBounds(depth, breadth)


if __name__ == "__main__":
    unittest.main()
