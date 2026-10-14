"""Unit tests for the compile-performance harness's pure parts.

    PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/perf -t tests
"""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError  # noqa: E402
from perf import bench, compare, receipts  # noqa: E402


def receipt(port="kwasm", stage="cargo-check", scenario="no-op", wall=1.0, peak=100, exit_status=0,
            counters=None, spans=None, **extra):
    timings = None
    if counters is not None or spans is not None:
        timings = {"spans": spans or [], "counters": counters}
    return {"schema": receipts.SCHEMA, "port": port, "stage": stage, "scenario": scenario, "wall_seconds": wall,
            "user_seconds": wall, "sys_seconds": 0.1, "peak_memory_bytes": peak, "exit_status": exit_status,
            "krs_timings": timings, "package": "krs-kwasm-semantics", **extra}


class SpreadTests(unittest.TestCase):
    def test_median_and_range(self):
        odd = compare.Spread.of([3.0, 1.0, 2.0])
        self.assertEqual((odd.median, odd.min, odd.max), (2.0, 1.0, 3.0))
        even = compare.Spread.of([1.0, 10.0, 2.0, 4.0])
        self.assertEqual((even.median, even.min, even.max), (3.0, 1.0, 10.0))

    def test_classification_follows_the_overlap_rule(self):
        slow = compare.Spread.of([2.0, 2.1])
        fast = compare.Spread.of([1.0, 1.1])
        overlapping = compare.Spread.of([1.05, 2.05])
        self.assertEqual(compare.classify(slow, fast, 2, 2), "faster")
        self.assertEqual(compare.classify(fast, slow, 2, 2), "slower")
        self.assertEqual(compare.classify(slow, overlapping, 2, 2), "within noise")
        self.assertEqual(compare.classify(slow, fast, 1, 2), "unreplicated")

    def test_exact_classification(self):
        self.assertEqual(compare.classify_exact(compare.Spread.of([3, 3]), compare.Spread.of([3])), "exact")
        self.assertEqual(compare.classify_exact(compare.Spread.of([3]), compare.Spread.of([4])), "changed")
        self.assertEqual(compare.classify_exact(compare.Spread.of([3, 4]), compare.Spread.of([3])), "varies")


class CompareTests(unittest.TestCase):
    def test_self_comparison_is_within_noise_or_exact(self):
        side = [receipt(wall=1.0, counters={"descriptors": 60}, spans=[{"id": "collector.run", "seconds": 0.5}]),
                receipt(wall=1.2, counters={"descriptors": 60}, spans=[{"id": "collector.run", "seconds": 0.6}])]
        rows, warnings = compare.compare(side, side)
        self.assertEqual(warnings, [])
        self.assertTrue(rows)
        self.assertEqual({row["verdict"] for row in rows}, {"within noise", "exact"})
        metrics = {row["metric"] for row in rows}
        self.assertIn("counter.descriptors", metrics)
        self.assertIn("krs.collector.run", metrics)

    def test_edit_directions_are_compared_separately(self):
        side = [receipt(scenario="edit-rule", counters={"bytes": 10}, scenario_detail={"direction": "apply"}),
                receipt(scenario="edit-rule", counters={"bytes": 11}, scenario_detail={"direction": "revert"})]
        verdicts = {row["metric"]: row["verdict"] for row in compare.compare(side, side)[0]}
        self.assertEqual(verdicts["counter.bytes"], "exact")

    def test_disjoint_ranges_and_changed_counters(self):
        before = [receipt(wall=10.0, peak=900, counters={"n": 1}), receipt(wall=11.0, peak=950, counters={"n": 1})]
        after = [receipt(wall=5.0, peak=500, counters={"n": 2}), receipt(wall=6.0, peak=550, counters={"n": 2})]
        verdicts = {row["metric"]: row["verdict"] for row in compare.compare(before, after)[0]}
        self.assertEqual(verdicts["wall_seconds"], "faster")
        self.assertEqual(verdicts["peak_memory_bytes"], "lower")
        self.assertEqual(verdicts["counter.n"], "changed")
        self.assertEqual(verdicts["exit_status"], "exact")

    def test_environment_differences_are_reported(self):
        before = [receipt(environment={"overrides": {}})]
        after = [receipt(environment={"overrides": {"CARGO_PROFILE_DEV_DEBUG": "0"}})]
        _, warnings = compare.compare(before, after)
        self.assertTrue(any("CARGO_PROFILE_DEV_DEBUG" in warning for warning in warnings))

    def test_summary_has_one_table_per_port(self):
        text = compare.render_summary([receipt(), receipt(port="kevm", stage="krs-build", scenario="cold")])
        self.assertIn("== kwasm ==", text)
        self.assertIn("== kevm ==", text)


class ReceiptTests(unittest.TestCase):
    def test_timings_normalization_accepts_both_span_shapes(self):
        spans = receipts.normalize_timings({"schema": "krs-timings/1", "spans": [{"id": "a", "seconds": 1, "depth": 0}],
                                            "total_wall_seconds": 2, "unattributed_seconds": 1})
        self.assertEqual(spans["spans"], [{"id": "a", "seconds": 1.0, "depth": 0}])
        phases = receipts.normalize_timings({"phases": [{"name": "b", "seconds": 0.5, "depth": 1}]})
        self.assertEqual(phases["spans"], [{"id": "b", "seconds": 0.5, "depth": 1}])
        self.assertIsNone(phases["counters"])

    def test_counters_flatten(self):
        flat = receipts.flatten_counters({"descriptors": {"rule": 3, "sort": 2}, "list": [{"id": "x", "value": 1}]})
        self.assertEqual(flat, {"descriptors.rule": 3, "descriptors.sort": 2, "list.x": 1})

    def test_counters_document(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "c.json"
            path.write_text('{"schema": "krs-counters/1", "counters": {"descriptors.total": 60}}', encoding="utf-8")
            status, document = receipts.ingest_counters(path)
            self.assertEqual(status, "collected")
            self.assertEqual(document["counters"], {"descriptors.total": 60})
            side = [receipt(krs_counters=document), receipt(krs_counters=document)]
            verdicts = {row["metric"]: row["verdict"] for row in compare.compare(side, side)[0]}
            self.assertEqual(verdicts["counter.descriptors.total"], "exact")

    def test_missing_and_invalid_timings(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "t.json"
            self.assertEqual(receipts.ingest_timings(path), ("missing", None))
            path.write_text("not json", encoding="utf-8")
            self.assertEqual(receipts.ingest_timings(path), ("invalid", None))

    def test_cargo_unit_table(self):
        html = ('DURATION = 29;\nconst UNIT_DATA = [\n  {"name": "serde", "duration": 1.0},\n'
                '  {"name": "krs-kwasm-semantics", "target": " lib", "mode": "todo", "start": 1.0, "duration": 4.5},\n'
                '  {"name": "krs-generated-collector-ab", "duration": 0.25}\n];\nconst CONCURRENCY_DATA = [];')
        parsed = receipts.cargo_units(html, ["krs-kwasm-semantics"])
        self.assertEqual(parsed["total_seconds"], 29.0)
        self.assertEqual([unit["name"] for unit in parsed["units"]],
                         ["krs-kwasm-semantics", "krs-generated-collector-ab"])
        self.assertEqual(compare._semantics_seconds({"package": "krs-kwasm-semantics", "cargo_timings": parsed}), 4.5)

    def test_rustc_verbose(self):
        parsed = receipts.parse_rustc_verbose("rustc 1.98.0 (abc 2026-01-01)\nhost: x86_64-unknown-linux-gnu\n")
        self.assertEqual(parsed["host"], "x86_64-unknown-linux-gnu")


class MatrixTests(unittest.TestCase):
    def test_every_edit_anchors_once_in_the_repository(self):
        for port in bench.load_ports().values():
            text = (bench.ROOT / "semantics" / port.key / port.source).read_text(encoding="utf-8")
            for scenario, edit in port.edits.items():
                edited = bench.apply_edit(text, edit["old"], edit["new"], label=scenario)
                self.assertEqual(bench.apply_edit(edited, edit["new"], edit["old"], label=scenario), text)

    def test_ambiguous_anchor_is_rejected(self):
        with self.assertRaises(GateError):
            bench.apply_edit("a a", "a", "b", label="x")

    def test_rustc_bootstrap_is_reserved_for_profiling(self):
        with self.assertRaises(GateError):
            bench.parse_overrides(["RUSTC_BOOTSTRAP=1"], None)
        self.assertEqual(bench.parse_overrides(["CARGO_PROFILE_DEV_DEBUG=0"], None), {"CARGO_PROFILE_DEV_DEBUG": "0"})

    def test_ambient_build_variables_are_stripped(self):
        for name in ("RUSTFLAGS", "CARGO_PROFILE_DEV_DEBUG", "RUSTC_BOOTSTRAP", "CARGO_TARGET_DIR", "CARGO_INCREMENTAL"):
            self.assertTrue(bench.STRIPPED_VARIABLES.match(name), name)
        for name in ("PATH", "HOME", "CARGO_HOME", "LD_LIBRARY_PATH"):
            self.assertFalse(bench.STRIPPED_VARIABLES.match(name), name)


if __name__ == "__main__":
    unittest.main()
