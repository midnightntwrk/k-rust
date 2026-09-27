"""Unit tests for the ladder harness's pure parts: growth fits, truncation, and generators.

    PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/perf -t tests
"""

from __future__ import annotations

import math
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from perf import growth, ladder, receipts, synth, truncate  # noqa: E402


def ladder_receipt(value, wall, peak=1000, counters=None, spans=None, exit_status=0, llvm=None):
    return {"schema": receipts.SCHEMA, "exit_status": exit_status, "wall_seconds": wall, "user_seconds": wall,
            "sys_seconds": 0.0, "peak_memory_bytes": peak,
            "krs_timings": {"spans": spans or []}, "krs_counters": {"counters": counters or {}},
            "ladder": {"name": "t", "kind": "synthetic", "param": "n", "value": value, "source_bytes": 10 * value,
                       "source_lines": value, "llvm_lines": llvm}}


class FitTests(unittest.TestCase):
    def test_exact_power_laws(self):
        for exponent in (0.5, 1.0, 2.0):
            fit = growth.fit_power_law([(n, 3 * n ** exponent) for n in (2, 4, 8, 16)])
            self.assertAlmostEqual(fit.slope, exponent)
            self.assertAlmostEqual(fit.intercept, math.log(3))
            self.assertAlmostEqual(fit.r_squared, 1.0)
            self.assertFalse(fit.fewer_than_three)

    def test_degenerate_inputs(self):
        self.assertIsNone(growth.fit_power_law([(4, 1.0)]))
        self.assertIsNone(growth.fit_power_law([(4, 1.0), (4, 2.0)]))
        self.assertIsNone(growth.fit_power_law([(0, 1.0), (4, 0.0), (8, 1.0)]))
        two = growth.fit_power_law([(2, 1.0), (4, 2.0)])
        self.assertTrue(two.fewer_than_three)
        self.assertAlmostEqual(two.slope, 1.0)

    def test_constant_metric_has_zero_slope_and_no_r_squared(self):
        fit = growth.fit_power_law([(2, 5.0), (4, 5.0), (8, 5.0)])
        self.assertAlmostEqual(fit.slope, 0.0)
        self.assertIsNone(fit.r_squared)

    def test_top_slope_uses_the_two_largest_sizes(self):
        # Linear, then quadratic between the last two sizes.
        item = growth.growth("counter.x", "param",
                             [(8, 8.0), (2, 2.0), (4, 4.0), (16, 16.0), (32, 32.0), (64, 128.0)])
        self.assertEqual(item.top_sizes, [32.0, 64.0])
        self.assertAlmostEqual(item.top_slope, 2.0)
        self.assertLess(item.fit.slope, 1.2)
        self.assertTrue(item.exceeds(1.2))

    def test_time_floor_never_flags(self):
        item = growth.growth("span.tiny", "param", [(1, 0.001), (2, 0.01), (4, 0.05)])
        self.assertTrue(item.below_floor)
        self.assertGreater(item.fit.slope, 1.2)
        self.assertFalse(item.exceeds(1.2))
        counter = growth.growth("counter.tiny", "param", [(1, 1.0), (2, 10.0)])
        self.assertFalse(counter.below_floor)
        self.assertTrue(counter.exceeds(1.2))

    def test_analysis_flags_superlinear_metrics_with_their_stage(self):
        found = [ladder_receipt(n, wall=0.5 * n, counters={"provenance.anchors": n * n},
                                spans=[{"id": "collector.build", "seconds": 0.1 * n, "depth": 0},
                                       {"id": "collector.run", "seconds": 0.2 * n, "depth": 0},
                                       {"id": "collector.exec", "seconds": 0.15 * n, "depth": 1},
                                       {"id": "native.compile", "seconds": 0.1, "depth": 0}])
                 for n in (2, 4, 8)]
        found.append(ladder_receipt(16, wall=999.0, exit_status=1))
        analysis = growth.analyse(found)
        self.assertEqual(analysis["values"], [2.0, 4.0, 8.0])
        flagged = {(item["metric"], item["x"]): item for item in analysis["flagged"]}
        self.assertIn(("counter.provenance.anchors", "param"), flagged)
        self.assertEqual(flagged[("counter.provenance.anchors", "param")]["stage"], "counter:provenance")
        self.assertNotIn(("wall_seconds", "param"), flagged)
        slopes = {(row["metric"], row["x"]): row["fit"]["slope"] for row in analysis["by_axis"]}
        self.assertAlmostEqual(slopes[("wall_seconds", "counter.provenance.anchors")], 0.5)
        self.assertEqual(analysis["dominant_leaf_span"]["span"], "collector.exec")
        self.assertEqual((analysis["dominant_leaf_span"]["from"], analysis["dominant_leaf_span"]["to"]), (4.0, 8.0))
        self.assertIn("## t", growth.render({"name": "t", "param": "n"}, analysis))

    def test_medians_over_repetitions(self):
        found = [ladder_receipt(4, wall=1.0), ladder_receipt(4, wall=3.0), ladder_receipt(4, wall=2.0)]
        self.assertEqual(growth.rung_medians(found)[4.0]["wall_seconds"], 2.0)
        self.assertEqual(growth.rung_medians(found)[4.0]["source.bytes"], 40.0)


class AttributionTests(unittest.TestCase):
    def test_function_groups_normalize_hashes_and_numbers(self):
        name = "krs_perf_synth[59a3112984385ac1]::__krs_head_rule_descriptor_0c154bab75ed6854"
        self.assertEqual(growth.function_group(name), "krs_perf_synth[H]::__krs_head_rule_descriptor_H")
        self.assertEqual(growth.function_group("a::__krs_enum_grammar_b60d04ee1f98d0cb_12"),
                         "a::__krs_enum_grammar_H_N")

    def test_largest_growth_group(self):
        small = [{"name": "rule_1", "lines": 10}, {"name": "enum_1", "lines": 5}]
        large = [{"name": "rule_1", "lines": 10}, {"name": "rule_2", "lines": 10}, {"name": "enum_1", "lines": 6}]
        self.assertEqual(growth.largest_growth_group(small, large), ("rule_N", 10.0))

    def test_llvm_lines_parse(self):
        text = ("  Lines                Copies             Function name\n"
                "  -----                ------             -------------\n"
                "  21639                245                (TOTAL)\n"
                "   1594 (7.4%,  7.4%)    1 (0.4%,  0.4%)  krs_perf_synth[59a3]::__krs_enum_grammar_b6_0\n"
                "   1380 (6.4%, 21.1%)    2 (0.4%,  1.2%)  <krs_perf_synth::Machine>::__krs_initializer_payload\n")
        parsed = ladder.parse_llvm_lines(text)
        self.assertEqual((parsed["total"], parsed["copies"], parsed["functions_listed"]), (21639, 245, 2))
        self.assertEqual(parsed["functions"][1], {"name": "<krs_perf_synth::Machine>::__krs_initializer_payload",
                                                  "lines": 1380, "copies": 2})
        self.assertIsNone(ladder.parse_llvm_lines("error: could not compile"))


SOURCE = '''//! Doc with a brace { and a "quote".
use k::KResult;

#[k::equation]
fn first(k::term![F(x)]: k::Term<S>) -> k::Term<S> {
    k::term![G("}", '}', r#"{"#)]
}

/* block { comment */
#[k::requires(int::gt(x, 0))]
#[k::equation]
fn second(x: k::Term<S>) -> k::Term<S> { k::term![H(x)] }

pub struct Kept { pub field: u8 }

#[rustfmt::skip]
k::rules! {
    for Machine;
    use Op::*;

    one: { k: [A(), ..] } => { k: [B(), ..] };
    #[k::rule(owise)]
    two: { k: [B(), ..] } => { k: [C(), ..] }
    where x: Int;
    three: { k: [C(), ..] } => { k: [D(), ..] };
    four: { k: ['a', ..] } => { k: [E(), ..] };
}

fn lifetime<'a>(value: &'a str) -> &'a str { value }
'''


class TruncateTests(unittest.TestCase):
    def test_full_fraction_is_identity(self):
        self.assertEqual(truncate.truncate(SOURCE, 4, 4).source, SOURCE)

    def test_counts_and_nested_selection(self):
        half = truncate.truncate(SOURCE, 2, 4)
        self.assertEqual((half.rules_total, half.rules_kept, half.equations_total, half.equations_kept), (4, 2, 2, 1))
        quarter = truncate.truncate(SOURCE, 1, 4)
        self.assertEqual((quarter.rules_kept, quarter.equations_kept), (1, 0))
        for kept in ("pub struct Kept", "for Machine;", "use Op::*;", "fn lifetime<'a>", "use k::KResult;"):
            self.assertIn(kept, quarter.source)
            self.assertIn(kept, half.source)
        # Nested: every rule kept at 1/4 is kept at 1/2.
        self.assertIn("four:", quarter.source)
        self.assertIn("four:", half.source)
        self.assertIn("two:", half.source)
        self.assertIn("#[k::rule(owise)]", half.source)
        self.assertNotIn("one:", half.source)
        self.assertNotIn("fn first", quarter.source)
        self.assertIn("fn second", half.source)
        self.assertNotIn("fn first", half.source)
        self.assertNotIn("int::gt", quarter.source)
        truncate.matching(truncate.tokenize(quarter.source))

    def test_empty_rule_block_is_dropped(self):
        source = "k::rules! {\n    for M;\n    only: { k: [A(), ..] } => { k: [B(), ..] };\n}\nfn keep() {}\n"
        cut = truncate.truncate(source, 1, 8)
        self.assertEqual(cut.rule_blocks_dropped, 1)
        self.assertNotIn("rules!", cut.source)
        self.assertIn("fn keep", cut.source)

    def test_keep_is_nested_and_exact(self):
        for denominator in (4, 8):
            previous: set[int] = set()
            for numerator in range(1, denominator + 1):
                kept = {i for i in range(64) if truncate.keep(i, numerator, denominator)}
                self.assertEqual(len(kept), 64 * numerator // denominator)
                if numerator & (numerator - 1) == 0:
                    self.assertTrue(previous <= kept)
                    previous = kept

    def test_ports_truncate_to_balanced_sources(self):
        for port in ("kwasm", "kevm", "kmir"):
            text = (ladder.ROOT / "semantics" / port / "src/lib.rs").read_text(encoding="utf-8")
            cut = truncate.truncate(text, 1, 8)
            self.assertGreater(cut.rules_total, 0)
            self.assertGreater(cut.equations_total, 0)
            self.assertIn("k::sorts!", cut.source)
            self.assertIn("#[k::configuration]", cut.source)
            truncate.matching(truncate.tokenize(cut.source))


class SynthTests(unittest.TestCase):
    def test_every_shape_generates_balanced_source(self):
        for shape in synth.SHAPES:
            for n in (4, 8, 64):
                source = synth.generate(shape, n)
                truncate.matching(truncate.tokenize(source))
                self.assertIn("#[k::configuration]", source)

    def test_shapes_grow_their_own_aspect(self):
        self.assertEqual(synth.generate("many-small-rules", 32).count("    step_"), 32)
        self.assertEqual(synth.generate("wide-enums", 32).count("#[k::syntax(\"w") - 1, 32)
        self.assertEqual(synth.generate("deep-terms", 32).count("Wrap("), 4 * 32)
        self.assertEqual(synth.generate("sorts-deep", 32).count("    impl Deep"), 32)
        dense = synth.generate("sorts-dense", 32)
        self.assertEqual(dense.count("    impl Dense"), 32)
        self.assertIn("Dense7x3: Dense6x0 + Dense6x1 + Dense6x2 + Dense6x3;", dense)
        self.assertEqual(synth.generate("anchors-per-rule", 32).count("int::add("), 4 * 31)
        with self.assertRaises(ValueError):
            synth.generate("sorts-dense", 6)

    def test_ladder_definitions_load(self):
        ladders = ladder.load_ladders()
        self.assertIn("kevm-fraction", ladders)
        self.assertEqual({item.shape for item in ladders.values() if item.kind == "synthetic"}, set(synth.SHAPES))
        for item in ladders.values():
            ladder.rung_source(item, item.values[0])


if __name__ == "__main__":
    unittest.main()
