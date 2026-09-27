"""Unit tests for the rustc profiling mode and the attribution tool's pure parts.

    PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/perf -t tests
"""

from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from perf import attribution, bench, rustc_profile  # noqa: E402


TIME_PASSES = """\
   Compiling krs-kevm-semantics v0.1.0 (/scratch/semantics/kevm)
time:   0.008; rss:   56MB ->   63MB (   +7MB)\tparse_crate
time:   7.088; rss:   70MB -> 1213MB (+1143MB)\texpand_crate
time:  13.131; rss: 1576MB -> 1251MB ( -325MB)\ttype_check_crate
time:  60.460; rss:   34MB ->  168MB ( +135MB)\ttotal
"""

MACRO_STATS = """\
macro-stats ===================================================================================
macro-stats MACRO EXPANSION STATS: krs_kevm_semantics
macro-stats Macro Name                         Uses      Lines  Avg Lines      Bytes  Avg Bytes
macro-stats -----------------------------------------------------------------------------------
macro-stats ::std::vec!                       6_742    822_157      121.9 63_530_435    9_423.1
macro-stats k::rules!                             3    500_529  166_843.0 31_007_15910_335_719.7
macro-stats ::krs::__private::inventory::submit!
macro-stats                                   1_099     17_580       16.0    693_174      630.7
macro-stats ===================================================================================
"""


def event(name, ts, dur, tid=1, args=None, cat="GenericActivity"):
    arguments = "null" if not args else json.dumps({f"arg{i}": value for i, value in enumerate(args)}, separators=(",", ":"))
    return (f'{{"name":{json.dumps(name)},"cat":"{cat}","ph":"X","ts":{ts},"dur":{dur},"pid":7,"tid":{tid},'
            f'"args":{arguments}}}')


class ParserTests(unittest.TestCase):
    def test_time_passes(self):
        passes = rustc_profile.parse_time_passes(TIME_PASSES)
        self.assertEqual([p["pass"] for p in passes], ["parse_crate", "expand_crate", "type_check_crate", "total"])
        self.assertEqual(passes[2], {"pass": "type_check_crate", "seconds": 13.131,
                                     "rss_start_mb": 1576, "rss_end_mb": 1251})

    def test_macro_stats_split_joined_columns_and_wrapped_names(self):
        rows = {row["macro"]: row for row in rustc_profile.parse_macro_stats(MACRO_STATS)}
        self.assertEqual(rows["::std::vec!"], {"macro": "::std::vec!", "uses": 6742, "lines": 822157,
                                               "bytes": 63530435})
        self.assertEqual(rows["k::rules!"]["bytes"], 31007159)
        self.assertEqual(rows["::krs::__private::inventory::submit!"]["uses"], 1099)

    def test_summarize_json(self):
        document = {"query_data": [{"label": "typeck_root", "time": {"secs": 2, "nanos": 500000000},
                                    "self_time": {"secs": 1, "nanos": 0}, "invocation_count": 3,
                                    "number_of_cache_hits": 4}],
                    "artifact_sizes": [{"label": "cgu_instructions", "value": 9}], "total_time": {"secs": 5, "nanos": 0}}
        parsed = rustc_profile.parse_summarize(document)
        self.assertEqual(parsed["total_seconds"], 5.0)
        self.assertEqual(parsed["queries"][0]["self_seconds"], 1.0)
        self.assertEqual(parsed["artifact_sizes"], {"cgu_instructions": 9})


class PhaseTests(unittest.TestCase):
    def trace(self):
        return "[" + ",".join([
            event("resolver_for_lowering_raw", 0, 100, cat="Query"),
            event("expand_crate", 5, 60),
            event("resolve_crate", 70, 25),
            event("analysis", 100, 300, cat="Query"),
            event("type_check_crate", 100, 120),
            event("typeck_root", 110, 50, args=["krs_x::__krs_head_rule_descriptor_0123456789abcdef"], cat="Query"),
            event("typeck_root", 115, 10, args=["krs_x::inner"], cat="Query"),
            event("MIR_borrow_checking", 220, 170),
            event("codegen_crate", 400, 40),
            event("LLVM_passes", 400, 200, tid=2),
            event("finish_ongoing_codegen", 440, 160),
            event("link", 600, 5),
        ]) + "]"

    def test_events_nest_and_self_time(self):
        events = rustc_profile.with_self_time(rustc_profile.iter_trace_events(self.trace()))
        outer = next(e for e in events if e["name"] == "typeck_root" and e["dur"] == 50)
        self.assertEqual(outer["self"], 40)
        self.assertEqual(outer["args"], ["krs_x::__krs_head_rule_descriptor_0123456789abcdef"])

    def test_phases_resolve_containers_and_ignore_worker_threads(self):
        phases = rustc_profile.phases(rustc_profile.with_self_time(rustc_profile.iter_trace_events(self.trace())))
        categories = phases["categories"]
        self.assertEqual(categories["expansion"], 60e-6)
        self.assertEqual(categories["type checking"], 120e-6)
        self.assertEqual(categories["borrow checking"], 170e-6)
        self.assertEqual(categories["llvm"], 160e-6)
        # containers' self time (15 + 10 microseconds) is `other`
        self.assertAlmostEqual(categories["other"], 25e-6)
        self.assertAlmostEqual(phases["sum_seconds"], 605e-6)
        self.assertEqual(phases["llvm_passes_worker_seconds"], 200e-6)

    def test_wrapper_is_posix_sh_and_selects_by_crate_name(self):
        self.assertTrue(rustc_profile.WRAPPER.startswith("#!/bin/sh\n"))
        self.assertIn("--crate-name", rustc_profile.WRAPPER)
        self.assertIn("RUSTC_BOOTSTRAP=1", rustc_profile.WRAPPER)

    def test_profiles_are_registered(self):
        for name in ("rustc", "rustc-trace"):
            profile = bench.PROFILES[name]
            self.assertEqual(profile.stages, ("collector-build", "cargo-check"))
            self.assertEqual(profile.receipt_field, "rustc_profile")


EXPANDED = """\
pub fn lookup(__krs_symbolic_subject: Machine) -> Machine {
    ::core::panicking::panic_fmt(format_args!("no runtime"));
}
#[doc(hidden)]
fn __krs_head_rule_sort_0123456789abcdef() -> ::core::any::TypeId {
    ::core::any::TypeId::of::<Machine>()
}
#[doc(hidden)]
fn __krs_head_rule_descriptor_0123456789abcdef() -> ::k::HostDescriptor {
    ::k::HostDescriptor {
        id: ::k::HostItemId::from_macro_context("krs-x", "0.1.0",
                "/scratch/x", "krs_x", "lookup", ::k::ItemKind::Rule,
                "").expect("valid"),
        provenance: ::k::HostProvenance::new(::k::HostSourceAnchor::new({
                    let source = ::std::path::Path::new("/scratch/x/src/lib.rs");
                    source.to_string_lossy().replace('\\\\', "/")
                },
                ::k::HostSourcePosition::new(12u32, 1u32).expect("one-based"),
                ::k::HostSourcePosition::new(14u32, 2u32).expect("one-based"),
                ::k::AnchorPrecision::Exact).expect("ordered (really)")),
    }
}
const _: () = {
    static __INVENTORY: u8 = 0;
};
"""


class AttributionTests(unittest.TestCase):
    def test_classify(self):
        crate = "krs_x"
        self.assertEqual(attribution.classify("krs_x[abcd1234]::__krs_head_rule_descriptor_0123456789abcdef", crate)
                         ["prefix"], "head_rule_descriptor")
        variant = attribution.classify("krs_x::__krs_enum_constructor_0123456789abcdef_3", crate)
        self.assertEqual((variant["prefix"], variant["variant"]), ("enum_constructor", "3"))
        self.assertEqual(attribution.classify("krs_x::_#12::__CTOR", crate)["prefix"], "registration")
        self.assertEqual(attribution.classify("<krs_x::Machine>::__krs_initializer_payload", crate)["prefix"],
                         "initializer_payload")
        self.assertEqual(attribution.classify("core[8c5a]::ptr::drop_glue::<krs_ir::X>", crate)["prefix"],
                         "generic:core")
        self.assertEqual(attribution.classify("krs_x::lookup", crate)["authored"], "lookup")
        instance = "(Instance { def: Item(DefId(0:77 ~ krs_x[a581]::__krs_sort_type_0123456789abcdef)), args: [] }, U)"
        self.assertEqual(attribution.classify(instance, crate)["prefix"], "sort_type")

    def test_expanded_constructs(self):
        expanded = attribution.expanded_constructs(EXPANDED, "krs_x")
        construct = expanded["constructs"]["0123456789abcdef"]
        self.assertEqual(construct["label"], "Rule lookup")
        self.assertEqual(construct["macro"], "rules! clause")
        self.assertEqual(construct["line"], 12)
        chunks = {chunk["prefix"]: chunk for chunk in expanded["chunks"]}
        self.assertEqual(chunks["head_rule_descriptor"]["anchors"], 1)
        self.assertEqual(chunks["head_rule_descriptor"]["anchor_lines"], 7)
        self.assertEqual(chunks["authored"]["authored"], "lookup")
        self.assertIn("registration", chunks)

    def test_expanded_constructs_with_compact_anchors(self):
        compact = '''\
#[doc(hidden)]
fn __krs_head_rule_descriptor_0123456789abcdef() -> ::k::HostDescriptor {
    ::k::HostDescriptor {
        id: ::k::HostItemId::from_macro_context("krs-x", "0.1.0",
                "/scratch/x", "krs_x", "lookup", ::k::ItemKind::Rule,
                "").expect("valid"),
        provenance: ::k::__krs_host_provenance(env!("CARGO_MANIFEST_DIR"),
            &["src/lib.rs"], ::k::__KrsRawAnchor {
                file: 0usize, absolute: false, start: (12u32, 1u32),
                end: (14u32, 2u32), exact: true
            }, &[]),
    }
}
'''
        expanded = attribution.expanded_constructs(compact, "krs_x")
        construct = expanded["constructs"]["0123456789abcdef"]
        self.assertEqual(construct["line"], 12)
        chunks = {chunk["prefix"]: chunk for chunk in expanded["chunks"]}
        self.assertEqual(chunks["head_rule_descriptor"]["anchors"], 1)

    def test_source_macro_prefers_covering_span_then_preceding_attribute(self):
        spans = [{"macro": "k::rules!", "start": 10, "end": 90}, {"macro": "#[k::equation]", "start": 100, "end": 100}]
        self.assertEqual(attribution.source_macro(12, spans), "k::rules!")
        self.assertEqual(attribution.source_macro(104, spans), "#[k::equation]")
        self.assertIsNone(attribution.source_macro(5, spans))

    def test_llvm_lines_nm_and_sections(self):
        rows = attribution.parse_llvm_lines(
            "  Lines          Copies        Function name\n"
            "  5110065        10578         (TOTAL)\n"
            "    69979 (1.4%,  1.4%)      1 (0.0%,  0.0%)  krs_x[fc]::__krs_head_rule_descriptor_b28b6a05522fec28\n")
        self.assertEqual(rows, [{"name": "krs_x[fc]::__krs_head_rule_descriptor_b28b6a05522fec28",
                                 "lines": 69979, "copies": 1}])
        symbols = attribution.parse_nm("0000000000001000 0000000000000040 t krs_x::__krs_sort_type_0123456789abcdef\n"
                                       "0000000000002000 0000000000000008 d krs_x::_::__INVENTORY\n")
        self.assertEqual([(s["section"], s["size"]) for s in symbols], [("text", 64), ("data", 8)])
        sections = attribution.parse_sections(
            "  [15] .text             PROGBITS        0000000000016040 016040 26b1d3a 00  AX  0   0 64\n"
            "  [21] .init_array       INIT_ARRAY      0000000002d9a9e8 2d999e8 002278 08  WA  0   0  8\n")
        self.assertEqual(sections[".init_array"] // 8, 1103)

    def test_least_squares(self):
        a, b = attribution.least_squares_two([(1, 0), (0, 1), (2, 3)], [2, 5, 19])
        self.assertAlmostEqual(a, 2.0)
        self.assertAlmostEqual(b, 5.0)


if __name__ == "__main__":
    unittest.main()
