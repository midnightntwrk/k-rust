"""Unit tests for the sampled-profile folding of tests/perf/sample.py.

    PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/perf -t tests
"""

from __future__ import annotations

import gzip
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from perf import bench, sample  # noqa: E402


def synthetic_profile(directory: Path) -> Path:
    """One process: `_start -> main -> work`, plus an unsymbolized libc leaf and a sleeping sample."""

    profile = {
        "meta": {"interval": 1.0},
        "libs": [
            {"name": "collector", "path": "/nonexistent/collector", "debugName": "collector", "codeId": "c1"},
            {"name": "libc.so.6", "path": "/nonexistent/libc.so.6", "debugName": "libc.so.6", "codeId": "c2"},
        ],
        "threads": [{
            "pid": "7", "processName": "collector", "name": "collector",
            "frameTable": {"length": 4, "address": [16, 32, 48, 64], "func": [0, 1, 2, 3]},
            "funcTable": {"length": 4, "resource": [0, 0, 0, 1]},
            "resourceTable": {"length": 2, "lib": [0, 1]},
            "stackTable": {"length": 4, "prefix": [None, 0, 1, 2], "frame": [0, 1, 2, 3]},
            "samples": {"stack": [2, 2, 2, 3, 1, None], "threadCPUDelta": [900, 1000, 0, 1000, 1000, 5]},
        }],
    }
    sidecar = {
        "string_table": ["_start", "collector::main", "krs_collector::collect::provenance::"
                         "materialize_descriptor_provenance::h0123456789abcdef"],
        "data": [{
            "debug_name": "collector", "code_id": "c1",
            "symbol_table": [{"rva": 0, "size": 20, "symbol": 0}, {"rva": 20, "size": 20, "symbol": 1},
                             {"rva": 40, "size": 20, "symbol": 2}],
            "known_addresses": [[16, 0], [32, 1], [48, 2]],
        }],
    }
    path = directory / "p.samply.json.gz"
    with gzip.open(path, "wt", encoding="utf-8") as handle:
        json.dump(profile, handle)
    (directory / "p.samply.json.syms.json").write_text(json.dumps(sidecar), encoding="utf-8")
    return path


class FoldTests(unittest.TestCase):
    def test_fold_counts_on_cpu_samples_and_names(self):
        with tempfile.TemporaryDirectory() as directory:
            summary, folded = sample.fold(synthetic_profile(Path(directory)), inline_binaries=[])
        (process,) = summary["processes"]
        self.assertEqual(process["samples"], 4)  # the zero-delta and stackless samples are dropped
        self.assertEqual(process["binary"], "collector")
        self.assertEqual(process["named_fraction"], 0.75)
        self.assertEqual(process["binary_fraction"], 1.0)
        self.assertEqual(process["attributed_fraction"], 1.0)
        self.assertEqual(process["spans"]["collector.resolve.provenance"], {"samples": 3, "fraction": 0.75})
        top = {row["function"]: row for row in process["top_self"]} if "top_self" in process else {}
        self.assertEqual(top, {})  # below the detail threshold
        self.assertIn("collector;_start;collector::main;"
                      "krs_collector::collect::provenance::materialize_descriptor_provenance 2\n", folded)
        self.assertTrue(any(line.endswith(";[libc.so.6+0x40] 1\n") for line in folded))

    def test_detail_tables_group_by_crate(self):
        process = sample.ProcessFold("1", "p")
        work = (("_start", "bin"), ("krs_ir::bundle::<impl krs_ir::bundle::DescriptorBundle>::to_collector_protocol_measured", "bin"),
                ("<serde_json::ser::Compound<W,F> as serde::ser::SerializeMap>::serialize_entry", "bin"))
        process.stacks[work] = 60
        process.stacks[work[:2] + (("__memmove_avx_unaligned_erms", "libc.so.6"),)] = 40
        process.samples = 100
        process.roots["bin"] = 100
        summary = sample.summarize(process)
        self.assertEqual(summary["spans"]["collector.serialize"]["fraction"], 1.0)
        self.assertEqual(summary["crates_self"][0], {"crate": "serde_json", "samples": 60, "fraction": 0.6})
        self.assertIn({"crate": "(libc.so.6)", "samples": 40, "fraction": 0.4}, summary["crates_self"])
        self.assertEqual(summary["top_inclusive"][0]["samples"], 100)


class SymbolTests(unittest.TestCase):
    def test_crate_of(self):
        self.assertEqual(sample.crate_of("core::ptr::drop_in_place<krs_ir::X>", "b"), "std")
        self.assertEqual(sample.crate_of("<&mut serde_json::Serializer as serde::Serializer>::f", "b"), "serde_json")
        self.assertEqual(sample.crate_of("malloc", "libc.so.6"), "(libc.so.6)")
        self.assertEqual(sample.crate_of("[b+0x10]", "b"), "(b)")
        self.assertEqual(sample.crate_of("<usize as core::convert::From<u8>>::from", "b"), "std")
        self.assertEqual(sample.crate_of("<T as alloc::vec::spec_from_elem::SpecFromElem>::from_elem", "b"), "std")
        self.assertEqual(sample.crate_of("void lld::elf::InputSection::writeTo<x::Y>(char*)", "lld"), "(lld)")
        self.assertEqual(sample.crate_of("try_span<krs_k_rust::X>", "krs"), "(krs)")

    def test_crate_of_file(self):
        self.assertEqual(sample.crate_of_file(
            "/h/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.140/src/ser.rs:10"), "serde_json")
        self.assertEqual(sample.crate_of_file("/h/.rustup/toolchains/s/lib/rustlib/src/rust/library/core/src/x.rs:1"),
                         "std")
        self.assertEqual(sample.crate_of_file("/w/krs/crates/krs-ir/src/bundle.rs:3"), "krs_ir")
        self.assertIsNone(sample.crate_of_file("??:0"))

    def test_clean_name_drops_hashes_and_generic_arguments(self):
        self.assertEqual(sample.clean_name("<core::option::Option<k::Sort>>::or_else::<<k::G>::f::{closure#0}>"),
                         "<core::option::Option<k::Sort>>::or_else")
        self.assertEqual(sample.clean_name("a::b::<fn(&T) -> bool>::c::h0123456789abcdef"), "a::b::c")

    def test_addr2line_output_is_outermost_first(self):
        text = ("0x0000000000000010\nclone<u8>\n/w/crates/krs-ir/src/a.rs:1\nm::outer\nb.rs:2\n"
                "0x0000000000000020\n??\n??:0\n0x0000000000000030\n<core::str::Chars as Iterator>::next\n/w/crates/krs-ir/src/a.rs:1\n")
        self.assertEqual(sample.parse_addr2line(text), {16: ["m::outer", "krs_ir::…::clone"], 32: [],
                                                        48: ["<core::str::Chars as Iterator>::next"]})

    def test_sidecar_path(self):
        self.assertEqual(sample.sidecar_path(Path("x/a.samply.json.gz")), Path("x/a.samply.json.syms.json"))


class ProfileRegistrationTests(unittest.TestCase):
    def test_samply_mode_is_registered_for_krs_stages(self):
        profile = bench.PROFILES[sample.NAME]
        self.assertEqual(set(profile.stages), {"krs-check", "krs-emit-k", "krs-build"})
        self.assertIsNotNone(profile.wrap)
        self.assertIsNotNone(profile.collect)


if __name__ == "__main__":
    unittest.main()
