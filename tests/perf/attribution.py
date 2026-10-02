#!/usr/bin/env python3
"""Attribute a semantics crate's compile cost to generated items and macro kinds.

KRS macros name every generated item `__krs_<kind>_<nonce>...`, where the
16-hex nonce identifies one source construct (a `rules!` clause, a
`#[k::rule]` or `#[k::equation]` sentence, a constructor or constructor
enum, a sort, ...). This tool builds one port's generated collector with the
semantics crate's rustc profiled and groups the cost of that crate by
generated-item prefix, by construct, and by source macro kind:

- LLVM IR lines and copies (`cargo llvm-lines --files` over `--emit=llvm-ir`);
- self-profile self time of `typeck_root`, `mir_borrowck`, `optimized_mir`
  (and the other MIR queries) per item, from a `default,args` self-profile;
- codegen time: rustc runs codegen and LLVM per codegen unit, not per item,
  so each unit's time is distributed over items in proportion to their IR
  lines (an estimate, labelled as such);
- `.text`/`.rodata`/`.data` symbol bytes in the collector binary (`nm`) and
  its section table (`readelf -SW`), including the `.init_array` entry count;
- `-Zmacro-stats` lines per macro and `expand_proc_macro` time per macro;
- provenance anchors: expanded lines inside `HostSourceAnchor::new(...)` or `__KrsRawAnchor { ... }` per construct (from `-Zunpretty=expanded`), and a least-squares estimate of LLVM IR lines per anchor line.

`--registration explicit` (or `both`) repeats the build with the crate-root
registration table that `RegistrationMode::Explicit` requires (taken from an
inventory census, as the explicit-registration gate does) and the `krs`
facade's `inventory` feature off, to size inventory's per-registration cost.

    python3 tests/perf/attribution.py run --port kevm [--registration both] [--out DIR]
    python3 tests/perf/attribution.py report DIR [--top 15]

Everything runs in scratch copies; the repository's `semantics/` is never
written. Attribution runs are profiled builds and are not timing receipts.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any, Iterable, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from perf import rustc_profile  # noqa: E402


SCHEMA = "krs-perf-attribution/1"
PROFILE_FLAGS = ("-Ztime-passes", "-Zmacro-stats", "-Zself-profile-events=default,args")
# MIR queries whose per-item self time is attributed. The ticket's three
# (typeck, mir_borrowck, optimized_mir) plus the MIR building they force.
ITEM_QUERIES = ("typeck_root", "typeck", "mir_borrowck", "optimized_mir", "mir_built", "thir_body",
                "mir_drops_elaborated_and_const_checked", "check_unsafety", "items_of_instance")
# Per-codegen-unit work, on the main thread (IR building) and LLVM workers.
CGU_EVENTS = ("codegen_module", "LLVM_module_optimize", "LLVM_module_codegen")

_DISAMBIGUATOR = re.compile(r"\[[0-9a-f]{4,16}\]")
_NONCE_ITEM = re.compile(r"__krs_([a-z0-9]+(?:_[a-z0-9]+)*?)_([0-9a-f]{16})(?:_(\d+))?(?![0-9a-f])")
_KRS_METHOD = re.compile(r"(?:^|::|>::)(__krs_[a-z_]+)")
_DEF_PATH = re.compile(r"DefId\(\d+:\d+ ~ ([^)\s]+)\)")
# Prefixes whose trailing `_N` names one variant of a `#[k::constructors]` enum.
_PER_VARIANT = ("enum_constructor", "enum_grammar")


# --- item classification ---------------------------------------------------------------------


def normalize(name: str) -> str:
    return _DISAMBIGUATOR.sub("", name)


def classify(name: str, crate: str) -> dict[str, Any]:
    """Group an item path (a symbol, IR function, or query key).

    Returns `{prefix, nonce, variant, authored}`: `prefix` is the generated
    kind (`head_rule_descriptor`, ...), `registration`, `generic:<crate>`
    for instantiations of other crates' generics, or `authored`.
    """

    name = normalize(name)
    instance = _DEF_PATH.search(name)
    if instance:
        name = instance.group(1)
    match = _NONCE_ITEM.search(name)
    if match:
        prefix = match.group(1)
        variant = match.group(3) if prefix in _PER_VARIANT else None
        return {"prefix": prefix, "nonce": match.group(2), "variant": variant, "authored": None}
    method = _KRS_METHOD.search(name)
    if method and crate in name:
        return {"prefix": method.group(1)[len("__krs_"):], "nonce": None, "variant": None, "authored": None}
    if re.match(rf"^<?{re.escape(crate)}::_(?:\[\d+\]|#\d+)?::", name) or "__KRS_REGISTRATIONS" in name:
        return {"prefix": "registration", "nonce": None, "variant": None, "authored": None}
    stripped = name.lstrip("<&*")
    if stripped.startswith(f"{crate}::"):
        rest = stripped[len(crate) + 2:]
        head = re.split(r"::|[<>{}\s]", rest, maxsplit=1)[0] or rest
        return {"prefix": "authored", "nonce": None, "variant": None, "authored": head}
    root = re.split(r"::|[<>\s\[]", stripped, maxsplit=1)[0] or "?"
    return {"prefix": f"generic:{root}", "nonce": None, "variant": None, "authored": None}


MACRO_BY_PREFIX: tuple[tuple[str, str], ...] = (
    ("head_rule", "rules! clause"),
    ("rule_application", "rules! clause"),
    ("constructor", "#[k::constructor]"),
    ("enum_", "#[k::constructors]"),
    ("variant", "#[k::constructors]"),
    ("sort", "k::sorts!"),
    ("subsort", "k::sorts!"),
    ("configuration_claim", "#[k::claim]"),
    ("claim", "#[k::claim]"),
    ("configuration", "#[k::configuration]"),
    ("cell", "#[k::cell]"),
    ("initializer", "#[k::init]"),
    ("registration", "registration"),
    ("register_descriptors", "registration"),
)
SENTENCE_MACRO = {"Transition": "#[k::rule]", "Equation": "#[k::equation]",
                  "Simplification": "#[k::simplification]", "Alias": "#[k::alias]"}


def macro_kind(prefix: str, construct: Mapping[str, Any] | None) -> str:
    if construct is not None and construct.get("macro"):
        return construct["macro"]
    if prefix.startswith("generic:"):
        return "generic instantiations"
    if prefix == "authored":
        return "authored code"
    for start, kind in MACRO_BY_PREFIX:
        if prefix.startswith(start):
            return kind
    if prefix.startswith(("rule_", "strictness", "context_alias")):
        return "#[k::rule]/#[k::equation]"
    return f"other generated ({prefix})"


# --- expanded source ------------------------------------------------------------------------------


_FACTORY_ID = re.compile(
    r'from_macro_context\(\s*"(?:[^"\\]|\\.)*",\s*"(?:[^"\\]|\\.)*",\s*"(?:[^"\\]|\\.)*",\s*"(?:[^"\\]|\\.)*",'
    r'\s*"((?:[^"\\]|\\.)*)",\s*::\w+::ItemKind::(\w+)')
_SENTENCE = re.compile(r"::\w+::SentenceKind::(\w+)")
_ANCHOR = "HostSourceAnchor::new("
_RAW_ANCHOR = re.compile(r"__KrsRawAnchor\s*\{")
_POSITION = re.compile(r"(?:HostSourcePosition::new\(|start:\s*\()(\d+)u32,\s*(\d+)u32\)")
_ITEM_NAME = re.compile(r"^(?:pub(?:\([^)]*\))?\s+)?(?:const\s+|unsafe\s+|async\s+|extern\s+\"C\"\s+)*"
                        r"(?:fn|struct|enum|trait|type|static|const|mod|union)\s+([A-Za-z_][A-Za-z0-9_]*)")


def _balanced_end(text: str, start: int, opening: str = "(", closing: str = ")") -> int:
    """Index just past the delimiter that closes the one opened before `start`."""

    depth, index, length = 1, start, len(text)
    while index < length and depth:
        character = text[index]
        if character == '"':
            index += 1
            while index < length and text[index] != '"':
                index += 2 if text[index] == "\\" else 1
        elif character == opening:
            depth += 1
        elif character == closing:
            depth -= 1
        index += 1
    return index


def top_level_chunks(text: str) -> Iterable[tuple[str, str]]:
    """(first line, chunk) for each item the pretty-printer starts at column 0."""

    lines = text.splitlines(keepends=True)
    start = 0
    for index in range(1, len(lines) + 1):
        if index == len(lines) or (lines[index][:1] not in ("", " ", "\t", "\n", "}", ")", "]")
                                   and not lines[index].startswith(("#[", "#!["))):
            # attributes on their own lines belong to the following item
            chunk = "".join(lines[start:index])
            first = next((line for line in lines[start:index] if not line.startswith("#")), lines[start])
            yield first, chunk
            start = index
    return


def expanded_constructs(text: str, crate: str) -> dict[str, Any]:
    """Constructs, per-chunk expanded lines, and anchor lines from `-Zunpretty=expanded`.

    Returns `{constructs {key: {...}}, chunks [...], totals}` where a
    construct key is the nonce (plus `#variant` for enum variants) and a chunk
    row is `{prefix, key, authored, lines, bytes, anchors, anchor_lines, anchor_bytes}`.
    """

    constructs: dict[str, dict[str, Any]] = {}
    chunks = []
    for first, chunk in top_level_chunks(text):
        header = chunk[chunk.index(first):].partition("{")[0].strip()
        if header.startswith("const _"):
            info = {"prefix": "registration", "nonce": None, "variant": None, "authored": None}
        else:
            match = _NONCE_ITEM.search(header)
            if match:
                info = classify(match.group(0), crate)
            else:
                named = _ITEM_NAME.match(header)
                if header.startswith("impl") and "__krs_" in chunk:
                    method = _KRS_METHOD.search(chunk)
                    info = {"prefix": method.group(1)[len("__krs_"):] if method else "impl", "nonce": None,
                            "variant": None, "authored": None}
                else:
                    info = {"prefix": "authored", "nonce": None, "variant": None,
                            "authored": named.group(1) if named else header.split("(")[0][:60]}
        key = construct_key(info)
        anchors = anchor_lines = anchor_bytes = 0
        position = chunk.find(_ANCHOR)
        while position >= 0:
            end = _balanced_end(chunk, position + len(_ANCHOR))
            anchors += 1
            anchor_lines += chunk.count("\n", position, end) + 1
            anchor_bytes += end - position
            position = chunk.find(_ANCHOR, end)
        for match in _RAW_ANCHOR.finditer(chunk):
            end = _balanced_end(chunk, match.end(), "{", "}")
            anchors += 1
            anchor_lines += chunk.count("\n", match.start(), end) + 1
            anchor_bytes += end - match.start()
        factory = _FACTORY_ID.search(chunk) if "HostDescriptor" in header else None
        if factory is not None and key is not None:
            sentence = _SENTENCE.search(chunk)
            construct = constructs.setdefault(key, {"key": key, "names": [], "item_kind": None, "sentence": None})
            construct["names"].append(json.loads(f'"{factory.group(1)}"'))
            construct["item_kind"] = construct["item_kind"] or factory.group(2)
            if sentence and info["prefix"] == "rule_descriptor":
                construct["sentence"] = sentence.group(1)
            provenance = chunk.find("HostProvenance::new(")
            if provenance < 0:
                provenance = chunk.find("__krs_host_provenance(")
            position = _POSITION.search(chunk, provenance if provenance >= 0 else 0)
            if position and "line" not in construct:
                construct["line"] = int(position.group(1))
            construct["factory_prefix"] = construct.get("factory_prefix") or info["prefix"]
        chunks.append({**info, "key": key, "lines": chunk.count("\n"), "bytes": len(chunk), "anchors": anchors,
                       "anchor_lines": anchor_lines, "anchor_bytes": anchor_bytes})
    for construct in constructs.values():
        construct["macro"] = construct_macro(construct)
        construct["label"] = f"{construct['item_kind'] or '?'} {construct['names'][0]}" if construct["names"] else construct["key"]
    return {"constructs": constructs, "chunks": chunks}


def construct_key(info: Mapping[str, Any]) -> str | None:
    if info.get("nonce") is None:
        return None
    return info["nonce"] + (f"#{info['variant']}" if info.get("variant") is not None else "")


def construct_macro(construct: Mapping[str, Any]) -> str:
    prefix = construct.get("factory_prefix") or ""
    if prefix == "rule_descriptor":
        return SENTENCE_MACRO.get(construct.get("sentence") or "", "#[k::rule]/#[k::equation]")
    for start, kind in MACRO_BY_PREFIX:
        if prefix.startswith(start):
            return kind
    kinds = {"Sort": "k::sorts!", "Cell": "#[k::cell]", "Configuration": "#[k::configuration]", "Claim": "#[k::claim]"}
    return kinds.get(construct.get("item_kind") or "", f"other generated ({prefix})")


def resolve_construct(info: Mapping[str, Any], constructs: Mapping[str, Any],
                      by_name: Mapping[str, str]) -> Mapping[str, Any] | None:
    key = construct_key(info)
    if key is not None:
        found = constructs.get(key)
        if found is None and "#" in key:
            found = constructs.get(key.split("#", 1)[0])
        return found
    if info.get("authored") and info["authored"] in by_name:
        return constructs.get(by_name[info["authored"]])
    return None


# --- parsers for the measured artifacts ---------------------------------------------------------


_LLVM_LINE = re.compile(r"^\s*(\d+)\s+\([^)]*\)\s+(\d+)\s+\([^)]*\)\s+(.*\S)\s*$")


def parse_llvm_lines(text: str) -> list[dict[str, Any]]:
    rows = []
    for line in text.splitlines():
        match = _LLVM_LINE.match(line)
        if match and match.group(3) != "(TOTAL)":
            rows.append({"name": match.group(3), "lines": int(match.group(1)), "copies": int(match.group(2))})
    return rows


_NM_LINE = re.compile(r"^([0-9a-f]+)\s+([0-9a-f]+)\s+(\S)\s+(.+)$")


def parse_nm(text: str) -> list[dict[str, Any]]:
    symbols = []
    for line in text.splitlines():
        match = _NM_LINE.match(line.strip())
        if match:
            kind = match.group(3)
            section = ("text" if kind in "tTwW" else "rodata" if kind in "rR" else
                       "data" if kind in "dDgG" else "bss" if kind in "bBsS" else kind)
            symbols.append({"name": match.group(4), "size": int(match.group(2), 16), "section": section})
    return symbols


_SECTION = re.compile(r"^\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+[0-9a-f]+\s+[0-9a-f]+\s+([0-9a-f]+)\s")


def parse_sections(text: str) -> dict[str, int]:
    sections = {}
    for line in text.splitlines():
        match = _SECTION.match(line)
        if match:
            sections[match.group(1)] = int(match.group(2), 16)
    return sections


_SPAN = re.compile(r":(\d+):\d+: (\d+):\d+$")


def source_macro(line: int | None, spans: Sequence[Mapping[str, Any]]) -> str | None:
    """The innermost proc-macro invocation whose source span covers `line`."""

    if line is None:
        return None
    covering = [span for span in spans if span["start"] <= line <= span["end"]]
    if covering:
        return min(covering, key=lambda span: span["end"] - span["start"])["macro"]
    # An attribute macro's span is the attribute itself; the item follows it.
    preceding = [span for span in spans if span["end"] <= line]
    return max(preceding, key=lambda span: (span["end"], span["start"]))["macro"] if preceding else None


def item_query_times(trace_text: str) -> dict[str, Any]:
    """Per-item self time of `ITEM_QUERIES`, per-CGU codegen time, and per-macro expansion time."""

    events = rustc_profile.with_self_time(rustc_profile.iter_trace_events(trace_text))
    items: dict[tuple[str, str], float] = defaultdict(float)
    cgus: dict[str, dict[str, float]] = defaultdict(lambda: defaultdict(float))
    cgu_sizes: dict[str, int] = {}
    macros: dict[str, dict[str, float]] = defaultdict(lambda: defaultdict(float))
    totals: dict[str, float] = defaultdict(float)
    spans: list[dict[str, Any]] = []
    for event in events:
        name = event["name"]
        if name in ITEM_QUERIES and event["args"]:
            items[(name, event["args"][0])] += event["self"] / 1e6
            totals[name] += event["self"] / 1e6
        elif name in CGU_EVENTS and event["args"]:
            cgus[event["args"][0]][name] += event["dur"] / 1e6
            if name == "codegen_module" and len(event["args"]) > 1 and event["args"][1].isdigit():
                cgu_sizes[event["args"][0]] = int(event["args"][1])
        elif name == "expand_proc_macro" and event["args"]:
            macro = macros[event["args"][0]]
            macro["seconds"] += event["dur"] / 1e6
            macro["invocations"] += 1
            span = _SPAN.search(event["args"][1]) if len(event["args"]) > 1 else None
            if span:
                spans.append({"macro": event["args"][0], "start": int(span.group(1)), "end": int(span.group(2)),
                              "seconds": round(event["dur"] / 1e6, 6)})
    return {
        "items": [{"query": query, "item": item, "self_seconds": round(seconds, 6)}
                  for (query, item), seconds in items.items()],
        "query_totals": {name: round(value, 6) for name, value in totals.items()},
        "cgus": {cgu: {**{k: round(v, 6) for k, v in times.items()}, "size_estimate": cgu_sizes.get(cgu)}
                 for cgu, times in cgus.items()},
        "expand_proc_macro": {name: {"seconds": round(v["seconds"], 6), "invocations": int(v["invocations"])}
                              for name, v in macros.items()},
        "expand_proc_macro_spans": spans,
        "phases": rustc_profile.phases(events),
    }


# --- aggregation ------------------------------------------------------------------------------------


def least_squares_two(xs: Sequence[tuple[float, float]], ys: Sequence[float]) -> tuple[float, float] | None:
    """Fit y = a*x1 + b*x2 (no intercept) by the normal equations."""

    s11 = sum(x1 * x1 for x1, _ in xs)
    s22 = sum(x2 * x2 for _, x2 in xs)
    s12 = sum(x1 * x2 for x1, x2 in xs)
    t1 = sum(x1 * y for (x1, _), y in zip(xs, ys))
    t2 = sum(x2 * y for (_, x2), y in zip(xs, ys))
    determinant = s11 * s22 - s12 * s12
    if abs(determinant) < 1e-9:
        return None
    return ((t1 * s22 - t2 * s12) / determinant, (s11 * t2 - s12 * t1) / determinant)


def aggregate(measured: Mapping[str, Any], crate: str) -> dict[str, Any]:
    """Group every measured quantity by prefix, construct, and macro kind."""

    expanded = measured["expanded"]
    constructs = expanded["constructs"]
    by_name: dict[str, str] = {}
    for key, construct in constructs.items():
        for name in construct["names"]:
            by_name.setdefault(name, key)
    spans = measured["queries"].get("expand_proc_macro_spans") or []
    for construct in constructs.values():
        construct["source_macro"] = source_macro(construct.get("line"), spans)
    groups: dict[str, dict[str, dict[str, float]]] = {"prefix": {}, "macro": {}, "source_macro": {}, "construct": {}}

    def add(info: Mapping[str, Any], metric: str, value: float) -> None:
        construct = resolve_construct(info, constructs, by_name)
        keys = {
            "prefix": info["prefix"],
            "macro": macro_kind(info["prefix"], construct),
            "source_macro": (construct.get("source_macro") if construct is not None else None)
            or macro_kind(info["prefix"], construct),
            "construct": construct["label"] if construct is not None else None,
        }
        for dimension, key in keys.items():
            if key is None:
                continue
            row = groups[dimension].setdefault(key, defaultdict(float))
            row[metric] += value
            if dimension == "construct" and construct is not None:
                row["_macro"] = construct["macro"]  # type: ignore[assignment]

    llvm_total = sum(row["lines"] for row in measured["llvm_lines"])
    for row in measured["llvm_lines"]:
        info = classify(row["name"], crate)
        add(info, "llvm_lines", row["lines"])
        add(info, "llvm_copies", row["copies"])
    queries = measured["queries"]
    codegen_seconds = sum(sum(v for k, v in times.items() if k != "size_estimate")
                          for times in queries["cgus"].values())
    for row in measured["llvm_lines"]:
        if llvm_total:
            add(classify(row["name"], crate), "codegen_seconds_est", codegen_seconds * row["lines"] / llvm_total)
    for row in queries["items"]:
        add(classify(row["item"], crate), f"{row['query']}_seconds", row["self_seconds"])
    for symbol in measured["symbols"]:
        if crate not in normalize(symbol["name"]):
            continue
        add(classify(symbol["name"], crate), f"{symbol['section']}_bytes", symbol["size"])
        add(classify(symbol["name"], crate), "symbols", 1)
    for chunk in expanded["chunks"]:
        info = {key: chunk[key] for key in ("prefix", "nonce", "variant", "authored")}
        for metric in ("lines", "anchors", "anchor_lines", "anchor_bytes"):
            add(info, f"expanded_{metric}", chunk[metric])

    # Provenance anchors as a kind: their expanded lines, and IR lines per anchor
    # line fitted over descriptor factories (IR ~ a*anchor_lines + b*other_lines).
    factory_ir: dict[str, float] = defaultdict(float)
    for row in measured["llvm_lines"]:
        info = classify(row["name"], crate)
        if info["prefix"].endswith(("descriptor", "grammar", "constructor", "claim")) and info["nonce"]:
            factory_ir[construct_key(info) or ""] += row["lines"]
    factory_expanded: dict[str, list[float]] = defaultdict(lambda: [0.0, 0.0])
    for chunk in expanded["chunks"]:
        if chunk["key"] in factory_ir and chunk["prefix"].endswith(("descriptor", "grammar", "constructor", "claim")):
            factory_expanded[chunk["key"]][0] += chunk["anchor_lines"]
            factory_expanded[chunk["key"]][1] += chunk["lines"] - chunk["anchor_lines"]
    keys = [key for key in factory_expanded if factory_ir.get(key)]
    fit = least_squares_two([tuple(factory_expanded[k]) for k in keys], [factory_ir[k] for k in keys])
    anchor_lines_total = sum(chunk["anchor_lines"] for chunk in expanded["chunks"])
    anchors = {
        "anchors": sum(chunk["anchors"] for chunk in expanded["chunks"]),
        "expanded_anchor_lines": anchor_lines_total,
        "expanded_lines": sum(chunk["lines"] for chunk in expanded["chunks"]),
        "fit_factories": len(keys),
        "ir_lines_per_anchor_line": None if fit is None else round(fit[0], 3),
        "ir_lines_per_other_line": None if fit is None else round(fit[1], 3),
        "estimated_anchor_ir_lines": None,
    }
    if fit is not None:
        anchors["estimated_anchor_ir_lines"] = round(fit[0] * sum(factory_expanded[k][0] for k in keys))
        observed = [factory_ir[k] for k in keys]
        mean = sum(observed) / len(observed)
        residual = sum((y - fit[0] * factory_expanded[k][0] - fit[1] * factory_expanded[k][1]) ** 2
                       for k, y in zip(keys, observed))
        spread = sum((y - mean) ** 2 for y in observed)
        anchors["fit_r2"] = round(1 - residual / spread, 4) if spread else None
    named = {key: value for key, value in groups["prefix"].items()
             if not key.startswith("generic:") and key != "authored"}
    attributed_ir = sum(value.get("llvm_lines", 0) for value in named.values())
    attributed_codegen = sum(value.get("codegen_seconds_est", 0) for value in named.values())
    return {
        "totals": {
            "llvm_lines": llvm_total,
            "llvm_functions": len(measured["llvm_lines"]),
            "codegen_seconds": round(codegen_seconds, 6),
            "query_seconds": queries["query_totals"],
            "attributed_llvm_lines_share": round(attributed_ir / llvm_total, 4) if llvm_total else None,
            "attributed_codegen_share": round(attributed_codegen / codegen_seconds, 4) if codegen_seconds else None,
            "constructs": len(constructs),
        },
        "anchors": anchors,
        "groups": {dimension: {key: dict(value) for key, value in rows.items()} for dimension, rows in groups.items()},
    }


# --- running ------------------------------------------------------------------------------------------


def run(command: Sequence[str | os.PathLike[str]], *, cwd: Path, environment: Mapping[str, str], log: Path,
        timeout: float = 3600, check: bool = True) -> subprocess.CompletedProcess[str]:
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    completed = subprocess.run([os.fspath(part) for part in command], cwd=cwd, env=dict(environment),
                               capture_output=True, text=True, check=False, timeout=timeout)
    log.write_text(f"$ {' '.join(os.fspath(p) for p in command)}\n# exit {completed.returncode} in "
                   f"{time.monotonic() - started:.1f}s\n{completed.stdout}\n{completed.stderr}", encoding="utf-8")
    if check and completed.returncode != 0:
        raise GateError(f"{command[0]} {command[1] if len(command) > 1 else ''} failed ({completed.returncode}); see {log}")
    return completed


def explicit_gate() -> Any:
    path = ROOT / "tests" / "explicit-registration" / "verify.py"
    spec = importlib.util.spec_from_file_location("krs_explicit_registration_gate", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CENSUS_MAIN = """\
//! Lists every inventory registration linked into this process.

#[allow(unused_extern_crates)]
extern crate lesson as _;

fn main() {
    let census = krs::__private::registration_census();
    for registration in &census.registrations {
        println!("registration\\t{}\\t{}", registration.path, registration.manifest_dir);
    }
    for manifest_dir in &census.framework_requests {
        println!("framework\\t{manifest_dir}");
    }
}
"""


def prepare_explicit(work: Path, port: Any, environment: Mapping[str, str], logs: Path) -> dict[str, Any]:
    """Append the crate-root registration table and turn the facade's `inventory` off in the scratch copy."""

    gate = explicit_gate()
    semantics = work / "semantics"
    lesson = semantics / port.key
    census = work / "census"
    (census / "src").mkdir(parents=True)
    facade = ROOT / "crates" / "krs"
    (census / "Cargo.toml").write_text(
        "[package]\nname = \"krs-perf-registration-census\"\nversion = \"0.0.0\"\nedition = \"2024\"\n"
        "publish = false\n\n[dependencies]\n"
        f"lesson = {{ package = \"{port.package}\", path = {json.dumps(os.fspath(lesson))} }}\n"
        f"krs = {{ path = {json.dumps(os.fspath(facade))} }}\n\n[workspace]\n", encoding="utf-8")
    (census / "src" / "main.rs").write_text(CENSUS_MAIN, encoding="utf-8")
    output = run(["cargo", "+stable", "run", "--quiet", "--offline", "--manifest-path", census / "Cargo.toml"],
                 cwd=census, environment={**environment, "CARGO_TARGET_DIR": os.fspath(work / "targets" / "census")},
                 log=logs / "census.log")
    shutil.rmtree(work / "targets" / "census", ignore_errors=True)
    registrations, framework = [], []
    for line in output.stdout.splitlines():
        kind, *fields = line.split("\t")
        if kind == "registration" and len(fields) == 2:
            registrations.append({"path": fields[0], "manifest_dir": fields[1]})
        elif kind == "framework" and len(fields) == 1:
            framework.append(fields[0])
    if not registrations:
        raise GateError("the registration census found nothing")
    table = gate.generate_table({"registrations": registrations, "framework_requests": framework}, lesson,
                                rustc_profile.crate_name(port.package), "k")
    with (lesson / port.source).open("a", encoding="utf-8") as source:
        source.write(table)
    # Feature unification is workspace-wide, so every member drops `inventory`.
    dependency = f'k = {{ package = "krs", path = "{facade}" }}'
    for manifest in semantics.glob("*/Cargo.toml"):
        text = manifest.read_text(encoding="utf-8")
        if text.count(dependency) != 1:
            raise GateError(f"{manifest}: the facade dependency has an unexpected form")
        manifest.write_text(text.replace(dependency, dependency[:-2] + ", default-features = false }"),
                            encoding="utf-8")
    return {"registrations": len(registrations), "table_lines": table.count("\n")}


def generate_collector(work: Path, krs: Path, port: Any, registration: str, environment: Mapping[str, str],
                       logs: Path) -> Path:
    shim = work / "cargo-shim"
    shim.mkdir(exist_ok=True)
    real = shutil.which("cargo", path=environment.get("PATH"))
    if real is None:
        raise GateError("cargo is not on PATH")
    (shim / "cargo").write_text("#!/bin/sh\nif [ \"$1\" = build ]; then exit 97; fi\n"
                                f"exec \"{real}\" \"$@\"\n", encoding="utf-8")
    (shim / "cargo").chmod(0o755)
    target = work / "targets" / f"generate-{registration}"
    run([krs, "expand", "--manifest-path", work / "semantics" / "Cargo.toml", "--package", port.package,
         "--definition", "main", "--registration", registration],
        cwd=ROOT, environment={**environment, "CARGO_TARGET_DIR": os.fspath(target),
                               "PATH": os.pathsep.join([os.fspath(shim), environment.get("PATH", "")])},
        log=logs / f"generate-{registration}.log", check=False)
    generated = sorted((target / "krs" / "collectors").glob("*/Cargo.toml"))
    if len(generated) != 1:
        raise GateError(f"collector generation produced {len(generated)} packages; see {logs}")
    destination = work / f"collector-{registration}"
    shutil.copytree(generated[0].parent, destination)
    shutil.rmtree(target, ignore_errors=True)
    return destination


def argv_value(argv: Sequence[str], flag: str) -> str | None:
    for index, argument in enumerate(argv):
        if argument == flag and index + 1 < len(argv):
            return argv[index + 1]
        if argument.startswith(flag + "="):
            return argument.split("=", 1)[1]
    return None


def measure_mode(work: Path, krs: Path, port: Any, registration: str, environment: Mapping[str, str],
                 out: Path, tools: Mapping[str, Any]) -> dict[str, Any]:
    logs = out / "logs"
    crate = rustc_profile.crate_name(port.package)
    collector = generate_collector(work, krs, port, registration, environment, logs)
    target = work / "targets" / registration
    profile_root = work / f"rustc-profile-{registration}"
    base = {**environment, "CARGO_TARGET_DIR": os.fspath(target)}

    def wrapped(flags: Sequence[str]) -> dict[str, str]:
        return {**base, **rustc_profile.profile_environment(profile_root, [crate], flags)}

    invocations = profile_root / "rustc-profile" / "invocations"
    host = subprocess.run(["rustc", "-vV"], env=dict(environment), capture_output=True, text=True,
                          check=True).stdout
    triple_match = re.search(r"^host: (\S+)", host, re.M)
    triple = triple_match.group(1) if triple_match else "x86_64-unknown-linux-gnu"
    build = ["cargo", "+stable", "build", "--offline", "--manifest-path", collector / "Cargo.toml"]
    clean = ["cargo", "+stable", "clean", "--offline", "-p", port.package, "--manifest-path",
             collector / "Cargo.toml", "--target", triple]

    # 1. The collector build with the crate's rustc profiled (query keys recorded).
    print(f"  {registration}: profiled collector build", flush=True)
    run(build, cwd=collector, environment=wrapped(PROFILE_FLAGS), log=logs / f"{registration}-build.log")
    [invocation] = rustc_profile.invocations(invocations, crate=crate)[-1:] or [None]
    if invocation is None:
        raise GateError("the profiled build ran no rustc for the semantics crate")
    stderr = (invocation / "stderr").read_text(encoding="utf-8", errors="replace")
    prefix = rustc_profile.profile_prefix(invocation)
    trace = rustc_profile.trace_events(tools, prefix, invocation / "trace.json", None) if prefix else None
    if trace is None:
        raise GateError("crox is required for attribution (python3 tests/perf/rustc_profile.py tools)")
    queries = item_query_times(trace.read_text(encoding="utf-8"))
    summary = rustc_profile.summarize(tools, prefix)
    shutil.rmtree(invocations, ignore_errors=True)

    # 2. Symbols and sections of the collector binary.
    binaries = [path for path in (target / triple / "debug").glob("krs-generated-collector-*")
                if path.is_file() and os.access(path, os.X_OK)]
    if len(binaries) != 1:
        raise GateError(f"expected one collector executable, found {binaries}")
    nm = run(["nm", "-S", "--size-sort", "-C", binaries[0]], cwd=work, environment=environment,
             log=logs / f"{registration}-nm.log")
    readelf = run(["readelf", "-SW", binaries[0]], cwd=work, environment=environment,
                  log=logs / f"{registration}-readelf.log")
    (logs / f"{registration}-nm.log").write_text("(nm output parsed into the attribution document)\n",
                                                 encoding="utf-8")
    sections = parse_sections(readelf.stdout)

    # 3. LLVM IR of a fresh (non-incremental) compile of the crate.
    print(f"  {registration}: LLVM IR", flush=True)
    run(clean, cwd=collector, environment=base, log=logs / f"{registration}-clean.log")
    run(build, cwd=collector, environment={**wrapped(("--emit=llvm-ir",)), "CARGO_INCREMENTAL": "0"},
        log=logs / f"{registration}-llvm-ir.log")
    [invocation] = rustc_profile.invocations(invocations, crate=crate)[-1:] or [None]
    argv = (invocation / "argv").read_text(encoding="utf-8").splitlines() if invocation else []
    extra = next((a.split("=", 1)[1] for a in argv if a.startswith("extra-filename=")), "")
    ll = Path(argv_value(argv, "--out-dir") or "") / f"{crate}{extra}.ll"
    if not ll.is_file():
        raise GateError(f"no LLVM IR at {ll}")
    lines = run(["cargo", "llvm-lines", "--files", ll], cwd=work, environment=environment,
                log=logs / f"{registration}-llvm-lines.log")
    (logs / f"{registration}-llvm-lines.log").write_text(lines.stdout, encoding="utf-8")
    ll.unlink()
    shutil.rmtree(invocations, ignore_errors=True)

    # 4. The expanded source (expansion only).
    print(f"  {registration}: expanded source", flush=True)
    run(["cargo", "+stable", "check", "--offline", "-p", port.package, "--manifest-path", collector / "Cargo.toml"],
        cwd=collector, environment=wrapped(("-Zunpretty=expanded",)), log=logs / f"{registration}-expand.log")
    [invocation] = rustc_profile.invocations(invocations, crate=crate)[-1:] or [None]
    text = (invocation / "stdout").read_text(encoding="utf-8") if invocation else ""
    if not text:
        raise GateError("-Zunpretty=expanded produced no output")
    expanded = expanded_constructs(text, crate)
    del text
    shutil.rmtree(profile_root, ignore_errors=True)

    measured = {
        "llvm_lines": parse_llvm_lines(lines.stdout),
        "queries": queries,
        "symbols": parse_nm(nm.stdout),
        "expanded": expanded,
    }
    document = aggregate(measured, crate)
    document.update({
        "registration": registration,
        "phases": queries["phases"],
        "cgus": queries["cgus"],
        "expand_proc_macro": queries["expand_proc_macro"],
        "macro_stats": rustc_profile.parse_macro_stats(stderr),
        "time_passes": rustc_profile.parse_time_passes(stderr),
        "self_profile_top": (summary or {}).get("queries", [])[:40],
        "binary": {
            "sections": sections,
            "init_array_entries": sections.get(".init_array", 0) // 8,
            "size": binaries[0].stat().st_size,
        },
        "constructs": {key: {k: v for k, v in construct.items() if k != "names"} | {"names": construct["names"][:4]}
                       for key, construct in expanded["constructs"].items()},
    })
    return document


def main_run(arguments: argparse.Namespace) -> int:
    from perf import bench
    from support.tools import checkout_scratch

    ports = bench.load_ports()
    port = ports[arguments.port]
    environment, _ = bench.base_environment({})
    tools = rustc_profile.measureme_tools(environment)
    if tools["status"] == "unavailable":
        raise GateError(f"measureme tools unavailable: {tools['note']}")
    run_id = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()) + f"-{os.getpid()}"
    out = arguments.out or checkout_scratch() / "perf-attribution" / f"{port.key}-{run_id}"
    out.mkdir(parents=True, exist_ok=True)
    krs = arguments.krs.resolve() if arguments.krs else bench.build_krs(environment)
    modes = ["inventory", "explicit"] if arguments.registration == "both" else [arguments.registration]
    documents = []
    try:
        for mode in modes:
            work = checkout_scratch() / "perf-work" / f"attribution-{run_id}-{mode}"
            try:
                bench.copy_semantics(work / "semantics")
                explicit = prepare_explicit(work, port, environment, out / "logs") if mode == "explicit" else None
                print(f"{port.key} {mode}", flush=True)
                document = measure_mode(work, krs, port, mode, environment, out, tools)
                document["explicit_table"] = explicit
                documents.append(document)
            finally:
                if not arguments.keep:
                    shutil.rmtree(work, ignore_errors=True)
    finally:
        pass
    from perf import receipts

    result = {"schema": SCHEMA, "port": port.key, "package": port.package, "created": receipts.utc_now(),
              "revision": receipts.revision(), "measureme": tools, "modes": documents}
    path = out / "attribution.json"
    path.write_text(json.dumps(result, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    print(render(result, top=arguments.top))
    print(f"\nattribution document: {path}")
    return 0


# --- rendering ------------------------------------------------------------------------------------------


def _table(rows: Mapping[str, Mapping[str, float]], sort: str, columns: Sequence[tuple[str, str, str]],
           top: int, total: float | None = None) -> list[str]:
    ordered = sorted(rows.items(), key=lambda item: -float(item[1].get(sort, 0) or 0))[:top]
    header = f"    {'group':<48}" + "".join(f" {title:>{len(title) if len(title) > 10 else 10}}" for _, title, _ in columns)
    lines = [header]
    for key, row in ordered:
        cells = []
        for metric, title, form in columns:
            value = row.get(metric, 0) or 0
            width = len(title) if len(title) > 10 else 10
            if form == "share":
                cells.append(f" {100 * float(row.get(sort, 0)) / total:>{width - 1}.1f}%" if total
                             else f" {'-':>{width}}")
            else:
                cells.append(f" {value:>{width}{form}}")
        label = key if len(key) <= 48 else key[:45] + "..."
        lines.append(f"    {label:<48}" + "".join(cells))
    return lines


COLUMNS = (
    ("llvm_lines", "IR lines", ",.0f"),
    ("llvm_lines", "IR %", "share"),
    ("llvm_copies", "copies", ",.0f"),
    ("codegen_seconds_est", "codegen s*", ".2f"),
    ("typeck_root_seconds", "typeck s", ".2f"),
    ("mir_borrowck_seconds", "borrowck s", ".2f"),
    ("optimized_mir_seconds", "opt_mir s", ".3f"),
    ("text_bytes", ".text B", ",.0f"),
    ("expanded_lines", "exp lines", ",.0f"),
    ("expanded_anchor_lines", "anchor lines", ",.0f"),
)


def render(document: Mapping[str, Any], *, top: int = 15) -> str:
    lines = [f"attribution for {document['port']} ({document['package']}) at "
             f"{(document.get('revision') or {}).get('commit', '?')[:12]}; measureme "
             f"{(document.get('measureme') or {}).get('version')}"]
    for mode in document["modes"]:
        totals = mode["totals"]
        phases = mode.get("phases") or {}
        lines.append("")
        lines.append(f"== registration {mode['registration']}")
        lines.append(f"  LLVM IR lines {totals['llvm_lines']:,} in {totals['llvm_functions']:,} functions; "
                     f"{100 * (totals['attributed_llvm_lines_share'] or 0):.1f}% attributed to generated-item groups")
        lines.append(f"  codegen time (codegen_module + LLVM per CGU, profiled run) {totals['codegen_seconds']:.2f} s; "
                     f"{100 * (totals['attributed_codegen_share'] or 0):.1f}% attributed (*estimated by IR-line share)")
        cgus = mode.get("cgus") or {}
        if cgus:
            timed = sorted(((sum(v for k, v in cgu.items() if k != "size_estimate"), cgu.get("size_estimate") or 0)
                            for cgu in cgus.values()), reverse=True)
            sizes = sum(size for _, size in timed) or 1
            lines.append(f"  {len(timed)} codegen units; largest by time: " + ", ".join(
                f"{seconds:.2f}s (size estimate {100 * size / sizes:.1f}%)" for seconds, size in timed[:3]))
        lines.append("  query self time (s): " + ", ".join(
            f"{name} {value:.2f}" for name, value in sorted(totals["query_seconds"].items(), key=lambda x: -x[1])))
        if phases.get("categories"):
            lines.append("  phases (profiled run, main thread): " + ", ".join(
                f"{name} {value:.2f}" for name, value in phases["categories"].items()))
        binary = mode.get("binary") or {}
        sections = binary.get("sections") or {}
        lines.append(f"  collector binary {binary.get('size', 0):,} B: .text {sections.get('.text', 0):,}, "
                     f".rodata {sections.get('.rodata', 0):,}, .data.rel.ro {sections.get('.data.rel.ro', 0):,}, "
                     f".init_array {sections.get('.init_array', 0):,} ({binary.get('init_array_entries')} entries)")
        anchors = mode.get("anchors") or {}
        lines.append(f"  provenance anchors: {anchors.get('anchors'):,} in expanded source, "
                     f"{anchors.get('expanded_anchor_lines'):,} of {anchors.get('expanded_lines'):,} expanded lines; "
                     f"fit over {anchors.get('fit_factories')} factories: {anchors.get('ir_lines_per_anchor_line')} IR "
                     f"lines per anchor line, {anchors.get('ir_lines_per_other_line')} per other line (R2 {anchors.get('fit_r2')}); "
                     f"estimated anchor IR lines {anchors.get('estimated_anchor_ir_lines')}")
        total_ir = float(totals["llvm_lines"] or 0)
        for dimension, title in (("macro", "by generated construct kind"),
                                 ("source_macro", "by source macro (innermost proc-macro invocation)"),
                                 ("prefix", "by generated-item prefix"),
                                 ("construct", "top constructs")):
            lines.append(f"  {title}:")
            lines += _table(mode["groups"][dimension], "llvm_lines", COLUMNS, top, total_ir)
        constructs = mode["groups"]["construct"]
        for label, macros in (("per rule", ("rules! clause", "#[k::rule]", "#[k::equation]", "#[k::simplification]")),
                              ("per constructor", ("#[k::constructor]", "#[k::constructors]"))):
            rows = {key: row for key, row in constructs.items() if row.get("_macro") in macros}
            lines.append(f"  top {label} ({len(rows)} constructs):")
            lines += _table(rows, "llvm_lines", COLUMNS, top, total_ir)
        rows = {key: row for key, row in constructs.items() if row.get("expanded_anchor_lines")}
        lines.append(f"  top per anchor volume (constructs by expanded anchor lines):")
        lines += _table(rows, "expanded_anchor_lines", COLUMNS, top, None)
        macros = sorted(mode.get("macro_stats") or [], key=lambda row: -row["lines"])[:top]
        expand = mode.get("expand_proc_macro") or {}
        lines.append("  -Zmacro-stats (and expand_proc_macro time):")
        for row in macros:
            timing = expand.get(row["macro"])
            extra = f"  {timing['seconds']:.2f}s x{timing['invocations']}" if timing else ""
            lines.append(f"    {row['macro']:<40} uses {row['uses']:>7,} lines {row['lines']:>10,} "
                         f"bytes {row['bytes']:>12,}{extra}")
    if len(document["modes"]) == 2:
        inventory, explicit = document["modes"]
        lines.append("")
        lines.append("== inventory vs explicit registration")
        for label, getter in (
            (".init_array entries", lambda m: (m.get("binary") or {}).get("init_array_entries")),
            ("binary bytes", lambda m: (m.get("binary") or {}).get("size")),
            (".text bytes", lambda m: ((m.get("binary") or {}).get("sections") or {}).get(".text")),
            ("IR lines", lambda m: m["totals"]["llvm_lines"]),
            ("registration IR lines", lambda m: sum(row.get("llvm_lines", 0) for key, row in
                                                    m["groups"]["macro"].items() if key == "registration")),
            ("registration expanded lines", lambda m: sum(row.get("expanded_lines", 0) for key, row in
                                                          m["groups"]["macro"].items() if key == "registration")),
            ("registration typeck s", lambda m: round(sum(row.get("typeck_root_seconds", 0) for key, row in
                                                          m["groups"]["macro"].items() if key == "registration"), 3)),
            ("codegen s (profiled)", lambda m: m["totals"]["codegen_seconds"]),
        ):
            a, b = getter(inventory), getter(explicit)
            lines.append(f"  {label:<30} inventory {a!s:>14}  explicit {b!s:>14}")
        registrations = (explicit.get("explicit_table") or {}).get("registrations")
        if registrations:
            lines.append(f"  registrations: {registrations}")
    return "\n".join(lines)


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    running = commands.add_parser("run", help="build, profile, and attribute one port")
    running.add_argument("--port", required=True)
    running.add_argument("--registration", choices=["inventory", "explicit", "both"], default="inventory")
    running.add_argument("--krs", type=Path, help="use this krs executable instead of building one")
    running.add_argument("--out", type=Path, help="output directory (default: under the checkout scratch)")
    running.add_argument("--keep", action="store_true", help="keep the scratch workspace and targets")
    running.add_argument("--top", type=int, default=15)
    reporting = commands.add_parser("report", help="render an attribution document")
    reporting.add_argument("path", type=Path, help="attribution.json or its directory")
    reporting.add_argument("--top", type=int, default=15)
    arguments = parser.parse_args(argv)
    if arguments.command == "run":
        return main_run(arguments)
    path = arguments.path / "attribution.json" if arguments.path.is_dir() else arguments.path
    print(render(json.loads(path.read_text(encoding="utf-8")), top=arguments.top))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except GateError as error:
        print(f"FAIL attribution: {error}", file=sys.stderr)
        raise SystemExit(1)
