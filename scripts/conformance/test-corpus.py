#!/usr/bin/env python3
"""Generate the Rust test-corpus census and exact reference-fixture markers."""

import argparse
import json
import os
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path


SUBSYSTEMS = [
    ("outer", r"k-rust/src/outer/|tests/outer_|tests/lexer\.rs|tests/string\.rs"),
    ("inner", r"k-rust/src/inner/|tests/inner_"),
    (
        "definition",
        r"k-rust/src/definition/|tests/definition_|tests/partial_order|tests/provenance_manifest|src/provenance\.rs|src/builtin\.rs|tests/hook_capabilities|tests/structured_definition_conformance",
    ),
    (
        "kompile-passes",
        r"k-rust/src/kompile/passes/|k-rust/src/kompile/compile\.rs|tests/kompile_passes",
    ),
    ("injections", r"tests/sort_injections|injection"),
    ("module_to_kore", r"module_to_kore|tests/term_to_kore"),
    ("kore-crate", r"k-rust-kore/|tests/kore_"),
    ("kast", r"k-rust/src/kast/|tests/kast_"),
    (
        "backend-matching",
        r"k-rust-backend/src/(matching|unification|substitution|term|definedness|alias|rule|definition)\.rs",
    ),
    (
        "backend-simplify-builtins",
        r"k-rust-backend/src/(simplify|builtin|smt|externalize|binary)|tests/simplification_budget",
    ),
    (
        "backend-rewrite-search",
        r"k-rust-backend/src/(rewrite|search|session|timeout|cancellation)\.rs",
    ),
    ("backend-proof", r"k-rust-backend/src/(proof|implication|claim)\.rs"),
    (
        "cli-rpc",
        r"k-rust/src/main\.rs|k-rust/src/rpc\.rs|k-rust/src/backend\.rs|k-rust/src/native\.rs|tests/cli\.rs|k-rust-wasm/|k-rust-napi/|tests/z3_acquisition|tests/differential_manifest|tests/reference_differential|tests/reference_fixtures|tests/conformance_ratchet|tests/wasm_ratchet",
    ),
]

# Tests for backend-facing reference fixtures live in CLI integration-test
# binaries, but their evidence belongs to the subsystem exercised by the
# fixture. Attribute an explicitly named fixture home before falling back to
# the source-file classification used by the baseline census.
REFERENCE_FIXTURE_SUBSYSTEMS = [
    ("inner", "inner"),
    ("kompile", "kompile-passes"),
    ("kore-syntax", "kore-crate"),
    ("matching", "backend-matching"),
    ("execution", "backend-rewrite-search"),
    ("search", "backend-rewrite-search"),
    ("simplify", "backend-simplify-builtins"),
    ("hooks", "backend-simplify-builtins"),
    ("implication", "backend-proof"),
    ("proof", "backend-proof"),
    ("rpc", "cli-rpc"),
    ("cli", "cli-rpc"),
    ("outer", "outer"),
]

SNAPSHOT = re.compile(
    r"assert_(debug_|yaml_|json_|display_|ron_|toml_|csv_|compact_debug_)?snapshot!|insta::"
)
ASSERTION = re.compile(
    r"\bassert(_eq|_ne|_matches)?!|\bpanic!|\bunreachable!|\.unwrap_err\(|\bassert_err|should_panic|expect_err|prop_assert|proptest!"
)
REFERENCE_MENTION = re.compile(
    r"fixtures/reference|fixtures/kore|fixtures/kast|K_REFERENCE|regression-new|k-distribution|reference[-_ ](kore|kast|json|output|frontend|backend|toolchain|differential|manifest|krun|kompile|parser|corpus|fixture|checkout|pyk|haskell)|pinned (reference|k |K )|haskell-backend|kore-exec|\bpyk\b|v7\.1\.337",
    re.IGNORECASE,
)
REFERENCE_MARKER = re.compile(r"^\{\s*//\s*reference:\s*\S")


def arguments() -> argparse.Namespace:
    repository = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workspace",
        type=Path,
        default=repository,
        help="workspace root to census (default: repository root)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="TOML output path (default: stdout)",
    )
    return parser.parse_args()


def subsystem(path: str) -> str:
    for name, pattern in SUBSYSTEMS:
        if re.search(pattern, path):
            return name
    return "other"


def test_subsystem(path: str, body: str) -> str:
    for fixture_home, name in REFERENCE_FIXTURE_SUBSYSTEMS:
        if f"fixtures/reference/{fixture_home}/" in body:
            return name
    return subsystem(path)


def extract_tests(source: str) -> list[tuple[str, str, str]]:
    tests = []
    for marker in re.finditer(r"#\[test\]", source):
        function = re.compile(r"fn\s+([A-Za-z_][A-Za-z0-9_]*)").search(
            source, marker.end()
        )
        if not function:
            continue
        attributes = source[marker.end() : function.start()]
        body_start = source.find("{", function.end())
        if body_start < 0:
            continue
        depth = 0
        body_end = body_start
        while body_end < len(source):
            character = source[body_end]
            if character == "{":
                depth += 1
            elif character == "}":
                depth -= 1
                if depth == 0:
                    break
            body_end += 1
        body = source[body_start : body_end + 1]
        tests.append((function.group(1), attributes, body))
    return tests


def reference_marker(name: str, body: str) -> bool:
    return name.startswith("reference_") or bool(REFERENCE_MARKER.match(body))


def collect(workspace: Path) -> list[dict[str, object]]:
    rows = []
    crates = workspace / "crates"
    for root, directories, files in os.walk(crates):
        directories[:] = [directory for directory in directories if directory != "target"]
        for filename in files:
            if not filename.endswith(".rs"):
                continue
            path = Path(root) / filename
            relative = path.relative_to(workspace).as_posix()
            source = path.read_text(errors="replace")
            file_reference = bool(REFERENCE_MENTION.search(source))
            for name, attributes, body in extract_tests(source):
                snapshot = bool(SNAPSHOT.search(body))
                assertion = bool(ASSERTION.search(body))
                if snapshot and not assertion:
                    kind = "snapshot-only"
                elif snapshot:
                    kind = "snapshot+assert"
                elif assertion:
                    kind = "assert"
                else:
                    kind = "no-explicit-assert"
                rows.append(
                    {
                        "file": relative,
                        "name": name,
                        "subsystem": test_subsystem(relative, body),
                        "kind": kind,
                        "reference_marked": reference_marker(name, body),
                        "mentions_reference": bool(REFERENCE_MENTION.search(body)),
                        "file_reference": file_reference,
                        "ignored": "#[ignore" in attributes,
                    }
                )
    return rows


def toml_array(values: list[str]) -> str:
    return "[" + ", ".join(json.dumps(value) for value in values) + "]"


def render(workspace: Path, rows: list[dict[str, object]]) -> str:
    kinds = Counter(str(row["kind"]) for row in rows)
    snapshots = sum(
        1
        for root, _, files in os.walk(workspace / "crates")
        for filename in files
        if filename.endswith(".snap")
    )
    per_subsystem: defaultdict[str, Counter[str]] = defaultdict(Counter)
    marked_names: defaultdict[str, list[str]] = defaultdict(list)
    for row in rows:
        name = str(row["subsystem"])
        counts = per_subsystem[name]
        counts["tests"] += 1
        counts[str(row["kind"])] += 1
        if row["reference_marked"]:
            counts["reference-marked"] += 1
            marked_names[name].append(f'{row["file"]}::{row["name"]}')
        if row["mentions_reference"]:
            counts["mentions-reference"] += 1
        if row["ignored"]:
            counts["ignored"] += 1
        if row["file_reference"]:
            counts["file-reference"] += 1

    lines = [
        "# Test-corpus census of k-rust, generated by scripts/conformance/test-corpus.py.",
        "# Method: grep-based. A test is every `#[test]` attribute followed by `fn`; its body is brace-matched.",
        "# reference_marked is exact: a reference_* name or // reference: as the first body line.",
        "# mentions_reference is the former heuristic upper bound and is reported separately.",
        "",
        "[totals]",
        f"tests = {len(rows)}",
        f"snapshot_files = {snapshots}",
    ]
    for kind in ("snapshot-only", "snapshot+assert", "assert", "no-explicit-assert"):
        key = kind.replace("+", "_plus_").replace("-", "_")
        lines.append(f"{key} = {kinds[kind]}")
    lines.extend(
        [
            f'reference_marked = {sum(bool(row["reference_marked"]) for row in rows)}',
            f'mentions_reference = {sum(bool(row["mentions_reference"]) for row in rows)}',
            f'in_files_mentioning_reference = {sum(bool(row["file_reference"]) for row in rows)}',
            f'ignored = {sum(bool(row["ignored"]) for row in rows)}',
            "",
        ]
    )

    for name, _ in SUBSYSTEMS + [("other", "")]:
        counts = per_subsystem.get(name)
        if not counts:
            continue
        lines.extend(
            [
                "[[subsystem]]",
                f'name = {json.dumps(name)}',
                f'tests = {counts["tests"]}',
                f'snapshot_only = {counts["snapshot-only"]}',
                f'snapshot_plus_assert = {counts["snapshot+assert"]}',
                f'assert = {counts["assert"]}',
                f'no_explicit_assert = {counts["no-explicit-assert"]}',
                f'reference_marked = {counts["reference-marked"]}',
                f'mentions_reference = {counts["mentions-reference"]}',
                f'in_files_mentioning_reference = {counts["file-reference"]}',
                f'ignored = {counts["ignored"]}',
                "has_reference_derived_test = "
                + ("true" if counts["reference-marked"] else "false"),
                "reference_marked_tests = " + toml_array(marked_names[name]),
                "",
            ]
        )

    files = Counter(str(row["file"]) for row in rows)
    file_counts: defaultdict[str, Counter[str]] = defaultdict(Counter)
    for row in rows:
        counts = file_counts[str(row["file"])]
        counts[str(row["kind"])] += 1
        counts["reference-marked"] += bool(row["reference_marked"])
        counts["mentions-reference"] += bool(row["mentions_reference"])
    for path, tests in sorted(files.items(), key=lambda item: (-item[1], item[0])):
        counts = file_counts[path]
        lines.extend(
            [
                "[[file]]",
                f'path = {json.dumps(path)}',
                f'subsystem = {json.dumps(subsystem(path))}',
                f"tests = {tests}",
                f'snapshot_only = {counts["snapshot-only"]}',
                f'reference_marked = {counts["reference-marked"]}',
                f'mentions_reference = {counts["mentions-reference"]}',
                "",
            ]
        )
    return "\n".join(lines)


def main() -> None:
    args = arguments()
    workspace = args.workspace.resolve()
    rows = collect(workspace)
    census = render(workspace, rows)
    if args.output is None:
        sys.stdout.write(census)
        return
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(census)
    print(
        f"{len(rows)} tests; "
        f"{sum(bool(row['reference_marked']) for row in rows)} reference-marked; "
        f"{sum(bool(row['mentions_reference']) for row in rows)} mention reference"
    )


if __name__ == "__main__":
    main()
