#!/usr/bin/env python3
"""Bounded, production-independent oracle for the M2 foo => bar theory."""

from __future__ import annotations

import argparse
import copy
import difflib
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
POSITIVE = HERE / "fixtures" / "foo-bar.k"
NEGATIVE = HERE / "fixtures" / "induced-rule-error.k"
NATIVE_MANIFEST = HERE / "native-probe" / "Cargo.toml"
RUST_WORKSPACE = HERE / "rust-workspace"
RUST_MANIFEST = RUST_WORKSPACE / "Cargo.toml"
RUST_SEMANTICS = RUST_WORKSPACE / "packages" / "m2-semantics" / "src" / "lib.rs"
UI_MANIFEST = HERE / "ui" / "Cargo.toml"
LSP_PROBE = HERE / "tools" / "lsp_probe.py"
PINS = HERE / "pins.json"
NATIVE_CHECKOUT = ROOT.parent / "inspirations" / "midnightntwrk" / "k-rust"
MODULE = "KRS-M2-REFERENCE"
NEGATIVE_MODULE = "KRS-M2-INDUCED-RULE-ERROR"
K_VERSION = "v7.1.337"
K_COMMIT = "4a46d1231473b599c699160132fd6e76a5c46406"
K_RUST_VERSION = "0.3.0"
K_RUST_COMMIT = "58f33885b736148dae189623d1aac989ce9be475"
LLVM_BACKEND_VERSION = "0.1.140"
HASKELL_BACKEND_VERSION = "0.1.155"

EXPECTED_SOURCE_LINES = [
    "module KRS-M2-REFERENCE",
    'syntax Bool ::= r"true" [token]',
    "syntax KItem",
    "syntax KResult",
    'syntax M2Obj ::= "foo" [symbol(foo)]',
    '| "bar" [symbol(bar)]',
    "syntax KItem ::= KResult",
    "syntax KResult ::= M2Obj",
    "configuration <k> foo </k>",
    "rule foo => bar",
    "endmodule",
]

METADATA_ATTRIBUTES = {
    "org.kframework.attributes.Source",
    "org.kframework.attributes.Location",
    "org.kframework.definition.Production",
    "contentStartLine",
    "contentStartColumn",
    "digest",
    "productionID",
    "UNIQUE_ID",
}


class Results:
    def __init__(self) -> None:
        self.failed = False

    def add(self, name: str, status: str, detail: str, *, required: bool = False) -> None:
        print(f"{status:11} {name}: {detail}")
        if required and status not in {"PASS", "MATCH"}:
            self.failed = True


def run(
    command: list[str],
    *,
    timeout: int = 180,
    env: dict[str, str] | None = None,
    cwd: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        env=env,
        cwd=cwd,
        check=False,
    )


def compact_output(process: subprocess.CompletedProcess[str], limit: int = 900) -> str:
    text = "\n".join(part.strip() for part in (process.stdout, process.stderr) if part.strip())
    text = re.sub(r"/[^\s:)]+/", "<PATH>/", text)
    return text[:limit] + ("…" if len(text) > limit else "")


def source_lines(path: Path) -> list[str]:
    result = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("//", 1)[0].strip()
        if line:
            result.append(re.sub(r"\s+", " ", line))
    return result


def verify_fixture(results: Results) -> None:
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    expected_hashes = pins.get("fixture_sha256", {})
    actual_hashes = {
        POSITIVE.name: hashlib.sha256(POSITIVE.read_bytes()).hexdigest(),
        NEGATIVE.name: hashlib.sha256(NEGATIVE.read_bytes()).hexdigest(),
    }
    results.add(
        "fixture_pins",
        "PASS" if actual_hashes == expected_hashes else "FAIL",
        "both handwritten fixture hashes match pins.json"
        if actual_hashes == expected_hashes
        else f"expected={expected_hashes}, actual={actual_hashes}",
        required=True,
    )
    actual = source_lines(POSITIVE)
    if actual == EXPECTED_SOURCE_LINES:
        results.add(
            "canonical_source",
            "PASS",
            "exact module/sorts/productions/subsorts/<k> initializer/foo=>bar sentence set",
            required=True,
        )
    else:
        difference = "\n".join(
            difflib.unified_diff(EXPECTED_SOURCE_LINES, actual, fromfile="expected", tofile="actual")
        )
        results.add("canonical_source", "FAIL", difference[:1200], required=True)

    occurrences = []
    for line_number, line in enumerate(NEGATIVE.read_text(encoding="utf-8").splitlines(), 1):
        if line.strip().startswith("rule ") and "+" in line:
            occurrences.append((line_number, line.index("+") + 1))
    if len(occurrences) == 1:
        results.add(
            "induced_token",
            "PASS",
            f"unexpected '+' is uniquely located at {NEGATIVE.name}:{occurrences[0][0]}:{occurrences[0][1]}",
            required=True,
        )
    else:
        results.add("induced_token", "FAIL", f"expected one rule-local '+', found {occurrences}", required=True)


def probe_command(results: Results, name: str) -> tuple[str | None, str | None]:
    executable = shutil.which(name)
    if executable is None:
        results.add(f"tool_{name}", "UNAVAILABLE", "not found on PATH")
        return None, None
    process = run([executable, "--version"], timeout=30)
    output = "\n".join((process.stdout, process.stderr)).strip()
    if process.returncode != 0:
        results.add(f"tool_{name}", "BLOCKED", compact_output(process))
        return executable, None
    first = output.splitlines()[0] if output else "version output was empty"
    status = "PASS" if K_VERSION in output else "MISMATCH"
    results.add(f"tool_{name}", status, first)
    return executable, output


def probe_tools(results: Results) -> dict[str, str | None]:
    tools: dict[str, str | None] = {}
    versions: dict[str, str | None] = {}
    for name in ("kompile", "krun", "kparse", "kast", "kprove"):
        tools[name], versions[name] = probe_command(results, name)
    try:
        pyk_version = importlib.metadata.version("kframework")
    except importlib.metadata.PackageNotFoundError:
        pyk_version = None
    if pyk_version is None:
        results.add("pyk_pin", "UNAVAILABLE", "Python distribution kframework is not installed")
    else:
        status = "PASS" if pyk_version == K_VERSION.removeprefix("v") else "MISMATCH"
        results.add(
            "pyk_pin",
            status,
            f"installed={pyk_version}, required={K_VERSION.removeprefix('v')}; mismatched pyk is not used",
        )

    cargo = shutil.which("cargo")
    tools["cargo"] = cargo
    if cargo is None:
        results.add("tool_cargo", "UNAVAILABLE", "not found on PATH")
    else:
        process = run([cargo, "--version"], timeout=30)
        results.add("tool_cargo", "PASS" if process.returncode == 0 else "BLOCKED", compact_output(process))

    for name, command, expected in (
        ("llvm_backend", "llvm-backend-version", LLVM_BACKEND_VERSION),
        ("haskell_executor", "kore-exec", HASKELL_BACKEND_VERSION),
        ("haskell_rpc", "kore-rpc", HASKELL_BACKEND_VERSION),
        ("booster_rpc", "kore-rpc-booster", HASKELL_BACKEND_VERSION),
    ):
        executable = shutil.which(command)
        tools[name] = executable
        if executable is None:
            results.add(name, "UNAVAILABLE", f"{command} not found on PATH")
            continue
        arguments = [executable] if command == "llvm-backend-version" else [executable, "--version"]
        process = run(arguments, timeout=30)
        version = "\n".join((process.stdout, process.stderr)).strip().splitlines()
        detected = version[0] if version else "<empty>"
        status = "PASS" if process.returncode == 0 and detected == expected else "MISMATCH"
        results.add(name, status, f"detected={detected}, pinned={expected}")
    optional_dev = shutil.which("kore-rpc-dev")
    tools["haskell_rpc_dev"] = optional_dev
    results.add(
        "haskell_rpc_dev",
        "PASS" if optional_dev else "UNAVAILABLE",
        "available" if optional_dev else "optional kore-rpc-dev executable not found on PATH",
    )

    matching_reference = all(versions.get(name) and K_VERSION in versions[name] for name in ("kompile", "krun"))
    tools["matching_reference"] = "yes" if matching_reference else None
    return tools


def probe_native_pin(results: Results) -> bool:
    manifest = NATIVE_CHECKOUT / "crates" / "k-rust" / "Cargo.toml"
    if not manifest.is_file():
        results.add("native_pin", "UNAVAILABLE", "pinned k-rust checkout is absent")
        return False
    manifest_text = manifest.read_text(encoding="utf-8")
    git = shutil.which("git")
    if git is None:
        results.add("native_pin", "BLOCKED", "git is unavailable, so checkout commit cannot be verified")
        return False
    process = run([git, "-C", str(NATIVE_CHECKOUT), "rev-parse", "HEAD"], timeout=30)
    commit = process.stdout.strip()
    version_ok = re.search(r'^version\s*=\s*"' + re.escape(K_RUST_VERSION) + r'"', manifest_text, re.MULTILINE)
    if process.returncode == 0 and commit == K_RUST_COMMIT and version_ok:
        results.add(
            "native_pin",
            "PASS",
            f"k-rust {K_RUST_VERSION} @ {K_RUST_COMMIT[:12]}, bundled K {K_VERSION} @ {K_COMMIT[:12]}",
        )
        return True
    results.add(
        "native_pin",
        "MISMATCH",
        f"version_ok={bool(version_ok)}, checkout={commit or '<unknown>'}, required={K_RUST_COMMIT}",
    )
    return False


def compile_reference(kompile: str, source: Path, module: str, output: Path) -> subprocess.CompletedProcess[str]:
    return run(
        [
            kompile,
            str(source),
            "--main-module",
            module,
            "--syntax-module",
            module,
            "--backend",
            "llvm",
            "--emit-json",
            "--output-definition",
            str(output),
        ],
        timeout=180,
    )


def find_project(envelope: dict[str, Any], module: str) -> dict[str, Any]:
    if envelope.get("format") != "KAST" or envelope.get("version") != 4:
        raise ValueError("expected fail-closed KAST JSON v4 envelope")
    term = envelope.get("term")
    if not isinstance(term, dict) or term.get("node") != "KDefinition":
        raise ValueError("expected KDefinition root")
    modules = [item for item in term.get("modules", []) if item.get("name") == module]
    if len(modules) != 1:
        raise ValueError(f"expected exactly one project module {module!r}, found {len(modules)}")
    return copy.deepcopy(modules[0])


def alpha_normalize_sentence(sentence: Any) -> Any:
    names: dict[str, str] = {}

    def visit(value: Any) -> Any:
        if isinstance(value, dict):
            result = {key: visit(child) for key, child in value.items()}
            if result.get("node") == "KVariable" and isinstance(result.get("name"), str):
                name = result["name"]
                if re.fullmatch(r"(?:Var_)?(?:Gen|DotVar)\d+|_+", name):
                    result["name"] = names.setdefault(name, f"@generated{len(names)}")
            return result
        if isinstance(value, list):
            return [visit(child) for child in value]
        return value

    return visit(sentence)


def normalize_project(path: Path, module: str) -> dict[str, Any]:
    project = find_project(json.loads(path.read_text(encoding="utf-8")), module)

    def visit(value: Any) -> Any:
        if isinstance(value, dict):
            result = {}
            for key, child in value.items():
                if value.get("node") == "KAtt" and key == "att":
                    if not isinstance(child, dict):
                        raise ValueError("KAtt.att must be an object")
                    child = {name: item for name, item in child.items() if name not in METADATA_ATTRIBUTES}
                result[key] = visit(child)
            return result
        if isinstance(value, list):
            return [visit(child) for child in value]
        return value

    project = visit(project)
    project["name"] = "<PROJECT>"
    for key in ("imports", "localSentences"):
        if not isinstance(project.get(key), list):
            raise ValueError(f"project {key} must be a list")
    project["localSentences"] = [alpha_normalize_sentence(item) for item in project["localSentences"]]
    canonical = lambda item: json.dumps(item, sort_keys=True, separators=(",", ":"))
    project["imports"].sort(key=canonical)
    project["localSentences"].sort(key=canonical)
    return project


def labels(value: Any) -> list[str]:
    found = []
    if isinstance(value, dict):
        if value.get("node") == "KLabel" and isinstance(value.get("name"), str):
            found.append(value["name"])
        for child in value.values():
            found.extend(labels(child))
    elif isinstance(value, list):
        for child in value:
            found.extend(labels(child))
    return found


def verify_parsed_structure(parsed: Path) -> None:
    project = find_project(json.loads(parsed.read_text(encoding="utf-8")), MODULE)
    sentences = project.get("localSentences", [])
    node_counts: dict[str, int] = {}
    for sentence in sentences:
        node_counts[sentence.get("node", "<missing>")] = node_counts.get(sentence.get("node", "<missing>"), 0) + 1
    if node_counts != {"KProduction": 7, "KRule": 2, "KSyntaxSort": 2}:
        raise ValueError(f"unexpected project sentence counts: {node_counts}")
    subsorts = {
        (
            sentence.get("productionItems", [{}])[0].get("sort", {}).get("name"),
            sentence.get("sort", {}).get("name"),
        )
        for sentence in sentences
        if sentence.get("node") == "KProduction"
        and "klabel" not in sentence
        and len(sentence.get("productionItems", [])) == 1
        and sentence["productionItems"][0].get("node") == "KNonTerminal"
    }
    if not {("M2Obj", "KResult"), ("KResult", "KItem")} <= subsorts:
        raise ValueError(f"missing M2Obj < KResult < KItem chain: {sorted(subsorts)}")
    all_labels = labels(project)
    for expected in ("foo", "bar", "<k>", "initKCell"):
        if expected not in all_labels:
            raise ValueError(f"parsed definition lacks label {expected!r}")
    transitions = [
        sentence
        for sentence in sentences
        if sentence.get("node") == "KRule"
        and sentence.get("body", {}).get("node") == "KRewrite"
        and labels(sentence.get("body", {}).get("lhs")) == ["foo"]
        and labels(sentence.get("body", {}).get("rhs")) == ["bar"]
    ]
    if len(transitions) != 1:
        raise ValueError(f"expected one foo=>bar transition, found {len(transitions)}")
    k_cell_productions = [
        sentence
        for sentence in sentences
        if sentence.get("node") == "KProduction"
        and sentence.get("klabel", {}).get("name") == "<k>"
    ]
    if len(k_cell_productions) != 1:
        raise ValueError(f"expected one <k> production, found {len(k_cell_productions)}")
    cell_items = k_cell_productions[0].get("productionItems", [])
    content_sorts = [
        item.get("sort", {}).get("name")
        for item in cell_items
        if item.get("node") == "KNonTerminal"
    ]
    if content_sorts != ["K"]:
        raise ValueError(f"<k> cell content must retain sort K, found {content_sorts}")


def reference_oracles(results: Results, tools: dict[str, str | None], workspace: Path) -> Path | None:
    kompile = tools.get("kompile")
    krun = tools.get("krun")
    if not kompile or not krun or not tools.get("matching_reference"):
        results.add("reference_frontend", "UNAVAILABLE", f"requires matching {K_VERSION} kompile and krun")
        results.add("reference_execution", "UNAVAILABLE", "reference frontend prerequisite is unavailable")
        results.add("reference_location", "UNAVAILABLE", "reference frontend prerequisite is unavailable")
        return None

    source = workspace / "source" / POSITIVE.name
    source.parent.mkdir(parents=True)
    shutil.copyfile(POSITIVE, source)
    definition = workspace / "reference-definition"
    process = compile_reference(kompile, source, MODULE, definition)
    required = True
    if process.returncode != 0:
        results.add("reference_frontend", "FAIL", compact_output(process), required=required)
        return None
    expected_artifacts = ("parsed.json", "compiled.json", "definition.kore", "syntaxDefinition.kore")
    missing = [name for name in expected_artifacts if not (definition / name).is_file()]
    try:
        if missing:
            raise ValueError(f"missing artifacts: {missing}")
        verify_parsed_structure(definition / "parsed.json")
        normalize_project(definition / "parsed.json", MODULE)
    except (ValueError, json.JSONDecodeError) as error:
        results.add("reference_frontend", "FAIL", str(error), required=required)
        return None
    results.add(
        "reference_frontend",
        "PASS",
        "KAST JSON v4 parsed/compiled outputs and both KORE artifacts; expected project sentences found",
        required=required,
    )

    initial = run([krun, "--definition", str(definition), "--depth", "0", "--output", "kore"], timeout=60)
    final = run([krun, "--definition", str(definition), "--output", "kore"], timeout=60)
    execution_ok = (
        initial.returncode == 0
        and final.returncode == 0
        and "Lblfoo" in initial.stdout
        and "Lblbar" not in initial.stdout
        and "kseq" in initial.stdout
        and "inj{SortM2Obj{}, SortKItem{}}" in initial.stdout
        and "Lblbar" in final.stdout
        and "Lblfoo" not in final.stdout
    )
    results.add(
        "reference_execution",
        "PASS" if execution_ok else "FAIL",
        "LLVM depth-0 is K sequence inj(M2Obj foo -> KItem); normal form contains bar"
        if execution_ok
        else compact_output(final),
        required=True,
    )

    bad_source = workspace / "negative" / NEGATIVE.name
    bad_source.parent.mkdir(parents=True)
    shutil.copyfile(NEGATIVE, bad_source)
    bad_output = workspace / "negative-definition"
    bad = compile_reference(kompile, bad_source, NEGATIVE_MODULE, bad_output)
    token_line = token_column = None
    for line_number, line in enumerate(NEGATIVE.read_text(encoding="utf-8").splitlines(), 1):
        if line.strip().startswith("rule ") and "+" in line:
            token_line, token_column = line_number, line.index("+") + 1
    location = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", bad.stderr)
    location_ok = (
        bad.returncode != 0
        and location is not None
        and (int(location.group(1)), int(location.group(2))) == (token_line, token_column)
        and NEGATIVE.name in bad.stderr
        and "unexpected character sequence '+'" in bad.stderr
    )
    results.add(
        "reference_location",
        "PASS" if location_ok else "FAIL",
        f"diagnostic selects authored '+' at {NEGATIVE.name}:{token_line}:{token_column}"
        if location_ok
        else compact_output(bad),
        required=True,
    )
    return definition


def run_native(
    results: Results,
    tools: dict[str, str | None],
    pinned: bool,
    workspace: Path,
    reference: Path | None,
) -> tuple[Path | None, Path | None]:
    cargo = tools.get("cargo")
    if not pinned or cargo is None:
        results.add("native_frontend", "UNAVAILABLE", "verified k-rust pin and cargo are required")
        results.add("native_source_comparison", "UNAVAILABLE", "native frontend prerequisite is unavailable")
        results.add("native_kore_comparison", "UNAVAILABLE", "native frontend prerequisite is unavailable")
        return None, None

    target = workspace / "native-target"
    output = workspace / "native-output"
    environment = os.environ.copy()
    environment["CARGO_INCREMENTAL"] = "0"
    process = run(
        [
            cargo,
            "run",
            "--quiet",
            "--locked",
            "--manifest-path",
            str(NATIVE_MANIFEST),
            "--target-dir",
            str(target),
            "--",
            "compile",
            str(POSITIVE),
            MODULE,
            str(output),
        ],
        timeout=240,
        env=environment,
    )
    if process.returncode != 0:
        results.add("native_frontend", "BLOCKED", compact_output(process))
        results.add("native_source_comparison", "UNAVAILABLE", "native compilation did not produce source JSON")
        results.add("native_kore_comparison", "UNAVAILABLE", "native compilation did not produce KORE")
        return None, None
    artifacts = ("source-definition.json", "definition.kore", "syntaxDefinition.kore")
    missing = [name for name in artifacts if not (output / name).is_file()]
    if missing:
        results.add("native_frontend", "FAIL", f"missing artifacts {missing}", required=True)
        return None, None
    definition_kore = (output / "definition.kore").read_text(encoding="utf-8")
    expected = all(symbol in definition_kore for symbol in ("Lblfoo", "Lblbar", "SortM2Obj"))
    results.add(
        "native_frontend",
        "PASS" if expected else "FAIL",
        "portable k-rust parsed source, compiled LLVM KORE, reparsed both KORE outputs"
        if expected
        else "native definition.kore lacks required symbols",
        required=True,
    )

    binary = target / "debug" / "krs-m2-native-reference-probe"
    source_json = output / "source-definition.json"
    if reference is not None:
        try:
            java_source = normalize_project(reference / "parsed.json", MODULE)
            rust_source = normalize_project(source_json, MODULE)
            java_sentences = java_source["localSentences"]
            rust_sentences = rust_source["localSentences"]
            sentence_match = java_sentences == rust_sentences
            full_match = java_source == rust_source
            results.add(
                "native_source_sentences",
                "MATCH" if sentence_match else "MISMATCH",
                "normalized project local-sentence multisets agree"
                if sentence_match
                else "normalized project local sentences differ",
            )
            if full_match:
                detail = "normalized project module including imports agrees"
                status = "MATCH"
            else:
                java_imports = [item.get("name") for item in java_source["imports"]]
                rust_imports = [item.get("name") for item in rust_source["imports"]]
                detail = f"imports differ: reference={java_imports}, portable-native={rust_imports}"
                status = "MISMATCH"
            results.add("native_source_comparison", status, detail)
        except (ValueError, json.JSONDecodeError) as error:
            results.add("native_source_comparison", "BLOCKED", str(error))

        self_compare = run(
            [str(binary), "compare-kore", str(reference / "definition.kore"), str(reference / "definition.kore"), MODULE, MODULE],
            timeout=60,
        )
        if self_compare.returncode != 0:
            results.add("kore_normalizer_selfcheck", "FAIL", compact_output(self_compare), required=True)
        else:
            results.add("kore_normalizer_selfcheck", "PASS", compact_output(self_compare), required=True)
        comparison = run(
            [str(binary), "compare-kore", str(reference / "definition.kore"), str(output / "definition.kore"), MODULE, MODULE],
            timeout=60,
        )
        results.add(
            "native_kore_comparison",
            "MATCH" if comparison.returncode == 0 else "MISMATCH",
            compact_output(comparison),
        )
    else:
        results.add("native_source_comparison", "UNAVAILABLE", "matching reference artifact is unavailable")
        results.add("native_kore_comparison", "UNAVAILABLE", "matching reference artifact is unavailable")
    return source_json, binary


def candidate_oracles(
    results: Results,
    args: argparse.Namespace,
    tools: dict[str, str | None],
    workspace: Path,
    reference: Path | None,
    kore_binary: Path | None,
) -> None:
    if args.candidate_k is None:
        results.add(
            "candidate_source_definition",
            "UNAVAILABLE",
            "no legacy --candidate-k override; the integrated Rust candidate is exercised separately",
        )
    else:
        if reference is None or not tools.get("kompile"):
            results.add("candidate_source_definition", "BLOCKED", "matching reference frontend is unavailable", required=True)
        else:
            candidate_output = workspace / "candidate-definition"
            process = compile_reference(tools["kompile"], args.candidate_k.resolve(), args.candidate_module, candidate_output)
            if process.returncode != 0:
                results.add("candidate_source_definition", "FAIL", compact_output(process), required=True)
            else:
                try:
                    expected = normalize_project(reference / "parsed.json", MODULE)
                    actual = normalize_project(candidate_output / "parsed.json", args.candidate_module)
                    matches = expected == actual
                    detail = "normalized KAST JSON v4 project modules agree"
                    if not matches:
                        detail = "normalized KAST JSON v4 project modules differ (imports and semantic attributes retained)"
                    results.add("candidate_source_definition", "MATCH" if matches else "MISMATCH", detail, required=True)
                except (ValueError, json.JSONDecodeError) as error:
                    results.add("candidate_source_definition", "FAIL", str(error), required=True)

    kore_arguments = (args.candidate_definition_kore, args.candidate_syntax_kore)
    if kore_arguments == (None, None):
        results.add(
            "candidate_kore",
            "UNAVAILABLE",
            "no legacy candidate KORE override; the structured Rust candidate is exercised separately",
        )
    elif None in kore_arguments:
        results.add("candidate_kore", "FAIL", "both candidate KORE paths are required", required=True)
    elif reference is None or kore_binary is None:
        results.add("candidate_kore", "BLOCKED", "reference/native KORE parser prerequisite is unavailable", required=True)
    else:
        comparisons = []
        for reference_name, candidate in (
            ("definition.kore", args.candidate_definition_kore),
            ("syntaxDefinition.kore", args.candidate_syntax_kore),
        ):
            comparisons.append(
                run(
                    [
                        str(kore_binary),
                        "compare-kore",
                        str(reference / reference_name),
                        str(candidate.resolve()),
                        MODULE,
                        args.candidate_module,
                    ],
                    timeout=60,
                )
            )
        matches = all(item.returncode == 0 for item in comparisons)
        detail = "definition and syntax KORE sentence multisets agree" if matches else compact_output(next(item for item in comparisons if item.returncode))
        results.add("candidate_kore", "MATCH" if matches else "MISMATCH", detail, required=True)


def rust_pipeline_ready() -> tuple[bool, str]:
    facade = (ROOT / "crates" / "krs" / "src" / "lib.rs").read_text(encoding="utf-8")
    compiler = (ROOT / "crates" / "krs-compiler" / "src" / "lib.rs").read_text(encoding="utf-8")
    missing = []
    for spelling in ("configuration", "init", " k,"):
        if spelling not in facade:
            missing.append(f"facade export {spelling.strip()!r}")
    if "lower_descriptor_bundle" not in compiler:
        missing.append("compiler lower_descriptor_bundle")
    return not missing, ", ".join(missing)


def cargo_fixture_gates(results: Results, cargo: str, workspace: Path) -> tuple[Path, str] | None:
    ready, missing = rust_pipeline_ready()
    if not ready:
        detail = f"staged prerequisite unavailable: {missing}"
        for name in (
            "rust_cargo_gates",
            "rust_determinism",
            "rust_protocol_structure",
            "rust_negative_collection",
            "rust_lsp",
            "rust_reference_candidate",
            "rust_structured_native",
            "rust_induced_diagnostic",
        ):
            results.add(name, "UNAVAILABLE", detail)
        return None

    if not (RUST_WORKSPACE / "Cargo.lock").is_file() or not (HERE / "ui" / "Cargo.lock").is_file():
        results.add(
            "rust_cargo_gates",
            "BLOCKED",
            "root-owned Cargo.lock generation is required for rust-workspace and ui",
            required=True,
        )
        return None

    common_env = os.environ.copy()
    common_env["CARGO_INCREMENTAL"] = "0"
    commands = [
        [
            cargo,
            "fmt",
            "--manifest-path",
            str(RUST_MANIFEST),
            "-p",
            "m2-semantics",
            "-p",
            "m2-oracle-runner",
            "--",
            "--check",
        ],
        [cargo, "check", "--manifest-path", str(RUST_MANIFEST), "--workspace", "--all-targets", "--locked"],
        [cargo, "test", "--manifest-path", str(RUST_MANIFEST), "--workspace", "--locked"],
        [
            cargo,
            "clippy",
            "--manifest-path",
            str(RUST_MANIFEST),
            "--workspace",
            "--all-targets",
            "--locked",
            "--",
            "-D",
            "warnings",
        ],
        [cargo, "fmt", "--manifest-path", str(UI_MANIFEST), "--", "--check"],
    ]
    for index, command in enumerate(commands):
        environment = common_env.copy()
        environment["CARGO_TARGET_DIR"] = str(workspace / f"cargo-gate-{index}")
        process = run(command, timeout=360, env=environment)
        if process.returncode:
            results.add("rust_cargo_gates", "FAIL", compact_output(process), required=True)
            return None
    results.add(
        "rust_cargo_gates",
        "PASS",
        "renamed-facade fixture passes fmt/check/test and warnings-denied Clippy",
        required=True,
    )

    outputs = []
    for label in ("a", "b"):
        target = workspace / f"clean-target-{label}"
        output = workspace / f"source-artifacts-{label}"
        environment = common_env.copy()
        environment["CARGO_TARGET_DIR"] = str(target)
        process = run(
            [
                cargo,
                "run",
                "--quiet",
                "--locked",
                "--manifest-path",
                str(RUST_MANIFEST),
                "-p",
                "m2-oracle-runner",
                "--",
                "source",
                str(output),
            ],
            timeout=420,
            env=environment,
        )
        if process.returncode:
            results.add("rust_determinism", "FAIL", compact_output(process), required=True)
            return None
        if "runtime_init_calls=0" not in process.stdout:
            results.add("rust_determinism", "FAIL", compact_output(process), required=True)
            return None
        outputs.append(output)

    artifact_names = (
        "bundle.json",
        "semantic-theory.json",
        "definition-ir.json",
        "definition.k",
        "symbols.json",
        "sources.json",
    )
    first, second = outputs
    differences = [name for name in artifact_names if (first / name).read_bytes() != (second / name).read_bytes()]
    if differences:
        results.add("rust_determinism", "FAIL", f"byte differences: {differences}", required=True)
        return None
    digest = hashlib.sha256(b"".join((first / name).read_bytes() for name in artifact_names)).hexdigest()
    results.add(
        "rust_determinism",
        "PASS",
        f"two independent clean builds are byte-identical; artifact_sha256={digest}",
        required=True,
    )
    return first, digest


def first_authored_range(entry: dict[str, Any]) -> dict[str, Any]:
    frames = entry.get("origin", [])
    if not frames or frames[0].get("frame_type") != "ranged" or frames[0].get("kind") != "authored":
        raise ValueError("source-map entry does not begin at an authored range")
    return frames[0]["range"]


def source_slice(source: bytes, source_range: dict[str, Any]) -> str:
    return source[int(source_range["start_byte"]):int(source_range["end_byte"])].decode("utf-8")


def verify_rust_artifacts(results: Results, artifacts: Path) -> None:
    try:
        bundle = json.loads((artifacts / "bundle.json").read_text(encoding="utf-8"))
        semantic = json.loads((artifacts / "semantic-theory.json").read_text(encoding="utf-8"))
        definition = json.loads((artifacts / "definition-ir.json").read_text(encoding="utf-8"))
        symbols = json.loads((artifacts / "symbols.json").read_text(encoding="utf-8"))
        sources = json.loads((artifacts / "sources.json").read_text(encoding="utf-8"))
        emitted = (artifacts / "definition.k").read_bytes()
        authored = RUST_SEMANTICS.read_bytes()

        assert bundle["protocol_version"] == 5
        descriptors = bundle["descriptors"]
        configurations = [item for item in descriptors if item["descriptor_kind"] == "configuration"]
        assert len(configurations) == 1
        configuration = configurations[0]
        assert configuration["id"]["item_kind"] == "configuration"
        assert configuration["id"]["item_name"] == "Machine"
        assert not any(item["id"]["item_name"] == "init" for item in descriptors)
        payload = configuration["descriptor"]
        assert payload["root"] == "machine"
        assert payload["cell"] == {"name": "k", "content_sort": "k_sequence"}
        assert "main_variable" not in payload
        references = payload["initializer"]["references"]
        assert len(references) == 1
        assert references[0]["key"] == {"role": "initializer_term_path", "ordinal": 0}
        assert references[0]["target"]["item_name"] == "Foo"
        assert references[0]["target"]["item_kind"] == "constructor"
        provenance = configuration["provenance"]
        keys = {(node["key"]["role"], node["key"]["ordinal"]): node for node in provenance["origins"]}
        foo_origin = keys[("initializer_term_path", 0)]
        assert source_slice(authored, first_authored_range(foo_origin)) == "Foo"

        assert semantic["schema_version"] == 1 and definition["schema_version"] == 1
        assert len(semantic["modules"]) == 1 and len(definition["modules"]) == 1
        assert definition["main_module"] == "ORG-KRS-M2-RUST"
        definition_module = definition["modules"][0]
        assert definition_module["id"] == "ORG-KRS-M2-RUST"
        definition_sentences = definition_module["sentences"]
        sentence_kinds = [item["sentence_kind"] for item in definition_sentences]
        assert sentence_kinds.count("syntax_sort") == 3
        assert sentence_kinds.count("subsort") == 2
        assert sentence_kinds.count("production") == 2
        assert sentence_kinds.count("configuration") == 1
        assert sentence_kinds.count("rule") == 1
        syntax_names = {
            item["sentence"]["symbol"]["emitted_name"]
            for item in definition_sentences
            if item["sentence_kind"] == "syntax_sort"
        }
        assert syntax_names == {"KItem", "KResult", "M2Obj"}
        productions = {
            item["sentence"]["symbol"]["emitted_name"]: item["sentence"]
            for item in definition_sentences
            if item["sentence_kind"] == "production"
        }
        assert set(productions) == {"foo", "bar"}
        assert productions["foo"]["items"] == [{"item_kind": "terminal", "text": "foo"}]
        assert productions["bar"]["items"] == [{"item_kind": "terminal", "text": "bar"}]
        definition_configuration = next(
            item["sentence"] for item in definition_sentences if item["sentence_kind"] == "configuration"
        )
        assert definition_configuration["cell"]["symbol"]["emitted_name"] == "k"
        assert definition_configuration["cell"]["content_sort"] == {
            "sort_source": "builtin",
            "sort": "k_sequence",
        }
        assert definition_configuration["initializer"]["symbol"]["emitted_name"] == "initKCell"
        assert definition_configuration["initializer"]["variables"] == []
        assert definition_configuration["initializer"]["body"]["term_kind"] == "k_sequence"
        definition_rule = next(
            item["sentence"] for item in definition_sentences if item["sentence_kind"] == "rule"
        )
        assert definition_rule["kind"] == "transition" and definition_rule["variables"] == []
        assert definition_rule["label"]["emitted_name"].startswith("krsRule_")
        assert definition_rule["body"]["term_kind"] == "rewrite"
        assert definition_rule["body"]["from"]["term_kind"] == "application"
        assert definition_rule["body"]["to"]["term_kind"] == "application"
        assert definition_rule["body"]["from"]["symbol"] == productions["foo"]["symbol"]["id"]
        assert definition_rule["body"]["to"]["symbol"] == productions["bar"]["symbol"]["id"]
        assert symbols["schema_version"] == 1 and sources["schema_version"] == 1

        mapped: dict[str, list[str]] = {}
        generated_slices: dict[str, list[str]] = {}
        for entry in sources["entries"]:
            token = source_slice(authored, first_authored_range(entry))
            mapped.setdefault(token, []).append(entry["node_kind"])
            generated = entry.get("generated")
            if generated:
                text = emitted[int(generated["start_byte"]):int(generated["end_byte"])].decode("utf-8")
                generated_slices.setdefault(token, []).append(text)
        for token in ("Foo", "Bar", "Machine", "init"):
            assert token in mapped, f"no source-map entry starts at authored {token}"
            assert token in generated_slices, f"no generated range maps to authored {token}"
        assert any(text == "foo" for text in generated_slices["Foo"])
        assert any(text == "bar" for text in generated_slices["Bar"])

        all_text = b"".join((artifacts / name).read_bytes() for name in (
            "bundle.json", "semantic-theory.json", "definition-ir.json", "definition.k", "symbols.json", "sources.json"
        )).decode("utf-8")
        assert str(ROOT) not in all_text and "/home/" not in all_text
        assert "TypeId" not in all_text and not re.search(r"0x[0-9a-fA-F]+", all_text)
    except (AssertionError, KeyError, ValueError, json.JSONDecodeError, UnicodeDecodeError) as error:
        results.add("rust_protocol_structure", "FAIL", str(error), required=True)
        return
    results.add(
        "rust_protocol_structure",
        "PASS",
        "protocol 5 combined config, exact refs/origins, structural IR, sidecars, and Rust-token ranges",
        required=True,
    )


def verify_rust_negatives(results: Results, cargo: str, workspace: Path) -> None:
    ui_cases = {
        "malformed_configuration": "contains exactly one computation cell",
        "malformed_init": "the body must contain exactly one declarative",
        "missing_init": "__krs_initializer_payload",
        "duplicate_init": "duplicate definitions with name `init`",
    }
    environment = os.environ.copy()
    environment["CARGO_TARGET_DIR"] = str(workspace / "ui-target")
    for case, message in ui_cases.items():
        process = run(
            [cargo, "check", "--locked", "--manifest-path", str(UI_MANIFEST), "--bin", case],
            timeout=180,
            env=environment,
        )
        if process.returncode == 0 or message not in process.stderr or not re.search(
            rf"--> src/{re.escape(case)}\.rs:\d+:\d+", process.stderr
        ):
            results.add("rust_negative_collection", "FAIL", f"{case}: {compact_output(process)}", required=True)
            return

    for case, expected in (
        ("negative-cross-wired-init", "InvalidConfiguration"),
        ("negative-wrong-reference-kind", "ReferenceKindMismatch"),
        ("negative-stale-split-provenance", "StaleAnchor"),
    ):
        process = run(
            [
                cargo,
                "run",
                "--quiet",
                "--locked",
                "--manifest-path",
                str(RUST_MANIFEST),
                "-p",
                "m2-oracle-runner",
                "--",
                case,
            ],
            timeout=180,
            env=environment,
        )
        if process.returncode or expected not in process.stdout:
            results.add("rust_negative_collection", "FAIL", f"{case}: {compact_output(process)}", required=True)
            return
    results.add(
        "rust_negative_collection",
        "PASS",
        "four exact macro failures plus cross-wire, wrong-kind, and stale split-file collection failures",
        required=True,
    )


def verify_rust_lsp(results: Results) -> None:
    rust_analyzer = shutil.which("rust-analyzer")
    if rust_analyzer is None:
        results.add("rust_lsp", "UNAVAILABLE", "rust-analyzer not found on PATH")
        return
    process = run([sys.executable, str(LSP_PROBE)], timeout=180)
    results.add(
        "rust_lsp",
        "PASS" if process.returncode == 0 else "FAIL",
        compact_output(process),
        required=True,
    )


def module_name_from_k(path: Path) -> str:
    match = re.search(r"(?m)^module\s+([A-Za-z0-9-]+)\s*$", path.read_text(encoding="utf-8"))
    if match is None:
        raise ValueError("candidate canonical K has no module declaration")
    return match.group(1)


def candidate_reference_and_diagnostic(
    results: Results,
    tools: dict[str, str | None],
    workspace: Path,
    artifacts: Path,
) -> None:
    kompile, krun = tools.get("kompile"), tools.get("krun")
    if not kompile or not krun or not tools.get("matching_reference"):
        results.add("rust_reference_candidate", "UNAVAILABLE", f"requires matching {K_VERSION} kompile and krun")
        results.add("rust_induced_diagnostic", "UNAVAILABLE", "matching reference frontend unavailable")
        return
    candidate = artifacts / "definition.k"
    try:
        module = module_name_from_k(candidate)
    except ValueError as error:
        results.add("rust_reference_candidate", "FAIL", str(error), required=True)
        return
    output = workspace / "rust-reference-definition"
    process = compile_reference(kompile, candidate, module, output)
    if process.returncode:
        results.add("rust_reference_candidate", "FAIL", compact_output(process), required=True)
        return
    initial = run([krun, "--definition", str(output), "--depth", "0", "--output", "kore"], timeout=60)
    final = run([krun, "--definition", str(output), "--output", "kore"], timeout=60)
    execution_ok = (
        initial.returncode == 0
        and final.returncode == 0
        and "Lblfoo" in initial.stdout
        and "Lblbar" in final.stdout
        and "Lblfoo" not in final.stdout
    )
    results.add(
        "rust_reference_candidate",
        "PASS" if execution_ok else "FAIL",
        "candidate canonical K compiles and executes foo -> bar; bootstrap Bool and generated labels use documented projection"
        if execution_ok else compact_output(final),
        required=True,
    )

    source_map = json.loads((artifacts / "sources.json").read_text(encoding="utf-8"))
    authored = RUST_SEMANTICS.read_bytes()
    emitted = candidate.read_bytes()
    rhs = []
    for entry in source_map["entries"]:
        generated = entry.get("generated")
        if not generated:
            continue
        authored_token = source_slice(authored, first_authored_range(entry))
        generated_token = emitted[int(generated["start_byte"]):int(generated["end_byte"])].decode("utf-8")
        if authored_token == "Bar" and generated_token == "bar":
            rhs.append((entry, generated))
    if len(rhs) != 1:
        results.add("rust_induced_diagnostic", "BLOCKED", f"expected one exact Bar->bar term range, found {len(rhs)}", required=True)
        return
    _, generated = rhs[0]
    start, end = int(generated["start_byte"]), int(generated["end_byte"])
    broken = emitted[:start] + b"+" + emitted[end:]
    broken_source = workspace / "induced-rust-sidecar.k"
    broken_source.write_bytes(broken)
    bad = compile_reference(kompile, broken_source, module, workspace / "induced-rust-definition")
    line = broken[:start].count(b"\n") + 1
    column = start - broken.rfind(b"\n", 0, start)
    location = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", bad.stderr)
    mapped = source_slice(authored, first_authored_range(rhs[0][0]))
    ok = (
        bad.returncode != 0
        and location is not None
        and (int(location.group(1)), int(location.group(2))) == (line, column)
        and mapped == "Bar"
    )
    results.add(
        "rust_induced_diagnostic",
        "PASS" if ok else "FAIL",
        f"frontend {broken_source.name}:{line}:{column} maps through generated range to exact authored Rust token `Bar`"
        if ok else compact_output(bad),
        required=True,
    )


def structured_native_candidate(
    results: Results,
    cargo: str,
    workspace: Path,
    artifacts: Path,
    native_pinned: bool,
    kore_binary: Path | None,
) -> None:
    if not native_pinned:
        results.add("rust_structured_native", "UNAVAILABLE", "verified k-rust pin is required")
        return
    output = workspace / "rust-native-artifacts"
    environment = os.environ.copy()
    environment["CARGO_TARGET_DIR"] = str(workspace / "rust-native-target")
    process = run(
        [
            cargo,
            "run",
            "--quiet",
            "--locked",
            "--manifest-path",
            str(RUST_MANIFEST),
            "-p",
            "m2-oracle-runner",
            "--",
            "native",
            str(output),
        ],
        timeout=420,
        env=environment,
    )
    if process.returncode:
        results.add("rust_structured_native", "FAIL", compact_output(process), required=True)
        return
    native_kore = output / "definition.kore"
    syntax_kore = output / "syntaxDefinition.kore"
    ok = all(path.is_file() and path.stat().st_size > 0 for path in (native_kore, syntax_kore))
    module = module_name_from_k(artifacts / "definition.k")
    if ok and kore_binary is not None:
        self_compare = run(
            [str(kore_binary), "compare-kore", str(native_kore), str(native_kore), module, module],
            timeout=60,
        )
        ok = self_compare.returncode == 0
    detail = "Definition IR provisional route produced reparsable definition/syntax KORE without emitted-K parsing"
    results.add("rust_structured_native", "PASS" if ok else "FAIL", detail, required=True)

    reference_kore = workspace / "rust-reference-definition" / "definition.kore"
    if reference_kore.is_file() and kore_binary is not None:
        comparison = run(
            [
                str(kore_binary),
                "compare-kore",
                str(reference_kore),
                str(native_kore),
                module,
                module,
            ],
            timeout=60,
        )
        results.add(
            "rust_structured_kore_closure",
            "MATCH" if comparison.returncode == 0 else "MISMATCH",
            compact_output(comparison),
        )
    else:
        results.add(
            "rust_structured_kore_closure",
            "UNAVAILABLE",
            "reference candidate or native KORE parser unavailable",
        )

    # Preserve the qualification gaps as evidence, not normalizations.
    source = (artifacts / "definition.k").read_text(encoding="utf-8")
    assert "syntax Bool" not in source
    results.add(
        "rust_native_bootstrap_projection",
        "MISMATCH",
        "handwritten portable-native fixture alone has Bool bootstrap; generated project semantics does not invent it",
    )
    results.add(
        "rust_native_prelude_closure",
        "MISMATCH",
        "reference MAP import and observed 251-vs-130 full-KORE closure remain outside the project-semantic projection",
    )


def rust_authoring_oracles(
    results: Results,
    tools: dict[str, str | None],
    workspace: Path,
    native_pinned: bool,
    kore_binary: Path | None,
) -> None:
    cargo = tools.get("cargo")
    if cargo is None:
        results.add("rust_cargo_gates", "UNAVAILABLE", "cargo not found on PATH")
        return
    built = cargo_fixture_gates(results, cargo, workspace)
    if built is None:
        return
    artifacts, _ = built
    verify_rust_artifacts(results, artifacts)
    verify_rust_negatives(results, cargo, workspace)
    verify_rust_lsp(results)
    candidate_reference_and_diagnostic(results, tools, workspace, artifacts)
    structured_native_candidate(results, cargo, workspace, artifacts, native_pinned, kore_binary)


def verify_no_path_leak(results: Results) -> None:
    leaks = []
    for path in HERE.rglob("*"):
        relative = path.relative_to(HERE)
        if (
            not path.is_file()
            or "target" in relative.parts
            or path.suffix in {".pyc"}
            or path.name == "Cargo.lock"
        ):
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        if str(ROOT) in text:
            leaks.append(relative.as_posix())
    results.add(
        "canonical_path_leaks",
        "PASS" if not leaks else "FAIL",
        "no absolute checkout paths in oracle inputs/code/docs" if not leaks else f"leaks={leaks}",
        required=True,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate-k", type=Path, help="optional generated .k to compare through the pinned reference frontend")
    parser.add_argument("--candidate-module", default=MODULE, help="main module in candidate artifacts")
    parser.add_argument("--candidate-definition-kore", type=Path)
    parser.add_argument("--candidate-syntax-kore", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    results = Results()
    print(f"KRS M2 reference oracle: sha256(foo-bar.k)={hashlib.sha256(POSITIVE.read_bytes()).hexdigest()}")
    verify_fixture(results)
    tools = probe_tools(results)
    native_pin = probe_native_pin(results)
    with tempfile.TemporaryDirectory(prefix="krs-m2-oracle-") as temporary:
        workspace = Path(temporary)
        reference = reference_oracles(results, tools, workspace)
        _, kore_binary = run_native(results, tools, native_pin, workspace, reference)
        candidate_oracles(results, args, tools, workspace, reference, kore_binary)
        rust_authoring_oracles(results, tools, workspace, native_pin, kore_binary)
    verify_no_path_leak(results)
    print("FAIL" if results.failed else "PASS", "m2_reference_oracle")
    return 1 if results.failed else 0


if __name__ == "__main__":
    sys.exit(main())
