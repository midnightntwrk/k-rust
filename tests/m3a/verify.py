#!/usr/bin/env python3
"""Strict independent M3A oracle for the IMP expression slice."""

from __future__ import annotations

import copy
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
FIXTURE = HERE / "fixtures" / "expr.k"
INDUCED = HERE / "fixtures" / "induced-definition-error.k"
ACCEPTED = HERE / "corpus" / "accepted"
SYNTAX_REJECTED = HERE / "corpus" / "rejected" / "syntax"
TYPE_REJECTED = HERE / "corpus" / "rejected" / "semantic-type"
PINS = HERE / "pins.json"
NATIVE_MANIFEST = HERE / "native-probe" / "Cargo.toml"
NATIVE_CHECKOUT = ROOT.parent / "inspirations" / "midnightntwrk" / "k-rust"
UPSTREAM_EXPR = (
    ROOT.parent
    / "inspirations"
    / "runtimeverification"
    / "imp-semantics"
    / "src"
    / "kimp"
    / "kdist"
    / "imp-semantics"
    / "expr.k"
)

MODULE = "KRS-M3A-EXPR"
SYNTAX_MODULE = "KRS-M3A-EXPR-SYNTAX"
RULES_MODULE = "KRS-M3A-EXPR-RULES"
INDUCED_MODULE = "KRS-M3A-INDUCED-DEFINITION-ERROR"
K_VERSION = "v7.1.337"
K_COMMIT = "4a46d1231473b599c699160132fd6e76a5c46406"
K_RUST_VERSION = "0.3.0"
K_RUST_COMMIT = "58f33885b736148dae189623d1aac989ce9be475"

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

EXPECTED_TREES: dict[str, Any] = {
    "arithmetic-precedence.expr": ["+", ["Int", "1"], ["*", ["Int", "2"], ["Int", "3"]]],
    "parentheses-override.expr": ["*", ["+", ["Int", "1"], ["Int", "2"]], ["Int", "3"]],
    "subtraction-left.expr": ["-", ["-", ["Int", "8"], ["Int", "3"]], ["Int", "2"]],
    "division-left.expr": ["/", ["/", ["Int", "8"], ["Int", "4"]], ["Int", "2"]],
    "division-parenthesized.expr": ["/", ["Int", "8"], ["/", ["Int", "4"], ["Int", "2"]]],
    "unary-binding.expr": ["+", ["neg", ["Int", "1"]], ["Int", "2"]],
    "comparison-equality.expr": [
        "==",
        [">=", ["+", ["Int", "1"], ["Int", "2"]], ["Int", "3"]],
        ["Bool", "true"],
    ],
    "boolean-precedence.expr": [
        "||",
        ["&&", ["not", ["Bool", "false"]], ["Bool", "false"]],
        ["Bool", "true"],
    ],
    "short-circuit-precedence.expr": [
        "||",
        ["Bool", "true"],
        [
            "&&",
            ["Bool", "false"],
            ["==", ["/", ["Int", "1"], ["Int", "0"]], ["Int", "0"]],
        ],
    ],
}

EXPECTED_RESULTS = {
    "arithmetic-precedence.expr": "7",
    "parentheses-override.expr": "9",
    "subtraction-left.expr": "3",
    "division-left.expr": "1",
    "division-parenthesized.expr": "4",
    "unary-binding.expr": "1",
    "comparison-equality.expr": "true",
    "boolean-precedence.expr": "true",
    "short-circuit-precedence.expr": "true",
}


class Results:
    def __init__(self) -> None:
        self.failed = False

    def add(self, name: str, status: str, detail: str, *, required: bool = True) -> None:
        print(f"{status:18} {name}: {detail}")
        if required and status not in {"PASS", "MATCH", "EXPECTED-MISMATCH"}:
            self.failed = True


def run(
    command: list[str],
    *,
    timeout: int = 180,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        cwd=cwd,
        env=env,
        check=False,
    )


def compact(process: subprocess.CompletedProcess[str], limit: int = 1000) -> str:
    value = "\n".join(part.strip() for part in (process.stdout, process.stderr) if part.strip())
    value = re.sub(r"/[A-Za-z0-9_.+@%/=-]+", "<PATH>", value)
    return value[:limit] + ("…" if len(value) > limit else "")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def fixture_files() -> list[Path]:
    return [FIXTURE, INDUCED, *sorted(ACCEPTED.glob("*.expr")), *sorted(SYNTAX_REJECTED.glob("*.expr")), *sorted(TYPE_REJECTED.glob("*.expr"))]


def verify_pins(results: Results) -> dict[str, Any]:
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    declared_pins_ok = pins.get("reference_k") == {"version": K_VERSION.removeprefix("v"), "commit": K_COMMIT} and pins.get("native_frontend") == {
        "crate": "k-rust", "version": K_RUST_VERSION, "commit": K_RUST_COMMIT,
    }
    results.add("declared_tool_pins", "PASS" if declared_pins_ok else "FAIL", "pins.json names the exact reference K and k-rust revisions")
    actual = {str(path.relative_to(HERE)): sha256(path) for path in fixture_files()}
    expected = pins.get("source_sha256", {})
    results.add(
        "source_pins",
        "PASS" if actual == expected else "FAIL",
        f"{len(actual)} handwritten fixture/corpus hashes are exact" if actual == expected else f"expected={expected}; actual={actual}",
    )
    upstream = sha256(UPSTREAM_EXPR)
    results.add(
        "upstream_expr_pin",
        "PASS" if upstream == pins.get("upstream_expr_sha256") else "FAIL",
        f"runtimeverification IMP expr.k sha256={upstream}",
    )
    lines = FIXTURE.read_text(encoding="utf-8")
    coverage = all(
        spelling in lines
        for spelling in (
            "UNSIGNED-INT-SYNTAX", "BOOL-SYNTAX", "syntax Value", "syntax KResult",
            '"(" Expr ")"', "[bracket", '"-" Expr', '"!" Expr', 'Expr "*" Expr',
            'Expr "/" Expr', 'Expr "+" Expr', 'Expr "-" Expr', 'Expr ">=" Expr',
            'Expr ">"  Expr', 'Expr "<=" Expr', 'Expr "<"  Expr', 'Expr "==" Expr',
            'Expr "!=" Expr', 'Expr "&&" Expr', 'Expr "||" Expr', "[seqstrict]", "[strict(1)]",
        )
    )
    results.add("fixture_surface", "PASS" if coverage else "FAIL", "all M3A grammar/builtin/attribute families occur literally")
    return pins


def tool(results: Results, name: str) -> str | None:
    executable = shutil.which(name)
    if executable is None:
        results.add(f"tool_{name}", "UNAVAILABLE", "not found on PATH")
        return None
    process = run([executable, "--version"], timeout=30)
    output = "\n".join((process.stdout, process.stderr))
    results.add(
        f"tool_{name}",
        "PASS" if process.returncode == 0 and K_VERSION in output else "MISMATCH",
        output.strip().splitlines()[0] if output.strip() else "empty version output",
    )
    return executable


def verify_capabilities(results: Results) -> dict[str, str | None]:
    tools = {name: tool(results, name) for name in ("kompile", "kast", "kparse", "krun")}
    llvm = shutil.which("llvm-backend-version")
    if llvm:
        process = run([llvm], timeout=30)
        results.add("llvm_backend", "PASS" if process.returncode == 0 else "MISMATCH", compact(process))
    else:
        results.add("llvm_backend", "UNAVAILABLE", "llvm-backend-version not found")
    try:
        pyk = importlib.metadata.version("kframework")
    except importlib.metadata.PackageNotFoundError:
        pyk = None
    results.add(
        "pyk_capability",
        "PASS" if pyk == K_VERSION.removeprefix("v") else "EXPECTED-MISMATCH",
        f"installed={pyk or '<absent>'}; required={K_VERSION.removeprefix('v')}; verifier does not import pyk",
    )
    cargo = shutil.which("cargo")
    tools["cargo"] = cargo
    results.add("tool_cargo", "PASS" if cargo else "UNAVAILABLE", cargo or "not found on PATH")
    return tools


def verify_native_pin(results: Results) -> bool:
    manifest = NATIVE_CHECKOUT / "crates" / "k-rust" / "Cargo.toml"
    git = shutil.which("git")
    if not manifest.is_file() or git is None:
        results.add("native_pin", "UNAVAILABLE", "pinned checkout or git is unavailable")
        return False
    revision = run([git, "-C", str(NATIVE_CHECKOUT), "rev-parse", "HEAD"], timeout=30)
    commit = revision.stdout.strip()
    version = re.search(r'^version\s*=\s*"([^"]+)"', manifest.read_text(encoding="utf-8"), re.MULTILINE)
    matched = revision.returncode == 0 and commit == K_RUST_COMMIT and version and version.group(1) == K_RUST_VERSION
    results.add(
        "native_pin",
        "PASS" if matched else "MISMATCH",
        f"k-rust {version.group(1) if version else '<unknown>'} @ {commit or '<unknown>'}; bundled K {K_VERSION} @ {K_COMMIT}",
    )
    return bool(matched)


def envelope(output: str) -> dict[str, Any]:
    parsed = json.loads(output)
    if parsed.get("format") != "KAST" or parsed.get("version") != 4 or "term" not in parsed:
        raise ValueError("expected fail-closed KAST JSON v4 envelope")
    return parsed


LABELS = {
    "_*__": "*", "_/__": "/", "_+__": "+", "_-__": "-", "_>=__": ">=",
    "_>__": ">", "_<=__": "<=", "_<__": "<", "_==__": "==", "_!=__": "!=",
    "_&&__": "&&", "_||__": "||", "-__": "neg", "!__": "not",
}


def abstract_term(value: Any) -> Any:
    if not isinstance(value, dict):
        raise ValueError(f"term node is not an object: {value!r}")
    node = value.get("node")
    if node == "KToken":
        sort = value.get("sort")
        if not isinstance(sort, dict) or sort.get("node") != "KSort" or sort.get("params") != []:
            raise ValueError(f"unsupported token sort, refusing to discard it: {sort!r}")
        return [sort.get("name"), value.get("token")]
    if node == "KApply":
        label = value.get("label")
        if not isinstance(label, dict) or label.get("node") != "KLabel" or label.get("params") != []:
            raise ValueError(f"unsupported label shape, refusing to discard it: {label!r}")
        name = label.get("name")
        matches = [short for prefix, short in LABELS.items() if isinstance(name, str) and name.startswith(prefix)]
        if len(matches) != 1:
            raise ValueError(f"unknown or ambiguous label {name!r}; normalizer fails closed")
        arguments = value.get("args")
        if not isinstance(arguments, list) or value.get("arity") != len(arguments):
            raise ValueError(f"invalid KApply arity for {name!r}")
        return [matches[0], *(abstract_term(item) for item in arguments)]
    raise ValueError(f"unknown KAST node {node!r}; normalizer fails closed")


def find_module(definition: dict[str, Any], name: str) -> dict[str, Any]:
    term = envelope(json.dumps(definition))["term"]
    if not isinstance(term, dict) or term.get("node") != "KDefinition":
        raise ValueError("definition is not a KDefinition")
    modules = [module for module in term.get("modules", []) if module.get("name") == name]
    if len(modules) != 1:
        raise ValueError(f"expected exactly one module {name!r}, found {len(modules)}")
    return modules[0]


def verify_definition_structure(parsed: dict[str, Any], compiled: dict[str, Any]) -> None:
    expected_parsed = {
        SYNTAX_MODULE: {"KProduction": 19, "KSyntaxAssociativity": 6, "KSyntaxPriority": 1},
        RULES_MODULE: {"KRule": 18},
        MODULE: {"KProduction": 2, "KRule": 1},
    }
    for name, expected in expected_parsed.items():
        counts: dict[str, int] = {}
        for sentence in find_module(parsed, name).get("localSentences", []):
            node = sentence.get("node", "<missing>")
            counts[node] = counts.get(node, 0) + 1
        if counts != expected:
            raise ValueError(f"parsed {name} sentence counts differ: {counts}")

    syntax_compiled = find_module(compiled, SYNTAX_MODULE)
    contexts = [sentence for sentence in syntax_compiled["localSentences"] if sentence.get("node") == "KContext"]
    attributes = [context.get("att", {}).get("att", {}) for context in contexts]
    seqstrict = sum("seqstrict" in attribute for attribute in attributes)
    strict = sum("strict" in attribute for attribute in attributes)
    if (len(contexts), seqstrict, strict) != (24, 20, 4):
        raise ValueError(f"expected 24 generated contexts (20 seqstrict, 4 strict), got {(len(contexts), seqstrict, strict)}")

    main_compiled = find_module(compiled, MODULE)
    rules = [sentence for sentence in main_compiled["localSentences"] if sentence.get("node") == "KRule"]
    heat = sum("heat" in sentence.get("att", {}).get("att", {}) for sentence in rules)
    cool = sum("cool" in sentence.get("att", {}).get("att", {}) for sentence in rules)
    if (heat, cool) != (24, 24):
        raise ValueError(f"expected 24 heat and 24 cool rules, got {(heat, cool)}")


def compile_reference(kompile: str, output: Path) -> subprocess.CompletedProcess[str]:
    return run(
        [
            kompile, str(FIXTURE), "--main-module", MODULE, "--syntax-module", MODULE,
            "--backend", "llvm", "--emit-json", "--output-definition", str(output),
        ],
        timeout=240,
    )


def reference_oracle(results: Results, tools: dict[str, str | None], workspace: Path, pins: dict[str, Any]) -> tuple[Path | None, dict[str, Any]]:
    if not all(tools.get(name) for name in ("kompile", "kast", "kparse", "krun")):
        results.add("reference_oracle", "UNAVAILABLE", "all pinned reference commands are required")
        return None, {}
    definition = workspace / "reference-definition"
    process = compile_reference(tools["kompile"], definition)  # type: ignore[arg-type]
    if process.returncode != 0:
        results.add("reference_compile", "FAIL", compact(process))
        return None, {}
    try:
        parsed = json.loads((definition / "parsed.json").read_text(encoding="utf-8"))
        compiled = json.loads((definition / "compiled.json").read_text(encoding="utf-8"))
        verify_definition_structure(parsed, compiled)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        results.add("reference_structure", "FAIL", str(error))
        return definition, {}
    results.add("reference_structure", "PASS", "19 grammar productions, 18 rules, 24 contexts and 24 heat/cool pairs")

    terms: dict[str, Any] = {}
    roundtrips: dict[str, str] = {}
    roundtrip_mismatches: list[str] = []
    reparsed_terms: dict[str, Any] = {}
    for path in sorted(ACCEPTED.glob("*.expr")):
        parsed_process = run([
            tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Expr",
            "--output", "json", str(path),
        ], timeout=60)  # type: ignore[list-item]
        if parsed_process.returncode != 0:
            raise RuntimeError(f"accepted parse failed for {path.name}: {compact(parsed_process)}")
        term = envelope(parsed_process.stdout)["term"]
        if abstract_term(term) != EXPECTED_TREES[path.name]:
            raise RuntimeError(f"wrong precedence/associativity tree for {path.name}: {abstract_term(term)!r}")
        terms[path.name] = term

        portable = run([
            tools["kparse"], "--definition", str(definition), "--module", MODULE, "--sort", "Expr", str(path),
        ], timeout=60)  # type: ignore[list-item]
        if portable.returncode != 0 or "Lbl" not in portable.stdout:
            raise RuntimeError(f"kparse failed for {path.name}: {compact(portable)}")

        unparsed = run([
            tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Expr",
            "--output", "program", str(path),
        ], timeout=60)  # type: ignore[list-item]
        if unparsed.returncode != 0:
            raise RuntimeError(f"unparse failed for {path.name}: {compact(unparsed)}")
        roundtrip_file = workspace / f"roundtrip-{path.name}"
        roundtrip_file.write_text(unparsed.stdout, encoding="utf-8")
        reparsed = run([
            tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Expr",
            "--output", "json", str(roundtrip_file),
        ], timeout=60)  # type: ignore[list-item]
        if reparsed.returncode != 0:
            raise RuntimeError(f"unparser output did not reparse for {path.name}: {compact(reparsed)}")
        reparsed_term = envelope(reparsed.stdout)["term"]
        reparsed_terms[path.name] = reparsed_term
        if canonical(reparsed_term) != canonical(term):
            roundtrip_mismatches.append(path.name)
        roundtrips[path.name] = unparsed.stdout.strip()

        executed = run([tools["krun"], "--definition", str(definition), "--output", "pretty", str(path)], timeout=60)  # type: ignore[list-item]
        normalized = re.sub(r"\s+", " ", executed.stdout).strip()
        expected = f"<k> {EXPECTED_RESULTS[path.name]} ~> .K </k>"
        if executed.returncode != 0 or normalized != expected:
            raise RuntimeError(f"wrong normal form for {path.name}: {compact(executed)}")

    aggregate = hashlib.sha256("".join(f"{name}\0{canonical(term)}\n" for name, term in sorted(terms.items())).encode()).hexdigest()
    results.add(
        "accepted_parse_trees",
        "PASS" if aggregate == pins.get("accepted_tree_aggregate_sha256") else "FAIL",
        f"9 full KAST v4 trees preserve every node; aggregate={aggregate}",
    )
    unparse_aggregate = hashlib.sha256("".join(f"{name}\0{text}\n" for name, text in sorted(roundtrips.items())).encode()).hexdigest()
    unparse_pin_ok = unparse_aggregate == pins.get("unparse_aggregate_sha256")
    expected_unparse_mismatch = (
        roundtrip_mismatches == ["unary-binding.expr"]
        and abstract_term(reparsed_terms["unary-binding.expr"])
        == ["+", ["Int", "-1"], ["Int", "2"]]
    )
    results.add(
        "unparse_output_pin",
        "PASS" if unparse_pin_ok else "FAIL",
        f"9 reference unparse outputs aggregate={unparse_aggregate}",
    )
    results.add(
        "unparse_roundtrips",
        "EXPECTED-MISMATCH" if expected_unparse_mismatch else ("PASS" if not roundtrip_mismatches else "FAIL"),
        "8 trees round-trip exactly; unary-binding unparses '- 1' as '-1' and reparses it as one signed Int token"
        if expected_unparse_mismatch
        else f"tree-changing unparse cases={roundtrip_mismatches}",
    )
    results.add("reference_execution", "PASS", "all accepted terms normalize; short-circuit avoids division by zero")

    syntax_locations = {
        "dangling-operator.expr": (2, 1),
        "unclosed-parenthesis.expr": (2, 1),
    }
    for path in sorted(SYNTAX_REJECTED.glob("*.expr")):
        rejected = run([
            tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Expr",
            "--output", "json", str(path),
        ], timeout=60)  # type: ignore[list-item]
        location = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", rejected.stderr)
        actual = (int(location.group(1)), int(location.group(2))) if location else None
        if rejected.returncode == 0 or actual != syntax_locations[path.name] or path.name not in rejected.stderr:
            raise RuntimeError(f"syntax rejection/location mismatch for {path.name}: {compact(rejected)}")
    results.add("syntax_rejections", "PASS", "both malformed programs fail exactly at authored EOF 2:1")

    for path in sorted(TYPE_REJECTED.glob("*.expr")):
        parsed_process = run([
            tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Expr",
            "--output", "json", str(path),
        ], timeout=60)  # type: ignore[list-item]
        executed = run([tools["krun"], "--definition", str(definition), "--output", "pretty", str(path)], timeout=60)  # type: ignore[list-item]
        normalized = re.sub(r"\s+", "", executed.stdout)
        stuck = (path.name == "bool-plus-int.expr" and "true+1~>.K" in normalized) or (path.name == "not-int.expr" and "!0~>.K" in normalized)
        if parsed_process.returncode != 0 or executed.returncode != 0 or not stuck:
            raise RuntimeError(f"semantic type rejection did not remain a stuck parsed Expr for {path.name}")
    results.add("semantic_type_rejections", "PASS", "true+1 and !0 parse as Expr but cannot normalize to Value")

    induced_output = workspace / "induced-definition"
    induced = run([
        tools["kompile"], str(INDUCED), "--main-module", INDUCED_MODULE, "--syntax-module", INDUCED_MODULE,
        "--backend", "llvm", "--output-definition", str(induced_output),
    ], timeout=120)  # type: ignore[list-item]
    location = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", induced.stderr)
    induced_ok = (
        induced.returncode != 0 and location is not None
        and tuple(map(int, location.groups())) == (3, 17, 3, 18)
        and "unexpected character sequence '@'" in induced.stderr and INDUCED.name in induced.stderr
    )
    results.add("induced_diagnostic", "PASS" if induced_ok else "FAIL", "authored '@' selected exactly at induced-definition-error.k:3:17-3:18" if induced_ok else compact(induced))
    return definition, parsed


def normalize_source_module(definition: dict[str, Any], name: str) -> dict[str, Any]:
    module = copy.deepcopy(find_module(definition, name))

    def visit(value: Any) -> Any:
        if isinstance(value, dict):
            result: dict[str, Any] = {}
            for key, child in value.items():
                if value.get("node") == "KAtt" and key == "att":
                    if not isinstance(child, dict):
                        raise ValueError("KAtt.att is not an object")
                    child = {attribute: item for attribute, item in child.items() if attribute not in METADATA_ATTRIBUTES}
                if key == "bracketLabel" and isinstance(child, dict):
                    if child.get("node") != "KLabel" or child.get("params") != [] or not isinstance(child.get("name"), str):
                        raise ValueError(f"unsupported bracketLabel object {child!r}")
                    child = child["name"]
                result[key] = visit(child)
            if result.get("node") == "KSyntaxAssociativity":
                if not isinstance(result.get("tags"), list):
                    raise ValueError("associativity tags are not a list")
                result["tags"].sort()
            if result.get("node") == "KSyntaxPriority":
                if not isinstance(result.get("priorities"), list):
                    raise ValueError("priority groups are not a list")
                for group in result["priorities"]:
                    if not isinstance(group, list):
                        raise ValueError("priority group is not a list")
                    group.sort()
            return result
        if isinstance(value, list):
            return [visit(item) for item in value]
        return value

    module = visit(module)
    module["imports"].sort(key=canonical)
    module["localSentences"].sort(key=canonical)
    return module


def native_oracle(results: Results, tools: dict[str, str | None], pinned: bool, workspace: Path, reference_parsed: dict[str, Any]) -> None:
    cargo = tools.get("cargo")
    if not cargo or not pinned:
        results.add("native_oracle", "UNAVAILABLE", "cargo and exact k-rust pin are required")
        return
    target = workspace / "native-target"
    environment = os.environ.copy()
    environment["CARGO_INCREMENTAL"] = "0"
    build = run([
        cargo, "build", "--quiet", "--locked", "--manifest-path", str(NATIVE_MANIFEST), "--target-dir", str(target),
    ], timeout=240, env=environment)
    if build.returncode != 0:
        results.add("native_build", "FAIL", compact(build))
        return
    binary = target / "debug" / "krs-m3a-native-expression-probe"
    source = run([str(binary), "source", str(FIXTURE), MODULE], timeout=60)
    if source.returncode != 0:
        results.add("native_outer_parse", "FAIL", compact(source))
        return
    try:
        native_definition = envelope(source.stdout)
        reference_grammar = normalize_source_module(reference_parsed, SYNTAX_MODULE)
        native_grammar = normalize_source_module(native_definition, SYNTAX_MODULE)
        grammar_match = reference_grammar == native_grammar
    except (ValueError, json.JSONDecodeError) as error:
        results.add("native_source_grammar", "FAIL", str(error))
        return
    results.add(
        "native_source_grammar",
        "MATCH" if grammar_match else "MISMATCH",
        "all 19 grammar productions, priority groups and associativity groups agree after explicit metadata/order/bracket-label normalization",
    )

    reference_project = {
        name: normalize_source_module(reference_parsed, name) for name in (SYNTAX_MODULE, RULES_MODULE, MODULE)
    }
    native_project = {
        name: normalize_source_module(native_definition, name) for name in (SYNTAX_MODULE, RULES_MODULE, MODULE)
    }
    full_match = reference_project == native_project
    def node_counts(module: dict[str, Any]) -> dict[str, int]:
        counts: dict[str, int] = {}
        for sentence in module["localSentences"]:
            node = sentence.get("node", "<missing>")
            counts[node] = counts.get(node, 0) + 1
        return counts

    exact_project_mismatch = (
        not full_match
        and node_counts(native_project[RULES_MODULE]) == {"KBubble": 18}
        and node_counts(reference_project[RULES_MODULE]) == {"KRule": 18}
        and node_counts(native_project[MODULE]) == {"KBubble": 1}
        and node_counts(reference_project[MODULE]) == {"KProduction": 2, "KRule": 1}
        and [item["name"] for item in native_project[MODULE]["imports"]] == [RULES_MODULE]
        and [item["name"] for item in reference_project[MODULE]["imports"]] == [RULES_MODULE, "MAP"]
    )
    results.add(
        "native_full_project",
        "MATCH" if full_match else ("EXPECTED-MISMATCH" if exact_project_mismatch else "FAIL"),
        "full project source agrees" if full_match else "outer Rust AST retains 19 unresolved rule/config bubbles while reference parsed.json contains resolved rules and generated cell productions/MAP import; no nodes were dropped",
    )

    resolved = run([str(binary), "resolve", str(FIXTURE), MODULE], timeout=120)
    blocker = resolved.returncode != 0 and 'module "ARRAY-IN-K"' in resolved.stderr and "requires native Z3 sort inference" in resolved.stderr
    native_parse_ok = True
    if resolved.returncode == 0:
        for path in sorted(ACCEPTED.glob("*.expr")):
            parsed = run([str(binary), "parse", str(FIXTURE), MODULE, str(path)], timeout=60)
            if parsed.returncode != 0 or canonical(envelope(parsed.stdout)["term"]) != canonical(envelope(run([
                tools["kast"], "--definition", str(workspace / "reference-definition"), "--module", MODULE,
                "--sort", "Expr", "--output", "json", str(path),
            ], timeout=60).stdout)["term"]):  # type: ignore[list-item]
                native_parse_ok = False
                break
    results.add(
        "native_resolution",
        "EXPECTED-MISMATCH" if blocker else ("PASS" if resolved.returncode == 0 and native_parse_ok else "FAIL"),
        "pinned public loader reaches domains.md but cannot resolve ambiguous ARRAY-IN-K without native Z3 sort inference" if blocker else compact(resolved),
    )


def main() -> int:
    results = Results()
    pins = verify_pins(results)
    tools = verify_capabilities(results)
    native_pinned = verify_native_pin(results)
    with tempfile.TemporaryDirectory(prefix="krs-m3a-oracle-") as temporary:
        definition, parsed = reference_oracle(results, tools, Path(temporary), pins)
        if definition is not None and parsed:
            native_oracle(results, tools, native_pinned, Path(temporary), parsed)
    if results.failed:
        print("\nM3A strict oracle FAILED")
        return 1
    print("\nM3A strict oracle PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
