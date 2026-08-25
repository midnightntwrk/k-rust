#!/usr/bin/env python3
"""Strict production-independent oracle for the IMP calculation/state slice."""

from __future__ import annotations

from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import copy
import hashlib
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
FIXTURES = HERE / "fixtures"
EXPR = FIXTURES / "expr.k"
CALC = FIXTURES / "calc.k"
INDUCED = FIXTURES / "induced-definition-error.k"
ACCEPTED = HERE / "corpus" / "accepted"
SYNTAX_REJECTED = HERE / "corpus" / "rejected" / "syntax"
SEMANTIC_REJECTED = HERE / "corpus" / "rejected" / "semantic"
PINS = HERE / "pins.json"
UPSTREAM = (
    ROOT.parent
    / "inspirations"
    / "runtimeverification"
    / "imp-semantics"
)
UPSTREAM_DEFINITION = UPSTREAM / "src" / "kimp" / "kdist" / "imp-semantics"

MODULE = "KRS-M3B-CALC"
SYNTAX_MODULE = "KRS-M3B-CALC-SYNTAX"
EXPR_SYNTAX_MODULE = "KRS-M3B-EXPR-SYNTAX"
EXPR_RULES_MODULE = "KRS-M3B-EXPR-RULES"
INDUCED_MODULE = "KRS-M3B-INDUCED-DEFINITION-ERROR"
K_VERSION = "v7.1.337"
K_COMMIT = "4a46d1231473b599c699160132fd6e76a5c46406"
UPSTREAM_COMMIT = "683a773418add3bcae8ded47c2b24e94494e1988"

EXPECTED_TREES: dict[str, Any] = {
    "single-assignment.calc": ["assign", ["Id", "x"], ["Int", "1"]],
    "initial-environment.calc": [
        "assign",
        ["Id", "y"],
        ["+", ["Id", "x"], ["Int", "1"]],
    ],
    "lookup-evaluation-order.calc": [
        "seq",
        ["assign", ["Id", "x"], ["Int", "2"]],
        [
            "assign",
            ["Id", "y"],
            ["+", ["Id", "x"], ["*", ["Id", "x"], ["Int", "3"]]],
        ],
    ],
    "update-existing.calc": [
        "seq",
        ["assign", ["Id", "x"], ["Int", "1"]],
        ["assign", ["Id", "x"], ["+", ["Id", "x"], ["Int", "4"]]],
    ],
    "right-associated-sequence.calc": [
        "seq",
        ["assign", ["Id", "x"], ["Int", "1"]],
        [
            "seq",
            ["assign", ["Id", "y"], ["Int", "2"]],
            ["assign", ["Id", "z"], ["+", ["Id", "x"], ["Id", "y"]]],
        ],
    ],
}

EXPECTED_EXECUTIONS = {
    "single-assignment.calc": {"initial_env": ".Map", "steps": 1, "env": {"x": "1"}},
    "initial-environment.calc": {
        "initial_env": "x |-> 41",
        "steps": 7,
        "env": {"x": "41", "y": "42"},
    },
    "lookup-evaluation-order.calc": {
        "initial_env": ".Map",
        "steps": 15,
        "env": {"x": "2", "y": "8"},
    },
    "update-existing.calc": {"initial_env": ".Map", "steps": 9, "env": {"x": "5"}},
    "right-associated-sequence.calc": {
        "initial_env": ".Map",
        "steps": 14,
        "env": {"x": "1", "y": "2", "z": "3"},
    },
}

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

    def add(self, name: str, status: str, detail: str) -> None:
        print(f"{status:12} {name}: {detail}")
        if status not in {"PASS", "MATCH"}:
            self.failed = True


def run(
    command: list[str],
    *,
    timeout: int = 180,
    cwd: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )


def compact(process: subprocess.CompletedProcess[str], limit: int = 1200) -> str:
    value = "\n".join(part.strip() for part in (process.stdout, process.stderr) if part.strip())
    value = re.sub(r"/[A-Za-z0-9_.+@%/=-]+", "<PATH>", value)
    return value[:limit] + ("…" if len(value) > limit else "")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def aggregate(values: dict[str, Any]) -> str:
    material = "".join(
        f"{name}\0{canonical(value)}\n" for name, value in sorted(values.items())
    )
    return hashlib.sha256(material.encode()).hexdigest()


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def fixture_files() -> list[Path]:
    return [
        EXPR,
        CALC,
        INDUCED,
        *sorted(ACCEPTED.glob("*.calc")),
        *sorted(SYNTAX_REJECTED.glob("*.calc")),
        *sorted(SEMANTIC_REJECTED.glob("*.calc")),
    ]


def verify_pins(results: Results) -> dict[str, Any]:
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    tool_pin = pins.get("reference_k") == {
        "version": K_VERSION.removeprefix("v"),
        "commit": K_COMMIT,
    }
    upstream_pin = pins.get("upstream_imp") == {"commit": UPSTREAM_COMMIT}
    results.add(
        "declared_pins",
        "PASS" if tool_pin and upstream_pin else "FAIL",
        "K and modern IMP revisions are exact",
    )
    actual = {str(path.relative_to(HERE)): sha256(path) for path in fixture_files()}
    results.add(
        "source_hashes",
        "PASS" if actual == pins.get("source_sha256") else "FAIL",
        f"{len(actual)} handwritten source hashes are exact; actual={actual}",
    )
    upstream_hashes = {
        "expr.k": sha256(UPSTREAM_DEFINITION / "expr.k"),
        "calc.k": sha256(UPSTREAM_DEFINITION / "calc.k"),
    }
    revision = run(["git", "rev-parse", "HEAD"], cwd=UPSTREAM, timeout=30)
    actual_revision = revision.stdout.strip() if revision.returncode == 0 else ""
    results.add(
        "upstream_sources",
        "PASS"
        if upstream_hashes == pins.get("upstream_sha256") and actual_revision == UPSTREAM_COMMIT
        else "FAIL",
        f"modern IMP {actual_revision or '<unknown>'}; hashes={upstream_hashes}",
    )
    surface = CALC.read_text(encoding="utf-8")
    required = (
        "imports ID-SYNTAX",
        "syntax Expr ::= Id",
        'Id "=" Expr ";"',
        "strict(2)",
        "right:",
        "syntax priority stmt > seq-stmt",
        "$PGM:Stmt",
        "$ENV:Map",
        "S1 ~> S2",
        "X |-> V",
        "E [ X <- V ]",
    )
    results.add(
        "fixture_surface",
        "PASS" if all(fragment in surface for fragment in required) else "FAIL",
        "Id injection, grammar, strictness, priority, cells and three state rules occur literally",
    )
    return pins


def verify_tools(results: Results) -> dict[str, str]:
    tools: dict[str, str] = {}
    for name in ("kompile", "kast", "kparse", "krun"):
        executable = shutil.which(name)
        if executable is None:
            results.add(f"tool_{name}", "FAIL", "not found on PATH")
            continue
        version = run([executable, "--version"], timeout=30)
        text = "\n".join((version.stdout, version.stderr))
        results.add(
            f"tool_{name}",
            "PASS" if version.returncode == 0 and K_VERSION in text else "FAIL",
            text.strip().splitlines()[0] if text.strip() else "empty version output",
        )
        tools[name] = executable
    return tools


def envelope(output: str) -> dict[str, Any]:
    start = output.find("{")
    if start < 0:
        raise ValueError("KAST output has no JSON envelope")
    value = json.loads(output[start:])
    if set(value) != {"format", "version", "term"}:
        raise ValueError(f"unexpected KAST envelope keys {sorted(value)}")
    if value["format"] != "KAST" or value["version"] != 4:
        raise ValueError(f"expected KAST v4, got {value.get('format')} v{value.get('version')}")
    validate_term(value["term"])
    return value


def validate_sort(sort: Any) -> None:
    if not isinstance(sort, dict) or set(sort) != {"node", "name", "params"}:
        raise ValueError(f"unsupported sort shape {sort!r}")
    if sort["node"] != "KSort" or not isinstance(sort["name"], str) or sort["params"] != []:
        raise ValueError(f"unsupported sort {sort!r}")


def validate_label(label: Any) -> str:
    if not isinstance(label, dict) or set(label) != {"node", "name", "params"}:
        raise ValueError(f"unsupported label shape {label!r}")
    if label["node"] != "KLabel" or label["params"] != [] or not isinstance(label["name"], str):
        raise ValueError(f"unsupported label {label!r}")
    name = label["name"]
    fixed = {"<generatedTop>", "<generatedCounter>", "<k>", "<env>", ".Map", "_Map_", "_|->_"}
    if name not in fixed and "KRS-M3B-" not in name and not name.startswith("#freezer"):
        raise ValueError(f"unrecognized project KLabel {name!r}")
    return name


def validate_term(term: Any) -> None:
    if not isinstance(term, dict) or not isinstance(term.get("node"), str):
        raise ValueError(f"unsupported KAST term {term!r}")
    node = term["node"]
    if node == "KApply":
        if set(term) != {"node", "label", "arity", "args"}:
            raise ValueError(f"unexpected KApply keys {sorted(term)}")
        validate_label(term["label"])
        if term["arity"] != len(term["args"]):
            raise ValueError("KApply arity differs from args")
        for argument in term["args"]:
            validate_term(argument)
    elif node == "KToken":
        if set(term) != {"node", "sort", "token"} or not isinstance(term["token"], str):
            raise ValueError(f"unsupported KToken {term!r}")
        validate_sort(term["sort"])
    elif node == "KSequence":
        if set(term) != {"node", "arity", "items"} or term["arity"] != len(term["items"]):
            raise ValueError(f"unsupported KSequence {term!r}")
        for item in term["items"]:
            validate_term(item)
    else:
        raise ValueError(f"unsupported KAST node {node!r}")


def label(term: dict[str, Any]) -> str:
    if term.get("node") != "KApply":
        raise ValueError(f"expected application, got {term!r}")
    return term["label"]["name"]


def abstract_term(term: dict[str, Any]) -> Any:
    node = term.get("node")
    if node == "KToken":
        return [term["sort"]["name"], term["token"]]
    if node != "KApply":
        raise ValueError(f"unexpected authored-tree node {node!r}")
    name = label(term)
    names = {
        "___KRS-M3B-CALC-SYNTAX_Stmt_Stmt_Stmt": "seq",
        "_=_;_KRS-M3B-CALC-SYNTAX_Stmt_Id_Expr": "assign",
        "_+__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr": "+",
        "_*__KRS-M3B-EXPR-SYNTAX_Expr_Expr_Expr": "*",
    }
    if name not in names:
        raise ValueError(f"unknown authored-tree label {name!r}")
    return [names[name], *(abstract_term(argument) for argument in term["args"])]


def find_module(definition: dict[str, Any], name: str) -> dict[str, Any]:
    if definition.get("format") != "KAST" or definition.get("version") != 4:
        raise ValueError("definition JSON is not KAST v4")
    modules = definition.get("term", {}).get("modules", [])
    matches = [module for module in modules if module.get("name") == name]
    if len(matches) != 1:
        raise ValueError(f"expected one module {name!r}, found {len(matches)}")
    return matches[0]


def sentence_counts(definition: dict[str, Any], name: str) -> Counter[str]:
    return Counter(sentence.get("node", "<missing>") for sentence in find_module(definition, name)["localSentences"])


def normalized_definition(definition: dict[str, Any]) -> dict[str, Any]:
    value = copy.deepcopy(definition)

    def visit(node: Any) -> Any:
        if isinstance(node, dict):
            result: dict[str, Any] = {}
            for key, child in node.items():
                if node.get("node") == "KAtt" and key == "att":
                    child = {name: item for name, item in child.items() if name not in METADATA_ATTRIBUTES}
                result[key] = visit(child)
            if isinstance(result.get("imports"), list):
                result["imports"].sort(key=canonical)
            if isinstance(result.get("localSentences"), list):
                result["localSentences"].sort(key=canonical)
            if result.get("node") == "KSyntaxAssociativity":
                result["tags"].sort()
            if result.get("node") == "KSyntaxPriority":
                for group in result["priorities"]:
                    group.sort()
            return result
        if isinstance(node, list):
            return [visit(item) for item in node]
        return node

    value = visit(value)
    value["term"]["modules"].sort(key=lambda module: module["name"])
    return value


def verify_definition_structure(parsed: dict[str, Any], compiled: dict[str, Any]) -> None:
    expected = {
        SYNTAX_MODULE: {"KSyntaxAssociativity": 1, "KProduction": 3, "KSyntaxPriority": 1},
        EXPR_SYNTAX_MODULE: {"KProduction": 19, "KSyntaxAssociativity": 6, "KSyntaxPriority": 1},
        EXPR_RULES_MODULE: {"KRule": 18},
        MODULE: {"KProduction": 11, "KRule": 6},
    }
    for name, counts in expected.items():
        actual = dict(sentence_counts(parsed, name))
        if actual != counts:
            raise ValueError(f"parsed {name} counts differ: expected={counts}, actual={actual}")
    calc_syntax = find_module(compiled, SYNTAX_MODULE)
    contexts = [sentence for sentence in calc_syntax["localSentences"] if sentence.get("node") == "KContext"]
    if len(contexts) != 1 or "strict" not in contexts[0].get("att", {}).get("att", {}):
        raise ValueError("assignment strict(2) did not generate exactly one strict context")
    main_rules = [sentence for sentence in find_module(compiled, MODULE)["localSentences"] if sentence.get("node") == "KRule"]
    heat = sum("heat" in sentence.get("att", {}).get("att", {}) for sentence in main_rules)
    cool = sum("cool" in sentence.get("att", {}).get("att", {}) for sentence in main_rules)
    if (heat, cool) != (25, 25):
        raise ValueError(f"expected 25 inherited+assignment heat/cool pairs, got {(heat, cool)}")


def parse_map(term: dict[str, Any]) -> dict[str, str]:
    name = label(term)
    if name == ".Map":
        return {}
    if name == "_Map_":
        merged: dict[str, str] = {}
        for child in term["args"]:
            for key, value in parse_map(child).items():
                if key in merged:
                    raise ValueError(f"duplicate concrete map key {key!r}")
                merged[key] = value
        return merged
    if name == "_|->_":
        key, value = term["args"]
        if key.get("node") != "KToken" or key["sort"]["name"] != "Id":
            raise ValueError(f"non-Id environment key {key!r}")
        if value.get("node") != "KToken" or value["sort"]["name"] not in {"Int", "Bool"}:
            raise ValueError(f"non-Value environment value {value!r}")
        return {key["token"]: value["token"]}
    raise ValueError(f"unsupported concrete Map label {name!r}")


def final_environment(term: dict[str, Any]) -> dict[str, str]:
    if label(term) != "<generatedTop>":
        raise ValueError("final configuration is not generatedTop")
    cells = {label(cell): cell["args"][0] for cell in term["args"]}
    k_cell = cells.get("<k>")
    if k_cell != {"node": "KSequence", "arity": 0, "items": []}:
        raise ValueError(f"final k cell is not empty: {k_cell!r}")
    env = cells.get("<env>")
    if not isinstance(env, dict):
        raise ValueError("final configuration lacks env cell")
    return parse_map(env)


def compile_reference(kompile: str, output: Path) -> subprocess.CompletedProcess[str]:
    return run(
        [
            kompile,
            str(CALC),
            "--main-module",
            MODULE,
            "--syntax-module",
            SYNTAX_MODULE,
            "--backend",
            "llvm",
            "--emit-json",
            "--output-definition",
            str(output),
        ],
        timeout=300,
    )


def parse_accepted(tools: dict[str, str], definition: Path, workspace: Path) -> tuple[dict[str, Any], dict[str, str]]:
    trees: dict[str, Any] = {}
    unparsed: dict[str, str] = {}
    for path in sorted(ACCEPTED.glob("*.calc")):
        process = run(
            [tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", "--output", "json", str(path)],
            timeout=60,
        )
        if process.returncode != 0:
            raise RuntimeError(f"accepted parse failed for {path.name}: {compact(process)}")
        term = envelope(process.stdout)["term"]
        if abstract_term(term) != EXPECTED_TREES[path.name]:
            raise RuntimeError(f"wrong tree for {path.name}: {abstract_term(term)!r}")
        trees[path.name] = term
        portable = run(
            [tools["kparse"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", str(path)],
            timeout=60,
        )
        if portable.returncode != 0 or "Lbl" not in portable.stdout:
            raise RuntimeError(f"kparse failed for {path.name}: {compact(portable)}")
        pretty = run(
            [tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", "--output", "program", str(path)],
            timeout=60,
        )
        if pretty.returncode != 0:
            raise RuntimeError(f"unparse failed for {path.name}: {compact(pretty)}")
        roundtrip = workspace / f"roundtrip-{path.name}"
        roundtrip.write_text(pretty.stdout, encoding="utf-8")
        reparsed = run(
            [tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", "--output", "json", str(roundtrip)],
            timeout=60,
        )
        if reparsed.returncode != 0 or canonical(envelope(reparsed.stdout)["term"]) != canonical(term):
            raise RuntimeError(f"parse/unparse/parse changed {path.name}: {compact(reparsed)}")
        unparsed[path.name] = pretty.stdout.strip()
    return trees, unparsed


def execute_case(krun: str, definition: Path, path: Path, initial_env: str, statistics: bool = False, depth: int | None = None) -> subprocess.CompletedProcess[str]:
    command = [krun, "--definition", str(definition)]
    if statistics:
        command.append("--statistics")
    if depth is not None:
        command.extend(["--depth", str(depth)])
    command.extend(["--output", "json", f"-cENV={initial_env}", str(path)])
    return run(command, timeout=60)


def execute_accepted(krun: str, definition: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    finals: dict[str, Any] = {}
    jobs: list[tuple[str, int, Path, str]] = []
    for name, expectation in EXPECTED_EXECUTIONS.items():
        path = ACCEPTED / name
        process = execute_case(krun, definition, path, expectation["initial_env"], statistics=True)
        if process.returncode != 0:
            raise RuntimeError(f"execution failed for {name}: {compact(process)}")
        match = re.search(r"\[(\d+) steps\]", process.stdout)
        if match is None or int(match.group(1)) != expectation["steps"]:
            raise RuntimeError(f"rewrite count differs for {name}: {compact(process)}")
        term = envelope(process.stdout)["term"]
        if final_environment(term) != expectation["env"]:
            raise RuntimeError(f"final environment differs for {name}: {final_environment(term)!r}")
        finals[name] = term
        jobs.extend(
            (name, depth, path, expectation["initial_env"])
            for depth in range(expectation["steps"] + 1)
        )

    def snapshot(job: tuple[str, int, Path, str]) -> tuple[str, dict[str, Any]]:
        name, depth, path, initial_env = job
        process = execute_case(krun, definition, path, initial_env, depth=depth)
        if process.returncode != 0:
            raise RuntimeError(f"depth-{depth} execution failed for {name}: {compact(process)}")
        return f"{name}@{depth:03d}", envelope(process.stdout)["term"]

    with ThreadPoolExecutor(max_workers=min(8, os.cpu_count() or 1)) as executor:
        trace = dict(executor.map(snapshot, jobs))
    return finals, trace


def verify_rejections(tools: dict[str, str], definition: Path) -> tuple[dict[str, Any], str]:
    locations = {
        "missing-semicolon.calc": (2, 1, 2, 1),
        "missing-identifier.calc": (1, 1, 1, 2),
    }
    for path in sorted(SYNTAX_REJECTED.glob("*.calc")):
        process = run(
            [tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", "--output", "json", str(path)],
            timeout=60,
        )
        match = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", process.stderr)
        actual = tuple(map(int, match.groups())) if match else None
        if process.returncode == 0 or actual != locations[path.name] or path.name not in process.stderr:
            raise RuntimeError(f"syntax rejection differs for {path.name}: {compact(process)}")

    stuck: dict[str, Any] = {}
    expectations = {"undefined-variable.calc": 2, "type-error.calc": 1}
    for name, steps in expectations.items():
        process = execute_case(tools["krun"], definition, SEMANTIC_REJECTED / name, ".Map", statistics=True)
        match = re.search(r"\[(\d+) steps\]", process.stdout)
        if process.returncode != 0 or match is None or int(match.group(1)) != steps:
            raise RuntimeError(f"stuck behavior differs for {name}: {compact(process)}")
        term = envelope(process.stdout)["term"]
        if final_environment_if_complete(term) is not None:
            raise RuntimeError(f"semantic rejection unexpectedly completed for {name}")
        stuck[name] = term

    timeout = shutil.which("timeout")
    if timeout is None:
        raise RuntimeError("GNU timeout is required to contain the LLVM division hook abort")
    division = run(
        [
            timeout,
            "--signal=KILL",
            "8s",
            tools["krun"],
            "--definition",
            str(definition),
            "--output",
            "json",
            "-cENV=.Map",
            str(SEMANTIC_REJECTED / "division-by-zero.calc"),
        ],
        timeout=15,
    )
    detail = "[hook_INT_tdiv]: Division by zero: 1 / 0"
    if division.returncode == 0 or detail not in division.stderr:
        raise RuntimeError(f"division-by-zero behavior differs: {compact(division)}")
    return stuck, detail


def final_environment_if_complete(term: dict[str, Any]) -> dict[str, str] | None:
    try:
        return final_environment(term)
    except ValueError:
        return None


def verify_induced_diagnostic(kompile: str, workspace: Path) -> None:
    process = run(
        [
            kompile,
            str(INDUCED),
            "--main-module",
            INDUCED_MODULE,
            "--syntax-module",
            INDUCED_MODULE,
            "--backend",
            "llvm",
            "--output-definition",
            str(workspace / "induced-kompiled"),
        ],
        timeout=120,
    )
    match = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", process.stderr)
    actual = tuple(map(int, match.groups())) if match else None
    if (
        process.returncode == 0
        or actual != (2, 19, 2, 20)
        or 'Encountered: "@"' not in process.stderr
        or INDUCED.name not in process.stderr
    ):
        raise RuntimeError(f"induced diagnostic differs: {compact(process)}")


def reference_oracle(results: Results, tools: dict[str, str], pins: dict[str, Any], workspace: Path) -> None:
    if set(tools) != {"kompile", "kast", "kparse", "krun"}:
        results.add("reference_oracle", "FAIL", "all four pinned K commands are required")
        return
    definition = workspace / "calc-kompiled"
    compiled_process = compile_reference(tools["kompile"], definition)
    if compiled_process.returncode != 0:
        results.add("reference_compile", "FAIL", compact(compiled_process))
        return
    try:
        parsed = json.loads((definition / "parsed.json").read_text(encoding="utf-8"))
        compiled = json.loads((definition / "compiled.json").read_text(encoding="utf-8"))
        verify_definition_structure(parsed, compiled)
        definition_hashes = {
            "parsed": hashlib.sha256(canonical(normalized_definition(parsed)).encode()).hexdigest(),
            "compiled": hashlib.sha256(canonical(normalized_definition(compiled)).encode()).hexdigest(),
        }
        expected_definition_hashes = pins.get("normalized_definition_sha256")
        results.add(
            "definition_structure",
            "PASS" if definition_hashes == expected_definition_hashes else "FAIL",
            f"3 calc productions, priority/right-assoc, 3 rules, 1 strict context and 25 heat/cool pairs; hashes={definition_hashes}",
        )

        trees, unparsed = parse_accepted(tools, definition, workspace)
        tree_hash = aggregate(trees)
        unparse_hash = aggregate(unparsed)
        results.add(
            "parse_trees",
            "PASS" if tree_hash == pins.get("accepted_tree_aggregate_sha256") else "FAIL",
            f"5 full KAST v4 trees and exact right association; aggregate={tree_hash}",
        )
        results.add(
            "unparse_roundtrip",
            "PASS" if unparse_hash == pins.get("unparse_aggregate_sha256") else "FAIL",
            f"all trees round-trip exactly; aggregate={unparse_hash}",
        )

        finals, trace = execute_accepted(tools["krun"], definition)
        final_hash = aggregate(finals)
        trace_hash = aggregate(trace)
        results.add(
            "final_states",
            "PASS" if final_hash == pins.get("final_state_aggregate_sha256") else "FAIL",
            f"initialization, lookup, assignment, update and sequencing match; aggregate={final_hash}",
        )
        results.add(
            "llvm_traces",
            "PASS" if trace_hash == pins.get("llvm_trace_aggregate_sha256") else "FAIL",
            f"{len(trace)} exact depth-indexed LLVM states retain generated heat/cool frames; aggregate={trace_hash}",
        )

        stuck, division_detail = verify_rejections(tools, definition)
        stuck_hash = aggregate(stuck)
        rejection_hashes = pins.get("rejection_sha256", {})
        rejection_ok = (
            stuck_hash == rejection_hashes.get("stuck_state_aggregate")
            and hashlib.sha256(division_detail.encode()).hexdigest() == rejection_hashes.get("division_error")
        )
        results.add(
            "rejections",
            "PASS" if rejection_ok else "FAIL",
            f"syntax locations, two stuck states and LLVM division error are exact; stuck aggregate={stuck_hash}",
        )
        verify_induced_diagnostic(tools["kompile"], workspace)
        results.add(
            "definition_diagnostic",
            "PASS",
            "authored @ selected exactly at induced-definition-error.k:2:19-2:20",
        )
    except (OSError, ValueError, RuntimeError, json.JSONDecodeError) as error:
        results.add("reference_oracle", "FAIL", str(error))


def main() -> int:
    results = Results()
    pins = verify_pins(results)
    tools = verify_tools(results)
    with tempfile.TemporaryDirectory(prefix="krs-m3b-oracle-") as temporary:
        reference_oracle(results, tools, pins, Path(temporary))
    if results.failed:
        print("\nM3B strict oracle FAILED")
        return 1
    print("\nM3B strict oracle PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
