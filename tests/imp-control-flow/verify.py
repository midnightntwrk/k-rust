#!/usr/bin/env python3
"""Strict production-independent oracle for the IMP control-flow slice."""

from __future__ import annotations

from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry  # noqa: E402
from support.checkouts import verify_checkout  # noqa: E402
from support.hashing import canonical_json, json_sha256, sha256_file, sha256_text  # noqa: E402
from support.lock import k_version  # noqa: E402
from support.pins import table  # noqa: E402
from support.process import compact, run  # noqa: E402
from support.report import Results  # noqa: E402
from support.tools import find_k_tool, k_version_matches  # noqa: E402


HERE = Path(__file__).resolve().parent
FIXTURES = HERE / "fixtures"
IMP = FIXTURES / "imp.k"
INDUCED = FIXTURES / "induced-definition-error.k"
ACCEPTED = HERE / "corpus" / "accepted"
NONTERMINATING = HERE / "corpus" / "nonterminating"
SYNTAX_REJECTED = HERE / "corpus" / "rejected" / "syntax"
SEMANTIC_REJECTED = HERE / "corpus" / "rejected" / "semantic"
PINS = HERE / "pins.json"
IMP_STATE = HERE.parent / "imp-state" / "fixtures"
UPSTREAM = ROOT.parent / "inspirations" / "runtimeverification" / "imp-semantics"

MODULE = "KRS-IMP-CONTROL-FLOW-IMP"
SYNTAX_MODULE = "KRS-IMP-CONTROL-FLOW-IMP-SYNTAX"
CALC_MODULE = "KRS-IMP-STATE-CALC"
CALC_SYNTAX_MODULE = "KRS-IMP-STATE-CALC-SYNTAX"
EXPR_SYNTAX_MODULE = "KRS-IMP-STATE-EXPR-SYNTAX"
EXPR_RULES_MODULE = "KRS-IMP-STATE-EXPR-RULES"
INDUCED_MODULE = "KRS-IMP-CONTROL-FLOW-INDUCED-DEFINITION-ERROR"


def ident(name: str) -> list[str]:
    return ["Id", name]


def integer(value: int) -> list[str]:
    return ["Int", str(value)]


def boolean(value: bool) -> list[str]:
    return ["Bool", str(value).lower()]


def assign(name: str, value: Any) -> list[Any]:
    return ["assign", ident(name), value]


def seq(first: Any, second: Any) -> list[Any]:
    return ["seq", first, second]


EXPECTED_TREES: dict[str, Any] = {
    "empty-block.imp": ["empty-block"],
    "if-true.imp": ["if", boolean(True), assign("x", integer(1))],
    "if-false.imp": ["if", boolean(False), assign("x", integer(1))],
    "explicit-else.imp": [
        "if-else",
        boolean(False),
        assign("x", integer(1)),
        assign("x", integer(2)),
    ],
    "dangling-else.imp": seq(
        assign("x", integer(0)),
        seq(
            assign("y", integer(0)),
            seq(
                [
                    "if",
                    boolean(False),
                    [
                        "if-else",
                        boolean(True),
                        assign("y", integer(1)),
                        assign("y", integer(2)),
                    ],
                ],
                assign("x", integer(1)),
            ),
        ),
    ),
    "block-sequence.imp": seq(
        [
            "block",
            seq(assign("x", integer(1)), assign("y", ["+", ident("x"), integer(1)])),
        ],
        assign("z", ["+", ident("y"), integer(1)]),
    ),
    "while-followed.imp": seq(
        assign("x", integer(3)),
        seq(
            [
                "while",
                [">", ident("x"), integer(0)],
                ["block", assign("x", ["-", ident("x"), integer(1)])],
            ],
            assign("y", ["+", ident("x"), integer(1)]),
        ),
    ),
    "nested-control.imp": seq(
        assign("x", integer(2)),
        [
            "if-else",
            [">", ident("x"), integer(0)],
            [
                "block",
                [
                    "while",
                    [">", ident("x"), integer(0)],
                    assign("x", ["-", ident("x"), integer(1)]),
                ],
            ],
            ["block", assign("x", integer(99))],
        ],
    ),
}

EXPECTED_EXECUTIONS: dict[str, dict[str, Any]] = {
    "empty-block.imp": {"steps": 1, "env": {}},
    "if-true.imp": {"steps": 3, "env": {"x": "1"}},
    "if-false.imp": {"steps": 3, "env": {}},
    "explicit-else.imp": {"steps": 2, "env": {"x": "2"}},
    "dangling-else.imp": {"steps": 9, "env": {"x": "1", "y": "0"}},
    "block-sequence.imp": {"steps": 19, "env": {"x": "1", "y": "2", "z": "3"}},
    "while-followed.imp": {"steps": 83, "env": {"x": "0", "y": "1"}},
    "nested-control.imp": {"steps": 59, "env": {"x": "0"}},
}

SEARCH_DEPTHS = {
    "explicit-else.imp": (0, 1, 2),
    "dangling-else.imp": (0, 1, 2, 4, 9),
}
NONTERMINATING_DEPTHS = (0, 1, 2, 3, 4, 8, 16, 32)
ORACLE_WORKERS = max(
    1,
    int(os.environ.get("KRS_IMP_CONTROL_FLOW_ORACLE_WORKERS", min(8, os.cpu_count() or 1))),
)

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


def aggregate(values: dict[str, Any]) -> str:
    material = "".join(
        f"{name}\0{canonical_json(value)}\n" for name, value in sorted(values.items())
    )
    return sha256_text(material)


def fixture_files() -> list[Path]:
    return [
        IMP,
        INDUCED,
        *sorted(ACCEPTED.glob("*.imp")),
        *sorted(NONTERMINATING.glob("*.imp")),
        *sorted(SYNTAX_REJECTED.glob("*.imp")),
        *sorted(SEMANTIC_REJECTED.glob("*.imp")),
    ]


def verify_pins(results: Results) -> dict[str, Any]:
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    upstream_commit = table(pins.get("upstream_imp"), "pins.upstream_imp").get("commit")
    actual = {str(path.relative_to(HERE)): sha256_file(path) for path in fixture_files()}
    results.add(
        "corpus_hashes",
        "PASS" if actual == pins.get("corpus_sha256") else "FAIL",
        f"{len(actual)} corpus and fixture hashes are exact; actual={actual}",
    )
    layered = {"expr.k": sha256_file(IMP_STATE / "expr.k"), "calc.k": sha256_file(IMP_STATE / "calc.k")}
    results.add(
        "imp_state_layer",
        "PASS" if layered == pins.get("imp_state_sha256") else "FAIL",
        f"the inherited expression/state oracle is exact; hashes={layered}",
    )
    try:
        verify_checkout(UPSTREAM, str(upstream_commit), label="modern IMP")
        detail = f"modern IMP {upstream_commit}, clean"
        status = "PASS"
    except GateError as error:
        detail, status = str(error), "FAIL"
    results.add("upstream_sources", status, detail)
    surface = IMP.read_text(encoding="utf-8")
    required = (
        'requires "../../imp-state/fixtures/calc.k"',
        '"if" "(" Expr ")" Stmt "else" Stmt',
        "strict(1)",
        "avoid",
        '"while" "(" Expr ")" Stmt',
        '"{" Stmt "}"',
        '"{" "}"',
        "if ( C ) S => if ( C ) S else {}",
        "while ( C ) S",
        "S ~> { }",
        "{ } => .K",
    )
    results.add(
        "fixture_surface",
        "PASS" if all(fragment in surface for fragment in required) else "FAIL",
        "if/else, dangling-else control, while, blocks and all six rules occur literally",
    )
    return pins


def verify_tools(results: Results) -> dict[str, str]:
    tools: dict[str, str] = {}
    for name in ("kompile", "kast", "kparse", "krun"):
        executable = find_k_tool(name)
        if executable is None:
            results.add(f"tool_{name}", "FAIL", "not found on PATH")
            continue
        version = run([executable, "--version"], timeout=30, check=False)
        output = "\n".join((version.stdout, version.stderr))
        results.add(
            f"tool_{name}",
            "PASS" if k_version_matches(version, k_version()) else "FAIL",
            output.strip().splitlines()[0] if output.strip() else "empty version output",
        )
        tools[name] = executable
    return tools


def envelope(output: str, *, search: bool = False) -> dict[str, Any]:
    start = output.find("{")
    if start < 0:
        raise ValueError("KAST output has no JSON envelope")
    value = json.loads(output[start:])
    if set(value) != {"format", "version", "term"}:
        raise ValueError(f"unexpected KAST envelope keys {sorted(value)}")
    if value["format"] != "KAST" or value["version"] != 4:
        raise ValueError(f"expected KAST v4, got {value.get('format')} v{value.get('version')}")
    validate_term(value["term"], search=search)
    return value


def validate_sort(sort: Any) -> None:
    if not isinstance(sort, dict) or set(sort) != {"node", "name", "params"}:
        raise ValueError(f"unsupported sort shape {sort!r}")
    if sort["node"] != "KSort" or not isinstance(sort["name"], str):
        raise ValueError(f"unsupported sort {sort!r}")
    for parameter in sort["params"]:
        validate_sort(parameter)


def validate_label(label: Any, *, search: bool) -> str:
    if not isinstance(label, dict) or set(label) != {"node", "name", "params"}:
        raise ValueError(f"unsupported label shape {label!r}")
    if label["node"] != "KLabel" or not isinstance(label["name"], str):
        raise ValueError(f"unsupported label {label!r}")
    for parameter in label["params"]:
        validate_sort(parameter)
    name = label["name"]
    fixed = {"<generatedTop>", "<generatedCounter>", "<k>", "<env>", ".Map", "_Map_", "_|->_"}
    accepted = name in fixed or "KRS-IMP-STATE-" in name or "KRS-IMP-CONTROL-FLOW-" in name or name.startswith("#freezer")
    if search and name == "#Equals":
        accepted = True
    if not accepted:
        raise ValueError(f"unrecognized project KLabel {name!r}")
    return name


def validate_term(term: Any, *, search: bool = False) -> None:
    if not isinstance(term, dict) or not isinstance(term.get("node"), str):
        raise ValueError(f"unsupported KAST term {term!r}")
    node = term["node"]
    if node == "KApply":
        if set(term) != {"node", "label", "arity", "args"}:
            raise ValueError(f"unexpected KApply keys {sorted(term)}")
        validate_label(term["label"], search=search)
        if term["arity"] != len(term["args"]):
            raise ValueError("KApply arity differs from args")
        for argument in term["args"]:
            validate_term(argument, search=search)
    elif node == "KToken":
        if set(term) != {"node", "sort", "token"} or not isinstance(term["token"], str):
            raise ValueError(f"unsupported KToken {term!r}")
        validate_sort(term["sort"])
    elif node == "KSequence":
        if set(term) != {"node", "arity", "items"} or term["arity"] != len(term["items"]):
            raise ValueError(f"unsupported KSequence {term!r}")
        for item in term["items"]:
            validate_term(item, search=search)
    elif node == "KVariable" and search:
        if set(term) != {"node", "name", "sort"} or not isinstance(term["name"], str):
            raise ValueError(f"unsupported KVariable {term!r}")
        validate_sort(term["sort"])
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
    names = {
        "___KRS-IMP-STATE-CALC-SYNTAX_Stmt_Stmt_Stmt": "seq",
        "_=_;_KRS-IMP-STATE-CALC-SYNTAX_Stmt_Id_Expr": "assign",
        "_+__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": "+",
        "_-__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": "-",
        "_>__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": ">",
        "if(_)__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt": "if",
        "if(_)_else__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt_Stmt": "if-else",
        "while(_)__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt": "while",
        "{_}_KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Stmt": "block",
        "{}_KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt": "empty-block",
    }
    name = label(term)
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
    return Counter(
        sentence.get("node", "<missing>") for sentence in find_module(definition, name)["localSentences"]
    )


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
                result["imports"].sort(key=canonical_json)
            if isinstance(result.get("localSentences"), list):
                result["localSentences"].sort(key=canonical_json)
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
        SYNTAX_MODULE: {"KProduction": 5},
        MODULE: {"KRule": 6},
        CALC_SYNTAX_MODULE: {"KSyntaxAssociativity": 1, "KProduction": 3, "KSyntaxPriority": 1},
        EXPR_SYNTAX_MODULE: {"KProduction": 19, "KSyntaxAssociativity": 6, "KSyntaxPriority": 1},
        EXPR_RULES_MODULE: {"KRule": 18},
        CALC_MODULE: {"KProduction": 11, "KRule": 6},
    }
    for name, counts in expected.items():
        actual = dict(sentence_counts(parsed, name))
        if actual != counts:
            raise ValueError(f"parsed {name} counts differ: expected={counts}, actual={actual}")

    productions = [
        sentence
        for sentence in find_module(parsed, SYNTAX_MODULE)["localSentences"]
        if sentence.get("node") == "KProduction"
    ]
    by_label = {production["klabel"]["name"]: production["att"]["att"] for production in productions}
    if_else = by_label.get("if(_)_else__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt_Stmt", {})
    while_attrs = by_label.get("while(_)__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt", {})
    if "avoid" not in if_else or "strict" not in if_else or "strict" in while_attrs:
        raise ValueError("dangling-else avoid/strict or deliberately non-strict while attributes differ")

    rule_labels = {
        sentence.get("att", {}).get("att", {}).get("label")
        for sentence in find_module(parsed, MODULE)["localSentences"]
        if sentence.get("node") == "KRule"
    }
    expected_labels = {f"{MODULE}.{name}" for name in ("if-true", "if-false", "if-else", "while", "block", "done")}
    if rule_labels != expected_labels:
        raise ValueError(f"control-flow labels differ: {rule_labels}")

    contexts = [
        sentence
        for sentence in find_module(compiled, SYNTAX_MODULE)["localSentences"]
        if sentence.get("node") == "KContext"
    ]
    if len(contexts) != 1 or "strict" not in contexts[0].get("att", {}).get("att", {}):
        raise ValueError("if/else strict(1) did not generate exactly one strict context")
    main_rules = [
        sentence
        for sentence in find_module(compiled, MODULE)["localSentences"]
        if sentence.get("node") == "KRule"
    ]
    heat = sum("heat" in sentence.get("att", {}).get("att", {}) for sentence in main_rules)
    cool = sum("cool" in sentence.get("att", {}).get("att", {}) for sentence in main_rules)
    if len(main_rules) != 58 or (heat, cool) != (26, 26):
        raise ValueError(f"expected 58 compiled rules and 26 heat/cool pairs, got {len(main_rules)}, {(heat, cool)}")


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


def final_environment_if_complete(term: dict[str, Any]) -> dict[str, str] | None:
    try:
        return final_environment(term)
    except ValueError:
        return None


def compile_reference(kompile: str, output: Path) -> subprocess.CompletedProcess[str]:
    return run(
        [
            kompile,
            str(IMP),
            "--main-module",
            MODULE,
            "--syntax-module",
            SYNTAX_MODULE,
            "--backend",
            "llvm",
            "--enable-search",
            "--emit-json",
            "--output-definition",
            str(output),
        ],
        timeout=300,
        check=False,
    )


def parse_accepted(
    tools: dict[str, str], definition: Path, workspace: Path
) -> tuple[dict[str, Any], dict[str, str]]:
    trees: dict[str, Any] = {}
    unparsed: dict[str, str] = {}
    for path in sorted(ACCEPTED.glob("*.imp")):
        command = [
            tools["kast"], "--definition", str(definition), "--module", MODULE,
            "--sort", "Stmt", "--output", "json", str(path),
        ]
        process = run(command, timeout=60, check=False)
        if process.returncode != 0:
            raise RuntimeError(f"accepted parse failed for {path.name}: {compact(process)}")
        term = envelope(process.stdout)["term"]
        abstract = abstract_term(term)
        if abstract != EXPECTED_TREES[path.name]:
            raise RuntimeError(f"wrong tree for {path.name}: {abstract!r}")
        trees[path.name] = term
        portable = run(
            [tools["kparse"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", str(path)],
            timeout=60,
            check=False,
        )
        if portable.returncode != 0 or "Lbl" not in portable.stdout:
            raise RuntimeError(f"kparse failed for {path.name}: {compact(portable)}")
        pretty = run(command[:-2] + ["program", str(path)], timeout=60, check=False)
        if pretty.returncode != 0:
            raise RuntimeError(f"unparse failed for {path.name}: {compact(pretty)}")
        roundtrip = workspace / f"roundtrip-{path.name}"
        roundtrip.write_text(pretty.stdout, encoding="utf-8")
        reparsed = run(command[:-1] + [str(roundtrip)], timeout=60, check=False)
        if reparsed.returncode != 0 or canonical_json(envelope(reparsed.stdout)["term"]) != canonical_json(term):
            raise RuntimeError(f"parse/unparse/parse changed {path.name}: {compact(reparsed)}")
        unparsed[path.name] = pretty.stdout.strip()
    return trees, unparsed


def execute_case(
    krun: str,
    definition: Path,
    path: Path,
    *,
    statistics: bool = False,
    depth: int | None = None,
    search: bool = False,
) -> subprocess.CompletedProcess[str]:
    command = [krun, "--definition", str(definition)]
    if statistics:
        command.append("--statistics")
    if search:
        command.append("--search")
    if depth is not None:
        command.extend(["--depth", str(depth)])
    command.extend(["--output", "json", "-cENV=.Map", str(path)])
    return run(command, timeout=60, check=False)


def execute_accepted(krun: str, definition: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    finals: dict[str, Any] = {}
    jobs: list[tuple[str, int, Path]] = []
    for name, expectation in EXPECTED_EXECUTIONS.items():
        path = ACCEPTED / name
        process = execute_case(krun, definition, path, statistics=True)
        if process.returncode != 0:
            raise RuntimeError(f"execution failed for {name}: {compact(process)}")
        match = re.search(r"\[(\d+) steps\]", process.stdout)
        if match is None or int(match.group(1)) != expectation["steps"]:
            raise RuntimeError(f"rewrite count differs for {name}: {compact(process)}")
        term = envelope(process.stdout)["term"]
        if final_environment(term) != expectation["env"]:
            raise RuntimeError(f"final environment differs for {name}: {final_environment(term)!r}")
        finals[name] = term
        jobs.extend((name, depth, path) for depth in range(expectation["steps"] + 1))

    def snapshot(job: tuple[str, int, Path]) -> tuple[str, dict[str, Any]]:
        name, depth, path = job
        process = execute_case(krun, definition, path, depth=depth)
        if process.returncode != 0:
            raise RuntimeError(f"depth-{depth} execution failed for {name}: {compact(process)}")
        return f"{name}@{depth:03d}", envelope(process.stdout)["term"]

    with ThreadPoolExecutor(max_workers=ORACLE_WORKERS) as executor:
        trace = dict(executor.map(snapshot, jobs))
    for name in ("if-true.imp", "if-false.imp"):
        desugared = trace[f"{name}@001"]
        cells = {label(cell): cell["args"][0] for cell in desugared["args"]}
        k_cell = cells.get("<k>")
        if (
            not isinstance(k_cell, dict)
            or k_cell.get("node") != "KSequence"
            or not k_cell.get("items")
            or label(k_cell["items"][0])
            != "if(_)_else__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt_Stmt"
        ):
            raise RuntimeError(f"no-else form did not desugar through [if-else] for {name}")
    return finals, trace


def search_frontier(term: dict[str, Any]) -> dict[str, Any]:
    if label(term) != "#Equals" or term.get("arity") != 2:
        raise ValueError(f"expected one deterministic #Equals search solution, got {term!r}")
    variable, frontier = term["args"]
    if variable.get("node") != "KVariable" or variable.get("name") != "Result":
        raise ValueError(f"unexpected search result binder {variable!r}")
    return frontier


def verify_search(
    krun: str, definition: Path
) -> tuple[dict[str, Any], dict[str, Any]]:
    searches: dict[str, Any] = {}
    bounded: dict[str, Any] = {}
    jobs: list[tuple[str, int, Path, bool]] = []
    for name, depths in SEARCH_DEPTHS.items():
        jobs.extend((name, depth, ACCEPTED / name, False) for depth in depths)
    infinite = NONTERMINATING / "infinite-loop.imp"
    jobs.extend((infinite.name, depth, infinite, True) for depth in NONTERMINATING_DEPTHS)

    def frontier(job: tuple[str, int, Path, bool]) -> tuple[str, dict[str, Any], dict[str, Any], bool]:
        name, depth, path, nonterminating = job
        ordinary = execute_case(krun, definition, path, depth=depth)
        searched = execute_case(krun, definition, path, depth=depth, search=True)
        if ordinary.returncode != 0 or searched.returncode != 0:
            raise RuntimeError(
                f"bounded search failed for {name}@{depth}: ordinary={compact(ordinary)}, search={compact(searched)}"
            )
        state = envelope(ordinary.stdout)["term"]
        search_term = envelope(searched.stdout, search=True)["term"]
        if canonical_json(search_frontier(search_term)) != canonical_json(state):
            raise RuntimeError(f"search frontier differs from execution at {name}@{depth}")
        if nonterminating and final_environment_if_complete(state) is not None:
            raise RuntimeError(f"infinite loop unexpectedly terminated by depth {depth}")
        return f"{name}@{depth:03d}", search_term, state, nonterminating

    with ThreadPoolExecutor(max_workers=ORACLE_WORKERS) as executor:
        for key, search_term, state, nonterminating in executor.map(frontier, jobs):
            searches[key] = search_term
            if nonterminating:
                bounded[key] = state
    return searches, bounded


def normalize_diagnostic(stderr: str) -> str:
    return stderr.replace(str(ROOT), "<ROOT>").strip()


def verify_rejections(
    tools: dict[str, str], definition: Path
) -> tuple[dict[str, Any], dict[str, str]]:
    locations = {
        "missing-condition.imp": (1, 5, 1, 6),
        "missing-else-body.imp": (2, 1, 2, 1),
        "stray-else.imp": (1, 1, 1, 5),
        "unclosed-block.imp": (2, 1, 2, 1),
    }
    fragments = {
        "missing-condition.imp": "unexpected token ')' following token '('",
        "missing-else-body.imp": "unexpected end of file following token",
        "stray-else.imp": "unexpected token 'else'",
        "unclosed-block.imp": "unexpected end of file following token ';'",
    }
    diagnostics: dict[str, str] = {}
    for path in sorted(SYNTAX_REJECTED.glob("*.imp")):
        process = run(
            [tools["kast"], "--definition", str(definition), "--module", MODULE, "--sort", "Stmt", "--output", "json", str(path)],
            timeout=60,
            check=False,
        )
        match = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", process.stderr)
        actual = tuple(map(int, match.groups())) if match else None
        if (
            process.returncode == 0
            or actual != locations[path.name]
            or fragments[path.name] not in process.stderr
            or path.name not in process.stderr
        ):
            raise RuntimeError(f"syntax rejection differs for {path.name}: {compact(process)}")
        diagnostics[path.name] = normalize_diagnostic(process.stderr)

    stuck: dict[str, Any] = {}
    expectations = {"non-bool-if.imp": 1, "undefined-condition.imp": 2, "non-bool-while.imp": 2}
    for name, steps in expectations.items():
        process = execute_case(tools["krun"], definition, SEMANTIC_REJECTED / name, statistics=True)
        match = re.search(r"\[(\d+) steps\]", process.stdout)
        if process.returncode != 0 or match is None or int(match.group(1)) != steps:
            raise RuntimeError(f"stuck behavior differs for {name}: {compact(process)}")
        term = envelope(process.stdout)["term"]
        if final_environment_if_complete(term) is not None:
            raise RuntimeError(f"semantic rejection unexpectedly completed for {name}")
        stuck[name] = term
    return stuck, diagnostics


def verify_induced_diagnostic(kompile: str, workspace: Path) -> str:
    process = run(
        [
            kompile, str(INDUCED), "--main-module", INDUCED_MODULE, "--syntax-module", INDUCED_MODULE,
            "--backend", "llvm", "--output-definition", str(workspace / "induced-kompiled"),
        ],
        timeout=120,
        check=False,
    )
    match = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", process.stderr)
    actual = tuple(map(int, match.groups())) if match else None
    if (
        process.returncode == 0
        or actual != (2, 27, 2, 28)
        or 'Encountered: "@"' not in process.stderr
        or INDUCED.name not in process.stderr
    ):
        raise RuntimeError(f"induced diagnostic differs: {compact(process)}")
    return normalize_diagnostic(process.stderr)


def reference_oracle(
    results: Results, tools: dict[str, str], pins: dict[str, Any], workspace: Path
) -> None:
    if set(tools) != {"kompile", "kast", "kparse", "krun"}:
        results.add("reference_oracle", "FAIL", "all four pinned K commands are required")
        return
    definition = workspace / "imp-kompiled"
    compiled_process = compile_reference(tools["kompile"], definition)
    if compiled_process.returncode != 0:
        results.add("reference_compile", "FAIL", compact(compiled_process))
        return
    try:
        parsed = json.loads((definition / "parsed.json").read_text(encoding="utf-8"))
        compiled = json.loads((definition / "compiled.json").read_text(encoding="utf-8"))
        verify_definition_structure(parsed, compiled)
        definition_hashes = {
            "parsed": json_sha256(normalized_definition(parsed)),
            "compiled": json_sha256(normalized_definition(compiled)),
        }
        results.add(
            "definition_structure",
            "PASS" if definition_hashes == pins.get("normalized_definition_sha256") else "FAIL",
            "5 control productions, 6 labeled rules, avoid/strict distinction, one context and "
            f"26 heat/cool pairs; hashes={definition_hashes}",
        )

        trees, unparsed = parse_accepted(tools, definition, workspace)
        tree_hash = aggregate(trees)
        unparse_hash = aggregate(unparsed)
        results.add(
            "parse_trees",
            "PASS" if tree_hash == pins.get("accepted_tree_aggregate_sha256") else "FAIL",
            f"8 full KAST v4 trees freeze right association and dangling else; aggregate={tree_hash}",
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
            f"both branches, blocks, loops and following statements match; aggregate={final_hash}",
        )
        results.add(
            "llvm_traces",
            "PASS" if trace_hash == pins.get("llvm_trace_aggregate_sha256") else "FAIL",
            f"{len(trace)} exact depth-indexed states retain control and generated strictness frames; aggregate={trace_hash}",
        )

        searches, bounded = verify_search(tools["krun"], definition)
        search_hash = aggregate(searches)
        bounded_hash = aggregate(bounded)
        search_pins = pins.get("bounded_search_sha256", {})
        results.add(
            "bounded_search",
            "PASS"
            if search_hash == search_pins.get("frontiers") and bounded_hash == search_pins.get("nontermination")
            else "FAIL",
            f"{len(searches)} single-result search frontiers equal direct execution; 8 infinite-loop bounds remain live; "
            f"frontiers={search_hash}, nontermination={bounded_hash}",
        )

        stuck, syntax_diagnostics = verify_rejections(tools, definition)
        stuck_hash = aggregate(stuck)
        diagnostic_hash = aggregate(syntax_diagnostics)
        rejection_pins = pins.get("rejection_sha256", {})
        results.add(
            "rejections",
            "PASS"
            if stuck_hash == rejection_pins.get("stuck_states")
            and diagnostic_hash == rejection_pins.get("syntax_diagnostics")
            else "FAIL",
            f"four exact syntax diagnostics and three exact stuck states; stuck={stuck_hash}, diagnostics={diagnostic_hash}",
        )

        induced = verify_induced_diagnostic(tools["kompile"], workspace)
        induced_hash = sha256_text(induced)
        results.add(
            "definition_diagnostic",
            "PASS" if induced_hash == pins.get("induced_diagnostic_sha256") else "FAIL",
            f"authored @ selected exactly at induced-definition-error.k:2:27-2:28; hash={induced_hash}",
        )
    except (OSError, ValueError, RuntimeError, json.JSONDecodeError) as error:
        results.add("reference_oracle", "FAIL", str(error))


def main() -> int:
    results = Results()
    pins = verify_pins(results)
    tools = verify_tools(results)
    with tempfile.TemporaryDirectory(prefix="krs-imp-control-flow-oracle-") as temporary:
        reference_oracle(results, tools, pins, Path(temporary))
    if results.failed:
        print("\nIMP control flow strict oracle FAILED")
        return 1
    print("\nIMP control flow strict oracle PASSED")
    return 0


if __name__ == "__main__":
    entry("IMP control flow strict oracle", main)
