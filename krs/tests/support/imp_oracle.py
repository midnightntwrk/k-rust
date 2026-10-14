"""Shared orchestration for the strict IMP state and control-flow oracles."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any, Mapping

from support import GateError, ROOT
from support import krs_gate
from support.checkouts import verify_checkout
from support.hashing import canonical_json, json_sha256, sha256_file, sha256_text
from support.lock import k_version
from support.pins import Ledger
from support.process import compact, run
from support.reference import (
    Key, Output, Pin, Snapshot, add_refresh_argument, json_sorted_lists, json_without_members, repository_inputs,
)
from support.report import Results
from support.tools import find_k_tool, install_k_advice, k_version_matches, z3_environment


TOOLS = ("kompile", "kast", "kparse", "krun")
"""The Java K commands the oracle runs live on a reference cache miss or `--refresh-reference`."""

DEFINITION_METADATA = (
    "org.kframework.attributes.Source",
    "org.kframework.attributes.Location",
    "org.kframework.definition.Production",
    "contentStartLine",
    "contentStartColumn",
    "digest",
    "productionID",
    "UNIQUE_ID",
)
"""Attribute names whose members the stored `parsed.json` and `compiled.json` omit.

They are the metadata attributes krs-gate's `normalized_definition` removes
(all but `syntaxModule`, which its reader still consults), and no structure
check reads them, so the recorded definitions keep every module and sentence
but none of the source locations or install paths.
"""

reduce_definition = json_without_members(DEFINITION_METADATA)

sort_module_lists = json_sorted_lists(("localSentences", "imports"))


def reduce_stored_definition(text: str) -> str:
    """The stored `parsed.json` or `compiled.json` of a kompiled definition.

    It omits the metadata attributes krs-gate removes, and sorts each module's
    `localSentences` and `imports`, which K writes in an order that varies
    between runs and checkouts; krs-gate's projection and normalized
    definition read both as sets, and the structure checks read counts,
    labels, and sets.
    """

    return sort_module_lists(reduce_definition(text))


@dataclass(frozen=True)
class InheritedLayer:
    """Fixtures of an earlier oracle that this oracle builds on, pinned by hash."""

    directory: Path
    files: tuple[str, ...]
    pin_key: str
    check: str
    detail: str


@dataclass(frozen=True)
class BoundedSearch:
    """Bounded `krun --search` frontiers compared with direct execution.

    Its presence compiles the reference definition with `--enable-search`.
    """

    depths: Mapping[str, tuple[int, ...]]
    nonterminating: Path
    nonterminating_program: str
    nonterminating_depths: tuple[int, ...]


@dataclass(frozen=True)
class DivisionCase:
    """A semantic rejection whose LLVM hook aborts with an exact message."""

    program: str
    stderr: str
    pin_key: str


@dataclass(frozen=True)
class RejectionPin:
    """Key and report names of the entries in the `rejection_sha256` pin table.

    `diagnostics_key` pins syntax diagnostics with the checkout path normalized.
    """

    stuck_key: str
    stuck_label: str
    diagnostics_key: str | None = None


@dataclass(frozen=True)
class Spec:
    """Fixture paths, expectations, and report wording of one strict oracle."""

    label: str
    here: Path
    source: Path
    fixture_sources: tuple[Path, ...]
    induced: Path
    accepted: Path
    syntax_rejected: Path
    semantic_rejected: Path
    pins_path: Path
    upstream: Path
    module: str
    syntax_module: str
    induced_module: str
    extension: str
    surface_fragments: tuple[str, ...]
    surface_detail: str
    expected_trees: Mapping[str, Any]
    expected_executions: Mapping[str, Mapping[str, Any]]
    syntax_locations: Mapping[str, tuple[int, int, int, int]]
    stuck_steps: Mapping[str, int]
    definition_detail: str
    trees_detail: str
    final_detail: str
    trace_detail: str
    rejection_detail: str
    induced_detail: str
    induced_location: tuple[int, int, int, int]
    compiled_dir: str
    rejection_pin: RejectionPin
    workers: int = 8
    syntax_fragments: Mapping[str, str] | None = None
    inherited_layer: InheritedLayer | None = None
    search: BoundedSearch | None = None
    division: DivisionCase | None = None
    pin_induced_diagnostic: bool = False
    """Hash the normalized induced diagnostic into `induced_diagnostic_sha256`."""


@dataclass(frozen=True)
class KAST:
    """Gate-owned validation policies and expectations for native KAST observations."""

    validation_policy: Mapping[str, Any]
    label_map: Mapping[str, str]
    parsed_counts: Mapping[str, Mapping[str, int]]
    heat_cool: tuple[int, int]
    context_attributes: tuple[str, ...]
    context_count: int
    search_validation_policy: Mapping[str, Any] | None = None
    production_attributes: Mapping[str, tuple[tuple[str, ...], tuple[str, ...]]] = field(default_factory=dict)
    rule_labels: tuple[str, ...] | None = None
    compiled_rule_count: int | None = None
    k_heads: Mapping[str, str] = field(default_factory=dict)


def read_term(session: krs_gate.Session, kast: KAST, output: str, *, search: bool = False) -> Any:
    """Read and validate tool output natively, retaining its lossless term for hashing."""

    policy = kast.search_validation_policy if search else kast.validation_policy
    if policy is None:
        raise GateError("bounded search needs a validation policy")
    return session.kast_inspect("term", text=output, allow_prefix=True, policy=policy)


def verify_definition_structure(
    spec: Spec, kast: KAST, session: krs_gate.Session, parsed: Path, compiled: Path,
) -> None:
    """Compare native sentence facts with the gate's data expectations."""

    facts = {
        name: session.kast_inspect("module_facts", path=parsed, name=name)
        for name in kast.parsed_counts
    }
    for name, counts in kast.parsed_counts.items():
        actual = facts[name]["counts"]
        if actual != counts:
            raise GateError(f"parsed {name} counts differ: expected={counts}, actual={actual}")
    productions = {
        fact["klabel"]: fact["attribute_keys"]
        for fact in facts[spec.syntax_module]["sentences"] if fact["node"] == "production"
    }
    for label, (required, forbidden) in kast.production_attributes.items():
        attributes = productions.get(label, [])
        if (label not in productions
                or any(key not in attributes for key in required)
                or any(key in attributes for key in forbidden)):
            raise GateError(f"production attributes differ for {label}: {attributes}")
    if kast.rule_labels is not None:
        actual_labels = {fact["label"] for fact in facts[spec.module]["sentences"] if fact["node"] == "rule"}
        if actual_labels != set(kast.rule_labels):
            raise GateError(f"rule labels differ: {actual_labels}")
    syntax = session.kast_inspect("module_facts", path=compiled, name=spec.syntax_module)
    contexts = [fact for fact in syntax["sentences"] if fact["node"] == "context"]
    if (len(contexts) != kast.context_count
            or any(key not in fact["attribute_keys"] for fact in contexts for key in kast.context_attributes)):
        raise GateError(f"compiled strict contexts differ: expected={kast.context_count}, actual={len(contexts)}")
    main = session.kast_inspect("module_facts", path=compiled, name=spec.module)
    rules = [fact for fact in main["sentences"] if fact["node"] == "rule"]
    heat_cool = tuple(sum(key in fact["attribute_keys"] for fact in rules) for key in ("heat", "cool"))
    if (heat_cool != kast.heat_cool
            or kast.compiled_rule_count is not None and len(rules) != kast.compiled_rule_count):
        raise GateError(f"compiled rules differ: count={len(rules)}, heat/cool={heat_cool}")


def normalize_diagnostic(stderr: str) -> str:
    """Replace the checkout path in a diagnostic before pinning it."""

    return stderr.replace(str(ROOT), "<ROOT>").strip()


def aggregate(values: Mapping[str, Any]) -> str:
    """Hash a named set of canonical JSON observations in key order."""

    material = "".join(
        f"{name}\0{canonical_json(value)}\n" for name, value in sorted(values.items())
    )
    return sha256_text(material)


def fixture_files(spec: Spec) -> list[Path]:
    """List every fixture and corpus input in the gate's established order."""

    files = [*spec.fixture_sources, spec.induced, *sorted(spec.accepted.glob(f"*{spec.extension}"))]
    if spec.search is not None:
        files.extend(sorted(spec.search.nonterminating.glob(f"*{spec.extension}")))
    files.extend(sorted(spec.syntax_rejected.glob(f"*{spec.extension}")))
    files.extend(sorted(spec.semantic_rejected.glob(f"*{spec.extension}")))
    return files


def verify_pins(spec: Spec, results: Results, pins: Ledger) -> None:
    """Compare fixture, checkout, and inherited layer input pins."""

    upstream_commit = pins.table("upstream_imp").get("commit")
    actual = {str(path.relative_to(spec.here)): sha256_file(path) for path in fixture_files(spec)}
    results.add(
        "corpus_hashes",
        "PASS" if actual == pins.get("corpus_sha256") else "FAIL",
        f"{len(actual)} corpus and fixture hashes are exact; actual={actual}",
    )
    layer = spec.inherited_layer
    if layer is not None:
        layered = {name: sha256_file(layer.directory / name) for name in layer.files}
        results.add(
            layer.check,
            "PASS" if layered == pins.get(layer.pin_key) else "FAIL",
            f"{layer.detail}; hashes={layered}",
        )
    try:
        verify_checkout(spec.upstream, str(upstream_commit), label="modern IMP")
        detail, status = f"modern IMP {upstream_commit}, clean", "PASS"
    except GateError as error:
        detail, status = str(error), "FAIL"
    results.add("upstream_sources", status, detail)
    surface = spec.source.read_text(encoding="utf-8")
    results.add(
        "fixture_surface",
        "PASS" if all(fragment in surface for fragment in spec.surface_fragments) else "FAIL",
        spec.surface_detail,
    )


def verify_tools(results: Results) -> dict[str, str]:
    """Find and version-check the four Java K commands for a live run.

    The snapshot calls this on its first live invocation; a missing or
    misversioned tool is reported here and then fails that invocation.
    """

    tools: dict[str, str] = {}
    for name in TOOLS:
        executable = find_k_tool(name)
        if executable is None:
            results.add(f"tool_{name}", "FAIL", f"not found in KRS_K_BIN or on PATH; {install_k_advice()}")
            continue
        version = run([executable, "--version"], timeout=30, check=False)
        output = "\n".join((version.stdout, version.stderr))
        matches = k_version_matches(version, k_version())
        results.add(
            f"tool_{name}",
            "PASS" if matches else "FAIL",
            output.strip().splitlines()[0] if output.strip() else "empty version output",
        )
        if matches:
            tools[name] = executable
    return tools


def compare_output(
    results: Results, pins: Ledger, name: str, key: str, observed: Any, detail: str
) -> None:
    """Report one Ledger output comparison without suppressing later checks."""

    try:
        pins.expect(key, observed)
    except GateError as error:
        results.add(name, "FAIL", str(error))
    else:
        results.add(name, "PASS", detail)


def reference_key(spec: Spec) -> Key:
    """The snapshot key: the oracle reads only its own and its inherited fixtures."""

    files = fixture_files(spec)
    if spec.inherited_layer is not None:
        files.extend(spec.inherited_layer.directory / name for name in spec.inherited_layer.files)
    return Key(tools=TOOLS, inputs=repository_inputs(files))


def compile_reference(spec: Spec, k: Snapshot, output: Path) -> subprocess.CompletedProcess[str]:
    """Compile the gate's reference definition with its selected search mode.

    Only the `parsed.json` and `compiled.json` the structure checks read are stored.
    """

    return k.run(
        "kompile/definition", "kompile",
        [
            str(spec.source), "--main-module", spec.module,
            "--syntax-module", spec.syntax_module, "--backend", "llvm",
            *(["--enable-search"] if spec.search is not None else []),
            "--emit-json", "--output-definition", str(output),
        ],
        timeout=300,
        outputs=(
            Output(output / "parsed.json", reduce_stored_definition),
            Output(output / "compiled.json", reduce_stored_definition),
        ),
    )


def parse_accepted(
    spec: Spec, kast: KAST, session: krs_gate.Session, k: Snapshot, definition: Path, workspace: Path
) -> tuple[dict[str, Any], dict[str, str]]:
    """Parse, unparse, and reparse the accepted corpus."""

    trees: dict[str, Any] = {}
    unparsed: dict[str, str] = {}
    for path in sorted(spec.accepted.glob(f"*{spec.extension}")):
        command = [
            "--definition", str(definition), "--module", spec.module,
            "--sort", "Stmt", "--output", "json", str(path),
        ]
        process = k.run(f"kast/accepted/{path.name}", "kast", command, timeout=60)
        if process.returncode != 0:
            raise RuntimeError(f"accepted parse failed for {path.name}: {compact(process)}")
        term = read_term(session, kast, process.stdout)
        abstract = session.kast_inspect("abstract_term", term, label_map=kast.label_map)
        if abstract != spec.expected_trees[path.name]:
            raise RuntimeError(f"wrong tree for {path.name}: {abstract!r}")
        trees[path.name] = term
        portable = k.run(
            f"kparse/accepted/{path.name}", "kparse",
            ["--definition", str(definition), "--module", spec.module, "--sort", "Stmt", str(path)],
            timeout=60,
        )
        if portable.returncode != 0 or not portable.stdout.strip():
            raise RuntimeError(f"kparse failed for {path.name}: {compact(portable)}")
        pretty = k.run(
            f"kast-unparse/accepted/{path.name}", "kast",
            command[:-2] + ["program", str(path)], timeout=60,
        )
        if pretty.returncode != 0:
            raise RuntimeError(f"unparse failed for {path.name}: {compact(pretty)}")
        roundtrip = workspace / f"roundtrip-{path.name}"
        roundtrip.write_text(pretty.stdout, encoding="utf-8")
        reparsed = k.run(
            f"kast-reparse/accepted/{path.name}", "kast", command[:-1] + [str(roundtrip)], timeout=60,
        )
        if reparsed.returncode != 0 or canonical_json(read_term(session, kast, reparsed.stdout)) != canonical_json(term):
            raise RuntimeError(f"parse/unparse/parse changed {path.name}: {compact(reparsed)}")
        unparsed[path.name] = pretty.stdout.strip()
    return trees, unparsed


def execute_case(
    k: Snapshot, label: str, definition: Path, path: Path, initial_env: str = ".Map",
    *, statistics: bool = False, depth: int | None = None, search: bool = False,
) -> subprocess.CompletedProcess[str]:
    """Execute one reference case with the gate's configuration."""

    command = ["--definition", str(definition)]
    if statistics:
        command.append("--statistics")
    if search:
        command.append("--search")
    if depth is not None:
        command.extend(["--depth", str(depth)])
    command.extend(["--output", "json", f"-cENV={initial_env}", str(path)])
    return k.run(label, "krun", command, timeout=60)


def execute_accepted(
    spec: Spec, kast: KAST, session: krs_gate.Session, k: Snapshot, definition: Path
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Collect final and depth-indexed states for every accepted case."""

    finals: dict[str, Any] = {}
    jobs: list[tuple[str, int, Path, str]] = []
    for name, expectation in spec.expected_executions.items():
        path = spec.accepted / name
        initial_env = str(expectation.get("initial_env", ".Map"))
        process = execute_case(k, f"krun/final/{name}", definition, path, initial_env, statistics=True)
        if process.returncode != 0:
            raise RuntimeError(f"execution failed for {name}: {compact(process)}")
        match = re.search(r"\[(\d+) steps\]", process.stdout)
        if match is None or int(match.group(1)) != expectation["steps"]:
            raise RuntimeError(f"rewrite count differs for {name}: {compact(process)}")
        term = read_term(session, kast, process.stdout)
        environment = session.kast_inspect("final_environment", term)
        if environment != expectation["env"]:
            raise RuntimeError(f"final environment differs for {name}: {environment!r}")
        finals[name] = term
        jobs.extend((name, depth, path, initial_env) for depth in range(int(expectation["steps"]) + 1))

    def snapshot(job: tuple[str, int, Path, str]) -> tuple[str, dict[str, Any]]:
        name, depth, path, initial_env = job
        process = execute_case(k, f"krun/depth/{name}@{depth:03d}", definition, path, initial_env, depth=depth)
        if process.returncode != 0:
            raise RuntimeError(f"depth-{depth} execution failed for {name}: {compact(process)}")
        return f"{name}@{depth:03d}", read_term(session, kast, process.stdout)

    with ThreadPoolExecutor(max_workers=spec.workers) as executor:
        trace = dict(executor.map(snapshot, jobs))
    for key, head in kast.k_heads.items():
        if not session.kast_inspect("k_head", trace[key], head=head):
            raise GateError(f"no-else form did not desugar through [if-else] at {key}")
    return finals, trace


def verify_search(
    spec: Spec, search: BoundedSearch, kast: KAST, session: krs_gate.Session, k: Snapshot, definition: Path
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Compare bounded search frontiers with direct execution."""

    searches: dict[str, Any] = {}
    bounded: dict[str, Any] = {}
    jobs: list[tuple[str, int, Path, bool]] = []
    for name, depths in search.depths.items():
        jobs.extend((name, depth, spec.accepted / name, False) for depth in depths)
    program = search.nonterminating / search.nonterminating_program
    jobs.extend((program.name, depth, program, True) for depth in search.nonterminating_depths)

    def frontier(job: tuple[str, int, Path, bool]) -> tuple[str, dict[str, Any], dict[str, Any], bool]:
        name, depth, path, nonterminating = job
        ordinary = execute_case(k, f"krun/bounded/{name}@{depth:03d}", definition, path, depth=depth)
        searched = execute_case(
            k, f"krun/search/{name}@{depth:03d}", definition, path, depth=depth, search=True,
        )
        if ordinary.returncode != 0 or searched.returncode != 0:
            raise RuntimeError(
                f"bounded search failed for {name}@{depth}: ordinary={compact(ordinary)}, search={compact(searched)}"
            )
        state = read_term(session, kast, ordinary.stdout)
        search_term = read_term(session, kast, searched.stdout, search=True)
        if canonical_json(session.kast_inspect("search_frontier", search_term)) != canonical_json(state):
            raise RuntimeError(f"search frontier differs from execution at {name}@{depth}")
        if nonterminating and session.kast_inspect("final_environment", state, if_complete=True) is not None:
            raise RuntimeError(f"{name} unexpectedly terminated by depth {depth}")
        return f"{name}@{depth:03d}", search_term, state, nonterminating

    with ThreadPoolExecutor(max_workers=spec.workers) as executor:
        for key, search_term, state, nonterminating in executor.map(frontier, jobs):
            searches[key] = search_term
            if nonterminating:
                bounded[key] = state
    return searches, bounded


def verify_rejections(
    spec: Spec, kast: KAST, session: krs_gate.Session, k: Snapshot, definition: Path
) -> tuple[dict[str, Any], dict[str, str]]:
    """Check exact parser locations and stuck reference executions.

    The normalized syntax diagnostics are returned only when the rejection pin
    has a key for them.
    """

    diagnostics: dict[str, str] = {}
    for path in sorted(spec.syntax_rejected.glob(f"*{spec.extension}")):
        process = k.run(
            f"kast/syntax-rejected/{path.name}", "kast",
            ["--definition", str(definition), "--module", spec.module,
             "--sort", "Stmt", "--output", "json", str(path)],
            timeout=60,
        )
        match = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", process.stderr)
        actual = tuple(map(int, match.groups())) if match else None
        fragment = (spec.syntax_fragments or {}).get(path.name)
        if (process.returncode == 0 or actual != spec.syntax_locations[path.name]
                or (fragment is not None and fragment not in process.stderr)
                or path.name not in process.stderr):
            raise RuntimeError(f"syntax rejection differs for {path.name}: {compact(process)}")
        if spec.rejection_pin.diagnostics_key is not None:
            diagnostics[path.name] = normalize_diagnostic(process.stderr)

    stuck: dict[str, Any] = {}
    expectations = spec.stuck_steps
    for name, steps in expectations.items():
        process = execute_case(
            k, f"krun/stuck/{name}", definition, spec.semantic_rejected / name, statistics=True,
        )
        match = re.search(r"\[(\d+) steps\]", process.stdout)
        if process.returncode != 0 or match is None or int(match.group(1)) != steps:
            raise RuntimeError(f"stuck behavior differs for {name}: {compact(process)}")
        term = read_term(session, kast, process.stdout)
        if session.kast_inspect("final_environment", term, if_complete=True) is not None:
            raise RuntimeError(f"semantic rejection unexpectedly completed for {name}")
        stuck[name] = term
    return stuck, diagnostics


def verify_division(
    spec: Spec, division: DivisionCase, k: Snapshot, definition: Path
) -> str:
    """Require the LLVM division hook to abort with its exact message.

    A live run contains the abort with GNU `timeout`.
    """

    process = k.run(
        f"krun/division/{division.program}", "krun",
        ["--definition", str(definition), "--output", "json", "-cENV=.Map",
         str(spec.semantic_rejected / division.program)],
        timeout=15, prefix=("timeout", "--signal=KILL", "8s"),
    )
    if process.returncode == 0 or division.stderr not in process.stderr:
        raise RuntimeError(f"{division.program} behavior differs: {compact(process)}")
    return division.stderr


def verify_induced_diagnostic(spec: Spec, k: Snapshot, workspace: Path) -> str | None:
    """Require the authored syntax error at its pinned source location.

    Return the normalized diagnostic when the gate pins it.
    """

    process = k.run(
        "kompile/induced-diagnostic", "kompile",
        [str(spec.induced), "--main-module", spec.induced_module,
         "--syntax-module", spec.induced_module, "--backend", "llvm",
         "--output-definition", str(workspace / "induced-kompiled")],
        timeout=120,
    )
    match = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", process.stderr)
    actual = tuple(map(int, match.groups())) if match else None
    if (process.returncode == 0 or actual != spec.induced_location
            or 'Encountered: "@"' not in process.stderr or spec.induced.name not in process.stderr):
        raise RuntimeError(f"induced diagnostic differs: {compact(process)}")
    if not spec.pin_induced_diagnostic:
        return None
    return normalize_diagnostic(process.stderr)


def reference_oracle(
    spec: Spec, kast: KAST, session: krs_gate.Session, results: Results, k: Snapshot, pins: Ledger, workspace: Path
) -> None:
    """Run the reference layers and retain every report line in gate order."""

    definition = workspace / spec.compiled_dir
    compiled_process = compile_reference(spec, k, definition)
    if compiled_process.returncode != 0:
        results.add("reference_compile", "FAIL", compact(compiled_process))
        return
    try:
        parsed = definition / "parsed.json"
        compiled = definition / "compiled.json"
        verify_definition_structure(spec, kast, session, parsed, compiled)
        definition_hashes = {
            "parsed": json_sha256(session.kast_normalize("normalized_definition", path=parsed)),
            "compiled": json_sha256(session.kast_normalize("normalized_definition", path=compiled)),
        }
        compare_output(results, pins, "definition_structure", "normalized_definition_sha256",
                       definition_hashes, f"{spec.definition_detail}; hashes={definition_hashes}")

        trees, unparsed = parse_accepted(spec, kast, session, k, definition, workspace)
        tree_hash, unparse_hash = aggregate(trees), aggregate(unparsed)
        compare_output(results, pins, "parse_trees", "accepted_tree_aggregate_sha256",
                       tree_hash, f"{spec.trees_detail}; aggregate={tree_hash}")
        compare_output(results, pins, "unparse_roundtrip", "unparse_aggregate_sha256",
                       unparse_hash, f"all trees round-trip exactly; aggregate={unparse_hash}")

        finals, trace = execute_accepted(spec, kast, session, k, definition)
        final_hash, trace_hash = aggregate(finals), aggregate(trace)
        compare_output(results, pins, "final_states", "final_state_aggregate_sha256",
                       final_hash, f"{spec.final_detail}; aggregate={final_hash}")
        compare_output(results, pins, "llvm_traces", "llvm_trace_aggregate_sha256",
                       trace_hash, f"{len(trace)} {spec.trace_detail}; aggregate={trace_hash}")

        search = spec.search
        if search is not None:
            searches, bounded = verify_search(spec, search, kast, session, k, definition)
            search_hash, bounded_hash = aggregate(searches), aggregate(bounded)
            compare_output(
                results, pins, "bounded_search", "bounded_search_sha256",
                {"frontiers": search_hash, "nontermination": bounded_hash},
                f"{len(searches)} single-result search frontiers equal direct execution; "
                f"{len(search.nonterminating_depths)} {Path(search.nonterminating_program).stem} "
                f"bounds remain live; frontiers={search_hash}, nontermination={bounded_hash}",
            )

        stuck, diagnostics = verify_rejections(spec, kast, session, k, definition)
        rejection_pin = spec.rejection_pin
        stuck_hash = aggregate(stuck)
        observed = {rejection_pin.stuck_key: stuck_hash}
        reported = [f"{rejection_pin.stuck_label}={stuck_hash}"]
        if rejection_pin.diagnostics_key is not None:
            diagnostic_hash = aggregate(diagnostics)
            observed[rejection_pin.diagnostics_key] = diagnostic_hash
            reported.append(f"diagnostics={diagnostic_hash}")
        if spec.division is not None:
            division_error = verify_division(spec, spec.division, k, definition)
            observed[spec.division.pin_key] = sha256_text(division_error)
        compare_output(results, pins, "rejections", "rejection_sha256", observed,
                       f"{spec.rejection_detail}; {', '.join(reported)}")

        induced = verify_induced_diagnostic(spec, k, workspace)
        if induced is not None:
            induced_hash = sha256_text(induced)
            compare_output(results, pins, "definition_diagnostic", "induced_diagnostic_sha256",
                           induced_hash, f"{spec.induced_detail}; hash={induced_hash}")
        else:
            results.add("definition_diagnostic", "PASS", spec.induced_detail)
    except (OSError, ValueError, RuntimeError) as error:
        results.add("reference_oracle", "FAIL", str(error))


def main(spec: Spec, kast: KAST) -> int:
    """Run a strict IMP oracle and finish its ledger and snapshot only after every check passes.

    The Java K observations replay the reference cache entry that
    `reference_sha256.oracle` pins; a cache miss or `--refresh-reference`
    runs Java K live instead.
    """

    parser = argparse.ArgumentParser(description=f"{spec.label} gate")
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    results = Results()
    pins = Ledger(spec.pins_path, record=arguments.record)
    binary = krs_gate.configured_or_build()
    verify_pins(spec, results, pins)
    with krs_gate.Session(binary, environment=z3_environment()) as session:
        with tempfile.TemporaryDirectory(prefix=f"krs-{spec.here.name}-oracle-") as temporary:
            workspace = Path(temporary)
            try:
                k = Snapshot(
                    f"{spec.here.name}/oracle", reference_key(spec), workspace=workspace,
                    refresh=arguments.refresh_reference, pin=Pin(pins, "oracle"),
                    tools=lambda: verify_tools(results),
                )
            except GateError as error:
                results.add("reference_snapshot", "FAIL", str(error))
            else:
                reference_oracle(spec, kast, session, results, k, pins, workspace)
                if not results.failed:
                    try:
                        results.add("reference_snapshot", "PASS", k.finish())
                    except GateError as error:
                        results.add("reference_snapshot", "FAIL", str(error))
    if results.failed:
        print(f"\n{spec.label} FAILED")
        return 1
    pins.finish(spec.label)
    print(f"\n{spec.label} PASSED")
    return 0
