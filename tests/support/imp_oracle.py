"""Shared orchestration for the strict IMP state and control-flow oracles."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from typing import Any, Callable, Mapping

from support import GateError
from support.checkouts import verify_checkout
from support.hashing import canonical_json, json_sha256, sha256_file, sha256_text
from support.lock import k_version
from support.pins import Ledger
from support.process import compact, run
from support.report import Results
from support.tools import find_k_tool, k_version_matches


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

    `diagnostics_key` pins the normalized syntax diagnostics and requires
    `KAST.normalize_diagnostic`.
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
    """Gate-owned KAST readers and checks; their implementations stay in each verifier."""

    envelope: Callable[..., dict[str, Any]]
    abstract_term: Callable[[dict[str, Any]], Any]
    normalized_definition: Callable[[dict[str, Any]], dict[str, Any]]
    verify_definition_structure: Callable[[dict[str, Any], dict[str, Any]], None]
    final_environment: Callable[[dict[str, Any]], dict[str, str]]
    final_environment_if_complete: Callable[[dict[str, Any]], dict[str, str] | None]
    search_frontier: Callable[[dict[str, Any]], dict[str, Any]] | None = None
    normalize_diagnostic: Callable[[str], str] | None = None
    execute_accepted: Callable[[str, Path], tuple[dict[str, Any], dict[str, Any]]] | None = None


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
    """Find and version-check the four Java K commands."""

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


def compile_reference(spec: Spec, kompile: str, output: Path) -> subprocess.CompletedProcess[str]:
    """Compile the gate's reference definition with its selected search mode."""

    return run(
        [
            kompile, str(spec.source), "--main-module", spec.module,
            "--syntax-module", spec.syntax_module, "--backend", "llvm",
            *(["--enable-search"] if spec.search is not None else []),
            "--emit-json", "--output-definition", str(output),
        ],
        timeout=300,
        check=False,
    )


def parse_accepted(
    spec: Spec, kast: KAST, tools: Mapping[str, str], definition: Path, workspace: Path
) -> tuple[dict[str, Any], dict[str, str]]:
    """Parse, unparse, and reparse the accepted corpus."""

    trees: dict[str, Any] = {}
    unparsed: dict[str, str] = {}
    for path in sorted(spec.accepted.glob(f"*{spec.extension}")):
        command = [
            tools["kast"], "--definition", str(definition), "--module", spec.module,
            "--sort", "Stmt", "--output", "json", str(path),
        ]
        process = run(command, timeout=60, check=False)
        if process.returncode != 0:
            raise RuntimeError(f"accepted parse failed for {path.name}: {compact(process)}")
        term = kast.envelope(process.stdout)["term"]
        abstract = kast.abstract_term(term)
        if abstract != spec.expected_trees[path.name]:
            raise RuntimeError(f"wrong tree for {path.name}: {abstract!r}")
        trees[path.name] = term
        portable = run(
            [tools["kparse"], "--definition", str(definition), "--module", spec.module,
             "--sort", "Stmt", str(path)],
            timeout=60, check=False,
        )
        if portable.returncode != 0 or "Lbl" not in portable.stdout:
            raise RuntimeError(f"kparse failed for {path.name}: {compact(portable)}")
        pretty = run(command[:-2] + ["program", str(path)], timeout=60, check=False)
        if pretty.returncode != 0:
            raise RuntimeError(f"unparse failed for {path.name}: {compact(pretty)}")
        roundtrip = workspace / f"roundtrip-{path.name}"
        roundtrip.write_text(pretty.stdout, encoding="utf-8")
        reparsed = run(command[:-1] + [str(roundtrip)], timeout=60, check=False)
        if reparsed.returncode != 0 or canonical_json(kast.envelope(reparsed.stdout)["term"]) != canonical_json(term):
            raise RuntimeError(f"parse/unparse/parse changed {path.name}: {compact(reparsed)}")
        unparsed[path.name] = pretty.stdout.strip()
    return trees, unparsed


def execute_case(
    spec: Spec, krun: str, definition: Path, path: Path, initial_env: str = ".Map",
    *, statistics: bool = False, depth: int | None = None, search: bool = False,
) -> subprocess.CompletedProcess[str]:
    """Execute one reference case with the gate's configuration."""

    command = [krun, "--definition", str(definition)]
    if statistics:
        command.append("--statistics")
    if search:
        command.append("--search")
    if depth is not None:
        command.extend(["--depth", str(depth)])
    command.extend(["--output", "json", f"-cENV={initial_env}", str(path)])
    return run(command, timeout=60, check=False)


def execute_accepted(
    spec: Spec, kast: KAST, krun: str, definition: Path
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Collect final and depth-indexed states for every accepted case."""

    finals: dict[str, Any] = {}
    jobs: list[tuple[str, int, Path, str]] = []
    for name, expectation in spec.expected_executions.items():
        path = spec.accepted / name
        initial_env = str(expectation.get("initial_env", ".Map"))
        process = execute_case(spec, krun, definition, path, initial_env, statistics=True)
        if process.returncode != 0:
            raise RuntimeError(f"execution failed for {name}: {compact(process)}")
        match = re.search(r"\[(\d+) steps\]", process.stdout)
        if match is None or int(match.group(1)) != expectation["steps"]:
            raise RuntimeError(f"rewrite count differs for {name}: {compact(process)}")
        term = kast.envelope(process.stdout)["term"]
        if kast.final_environment(term) != expectation["env"]:
            raise RuntimeError(f"final environment differs for {name}: {kast.final_environment(term)!r}")
        finals[name] = term
        jobs.extend((name, depth, path, initial_env) for depth in range(int(expectation["steps"]) + 1))

    def snapshot(job: tuple[str, int, Path, str]) -> tuple[str, dict[str, Any]]:
        name, depth, path, initial_env = job
        process = execute_case(spec, krun, definition, path, initial_env, depth=depth)
        if process.returncode != 0:
            raise RuntimeError(f"depth-{depth} execution failed for {name}: {compact(process)}")
        return f"{name}@{depth:03d}", kast.envelope(process.stdout)["term"]

    with ThreadPoolExecutor(max_workers=spec.workers) as executor:
        trace = dict(executor.map(snapshot, jobs))
    return finals, trace


def verify_search(
    spec: Spec, search: BoundedSearch, kast: KAST, krun: str, definition: Path
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Compare bounded search frontiers with direct execution."""

    search_frontier = kast.search_frontier
    if search_frontier is None:
        raise GateError("bounded search needs the KAST search frontier reader")
    searches: dict[str, Any] = {}
    bounded: dict[str, Any] = {}
    jobs: list[tuple[str, int, Path, bool]] = []
    for name, depths in search.depths.items():
        jobs.extend((name, depth, spec.accepted / name, False) for depth in depths)
    program = search.nonterminating / search.nonterminating_program
    jobs.extend((program.name, depth, program, True) for depth in search.nonterminating_depths)

    def frontier(job: tuple[str, int, Path, bool]) -> tuple[str, dict[str, Any], dict[str, Any], bool]:
        name, depth, path, nonterminating = job
        ordinary = execute_case(spec, krun, definition, path, depth=depth)
        searched = execute_case(spec, krun, definition, path, depth=depth, search=True)
        if ordinary.returncode != 0 or searched.returncode != 0:
            raise RuntimeError(
                f"bounded search failed for {name}@{depth}: ordinary={compact(ordinary)}, search={compact(searched)}"
            )
        state = kast.envelope(ordinary.stdout)["term"]
        search_term = kast.envelope(searched.stdout, search=True)["term"]
        if canonical_json(search_frontier(search_term)) != canonical_json(state):
            raise RuntimeError(f"search frontier differs from execution at {name}@{depth}")
        if nonterminating and kast.final_environment_if_complete(state) is not None:
            raise RuntimeError(f"{name} unexpectedly terminated by depth {depth}")
        return f"{name}@{depth:03d}", search_term, state, nonterminating

    with ThreadPoolExecutor(max_workers=spec.workers) as executor:
        for key, search_term, state, nonterminating in executor.map(frontier, jobs):
            searches[key] = search_term
            if nonterminating:
                bounded[key] = state
    return searches, bounded


def verify_rejections(
    spec: Spec, kast: KAST, tools: Mapping[str, str], definition: Path
) -> tuple[dict[str, Any], dict[str, str]]:
    """Check exact parser locations and stuck reference executions.

    The normalized syntax diagnostics are returned only when the rejection pin
    has a key for them.
    """

    normalize = kast.normalize_diagnostic
    if spec.rejection_pin.diagnostics_key is not None and normalize is None:
        raise GateError("pinned syntax diagnostics need the KAST diagnostic normalizer")
    diagnostics: dict[str, str] = {}
    for path in sorted(spec.syntax_rejected.glob(f"*{spec.extension}")):
        process = run(
            [tools["kast"], "--definition", str(definition), "--module", spec.module,
             "--sort", "Stmt", "--output", "json", str(path)],
            timeout=60, check=False,
        )
        match = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", process.stderr)
        actual = tuple(map(int, match.groups())) if match else None
        fragment = (spec.syntax_fragments or {}).get(path.name)
        if (process.returncode == 0 or actual != spec.syntax_locations[path.name]
                or (fragment is not None and fragment not in process.stderr)
                or path.name not in process.stderr):
            raise RuntimeError(f"syntax rejection differs for {path.name}: {compact(process)}")
        if spec.rejection_pin.diagnostics_key is not None and normalize is not None:
            diagnostics[path.name] = normalize(process.stderr)

    stuck: dict[str, Any] = {}
    expectations = spec.stuck_steps
    for name, steps in expectations.items():
        process = execute_case(spec, tools["krun"], definition, spec.semantic_rejected / name, statistics=True)
        match = re.search(r"\[(\d+) steps\]", process.stdout)
        if process.returncode != 0 or match is None or int(match.group(1)) != steps:
            raise RuntimeError(f"stuck behavior differs for {name}: {compact(process)}")
        term = kast.envelope(process.stdout)["term"]
        if kast.final_environment_if_complete(term) is not None:
            raise RuntimeError(f"semantic rejection unexpectedly completed for {name}")
        stuck[name] = term
    return stuck, diagnostics


def verify_division(
    spec: Spec, division: DivisionCase, krun: str, definition: Path
) -> str:
    """Require the LLVM division hook to abort with its exact message."""

    timeout = shutil.which("timeout")
    if timeout is None:
        raise RuntimeError("GNU timeout is required to contain the LLVM division hook abort")
    process = run(
        [timeout, "--signal=KILL", "8s", krun, "--definition", str(definition),
         "--output", "json", "-cENV=.Map", str(spec.semantic_rejected / division.program)],
        timeout=15, check=False,
    )
    if process.returncode == 0 or division.stderr not in process.stderr:
        raise RuntimeError(f"{division.program} behavior differs: {compact(process)}")
    return division.stderr


def verify_induced_diagnostic(spec: Spec, kast: KAST, kompile: str, workspace: Path) -> str | None:
    """Require the authored syntax error at its pinned source location.

    Return the normalized diagnostic when the gate pins it.
    """

    process = run(
        [kompile, str(spec.induced), "--main-module", spec.induced_module,
         "--syntax-module", spec.induced_module, "--backend", "llvm",
         "--output-definition", str(workspace / "induced-kompiled")],
        timeout=120, check=False,
    )
    match = re.search(r"Location\((\d+),(\d+),(\d+),(\d+)\)", process.stderr)
    actual = tuple(map(int, match.groups())) if match else None
    if (process.returncode == 0 or actual != spec.induced_location
            or 'Encountered: "@"' not in process.stderr or spec.induced.name not in process.stderr):
        raise RuntimeError(f"induced diagnostic differs: {compact(process)}")
    if not spec.pin_induced_diagnostic:
        return None
    if kast.normalize_diagnostic is None:
        raise GateError("a pinned induced diagnostic needs the KAST diagnostic normalizer")
    return kast.normalize_diagnostic(process.stderr)


def reference_oracle(
    spec: Spec, kast: KAST, results: Results, tools: Mapping[str, str], pins: Ledger, workspace: Path
) -> None:
    """Run the reference layers and retain every report line in gate order."""

    if set(tools) != {"kompile", "kast", "kparse", "krun"}:
        results.add("reference_oracle", "FAIL", "all four pinned K commands are required")
        return
    definition = workspace / spec.compiled_dir
    compiled_process = compile_reference(spec, tools["kompile"], definition)
    if compiled_process.returncode != 0:
        results.add("reference_compile", "FAIL", compact(compiled_process))
        return
    try:
        parsed = json.loads((definition / "parsed.json").read_text(encoding="utf-8"))
        compiled = json.loads((definition / "compiled.json").read_text(encoding="utf-8"))
        kast.verify_definition_structure(parsed, compiled)
        definition_hashes = {
            "parsed": json_sha256(kast.normalized_definition(parsed)),
            "compiled": json_sha256(kast.normalized_definition(compiled)),
        }
        compare_output(results, pins, "definition_structure", "normalized_definition_sha256",
                       definition_hashes, f"{spec.definition_detail}; hashes={definition_hashes}")

        trees, unparsed = parse_accepted(spec, kast, tools, definition, workspace)
        tree_hash, unparse_hash = aggregate(trees), aggregate(unparsed)
        compare_output(results, pins, "parse_trees", "accepted_tree_aggregate_sha256",
                       tree_hash, f"{spec.trees_detail}; aggregate={tree_hash}")
        compare_output(results, pins, "unparse_roundtrip", "unparse_aggregate_sha256",
                       unparse_hash, f"all trees round-trip exactly; aggregate={unparse_hash}")

        if kast.execute_accepted is None:
            finals, trace = execute_accepted(spec, kast, tools["krun"], definition)
        else:
            finals, trace = kast.execute_accepted(tools["krun"], definition)
        final_hash, trace_hash = aggregate(finals), aggregate(trace)
        compare_output(results, pins, "final_states", "final_state_aggregate_sha256",
                       final_hash, f"{spec.final_detail}; aggregate={final_hash}")
        compare_output(results, pins, "llvm_traces", "llvm_trace_aggregate_sha256",
                       trace_hash, f"{len(trace)} {spec.trace_detail}; aggregate={trace_hash}")

        search = spec.search
        if search is not None:
            searches, bounded = verify_search(spec, search, kast, tools["krun"], definition)
            search_hash, bounded_hash = aggregate(searches), aggregate(bounded)
            compare_output(
                results, pins, "bounded_search", "bounded_search_sha256",
                {"frontiers": search_hash, "nontermination": bounded_hash},
                f"{len(searches)} single-result search frontiers equal direct execution; "
                f"{len(search.nonterminating_depths)} {Path(search.nonterminating_program).stem} "
                f"bounds remain live; frontiers={search_hash}, nontermination={bounded_hash}",
            )

        stuck, diagnostics = verify_rejections(spec, kast, tools, definition)
        rejection_pin = spec.rejection_pin
        stuck_hash = aggregate(stuck)
        observed = {rejection_pin.stuck_key: stuck_hash}
        reported = [f"{rejection_pin.stuck_label}={stuck_hash}"]
        if rejection_pin.diagnostics_key is not None:
            diagnostic_hash = aggregate(diagnostics)
            observed[rejection_pin.diagnostics_key] = diagnostic_hash
            reported.append(f"diagnostics={diagnostic_hash}")
        if spec.division is not None:
            division_error = verify_division(spec, spec.division, tools["krun"], definition)
            observed[spec.division.pin_key] = sha256_text(division_error)
        compare_output(results, pins, "rejections", "rejection_sha256", observed,
                       f"{spec.rejection_detail}; {', '.join(reported)}")

        induced = verify_induced_diagnostic(spec, kast, tools["kompile"], workspace)
        if induced is not None:
            induced_hash = sha256_text(induced)
            compare_output(results, pins, "definition_diagnostic", "induced_diagnostic_sha256",
                           induced_hash, f"{spec.induced_detail}; hash={induced_hash}")
        else:
            results.add("definition_diagnostic", "PASS", spec.induced_detail)
    except (OSError, ValueError, RuntimeError, json.JSONDecodeError) as error:
        results.add("reference_oracle", "FAIL", str(error))


def main(spec: Spec, kast: KAST) -> int:
    """Run a strict IMP oracle and finish its ledger only after every check passes."""

    parser = argparse.ArgumentParser(description=f"{spec.label} gate")
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    arguments = parser.parse_args()
    results = Results()
    pins = Ledger(spec.pins_path, record=arguments.record)
    verify_pins(spec, results, pins)
    tools = verify_tools(results)
    with tempfile.TemporaryDirectory(prefix=f"krs-{spec.here.name}-oracle-") as temporary:
        reference_oracle(spec, kast, results, tools, pins, Path(temporary))
    if results.failed:
        print(f"\n{spec.label} FAILED")
        return 1
    pins.finish(spec.label)
    print(f"\n{spec.label} PASSED")
    return 0
