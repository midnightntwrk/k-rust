"""Manifest-driven parser, execution, and search differential oracle.

This runner consumes the IMP-owned expression corpus and the existing
IMP state, IMP control flow, and IMP static semantics corpus paths. It does not copy their inputs or import
their verifiers.

Every `kast` and `krun` invocation of both routes goes through one reference
snapshot (`support.reference`): a default run replays the cached Java K
results its pin names, and a cache miss or `--refresh-reference` runs Java K
live. The KRS normalization and comparison of those results always runs live.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from json import dumps as json_dumps
from pathlib import Path
import re
import subprocess
from typing import Any, Callable, Mapping, Sequence

from support import GateError, krs_gate
from support.hashing import json_sha256
from support.parallel import settle_all, worker_count
from support.process import compact
from support.reference import Snapshot, reduce_kore_exec_log
from support.tools import executable, z3_environment


@dataclass(frozen=True)
class Route:
    definition: Path
    term_policy: Mapping[str, Any]
    failure_definition: Path | None = None


@dataclass(frozen=True)
class ParseCase:
    name: str
    path: Path
    sort: str
    reference_module: str
    actual_module: str
    # Every entry is one complete, case-named pair of stripped outputs; no
    # token or whitespace normalization is applied.
    allowed_unparse_pair: tuple[str, str] | None = None


@dataclass(frozen=True)
class ExecutionCase:
    name: str
    path: Path
    configurations: tuple[str, ...] = ("ENV=.Map",)
    depths: tuple[int, ...] = ()
    search_depths: tuple[int, ...] = ()
    run_to_completion: bool = True
    # An exact manifest-derived program replaces ``path`` at execution time.
    # This is used only to embed expression cases in the shared Stmt shell.
    input_text: str | None = None


@dataclass(frozen=True)
class RejectionCase:
    name: str
    path: Path
    sort: str
    reference_module: str
    actual_module: str
    expected_class: str
    expected_range: tuple[int, int, int, int]


@dataclass(frozen=True)
class FailureCase:
    name: str
    path: Path
    configurations: tuple[str, ...] = ("ENV=.Map",)
    expected_class: str = "hook"
    expected_fragment: str = ""


@dataclass(frozen=True)
class BehaviorPlan:
    parse_cases: tuple[ParseCase, ...]
    execution_cases: tuple[ExecutionCase, ...]
    rejection_cases: tuple[RejectionCase, ...]
    failure_cases: tuple[FailureCase, ...] = ()
    timeout_seconds: int = 60

    def __post_init__(self) -> None:
        if self.timeout_seconds <= 0:
            raise GateError("timeout_seconds must be positive")
        for category in (
            self.parse_cases,
            self.execution_cases,
            self.rejection_cases,
            self.failure_cases,
        ):
            names = [case.name for case in category]
            duplicates = sorted(name for name in set(names) if names.count(name) > 1)
            if duplicates:
                raise GateError(f"duplicate corpus case names: {duplicates}")
        for case in self.execution_cases:
            if any(depth < 0 for depth in (*case.depths, *case.search_depths)):
                raise GateError(f"negative depth in {case.name}")
            if not case.run_to_completion and not (case.depths or case.search_depths):
                raise GateError(f"bounded-only case {case.name} has no bounds")
        for case in self.rejection_cases:
            if case.expected_class not in {"scanner", "parser"}:
                raise GateError(f"invalid rejection class for {case.name}")
        for case in self.failure_cases:
            if not case.expected_fragment:
                raise GateError(f"failure case {case.name} needs an exact diagnostic fragment")


@dataclass(frozen=True)
class BehaviorSummary:
    parse_count: int
    execution_count: int
    depth_state_count: int
    search_count: int
    rejection_count: int
    failure_count: int
    evidence_sha256: str
    evidence: Mapping[str, Any] | None = None
    """The normalized Java evidence of the actual route, which the native-run step compares with."""


@dataclass(frozen=True)
class NativeSummary:
    execution_count: int
    depth_state_count: int
    search_count: int
    pretty_count: int
    program_count: int
    evidence_sha256: str
    reports: Mapping[str, Mapping[str, Any]]
    """The `krs-exec/1` run report of every complete execution case, by case name."""


def _without_address_space_limit(live: bool) -> tuple[str, ...]:
    """The wrapper that permits the LLVM runtime's sparse semispace without lifting RAM limits.

    A live run requires `prlimit`; replay starts no process.
    """

    if live:
        executable("prlimit")
    return ("prlimit", "--as=unlimited", "--")


def _parse(
    k: Snapshot, label: str, route: Route, module: str, sort: str, path: Path, timeout: int
) -> subprocess.CompletedProcess[str]:
    return k.run(
        label,
        "kast",
        [
            "--definition",
            str(route.definition),
            "--module",
            module,
            "--sort",
            sort,
            "--output",
            "json",
            str(path),
        ],
        timeout=timeout,
    )


def _unparse(
    k: Snapshot, label: str, route: Route, module: str, sort: str, path: Path, timeout: int
) -> subprocess.CompletedProcess[str]:
    return k.run(
        label,
        "kast",
        [
            "--definition",
            str(route.definition),
            "--module",
            module,
            "--sort",
            sort,
            "--output",
            "program",
            str(path),
        ],
        timeout=timeout,
    )


def _execute(
    k: Snapshot,
    label: str,
    route: Route,
    path: Path,
    configurations: Sequence[str],
    timeout: int,
    *,
    depth: int | None = None,
    search: bool = False,
    kill_after: int | None = None,
    unlimited_address_space: bool = False,
    output: str = "json",
) -> subprocess.CompletedProcess[str]:
    # krun parses with the syntax/main modules frozen into the compiled
    # definition; unlike kast, it has no --module option.
    command = ["--definition", str(route.definition)]
    if search:
        command.append("--search")
    if depth is not None:
        command.extend(["--depth", str(depth)])
    command.extend(["--output", output])
    command.extend(f"-c{configuration}" for configuration in configurations)
    command.append(str(path))
    prefix: tuple[str, ...] = ()
    if unlimited_address_space:
        # The pinned LLVM runtime reserves a sparse 2 TiB region for two
        # aligned 1 TiB semispaces. RLIMIT_AS measures that reservation, not
        # resident memory, so only this LLVM route may restore the inherited
        # unlimited soft address-space limit.
        prefix = _without_address_space_limit(k.live)
    if kill_after is not None:
        prefix = ("timeout", "--signal=KILL", f"{kill_after}s", *prefix)
        timeout = kill_after + 7
    return k.run(
        label, "krun", command, timeout=timeout, prefix=prefix, streams={"stderr": reduce_kore_exec_log},
    )


def _normalized_output(
    session: krs_gate.Session, process: subprocess.CompletedProcess[str],
    policy: Mapping[str, Any], name: str,
) -> Any:
    if process.returncode != 0:
        raise GateError(f"{name} failed: {compact(process)}")
    return session.kast_normalize("behavior", text=process.stdout, allow_prefix=True, policy=policy)


def _diagnostic_class(stderr: str) -> str:
    text = stderr.lower()
    # A concrete backend hook abort can make the wrapper's subsequent KORE
    # read fail with a secondary parse error. The exact hook marker or
    # division-by-zero message identifies the primary failure unambiguously.
    if "[hook_" in text or "division by zero" in text or "divide by zero" in text:
        return "hook"
    classes = [
        name
        for name, fragments in {
            "scanner": ("scanner error", "unexpected character sequence"),
            "parser": ("parse error", "unexpected token", "unexpected end of file"),
            "backend": ("backend", "unsupported"),
        }.items()
        if any(fragment in text for fragment in fragments)
    ]
    if len(classes) != 1:
        raise GateError(f"diagnostic has unknown or ambiguous class: {classes}")
    return classes[0]


def _diagnostic_range(stderr: str) -> tuple[int, int, int, int]:
    matches = re.findall(r"Location\((\d+),(\d+),(\d+),(\d+)\)", stderr)
    unique = {tuple(map(int, match)) for match in matches}
    if len(unique) != 1:
        raise GateError(f"diagnostic has {len(unique)} distinct source ranges")
    return next(iter(unique))


def compare_behavior(
    *,
    k: Snapshot,
    workspace: Path,
    gate: Path,
    reference: Route,
    actual: Route,
    plan: BehaviorPlan,
) -> BehaviorSummary:
    """Run the complete checked corpus against both source definitions.

    `k` replays or refreshes the `kast` and `krun` invocations; `workspace` is
    a new directory inside the snapshot's workspace for the generated
    execution and reparse inputs, so their paths are stored as placeholders.
    Every frontend and backend invocation of the plan is independent of every
    other case, so all of them run in one pool bounded by
    ``KRS_IMP_ORACLE_WORKERS``. The comparison then walks the plan serially in
    manifest order, so the evidence and the first reported difference do not
    depend on scheduling.
    """

    worker_limit = worker_count("KRS_IMP_ORACLE_WORKERS", 4)
    timeout = plan.timeout_seconds
    sides = ((reference, "reference"), (actual, "actual"))

    workspace.mkdir(parents=True, exist_ok=False)
    jobs: list[Callable[[], Any]] = []

    def job(call: Callable[[], Any]) -> int:
        jobs.append(call)
        return len(jobs) - 1

    def parse_chain(case: ParseCase) -> dict[str, Any]:
        # Each frontend's unparse output is reparsed by that same frontend;
        # the reparse depends only on this case's own unparse.
        modules = (case.reference_module, case.actual_module)
        parsed = [
            _parse(k, f"kast/{side}/{case.name}", route, module, case.sort, case.path, timeout)
            for (route, side), module in zip(sides, modules)
        ]
        unparsed = [
            _unparse(k, f"kast-unparse/{side}/{case.name}", route, module, case.sort, case.path, timeout)
            for (route, side), module in zip(sides, modules)
        ]
        reparsed = None
        if all(process.returncode == 0 for process in unparsed):
            reparsed = []
            for index, ((route, side), module, process) in enumerate(
                zip(sides, modules, unparsed)
            ):
                path = workspace / f"{index}-{case.name}"
                path.write_text(process.stdout, encoding="utf-8")
                reparsed.append(
                    _parse(k, f"kast-reparse/{side}/{case.name}", route, module, case.sort, path, timeout)
                )
        return {"parsed": parsed, "unparsed": unparsed, "reparsed": reparsed}

    parse_jobs = [job(lambda case=case: parse_chain(case)) for case in plan.parse_cases]

    execution_jobs = []
    for case in plan.execution_cases:
        execution_path = case.path
        if case.input_text is not None:
            execution_path = workspace / f"execution-{case.name}.imp"
            execution_path.write_text(case.input_text, encoding="utf-8")

        def execute(
            label: str, route: Route, path: Path = execution_path, case: ExecutionCase = case, **options: Any
        ):
            return lambda: _execute(k, label, route, path, case.configurations, timeout, **options)

        execution_jobs.append({
            "full": [job(execute(f"krun/{side}/{case.name}", route)) for route, side in sides]
            if case.run_to_completion else None,
            # `krun --output pretty` on the actual route, which `krs run` prints identically (KF-017).
            "pretty": job(execute(f"krun-pretty/actual/{case.name}", actual, output="pretty"))
            if case.run_to_completion else None,
            "depths": [
                [
                    job(execute(f"krun-depth/{side}/{case.name}@{depth:03d}", route, depth=depth))
                    for route, side in sides
                ]
                for depth in case.depths
            ],
            "searches": [
                [
                    job(execute(
                        f"krun-search/{side}/{case.name}@{depth:03d}", route, depth=depth, search=True,
                    ))
                    for route, side in sides
                ]
                for depth in case.search_depths
            ],
        })

    rejection_jobs = [
        [
            job(lambda route=route, side=side, module=module, case=case: _parse(
                k, f"kast-rejected/{side}/{case.name}", route, module, case.sort, case.path, timeout
            ))
            for (route, side), module in zip(sides, (case.reference_module, case.actual_module))
        ]
        for case in plan.rejection_cases
    ]

    failure_jobs = [
        [
            job(lambda route=route, side=side, case=case: _execute(
                k,
                f"krun-failure/{side}/{case.name}",
                Route(route.failure_definition or route.definition, route.term_policy),
                case.path,
                case.configurations,
                timeout,
                kill_after=8,
                unlimited_address_space=True,
            ))
            for route, side in sides
        ]
        for case in plan.failure_cases
    ]

    results = settle_all(jobs, worker_limit)

    with krs_gate.Session(gate, environment=z3_environment()) as session:
        evidence: dict[str, Any] = {
            "parse": {}, "execution": {}, "search": {}, "rejection": {}, "failure": {}, "pretty": {},
        }
        depth_count = 0

        for case, index in zip(plan.parse_cases, parse_jobs):
            chain = results[index].get()
            left, right = chain["parsed"]
            left_term = _normalized_output(session, left, reference.term_policy, f"reference parse {case.name}")
            right_term = _normalized_output(session, right, actual.term_policy, f"actual parse {case.name}")
            if left_term != right_term:
                raise GateError(f"parse tree differs for {case.name}")

            unparsed_left, unparsed_right = chain["unparsed"]
            if unparsed_left.returncode != 0 or unparsed_right.returncode != 0:
                raise GateError(f"unparse failed for {case.name}")
            pair = (unparsed_left.stdout.strip(), unparsed_right.stdout.strip())
            if pair[0] != pair[1] and pair != case.allowed_unparse_pair:
                raise GateError(f"unparse output differs for {case.name}: {pair!r}")

            # Each frontend's output must reparse to its original term unless the pin permits a parser/unparser mismatch.
            reparsed = [
                _normalized_output(session, process, route.term_policy, f"reparse {case.name}")
                for (route, _), process in zip(sides, chain["reparsed"])
            ]
            if case.allowed_unparse_pair is None and reparsed != [left_term, right_term]:
                raise GateError(f"parse/unparse/parse changed {case.name}")
            evidence["parse"][case.name] = {"term": left_term, "unparse": pair}

        for case, indices in zip(plan.execution_cases, execution_jobs):
            if indices["full"] is not None:
                full = [
                    _normalized_output(session, results[index].get(), route.term_policy, f"{side} execution {case.name}")
                    for (route, side), index in zip(sides, indices["full"])
                ]
                if full[0] != full[1]:
                    raise GateError(f"final state differs for {case.name}")
                evidence["execution"][case.name] = {"term": full[0]}
                pretty = results[indices["pretty"]].get()
                if pretty.returncode != 0:
                    raise GateError(f"krun --output pretty failed for {case.name}: {compact(pretty)}")
                evidence["pretty"][case.name] = pretty.stdout

            for depth, pair_indices in zip(case.depths, indices["depths"]):
                states = [
                    _normalized_output(session, results[index].get(), route.term_policy, f"{case.name}@{depth}")
                    for (route, _), index in zip(sides, pair_indices)
                ]
                if states[0] != states[1]:
                    raise GateError(f"depth state differs for {case.name}@{depth}")
                evidence["execution"][f"{case.name}@{depth:03d}"] = states[0]
                depth_count += 1

            for depth, pair_indices in zip(case.search_depths, indices["searches"]):
                searches = [
                    session.kast_frontier("search_set", _normalized_output(session,
                        results[index].get(), route.term_policy, f"search {case.name}@{depth}"
                    ))
                    for (route, _), index in zip(sides, pair_indices)
                ]
                if searches[0] != searches[1]:
                    raise GateError(f"search set differs for {case.name}@{depth}")
                evidence["search"][f"{case.name}@{depth:03d}"] = searches[0]

        for case, indices in zip(plan.rejection_cases, rejection_jobs):
            observed = []
            for index in indices:
                process = results[index].get()
                if process.returncode == 0:
                    raise GateError(f"rejected input parsed successfully: {case.name}")
                observed.append((_diagnostic_class(process.stderr), _diagnostic_range(process.stderr)))
            expected = (case.expected_class, case.expected_range)
            if observed != [expected, expected]:
                raise GateError(f"rejection differs for {case.name}: {observed}")
            evidence["rejection"][case.name] = expected

        for case, indices in zip(plan.failure_cases, failure_jobs):
            observed = []
            for (_, side), index in zip(sides, indices):
                process = results[index].get()
                if process.returncode == 0:
                    raise GateError(
                        f"{side} failure input completed successfully: {case.name}"
                    )
                if case.expected_fragment not in process.stderr:
                    raise GateError(
                        f"failure diagnostic fragment differs for {case.name}: {compact(process)}"
                    )
                observed.append(_diagnostic_class(process.stderr))
            if observed != [case.expected_class, case.expected_class]:
                raise GateError(f"failure class differs for {case.name}: {observed}")
            evidence["failure"][case.name] = {
                "class": case.expected_class,
                "fragment": case.expected_fragment,
            }

        return BehaviorSummary(
            parse_count=len(plan.parse_cases),
            execution_count=len(plan.execution_cases),
            depth_state_count=depth_count,
            search_count=sum(len(case.search_depths) for case in plan.execution_cases),
            rejection_count=len(plan.rejection_cases),
            failure_count=len(plan.failure_cases),
            evidence_sha256=json_sha256(evidence),
            evidence=evidence,
        )


def configuration_variables(configurations: Sequence[str]) -> dict[str, str]:
    """The `-c NAME=TEXT` bindings of krun-style `NAME=TEXT` configuration arguments."""

    variables: dict[str, str] = {}
    for configuration in configurations:
        name, separator, text = configuration.partition("=")
        if not separator or not name or name in variables:
            raise GateError(f"invalid configuration argument {configuration!r}")
        variables[name] = text
    return variables


def execution_input(case: ExecutionCase) -> str:
    """The program text one execution case binds to `$PGM`."""

    return case.input_text if case.input_text is not None else case.path.read_text(encoding="utf-8")


def _difference(native: Any, java: Any) -> str:
    """Both normalized results, abbreviated, for a native-versus-krun mismatch."""

    def text(value: Any) -> str:
        spelled = json_dumps(value)
        return spelled if len(spelled) <= 1500 else f"{spelled[:1500]}..."

    return f"native={text(native)}; krun={text(java)}"


def _native_search_set(
    session: krs_gate.Session, report: Mapping[str, Any], policy: Mapping[str, Any],
) -> list[str]:
    """The comparable set of normalized solution states, as `kast.frontier search_set` spells krun's."""

    values: set[str] = set()
    for solution in report["solutions"]:
        normalized = session.kast_normalize("behavior", solution["state"], policy=policy)
        values.update(session.kast_frontier("search_set", normalized))
    return _comparable_set(session, values)


def _comparable_set(session: krs_gate.Session, values: Any) -> list[str]:
    """A `search_set` of solution states with collections canonicalized by the gate, as canonical JSON."""

    return sorted({
        json_dumps(
            session.kast_inspect("collections", session.kast_inspect("search_solution", json.loads(value))),
            sort_keys=True,
        )
        for value in values
    })


def compare_native(
    *,
    gate: Path,
    definition_ir: Path,
    module: str,
    plan: BehaviorPlan,
    policy: Mapping[str, Any],
    evidence: Mapping[str, Any],
    divergences: Mapping[str, str],
) -> NativeSummary:
    """Run every execution case through `krs-exec` and require krun's normalized results.

    One gate session loads the actual Definition IR and runs the `krs run` and
    `krs search` code paths (`exec.run`, `exec.search`): a complete execution
    and each depth state with strategy `any`, and each bounded search as a set.
    Each result is normalized with the actual route's term policy and must
    equal the Java evidence `compare_behavior` returned for the same case.
    Failure cases stay Java-only: they exercise the LLVM backend's hook abort.

    Builtin collections are canonicalized on both sides by the gate's
    `collections` inspection, because the two backends associate them
    differently.

    Grammar-directed printing (KF-017) is compared byte for byte: each complete
    execution's final state as `krs run` prints it must equal `krun --output
    pretty` on the actual route, and each accepted parse case as `krs parse
    --output program` prints it must equal the actual route's `kast --module
    <main> --output program` (stripped, as the unparse pair is pinned), which
    reverses the main module's aliases (the `zeroAlias` pairs).

    `divergences` names the reviewed known divergences. `depth-zero`: LLVM
    `krun --depth 0` prints the unevaluated initial-configuration function
    application, while k-rust evaluates it before it counts steps; each
    depth-zero state must show exactly that difference (krun's root label is
    the divergence's pinned `krun_root`, and `krs run` is depth-bound after
    zero steps), so a change on either side fails. It is upstream
    k-rust/depth-zero-initial-evaluation (reviewed, not a request).
    """

    native: dict[str, Any] = {"execution": {}, "search": {}, "pretty": {}, "program": {}}
    reports: dict[str, Mapping[str, Any]] = {}
    depth_count = 0
    search_count = 0
    with krs_gate.Session(gate, environment=z3_environment()) as session:
        session.load(definition_ir, module)
        for case in plan.parse_cases:
            printed = session.term_unparse(
                "program", program=case.path.read_text(encoding="utf-8"),
                program_name=case.path.name, sort=case.sort,
            )
            if printed["warnings"]:
                raise GateError(f"krs parse --output program warned for {case.name}: {printed['warnings']}")
            java = evidence["parse"][case.name]["unparse"][1]
            if printed["text"].strip() != java:
                raise GateError(
                    f"krs parse --output program differs from kast --output program for {case.name}: "
                    f"native={printed['text']!r}; kast={java!r}"
                )
            native["program"][case.name] = printed["text"]
        for case in plan.execution_cases:
            inputs = {
                "program": execution_input(case),
                "program_name": case.path.name,
                "variables": configuration_variables(case.configurations),
            }
            if case.run_to_completion:
                report = dict(session.exec_run(**inputs, print_style="pretty"))
                printed = report.pop("printed")
                if printed["warnings"]:
                    raise GateError(f"krs run printed {case.name} with warnings: {printed['warnings']}")
                java_pretty = evidence["pretty"][case.name]
                if printed["text"] + "\n" != java_pretty:
                    raise GateError(
                        f"krs run output differs from krun --output pretty for {case.name}: "
                        f"native={printed['text']!r}; krun={java_pretty!r}"
                    )
                native["pretty"][case.name] = printed["text"]
                term = session.kast_inspect(
                    "collections", session.kast_normalize("behavior", report["state"], policy=policy)
                )
                java = session.kast_inspect("collections", evidence["execution"][case.name]["term"])
                if term != java:
                    raise GateError(
                        f"krs run final state differs from krun for {case.name}: " + _difference(term, java)
                    )
                if report["halt"] != "stuck":
                    raise GateError(f"krs run of {case.name} halted {report['halt']}, not stuck")
                native["execution"][case.name] = {"halt": report["halt"], "steps": report["steps"]}
                reports[case.name] = report
            for depth in case.depths:
                key = f"{case.name}@{depth:03d}"
                report = session.exec_run(**inputs, depth=depth)
                if depth == 0 and "depth-zero" in divergences:
                    java_root = session.kast_inspect("root_label", evidence["execution"][key])
                    expected_root = divergences["depth-zero"]["krun_root"]
                    if java_root != expected_root or report["halt"] != "depth-bound" or report["steps"] != 0:
                        raise GateError(
                            f"the depth-zero known divergence no longer describes {case.name}: "
                            f"krun root {java_root!r}, krs run {report['halt']} after {report['steps']} steps"
                        )
                    native["execution"][key] = {"halt": report["halt"], "steps": 0, "divergence": "depth-zero"}
                    depth_count += 1
                    continue
                term = session.kast_inspect(
                    "collections", session.kast_normalize("behavior", report["state"], policy=policy)
                )
                java = session.kast_inspect("collections", evidence["execution"][key])
                if term != java:
                    raise GateError(
                        f"krs run --depth {depth} state differs from krun for {case.name}: "
                        + _difference(term, java)
                    )
                native["execution"][key] = {"halt": report["halt"], "steps": report["steps"]}
                depth_count += 1
            for depth in case.search_depths:
                key = f"{case.name}@{depth:03d}"
                report = session.exec_search(**inputs, depth=depth)
                states = _native_search_set(session, report, policy)
                java_states = _comparable_set(session, evidence["search"][key])
                if states != java_states:
                    raise GateError(
                        f"krs search --depth {depth} set differs from krun --search for {case.name}: "
                        + _difference(states, java_states)
                    )
                native["search"][key] = {"complete": report["complete"], "solutions": len(states)}
                search_count += 1
    return NativeSummary(
        execution_count=len(native["execution"]) - depth_count,
        depth_state_count=depth_count,
        search_count=search_count,
        pretty_count=len(native["pretty"]),
        program_count=len(native["program"]),
        evidence_sha256=json_sha256(native),
        reports=reports,
    )


def term_policies(raw: Mapping[str, Any]) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    """Select the two pin policy tables for native validation and normalization."""

    policies = raw.get("term_policy")
    if not isinstance(policies, dict) or set(policies) != {"reference", "actual"}:
        raise GateError("behavior.term_policy must name exactly reference and actual")
    return policies["reference"], policies["actual"]


def plan_from_manifest(
    root: Path, manifest: Mapping[str, Any], pins: Mapping[str, Any]
) -> BehaviorPlan:
    """Expand the exact schema-2 root manifest into the complete IMP plan."""

    if manifest.get("schema") != 2:
        raise GateError("behavior manifest is not schema 2")
    routes = manifest.get("routes")
    parse = manifest.get("parse")
    execution = manifest.get("execution")
    search = manifest.get("search")
    if not all(isinstance(value, dict) for value in (routes, parse, execution, search)):
        raise GateError("behavior manifest sections are missing")
    reference_module = routes["reference"].get("syntax_module")
    actual_module = routes["actual"].get("syntax_module")
    if not isinstance(reference_module, str) or not isinstance(actual_module, str):
        raise GateError("behavior routes lack exact syntax modules")

    allowed = pins.get("allowed_unparse_pairs", {})
    if not isinstance(allowed, dict):
        raise GateError("allowed_unparse_pairs is not an object")
    parse_cases: list[ParseCase] = []
    accepted = parse.get("accepted")
    if not isinstance(accepted, list):
        raise GateError("parse.accepted is not an array")
    for group in accepted:
        if not isinstance(group, dict) or set(group) != {"root", "glob", "sort", "count"}:
            raise GateError("accepted parse group has an unknown shape")
        paths = sorted((root / group["root"]).glob(group["glob"]))
        if len(paths) != group["count"] or any(not path.is_file() for path in paths):
            raise GateError(f"accepted parse group count differs: {group['root']}")
        for path in paths:
            pair = allowed.get(path.name)
            if pair is not None and (
                not isinstance(pair, list) or len(pair) != 2
                or not all(isinstance(child, str) for child in pair)
            ):
                raise GateError(f"invalid allowed unparse pair for {path.name}")
            parse_cases.append(ParseCase(
                name=path.name, path=path, sort=group["sort"],
                reference_module=reference_module, actual_module=actual_module,
                allowed_unparse_pair=tuple(pair) if pair is not None else None,
            ))
    if set(allowed) - {case.name for case in parse_cases}:
        raise GateError("allowed unparse pair names an unknown accepted case")

    rejection_cases: list[RejectionCase] = []
    rejected = parse.get("rejected")
    if not isinstance(rejected, list):
        raise GateError("parse.rejected is not an array")
    for entry in rejected:
        if not isinstance(entry, dict) or set(entry) != {"path", "sort", "class", "range"}:
            raise GateError("syntax rejection has an unknown shape")
        coordinates = entry["range"]
        if not isinstance(coordinates, list) or len(coordinates) != 4:
            raise GateError("syntax rejection range is not four coordinates")
        path = root / entry["path"]
        rejection_cases.append(RejectionCase(
            name=path.name, path=path, sort=entry["sort"],
            reference_module=reference_module, actual_module=actual_module,
            expected_class=entry["class"], expected_range=tuple(coordinates),
        ))

    execution_cases: list[ExecutionCase] = []
    wrapper = execution.get("expression_wrapper")
    if not isinstance(wrapper, str) or wrapper.count("{expression}") != 1:
        raise GateError("expression wrapper must contain one {expression} field")
    for category in ("expression_accepted_root", "expression_stuck_root"):
        directory = root / execution[category]
        expected_count = 9 if category == "expression_accepted_root" else 2
        paths = sorted(directory.glob("*.expr"))
        if len(paths) != expected_count:
            raise GateError(f"expression execution count differs: {category}")
        for path in paths:
            expression = path.read_text(encoding="utf-8").strip()
            execution_cases.append(ExecutionCase(
                name=f"expression-{path.name}", path=path,
                input_text=wrapper.format(expression=expression),
            ))

    for level in ("imp-state", "imp-control-flow"):
        entries = execution.get(level)
        if not isinstance(entries, dict):
            raise GateError(f"execution.{level} is not an object")
        for relative, raw in entries.items():
            if level == "imp-state":
                if not isinstance(raw, dict) or set(raw) != {"environment", "steps"}:
                    raise GateError(f"IMP state execution case has an unknown shape: {relative}")
                environment, steps = raw["environment"], raw["steps"]
            else:
                environment, steps = ".Map", raw
            if not isinstance(environment, str) or not isinstance(steps, int) or steps < 0:
                raise GateError(f"invalid execution expectation: {relative}")
            finite = search.get("finite", {}).get(relative, [])
            if not isinstance(finite, list) or not all(isinstance(value, int) for value in finite):
                raise GateError(f"invalid finite search depths: {relative}")
            path = root / relative
            execution_cases.append(ExecutionCase(
                name=path.name, path=path, configurations=(f"ENV={environment}",),
                depths=tuple(range(steps + 1)), search_depths=tuple(finite),
            ))

    bounded = execution.get("bounded_live")
    bounded_search = search.get("bounded_live")
    if not isinstance(bounded, dict) or not isinstance(bounded_search, dict) or bounded.get("path") != bounded_search.get("path"):
        raise GateError("bounded-live execution/search paths differ")
    execution_cases.append(ExecutionCase(
        name="infinite-loop.imp", path=root / bounded["path"],
        depths=tuple(bounded["depths"]), search_depths=tuple(bounded_search["depths"]),
        run_to_completion=False,
    ))

    stuck = execution.get("stuck")
    if not isinstance(stuck, list) or len(stuck) != 5:
        raise GateError("expected five Stmt stuck cases")
    for relative in stuck:
        path = root / relative
        execution_cases.append(ExecutionCase(
            name=f"stuck-{path.name}", path=path,
        ))
    static = root / execution["static"]
    execution_cases.append(ExecutionCase(name="static-evaluation.imp", path=static))

    failures = manifest.get("failures")
    if not isinstance(failures, list) or len(failures) != 1:
        raise GateError("expected one exact failure case")
    failure_cases = tuple(FailureCase(
        name=entry["name"], path=root / entry["path"],
        expected_class=entry["class"], expected_fragment=entry["fragment"],
    ) for entry in failures)

    plan = BehaviorPlan(
        parse_cases=tuple(parse_cases), execution_cases=tuple(execution_cases),
        rejection_cases=tuple(rejection_cases), failure_cases=failure_cases,
        timeout_seconds=int(pins.get("timeout_seconds", 60)),
    )
    depth_count = sum(len(case.depths) for case in plan.execution_cases)
    search_count = sum(len(case.search_depths) for case in plan.execution_cases)
    declared_depths = execution.get("depth_state_counts", {})
    if depth_count != 246 or declared_depths.get("total") != 246:
        raise GateError(f"expected 246 depth states, constructed {depth_count}")
    if search_count != 16 or search.get("frontier_count") != 16:
        raise GateError(f"expected 16 search frontiers, constructed {search_count}")
    if len(plan.parse_cases) != 23 or len(plan.rejection_cases) != 8:
        raise GateError("parse/rejection corpus coverage differs")
    return plan
