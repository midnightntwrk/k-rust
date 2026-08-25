"""Manifest-driven parser, execution, and search differential oracle.

This runner consumes the existing M3A--M3D corpus paths; it does not copy
their inputs or mutate their module constants.  Frozen verifier modules are
loaded only after their exact reviewed hashes have been checked.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
from types import ModuleType
from typing import Any, Mapping, Sequence

try:
    from .source_definition import NODE_FIELDS, canonical, digest
except ImportError:  # Direct loading by tests/m4/verify.py.
    from source_definition import NODE_FIELDS, canonical, digest


FROZEN_HELPER_SHA256: Mapping[str, str] = {
    "m3a": "8cf21899e30a9a6f41e13b4310989ee535314907954e50df9c9f325bee6348f9",
    "m3b": "08401de91efba5c39456e094295643b36504a123801c6db5d421667b5762ea05",
    "m3c": "9ef82c970a37128ac7b445fae30ee99590d56ae8a8f66190cf62afbcd4e1358b",
    "m3d": "2ed14f41b39cf95fdfd132d1fa675c3d550375c75499d78711a2c901d023bc9f",
}


class BehaviorError(RuntimeError):
    """Behavioral evidence is unavailable, malformed, or different."""


@dataclass(frozen=True)
class TermPolicy:
    label_map: Mapping[str, str] = field(default_factory=dict)
    identity_labels: frozenset[str] = frozenset()
    sort_map: Mapping[str, str] = field(default_factory=dict)
    identity_sorts: frozenset[str] = frozenset()


@dataclass(frozen=True)
class Route:
    definition: Path
    term_policy: TermPolicy
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
            raise BehaviorError("timeout_seconds must be positive")
        for category in (
            self.parse_cases,
            self.execution_cases,
            self.rejection_cases,
            self.failure_cases,
        ):
            names = [case.name for case in category]
            duplicates = sorted(name for name in set(names) if names.count(name) > 1)
            if duplicates:
                raise BehaviorError(f"duplicate corpus case names: {duplicates}")
        for case in self.execution_cases:
            if any(depth < 0 for depth in (*case.depths, *case.search_depths)):
                raise BehaviorError(f"negative depth in {case.name}")
            if not case.run_to_completion and not (case.depths or case.search_depths):
                raise BehaviorError(f"bounded-only case {case.name} has no bounds")
        for case in self.rejection_cases:
            if case.expected_class not in {"scanner", "parser"}:
                raise BehaviorError(f"invalid rejection class for {case.name}")
        for case in self.failure_cases:
            if not case.expected_fragment:
                raise BehaviorError(f"failure case {case.name} needs an exact diagnostic fragment")


@dataclass(frozen=True)
class BehaviorSummary:
    parse_count: int
    execution_count: int
    depth_state_count: int
    search_count: int
    rejection_count: int
    failure_count: int
    evidence_sha256: str


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_frozen_helpers(root: Path) -> Mapping[str, ModuleType]:
    """Hash-check and import the reviewed M3 helpers without mutating them."""

    loaded: dict[str, ModuleType] = {}
    for milestone, expected in FROZEN_HELPER_SHA256.items():
        path = root / "tests" / milestone / "verify.py"
        if not path.is_file() or _sha256(path) != expected:
            actual = _sha256(path) if path.is_file() else "<missing>"
            raise BehaviorError(
                f"frozen {milestone} helper hash differs: expected={expected}, actual={actual}"
            )
        spec = importlib.util.spec_from_file_location(f"krs_m4_frozen_{milestone}", path)
        if spec is None or spec.loader is None:
            raise BehaviorError(f"cannot import frozen helper {path}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        loaded[milestone] = module
    return loaded


def run_frozen_behavior_gates(
    root: Path, *, milestones: Sequence[str] = ("m3a", "m3b", "m3c"), timeout: int = 900
) -> None:
    """Re-run prior bounded gates after checking their helper hashes.

    M3D is deliberately rejected here because its top-level verifier launches
    proofs.  The M4 proof layer consumes proof evidence through ``proofs.py``.
    """

    load_frozen_helpers(root)
    unknown = set(milestones) - {"m3a", "m3b", "m3c"}
    if unknown:
        raise BehaviorError(f"not a bounded behavior milestone: {sorted(unknown)}")
    for milestone in milestones:
        process = _run(
            [os.environ.get("PYTHON", "python3"), str(root / "tests" / milestone / "verify.py")],
            timeout=timeout,
            cwd=root,
        )
        if process.returncode != 0 or "FAIL" in process.stdout:
            raise BehaviorError(
                f"frozen {milestone} gate failed: {_compact(process)}"
            )


def _run(
    command: Sequence[str], *, timeout: int, cwd: Path | None = None
) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C", "PYTHONDONTWRITEBYTECODE": "1"})
    process = subprocess.Popen(
        list(command),
        cwd=cwd,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as error:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            stdout, stderr = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
        raise BehaviorError(
            f"command timed out after {timeout}s and its process group was terminated: {command[0]}"
        ) from error
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        raise
    return subprocess.CompletedProcess(list(command), process.returncode, stdout, stderr)


def _compact(process: subprocess.CompletedProcess[str], limit: int = 1200) -> str:
    text = "\n".join(part.strip() for part in (process.stdout, process.stderr) if part.strip())
    return text[:limit] + ("…" if len(text) > limit else "")


def _envelope(output: str) -> dict[str, Any]:
    start = output.find("{")
    if start < 0:
        raise BehaviorError("KAST output has no JSON envelope")
    try:
        value = json.loads(output[start:])
    except json.JSONDecodeError as error:
        raise BehaviorError(f"invalid KAST JSON: {error}") from error
    if (
        not isinstance(value, dict)
        or set(value) != {"format", "version", "term"}
        or value["format"] != "KAST"
        or value["version"] != 4
    ):
        raise BehaviorError("output is not exactly a KAST v4 envelope")
    return value


class _TermNormalizer:
    def __init__(self, policy: TermPolicy) -> None:
        self.policy = policy
        self.variables: dict[tuple[str, str, str], str] = {}

    def _name(self, raw: Any, mapping: Mapping[str, str], identities: frozenset[str], kind: str) -> str:
        if not isinstance(raw, str):
            raise BehaviorError(f"{kind} is not a string")
        if raw in mapping:
            return mapping[raw]
        if raw in identities:
            return raw
        raise BehaviorError(f"unknown {kind} {raw!r}")

    def visit(self, value: Any) -> Any:
        if isinstance(value, list):
            return [self.visit(child) for child in value]
        if not isinstance(value, dict):
            if isinstance(value, (str, int, bool)) or value is None:
                return value
            raise BehaviorError(f"unsupported KAST scalar {value!r}")
        kind = value.get("node")
        if kind not in {"KApply", "KLabel", "KSort", "KToken", "KVariable", "KSequence", "KRewrite"}:
            raise BehaviorError(f"unclassified behavior KAST node {kind!r}")
        fields = frozenset(value)
        if fields not in NODE_FIELDS[kind]:
            raise BehaviorError(f"unknown {kind} fields: {sorted(fields)}")
        if kind == "KVariable":
            name = value["name"]
            raw_sort = value.get("sort")
            sort = "<unsorted>"
            if raw_sort is not None:
                sort = self._name(
                    raw_sort.get("name"),
                    self.policy.sort_map,
                    self.policy.identity_sorts,
                    "sort",
                )
            variable_kind = "e" if str(name).startswith("?") else "a" if str(name).startswith("_") else "v"
            key = (str(name), variable_kind, sort)
            self.variables.setdefault(key, f"{variable_kind.upper()}{len(self.variables)}")
            result: dict[str, Any] = {"node": kind, "name": self.variables[key]}
            if raw_sort is not None:
                result["sort"] = self.visit(raw_sort)
            return result
        result = {key: self.visit(child) for key, child in value.items()}
        if kind == "KLabel":
            result["name"] = self._name(
                value["name"], self.policy.label_map, self.policy.identity_labels, "label"
            )
        elif kind == "KSort":
            result["name"] = self._name(
                value["name"], self.policy.sort_map, self.policy.identity_sorts, "sort"
            )
        elif kind in {"KApply", "KSequence"}:
            children = result["args"] if kind == "KApply" else result["items"]
            if result["arity"] != len(children):
                raise BehaviorError(f"invalid {kind} arity")
        return result


def normalize_term(term: Mapping[str, Any], policy: TermPolicy) -> Any:
    return _TermNormalizer(policy).visit(dict(term))


def _parse(
    kast: str, route: Route, module: str, sort: str, path: Path, timeout: int
) -> subprocess.CompletedProcess[str]:
    return _run(
        [
            kast,
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


def _unparse(kast: str, route: Route, module: str, sort: str, path: Path, timeout: int) -> subprocess.CompletedProcess[str]:
    return _run(
        [
            kast,
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
    krun: str,
    route: Route,
    path: Path,
    configurations: Sequence[str],
    timeout: int,
    *,
    depth: int | None = None,
    search: bool = False,
    kill_after: int | None = None,
) -> subprocess.CompletedProcess[str]:
    # krun parses with the syntax/main modules frozen into the compiled
    # definition; unlike kast, it has no --module option.
    command = [krun, "--definition", str(route.definition)]
    if search:
        command.append("--search")
    if depth is not None:
        command.extend(["--depth", str(depth)])
    command.extend(["--output", "json"])
    command.extend(f"-c{configuration}" for configuration in configurations)
    command.append(str(path))
    if kill_after is not None:
        watchdog = shutil.which("timeout")
        if watchdog is None:
            raise BehaviorError("GNU timeout is required to contain a backend hook abort")
        command = [watchdog, "--signal=KILL", f"{kill_after}s", *command]
        timeout = kill_after + 7
    return _run(command, timeout=timeout)


def _normalized_output(process: subprocess.CompletedProcess[str], policy: TermPolicy, name: str) -> Any:
    if process.returncode != 0:
        raise BehaviorError(f"{name} failed: {_compact(process)}")
    return normalize_term(_envelope(process.stdout)["term"], policy)


def _search_set(term: Any) -> list[str]:
    if (
        isinstance(term, dict)
        and term.get("node") == "KApply"
        and term.get("label", {}).get("name") == "#Or"
    ):
        values: list[Any] = []
        for child in term["args"]:
            child_values = _search_set(child)
            values.extend(json.loads(item) for item in child_values)
        return sorted({canonical(value) for value in values})
    return [canonical(term)]


def _diagnostic_class(stderr: str) -> str:
    text = stderr.lower()
    classes = [
        name
        for name, fragments in {
            "scanner": ("scanner error", "unexpected character sequence"),
            "parser": ("parse error", "unexpected token", "unexpected end of file"),
            "hook": ("hook", "division by zero", "divide by zero"),
            "backend": ("backend", "unsupported"),
        }.items()
        if any(fragment in text for fragment in fragments)
    ]
    if len(classes) != 1:
        raise BehaviorError(f"diagnostic has unknown or ambiguous class: {classes}")
    return classes[0]


def _diagnostic_range(stderr: str) -> tuple[int, int, int, int]:
    matches = re.findall(r"Location\((\d+),(\d+),(\d+),(\d+)\)", stderr)
    unique = {tuple(map(int, match)) for match in matches}
    if len(unique) != 1:
        raise BehaviorError(f"diagnostic has {len(unique)} distinct source ranges")
    return next(iter(unique))


def compare_behavior(
    *,
    kast: str,
    krun: str,
    reference: Route,
    actual: Route,
    plan: BehaviorPlan,
) -> BehaviorSummary:
    """Run the complete checked corpus against both source definitions."""

    evidence: dict[str, Any] = {"parse": {}, "execution": {}, "search": {}, "rejection": {}, "failure": {}}
    depth_count = 0
    try:
        worker_limit = int(os.environ.get("KRS_M4_ORACLE_WORKERS", "4"))
    except ValueError as error:
        raise BehaviorError("KRS_M4_ORACLE_WORKERS must be an integer") from error
    if not 1 <= worker_limit <= 8:
        raise BehaviorError("KRS_M4_ORACLE_WORKERS must be between 1 and 8")

    def parallel(function, values):
        values = list(values)
        with ThreadPoolExecutor(max_workers=min(worker_limit, len(values))) as executor:
            return list(executor.map(function, values))

    with tempfile.TemporaryDirectory(prefix="krs-m4-behavior-") as temporary:
        workspace = Path(temporary)
        for case in plan.parse_cases:
            left = _parse(kast, reference, case.reference_module, case.sort, case.path, plan.timeout_seconds)
            right = _parse(kast, actual, case.actual_module, case.sort, case.path, plan.timeout_seconds)
            left_term = _normalized_output(left, reference.term_policy, f"reference parse {case.name}")
            right_term = _normalized_output(right, actual.term_policy, f"actual parse {case.name}")
            if left_term != right_term:
                raise BehaviorError(f"parse tree differs for {case.name}")

            unparsed_left = _unparse(kast, reference, case.reference_module, case.sort, case.path, plan.timeout_seconds)
            unparsed_right = _unparse(kast, actual, case.actual_module, case.sort, case.path, plan.timeout_seconds)
            if unparsed_left.returncode != 0 or unparsed_right.returncode != 0:
                raise BehaviorError(f"unparse failed for {case.name}")
            pair = (unparsed_left.stdout.strip(), unparsed_right.stdout.strip())
            if pair[0] != pair[1] and pair != case.allowed_unparse_pair:
                raise BehaviorError(f"unparse output differs for {case.name}: {pair!r}")

            # Each frontend's output must reparse to its own original term,
            # except for an explicitly frozen parser/unparser mismatch.
            reparsed: list[Any] = []
            for index, (route, module, output) in enumerate(
                (
                    (reference, case.reference_module, unparsed_left.stdout),
                    (actual, case.actual_module, unparsed_right.stdout),
                )
            ):
                path = workspace / f"{index}-{case.name}"
                path.write_text(output, encoding="utf-8")
                process = _parse(kast, route, module, case.sort, path, plan.timeout_seconds)
                reparsed.append(_normalized_output(process, route.term_policy, f"reparse {case.name}"))
            if case.allowed_unparse_pair is None and reparsed != [left_term, right_term]:
                raise BehaviorError(f"parse/unparse/parse changed {case.name}")
            evidence["parse"][case.name] = {"term": left_term, "unparse": pair}

        for case in plan.execution_cases:
            execution_path = case.path
            if case.input_text is not None:
                execution_path = workspace / f"execution-{case.name}.imp"
                execution_path.write_text(case.input_text, encoding="utf-8")
            if case.run_to_completion:
                def complete(job):
                    route, side = job
                    process = _execute(
                        krun,
                        route,
                        execution_path,
                        case.configurations,
                        plan.timeout_seconds,
                    )
                    return _normalized_output(
                        process, route.term_policy, f"{side} execution {case.name}"
                    )
                full = parallel(complete, ((reference, "reference"), (actual, "actual")))
                if full[0] != full[1]:
                    raise BehaviorError(f"final state differs for {case.name}")
                evidence["execution"][case.name] = {"term": full[0]}

            def bounded(job):
                route, depth = job
                process = _execute(
                    krun, route, execution_path, case.configurations,
                    plan.timeout_seconds, depth=depth,
                )
                return _normalized_output(process, route.term_policy, f"{case.name}@{depth}")

            depth_jobs = [
                (route, depth) for depth in case.depths for route in (reference, actual)
            ]
            bounded_states = parallel(bounded, depth_jobs) if depth_jobs else []
            for index, depth in enumerate(case.depths):
                states = bounded_states[index * 2:index * 2 + 2]
                if states[0] != states[1]:
                    raise BehaviorError(f"depth state differs for {case.name}@{depth}")
                evidence["execution"][f"{case.name}@{depth:03d}"] = states[0]
                depth_count += 1

            def search(job):
                route, depth = job
                process = _execute(
                    krun, route, execution_path, case.configurations,
                    plan.timeout_seconds, depth=depth, search=True,
                )
                normalized = _normalized_output(
                    process, route.term_policy, f"search {case.name}@{depth}"
                )
                return _search_set(normalized)

            search_jobs = [
                (route, depth)
                for depth in case.search_depths
                for route in (reference, actual)
            ]
            search_states = parallel(search, search_jobs) if search_jobs else []
            for index, depth in enumerate(case.search_depths):
                searches = search_states[index * 2:index * 2 + 2]
                if searches[0] != searches[1]:
                    raise BehaviorError(f"search set differs for {case.name}@{depth}")
                evidence["search"][f"{case.name}@{depth:03d}"] = searches[0]

        for case in plan.rejection_cases:
            observed = []
            for route, module in (
                (reference, case.reference_module),
                (actual, case.actual_module),
            ):
                process = _parse(kast, route, module, case.sort, case.path, plan.timeout_seconds)
                if process.returncode == 0:
                    raise BehaviorError(f"rejected input parsed successfully: {case.name}")
                observed.append((_diagnostic_class(process.stderr), _diagnostic_range(process.stderr)))
            expected = (case.expected_class, case.expected_range)
            if observed != [expected, expected]:
                raise BehaviorError(f"rejection differs for {case.name}: {observed}")
            evidence["rejection"][case.name] = expected

        for case in plan.failure_cases:
            observed = []
            for route, side in ((reference, "reference"), (actual, "actual")):
                process = _execute(
                    krun,
                    Route(route.failure_definition or route.definition, route.term_policy),
                    case.path,
                    case.configurations,
                    plan.timeout_seconds,
                    kill_after=8,
                )
                if process.returncode == 0:
                    raise BehaviorError(
                        f"{side} failure input completed successfully: {case.name}"
                    )
                if case.expected_fragment not in process.stderr:
                    raise BehaviorError(
                        f"failure diagnostic fragment differs for {case.name}: {_compact(process)}"
                    )
                observed.append(_diagnostic_class(process.stderr))
            if observed != [case.expected_class, case.expected_class]:
                raise BehaviorError(f"failure class differs for {case.name}: {observed}")
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
        evidence_sha256=digest(evidence),
    )


def term_policies(raw: Mapping[str, Any]) -> tuple[TermPolicy, TermPolicy]:
    """Build both fail-closed term policies from the checked root ledger."""

    policies = raw.get("term_policy")
    if not isinstance(policies, dict) or set(policies) != {"reference", "actual"}:
        raise BehaviorError("behavior.term_policy must name exactly reference and actual")

    def build(side: str) -> TermPolicy:
        value = policies[side]
        if not isinstance(value, dict) or set(value) != {
            "label_map", "identity_labels", "sort_map", "identity_sorts"
        }:
            raise BehaviorError(f"behavior term policy has unknown shape: {side}")
        if not isinstance(value["label_map"], dict) or not isinstance(value["sort_map"], dict):
            raise BehaviorError(f"behavior term maps are not objects: {side}")
        if not isinstance(value["identity_labels"], list) or not isinstance(value["identity_sorts"], list):
            raise BehaviorError(f"behavior identity sets are not arrays: {side}")
        return TermPolicy(
            label_map=value["label_map"],
            identity_labels=frozenset(value["identity_labels"]),
            sort_map=value["sort_map"],
            identity_sorts=frozenset(value["identity_sorts"]),
        )

    return build("reference"), build("actual")


def plan_from_manifest(
    root: Path, manifest: Mapping[str, Any], pins: Mapping[str, Any]
) -> BehaviorPlan:
    """Expand the exact schema-2 root manifest into the complete M4 plan."""

    if manifest.get("schema") != 2:
        raise BehaviorError("behavior manifest is not schema 2")
    routes = manifest.get("routes")
    parse = manifest.get("parse")
    execution = manifest.get("execution")
    search = manifest.get("search")
    if not all(isinstance(value, dict) for value in (routes, parse, execution, search)):
        raise BehaviorError("behavior manifest sections are missing")
    reference_module = routes["reference"].get("syntax_module")
    actual_module = routes["actual"].get("syntax_module")
    if not isinstance(reference_module, str) or not isinstance(actual_module, str):
        raise BehaviorError("behavior routes lack exact syntax modules")

    allowed = pins.get("allowed_unparse_pairs", {})
    if not isinstance(allowed, dict):
        raise BehaviorError("allowed_unparse_pairs is not an object")
    parse_cases: list[ParseCase] = []
    accepted = parse.get("accepted")
    if not isinstance(accepted, list):
        raise BehaviorError("parse.accepted is not an array")
    for group in accepted:
        if not isinstance(group, dict) or set(group) != {"root", "glob", "sort", "count"}:
            raise BehaviorError("accepted parse group has an unknown shape")
        paths = sorted((root / group["root"]).glob(group["glob"]))
        if len(paths) != group["count"] or any(not path.is_file() for path in paths):
            raise BehaviorError(f"accepted parse group count differs: {group['root']}")
        for path in paths:
            pair = allowed.get(path.name)
            if pair is not None and (
                not isinstance(pair, list) or len(pair) != 2
                or not all(isinstance(child, str) for child in pair)
            ):
                raise BehaviorError(f"invalid allowed unparse pair for {path.name}")
            parse_cases.append(ParseCase(
                name=path.name, path=path, sort=group["sort"],
                reference_module=reference_module, actual_module=actual_module,
                allowed_unparse_pair=tuple(pair) if pair is not None else None,
            ))
    if set(allowed) - {case.name for case in parse_cases}:
        raise BehaviorError("allowed unparse pair names an unknown accepted case")

    rejection_cases: list[RejectionCase] = []
    rejected = parse.get("rejected")
    if not isinstance(rejected, list):
        raise BehaviorError("parse.rejected is not an array")
    for entry in rejected:
        if not isinstance(entry, dict) or set(entry) != {"path", "sort", "class", "range"}:
            raise BehaviorError("syntax rejection has an unknown shape")
        coordinates = entry["range"]
        if not isinstance(coordinates, list) or len(coordinates) != 4:
            raise BehaviorError("syntax rejection range is not four coordinates")
        path = root / entry["path"]
        rejection_cases.append(RejectionCase(
            name=path.name, path=path, sort=entry["sort"],
            reference_module=reference_module, actual_module=actual_module,
            expected_class=entry["class"], expected_range=tuple(coordinates),
        ))

    execution_cases: list[ExecutionCase] = []
    wrapper = execution.get("expression_wrapper")
    if not isinstance(wrapper, str) or wrapper.count("{expression}") != 1:
        raise BehaviorError("expression wrapper must contain one {expression} field")
    for category in ("expression_accepted_root", "expression_stuck_root"):
        directory = root / execution[category]
        expected_count = 9 if category == "expression_accepted_root" else 2
        paths = sorted(directory.glob("*.expr"))
        if len(paths) != expected_count:
            raise BehaviorError(f"expression execution count differs: {category}")
        for path in paths:
            expression = path.read_text(encoding="utf-8").strip()
            execution_cases.append(ExecutionCase(
                name=f"expression-{path.name}", path=path,
                input_text=wrapper.format(expression=expression),
            ))

    for level in ("m3b", "m3c"):
        entries = execution.get(level)
        if not isinstance(entries, dict):
            raise BehaviorError(f"execution.{level} is not an object")
        for relative, raw in entries.items():
            if level == "m3b":
                if not isinstance(raw, dict) or set(raw) != {"environment", "steps"}:
                    raise BehaviorError(f"M3B execution case has an unknown shape: {relative}")
                environment, steps = raw["environment"], raw["steps"]
            else:
                environment, steps = ".Map", raw
            if not isinstance(environment, str) or not isinstance(steps, int) or steps < 0:
                raise BehaviorError(f"invalid execution expectation: {relative}")
            finite = search.get("finite", {}).get(relative, [])
            if not isinstance(finite, list) or not all(isinstance(value, int) for value in finite):
                raise BehaviorError(f"invalid finite search depths: {relative}")
            path = root / relative
            execution_cases.append(ExecutionCase(
                name=path.name, path=path, configurations=(f"ENV={environment}",),
                depths=tuple(range(steps + 1)), search_depths=tuple(finite),
            ))

    bounded = execution.get("bounded_live")
    bounded_search = search.get("bounded_live")
    if not isinstance(bounded, dict) or not isinstance(bounded_search, dict) or bounded.get("path") != bounded_search.get("path"):
        raise BehaviorError("bounded-live execution/search paths differ")
    execution_cases.append(ExecutionCase(
        name="infinite-loop.imp", path=root / bounded["path"],
        depths=tuple(bounded["depths"]), search_depths=tuple(bounded_search["depths"]),
        run_to_completion=False,
    ))

    stuck = execution.get("stuck")
    if not isinstance(stuck, list) or len(stuck) != 5:
        raise BehaviorError("expected five Stmt stuck cases")
    for relative in stuck:
        path = root / relative
        execution_cases.append(ExecutionCase(
            name=f"stuck-{path.name}", path=path,
        ))
    static = root / execution["static"]
    execution_cases.append(ExecutionCase(name="static-evaluation.imp", path=static))

    failures = manifest.get("failures")
    if not isinstance(failures, list) or len(failures) != 1:
        raise BehaviorError("expected one exact failure case")
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
        raise BehaviorError(f"expected 246 depth states, constructed {depth_count}")
    if search_count != 16 or search.get("frontier_count") != 16:
        raise BehaviorError(f"expected 16 search frontiers, constructed {search_count}")
    if len(plan.parse_cases) != 23 or len(plan.rejection_cases) != 9:
        raise BehaviorError("parse/rejection corpus coverage differs")
    return plan
