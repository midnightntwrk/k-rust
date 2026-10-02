"""The gate flow the KWasm, KMIR, and KEVM semantics ports share.

Each port is a readable Rust package under `semantics/<port>/` with a corpus
and a pin ledger under `tests/<port>/`. The shared steps are: preflight over
the external checkout and the corpus, the ordinary Rust checks, repeated
expansion and emission with their output pins, native k-rust compilation and
execution, and the kompiled reference definition behind `--java-reference`.
Each corpus declares structural state expectations and report fields.
Each verifier supplies surface configuration and report wording.

`--artifacts-only` stops after the native definition: it checks every emitted
artifact against its pin and skips the behavior and proof comparisons, which
cannot find anything new while the artifacts are unchanged.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
from typing import Any, Callable, Mapping, Sequence

from support import ROOT, GateError, behavior as behavior_module, krs_gate, lsp
from support.checkouts import verify_checkout
from support.hashing import exact_directory, json_sha256, sha256_file, sha256_text
from support.kdefinition import emitted_claims, emitted_files
from support.krs import Invocation, build, fresh_deterministic_emissions
from support.lock import k_version, krs_ir_schema, msrv
from support.pins import Ledger, load_toml
from support.process import run
from support.tools import checkout_scratch, k_tool, rust_analyzer, scratch_root, z3_environment


LOCK = ROOT / "semantics/Cargo.lock"


@dataclass(frozen=True)
class Port:
    """One semantics port and the names its gate uses."""

    label: str
    """The display name, such as `KWasm`."""
    key: str
    """The lower-case name of `semantics/<key>`, `tests/<key>`, and the pin table."""
    checkout: Path
    """The pinned Runtime Verification checkout the port is qualified against."""
    descriptors: int
    lsp_probes: tuple[lsp.Probe, ...]
    lsp_diagnostic_timeout: float
    clippy_allow: tuple[str, ...] = ()
    hook_namespaces: tuple[str, ...] = ()
    """Hook namespaces the Java frontend must keep; it drops hooks outside its defaults."""

    @property
    def here(self) -> Path:
        return ROOT / "tests" / self.key

    @property
    def manifest(self) -> Path:
        return ROOT / "semantics" / self.key / "Cargo.toml"

    @property
    def source(self) -> Path:
        return ROOT / "semantics" / self.key / "src/lib.rs"

    @property
    def corpus_path(self) -> Path:
        return self.here / "corpus.toml"

    @property
    def pins_path(self) -> Path:
        return self.here / "pins.toml"

    @property
    def package(self) -> str:
        return f"krs-{self.key}-semantics"

    @property
    def module(self) -> str:
        return f"KRS-{self.key.upper()}"

    @property
    def spec_module(self) -> str:
        return f"{self.module}-SPEC"

    def target(self, role: str) -> Path:
        """A persistent Cargo target: `KRS_<PORT>_<ROLE>_TARGET`, else under checkout scratch."""

        variable = f"KRS_{self.key.upper()}_{role.upper()}_TARGET"
        default = checkout_scratch() / f"{self.key}-gate-{role}-target"
        return Path(os.environ.get(variable, os.fspath(default)))


@dataclass(frozen=True)
class Hooks:
    """The port-specific configuration and report wording."""

    description: str
    label: str
    java_help: str
    claim_count: int
    configuration_variables: behavior_module.Variables
    kore_configuration: bool = False
    summary: Callable[[Port, int, int, bool], str] | None = None
    definition_checks: Callable[[Path, Path, Mapping[str, str]], None] | None = None
    java_skips: Mapping[str, str] | None = None


def add_artifacts_only_argument(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--artifacts-only",
        action="store_true",
        help=(
            "stop after preflight, the Rust checks, and artifact determinism, with every "
            "emitted artifact compared to its pin; skip the behavior and proof comparisons"
        ),
    )


def reject_artifacts_only_conflicts(
    parser: argparse.ArgumentParser, arguments: argparse.Namespace
) -> None:
    """`--artifacts-only` cannot record pins or run the Java reference layer it skips."""

    if arguments.artifacts_only and (arguments.record or arguments.java_reference):
        parser.error("--artifacts-only cannot be combined with --record or --java-reference")


def artifacts_only_summary(port: Port) -> str:
    return (
        f"{port.descriptors} descriptors; emitted artifacts and native KORE match their pins; "
        "behavior and proof comparison layers skipped (--artifacts-only)"
    )


def preflight(port: Port, pins: Ledger, corpus: Mapping[str, Any]) -> dict[str, str]:
    """Check the input pins and return the build environment.

    Inputs are the clean external checkout at its pinned revision, its K
    release, the external files the corpus cites, and the corpus itself. Schema
    constants must agree with `Krs.lock`. KRS source is deliberately not pinned.
    """

    if pins.get("schema") != 1 or corpus.get("schema") != 1:
        raise GateError(f"{port.label} gate schema differs from 1")
    if sha256_file(port.corpus_path) != pins.get("corpus_sha256"):
        raise GateError("corpus.toml differs from its pin")
    checkout_pin = pins.table(port.key)
    verify_checkout(port.checkout, str(checkout_pin.get("commit")), label=f"{port.label} evidence")
    release = (port.checkout / "deps/k_release").read_text(encoding="utf-8").strip()
    if release != checkout_pin.get("version"):
        raise GateError(f"{port.label} K release differs: {release}")

    # The clean checkout at the pinned commit fixes every evidence file.
    evidence = corpus.get("source_evidence")
    if not isinstance(evidence, list) or not evidence:
        raise GateError("source evidence is empty")
    for relative in sorted({str(entry["path"]) for entry in evidence}):
        if not (port.checkout / relative).is_file():
            raise GateError(f"external {port.label} evidence is missing: {relative}")

    return {**z3_environment(), "CARGO_NET_OFFLINE": "true"}


def rust_gate(port: Port, environment: Mapping[str, str]) -> tuple[Path, Path]:
    """Build the CLI and native gate; check, test, lint, and format the port."""

    root_target = port.target("root")
    root_env = {**environment, "CARGO_TARGET_DIR": os.fspath(root_target)}
    krs = build(root_env, target=root_target)
    gate = krs_gate.build(root_target, environment=root_env)
    common = ["--manifest-path", port.manifest, "--locked", "--offline"]
    fixture_env = {**environment, "CARGO_TARGET_DIR": os.fspath(port.target("fixture"))}
    run(["cargo", "+stable", "check", *common, "--all-targets"], environment=fixture_env)
    run(["cargo", "+stable", "test", *common], environment=fixture_env, timeout=900)
    allow = [argument for lint in port.clippy_allow for argument in ("-A", lint)]
    run(
        ["cargo", "+stable", "clippy", *common, "--all-targets", "--", "-D", "warnings", *allow],
        environment=fixture_env,
        timeout=900,
    )
    run(["cargo", "+stable", "fmt", "--all", "--", "--check"])
    run(
        [krs, "fmt", "--check", "--manifest-path", port.manifest, port.source],
        environment=environment,
    )
    run(["cargo", f"+{msrv()}", "check", *common, "--all-targets"], environment=fixture_env, timeout=900)
    analyzer = rust_analyzer()
    lsp_env = {**environment, "PATH": os.pathsep.join([os.fspath(analyzer.parent), os.environ["PATH"]])}
    lsp.probe(
        ROOT / "semantics" / port.key,
        port.lsp_probes,
        diagnostic_timeout=port.lsp_diagnostic_timeout,
        environment=lsp_env,
        timeout=900,
    )
    return krs, gate


def artifact_gate(
    port: Port,
    workspace: Path,
    krs: Path,
    pins: Ledger,
    gate: Path,
    environment: Mapping[str, str],
) -> Path:
    """Check, expand, and emit the port fresh twice; compile the expansion independently.

    Records the expansion and emitted-artifact digests, requires a cached replay
    to equal the first fresh emission, requires the independently compiled
    expansion to emit the same syntax, configuration, and sentence identities,
    and returns the first emission directory.
    """

    invocation = Invocation(krs, port.manifest, port.package, "main")
    check = invocation.run("check", environment=environment)
    if f"{port.descriptors} descriptors" not in check.stdout:
        raise GateError(f"unexpected descriptor count: {check.stdout.strip()}")
    expansions = [invocation.run("expand", environment=environment).stdout for _ in range(2)]
    if expansions[0] != expansions[1]:
        raise GateError("readable expansion is nondeterministic")
    pins.expect("expansion_sha256", sha256_text(expansions[0]))

    expanded = workspace / "expanded"
    expanded.joinpath("src").mkdir(parents=True)
    manifest = port.manifest.read_text(encoding="utf-8").replace(
        '"../../crates/', f'"{os.fspath(ROOT / "crates")}/'
    )
    expanded.joinpath("Cargo.toml").write_text(manifest, encoding="utf-8")
    shutil.copy2(LOCK, expanded / "Cargo.lock")
    expanded.joinpath("src/lib.rs").write_text(expansions[0], encoding="utf-8")
    expanded_env = {**environment, "CARGO_TARGET_DIR": os.fspath(port.target("expanded"))}
    run(
        ["cargo", "+stable", "check", "--manifest-path", expanded / "Cargo.toml", "--locked", "--offline"],
        environment=expanded_env,
        timeout=900,
    )

    emit_a, emit_b = fresh_deterministic_emissions(invocation, workspace, environment=environment)
    for name, digest in exact_directory(emit_a, emit_b, emitted_files(emit_a, gate, environment=environment)).items():
        pins.expect(("artifact_sha256", name), digest)

    expanded_output = workspace / "expanded-emit"
    run(
        Invocation(krs, expanded / "Cargo.toml", port.package, "main").argv(
            "emit-k", "--output", expanded_output
        ),
        environment=expanded_env,
        timeout=900,
    )
    with krs_gate.Session(gate, environment=environment) as session:
        readable_shape = session.ir_query(emit_a, {"kind": "definition_shape"})
        expanded_shape = session.ir_query(expanded_output, {"kind": "definition_shape"})
        if readable_shape != expanded_shape:
            raise GateError("independently compiled expansion changed the typed definition shape")
    return emit_a


EXPECTATION_KEYS = frozenset(
    {"message", "required", "forbidden", "cells", "subsorts", "applied_operations", "applications"}
)


def definition_expectations(
    artifacts: Path,
    gate: Path,
    expectations: Path,
    environment: Mapping[str, str],
) -> None:
    """Require the query projections declared beside a port's pins.

    Python compares flat Rust query rows with expectation data.
    Nested application patterns are matched by Rust.
    """

    checks = load_toml(expectations)["check"]
    with krs_gate.Session(gate, environment=environment) as session:
        vocabulary = session.ir_query(artifacts, {"kind": "vocabulary"})
        facets = {
            name: set(vocabulary[name])
            for name in ("sorts", "production_symbols", "terminals", "rule_labels", "imports")
        }
        facets["cell_names"] = {row["name"] for row in vocabulary["cells"]}
        for check in checks:
            unknown = set(check) - EXPECTATION_KEYS
            if unknown or not isinstance(check.get("message"), str):
                raise GateError(f"{expectations}: malformed check {check!r}; unknown keys {sorted(unknown)}")
            for facet, expected in check.get("required", {}).items():
                if not set(expected) <= facets[facet]:
                    raise GateError(f"{check['message']}: missing {facet} {sorted(set(expected) - facets[facet])}")
            for facet, forbidden in check.get("forbidden", {}).items():
                if set(forbidden) & facets[facet]:
                    raise GateError(f"{check['message']}: forbidden {facet} {sorted(set(forbidden) & facets[facet])}")
            for facet in ("cells", "subsorts", "applied_operations"):
                for expected in check.get(facet, []):
                    if not any(
                        all(row.get(name) == value for name, value in expected.items())
                        for row in vocabulary[facet]
                    ):
                        raise GateError(f"{check['message']}: missing {facet} row {expected}")
            for pattern in check.get("applications", []):
                if not session.ir_query(artifacts, {"kind": "applications", **pattern})["rows"]:
                    raise GateError(f"{check['message']}: missing application {pattern}")


def native_definition(
    workspace: Path,
    artifacts: Path,
    gate: Path,
    pins: Ledger,
    environment: Mapping[str, str],
) -> str:
    """Lower the emitted Definition IR through k-rust and return its pinned KORE digest."""

    definition = workspace / "native-definition.kore"
    krs_gate.compile(gate, artifacts / "definition-ir.json", definition, environment=environment)
    digest = sha256_file(definition)
    pins.expect("native_definition_kore_sha256", digest)
    return digest


_NATIVE_SUMMARY = re.compile(r"^PASS native (\S+) behavior: (\d+) executions; sha256=([0-9a-f]{64})$")


def native_behavior(
    port: Port,
    gate: Path,
    definition_ir: Path,
    definition_kore_sha256: str,
    pins: Ledger,
    corpus: Mapping[str, Any],
    environment: Mapping[str, str],
) -> tuple[int, list[dict[str, Any]]]:
    """Execute the corpus, pin its digest, and return its ordered outcomes."""

    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    with tempfile.TemporaryDirectory(prefix=f"krs-{port.key}-outcomes-", dir=scratch_root()) as temporary:
        outcomes_path = Path(temporary) / "outcomes.json"
        result = run(
            [sys.executable, port.here / "native.py", gate, definition_ir, port.module,
             port.corpus_path, "--definition-kore-sha256", definition_kore_sha256,
             "--outcomes", outcomes_path],
            environment=environment,
            timeout=900,
        )
        outcomes = json.loads(outcomes_path.read_text(encoding="utf-8"))
    summary = _NATIVE_SUMMARY.match(result.stdout.strip())
    if (
        summary is None
        or summary.group(1) != port.label
        or int(summary.group(2)) != len(behavior)
    ):
        raise GateError(f"K-Rust behavior evidence differs: {result.stdout.strip()}")
    pins.expect("behavior_sha256", summary.group(3))
    if not isinstance(outcomes, list) or len(outcomes) != len(behavior) or any(
        not isinstance(outcome, dict) or outcome.get("id") != case.get("id")
        for outcome, case in zip(outcomes, behavior, strict=True)
    ):
        raise GateError("native outcomes differ from the ordered corpus")
    if json_sha256(outcomes) != summary.group(3):
        raise GateError("native outcome list differs from its reported digest")
    return len(behavior), outcomes


def compare_routes(
    label: str,
    native_outcomes: Sequence[Mapping[str, Any]],
    java_outcomes: Sequence[Mapping[str, Any]],
    skipped: Mapping[str, str],
) -> None:
    """Require every Java outcome to match its native peer and account for all ids."""

    native = {str(outcome["id"]): outcome for outcome in native_outcomes}
    if len(native) != len(native_outcomes):
        raise GateError(f"{label} native outcomes contain duplicate ids")
    unknown_skips = set(skipped) - set(native)
    if unknown_skips:
        raise GateError(f"{label} skipped id is absent from corpus: {sorted(unknown_skips)}")
    compared: set[str] = set()
    for outcome in java_outcomes:
        case_id = str(outcome["id"])
        if case_id not in native or case_id in compared or case_id in skipped:
            raise GateError(f"{label} unexpected or duplicate Java case id: {case_id}")
        compared.add(case_id)
        expected = native[case_id]
        if outcome != expected:
            key = next(
                key for key in dict.fromkeys([*expected, *outcome])
                if key not in expected or key not in outcome or expected[key] != outcome[key]
            )
            raise GateError(
                f"{label} case {case_id} differs at {key}: native={expected.get(key)!r}, "
                f"Java={outcome.get(key)!r}"
            )
    missing = set(native) - compared - set(skipped)
    if missing:
        raise GateError(f"{label} Java route did not compare cases: {sorted(missing)}")
    skip_text = f" ({len(skipped)} skipped: Haskell backend gaps)" if skipped else ""
    print(
        f"PASS Java reference {label} agrees with K-Rust on "
        f"{len(compared)} of {len(native)} cases{skip_text}"
    )


def reference_definition(
    port: Port,
    workspace: Path,
    artifacts: Path,
    kompile: str,
    claim_count: int,
    pins: Ledger,
    gate: Path,
    environment: Mapping[str, str],
) -> tuple[Path, Path]:
    """Kompile the emitted claim-free definition with the pinned K frontend.

    Records its normalized KORE digest and returns the kompiled directory and
    the emitted specification, whose claims are checked against `claim_count`.
    """

    emitted_claims(artifacts, port.module, claim_count, gate=gate, environment=environment)
    semantics = workspace / "definition.k"
    shutil.copy2(artifacts / "definition.k", semantics)
    spec = workspace / "spec.k"
    shutil.copy2(artifacts / "spec.k", spec)
    definition = workspace / "semantics-kompiled"
    run(
        [
            kompile, semantics, "--backend", "haskell", "--main-module", port.module,
            "--syntax-module", port.module, "--emit-json", "--output-definition", definition,
            *(["--hook-namespaces", " ".join(port.hook_namespaces)] if port.hook_namespaces else []),
        ],
        timeout=900,
    )
    pins.expect(
        "definition_kore_sha256",
        krs_gate.digest(gate, definition / "definition.kore", semantics, environment=environment),
    )
    return definition, spec


def reference_proof(port: Port, definition: Path, spec: Path, kprove: str) -> None:
    """Prove the emitted claims with the Haskell prover selected by `kprove`."""

    base = [kprove, spec, "--definition", definition, "--spec-module", port.spec_module]
    dry = run([*base, "--dry-run"], timeout=180)
    if "kore-exec" not in dry.stdout or "--prove" not in dry.stdout:
        raise GateError("proof dry run did not select the native Haskell prover")
    proof = run(base, timeout=300)
    if proof.stdout.strip() != "#Top":
        raise GateError(f"{port.label} claims did not close: {proof.stdout.strip()}")


def java_reference_gate(
    port: Port,
    hooks: Hooks,
    workspace: Path,
    artifacts: Path,
    k: Mapping[str, str],
    pins: Ledger,
    corpus: Mapping[str, Any],
    native_outcomes: list[dict[str, Any]],
    gate: Path,
    environment: Mapping[str, str],
    definition_kore_sha256: str,
) -> int:
    """Compare the pinned Java route with native outcomes and prove emitted claims."""

    definition, spec = reference_definition(
        port, workspace, artifacts, k["kompile"], hooks.claim_count, pins, gate, environment
    )
    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    skipped = hooks.java_skips or {}
    outcomes: list[dict[str, Any]] = []
    with krs_gate.Session(gate, environment=environment) as session:
        session.load(
            artifacts / "definition-ir.json", port.module,
            definition_kore_sha256=definition_kore_sha256,
        )
        for case in behavior:
            if str(case["id"]) in skipped:
                continue
            surface = hooks.configuration_variables(case)
            if hooks.kore_configuration:
                configured = session.configure(surface)["variables"]
                names = [name for name in surface if name != "PGM"]
                arguments = [
                    f"-cPGM={surface['PGM']}",
                    *(f"-c{name}={configured[name]['kore']}" for name in names),
                    *(f"-p{name}=cat" for name in names),
                ]
            else:
                arguments = [f"-c{name}={value}" for name, value in surface.items()]
            result = run(
                [
                    k["krun"], "--definition", definition,
                    *arguments, "--output", "kore",
                ],
                timeout=120,
            ).stdout
            outcomes.append(behavior_module.java_case(session, case, result, corpus))

    compare_routes(port.label, native_outcomes, outcomes, skipped)
    reference_proof(port, definition, spec, k["kprove"])
    return hooks.claim_count


def reference_summary(port: Port, executions: int, proofs: int, java_reference: bool) -> str:
    """The PASS summary of a port with one Java reference proof."""

    proof_status = (
        f"{proofs} reference proof"
        if java_reference
        else "1 reference proof deferred to --java-reference"
    )
    return (
        f"{port.descriptors} descriptors; {executions} K-Rust executions; {proof_status}; "
        f"KRS schema {krs_ir_schema()}"
    )


def run_port(port: Port, hooks: Hooks) -> int:
    """Run one semantics qualification gate with its port-specific hooks."""

    parser = argparse.ArgumentParser(description=hooks.description)
    parser.add_argument("--java-reference", action="store_true", help=hooks.java_help)
    parser.add_argument(
        "--record", action="store_true",
        help="run the gate and rewrite the output pins it measured",
    )
    add_artifacts_only_argument(parser)
    arguments = parser.parse_args()
    reject_artifacts_only_conflicts(parser, arguments)

    pins = Ledger(port.pins_path, record=arguments.record, artifacts_only=arguments.artifacts_only)
    corpus = load_toml(port.corpus_path)
    environment = preflight(port, pins, corpus)
    krs, gate = rust_gate(port, environment)
    with tempfile.TemporaryDirectory(prefix=f"krs-{port.key}-gate-", dir=scratch_root()) as temporary:
        workspace = Path(temporary)
        artifacts = artifact_gate(port, workspace, krs, pins, gate, environment)
        if hooks.definition_checks is not None:
            hooks.definition_checks(artifacts, gate, environment)
        definition_kore_sha256 = native_definition(workspace, artifacts, gate, pins, environment)
        if arguments.artifacts_only:
            print(f"PASS {hooks.label}: {artifacts_only_summary(port)}")
            return 0
        executions, native_outcomes = native_behavior(
            port, gate, artifacts / "definition-ir.json", definition_kore_sha256, pins, corpus, environment
        )
        proofs = 0
        if arguments.java_reference:
            k = {name: k_tool(name, k_version()) for name in ("kompile", "krun", "kprove")}
            proofs = java_reference_gate(
                port, hooks, workspace, artifacts, k, pins, corpus, native_outcomes,
                gate, environment, definition_kore_sha256,
            )
    pins.finish(hooks.label)
    summary = hooks.summary or reference_summary
    print(f"PASS {hooks.label}: {summary(port, executions, proofs, arguments.java_reference)}")
    return 0
