#!/usr/bin/env python3
"""Ordered, fail-closed IMP complete-IMP release gate.

The default mode stops on the first failed evidence layer.  ``--audit-all``
continues only with layers whose prerequisites are independently available;
it never turns missing evidence into a skip or a pass.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field, replace
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Callable, Mapping, TypeVar, cast

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry  # noqa: E402
from support import krs_gate, lock  # noqa: E402
from support.checkouts import verify_checkout  # noqa: E402
from support.hashing import (  # noqa: E402
    canonical_json,
    exact_directory,
    json_sha256,
    sha256_file,
    sha256_text,
)
from support.kdefinition import emitted_claims, emitted_files  # noqa: E402
from support.krs import Invocation, build, fresh_deterministic_emissions  # noqa: E402
from support.parallel import settle_all, worker_count  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger, load_json, load_toml, table  # noqa: E402
from support.process import compact, run  # noqa: E402
from support.imp_oracle import reduce_definition  # noqa: E402
from support.reference import (  # noqa: E402
    Key, Output, Promotion, STAGING_OPTION, Snapshot, add_refresh_argument, json_sorted_lists,
    reduce_kprove_temp, reduce_store_paths, repository_inputs, sorted_kore_claims,
)
from support.tools import checkout_scratch, executable, k_version_matches, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
PINS_PATH = HERE / "pins.json"
CORPUS_PATH = HERE / "corpus.json"
RUST_MANIFEST = HERE / "rust-definition/Cargo.toml"
EXPANSION_GOLDEN = HERE / "goldens/imp.expanded.rs"
EXPANDED_MANIFEST = HERE / "expanded-definition/Cargo.toml"
EXPANDED_SOURCE = HERE / "expanded-definition/src/imp.rs"
PROBE_MANIFEST = HERE / "oracle/artifact-probe/Cargo.toml"
PACKAGE = "krs-imp-definition"
DEFINITION = "main"
MODULE = "KRS-IMP"
REFERENCE_MODULE = "KRS-IMP-STATIC"
REFERENCE_SYNTAX_MODULE = "KRS-IMP-STATIC-SYNTAX"
EXPANDED_PACKAGE = "krs-imp-expanded"
CLAIM_COUNT = 20
REPLACED_K_TAIL_CELLS = ["k"]
PRESERVED_MAP_REMAINDER_CELLS = ["env"]
REFERENCE = HERE / "reference"
KOMPILE_TESTS_REFERENCE = REFERENCE / "kompile-tests"
KOMPILE_TEST_COUNT = 2
UPSTREAM_IMP = ROOT.parent / "inspirations/runtimeverification/imp-semantics"
UPSTREAM_DEFINITION = UPSTREAM_IMP / "src/kimp/kdist/imp-semantics"
REFERENCE_SOURCE = ROOT / "tests/imp_static_semantics/fixtures/static-adjunct.k"
EMITTED_DEFINITION_INPUT = "emitted/definition.k"
"""The key name of the KRS-emitted `definition.k` the actual route compiles."""


def reduce_source_definition(text: str) -> str:
    """The stored `parsed.json` or `compiled.json` of an IMP.4 definition.

    It omits the metadata attributes krs-gate removes, and sorts each module's
    `localSentences`, which K writes in a run-dependent order for the emitted
    modules and which the projection reads as a multiset.
    """

    return sort_sentences(reduce_definition(text))


sort_sentences = json_sorted_lists(("localSentences",))

BASE_TOOLS = ("cargo", "rustc", "rustfmt", "clippy-driver", "git")
"""Tools every run needs: the Rust checks and the checkout verification."""
LSP_TOOLS = ("rust-analyzer",)
"""The live LSP probes of IMP.2 (and IMP.8) start rust-analyzer from PATH."""
JAVA_TOOLS = ("kompile", "kast", "krun", "kprove", "kore-exec", "llvm-kompile", "z3")
"""The pinned K toolchain and the solver its Haskell backend starts."""


def require_exact_summary(
    process: subprocess.CompletedProcess[str], expected: str, phase: str
) -> None:
    """Reject a nominal PASS accompanied by missing, extra, or stderr output."""

    if process.stdout != expected or process.stderr:
        raise GateError(f"{phase} did not report its exact PASS summary: {compact(process)}")


def _verify_replacement_parity(authored: Path, replacement: Path, gate: Path, environment: Mapping[str, str]) -> None:
    facts = krs_gate.ir_query(gate, replacement, {
        "kind": "replacement_parity", "reference": os.fspath(authored),
        "module": MODULE, "module_path": ["imp"],
        "k_namespace": MODULE,
        "replaced_k_tail_cells": REPLACED_K_TAIL_CELLS,
        "preserved_map_remainder_cells": PRESERVED_MAP_REMAINDER_CELLS,
    }, environment=environment)
    expected = load_json(HERE / "replacement-parity.json")
    if facts != expected:
        raise GateError(f"typed replacement parity differs: {facts!r}")


@dataclass
class Context:
    pins: Ledger
    corpus: dict[str, Any]
    workspace: Path
    target: Path
    live_java: bool = True
    """Whether a layer that runs Java K live runs: a refresh, or IMP.8."""
    refresh: bool = False
    """Whether the run refreshes the reference snapshots."""
    tools: dict[str, str] = field(default_factory=dict)
    environment: dict[str, str] = field(default_factory=dict)
    snapshots: list[Snapshot | Promotion] = field(default_factory=list)
    """Reference snapshots to finish once every layer passed."""

    def upstream(self) -> dict[str, str]:
        """The upstream revision every IMP.4-IMP.8 snapshot reads."""

        revisions = table(self.pins.get("revisions"), "pins.revisions")
        return {"imp": str(table(revisions.get("imp"), "revisions.imp").get("commit"))}

    def snapshot(self, name: str, tools: tuple[str, ...], inputs: Mapping[str, Path]) -> Snapshot:
        """Open the layer snapshot `reference/<name>` and finish it with the gate."""

        snapshot = Snapshot(
            REFERENCE / name, Key(tools=tools, upstream=self.upstream(), inputs=inputs),
            workspace=self.workspace, refresh=self.refresh,
            executables={tool: self.tools[tool] for tool in tools} if self.refresh else None,
        )
        self.snapshots.append(snapshot)
        return snapshot

    def child_snapshot(self, name: str) -> list[str]:
        """The arguments that let a child process replay or refresh `reference/<name>`.

        A refresh stages the child's snapshot in the workspace; the gate
        promotes it only after every layer passed.
        """

        if not self.refresh:
            return []
        staged = self.workspace / "reference-staging" / name
        self.snapshots.append(Promotion(staged, REFERENCE / name))
        return ["--refresh-reference", STAGING_OPTION, os.fspath(staged)]


def required_tools(live_java: bool) -> tuple[str, ...]:
    """The executables IMP.1 requires for the layers that will run.

    IMP.2 always runs its LSP probes; Java K and the solver are required only
    when a layer runs them live. IMP.2's kompile tests replay a recorded
    snapshot unless the run refreshes it.
    """

    return (*BASE_TOOLS, *LSP_TOOLS, *(JAVA_TOOLS if live_java else ()))


@dataclass(frozen=True)
class RustBuild:
    krs: Path

    @property
    def detail(self) -> str:
        return (
            "authored package formatting, Clippy, and MSRV checks; authored and expanded "
            "helper tests; authored helper docs; kompile tests; gate self-tests; "
            "krs/krs-gate builds; diagnostic and readable IMP LSP evidence"
        )


@dataclass(frozen=True)
class Artifacts:
    paths: Path
    hashes: Mapping[str, str]
    native_build: Path

    @property
    def detail(self) -> str:
        return (
            "124 descriptors; deterministic reviewed Rust expansion; 83-descriptor replacement parity; "
            "seven repeated CLI/API source artifacts; repeated claim-free LLVM and Haskell native builds; "
            f"sha256={json_sha256(self.hashes)}"
        )


@dataclass(frozen=True)
class SourceDefinitions:
    actual: Path
    reference: Path
    actual_failure: Path
    reference_failure: Path
    actual_execution_k: Path
    comparison: Mapping[str, Any]

    @property
    def detail(self) -> str:
        return f"parsed/compiled fail-closed projection: {self.comparison}"


def phase_preflight(context: Context) -> str:
    """Check the input pins: external checkouts, their files, the corpus, and tools.

    KRS source is deliberately not pinned; the later phases pin what KRS
    produces. Toolchain and schema versions come from `Krs.lock`.
    """

    pins = context.pins
    corpus = context.corpus
    if pins.get("schema") != 1 or pins.get("milestone") != "IMP":
        raise GateError("pins.json is not the exact IMP schema-1 ledger")
    if corpus.get("schema") != 2:
        raise GateError("corpus.json is not schema 2")
    if sha256_file(CORPUS_PATH) != pins.get("corpus_sha256"):
        raise GateError("corpus.json hash differs from pins.json")

    # IMP reuses the IMP state, IMP control flow, and IMP static semantics corpora; each is pinned in its own gate ledger.
    ledgers = table(corpus.get("input_ledgers"), "corpus.input_ledgers")
    if set(ledgers) != {"imp-state", "imp-control-flow", "imp-static-semantics"}:
        raise GateError("corpus must name exactly the IMP state, IMP control flow, and IMP static semantics input ledgers")
    for name, raw in ledgers.items():
        path = ROOT / str(table(raw, f"input ledger {name}").get("path"))
        ledger = Ledger(path)
        for relative, expected in ledger.table("corpus_sha256").items():
            if sha256_file(path.parent / relative) != expected:
                raise GateError(f"{name} corpus hash differs: {relative}")

    checkouts = {
        "imp": UPSTREAM_IMP,
        "k_rust": ROOT.parent / "inspirations/midnightntwrk/k-rust-krs-main",
    }
    expected = {
        "imp": table(table(pins.get("revisions"), "pins.revisions").get("imp"), "revisions.imp").get("commit"),
        "k_rust": str(lock.value("k_rust", "commit")),
    }
    if context.live_java:
        # The K source checkout qualifies only the live toolchain.
        checkouts["k"] = ROOT.parent / "inspirations/runtimeverification/k"
        expected["k"] = lock.k_commit()
    # A clean checkout at the pinned commit fixes every input file; the gate
    # does not digest external files separately.
    for name, path in checkouts.items():
        verify_checkout(path, str(expected[name]), label=name)
    for crate, key in (
        ("k-rust", "version"), ("k-rust-backend", "backend_version"), ("k-rust-kore", "kore_version")
    ):
        manifest = load_toml(checkouts["k_rust"] / "crates" / crate / "Cargo.toml")
        if table(manifest.get("package"), f"{crate} package").get("version") != lock.value("k_rust", key):
            raise GateError(f"{crate} version differs from Krs.lock [k_rust] {key}")

    context.tools = {name: executable(name) for name in required_tools(context.live_java)}
    if context.live_java:
        verify_java_tools(context.tools)
    context.environment = z3_environment()
    msrv = run(["rustc", f"+{lock.msrv()}", "--version"], timeout=30).stdout.strip()
    if not msrv.startswith(f"rustc {lock.msrv()} "):
        raise GateError(f"MSRV toolchain differs from Krs.lock: {msrv}")
    native_rust = run(["rustc", "+stable", "--version"], timeout=30).stdout.strip()
    lock.require_stable_at_least_msrv(native_rust)
    java = "live Java K" if context.live_java else "recorded Java K (no K tools required)"
    return (
        f"external checkouts and files, corpus, tools, {java}, KRS schema {lock.krs_ir_schema()}, "
        f"MSRV {lock.msrv()}, and {native_rust}"
    )


def verify_java_tools(tools: Mapping[str, str]) -> None:
    """Require the `Krs.lock` K, kore-exec, LLVM backend, and Z3 versions."""

    version = run([tools["kompile"], "--version"], timeout=30)
    if not k_version_matches(version, lock.k_version()):
        raise GateError(f"K tool version differs from Krs.lock: {compact(version)}")
    kore = run([tools["kore-exec"], "--version"], timeout=30).stdout.strip()
    if kore != lock.value("k", "kore_exec_version"):
        raise GateError(f"kore-exec version differs from Krs.lock: {kore}")
    llvm = Path(tools["llvm-kompile"]).resolve()
    if f"llvm-backend-{lock.value('k', 'llvm_backend_version')}" not in llvm.as_posix():
        raise GateError("LLVM backend version differs from Krs.lock")
    z3 = run([tools["z3"], "--version"], timeout=30).stdout.strip()
    if z3 != f"Z3 version {lock.z3_version()} - 64 bit":
        raise GateError(f"Z3 version differs from Krs.lock: {z3}")


def kompile_exported_tests(context: Context, exports: Path) -> Snapshot:
    """Compile the sources IMP.2's kompile tests exported through the recorded snapshot.

    Each exported source is keyed by its digest, so a change to what the
    lowering emits requires `--refresh-reference`.
    """

    requests = sorted(exports.glob("*.json"))
    sources = sorted(exports.glob("*.k"))
    if len(requests) != KOMPILE_TEST_COUNT or [path.with_suffix(".k") for path in requests] != sources:
        raise GateError(f"kompile tests exported {[path.name for path in sorted(exports.iterdir())]}")
    executables = {"kompile": context.tools["kompile"]} if context.refresh else None
    snapshot = Snapshot(
        KOMPILE_TESTS_REFERENCE, Key(tools=("kompile",)), workspace=context.workspace,
        refresh=context.refresh, executables=executables,
    )
    for path in requests:
        request = load_json(path)
        main, syntax = str(request.get("main")), str(request.get("syntax"))
        definition = exports / f"{main}-kompiled"
        process = snapshot.run(
            f"kompile/{main}", "kompile",
            [
                path.with_suffix(".k"), "--main-module", main, "--syntax-module", syntax,
                "--backend", "llvm", *(["--enable-search"] if request.get("enable_search") is True else []),
                "--output-definition", definition,
            ],
            timeout=600,
        )
        if process.returncode != 0:
            raise GateError(f"kompile rejected the canonical {main} source: {compact(process)}")
        if context.refresh and not (definition / "definition.kore").is_file():
            raise GateError(f"kompile produced no definition.kore for {main}")
    return snapshot


def phase_rust(context: Context) -> RustBuild:
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
    commands = [
        ["cargo", "test", "--manifest-path", os.fspath(RUST_MANIFEST), "--locked"],
        ["cargo", "test", "--manifest-path", os.fspath(EXPANDED_MANIFEST), "--locked"],
    ]
    for command in commands:
        run(command, timeout=900, environment=env)
    exports = context.workspace / "kompile-tests"
    kompile_tests = run(
        [
            "cargo", "test", "--locked", "-p", "krs-compiler",
            "--test", "control_flow_lowering", "--test", "fixed_state_lowering",
            "--", "--ignored",
        ],
        timeout=900,
        environment={**env, "KRS_REFERENCE_EXPORT_DIR": os.fspath(exports)},
    )
    results = re.findall(
        r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed;",
        kompile_tests.stdout,
        flags=re.MULTILINE,
    )
    if sum(int(passed) for _, passed, _ in results) != KOMPILE_TEST_COUNT or any(
        status != "ok" or int(failed) != 0 for status, _, failed in results
    ):
        raise GateError(f"expected exactly two passing kompile tests: {compact(kompile_tests)}")
    context.snapshots.append(kompile_exported_tests(context, exports))
    doc_env = {**env, "RUSTDOCFLAGS": "-D warnings"}
    run(
        [
            "cargo", "doc", "--manifest-path", RUST_MANIFEST,
            "--no-deps", "--locked",
        ],
        timeout=900,
        environment=doc_env,
    )
    for suite in (
        HERE / "test_gate.py",
        HERE / "oracle/test_orchestration.py",
        HERE / "compatibility/test_probes.py",
    ):
        run([sys.executable, suite], timeout=300, environment=env)

    krs = build(env, target=context.target, timeout=600)
    krs_gate.build(context.target, environment=env)
    check_packages("imp", krs=krs, env=env, target_dir=context.target)
    # These live LSP probes select authored tokens. A mere rust-analyzer
    # --version check is deliberately insufficient evidence.
    run(
        [sys.executable, HERE / "compatibility/diagnostics/rust-expansion/lsp_probe.py"],
        timeout=240,
        environment={
            **context.environment,
            "CARGO_TARGET_DIR": os.fspath(context.target / "lsp"),
        },
    )
    run(
        [sys.executable, HERE / "rust-definition/tools/lsp_probe.py"],
        timeout=240,
        environment={
            **context.environment,
            "CARGO_TARGET_DIR": os.fspath(context.target / "readable-lsp"),
        },
    )
    return RustBuild(krs)


NATIVE_ARTIFACTS = (".krs-artifacts", "definition.kore", "macros.kore", "syntaxDefinition.kore")


def krs_invocation(krs: Path) -> Invocation:
    return Invocation(krs, RUST_MANIFEST, PACKAGE, DEFINITION)


def native_artifacts(context: Context, krs: Path, env: Mapping[str, str]) -> Path:
    """Build the native definition twice per backend and pin both.

    The concrete LLVM backend does not prove, so its build omits every claim.
    """

    llvm_builds: list[Path] = []
    for name in ("llvm-a", "llvm-b"):
        output = context.workspace / name
        process = run(
            krs_invocation(krs).argv("build", "--backend", "llvm", "--output", output),
            timeout=900,
            environment=env,
        )
        omitted = f"omitted {CLAIM_COUNT} claims: the llvm backend executes but does not prove\n"
        if not process.stdout.endswith(omitted):
            raise GateError(f"LLVM build did not report its omitted claims: {process.stdout!r}")
        llvm_builds.append(output)
    for name, digest in exact_directory(llvm_builds[0], llvm_builds[1], NATIVE_ARTIFACTS).items():
        context.pins.expect(("llvm_artifact_sha256", name), digest)

    builds: list[Path] = []
    for name in ("native-a", "native-b"):
        output = context.workspace / name
        run(
            krs_invocation(krs).argv("build", "--backend", "haskell", "--output", output),
            timeout=900,
            environment=env,
        )
        builds.append(output)
    native_files = tuple(context.pins.get("native_artifact_sha256", {}).keys())
    if not native_files:
        raise GateError("native artifact set is absent from pins.json")
    for name, digest in exact_directory(builds[0], builds[1], native_files).items():
        context.pins.expect(("native_artifact_sha256", name), digest)
    return builds[0]


def phase_artifacts(context: Context, rust_build: RustBuild) -> Artifacts:
    krs = rust_build.krs
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
    check = run(krs_invocation(krs).argv("check"), timeout=300, environment=env)
    if "KRS check passed: 124 descriptors, 2 semantic modules" not in check.stdout:
        raise GateError(f"KRS check summary differs: {compact(check)}")

    expands = [
        run(krs_invocation(krs).argv("expand"), timeout=300, environment=env).stdout
        for _ in range(2)
    ]
    if expands[0] != expands[1]:
        raise GateError("repeated KRS expansion differs byte-for-byte")
    golden = EXPANSION_GOLDEN.read_text(encoding="utf-8")
    if expands[0] != golden:
        raise GateError("live KRS expansion differs from goldens/imp.expanded.rs")
    if EXPANDED_SOURCE.read_text(encoding="utf-8") != golden:
        raise GateError("replacement crate source differs from the reviewed expansion golden")

    emit_a, emit_b = fresh_deterministic_emissions(
        krs_invocation(krs), context.workspace,
        extra=("--backend", "haskell"), environment=env, timeout=300,
    )
    replacement_invocation = Invocation(krs, EXPANDED_MANIFEST, EXPANDED_PACKAGE, DEFINITION)
    replacement_check = replacement_invocation.run("check", timeout=300, environment=env)
    if "KRS check passed: 83 descriptors, 2 semantic modules" not in replacement_check.stdout:
        raise GateError(f"replacement KRS check summary differs: {compact(replacement_check)}")
    replacement = context.workspace / "expanded-replacement"
    replacement_invocation.run(
        "emit-k", "--backend", "haskell", "--output", replacement,
        timeout=300, environment=env,
    )
    _verify_replacement_parity(emit_a, replacement, context.target / "release/krs-gate", env)
    emitted_names = emitted_files(emit_a, context.target / "release/krs-gate", environment=env)
    for name, digest in exact_directory(emit_a, emit_b, emitted_names).items():
        # The ownership marker is the same file `krs build` writes natively.
        table_name = "native_artifact_sha256" if name == ".krs-artifacts" else "artifact_sha256"
        context.pins.expect((table_name, name), digest)

    probes: list[Path] = []
    for name in ("probe-a", "probe-b"):
        output = context.workspace / name
        run(
            ["cargo", "run", "--locked", "--quiet", "--manifest-path", PROBE_MANIFEST, "--", output],
            timeout=600,
            environment=env,
        )
        probes.append(output)
    probe_names = tuple(name for name in emitted_names if name != ".krs-artifacts")
    probe_hashes = exact_directory(probes[0], probes[1], (*probe_names, "native-source.txt"))
    for name in probe_names:
        if emit_a.joinpath(name).read_bytes() != probes[0].joinpath(name).read_bytes():
            raise GateError(f"CLI and production API probe differ: {name}")

    for name, digest in probe_hashes.items():
        context.pins.expect(("artifact_sha256", name), digest)
    native_build = native_artifacts(context, krs, env)
    return Artifacts(probes[0], probe_hashes, native_build)


def compile_source_definitions(context: Context, artifacts: Artifacts) -> SourceDefinitions:
    labels, _ = emitted_claims(artifacts.paths, MODULE, CLAIM_COUNT, gate=context.target / "release/krs-gate", environment=context.environment)
    actual_source = context.workspace / "actual-execution.k"
    shutil.copy2(artifacts.paths / "definition.k", actual_source)
    if labels != context.pins.get("claim_labels"):
        raise GateError("emitted claim order differs from its exact pin")

    actual = context.workspace / "actual-execution-kompiled"
    reference = context.workspace / "reference-execution-kompiled"
    actual_failure = context.workspace / "actual-execution-llvm-kompiled"
    reference_failure = context.workspace / "reference-execution-llvm-kompiled"
    # The reference side is keyed by the upstream revision and the adjunct
    # fixture; the actual side by the digest of the emitted definition.k.
    # Replay restores what the later layers read: both projected definitions
    # and the actual KORE that IMP.5 compares with the native build.
    k = context.snapshot("source-definitions", ("kompile",), source_inputs(actual_source))
    commands: list[tuple[str, list[str | os.PathLike[str]], int, tuple[Output, ...]]] = [
        (
            "kompile/actual-haskell",
            [
                actual_source, "--backend", "haskell", "--main-module", MODULE,
                "--syntax-module", MODULE, "--emit-json", "--output-definition", actual,
            ],
            600,
            (
                Output(actual / "parsed.json", reduce_source_definition),
                Output(actual / "compiled.json", reduce_source_definition),
                Output(actual / "definition.kore", reduce_store_paths),
            ),
        ),
        (
            "kompile/actual-llvm",
            [
                actual_source, "--backend", "llvm", "--main-module", MODULE,
                "--syntax-module", MODULE, "--emit-json", "--output-definition", actual_failure,
            ],
            900,
            (),
        ),
        (
            "kompile/reference-llvm",
            [
                REFERENCE_SOURCE, "-I", UPSTREAM_DEFINITION, "--backend", "llvm",
                "--main-module", REFERENCE_MODULE, "--syntax-module", REFERENCE_SYNTAX_MODULE,
                "--emit-json", "--output-definition", reference_failure,
            ],
            900,
            (),
        ),
        (
            "kompile/reference-haskell",
            [
                REFERENCE_SOURCE, "-I", UPSTREAM_DEFINITION, "--backend", "haskell",
                "--main-module", REFERENCE_MODULE, "--syntax-module", REFERENCE_SYNTAX_MODULE,
                "--emit-json", "--output-definition", reference,
            ],
            600,
            (
                Output(reference / "parsed.json", reduce_source_definition),
                Output(reference / "compiled.json", reduce_source_definition),
            ),
        ),
    ]
    for label, arguments, timeout, outputs in commands:
        process = k.run(label, "kompile", arguments, timeout=timeout, outputs=outputs)
        if process.returncode != 0:
            raise GateError(f"{label} failed: {compact(process)}")
        if context.refresh:
            directory = Path(arguments[arguments.index("--output-definition") + 1])
            if not directory.joinpath("definition.kore").is_file():
                raise GateError(f"source frontend omitted {directory.name}/definition.kore")
        for output in outputs:
            if not output.path.is_file():
                raise GateError(f"source frontend omitted {output.path.parent.name}/{output.path.name}")
    return SourceDefinitions(actual, reference, actual_failure, reference_failure, actual_source, {})


def source_inputs(actual_source: Path) -> dict[str, Path]:
    """The key inputs of a snapshot that reads both compiled source definitions."""

    return {
        **repository_inputs([REFERENCE_SOURCE]),
        EMITTED_DEFINITION_INPUT: actual_source,
    }


def phase_source_definition(context: Context, artifacts: Artifacts) -> SourceDefinitions:
    definitions = compile_source_definitions(context, artifacts)
    policies = table(context.pins.get("source_definition"), "pins.source_definition")
    if policies.get("status") != "ready":
        raise GateError(str(policies.get("blocker", "source-definition policy is not ready")))
    files = table(policies.get("files"), "source_definition.files")
    if set(files) != {"parsed.json", "compiled.json"}:
        raise GateError("source-definition policies must cover parsed.json and compiled.json")
    comparison = {}
    with krs_gate.Session(context.target / "release/krs-gate", environment=context.environment) as session:
        for filename in ("parsed.json", "compiled.json"):
            file_policy = table(files[filename], f"source_definition.files.{filename}")
            if set(file_policy) != {
                "reference_ignored_sha256", "actual_ignored_sha256",
                "reference_supplemental_sha256", "actual_supplemental_sha256",
                "compatible_sentence_pairs",
            }:
                raise GateError(f"{filename} source compatibility policy has unknown fields")
            reference_raw = dict(table(policies.get("reference"), "source_definition.reference"))
            actual_raw = dict(table(policies.get("actual"), "source_definition.actual"))
            reference_raw["ignored_sentence_sha256"] = table(
                file_policy["reference_ignored_sha256"],
                f"source_definition.files.{filename}.reference_ignored_sha256",
            )
            actual_raw["ignored_sentence_sha256"] = table(
                file_policy["actual_ignored_sha256"],
                f"source_definition.files.{filename}.actual_ignored_sha256",
            )
            reference_raw["supplemental_sentence_sha256"] = table(
                file_policy["reference_supplemental_sha256"],
                f"source_definition.files.{filename}.reference_supplemental_sha256",
            )
            actual_raw["supplemental_sentence_sha256"] = table(
                file_policy["actual_supplemental_sha256"],
                f"source_definition.files.{filename}.actual_supplemental_sha256",
            )
            comparison[filename] = session.kast_project(
                {"path": os.fspath(definitions.reference / filename)},
                {"path": os.fspath(definitions.actual / filename)},
                reference_raw, actual_raw,
                compatible_sentence_pairs=file_policy["compatible_sentence_pairs"],
            )
    observed = {
        "parsed_reference_sha256": comparison["parsed.json"]["baseline_sha256"],
        "parsed_actual_sha256": comparison["parsed.json"]["actual_sha256"],
        "compiled_reference_sha256": comparison["compiled.json"]["baseline_sha256"],
        "compiled_actual_sha256": comparison["compiled.json"]["actual_sha256"],
        "parsed_sentence_count": comparison["parsed.json"]["sentence_count"],
        "compiled_sentence_count": comparison["compiled.json"]["sentence_count"],
    }
    context.pins.expect(("source_definition", "expected"), observed)
    return replace(definitions, comparison=observed)


def phase_native(context: Context, artifacts: Artifacts, definitions: SourceDefinitions) -> str:
    env = {**context.environment, "CARGO_TARGET_DIR": os.fspath(context.target)}
    native_kore = artifacts.native_build / "definition.kore"
    reference_kore = definitions.actual / "definition.kore"
    comparator = [context.target / "release/krs-gate", "kore-compare", reference_kore, native_kore, MODULE]
    native_policy = table(context.pins.get("native_comparison"), "pins.native_comparison")
    expected_native_policy_fields = {"status", "label_map", "reference_claims_module"}
    if set(native_policy) != expected_native_policy_fields or native_policy.get("status") != "ready":
        raise GateError("native comparison policy is not the exact ready schema")
    # K's frontend rejects claims in an executable definition, so emit-k
    # writes them to spec.k.  Compile the exact emitted claims as a
    # supplemental spec through the supported kprove --dry-run route, then
    # require the comparator to merge only that one-import/claims-only KORE
    # module.
    execution_source = definitions.actual_execution_k
    labels, claim_source = emitted_claims(artifacts.paths, MODULE, CLAIM_COUNT, gate=context.target / "release/krs-gate", environment=context.environment)
    if labels != context.pins.get("claim_labels"):
        raise GateError("native supplemental claim order differs")
    spec_module = str(native_policy.get("reference_claims_module"))
    if spec_module != f"{MODULE}-SPEC":
        raise GateError("native supplemental spec module pin differs")
    expected_label_map = {
        f"{spec_module}.{label}": f"{MODULE}.{label}"
        for label in context.pins.get("claim_labels", [])
    }
    if native_policy.get("label_map") != expected_label_map:
        raise GateError("native label map is not the exact 20-claim mapping")
    spec_path = context.workspace / "actual-claims-spec.k"
    spec_path.write_text(
        f'requires "{execution_source.name}"\n'
        'requires "imp-verification.k"\n\n'
        f'module {spec_module}\n'
        f'  imports {MODULE}\n'
        f'  imports IMP-VERIFICATION-SYNTAX\n\n{claim_source}endmodule\n',
        encoding="utf-8",
    )
    spec_temp = context.workspace / "native-spec-temp"
    spec_temp.mkdir()
    spec_kore = context.workspace / "native-spec" / "spec.kore"
    # The claims compile against the actual definition IMP.4 compiled, so the
    # emitted definition.k keys this snapshot as well as the spec.k digest.
    k = context.snapshot(
        "native-claims", ("kprove",), {EMITTED_DEFINITION_INPUT: execution_source},
    )
    process = k.run(
        "kprove/dry-run", "kprove",
        [
            spec_path, "-I", UPSTREAM_DEFINITION, "-d", definitions.actual,
            "--spec-module", spec_module, "--dry-run", "--temp-dir", spec_temp,
        ],
        timeout=900,
        # kprove writes the claims in a run-dependent order; the comparator reads them by label.
        outputs=(Output(
            spec_kore, sorted_kore_claims,
            locate=lambda: unique_file(spec_temp, "spec.kore", "kprove --dry-run"),
        ),),
        streams={"stdout": reduce_kprove_temp},
    )
    if process.returncode != 0 or not spec_kore.is_file():
        raise GateError(f"kprove --dry-run did not emit spec.kore: {compact(process)}")
    comparator.extend(["--reference-claims", spec_kore, spec_module])
    for source, target in table(native_policy.get("label_map", {}), "native label map").items():
        comparator.extend(["--label", f"{source}={target}"])
    result = run(comparator, timeout=600, environment=env)
    expected_summary = (
        "PASS native KORE: reference=1188 native=1188 "
        "reference_projector_pairs=0 native_projector_pairs=39\n"
    )
    require_exact_summary(result, expected_summary, "native comparator")
    return result.stdout.strip()


def unique_file(directory: Path, name: str, producer: str) -> Path:
    """The one file `name` a tool wrote below `directory`, or a missing path when it wrote none."""

    matches = sorted(directory.rglob(name))
    if len(matches) > 1:
        raise GateError(f"{producer} emitted {len(matches)} {name} files")
    return matches[0] if matches else directory / name


def phase_behavior(context: Context, definitions: SourceDefinitions) -> str:
    # The complete plan is deliberately constructed from corpus.json by a
    # separately tested fail-closed adapter.  Importing it here keeps the root
    # runner's ordered process ownership while retaining a small oracle API.
    sys.path.insert(0, os.fspath(HERE / "oracle"))
    import behavior
    adapter = getattr(behavior, "plan_from_manifest", None)
    policy_adapter = getattr(behavior, "term_policies", None)
    if adapter is None or policy_adapter is None:
        raise GateError("oracle behavior manifest adapter is missing")
    reference_policy, actual_policy = policy_adapter(context.pins["behavior"])
    plan = adapter(ROOT, context.corpus, context.pins["behavior"])
    # Corpus files and generated inputs are keyed by their argument digests;
    # both compiled definitions are keyed through their sources.
    k = context.snapshot(
        "behavior", ("kast", "krun"), source_inputs(definitions.actual_execution_k),
    )
    summary = behavior.compare_behavior(
        k=k, workspace=context.workspace / "behavior",
        gate=context.target / "release/krs-gate",
        reference=behavior.Route(
            definitions.reference,
            reference_policy,
            definitions.reference_failure,
        ),
        actual=behavior.Route(
            definitions.actual,
            actual_policy,
            definitions.actual_failure,
        ),
        plan=plan,
    )
    observed = {
        "parse_count": summary.parse_count,
        "execution_count": summary.execution_count,
        "depth_state_count": summary.depth_state_count,
        "search_count": summary.search_count,
        "rejection_count": summary.rejection_count,
        "failure_count": summary.failure_count,
        "evidence_sha256": summary.evidence_sha256,
    }
    context.pins.expect(("behavior", "expected"), observed)
    return canonical_json(observed)


def phase_proofs(context: Context, rust_build: RustBuild) -> str:
    proof_pins = table(context.pins.get("proof_outcomes"), "pins.proof_outcomes")
    if len(proof_pins) != 21:
        raise GateError(f"expected 21 proof invocations, found {len(proof_pins)}")
    harness = HERE / "oracle/run_proofs.py"
    if not harness.is_file():
        raise GateError("complete source/native proof harness is missing")
    result = run(
        [
            sys.executable, harness, "--pins", PINS_PATH,
            "--workspace", context.workspace / "proofs",
            "--k-version", lock.k_version(), "--k-commit", lock.k_commit(),
            "--krs", rust_build.krs,
            *context.child_snapshot("proofs"),
        ],
        timeout=7200,
        environment={
            **context.environment,
            "CARGO_TARGET_DIR": os.fspath(context.target),
            "KRS_GATE_BIN": os.fspath(context.target / "release/krs-gate"),
        },
    )
    expected_summary = (
        "PASS IMP proofs: reference_source=21 actual_source=21 "
        "dry_run_specs=21 native_haskell=21 native_unique_claims=20\n"
    )
    require_exact_summary(result, expected_summary, "proof harness")
    return result.stdout.strip()


def phase_compatibility(context: Context, rust_build: RustBuild, artifacts: Artifacts) -> str:
    env = {
        **context.environment,
        "CARGO_TARGET_DIR": os.fspath(context.target),
        "KRS_GATE_BIN": os.fspath(context.target / "release/krs-gate"),
        "KRS_IMP_PROBE_TARGET_ROOT": os.fspath(context.target / "probes"),
    }
    commands = [
        [sys.executable, HERE / "compatibility/stable-names/probe.py", "--krs", rust_build.krs],
        [sys.executable, HERE / "compatibility/diagnostics/rust-expansion/probe.py"],
        [sys.executable, HERE / "compatibility/diagnostics/rust-expansion/lsp_probe.py"],
        [sys.executable, HERE / "compatibility/diagnostics/krs-analysis/probe.py", "--krs", rust_build.krs],
        [
            sys.executable, HERE / "compatibility/diagnostics/k-frontend/probe.py",
            "--spec", artifacts.paths / "spec.k",
            "--sources", artifacts.paths / "sources.json",
            "--authored", HERE / "rust-definition/src/claims.rs",
            "--source-relative-path", "src/claims.rs", "--token", "bool::and",
            "--kompile", context.tools["kompile"], "--module", MODULE,
            "--verification-definition", ROOT.parent
            / "inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics",
        ],
    ]
    # Each probe owns its Cargo target and scratch directories. Reports keep
    # this order.
    groups = [[command] for command in commands]

    def run_group(group: list[list[Any]]) -> list[str]:
        return [run(command, timeout=900, environment=env).stdout.strip() for command in group]

    outcomes = settle_all(
        [lambda group=group: run_group(group) for group in groups],
        worker_count("KRS_IMP_ORACLE_WORKERS", 4),
    )
    reports = [report for outcome in outcomes for report in outcome.get()]
    digest = sha256_text("\n".join(reports))
    if table(context.pins.get("compatibility"), "pins.compatibility").get("policy_version") != 1:
        raise GateError("compatibility policy version differs from 1")
    context.pins.expect(("compatibility", "report_sha256"), digest)
    return f"five live compatibility probes; policy=1; sha256={digest}"


PHASES = (
    "preflight",
    "rust-and-lsp",
    "deterministic-artifacts",
    "source-definition",
    "native-kore",
    "parser-execution-search",
    "bounded-proofs",
    "compatibility-reproduction",
)
ARTIFACT_PHASES = 3
"""Preflight, the Rust checks, and every emitted artifact; `--artifacts-only` stops here."""


class StopPhases(Exception):
    """End the default gate after its first failed phase."""


PhaseResult = str | RustBuild | Artifacts | SourceDefinitions
T = TypeVar("T", bound=PhaseResult)


def run_phase(
    index: int,
    name: str,
    requires: tuple[str, ...],
    passed: set[str],
    failures: list[tuple[str, str]],
    audit_all: bool,
    function: Callable[[], T],
) -> T | None:
    for dependency in requires:
        if dependency not in passed:
            print(f"SKIP {name}: requires {dependency}", flush=True)
            return None
    try:
        result = function()
    except Exception as error:
        failures.append((name, str(error)))
        print(f"FAIL IMP.{index} {name}: {error}", file=sys.stderr, flush=True)
        if not audit_all:
            raise StopPhases from error
        return None
    passed.add(name)
    detail = result if isinstance(result, str) else result.detail
    print(f"PASS IMP.{index} {name}: {detail}", flush=True)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--audit-all", action="store_true")
    parser.add_argument(
        "--record",
        action="store_true",
        help="run every phase and rewrite the output pins it measured",
    )
    parser.add_argument(
        "--target-dir",
        type=Path,
        default=Path(
            os.environ.get(
                "KRS_IMP_TARGET_DIR",
                os.fspath(checkout_scratch() / "imp-root-target"),
            )
        ),
    )
    parser.add_argument(
        "--artifacts-only",
        action="store_true",
        help=(
            f"stop after IMP.{ARTIFACT_PHASES}, with every emitted artifact compared to its pin; "
            "skip the source, native KORE, behavior, proof, and compatibility comparisons"
        ),
    )
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    if arguments.artifacts_only and (arguments.record or arguments.audit_all):
        parser.error("--artifacts-only cannot be combined with --record or --audit-all")
    pins = Ledger(PINS_PATH, record=arguments.record, artifacts_only=arguments.artifacts_only)
    corpus = load_json(CORPUS_PATH)
    failures: list[tuple[str, str]] = []
    passed: set[str] = set()
    artifacts: Artifacts | None = None
    with tempfile.TemporaryDirectory(prefix="krs-imp-root-") as temporary:
        # IMP.8 still runs Java K live; every other K invocation replays a snapshot.
        context = Context(
            pins, corpus, Path(temporary), arguments.target_dir.resolve(),
            live_java=arguments.refresh_reference or not arguments.artifacts_only,
            refresh=arguments.refresh_reference,
        )
        context.target.mkdir(parents=True, exist_ok=True)
        try:
            run_phase(1, PHASES[0], (), passed, failures, arguments.audit_all,
                      lambda: phase_preflight(context))
            rust_build = run_phase(2, PHASES[1], (PHASES[0],), passed, failures,
                                   arguments.audit_all, lambda: phase_rust(context))
            artifacts = run_phase(3, PHASES[2], (PHASES[1],), passed, failures,
                                  arguments.audit_all,
                                  lambda: phase_artifacts(context, cast(RustBuild, rust_build)))
            if not arguments.artifacts_only:
                definitions = run_phase(
                    4, PHASES[3], (PHASES[2],), passed, failures, arguments.audit_all,
                    lambda: phase_source_definition(context, cast(Artifacts, artifacts)),
                )
                run_phase(
                    5, PHASES[4], (PHASES[2], PHASES[3]), passed, failures,
                    arguments.audit_all,
                    lambda: phase_native(context, cast(Artifacts, artifacts),
                                         cast(SourceDefinitions, definitions)),
                )
                run_phase(
                    6, PHASES[5], (PHASES[3],), passed, failures, arguments.audit_all,
                    lambda: phase_behavior(context, cast(SourceDefinitions, definitions)),
                )
                run_phase(7, PHASES[6], (PHASES[1],), passed, failures, arguments.audit_all,
                          lambda: phase_proofs(context, cast(RustBuild, rust_build)))
                run_phase(
                    8, PHASES[7], (PHASES[1], PHASES[2]), passed, failures,
                    arguments.audit_all,
                    lambda: phase_compatibility(context, cast(RustBuild, rust_build),
                                                cast(Artifacts, artifacts)),
                )
        except StopPhases:
            pass
        if not failures:
            for snapshot in context.snapshots:
                try:
                    print(f"PASS IMP reference snapshot: {snapshot.finish()}", flush=True)
                except GateError as error:
                    failures.append(("reference-snapshot", str(error)))
                    print(f"FAIL IMP reference snapshot: {error}", file=sys.stderr, flush=True)
    if failures:
        if arguments.audit_all:
            print("IMP audit blockers:", file=sys.stderr)
            for name, error in failures:
                print(f"- {name}: {error}", file=sys.stderr)
        return 1
    if arguments.artifacts_only:
        print(
            f"PASS IMP artifacts only: IMP.1-IMP.{ARTIFACT_PHASES} passed and every emitted artifact "
            f"matches its pin; comparison layers IMP.{ARTIFACT_PHASES + 1}-IMP.{len(PHASES)} skipped"
        )
        return 0
    pins.finish("IMP complete IMP")
    summary = {
        "krs_schema": lock.krs_ir_schema(),
        "k": {"version": lock.k_version(), "commit": lock.k_commit()},
        "k_rust": {
            "version": lock.value("k_rust", "version"),
            "commit": lock.value("k_rust", "commit"),
        },
        "proof_bounds": pins["proof_policy"],
        "artifacts": cast(Artifacts, artifacts).hashes,
        "compatibility_policy": pins["compatibility"]["policy_version"],
    }
    print(f"PASS IMP complete IMP: {canonical_json(summary)}")
    return 0


if __name__ == "__main__":
    entry("IMP setup", main)
