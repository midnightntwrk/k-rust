"""The gate flow the KWasm, KMIR, and KEVM semantics ports share.

Each port is a readable Rust package under `semantics/<port>/` with a corpus
and a pin ledger under `tests/<port>/`. The shared steps are: preflight over
the external checkout and the corpus, the ordinary Rust checks, repeated
expansion and emission with their output pins, native k-rust compilation and
execution, and the kompiled reference definition behind `--java-reference`.
The port-specific behavior and proof comparisons stay in each verifier.

`--artifacts-only` stops after the native definition: it checks every emitted
artifact against its pin and skips the behavior and proof comparisons, which
cannot find anything new while the artifacts are unchanged.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import shutil
import sys
from typing import Any, Mapping, Sequence

from support import ROOT, GateError
from support.checkouts import verify_checkout
from support.hashing import exact_directory, sha256_file, sha256_text
from support.kdefinition import EMITTED_ARTIFACTS, normalized_kore_sha256, split_claims
from support.lock import msrv
from support.pins import Ledger
from support.process import run
from support.tools import rust_analyzer, scratch_root, z3_environment


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
        """A persistent Cargo target: `KRS_<PORT>_<ROLE>_TARGET`, else under the scratch root."""

        variable = f"KRS_{self.key.upper()}_{role.upper()}_TARGET"
        default = scratch_root() / f"krs-{self.key}-gate-{role}-target"
        return Path(os.environ.get(variable, os.fspath(default)))


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

    Inputs are the external checkout revision, its K release, the digests of
    every external file the corpus cites, and the corpus itself. Schema
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

    expected_external = pins.table("external_sha256")
    evidence = corpus.get("source_evidence")
    if not isinstance(evidence, list) or not evidence:
        raise GateError("source evidence is empty")
    evidence_paths = {str(entry["path"]) for entry in evidence}
    if set(expected_external) != evidence_paths:
        raise GateError("external evidence-ledger path set differs")
    for relative in sorted(evidence_paths):
        if sha256_file(port.checkout / relative) != expected_external[relative]:
            raise GateError(f"external {port.label} evidence differs: {relative}")

    return {**z3_environment(), "CARGO_NET_OFFLINE": "true"}


def rust_gate(port: Port, environment: Mapping[str, str]) -> tuple[Path, Path, Path]:
    """Build the CLI and native tools; check, test, lint, and format the port."""

    root_target = port.target("root")
    root_env = {**environment, "CARGO_TARGET_DIR": os.fspath(root_target)}
    run(["cargo", "build", "--locked", "--offline", "-p", "krs-cli", "--bin", "krs"], environment=root_env)
    run(
        ["cargo", "build", "--locked", "--offline", "--release", "-p", "krs-k-rust", "--bins"],
        environment=root_env,
        timeout=900,
    )
    common = ["--manifest-path", port.manifest, "--locked", "--offline"]
    fixture_env = {**environment, "CARGO_TARGET_DIR": os.fspath(port.target("fixture"))}
    run(["cargo", "check", *common, "--all-targets"], environment=fixture_env)
    run(["cargo", "test", *common], environment=fixture_env, timeout=900)
    allow = [argument for lint in port.clippy_allow for argument in ("-A", lint)]
    run(
        ["cargo", "clippy", *common, "--all-targets", "--", "-D", "warnings", *allow],
        environment=fixture_env,
        timeout=900,
    )
    run(["cargo", "fmt", "--all", "--", "--check"])
    run(
        [root_target / "debug/krs", "fmt", "--check", "--manifest-path", port.manifest, port.source],
        environment=environment,
    )
    run(["cargo", f"+{msrv()}", "check", *common, "--all-targets"], environment=fixture_env, timeout=900)
    analyzer = rust_analyzer()
    lsp_env = {**environment, "PATH": os.pathsep.join([os.fspath(analyzer.parent), os.environ["PATH"]])}
    run([sys.executable, port.here / "lsp_probe.py"], environment=lsp_env, timeout=900)
    return (
        root_target / "debug/krs",
        root_target / "release/krs-native-compile",
        root_target / "release/krs-native-runner",
    )


def artifact_gate(
    port: Port,
    workspace: Path,
    krs: Path,
    pins: Ledger,
    environment: Mapping[str, str],
) -> Path:
    """Check, expand, and emit the port twice; compile the expansion independently.

    Records the expansion and emitted-artifact digests, requires the
    independently compiled expansion to emit the same syntax, configuration, and
    sentence identities, and returns the first emission directory.
    """

    base: Sequence[str | Path] = [
        "--manifest-path", port.manifest, "--package", port.package, "--definition", "main",
    ]
    check = run([krs, "check", *base], environment=environment)
    if f"{port.descriptors} descriptors" not in check.stdout:
        raise GateError(f"unexpected descriptor count: {check.stdout.strip()}")
    expansions = [run([krs, "expand", *base], environment=environment).stdout for _ in range(2)]
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
        ["cargo", "check", "--manifest-path", expanded / "Cargo.toml", "--locked", "--offline"],
        environment=expanded_env,
        timeout=900,
    )

    outputs = [workspace / "emit-a", workspace / "emit-b"]
    for output in outputs:
        run([krs, "emit-k", *base, "--output", output], environment=environment)
    for name, digest in exact_directory(outputs[0], outputs[1], EMITTED_ARTIFACTS).items():
        pins.expect(("artifact_sha256", name), digest)

    expanded_output = workspace / "expanded-emit"
    run(
        [
            krs, "emit-k", "--manifest-path", expanded / "Cargo.toml", "--package", port.package,
            "--definition", "main", "--output", expanded_output,
        ],
        environment=expanded_env,
        timeout=900,
    )
    readable = (outputs[0] / "definition.k").read_text(encoding="utf-8")
    replacement = (expanded_output / "definition.k").read_text(encoding="utf-8")
    if readable.split("\n  rule ", 1)[0] != replacement.split("\n  rule ", 1)[0]:
        raise GateError("independently compiled expansion changed syntax or configuration")
    sentence = re.compile(r"^  (rule|claim)(?: \[([^]]+)\])?", re.MULTILINE)
    if sentence.findall(readable) != sentence.findall(replacement):
        raise GateError("independently compiled expansion changed rule or claim identity transport")
    return outputs[0]


def native_definition(
    workspace: Path,
    artifacts: Path,
    compiler: Path,
    pins: Ledger,
    environment: Mapping[str, str],
) -> Path:
    """Lower the emitted Definition IR through k-rust and record its KORE digest."""

    definition = workspace / "native-definition.kore"
    run([compiler, artifacts / "definition-ir.json", definition], environment=environment, timeout=900)
    pins.expect("native_definition_kore_sha256", sha256_file(definition))
    return definition


_NATIVE_SUMMARY = re.compile(r"^PASS native (\S+) behavior: (\d+) executions; sha256=([0-9a-f]{64})$")


def native_behavior(
    port: Port,
    runner: Path,
    definition: Path,
    pins: Ledger,
    corpus: Mapping[str, Any],
    environment: Mapping[str, str],
) -> int:
    """Execute the corpus on the native runner and record its behavior digest."""

    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    result = run(
        [sys.executable, port.here / "native.py", runner, definition, port.module, port.corpus_path],
        environment=environment,
        timeout=900,
    )
    summary = _NATIVE_SUMMARY.match(result.stdout.strip())
    if (
        summary is None
        or summary.group(1) != port.label
        or int(summary.group(2)) != len(behavior)
    ):
        raise GateError(f"K-Rust behavior evidence differs: {result.stdout.strip()}")
    pins.expect("behavior_sha256", summary.group(3))
    return len(behavior)


def reference_definition(
    port: Port,
    workspace: Path,
    artifacts: Path,
    kompile: str,
    claim_count: int,
    pins: Ledger,
) -> tuple[Path, Path, str]:
    """Kompile the claim-free emitted definition with the pinned K frontend.

    Records its normalized KORE digest and returns the kompiled directory, the
    semantics source, and the claim sentences.
    """

    claim_free, _, claims = split_claims(
        (artifacts / "definition.k").read_text(encoding="utf-8"), claim_count
    )
    semantics = workspace / "semantics.k"
    semantics.write_text(claim_free, encoding="utf-8")
    definition = workspace / "semantics-kompiled"
    run(
        [
            kompile, semantics, "--backend", "haskell", "--main-module", port.module,
            "--syntax-module", port.module, "--emit-json", "--output-definition", definition,
            *(["--hook-namespaces", " ".join(port.hook_namespaces)] if port.hook_namespaces else []),
        ],
        timeout=900,
    )
    pins.expect("definition_kore_sha256", normalized_kore_sha256(definition / "definition.kore", semantics))
    return definition, semantics, claims


def reference_proof(
    port: Port,
    workspace: Path,
    definition: Path,
    semantics: Path,
    claims: str,
    kprove: str,
) -> None:
    """Prove the emitted claims with the Haskell prover selected by `kprove`."""

    spec = workspace / "spec.k"
    spec.write_text(
        f'requires "{semantics.name}"\n\nmodule {port.spec_module}\n'
        f"  imports {port.module}\n\n{claims}endmodule\n",
        encoding="utf-8",
    )
    base = [kprove, spec, "--definition", definition, "--spec-module", port.spec_module]
    dry = run([*base, "--dry-run"], timeout=180)
    if "kore-exec" not in dry.stdout or "--prove" not in dry.stdout:
        raise GateError("proof dry run did not select the native Haskell prover")
    proof = run(base, timeout=300)
    if proof.stdout.strip() != "#Top":
        raise GateError(f"{port.label} claims did not close: {proof.stdout.strip()}")
