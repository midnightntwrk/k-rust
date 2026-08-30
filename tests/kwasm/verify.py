#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KWasm integer slice."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from typing import Any, Mapping, Sequence


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = ROOT / "semantics/kwasm/Cargo.toml"
SOURCE = ROOT / "semantics/kwasm/src/lib.rs"
LOCK = ROOT / "semantics/Cargo.lock"
CORPUS_PATH = HERE / "corpus.toml"
PINS_PATH = HERE / "pins.toml"
KWASM = ROOT.parent / "inspirations/runtimeverification/wasm-semantics"
PACKAGE = "krs-kwasm-semantics"
DEFINITION = "main"
MODULE = "KRS-KWASM"
SPEC_MODULE = f"{MODULE}-SPEC"
ARTIFACTS = (
    ".krs-artifacts",
    "definition-ir.json",
    "definition.k",
    "descriptor-bundle.json",
    "semantic-ir.json",
    "sources.json",
    "symbols.json",
)
SOURCE_LEDGER_PATHS = (
    "crates/krs-compiler/src/collect.rs",
    "crates/krs-compiler/src/emit.rs",
    "crates/krs-compiler/src/lowering.rs",
    "crates/krs-compiler/src/overlap.rs",
    "crates/krs-compiler/src/reference.rs",
    "crates/krs-compiler/src/semantic.rs",
    "crates/krs-compiler/src/sidecar.rs",
    "crates/krs-ir/src/definition.rs",
    "crates/krs-ir/src/grammar.rs",
    "crates/krs-ir/src/head_rule.rs",
    "crates/krs-ir/src/ir.rs",
    "crates/krs-ir/src/lib.rs",
    "crates/krs-ir/src/protocol_v6.rs",
    "crates/krs-ir/src/protocol_v7_rule.rs",
    "crates/krs-ir/src/semantic.rs",
    "crates/krs-ir/src/state.rs",
    "crates/krs-k-rust/src/lib.rs",
    "crates/krs-k-rust/src/bin/krs-native-compile.rs",
    "crates/krs-k-rust/src/bin/krs-native-runner.rs",
    "crates/krs-macros/src/expand.rs",
    "crates/krs-macros/src/lib.rs",
    "crates/krs-syntax/src/provenance.rs",
    "crates/krs-syntax/src/rule.rs",
    "crates/krs-syntax/src/state_rule.rs",
    "crates/krs-syntax/src/term.rs",
    "crates/krs-syntax/tests/rule_blocks.rs",
    "crates/krs/src/lib.rs",
    "draft/readability/kwasm/README.md",
    "tests/kwasm/corpus.toml",
    "tests/kwasm/lsp_probe.py",
    "tests/kwasm/native.py",
    "semantics/Cargo.lock",
    "semantics/Cargo.toml",
    "semantics/README.md",
    "semantics/coverage.toml",
    "semantics/kwasm/Cargo.toml",
    "semantics/kwasm/src/lib.rs",
    "tests/kwasm/verify.py",
)


class GateError(RuntimeError):
    """One required qualification layer failed."""


def sha256(path: Path) -> str:
    if not path.is_file():
        raise GateError(f"required file is missing: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized_kore_sha256(path: Path, semantics: Path) -> str:
    if not path.is_file():
        raise GateError(f"required file is missing: {path}")
    contents = path.read_bytes()
    temporary_source = os.fsencode(semantics.absolute())
    if temporary_source not in contents:
        raise GateError("native definition.kore does not record its semantics source")
    normalized = contents.replace(temporary_source, b"semantics.k")

    generated_binder = re.compile(
        rb"(?P<prefix>\\exists\{R\} \()"
        rb"(?P<variable>Var'Unds'Gen[0-9]+)"
        rb"(?P<sort>:Sort[A-Za-z0-9']+\{\})"
        rb"(?P<body>,.*?)"
        rb"(?P=variable)(?P=sort)"
        rb"(?P<suffix>.*?\\bottom\{R\}\(\))",
        re.DOTALL,
    )

    def normalize_generated_binder(match: re.Match[bytes]) -> bytes:
        variable = match.group("variable") + match.group("sort")
        if match.group(0).count(variable) != 2:
            raise GateError("native definition.kore changed a generated binder shape")
        replacement = b"Var'Unds'KrsAlpha" + match.group("sort")
        return match.group(0).replace(variable, replacement)

    normalized, binder_count = generated_binder.subn(
        normalize_generated_binder, normalized
    )
    if binder_count == 0:
        raise GateError("native definition.kore has no generated sort binders")
    return hashlib.sha256(normalized).hexdigest()


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def run(
    command: Sequence[str | os.PathLike[str]],
    *,
    cwd: Path = ROOT,
    environment: Mapping[str, str] | None = None,
    timeout: int = 600,
) -> subprocess.CompletedProcess[str]:
    env = {
        **os.environ,
        "LC_ALL": "C",
        "LANG": "C",
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    if environment:
        env.update(environment)
    process = subprocess.run(
        [os.fspath(item) for item in command],
        cwd=cwd,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    if process.returncode != 0:
        detail = "\n".join(
            part.strip() for part in (process.stdout, process.stderr) if part.strip()
        )
        rendered = " ".join(os.fspath(item) for item in command)
        raise GateError(f"command failed ({process.returncode}): {rendered}\n{detail}")
    return process


def git_revision(path: Path) -> str:
    return run(["git", "rev-parse", "HEAD"], cwd=path, timeout=30).stdout.strip()


def mapping(value: Any, name: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise GateError(f"{name} must be a TOML table")
    return value


def find_k_bin(version: str, commit: str) -> Path:
    configured = os.environ.get("KRS_K_BIN")
    candidates = []
    if configured:
        candidates.append(Path(configured))
    ambient = shutil.which("kompile")
    if ambient:
        candidates.append(Path(ambient).resolve().parent)
    candidates.extend(
        path.parent
        for path in Path("/nix/store").glob(f"*-k-{version}-{commit}/bin/kompile")
    )
    for candidate in candidates:
        if (candidate / "kompile").is_file() and (candidate / "krun").is_file():
            return candidate
    raise GateError(f"could not locate the pinned K {version} executable directory")


def find_z3_lib() -> Path:
    configured = os.environ.get("KRS_Z3_LIB")
    candidates = [Path(configured)] if configured else []
    candidates.extend(Path("/nix/store").glob("*-z3-4.12.5-lib/lib"))
    for candidate in candidates:
        if (candidate / "libz3.so").exists():
            return candidate
    raise GateError("could not locate the qualified Z3 4.12.5 library")


def find_rust_analyzer() -> Path:
    candidates = [
        Path("/var/tmp/krs-ra-1.97.1-bin/rust-analyzer"),
        Path(
            "/var/tmp/krs-rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin/rust-analyzer"
        ),
    ]
    ambient = shutil.which("rust-analyzer")
    if ambient:
        candidates.append(Path(ambient))
    for candidate in candidates:
        if candidate.is_file():
            return candidate.absolute()
    raise GateError("could not locate the qualified rust-analyzer")


def exact_directory(first: Path, second: Path) -> dict[str, str]:
    first_names = sorted(path.name for path in first.iterdir() if path.is_file())
    second_names = sorted(path.name for path in second.iterdir() if path.is_file())
    if first_names != list(ARTIFACTS) or second_names != list(ARTIFACTS):
        raise GateError(
            f"artifact set differs: first={first_names}, second={second_names}"
        )
    hashes = {name: sha256(first / name) for name in ARTIFACTS}
    for name, digest in hashes.items():
        if sha256(second / name) != digest:
            raise GateError(f"repeated emission differs: {name}")
    return hashes


def split_claims(source: str) -> tuple[str, list[str]]:
    lines = source.splitlines(keepends=True)
    starters = re.compile(
        r"^(?:endmodule\b|  (?:syntax\b|configuration\b|context alias\b|rule\b|claim \[))"
    )
    semantics: list[str] = []
    claims: list[str] = []
    index = 0
    while index < len(lines):
        if not lines[index].startswith("  claim ["):
            semantics.append(lines[index])
            index += 1
            continue
        start = index
        index += 1
        while index < len(lines) and starters.match(lines[index]) is None:
            index += 1
        claims.extend(lines[start:index])
    value = "".join(semantics)
    if len([line for line in claims if line.startswith("  claim [")]) != 1:
        raise GateError("expected exactly one emitted KWasm claim")
    if "  claim [" in value or not value.endswith("endmodule\n"):
        raise GateError("claim stripping did not preserve a claim-free module")
    return value, claims


def preflight(pins: Mapping[str, Any], corpus: Mapping[str, Any]) -> dict[str, str]:
    if pins.get("schema") != 1 or corpus.get("schema") != 1:
        raise GateError("KWasm gate schema differs from 1")
    if sha256(CORPUS_PATH) != pins.get("corpus_sha256"):
        raise GateError("corpus.toml differs from its pin")
    k_pin = mapping(pins.get("k"), "pins.k")
    kwasm_pin = mapping(pins.get("kwasm"), "pins.kwasm")
    if git_revision(KWASM) != kwasm_pin.get("commit"):
        raise GateError("KWasm checkout revision differs")
    if run(["git", "status", "--porcelain"], cwd=KWASM, timeout=30).stdout:
        raise GateError("KWasm evidence checkout is dirty")
    version_path = KWASM / "deps/k_release"
    if version_path.read_text(encoding="utf-8").strip() != kwasm_pin.get("version"):
        raise GateError("KWasm K release differs")

    schemas = mapping(pins.get("schemas"), "pins.schemas")
    protocol = (ROOT / "crates/krs-ir/src/lib.rs").read_text(encoding="utf-8")
    ir = (ROOT / "crates/krs-ir/src/ir.rs").read_text(encoding="utf-8")
    if (
        f"pub const CURRENT: Self = Self({schemas.get('descriptor_protocol')});"
        not in protocol
    ):
        raise GateError("descriptor protocol differs")
    if f"pub const CURRENT: Self = Self({schemas.get('definition_ir')});" not in ir:
        raise GateError("Definition IR schema differs")

    expected_sources = mapping(pins.get("source_sha256"), "pins.source_sha256")
    if set(expected_sources) != set(SOURCE_LEDGER_PATHS):
        raise GateError("KWasm source-ledger path set differs")
    for relative in SOURCE_LEDGER_PATHS:
        if sha256(ROOT / relative) != expected_sources[relative]:
            raise GateError(f"KWasm source ledger differs: {relative}")

    expected_external = mapping(pins.get("external_sha256"), "pins.external_sha256")
    evidence = corpus.get("source_evidence")
    if not isinstance(evidence, list) or not evidence:
        raise GateError("source evidence is empty")
    evidence_paths = {str(entry["path"]) for entry in evidence}
    if set(expected_external) != evidence_paths:
        raise GateError("external evidence-ledger path set differs")
    for relative in evidence_paths:
        if sha256(KWASM / relative) != expected_external[relative]:
            raise GateError(f"external KWasm evidence differs: {relative}")

    z3 = find_z3_lib()
    environment = {
        "LIBRARY_PATH": os.pathsep.join(
            [os.fspath(z3), os.environ.get("LIBRARY_PATH", "")]
        ).rstrip(os.pathsep),
        "LD_LIBRARY_PATH": os.pathsep.join(
            [os.fspath(z3), os.environ.get("LD_LIBRARY_PATH", "")]
        ).rstrip(os.pathsep),
        "CARGO_NET_OFFLINE": "true",
    }
    return environment


def rust_gate(workspace: Path, environment: Mapping[str, str]) -> tuple[Path, Path, Path]:
    root_target = Path(
        os.environ.get("KRS_KWASM_ROOT_TARGET", "/var/tmp/krs-kwasm-gate-root-target")
    )
    fixture_target = Path(
        os.environ.get("KRS_KWASM_FIXTURE_TARGET", "/var/tmp/krs-kwasm-gate-fixture-target")
    )
    run(
        ["cargo", "build", "--locked", "--offline", "-p", "krs-cli", "--bin", "krs"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(root_target)},
    )
    run(
        ["cargo", "build", "--locked", "--offline", "--release", "-p", "krs-k-rust", "--bins"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(root_target)},
        timeout=900,
    )
    common = ["--manifest-path", MANIFEST, "--locked", "--offline"]
    fixture_env = {**environment, "CARGO_TARGET_DIR": os.fspath(fixture_target)}
    run(["cargo", "check", *common, "--all-targets"], environment=fixture_env)
    run(["cargo", "test", *common], environment=fixture_env, timeout=900)
    run(
        ["cargo", "clippy", *common, "--all-targets", "--", "-D", "warnings"],
        environment=fixture_env,
        timeout=900,
    )
    run(["cargo", "fmt", "--all", "--", "--check"])
    run(
        [
            root_target / "debug/krs",
            "fmt",
            "--check",
            "--manifest-path",
            MANIFEST,
            SOURCE,
        ],
        environment=environment,
    )
    run(
        ["cargo", "+1.88.0", "check", *common, "--all-targets"],
        environment=fixture_env,
        timeout=900,
    )
    analyzer = find_rust_analyzer()
    lsp_env = {
        **environment,
        "PATH": os.pathsep.join([os.fspath(analyzer.parent), os.environ["PATH"]]),
    }
    run([sys.executable, HERE / "lsp_probe.py"], environment=lsp_env, timeout=240)
    return (
        root_target / "debug/krs",
        root_target / "release/krs-native-compile",
        root_target / "release/krs-native-runner",
    )


def artifact_gate(
    workspace: Path,
    krs: Path,
    pins: Mapping[str, Any],
    environment: Mapping[str, str],
) -> Path:
    base = [
        "--manifest-path",
        MANIFEST,
        "--package",
        PACKAGE,
        "--definition",
        DEFINITION,
    ]
    check = run([krs, "check", *base], environment=environment)
    if "60 descriptors" not in check.stdout:
        raise GateError(f"unexpected descriptor count: {check.stdout.strip()}")
    expansions = [run([krs, "expand", *base], environment=environment).stdout for _ in range(2)]
    if expansions[0] != expansions[1]:
        raise GateError("readable expansion is nondeterministic")
    expansion_hash = hashlib.sha256(expansions[0].encode()).hexdigest()
    if expansion_hash != pins.get("expansion_sha256"):
        raise GateError(f"expansion hash differs: {expansion_hash}")

    expanded = workspace / "expanded"
    expanded.joinpath("src").mkdir(parents=True)
    manifest = MANIFEST.read_text(encoding="utf-8")
    for relative, absolute in {
        "../../crates/krs": ROOT / "crates/krs",
        "../../crates/krs-compiler": ROOT / "crates/krs-compiler",
        "../../crates/krs-ir": ROOT / "crates/krs-ir",
        "../../../crates/krs-k-rust": ROOT / "crates/krs-k-rust",
    }.items():
        manifest = manifest.replace(relative, os.fspath(absolute))
    expanded.joinpath("Cargo.toml").write_text(manifest, encoding="utf-8")
    shutil.copy2(LOCK, expanded / "Cargo.lock")
    expanded.joinpath("src/lib.rs").write_text(expansions[0], encoding="utf-8")
    expanded_target = workspace / "expanded-target"
    run(
        ["cargo", "check", "--manifest-path", expanded / "Cargo.toml", "--locked", "--offline"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(expanded_target)},
        timeout=900,
    )

    outputs = [workspace / "emit-a", workspace / "emit-b"]
    for output in outputs:
        run([krs, "emit-k", *base, "--output", output], environment=environment)
    hashes = exact_directory(outputs[0], outputs[1])
    if hashes != dict(mapping(pins.get("artifact_sha256"), "pins.artifact_sha256")):
        raise GateError(f"emitted artifact hashes differ: {canonical(hashes)}")

    expanded_output = workspace / "expanded-emit"
    run(
        [
            krs,
            "emit-k",
            "--manifest-path",
            expanded / "Cargo.toml",
            "--package",
            PACKAGE,
            "--definition",
            DEFINITION,
            "--output",
            expanded_output,
        ],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(expanded_target)},
        timeout=900,
    )
    readable_k = (outputs[0] / "definition.k").read_text(encoding="utf-8")
    expanded_k = (expanded_output / "definition.k").read_text(encoding="utf-8")
    readable_prefix = readable_k.split("\n  rule ", 1)[0]
    expanded_prefix = expanded_k.split("\n  rule ", 1)[0]
    if readable_prefix != expanded_prefix:
        raise GateError("independently compiled expansion changed syntax or configuration")
    sentence_pattern = re.compile(r"^  (rule|claim)(?: \[([^]]+)\])?", re.MULTILINE)
    readable_sentences = sentence_pattern.findall(readable_k)
    expanded_sentences = sentence_pattern.findall(expanded_k)
    if readable_sentences != expanded_sentences:
        raise GateError(
            "independently compiled expansion changed rule or claim identity transport"
        )
    return outputs[0]


def compile_native_definition(
    workspace: Path,
    artifacts: Path,
    compiler: Path,
    pins: Mapping[str, Any],
    environment: Mapping[str, str],
) -> Path:
    definition = workspace / "native-definition.kore"
    run(
        [compiler, artifacts / "definition-ir.json", definition],
        environment=environment,
        timeout=900,
    )
    kore_hash = sha256(definition)
    if kore_hash != pins.get("native_definition_kore_sha256"):
        raise GateError(f"native K-Rust definition.kore hash differs: {kore_hash}")
    return definition


def k_rust_gate(
    runner: Path,
    definition: Path,
    pins: Mapping[str, Any],
    corpus: Mapping[str, Any],
    environment: Mapping[str, str],
) -> int:
    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    result = run(
        [sys.executable, HERE / "native.py", runner, definition, MODULE, CORPUS_PATH],
        environment=environment,
        timeout=900,
    )
    expected = f"PASS native KWasm behavior: {len(behavior)} executions; sha256={pins.get('behavior_sha256')}"
    if result.stdout.strip() != expected:
        raise GateError(f"K-Rust behavior evidence differs: {result.stdout.strip()}")
    return len(behavior)


def java_reference_gate(
    workspace: Path,
    artifacts: Path,
    k_bin: Path,
    pins: Mapping[str, Any],
    corpus: Mapping[str, Any],
) -> tuple[int, int]:
    claim_free, claims = split_claims(
        (artifacts / "definition.k").read_text(encoding="utf-8")
    )
    semantics = workspace / "semantics.k"
    semantics.write_text(claim_free, encoding="utf-8")
    definition = workspace / "semantics-kompiled"
    run(
        [
            k_bin / "kompile",
            semantics,
            "--backend",
            "haskell",
            "--main-module",
            MODULE,
            "--syntax-module",
            MODULE,
            "--emit-json",
            "--output-definition",
            definition,
        ],
        timeout=900,
    )
    kore_hash = normalized_kore_sha256(definition / "definition.kore", semantics)
    if kore_hash != pins.get("definition_kore_sha256"):
        raise GateError(f"native definition.kore hash differs: {kore_hash}")

    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    outcomes: list[dict[str, str]] = []
    for case in behavior:
        case_id = str(case["id"])
        expected_outcome = str(case.get("expected_outcome", "value"))
        if expected_outcome not in {"trap", "value"}:
            raise GateError(f"{case_id} has an unsupported expected outcome")
        result = run(
            [
                k_bin / "krun",
                "--definition",
                definition,
                f"-cPGM={case['program']}",
                "-cSTACK=.ValStack",
                "--output",
                "pretty",
            ],
            timeout=120,
        ).stdout
        if expected_outcome == "trap":
            if not re.search(
                r"<instrs>\s*trap\s*~>\s*\.Instrs\s*~>\s*\.K\s*</instrs>",
                result,
            ):
                raise GateError(f"{case_id} did not finish with a trap: {result}")
            if not re.search(r"<valstack>\s*\.ValStack\s*</valstack>", result):
                raise GateError(f"{case_id} trapped with an unexpected stack: {result}")
            observed = {"id": case_id, "outcome": "trap"}
            expected = {"id": case_id, "outcome": "trap"}
        else:
            if not re.search(r"<instrs>\s*\.K\s*</instrs>", result):
                raise GateError(
                    f"{case_id} did not finish its instruction stream: {result}"
                )
            match = re.search(
                r"<valstack>\s*<\s*(i32|i64)\s*>\s*(-?[0-9]+)\s*:\s*\.ValStack\s*</valstack>",
                result,
            )
            if match is None:
                raise GateError(f"{case_id} has an unexpected value stack: {result}")
            observed = {
                "id": case_id,
                "outcome": "value",
                "type": match.group(1),
                "value": match.group(2),
            }
            expected = {
                "id": case_id,
                "outcome": "value",
                "type": str(case["expected_type"]),
                "value": str(case["expected_value"]),
            }
        if observed != expected:
            raise GateError(f"{case_id} differs: expected={expected}, actual={observed}")
        outcomes.append(observed)
    behavior_hash = hashlib.sha256(canonical(outcomes).encode()).hexdigest()
    if behavior_hash != pins.get("behavior_sha256"):
        raise GateError(f"behavior hash differs: {behavior_hash}")

    spec = workspace / "spec.k"
    spec.write_text(
        f'requires "{semantics.name}"\n\nmodule {SPEC_MODULE}\n'
        f"  imports {MODULE}\n\n{''.join(claims)}endmodule\n",
        encoding="utf-8",
    )
    dry = run(
        [
            k_bin / "kprove",
            spec,
            "--definition",
            definition,
            "--spec-module",
            SPEC_MODULE,
            "--dry-run",
        ],
        timeout=180,
    )
    if "kore-exec" not in dry.stdout or "--prove" not in dry.stdout:
        raise GateError("proof dry run did not select the native Haskell prover")
    proof = run(
        [
            k_bin / "kprove",
            spec,
            "--definition",
            definition,
            "--spec-module",
            SPEC_MODULE,
        ],
        timeout=300,
    )
    if proof.stdout.strip() != "#Top":
        raise GateError(f"KWasm claim did not close: {proof.stdout.strip()}")
    return len(outcomes), 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--show-observed", action="store_true")
    parser.add_argument(
        "--java-reference",
        action="store_true",
        help="run the deferred K toolchain behavior comparison and proof",
    )
    arguments = parser.parse_args()
    pins = tomllib.loads(PINS_PATH.read_text(encoding="utf-8"))
    corpus = tomllib.loads(CORPUS_PATH.read_text(encoding="utf-8"))
    environment = preflight(pins, corpus)
    with tempfile.TemporaryDirectory(prefix="krs-kwasm-gate-", dir="/var/tmp") as temporary:
        workspace = Path(temporary)
        krs, compiler, runner = rust_gate(workspace, environment)
        artifacts = artifact_gate(workspace, krs, pins, environment)
        definition = compile_native_definition(
            workspace, artifacts, compiler, pins, environment
        )
        behavior_count = k_rust_gate(runner, definition, pins, corpus, environment)
        proof_count = 0
        if arguments.java_reference:
            k_pin = mapping(pins.get("k"), "pins.k")
            k_bin = find_k_bin(str(k_pin["version"]), str(k_pin["commit"]))
            observed_version = run([k_bin / "kompile", "--version"], timeout=30)
            if f"v{k_pin['version']}" not in observed_version.stdout + observed_version.stderr:
                raise GateError("K executable version differs")
            reference_behavior, proof_count = java_reference_gate(
                workspace, artifacts, k_bin, pins, corpus
            )
            if reference_behavior != behavior_count:
                raise GateError("K-Rust and reference execution counts differ")
    if arguments.show_observed:
        print("all observed values matched their pins")
    proof_status = (
        f"{proof_count} reference proof" if arguments.java_reference else "1 reference proof deferred to --java-reference"
    )
    print(
        "PASS readable KWasm integer slice: "
        f"60 descriptors; {behavior_count} K-Rust executions; {proof_status}; "
        f"protocol {pins['schemas']['descriptor_protocol']}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (GateError, OSError, subprocess.TimeoutExpired) as error:
        print(f"FAIL readable KWasm integer slice: {error}", file=sys.stderr)
        raise SystemExit(1)
