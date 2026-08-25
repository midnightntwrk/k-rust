#!/usr/bin/env python3
"""Run native KRS Claim KORE through kprove and the frozen M3D normalizer."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Any

from normalize import digest, envelope, normalize_claim_spec, normalize_proof


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CASES = HERE / "cases.json"
MANIFEST = HERE / "Cargo.toml"
SHIM = HERE / "backend_shim.py"
UPSTREAM_DEFINITION = (
    ROOT.parent
    / "inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics"
)
SHELL_SOURCE = ROOT / "tests/m3d/fixtures/static-adjunct.k"
SEMANTIC_MODULE = "KRS-M3D-STATIC"
SYNTAX_MODULE = "KRS-M3D-STATIC-SYNTAX"
K_VERSION = "v7.1.337"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--native-kore", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument(
        "--skeleton",
        type=Path,
        help="reuse a compatible Haskell *-kompiled directory instead of compiling the pinned shell",
    )
    arguments = parser.parse_args()

    native_kore = arguments.native_kore.resolve(strict=True)
    workspace = arguments.workspace.resolve()
    prepare_workspace(workspace)
    tools = require_tools()
    cases = read_cases()
    environment = stable_environment()

    split = workspace / "split"
    cargo(
        ["split", str(native_kore), str(split), SEMANTIC_MODULE, str(CASES)],
        environment,
    )

    kompiled = workspace / "native-kompiled"
    if arguments.skeleton is None:
        run_checked(
            [
                tools["kompile"],
                str(SHELL_SOURCE),
                "-I",
                str(UPSTREAM_DEFINITION),
                "--backend",
                "haskell",
                "--main-module",
                SEMANTIC_MODULE,
                "--syntax-module",
                SYNTAX_MODULE,
                "--emit-json",
                "--output-definition",
                str(kompiled),
            ],
            environment=environment,
            timeout=300,
        )
    else:
        shutil.copytree(arguments.skeleton.resolve(strict=True), kompiled)
    validate_skeleton(kompiled)
    shutil.copyfile(split / "definition.kore", kompiled / "definition.kore")

    results_dir = workspace / "results"
    results_dir.mkdir()
    summary: dict[str, Any] = {}
    for case in cases:
        summary[case["name"]] = run_case(
            case, tools, environment, workspace, kompiled, split, results_dir
        )

    (workspace / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    for name, result in summary.items():
        print(
            f"PASS\t{name}\tresult={result['result_sha256']}\tclaim={result['claim_sha256']}"
        )
    print(f"PASS\tall\tworkspace={workspace}")
    return 0


def run_case(
    case: dict[str, Any],
    tools: dict[str, str],
    environment: dict[str, str],
    workspace: Path,
    kompiled: Path,
    split: Path,
    results_dir: Path,
) -> dict[str, Any]:
    name = case["name"]
    source_spec = (ROOT / case["source_spec"]).resolve(strict=True)
    native_spec = (split / "specs" / f"{name}.kore").resolve(strict=True)

    dry_root = workspace / "kprove-dry" / name
    dry_root.mkdir(parents=True)
    run_checked(
        proof_command(
            tools["kprove"], source_spec, kompiled, case, dry_root=dry_root
        )
        + ["--dry-run"],
        environment=environment,
        timeout=300,
    )
    generated_specs = list(dry_root.rglob("spec.kore"))
    if len(generated_specs) != 1:
        raise RuntimeError(
            f"{name}: expected one kprove-generated spec.kore, found {generated_specs}"
        )
    cargo(
        [
            "compare",
            str(generated_specs[0]),
            str(native_spec),
            case["source_claim"],
            case["native_label"],
        ],
        environment,
    )

    claim_json = results_dir / f"{name}-claim.json"
    prove_root = workspace / "kprove-run" / name
    prove_root.mkdir(parents=True)
    command = proof_command(
        tools["kprove"],
        source_spec,
        kompiled,
        case,
        dry_root=prove_root,
        claim_json=claim_json,
    )
    command.extend(
        [
            "--haskell-backend-command",
            f"{sys.executable} {SHIM}",
        ]
    )
    proof_environment = environment.copy()
    proof_environment["KRS_CLAIM_SPEC_KORE"] = str(native_spec)
    proof_environment["KRS_CLAIM_SPEC_MODULE"] = case["source_module"]
    proof_environment["KRS_KORE_EXEC"] = tools["kore-exec"]
    process = subprocess.run(
        command,
        env=proof_environment,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=300,
        check=False,
    )
    (results_dir / f"{name}.stderr").write_text(process.stderr, encoding="utf-8")
    (results_dir / f"{name}.json").write_text(process.stdout, encoding="utf-8")
    if process.returncode != 0:
        raise RuntimeError(
            f"{name}: native Claim proof failed with rc={process.returncode}\n{process.stderr}"
        )

    normalized = normalize_proof(envelope(process.stdout))
    if normalized["term"].get("label", {}).get("name") != "#Top":
        raise RuntimeError(f"{name}: proof result is not #Top")
    normalized_claim = normalize_claim_spec(
        json.loads(claim_json.read_text(encoding="utf-8"))
    )
    result_hash = digest(normalized)
    claim_hash = digest(normalized_claim)
    if result_hash != case["result_sha256"]:
        raise RuntimeError(
            f"{name}: result hash {result_hash} != {case['result_sha256']}"
        )
    if claim_hash != case["claim_sha256"]:
        raise RuntimeError(
            f"{name}: claim hash {claim_hash} != {case['claim_sha256']}"
        )
    return {
        "status": "proved",
        "result_sha256": result_hash,
        "claim_sha256": claim_hash,
        "native_label": case["native_label"],
        "source_claim": case["source_claim"],
    }


def proof_command(
    kprove: str,
    source_spec: Path,
    kompiled: Path,
    case: dict[str, Any],
    *,
    dry_root: Path,
    claim_json: Path | None = None,
) -> list[str]:
    command = [
        kprove,
        str(source_spec),
        "-d",
        str(kompiled),
        "-I",
        str(UPSTREAM_DEFINITION),
        "-I",
        str(ROOT / "tests/m3d/fixtures"),
        "--spec-module",
        case["source_module"],
        "--output",
        "json",
        "--claims",
        case["source_claim"],
        "--temp-dir",
        str(dry_root),
    ]
    if claim_json is not None:
        command.extend(["--emit-json-spec", str(claim_json)])
    return command


def cargo(arguments: list[str], environment: dict[str, str]) -> None:
    run_checked(
        [
            "cargo",
            "run",
            "--quiet",
            "--manifest-path",
            str(MANIFEST),
            "--",
            *arguments,
        ],
        environment=environment,
        timeout=300,
    )


def validate_skeleton(path: Path) -> None:
    required = {
        "backend.txt",
        "compiled.bin",
        "definition.kore",
        "mainModule.txt",
        "parsed.json",
        "scanner",
        "syntaxDefinition.kore",
    }
    missing = sorted(name for name in required if not (path / name).is_file())
    if missing:
        raise RuntimeError(f"incomplete Haskell kompiled skeleton: missing {missing}")
    if (path / "backend.txt").read_text(encoding="utf-8").strip() != "haskell":
        raise RuntimeError("kompiled skeleton is not a Haskell definition")
    if (path / "mainModule.txt").read_text(encoding="utf-8").strip() != SEMANTIC_MODULE:
        raise RuntimeError("kompiled skeleton main module does not match native KORE")


def prepare_workspace(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise RuntimeError(f"refusing nonempty workspace {path}")
    path.mkdir(parents=True, exist_ok=True)


def require_tools() -> dict[str, str]:
    tools = {}
    for name in ("kompile", "kprove", "kore-exec"):
        executable = shutil.which(name)
        if executable is None:
            raise RuntimeError(f"required tool {name!r} is not on PATH")
        tools[name] = executable
    version = subprocess.run(
        [tools["kprove"], "--version"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=30,
        check=False,
    )
    if version.returncode != 0 or K_VERSION not in version.stdout:
        raise RuntimeError(f"expected pinned K {K_VERSION}, got {version.stdout.strip()!r}")
    return tools


def read_cases() -> list[dict[str, Any]]:
    value = json.loads(CASES.read_text(encoding="utf-8"))
    cases = value.get("cases")
    if not isinstance(cases, list) or {case.get("name") for case in cases} != {
        "branching",
        "sum-loop",
        "sum-spec",
    }:
        raise RuntimeError("cases.json does not contain exactly the three frozen cases")
    return cases


def stable_environment() -> dict[str, str]:
    environment = os.environ.copy()
    environment["LC_ALL"] = "C"
    environment["LANG"] = "C"
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment.setdefault("CARGO_TARGET_DIR", "/dev/shm/krs-m3d-target")
    environment.setdefault("TMPDIR", "/tmp")
    return environment


def run_checked(
    command: list[str], *, environment: dict[str, str], timeout: int
) -> subprocess.CompletedProcess[str]:
    process = subprocess.run(
        command,
        env=environment,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    if process.stdout:
        print(process.stdout, end="")
    if process.returncode != 0:
        raise RuntimeError(
            f"command failed with rc={process.returncode}: {command!r}\n{process.stderr}"
        )
    return process


if __name__ == "__main__":
    sys.exit(main())

