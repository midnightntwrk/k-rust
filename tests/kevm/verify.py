#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KEVM operational slice."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
import tempfile
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, semantics  # noqa: E402
from support.kdefinition import parse_kore_pattern  # noqa: E402
from support.lock import k_version, krs_ir_schema  # noqa: E402
from support.pins import Ledger, load_toml  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool, scratch_root  # noqa: E402
from kevm import native  # noqa: E402


PORT = semantics.Port(
    label="KEVM",
    key="kevm",
    checkout=ROOT.parent / "inspirations/runtimeverification/evm-semantics",
    descriptors=1100,
    clippy_allow=("clippy::too_many_arguments",),
    hook_namespaces=("KRYPTO",),
)
CLAIM_COUNT = 8

# Cases the pinned Haskell backend (kore-exec 0.1.155, K 7.1.337) cannot execute
# concretely. The K-Rust route still executes them; the Java reference route
# skips them and compares the remaining cases with native outcomes.
_NO_HOOK = "the Haskell backend implements no {} hook"
_KECCAK = "the Haskell backend's KRYPTO.keccak256raw result is rejected by BYTES.length"
HASKELL_BACKEND_GAPS: Mapping[str, str] = {
    "sha3-empty": _KECCAK,
    "sha3-abc-with-expansion": _KECCAK,
    "extcodehash-code-nonempty-cold": _KECCAK,
    "extcodehash-nonce-nonempty-warm": _KECCAK,
    "extcodehash-balance-nonempty-cold": _KECCAK,
    "staticcall-ecrec-precompile-success": _KECCAK,
    "staticcall-ecrec-precompile-invalid-signature": (
        "the Haskell backend's KRYPTO.ecdsaRecover fails an internal assertion"
    ),
    "staticcall-sha256-precompile-success": _NO_HOOK.format("KRYPTO.sha256raw"),
    "staticcall-ripemd160-precompile-success": _NO_HOOK.format("KRYPTO.ripemd160raw"),
    **{
        f"staticcall-{case}": _NO_HOOK.format("KRYPTO.bn128valid")
        for case in (
            "ecadd-precompile-success",
            "ecadd-precompile-empty-input-infinity",
            "ecadd-precompile-invalid-point",
            "ecadd-precompile-out-of-gas",
            "ecmul-precompile-generator-times-two",
            "ecmul-precompile-zero-scalar-infinity",
            "ecmul-precompile-invalid-point",
            "ecmul-precompile-out-of-gas",
            "ecpairing-precompile-generator-is-not-identity",
            "ecpairing-precompile-invalid-g1",
            "ecpairing-precompile-invalid-g2",
            "ecpairing-precompile-out-of-gas",
        )
    },
    "staticcall-ecpairing-precompile-empty-input": _NO_HOOK.format("KRYPTO.bn128ate"),
}


def definition_checks(readable: str) -> None:
    """Require the emitted definition to use the builtin Bytes surface."""

    if "  imports BYTES\n" not in readable:
        raise GateError("emitted KEVM definition does not import pinned BYTES")
    if "lengthBytes(" not in readable:
        raise GateError("emitted KEVM definition omits functional lengthBytes syntax")
    if re.search(r"V[0-9A-F]+:Bytes \[ V[0-9A-F]+:Int \]", readable) is None:
        raise GateError("emitted KEVM definition omits builtin byte lookup syntax")
    if "EvmProgram" in readable:
        raise GateError("emitted KEVM definition retained the structured program adapter")


def java_reference_gate(
    workspace: Path,
    artifacts: Path,
    k: Mapping[str, str],
    pins: Ledger,
    corpus: Mapping[str, Any],
    native_outcomes: list[dict[str, Any]],
) -> int:
    definition, source, claims = semantics.reference_definition(
        PORT, workspace, artifacts, k["kompile"], CLAIM_COUNT, pins
    )
    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    outcomes: list[dict[str, str]] = []
    for case in behavior:
        if str(case["id"]) in HASKELL_BACKEND_GAPS:
            continue
        # Every variable except $PGM, which the configuration declares at sort
        # K, is passed as the KORE value the native route builds. Both routes
        # then start from the same configuration, and krun spawns no kparse JVM
        # per variable (kparse also exhausts an 8 GiB heap on the 256-entry
        # block-hash List).
        variables = [entry for entry in native.configuration(case) if entry[0] != "PGM"]
        result = run(
            [
                k["krun"], "--definition", definition, "-cPGM=run",
                *(f"-c{name}={value}" for name, _, value in variables),
                *(f"-p{name}=cat" for name, _, _ in variables),
                "--output", "kore",
            ],
            timeout=120,
        ).stdout
        state = parse_kore_pattern(result)
        outcomes.append(native.observed(case, state))

    semantics.compare_routes(PORT.label, native_outcomes, outcomes, HASKELL_BACKEND_GAPS)
    cases_by_id = {str(case["id"]): case for case in behavior}
    for outcome in outcomes:
        native.checked(cases_by_id[str(outcome["id"])], outcome)

    semantics.reference_proof(PORT, workspace, definition, source, claims, k["kprove"])
    return CLAIM_COUNT


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--java-reference",
        action="store_true",
        help="run the expensive pinned Java behavior and proof authority gate",
    )
    parser.add_argument(
        "--record",
        action="store_true",
        help="run the gate and rewrite the output pins it measured",
    )
    semantics.add_artifacts_only_argument(parser)
    arguments = parser.parse_args()
    semantics.reject_artifacts_only_conflicts(parser, arguments)
    try:
        pins = Ledger(PORT.pins_path, record=arguments.record, artifacts_only=arguments.artifacts_only)
        corpus = load_toml(PORT.corpus_path)
        environment = semantics.preflight(PORT, pins, corpus)
        krs, compiler, runner = semantics.rust_gate(PORT, environment)
        with tempfile.TemporaryDirectory(prefix="krs-kevm-", dir=scratch_root()) as temporary:
            workspace = Path(temporary)
            artifacts = semantics.artifact_gate(PORT, workspace, krs, pins, environment)
            definition_checks((artifacts / "definition.k").read_text(encoding="utf-8"))
            if arguments.artifacts_only:
                semantics.native_definition(workspace, artifacts, compiler, pins, environment)
                print(f"PASS readable KEVM operational slice: {semantics.artifacts_only_summary(PORT)}")
                return 0
            definition = semantics.native_definition(
                workspace, artifacts, compiler, pins, environment
            )
            executions, native_outcomes = semantics.native_behavior(
                PORT, runner, definition, pins, corpus, environment
            )
            proofs = 0
            if arguments.java_reference:
                k = {name: k_tool(name, k_version()) for name in ("kompile", "krun", "kprove")}
                proofs = java_reference_gate(workspace, artifacts, k, pins, corpus, native_outcomes)
            proof_status = (
                f"{proofs} Java reference proofs"
                if arguments.java_reference
                else f"{CLAIM_COUNT} Java reference proofs deferred to --java-reference"
            )
            qualification = f"{executions} K-Rust executions; {proof_status}"
        pins.finish("readable KEVM operational slice")
        print(
            f"PASS readable KEVM operational slice: {PORT.descriptors} descriptors; {qualification}; "
            f"KRS schema {krs_ir_schema()}; K {k_version()}"
        )
        return 0
    except (GateError, OSError) as error:
        print(f"FAIL readable KEVM operational slice: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
