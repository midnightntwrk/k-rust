#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KEVM operational slice."""

from __future__ import annotations

from pathlib import Path
import re
import sys
from typing import Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, semantics, entry  # noqa: E402
from support.lock import k_version, krs_ir_schema  # noqa: E402
from kevm import native  # noqa: E402


PROBES = (
    (
        "program lookup",
        "k: [crate::Lookup { program, pc }, ..]",
        "Lookup",
        "pub struct Lookup {",
    ),
    (
        "stack result constructor",
        "word_stack: Stack::StackCons(crate::Chop(value), stack)",
        "StackCons",
        "    StackCons { head: Int, tail: WordStack },",
    ),
    (
        "push preparation function",
        "k: [crate::PreparePush { op: Operation::Push { width, value }, stack, gas, cost: 3 }, ..]",
        "PreparePush",
        "pub struct PreparePush {",
    ),
    (
        "configuration target",
        "    for Machine;",
        "Machine",
        "pub struct Machine {",
    ),
    (
        "width binding",
        "pc: int::add(pc, int::add(width, 1))",
        "width",
        "k: [GasResult::EnoughGas(Operation::Push { width, value }, remaining), ..]",
    ),
    (
        "exception constructor",
        "status_code: Status::OutOfGas()",
        "OutOfGas",
        "    OutOfGas(),",
    ),
)


PORT = semantics.Port(
    label="KEVM",
    key="kevm",
    checkout=ROOT.parent / "inspirations/runtimeverification/evm-semantics",
    descriptors=1100,
    clippy_allow=("clippy::too_many_arguments",),
    hook_namespaces=("KRYPTO",),
    lsp_probes=PROBES,
    lsp_diagnostic_timeout=600,
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


def krun_arguments(case: dict) -> list[str]:
    """Build the KEVM KORE configuration for the Java route."""

    # Every variable except $PGM, which the configuration declares at sort
    # K, is passed as the KORE value the native route builds. Both routes
    # then start from the same configuration, and krun spawns no kparse JVM
    # per variable (kparse also exhausts an 8 GiB heap on the 256-entry
    # block-hash List).
    variables = [entry for entry in native.configuration(case) if entry[0] != "PGM"]
    return [
        "-cPGM=run",
        *(f"-c{name}={value}" for name, _, value in variables),
        *(f"-p{name}=cat" for name, _, _ in variables),
    ]


def summary(port: semantics.Port, executions: int, proofs: int, java_reference: bool) -> str:
    proof_status = (
        f"{proofs} Java reference proofs"
        if java_reference
        else f"{CLAIM_COUNT} Java reference proofs deferred to --java-reference"
    )
    return (
        f"{port.descriptors} descriptors; {executions} K-Rust executions; {proof_status}; "
        f"KRS schema {krs_ir_schema()}; K {k_version()}"
    )


HOOKS = semantics.Hooks(
    description=__doc__,
    label="readable KEVM operational slice",
    java_help="run the expensive pinned Java behavior and proof authority gate",
    claim_count=CLAIM_COUNT,
    krun_arguments=krun_arguments,
    observed=native.observed,
    checked=native.checked,
    summary=summary,
    definition_checks=definition_checks,
    java_skips=HASKELL_BACKEND_GAPS,
)


def main() -> int:
    return semantics.run_port(PORT, HOOKS)


if __name__ == "__main__":
    entry(HOOKS.label, main, errors=(OSError,))
