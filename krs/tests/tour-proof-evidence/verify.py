#!/usr/bin/env python3
"""Fail closed when the tour's proof/outcome evidence drifts."""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import z3_environment  # noqa: E402


def text(relative: str) -> str:
    return (ROOT / relative).read_text(encoding="utf-8")


def require_fragments(relative: str, *fragments: str) -> str:
    value = text(relative)
    missing = [fragment for fragment in fragments if fragment not in value]
    if missing:
        raise GateError(f"{relative} is missing evidence: {missing!r}")
    return value


def require_named_tests(package: str, target: tuple[str, ...], *expected: str) -> None:
    """Require one Rust test binary to list every `expected` test name.

    Cargo builds the binary, so the qualified Z3 library must be available.
    """

    listed = run(
        ["cargo", "+stable", "test", "--locked", "-p", package, *target, "--", "--list"],
        cwd=ROOT,
        environment=z3_environment(),
        timeout=1800,
    )
    names = {
        line.removesuffix(": test")
        for line in listed.stdout.splitlines()
        if line.endswith(": test")
    }
    missing = sorted(set(expected) - names)
    if missing:
        raise GateError(f"{package} {' '.join(target)} is missing named tests: {missing!r}")


def require_sha256_pin(pins: Ledger, key: str) -> None:
    digest = pins.get(key)
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise GateError(f"{pins.path.name} {key} output pin is absent")


def verify_undefined_partial() -> None:
    source = require_fragments(
        "tests/imp/rust-definition/src/static_adjunct.rs",
        "#[k::function(partial, sort = Int, syntax = \"#nonnegativeIdentity({value})\")]",
        "fn nonnegative_identity(k::term![NonnegativeIdentity(value)]: Term<Int>) -> Term<Int>",
        "#[k::requires(int::le(0, value))]",
    )
    if len(re.findall(r"k::term!\[NonnegativeIdentity\(", source)) != 1:
        raise GateError("NonnegativeIdentity no longer has exactly one authored equation")

    pins = Ledger(ROOT / "tests/imp/pins.json")
    outcome = pins.table("proof_outcomes").get("partial-equation", {})
    if outcome.get("status") != "proved" or outcome.get("frontier_count") != 0:
        raise GateError("IMP's defined partial-function claim is no longer proved")

    require_fragments(
        "docs-site/src/pages/semantics/static-semantics.mdx",
        "#nonnegativeIdentity(-1)",
        "the application has no denotation: semantic bottom",
        "not a claimed `krun` trace",
    )


def verify_stuck_state() -> None:
    if text("tests/imp-state/corpus/rejected/semantic/undefined-variable.calc") != "y = x + 1;\n":
        raise GateError("IMP state's documented stuck program changed")
    pins = Ledger(ROOT / "tests/imp-state/pins.json")
    aggregate = pins.table("rejection_sha256").get("stuck_state_aggregate")
    if not isinstance(aggregate, str) or not re.fullmatch(r"[0-9a-f]{64}", aggregate):
        raise GateError("IMP state's stuck-state aggregate pin is absent")
    require_fragments(
        "docs-site/src/pages/semantics/applicability-and-failure.mdx",
        "`y = x + 1;` in the checked IMP stuck-state fixture",
        "LLVM performs two rewrites",
        "leaves a non-final configuration",
    )


def verify_authored_trap() -> None:
    require_fragments(
        "semantics/kwasm/src/lib.rs",
        '#[k::syntax("trap")]\n    Trap(),',
        "fn div_u_zero(",
        "k::term![Value::Undefined()]",
        "undefined_traps:",
        "instrs: [Trap(), ..]",
    )
    corpus = tomllib.loads(text("tests/kwasm/corpus.toml"))
    traps = {
        case.get("id"): case.get("program")
        for case in corpus.get("behavior", [])
        if case.get("expect", {}).get("instrs") == "trap ~> .Instrs"
    }
    expected = {
        "i32-div-u-zero": "i32.const 7 ; i32.const 0 ; i32.div_u ; .Instrs",
        "i64-div-u-zero": "i64.const 7 ; i64.const 0 ; i64.div_u ; .Instrs",
    }
    if traps != expected:
        raise GateError(f"KWasm trap corpus differs: {traps!r}")
    require_sha256_pin(Ledger(ROOT / "tests/kwasm/pins.toml"), "behavior_sha256")
    require_fragments(
        "docs-site/src/pages/semantics/applicability-and-failure.mdx",
        "`i32.const 7 ; i32.const 0 ; i32.div_u ; .Instrs` from KWasm",
        "`trap ~> .Instrs ~> .K` with an empty value stack",
        "`Instruction::Trap` constructor",
    )


def verify_llvm_claim_omission() -> None:
    lock = tomllib.loads(text("Krs.lock"))
    if lock.get("backend_policy", {}).get("llvm_claims") != "omitted":
        raise GateError("Krs.lock no longer pins the LLVM claim-omission policy")

    pins = Ledger(ROOT / "tests/imp/pins.json")
    llvm = pins.table("llvm_artifact_sha256")
    if set(llvm) != {".krs-artifacts", "definition.kore", "macros.kore", "syntaxDefinition.kore"} or not all(
        isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) for digest in llvm.values()
    ):
        raise GateError("IMP's claim-free LLVM artifacts are not pinned")

    require_named_tests(
        "krs-k-rust",
        ("--lib",),
        "tests::only_the_haskell_backend_proves_claims",
        "provenance::tests::llvm_compilation_omits_claims_and_keeps_provenance_consistent",
    )
    require_fragments(
        "docs-site/src/pages/verification/reachability-claims.mdx",
        "`krs build --backend llvm` omits every claim from its KORE and reports how many it omitted",
    )


def verify_capability_matrix() -> None:
    claims = text("tests/imp/rust-definition/src/claims.rs")
    if claims.count("#[k::claim(all_paths") != 20:
        raise GateError("IMP no longer has the matrix's 20 all-path claims")
    if claims.count("#[k::exists(") != 6 or claims.count("circularity)]") != 2:
        raise GateError("IMP existential or circular claim coverage differs")

    pins = Ledger(ROOT / "tests/imp/pins.json")
    outcomes = pins.table("proof_outcomes")
    expected = {
        "addition-1": ("proved", 0),
        "branching": ("proved", 0),
        "sum-spec": ("proved", 0),
        "two-sum-spec": ("incomplete", 1),
    }
    for label, (status, frontier_count) in expected.items():
        outcome = outcomes.get(label, {})
        if (outcome.get("status"), outcome.get("frontier_count")) != (
            status,
            frontier_count,
        ):
            raise GateError(f"IMP proof outcome differs for {label}: {outcome!r}")
        if outcome.get("bounds") != {"branching_allowed": 64, "depth": 100}:
            raise GateError(f"IMP proof bounds differ for {label}")

    if text("semantics/kwasm/src/lib.rs").count("#[k::claim(all_paths") != 1:
        raise GateError("KWasm no longer has exactly one authored all-path claim")
    require_sha256_pin(Ledger(ROOT / "tests/kwasm/pins.toml"), "definition_kore_sha256")
    help_output = run([sys.executable, "tests/kwasm/verify.py", "--help"], cwd=ROOT)
    if "--java-reference" not in help_output.stdout:
        raise GateError("KWasm gate help does not name --java-reference")
    require_named_tests(
        "krs-syntax",
        ("--test", "claims"),
        "claim_metadata_rejects_missing_duplicate_and_incompatible_modalities",
    )
    require_named_tests(
        "krs-compiler",
        ("--test", "control_flow_lowering"),
        "context_alias_and_claim_adjuncts_lower_emit_and_map_every_distinct_role",
    )
    require_fragments(
        "docs-site/src/pages/verification/reachability-claims.mdx",
        "| Claim form | Collection and emitted K | Haskell route |",
        "All-path, without existential binders",
        "including a proved `addition-1` claim",
        "only when its gate receives `--java-reference`",
        "All-path with existential results, anonymous values, or `ensures`",
        "Circular all-path",
        "| One-path | Accepted by parsing, lowering, and emission.",
        "`krs prove` proves the same claims in-process with the k-rust backend",
    )


def main() -> int:
    verify_undefined_partial()
    verify_stuck_state()
    verify_authored_trap()
    verify_llvm_claim_omission()
    verify_capability_matrix()
    print(
        "PASS tour proof evidence: undefined partial, stuck state, authored trap, "
        "LLVM claim omission, and capability matrix"
    )
    return 0


if __name__ == "__main__":
    entry(
        "tour proof evidence",
        main,
        errors=(OSError, json.JSONDecodeError, tomllib.TOMLDecodeError),
    )
