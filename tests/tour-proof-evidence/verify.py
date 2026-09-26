#!/usr/bin/env python3
"""Fail closed when the tour's proof/outcome evidence drifts."""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from support.process import run  # noqa: E402


def text(relative: str) -> str:
    return (ROOT / relative).read_text(encoding="utf-8")


def require_fragments(relative: str, *fragments: str) -> str:
    value = text(relative)
    missing = [fragment for fragment in fragments if fragment not in value]
    if missing:
        raise GateError(f"{relative} is missing evidence: {missing!r}")
    return value


def verify_undefined_partial() -> None:
    source = require_fragments(
        "tests/imp/rust-definition/src/static_adjunct.rs",
        "#[k::function(partial, sort = Int, syntax = \"#nonnegativeIdentity({value})\")]",
        "fn nonnegative_identity(k::term![NonnegativeIdentity(value)]: Term<Int>) -> Term<Int>",
        "#[k::requires(int::le(0, value))]",
    )
    if len(re.findall(r"k::term!\[NonnegativeIdentity\(", source)) != 1:
        raise GateError("NonnegativeIdentity no longer has exactly one authored equation")

    pins = json.loads(text("tests/imp/pins.json"))
    outcome = pins.get("proof_outcomes", {}).get("partial-equation", {})
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
    require_fragments(
        "tests/imp-state/verify.py",
        'expectations = {"undefined-variable.calc": 2, "type-error.calc": 1}',
        "if final_environment_if_complete(term) is not None:",
        'raise RuntimeError(f"semantic rejection unexpectedly completed for {name}")',
    )
    pins = json.loads(text("tests/imp-state/pins.json"))
    aggregate = pins.get("rejection_sha256", {}).get("stuck_state_aggregate")
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
        if case.get("expected_outcome") == "trap"
    }
    expected = {
        "i32-div-u-zero": "i32.const 7 ; i32.const 0 ; i32.div_u ; .Instrs",
        "i64-div-u-zero": "i64.const 7 ; i64.const 0 ; i64.div_u ; .Instrs",
    }
    if traps != expected:
        raise GateError(f"KWasm trap corpus differs: {traps!r}")
    require_fragments(
        "tests/kwasm/native.py",
        'return {"id": str(case["id"]), "outcome": "trap"}',
        'raise GateError(f"{case[\'id\']} trapped with an unexpected stack")',
    )
    require_fragments(
        "docs-site/src/pages/semantics/applicability-and-failure.mdx",
        "`i32.const 7 ; i32.const 0 ; i32.div_u ; .Instrs` from KWasm",
        "`trap ~> .Instrs ~> .K` with an empty value stack",
        "`Instruction::Trap` constructor",
    )


def verify_backend_rejection() -> None:
    lock = tomllib.loads(text("Krs.lock"))
    if lock.get("backend_policy", {}).get("llvm_existential_claims") != (
        "typed-backend-capability-error"
    ):
        raise GateError("Krs.lock no longer pins the LLVM existential policy")

    pins = json.loads(text("tests/imp/pins.json"))
    digest = pins.get("native_comparison", {}).get("llvm_failure_sha256")
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise GateError("IMP's LLVM failure transcript hash is absent")

    probe = run(
        [sys.executable, ROOT / "tests/imp/compatibility/diagnostics/backend-capability/probe.py"],
        check=False,
    )
    if probe.returncode != 0:
        raise GateError(f"backend static probe failed: {probe.stderr.strip()}")
    report = json.loads(probe.stdout)
    expected_true = {
        "adapter_structured_diagnostic",
        "cli_structured_diagnostic_envelope",
        "cli_authored_origin_translation",
        "cli_structured_diagnostic_rendering",
    }
    if any(report.get(key) is not True for key in expected_true):
        raise GateError(f"backend static diagnostic seam is incomplete: {report!r}")

    require_fragments(
        "tests/imp/compatibility/diagnostics/backend-capability/probe.py",
        'EXPECTED_LABELS = {',
        'envelope.get("stage") != "backend-capability"',
        'envelope.get("code") != "UnsupportedExistentialVariable"',
        '"partial_artifacts_absent": artifacts_absent',
    )
    require_fragments(
        "docs-site/src/pages/semantics/applicability-and-failure.mdx",
        "six deduplicated schema-1 `backend-capability` / `UnsupportedExistentialVariable` envelopes",
        "creates no partial artifacts",
    )


def verify_capability_matrix() -> None:
    claims = text("tests/imp/rust-definition/src/claims.rs")
    if claims.count("#[k::claim(all_paths") != 20:
        raise GateError("IMP no longer has the matrix's 20 all-path claims")
    if claims.count("#[k::exists(") != 6 or claims.count("circularity)]") != 2:
        raise GateError("IMP existential or circular claim coverage differs")

    pins = json.loads(text("tests/imp/pins.json"))
    outcomes = pins.get("proof_outcomes", {})
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

    require_fragments(
        "tests/kwasm/verify.py",
        "semantics.reference_definition(",
        'semantics.reference_proof(PORT, workspace, definition, source, claims, k["kprove"])',
        '"1 reference proof deferred to --java-reference"',
    )
    require_fragments(
        "tests/support/semantics.py",
        '"--backend", "haskell"',
        'if proof.stdout.strip() != "#Top":',
    )
    require_fragments(
        "crates/krs-syntax/tests/claims.rs",
        'r#"one_path, label = "circular", circularity"#',
    )
    require_fragments(
        "crates/krs-compiler/tests/control_flow_lowering.rs",
        "ClaimModality::OnePath",
        'assert!(source.contains("[one-path]"), "{source}")',
    )
    require_fragments(
        "docs-site/src/pages/verification/reachability-claims.mdx",
        "| Claim form | Collection and emitted K | Haskell route | LLVM route |",
        "All-path, without existential binders",
        "including a proved `addition-1` claim",
        "only when its gate receives `--java-reference`",
        "All-path with existential results, anonymous values, or `ensures`",
        "Circular all-path",
        "| One-path | Accepted by parsing, lowering, and emission.",
        "there is no `krs prove` or `krs run` command",
    )


def main() -> int:
    verify_undefined_partial()
    verify_stuck_state()
    verify_authored_trap()
    verify_backend_rejection()
    verify_capability_matrix()
    print(
        "PASS tour proof evidence: undefined partial, stuck state, authored trap, "
        "backend rejection, and capability matrix"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (GateError, OSError, json.JSONDecodeError, tomllib.TOMLDecodeError) as error:
        print(f"FAIL tour proof evidence: {error}", file=sys.stderr)
        raise SystemExit(1)
