#!/usr/bin/env python3
"""Fail closed when the tour's proof/outcome evidence drifts."""

from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[2]


class EvidenceError(RuntimeError):
    pass


def text(relative: str) -> str:
    return (ROOT / relative).read_text(encoding="utf-8")


def require_fragments(relative: str, *fragments: str) -> str:
    value = text(relative)
    missing = [fragment for fragment in fragments if fragment not in value]
    if missing:
        raise EvidenceError(f"{relative} is missing evidence: {missing!r}")
    return value


def verify_undefined_partial() -> None:
    source = require_fragments(
        "tests/m4/rust-definition/src/static_adjunct.rs",
        "#[k::function(partial, sort = Int, syntax = \"#m3dPositive({value})\")]",
        "fn m3d_positive(k::term![M3dPositive(value)]: Term<Int>) -> Term<Int>",
        "#[k::requires(int::le(0, value))]",
    )
    if len(re.findall(r"k::term!\[M3dPositive\(", source)) != 1:
        raise EvidenceError("M3dPositive no longer has exactly one authored equation")

    pins = json.loads(text("tests/m4/pins.json"))
    outcome = pins.get("proof_outcomes", {}).get("partial-equation", {})
    if outcome.get("status") != "proved" or outcome.get("frontier_count") != 0:
        raise EvidenceError("M4's defined partial-function claim is no longer proved")

    require_fragments(
        "docs-site/src/pages/semantics/static-semantics.mdx",
        "#m3dPositive(-1)",
        "the application has no denotation: semantic bottom",
        "not a claimed `krun` trace",
    )


def verify_stuck_state() -> None:
    if text("tests/m3b/corpus/rejected/semantic/undefined-variable.calc") != "y = x + 1;\n":
        raise EvidenceError("M3B's documented stuck program changed")
    require_fragments(
        "tests/m3b/verify.py",
        'expectations = {"undefined-variable.calc": 2, "type-error.calc": 1}',
        "if final_environment_if_complete(term) is not None:",
        'raise RuntimeError(f"semantic rejection unexpectedly completed for {name}")',
    )
    pins = json.loads(text("tests/m3b/pins.json"))
    aggregate = pins.get("rejection_sha256", {}).get("stuck_state_aggregate")
    if not isinstance(aggregate, str) or not re.fullmatch(r"[0-9a-f]{64}", aggregate):
        raise EvidenceError("M3B's stuck-state aggregate pin is absent")
    require_fragments(
        "docs-site/src/pages/semantics/applicability-and-failure.mdx",
        "`y = x + 1;` from M3B",
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
        raise EvidenceError(f"KWasm trap corpus differs: {traps!r}")
    require_fragments(
        "tests/kwasm/native.py",
        'return {"id": str(case["id"]), "outcome": "trap"}',
        'raise NativeError(f"{case[\'id\']} trapped with an unexpected stack")',
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
        raise EvidenceError("Krs.lock no longer pins the LLVM existential policy")

    pins = json.loads(text("tests/m4/pins.json"))
    digest = pins.get("native_comparison", {}).get("llvm_failure_sha256")
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise EvidenceError("M4's LLVM failure transcript hash is absent")

    probe = subprocess.run(
        [sys.executable, ROOT / "tests/m4/compatibility/diagnostics/backend-capability/probe.py"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if probe.returncode != 0:
        raise EvidenceError(f"backend static probe failed: {probe.stderr.strip()}")
    report = json.loads(probe.stdout)
    expected_true = {
        "adapter_structured_diagnostic",
        "cli_structured_diagnostic_envelope",
        "cli_authored_origin_translation",
        "cli_structured_diagnostic_rendering",
    }
    if any(report.get(key) is not True for key in expected_true):
        raise EvidenceError(f"backend static diagnostic seam is incomplete: {report!r}")

    require_fragments(
        "tests/m4/compatibility/diagnostics/backend-capability/probe.py",
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
    claims = text("tests/m4/rust-definition/src/claims.rs")
    if claims.count("#[k::claim(all_paths") != 20:
        raise EvidenceError("M4 no longer has the matrix's 20 all-path claims")
    if claims.count("#[k::exists(") != 6 or claims.count("circularity)]") != 2:
        raise EvidenceError("M4 existential or circular claim coverage differs")

    pins = json.loads(text("tests/m4/pins.json"))
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
            raise EvidenceError(f"M4 proof outcome differs for {label}: {outcome!r}")
        if outcome.get("bounds") != {"branching_allowed": 64, "depth": 100}:
            raise EvidenceError(f"M4 proof bounds differ for {label}")

    require_fragments(
        "tests/kwasm/verify.py",
        '"--backend",\n            "haskell"',
        'k_bin / "kprove"',
        'if proof.stdout.strip() != "#Top":',
        '"1 reference proof deferred to --java-reference"',
    )
    require_fragments(
        "crates/krs-syntax/tests/claims.rs",
        'r#"one_path, label = "circular", circularity"#',
    )
    require_fragments(
        "crates/krs-compiler/tests/m3c_lowering.rs",
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
    except (EvidenceError, OSError, json.JSONDecodeError, tomllib.TOMLDecodeError) as error:
        print(f"FAIL tour proof evidence: {error}", file=sys.stderr)
        raise SystemExit(1)
