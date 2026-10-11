//! Proof semantics on the KORE krust compiles, checked in-process.
//!
//! What a claim's proof concludes is the backend's contract: the prover's result for a claim of a
//! compiled definition. `cli.rs` checks how `krust kprove` reports these results (verdict lines,
//! exit status) on the same definitions (`support/proof_sources.rs`); the tests here compile each
//! definition as `kprove` does and ask the backend for the result directly, so a change to what
//! the prover concludes fails here, in the backend's terms, and not only through the rendering.

use k_rust::{
    backend::{Backend, BackendOptions, ProofResultOutput, ProveRequest},
    builtin::embedded,
    definition::CheckMode,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{codec, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

#[path = "support/proof_sources.rs"]
mod proof_sources;
use proof_sources::{
    ANYWHERE_OVERLOAD_REMAINDER, LATER_BINDING_RULE, LET_PARTIAL_CONDITION, UNDEFINED_STEP,
};

/// The KORE of `source` compiled for proving `spec` against `definition`, as `kprove` compiles a
/// source: the prelude, the Rust backend's module selection, and claims all-path by default.
fn compile(source: &str, spec: &str, definition: &str) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("spec.k", source),
        spec,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            configuration_module: Some(definition.to_owned()),
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Rust,
            default_claims_to_all_path: true,
            check_mode: CheckMode::Proof {
                definition_module: definition.to_owned(),
            },
            ..CompileOptions::default()
        },
    )
    .unwrap()
    .definition_kore
}

/// The prover's result for the claim `claim` (a label or `#index`) of `spec`.
fn prove(kore: &str, spec: &str, claim: &str, request: ProveRequest) -> ProofResultOutput {
    let mut backend = Backend::new(kore, spec, BackendOptions::default()).unwrap();
    backend
        .prove(ProveRequest {
            claim: Some(claim.to_owned()),
            ..request
        })
        .unwrap_or_else(|error| panic!("{claim}: {error:?}"))
}

fn leaf_text(result: &ProofResultOutput) -> Vec<String> {
    result
        .leaves
        .iter()
        .map(|leaf| Printer::compact().print_pattern(&codec::from_value(&leaf.state).unwrap()))
        .collect()
}

/// A lower-priority rule applies to the remainder of a step as the remainder simplifies, not to
/// the step's subject: the priority-10 rule covers `N <= 0`, and on the remainder `N > 0` the
/// anywhere equation turns `app(N, 0)` into `c(N)`, which the `c` rule rewrites. So the claim
/// is proven in three states whether the overloaded item heads `<k>` or follows another item.
#[test]
fn a_lower_priority_rule_applies_to_the_simplified_remainder() {
    for next in ["", "mark() ~>"] {
        let kore = compile(
            &ANYWHERE_OVERLOAD_REMAINDER.replace("$NEXT", next),
            "OVL-SPEC",
            "OVL",
        );
        let result = prove(&kore, "OVL-SPEC", "#0", ProveRequest::default());
        assert_eq!(
            (
                result.status.as_str(),
                result.explored_states,
                result.unexplored_states
            ),
            ("proven", 3, 0),
            "next item {next:?}: {result:?}"
        );
    }
}

/// The rule binds `X` only in a later argument (`c(X, Y)` is matched against `f(A)`, which no
/// equation evaluates), so the step's condition over `X` is stated under the binding the match
/// leaves, and the claim fails on a `bar` leaf that names no rule variable and no existential.
#[test]
fn a_rule_condition_over_a_later_binding_is_stated_under_it() {
    let kore = compile(LATER_BINDING_RULE, "RULESOLVED-SPEC", "RULESOLVED");
    let result = prove(
        &kore,
        "RULESOLVED-SPEC",
        "RULESOLVED-SPEC.main",
        ProveRequest {
            max_counterexamples: 5,
            ..ProveRequest::default()
        },
    );
    assert_eq!(result.status, "failed", "{result:?}");
    let leaves = leaf_text(&result).join("\n");
    assert!(leaves.contains("Lblbar"), "{leaves}");
    assert!(!leaves.contains("RuleVar"), "{leaves}");
    assert!(!leaves.contains(r"\exists"), "{leaves}");
}

/// `10 /Int A` is undefined at `A = 0`, where the ground claim is disproved, so the symbolic
/// claim, which holds for every instance, is not proven, whether the division is bound by
/// `#let` or not.
#[test]
fn a_let_bound_partial_condition_keeps_its_definedness() {
    for (case, condition) in [
        ("plain", "10 /Int A <=Int 10 /Int A"),
        (
            "let",
            "(#let Y = A #in 10 /Int Y) <=Int (#let Y = A #in 10 /Int Y)",
        ),
    ] {
        let kore = compile(
            &LET_PARTIAL_CONDITION.replace("$CONDITION", condition),
            "LETDIV-SPEC",
            "LETDIV",
        );
        let status =
            |claim: &str| prove(&kore, "LETDIV-SPEC", claim, ProveRequest::default()).status;
        assert_ne!(status("LETDIV-SPEC.symbolic"), "proven", "{case}");
        assert_eq!(status("LETDIV-SPEC.ground"), "disproved", "{case}");
    }
}

/// A claim holds for every instance of its left-hand side, so a symbolic claim is not proven
/// while one of its instances ends in an undefined step (`apart(0, 0)`, whose `ensures` fails),
/// and allowing vacuous results accepts every claim. An instance a sibling rule takes to a
/// defined result (`cover`) and an `ensures` that always has a witness (`fresh`) leave no
/// undefined step. One-path, the instances where a rule applies but its result is undefined go to
/// the later rules of the same priority (`cover`, `skip` proven), never to a lower priority
/// (`low` fails), and fail where no rule of the priority gives a defined result (`pick`).
#[test]
fn a_claim_fails_on_the_instances_a_rule_leaves_undefined() {
    let kore = compile(UNDEFINED_STEP, "UNDEF-SPEC", "UNDEF");
    let status = |claim: &str, allow_vacuous: bool| {
        prove(
            &kore,
            "UNDEF-SPEC",
            &format!("UNDEF-SPEC.{claim}"),
            ProveRequest {
                allow_vacuous,
                ..ProveRequest::default()
            },
        )
    };
    for claim in [
        "sym", "gnd", "sym-one", "pick", "pick-one", "low-one", "low",
    ] {
        let result = status(claim, false);
        assert_eq!(result.status, "failed", "{claim}: {result:?}");
        assert!(
            result
                .leaves
                .iter()
                .any(|leaf| leaf.outcome.contains("Trivial")),
            "{claim}: {result:?}"
        );
        assert_eq!(
            status(claim, true).status,
            "proven",
            "{claim} allowing vacuous results"
        );
    }
    for claim in [
        "defined",
        "cover",
        "fresh",
        "fresh-one",
        "cover-one",
        "skip-one",
        "skip",
    ] {
        assert_eq!(status(claim, false).status, "proven", "{claim}");
    }
}
