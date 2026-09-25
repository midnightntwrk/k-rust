//! `NativeValidator` over `testdata/k/counter.k`: kink-patch application
//! followed by k-rust compilation, publishing nothing unless both succeed.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::kompile::CompileOptions;
use kink_native::{IdentityError, MutantRejection, NativeValidator, ValidatedDefinition};
use kink_patch::{Edit, Patch, PatchFailureKind, SentenceOrigin, TermRef, apply};
use serde_json::Value;

fn position(label: &str) -> (String, k_rust::definition::Location) {
    let baseline = support::load("counter.k");
    let at = support::rule(&baseline, label);
    let attrs = baseline.sentence(&at).expect("rule").attributes();
    (
        attrs.source().expect("source").to_owned(),
        attrs.location().expect("location"),
    )
}

fn validator() -> NativeValidator {
    NativeValidator::bind(support::load("counter.k"), CompileOptions::default())
}

/// `increment` with `s(N)` on its right-hand side replaced by `N`.
fn increment_mutant(validator: &NativeValidator) -> Patch {
    let at = |path: &[u32]| {
        TermRef::new(
            support::rule(validator.baseline(), "COUNTER.increment"),
            path,
        )
    };
    let term = |path: &[u32]| validator.baseline().term(&at(path)).expect("term").clone();
    Patch::new(vec![Edit::ReplaceTerm {
        at: at(&[0, 1, 0]),
        expected: term(&[0, 1, 0]),
        replacement: term(&[0, 1, 0, 0]),
    }])
    .expect("one edit")
}

fn identity<'a>(side: &'a ValidatedDefinition, label: &str) -> &'a str {
    let identity = side
        .rule_identity(&position(label).0, position(label).1)
        .unwrap_or_else(|error| panic!("{label}: {error}"));
    assert!(
        side.artifacts()
            .execution_rewrite_order
            .iter()
            .any(|rule| rule == identity),
        "{label} is an executable rule of its side"
    );
    identity
}

#[test]
fn validator_publishes_a_compiled_mutant_only_after_patch_and_compile_succeed() {
    let validator = validator();
    let baseline = validator.compile_baseline().expect("counter.k compiles");
    assert!(baseline.origins().is_none());
    assert_eq!(
        baseline.definition(),
        validator.baseline().definition(),
        "the baseline side compiles the loaded baseline"
    );

    let patch = increment_mutant(&validator);
    let mutant = validator.validate(&patch).expect("the mutant compiles");
    let applied = apply(validator.baseline(), &patch).expect("the patch applies");
    assert_eq!(mutant.definition(), applied.definition());
    assert_eq!(mutant.origins(), Some(applied.origins()));
    assert!(
        mutant
            .origins()
            .expect("mutant origins")
            .values()
            .all(|origin| matches!(origin, SentenceOrigin::Baseline(_))),
        "a replacement keeps every sentence in place"
    );
    assert_eq!(mutant.compile_options(), &CompileOptions::default());
    assert_ne!(
        mutant.artifacts().definition_kore,
        baseline.artifacts().definition_kore,
        "the mutant's KORE is compiled from the patched definition"
    );
}

#[test]
fn compile_rejection_publishes_nothing() {
    let validator = validator();
    let patch = Patch::new(vec![Edit::AddAttribute {
        at: support::rule(validator.baseline(), "COUNTER.increment"),
        key: "foo".to_owned(),
        value: Value::String(String::new()),
    }])
    .expect("one edit");
    assert!(
        apply(validator.baseline(), &patch).is_ok(),
        "kink-patch does not know which attributes k-rust recognizes"
    );
    match validator.validate(&patch) {
        Err(MutantRejection::Compilation(error)) => {
            assert_eq!(error.stage, "definition checks");
            assert!(
                error.diagnostics.iter().any(|diagnostic| diagnostic
                    .message
                    .contains("Unrecognized attributes: [foo]")),
                "{:?}",
                error.diagnostics
            );
        }
        other => panic!("expected a compilation rejection, got {other:?}"),
    }
}

#[test]
fn patch_failure_never_reaches_compilation() {
    let validator = validator();
    let at = TermRef::new(
        support::rule(validator.baseline(), "COUNTER.increment"),
        [0, 1, 0],
    );
    let current = validator.baseline().term(&at).expect("term").clone();
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        at,
        expected: k_rust::kast::Term::apply("z", vec![]),
        replacement: current,
    }])
    .expect("one edit");
    match validator.validate(&patch) {
        Err(MutantRejection::Patch(failure)) => {
            assert_eq!(failure.kind(), PatchFailureKind::StalePrecondition);
        }
        other => panic!("expected a patch rejection, got {other:?}"),
    }
}

/// `UNIQUE_ID` is content-derived: a mutated rule has a different identity
/// on each compiled side, and an untouched rule keeps it.
#[test]
fn rule_identities_resolve_by_source_position_per_compiled_side() {
    let validator = validator();
    let baseline = validator.compile_baseline().expect("counter.k compiles");
    let mutant = validator
        .validate(&increment_mutant(&validator))
        .expect("the mutant compiles");
    assert_ne!(
        identity(&baseline, "COUNTER.increment"),
        identity(&mutant, "COUNTER.increment")
    );
    assert_eq!(
        identity(&baseline, "COUNTER.branch"),
        identity(&mutant, "COUNTER.branch")
    );
    assert_eq!(
        baseline.rule_identity("nonexistent", position("COUNTER.branch").1),
        Err(IdentityError::Missing)
    );

    let deleted = validator
        .validate(
            &Patch::new(vec![Edit::DeleteSentence {
                at: support::rule(validator.baseline(), "COUNTER.fallback"),
            }])
            .expect("one edit"),
        )
        .expect("the mutant without fallback compiles");
    assert_eq!(
        deleted.rule_identity(
            &position("COUNTER.fallback").0,
            position("COUNTER.fallback").1
        ),
        Err(IdentityError::Missing)
    );
}

#[test]
fn position_and_label_name_the_same_compiled_rule() {
    use k_rust::definition::{AttributeKey, Sentence};
    #[rustfmt::skip]
    let rows = ["counter.k", "nd.k", "memory.k", "annotated.k"];
    for fixture in rows {
        let validator = NativeValidator::bind(support::load(fixture), CompileOptions::default());
        let side = validator.compile_baseline().expect("baseline compiles");
        for (_, sentence) in validator.baseline().authored_sentences() {
            if !matches!(sentence, Sentence::Rule { .. }) {
                continue;
            }
            let attrs = sentence.attributes();
            let Some(label) = attrs.string(AttributeKey::Label) else {
                continue;
            };
            let by_position = side
                .rule_identity(
                    attrs.source().expect("source"),
                    attrs.location().expect("location"),
                )
                .expect("position id");
            let by_label = side
                .artifacts()
                .execution_definition
                .modules
                .iter()
                .flat_map(|module| &module.local_sentences)
                .filter(|candidate| {
                    matches!(***candidate, Sentence::Rule { .. })
                        && candidate.attributes().string(AttributeKey::Label) == Some(label)
                })
                .map(|candidate| candidate.attributes().string(AttributeKey::UniqueId))
                .next()
                .flatten()
                .expect("label id");
            assert_eq!(by_position, by_label, "{fixture}: {label}");
        }
    }
}
