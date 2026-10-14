//! `NativeValidator` over `testdata/k/counter.k`: kink-patch application
//! followed by k-rust compilation, publishing nothing unless both succeed.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::kompile::{CompileOptions, compile_loaded_definition};
use kink_native::{MutantRejection, NativeValidator};
use kink_patch::{Edit, Patch, PatchFailureKind, SentenceOrigin, TermRef, apply};
use serde_json::Value;

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

#[test]
fn stale_fingerprint_is_rejected_before_compilation() {
    let baseline = support::load("counter.k");
    let at = TermRef::new(support::rule(&baseline, "COUNTER.increment"), [1]);
    let expected = baseline.term(&at).expect("requires").clone();
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        at,
        expected,
        replacement: k_rust::kast::Term::Token {
            token: "false".to_owned(),
            sort: k_rust::kast::Sort::new("Bool"),
        },
    }])
    .expect("patch")
    .pinned(&baseline)
    .expect("pins");
    let text = std::fs::read_to_string(std::path::Path::new(support::DIR).join("counter.k"))
        .expect("source");
    let directory =
        std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("validator-stale-fingerprint");
    std::fs::create_dir_all(&directory).expect("directory");
    let path = directory.join("counter.k");
    std::fs::write(
        &path,
        text.replace("counter(s(N), L)", "counter(s(s(N)), L)"),
    )
    .expect("variant");
    let validator = NativeValidator::bind(
        support::load_path(&path, "COUNTER"),
        CompileOptions::default(),
    );
    match validator.validate(&patch) {
        Err(MutantRejection::Patch(failure)) => {
            assert_eq!(failure.kind(), PatchFailureKind::StalePrecondition)
        }
        other => panic!("expected a stale patch rejection, got {other:?}"),
    }
}

/// F-01: `compile_baseline` memoises its result inside the validator. The memo returns
/// exactly what a fresh k-rust compile of that validator's own baseline under its own
/// options returns, never the result of another baseline or of other options, and a
/// clone carries the result its source holds.
#[test]
fn compile_baseline_memo_is_the_validators_own_compile() {
    let fresh = |validator: &NativeValidator, options: CompileOptions| {
        compile_loaded_definition(validator.baseline().loaded(), options).expect("fresh compile")
    };
    let default = validator();
    let narrow_options = CompileOptions {
        kore_width: 40,
        ..CompileOptions::default()
    };
    let narrow = NativeValidator::bind(support::load("counter.k"), narrow_options.clone());
    let memory = NativeValidator::bind(support::load("memory.k"), CompileOptions::default());

    let first = default.compile_baseline().expect("counter.k compiles");
    assert_eq!(
        first.artifacts(),
        &fresh(&default, CompileOptions::default())
    );
    assert_eq!(first.compile_options(), &CompileOptions::default());
    assert_eq!(first.definition(), default.baseline().definition());
    assert!(first.origins().is_none());
    assert_eq!(default.compile_baseline().expect("memoised"), first);

    let narrowed = narrow
        .compile_baseline()
        .expect("counter.k compiles narrow");
    assert_eq!(narrowed.compile_options(), &narrow_options);
    assert_eq!(narrowed.artifacts(), &fresh(&narrow, narrow_options));
    assert_ne!(
        narrowed.artifacts().definition_kore,
        first.artifacts().definition_kore,
        "the options reach the compile"
    );
    assert_eq!(default.compile_baseline().expect("memoised"), first);

    let other = memory.compile_baseline().expect("memory.k compiles");
    assert_ne!(other.definition(), first.definition());
    assert_eq!(
        other.artifacts(),
        &fresh(&memory, CompileOptions::default())
    );

    let before = validator();
    let cloned_before = before.clone();
    let cloned_after = default.clone();
    assert_eq!(cloned_after.compile_baseline().expect("clone"), first);
    assert_eq!(cloned_before.compile_baseline().expect("clone"), first);
    assert_eq!(before.compile_baseline().expect("source"), first);

    // A mutant compile is never memoised: it compiles the patched definition.
    let patch = increment_mutant(&default);
    let mutant = default.validate(&patch).expect("mutant");
    assert_ne!(mutant.artifacts(), first.artifacts());
    assert_eq!(default.compile_baseline().expect("memoised"), first);
}
