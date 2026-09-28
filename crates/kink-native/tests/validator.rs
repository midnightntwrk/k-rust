//! `NativeValidator` over `testdata/k/counter.k`: kink-patch application
//! followed by k-rust compilation, publishing nothing unless both succeed.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::Term;
use k_rust::kompile::CompileOptions;
use kink_native::observation::{DomainEventSpec, PayloadSource};
use kink_native::{
    IdentityError, ManifestFailure, MutantRejection, NativeValidator, ObservedRule,
    ValidatedDefinition,
};
use kink_patch::{
    Baseline, Edit, InsertPosition, Patch, PatchFailureKind, SentenceOrigin, TermRef, apply,
};
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

/// The campaign observation of symmem (`write`, `load`, `free`) or guardedmem (`write`,
/// `load`, `loadNeg`), with the pre-state payload paths of the campaign fixtures.
fn memory_observation(baseline: &Baseline, module: &str) -> Vec<ObservedRule> {
    let (rules, address): (&[(&str, &str, usize)], &[u32]) = if module == "SYMMEM" {
        (
            &[
                ("write", "memoryWrite", 2),
                ("load", "memoryLoad", 2),
                ("free", "memoryFree", 1),
            ],
            &[0, 0],
        )
    } else {
        (
            &[
                ("write", "memoryWrite", 2),
                ("load", "memoryLoad", 2),
                ("loadNeg", "memoryLoad", 2),
            ],
            &[0, 0, 0],
        )
    };
    rules
        .iter()
        .map(|(label, constructor, arity)| ObservedRule {
            rule: support::rule(baseline, &format!("{module}.{label}")),
            emit_rule_applied: false,
            domain_events: vec![DomainEventSpec {
                constructor: (*constructor).into(),
                payload: [support::k_head(address), support::k_head(&[0, 1])]
                    .into_iter()
                    .take(*arity)
                    .map(PayloadSource::BeforeTerm)
                    .collect(),
            }],
        })
        .collect()
}

fn term_at(baseline: &Baseline, label: &str, path: &[u32]) -> (TermRef, Term) {
    let at = TermRef::new(support::rule(baseline, label), path);
    let term = baseline.term(&at).expect("term").clone();
    (at, term)
}

fn replace(at: TermRef, expected: Term, replacement: Term) -> Edit {
    Edit::ReplaceTerm {
        at,
        expected,
        replacement,
    }
}

/// S1 (`release-after-write`) and K (`release-after-access`): `P` becomes `seq(free(A), P)`
/// on the right-hand side of the listed symmem rules.
fn release(baseline: &Baseline, labels: &[&str]) -> Patch {
    Patch::new(
        labels
            .iter()
            .map(|label| {
                let (_, address) = term_at(baseline, label, &[0, 0, 0, 0]);
                let (at, continuation) = term_at(baseline, label, &[0, 1]);
                replace(
                    at,
                    continuation.clone(),
                    Term::apply(
                        "seq",
                        vec![Term::apply("free", vec![address]), continuation],
                    ),
                )
            })
            .collect(),
    )
    .expect("patch")
}

/// C (`coupled-value-representation`): `V` becomes `s(V)` in the left-hand sides of symmem's
/// `write` and `load`.
fn value_representation(baseline: &Baseline) -> Patch {
    Patch::new(
        ["SYMMEM.write", "SYMMEM.load"]
            .into_iter()
            .map(|label| {
                let (at, value) = term_at(baseline, label, &[0, 0, 0, 1]);
                replace(at, value.clone(), Term::apply("s", vec![value]))
            })
            .collect(),
    )
    .expect("patch")
}

/// G (`inverted-load-sign`): guardedmem's `load` and `loadFault` exchange their `requires`.
fn inverted_load_sign(baseline: &Baseline) -> Patch {
    let (load_at, load) = term_at(baseline, "GUARDEDMEM.load", &[1]);
    let (fault_at, fault) = term_at(baseline, "GUARDEDMEM.loadFault", &[1]);
    Patch::new(vec![
        replace(load_at, load.clone(), fault.clone()),
        replace(fault_at, fault, load),
    ])
    .expect("patch")
}

/// A1 (`relabel-swap`): symmem's `write` and `load` exchange their operations.
fn relabel_swap(baseline: &Baseline) -> Patch {
    let (write_at, write) = term_at(baseline, "SYMMEM.write", &[0, 0, 0]);
    let (load_at, load) = term_at(baseline, "SYMMEM.load", &[0, 0, 0]);
    Patch::new(vec![
        replace(write_at, write.clone(), load.clone()),
        replace(load_at, load, write),
    ])
    .expect("patch")
}

/// For mutants that edit observed rules, content anchoring changes nothing: every rule the
/// patch did not change is anchored to the observation positional resolution already gives,
/// and every edited rule has no baseline counterpart content, so it stays positional.
#[test]
fn anchored_manifest_equals_positional_for_edited_rules() {
    for (fixture, module) in [("symmem.k", "SYMMEM"), ("guardedmem.k", "GUARDEDMEM")] {
        let validator = NativeValidator::bind(support::load(fixture), CompileOptions::default());
        let baseline = validator.baseline();
        let compiled = validator.compile_baseline().expect("baseline compiles");
        let observed = memory_observation(baseline, module);
        let mutants = if module == "SYMMEM" {
            vec![
                ("S1", release(baseline, &["SYMMEM.write"])),
                ("K", release(baseline, &["SYMMEM.write", "SYMMEM.load"])),
                ("C", value_representation(baseline)),
            ]
        } else {
            vec![("G", inverted_load_sign(baseline))]
        };
        for (name, patch) in mutants {
            let side = validator.validate(&patch).expect("mutant compiles");
            let positional = validator
                .observation_manifest(&side, &observed)
                .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
            let anchored = validator
                .observation_manifest_anchored(&compiled, &side, &observed)
                .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
            assert_eq!(anchored, positional, "{name}");
        }
    }
}

/// A1: each moved content carries the baseline observation of that content, where source
/// positions attach it to the other rule's observation.
#[test]
fn relabel_swap_is_anchored_by_content() {
    let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
    let baseline = validator.baseline();
    let compiled = validator.compile_baseline().expect("baseline compiles");
    let observed = memory_observation(baseline, "SYMMEM");
    let side = validator
        .validate(&relabel_swap(baseline))
        .expect("mutant compiles");
    let anchored = validator
        .observation_manifest_anchored(&compiled, &side, &observed)
        .expect("anchored manifest");
    let positional = validator
        .observation_manifest(&side, &observed)
        .expect("positional manifest");
    let write = support::rule(baseline, "SYMMEM.write");
    let load = support::rule(baseline, "SYMMEM.load");
    for (content, other, constructor) in [
        (&write, &load, "memoryWrite"),
        (&load, &write, "memoryLoad"),
    ] {
        let identity = compiled
            .rule_identity_for(content)
            .expect("baseline identity");
        let spec = anchored
            .attribution(identity)
            .expect("anchored attribution");
        assert_eq!(&spec.rule, content);
        assert_eq!(spec.domain_events[0].constructor, constructor);
        assert_eq!(
            spec.label.as_deref(),
            baseline
                .sentence(content)
                .expect("rule")
                .attributes()
                .string(AttributeKey::Label),
            "events carry the baseline label of the content"
        );
        assert_eq!(
            &positional.attribution(identity).expect("positional").rule,
            other,
            "source positions attach the content to the other rule"
        );
    }
    assert_eq!(
        anchored.backend_rule_ids(),
        validator
            .observation_manifest(&compiled, &observed)
            .expect("baseline manifest")
            .backend_rule_ids(),
        "the anchored mutant selects the baseline's identities in manifest order"
    );
}

/// A `UNIQUE_ID` with two distinct normalized axioms is not anchored: the mutant adds an
/// alpha-variant of `SYMMEM.write` (`V` renamed to `U`), which shares its identity. Anchoring
/// falls back to positional resolution, which refuses the shared identity.
#[test]
fn divergent_identity_is_not_anchored() {
    fn rename(term: &mut Term) {
        match term {
            Term::Variable { name, .. } if name == "V" => *name = "U".into(),
            Term::Rewrite { left, right } => {
                rename(left);
                rename(right);
            }
            Term::As { pattern, alias } => {
                rename(pattern);
                rename(alias);
            }
            Term::Sequence(items) => items.iter_mut().for_each(rename),
            Term::Apply { arguments, .. } => arguments.iter_mut().for_each(rename),
            Term::Annotated { term, .. } => rename(term),
            _ => {}
        }
    }
    let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
    let baseline = validator.baseline();
    let compiled = validator.compile_baseline().expect("baseline compiles");
    let observed = memory_observation(baseline, "SYMMEM");
    let write = support::rule(baseline, "SYMMEM.write");
    let mut variant = baseline.sentence(&write).expect("rule").clone();
    for key in [
        AttributeKey::Label,
        AttributeKey::UniqueId,
        AttributeKey::Origin,
        AttributeKey::Location,
        AttributeKey::Source,
        AttributeKey::SourceId,
        AttributeKey::SentenceStartOffset,
        AttributeKey::SentenceEndOffset,
        AttributeKey::ContentStartLine,
        AttributeKey::ContentStartColumn,
        AttributeKey::ContentStartOffset,
    ] {
        variant.attributes_mut().remove(key.as_str());
    }
    let Sentence::Rule { body, .. } = &mut variant else {
        panic!("SYMMEM.write is a rule")
    };
    rename(body);
    let side = validator
        .validate(
            &Patch::new(vec![Edit::InsertSentence {
                position: InsertPosition::ModuleEnd(write.module.clone()),
                ordinal: 0,
                sentence: variant,
            }])
            .expect("patch"),
        )
        .expect("mutant compiles");
    let identity = compiled
        .rule_identity_for(&write)
        .expect("baseline identity");
    assert_eq!(
        side.artifacts()
            .execution_rewrite_order
            .iter()
            .filter(|id| *id == identity)
            .count(),
        1,
        "the variant shares the identity of SYMMEM.write"
    );
    let positional = validator.observation_manifest(&side, &observed);
    assert_eq!(
        positional,
        Err(ManifestFailure::Identity {
            rule: write,
            error: IdentityError::Ambiguous,
        })
    );
    assert_eq!(
        validator.observation_manifest_anchored(&compiled, &side, &observed),
        positional
    );
}
