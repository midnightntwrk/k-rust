//! Plan row O4 over `testdata/k/counter.k`: structural, attribute, label and all-transitions
//! selectors choose exactly the matching written rules, in definition order, and publish
//! nothing on failure.
//!
//! The structural rows use `counter.k`: the `increment` right-hand side is
//! `counter(s(N), L)`, and the `fallback` rule has the same right-hand side as
//! `branch`. The label clause of `labeled-branch-rhs` excludes `fallback`.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::definition::{Sentence, sentence_mut};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::ast::Pattern;
use kink_native::execution::{ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget};
use kink_native::observation::NativeEvent;
use kink_native::{
    MutantRejection, NativeValidator, RewriteRules, RuleSelection, RuleSelector, SelectionFailure,
    select_rules,
};
use kink_patch::{Baseline, CandidateFailureKind, Edit, Patch, SentenceRef};
use serde_json::Value;

fn structural(label: Option<&str>, path: &[u32], sort: &str, head: Option<&str>) -> RuleSelector {
    RuleSelector::Structural {
        label: label.map(str::to_owned),
        path: path.to_vec(),
        sort: Sort::new(sort),
        head: head.map(str::to_owned),
    }
}

fn selection(selector: RuleSelector, expected_cardinality: usize) -> RuleSelection {
    RuleSelection {
        selector,
        expected_cardinality,
        emit_rule_applied: true,
        domain_events: Vec::new(),
    }
}

fn label_free_counter_rhs() -> RuleSelector {
    structural(None, &[0, 1], "Counter", Some("counter"))
}

fn labeled_branch_rhs() -> RuleSelector {
    structural(Some("COUNTER.branch"), &[0, 1], "Control", Some("selected"))
}

/// Every rule body of sort `Control`; without a head clause the rewrite itself matches.
fn multi_rule_body() -> RuleSelector {
    structural(None, &[0], "Control", None)
}

fn priority(value: &str) -> RuleSelector {
    RuleSelector::Attribute {
        key: "priority".to_owned(),
        value: Value::String(value.to_owned()),
    }
}

/// (id, selections as (selector, expected cardinality), expected outcome)
type Row<T> = (&'static str, Vec<(RuleSelector, usize)>, T);

fn labels(
    baseline: &Baseline,
    selections: &[RuleSelection],
) -> Result<Vec<String>, SelectionFailure> {
    let classification = selections
        .iter()
        .any(|selection| matches!(selection.selector, RuleSelector::AllTransitions))
        .then(|| {
            let module = baseline
                .authored_sentences()
                .find(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
                .expect("an authored rule")
                .0
                .module;
            let validator = NativeValidator::bind(baseline.clone(), CompileOptions::default());
            let side = validator.compile_baseline().expect("baseline compiles");
            RewriteRules::classify(&validator, &side, &module).expect("rewrite classification")
        });
    select_rules(baseline, classification.as_ref(), selections).map(|rules| {
        rules
            .into_iter()
            .map(|rule| {
                baseline
                    .sentence(&rule.rule)
                    .expect("rule")
                    .attributes()
                    .string(k_rust::definition::AttributeKey::Label)
                    .unwrap_or("")
                    .to_owned()
            })
            .collect()
    })
}

#[test]
fn selectors_choose_exactly_the_matching_rules_in_definition_order() {
    let counter = support::load("counter.k");
    #[rustfmt::skip]
    let rows: [Row<&[&str]>; 8] = [
        // Without a label clause, a labelled rule matches.
        ("label-free-counter-rhs", vec![(label_free_counter_rhs(), 1)], &["COUNTER.increment"]),
        ("labeled-branch-rhs", vec![(labeled_branch_rhs(), 1)], &["COUNTER.branch"]),
        ("multi-rule-body", vec![(multi_rule_body(), 2)], &["COUNTER.branch", "COUNTER.fallback"]),
        ("no-head-accepts-any-term-of-the-sort", vec![(structural(None, &[0, 1], "Control", None), 2)], &["COUNTER.branch", "COUNTER.fallback"]),
        ("attribute", vec![(priority("200"), 1)], &["COUNTER.fallback"]),
        ("label", vec![(RuleSelector::Label("COUNTER.increment".to_owned()), 1)], &["COUNTER.increment"]),
        ("all-transitions", vec![(RuleSelector::AllTransitions, 3)], &["COUNTER.increment", "COUNTER.branch", "COUNTER.fallback"]),
        // Selections keep their order; each lists its rules in definition order.
        ("selection-order", vec![(multi_rule_body(), 2), (label_free_counter_rhs(), 1)], &["COUNTER.branch", "COUNTER.fallback", "COUNTER.increment"]),
    ];
    for (id, selections, expected) in rows {
        let selections = selections
            .into_iter()
            .map(|(selector, cardinality)| selection(selector, cardinality))
            .collect::<Vec<_>>();
        assert_eq!(
            labels(&counter, &selections).unwrap_or_else(|failure| panic!("{id}: {failure}")),
            expected,
            "{id}"
        );
    }
}

#[test]
fn selection_failures_publish_no_rule() {
    let counter = support::load("counter.k");
    let mismatch = |selection, expected, actual| SelectionFailure::CardinalityMismatch {
        selection,
        expected,
        actual,
    };
    let rule = |label| support::rule(&counter, label);
    #[rustfmt::skip]
    let rows: [Row<SelectionFailure>; 9] = [
        ("wrong-cardinality", vec![(multi_rule_body(), 1)], mismatch(0, 1, 2)),
        ("path-past-a-leaf", vec![(structural(None, &[0, 1, 99], "Counter", None), 1)], mismatch(0, 1, 0)),
        ("wrong-sort", vec![(structural(None, &[0, 1], "Control", Some("counter")), 1)], mismatch(0, 1, 0)),
        ("wrong-head", vec![(structural(None, &[0, 1], "Counter", Some("selected")), 1)], mismatch(0, 1, 0)),
        ("wrong-attribute-value", vec![(priority("100"), 1)], mismatch(0, 1, 0)),
        // A selection that matches nothing is refused even when it expects nothing.
        ("empty-selection", vec![(RuleSelector::Label("COUNTER.nothing".to_owned()), 0)], mismatch(0, 0, 0)),
        // A later failure withdraws the rules earlier selections matched.
        ("later-failure-is-atomic", vec![(label_free_counter_rhs(), 1), (multi_rule_body(), 3)], mismatch(1, 3, 2)),
        ("rule-selected-twice", vec![(RuleSelector::AllTransitions, 3), (labeled_branch_rhs(), 1)], SelectionFailure::DuplicateRule { selection: 1, rule: rule("COUNTER.branch") }),
        ("rule-selected-by-two-selector-kinds", vec![(multi_rule_body(), 2), (priority("200"), 1)], SelectionFailure::DuplicateRule { selection: 1, rule: rule("COUNTER.fallback") }),
    ];
    for (id, selections, failure) in rows {
        let selections = selections
            .into_iter()
            .map(|(selector, cardinality)| selection(selector, cardinality))
            .collect::<Vec<_>>();
        assert_eq!(labels(&counter, &selections), Err(failure), "{id}");
    }
}

#[test]
fn invalid_structural_sites_publish_no_rule() {
    let counter = support::load("counter.k");
    #[rustfmt::skip]
    let rows = [
        ("labelled-path-past-leaf", structural(Some("COUNTER.increment"), &[0, 1, 0, 99], "Counter", None)),
        ("unknown-label", structural(Some("COUNTER.nothing"), &[0], "Control", None)),
    ];
    for (id, selector) in rows {
        let result = select_rules(
            &counter,
            None,
            &[
                selection(RuleSelector::Label("COUNTER.branch".into()), 1),
                selection(selector, 1),
            ],
        );
        assert!(
            matches!(result, Err(SelectionFailure::Structural { selection: 1, ref failure }) if failure.kind() == CandidateFailureKind::UnknownSite),
            "{id}: {result:?}"
        );
    }
}

#[test]
fn all_undecided_rewrite_rules_are_selected_in_definition_order() {
    let baseline = support::load("undecided.k");
    let validator = NativeValidator::bind(baseline.clone(), CompileOptions::default());
    let side = validator.compile_baseline().expect("baseline");
    let classification =
        RewriteRules::classify(&validator, &side, "UNDECIDED").expect("classification");
    let rules = select_rules(
        &baseline,
        Some(&classification),
        &[selection(RuleSelector::AllTransitions, 4)],
    )
    .expect("four rewrite rules are selectable");
    assert_eq!(
        rules.into_iter().map(|rule| rule.rule).collect::<Vec<_>>(),
        (4..8)
            .map(|index| SentenceRef::new("UNDECIDED", index))
            .collect::<Vec<_>>()
    );
}

#[test]
fn unlabelled_rules_are_selected_in_definition_order() {
    let baseline = support::load("unlabelled.k");
    let validator = NativeValidator::bind(baseline.clone(), CompileOptions::default());
    let side = validator.compile_baseline().expect("baseline");
    let classification =
        RewriteRules::classify(&validator, &side, "UNLABELLED").expect("classification");
    let rules = select_rules(
        &baseline,
        Some(&classification),
        &[selection(RuleSelector::AllTransitions, 3)],
    )
    .expect("all three written rules are selectable");
    assert_eq!(
        rules.into_iter().map(|rule| rule.rule).collect::<Vec<_>>(),
        (0..3)
            .map(|index| SentenceRef::new("UNLABELLED", index))
            .collect::<Vec<_>>()
    );
}

#[test]
fn all_transitions_without_classification_publishes_no_rule() {
    let baseline = support::load("counter.k");
    #[rustfmt::skip]
    let rows = [
        (vec![selection(RuleSelector::AllTransitions, 3)], 0),
        (vec![selection(RuleSelector::Label("COUNTER.increment".to_owned()), 1), selection(RuleSelector::AllTransitions, 3)], 1),
    ];
    for (selections, failing_selection) in rows {
        assert_eq!(
            select_rules(&baseline, None, &selections),
            Err(SelectionFailure::Unclassified {
                selection: failing_selection
            })
        );
    }
}

#[test]
fn selected_rewrite_reclassified_as_equation_fails_closed() {
    let validator = NativeValidator::bind(support::load("undecided.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("baseline");
    let classification = RewriteRules::classify(&validator, &baseline, "UNDECIDED")
        .expect("baseline classification");
    let rules = select_rules(
        validator.baseline(),
        Some(&classification),
        &[selection(RuleSelector::AllTransitions, 4)],
    )
    .expect("four rewrite rules");
    let patch = Patch::new(vec![Edit::AddAttribute {
        at: support::rule(validator.baseline(), "UNDECIDED.step"),
        key: "simplification".to_owned(),
        value: Value::String(String::new()),
    }])
    .expect("patch");
    let mutant = match validator.validate(&patch) {
        Ok(mutant) => mutant,
        Err(MutantRejection::Compilation(error)) => {
            assert_eq!(error.stage, "check simplification rules");
            return;
        }
        Err(error) => panic!("unexpected rejection: {error}"),
    };
    let manifest = validator
        .observation_manifest(&mutant, &rules)
        .expect("manifest");
    let mut backend = Backend::new(
        &mutant.artifacts().definition_kore,
        "UNDECIDED",
        BackendOptions::default(),
    )
    .expect("backend");
    let state = support::initial_state(
        kore_application("Lblvacuous", Vec::new(), Vec::new()),
        "SortS",
    );
    assert!(matches!(
        ExecutionAdapter::new(manifest).execute(
            &mut backend,
            &state,
            ExecutionBudget {
                time: Duration::from_secs(30),
                max_simplification_iterations: 1000,
            },
        ),
        Err(ExecutionAdapterFailure::Backend(_))
    ));
}

#[test]
fn function_equations_are_not_observable() {
    let validator = NativeValidator::bind(support::load("undecided.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("baseline");
    let rules = select_rules(
        validator.baseline(),
        None,
        &[selection(
            structural(None, &[0, 0], "Bool", Some("isZero")),
            2,
        )],
    )
    .expect("two equations selected by position");
    let manifest = validator
        .observation_manifest(&side, &rules)
        .expect("manifest");
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "UNDECIDED",
        BackendOptions::default(),
    )
    .expect("backend");
    let state = support::initial_state(
        kore_application("LblisZero", Vec::new(), vec![z()]),
        "SortBool",
    );
    assert!(matches!(
        ExecutionAdapter::new(manifest).execute(
            &mut backend,
            &state,
            ExecutionBudget {
                time: Duration::from_secs(30),
                max_simplification_iterations: 1000
            }
        ),
        Err(ExecutionAdapterFailure::Backend(_))
    ));
}

/// A structural selector that meets a position of unknown sort cannot say whether that rule
/// matches, so it publishes nothing rather than the rules it could decide.
#[test]
fn an_undecided_sort_publishes_no_rule() {
    let counter = support::load("counter.k");
    let increment = support::rule(&counter, "COUNTER.increment");
    // `increment`'s `requires` becomes a variable without a sort or cast.
    let mut loaded = counter.loaded().clone();
    let module = loaded
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == increment.module)
        .expect("module");
    let slot = &mut module.local_sentences[usize::try_from(increment.index).expect("index")];
    let Sentence::Rule { requires, .. } = sentence_mut(slot) else {
        panic!("increment is a rule");
    };
    *requires = Term::Variable {
        name: "B".to_owned(),
        sort: None,
    };
    let unsorted = Baseline::new(loaded);
    assert_eq!(
        labels(
            &unsorted,
            &[selection(structural(None, &[1], "Bool", None), 2)]
        ),
        Err(SelectionFailure::UndecidedSort { selection: 0 })
    );
    assert_eq!(
        labels(
            &unsorted,
            &[selection(structural(None, &[2], "Bool", None), 3)]
        ),
        Ok(vec![
            "COUNTER.increment".to_owned(),
            "COUNTER.branch".to_owned(),
            "COUNTER.fallback".to_owned()
        ]),
        "a selector that never asks for that position's sort is unaffected"
    );
}

fn z() -> Pattern {
    kore_application("Lblz", Vec::new(), Vec::new())
}

fn s(pattern: Pattern) -> Pattern {
    kore_application("Lbls", Vec::new(), vec![pattern])
}

/// The rule labels of the `RuleApplied` events of each leaf when `selector` is observed on the
/// compiled baseline.
fn observed(selector: RuleSelector, cardinality: usize, state: &Pattern) -> Vec<Vec<String>> {
    let validator = NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("counter.k compiles");
    let classification = matches!(selector, RuleSelector::AllTransitions)
        .then(|| RewriteRules::classify(&validator, &side, "COUNTER").expect("classification"));
    let rules = select_rules(
        validator.baseline(),
        classification.as_ref(),
        &[selection(selector, cardinality)],
    )
    .expect("selection");
    let manifest = validator
        .observation_manifest(&side, &rules)
        .expect("manifest installs");
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "COUNTER",
        BackendOptions::default(),
    )
    .expect("backend");
    let execution = ExecutionAdapter::new(manifest)
        .execute(
            &mut backend,
            state,
            ExecutionBudget {
                time: Duration::from_secs(30),
                max_simplification_iterations: 1000,
            },
        )
        .expect("execution adapts");
    execution
        .leaves()
        .iter()
        .map(|leaf| {
            leaf.branch
                .events
                .iter()
                .map(|event| match event {
                    NativeEvent::RuleApplied(event) => validator
                        .baseline()
                        .sentence(&event.rule)
                        .expect("rule")
                        .attributes()
                        .string(k_rust::definition::AttributeKey::Label)
                        .unwrap_or("")
                        .to_owned(),
                    NativeEvent::Domain(event) => panic!("no domain events: {event:?}"),
                })
                .collect()
        })
        .collect()
}

/// Selected rules are the ones the backend observes: three `increment`s for
/// `counter(z, s(s(s(z))))`, and `branch` but not `fallback` for `choose(true)`.
#[test]
fn structurally_selected_rules_are_observed_live() {
    let t1 = support::initial_state(
        kore_application("Lblcounter", Vec::new(), vec![z(), s(s(s(z())))]),
        "SortCounter",
    );
    assert_eq!(
        observed(label_free_counter_rhs(), 1, &t1),
        [vec!["COUNTER.increment".to_owned(); 3]]
    );
    let t2 = support::initial_state(
        kore_application(
            "Lblchoose",
            Vec::new(),
            vec![Pattern::DomainValue {
                sort: kore_sort("SortBool"),
                value: "true".into(),
            }],
        ),
        "SortControl",
    );
    assert_eq!(
        observed(multi_rule_body(), 2, &t2),
        [vec!["COUNTER.branch".to_owned()]]
    );
}
