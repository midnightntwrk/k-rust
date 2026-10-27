//! Fresh values in the differential target (FZ-FRESH).
//!
//! A rule's `!` names are lowered by compilation to offsets from the `<generatedCounter>` cell,
//! and `docs/compatibility.md` ("Compiler-resolved fresh constants") leaves open which name gets
//! which offset in a rule with two or more names. So a definition with such a rule denotes one
//! rewrite theory per association, and a kill must hold for every pair of associations of the
//! two definitions. k-rust marks every run that builds a candidate of such a rule
//! (`fresh-association`), and the differential's condition 3 refuses the case as for any
//! implementation-chosen value. The counter is not part of an end: ends are compared with its
//! content erased, so a mutant that only mints more values is no kill, while one whose minted
//! values reach a declared cell still is.
//!
//! Every fixture is `tests/data/fresh/*.k` over the one program `mk(3)`, with an `Int` hole on
//! the `3`.

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust::kore::ast::{Pattern, Sentence};
use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, FuzzReport, HoleDecl,
    HoleLocation, OutcomeClass, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    exec::UnjudgedReason,
    report::{KillKind, ReasonHook},
    spec::{DEFAULT_REJECTION_CAP, PathMode},
    target::DifferentialTarget,
    values::{Constraints, GenerationBounds},
};
use support::{
    FRESH_BASE, FRESH_CMPB, FRESH_CMPM, FRESH_CONST0, FRESH_CONST5, FRESH_DISC0, FRESH_DISC1,
    FRESH_LIT, FRESH_LIT_M, FRESH_MINT, FRESH_MINT2, FRESH_MUT, FRESH_RB0, FRESH_RB1, FRESH_RB2,
    FRESH_SHIFT, FRESH_SWAP, Fixture,
};

const PROGRAM: &str = "fresh/mk.pgm";

/// A differential campaign of `mutant` against `baseline` over the hole `N` on the `3` of
/// `mk(3)`, in `paths`.
fn spec(baseline: &'static Fixture, mutant: &'static Fixture, paths: PathMode) -> CampaignSpec {
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(baseline.compiled().definition()),
            mutant: Some(Arc::new(mutant.compiled().definition())),
        },
        program: ProgramInput::Source(baseline.compiled().program_source(PROGRAM)),
        holes: vec![HoleDecl {
            name: "N".into(),
            sort: "Int".into(),
            location: HoleLocation::Span(SpanAddress {
                program: PROGRAM.into(),
                line: None,
                column: None,
                find: "3".into(),
                literal: "3".into(),
            }),
            constraints: Constraints::default(),
            allow_refused_sort: false,
        }],
        target: Target {
            kind: TargetKind::Differential(DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
            comparable: false,
            query_confirmable: false,
        },
        options: CaseOptions {
            paths,
            ..CaseOptions::default()
        },
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights: ProposerConfig::default().weights,
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 7,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

/// 8 cases of `mutant` against `baseline` in `paths`, without engine defects.
fn report_of(baseline: &'static Fixture, mutant: &'static Fixture, paths: PathMode) -> FuzzReport {
    let report = Campaign::new(spec(baseline, mutant, paths))
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    report
}

/// The `UNIQUE_ID` of the rewrite axiom of `fixture` labelled `label` (`FRESH.<label>`).
fn rule_id(fixture: &'static Fixture, label: &str) -> String {
    let label = format!("FRESH.{label}");
    let string = |attribute: &Pattern, name: &str| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == name => match &arguments[..] {
            [Pattern::String(value)] => {
                Some(String::from_utf8_lossy(value.as_bytes()).into_owned())
            }
            _ => None,
        },
        _ => None,
    };
    fixture
        .compiled()
        .kore
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .find_map(|sentence| {
            let Sentence::Axiom { attributes, .. } = sentence else {
                return None;
            };
            attributes
                .0
                .iter()
                .any(|attribute| string(attribute, "label").as_deref() == Some(label.as_str()))
                .then(|| {
                    attributes
                        .0
                        .iter()
                        .find_map(|attribute| string(attribute, "UNIQUE'Unds'ID"))
                })
                .flatten()
        })
        .unwrap_or_else(|| panic!("{} has no rule {label}", fixture.file))
}

/// Every case of `report` is `baseline-incomplete` with `reason`, no witness is found, and the
/// reason's hooks name `fresh-association` of the rule `rule`.
fn assert_fresh_baseline_incomplete(report: &FuzzReport, reason: UnjudgedReason, rule: &str) {
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert_eq!(
        report.totals.classes.keys().collect::<Vec<_>>(),
        [&OutcomeClass::BaselineIncomplete],
        "{:?}",
        report.totals
    );
    assert_eq!(
        report
            .totals
            .baseline_incomplete_reasons
            .keys()
            .collect::<Vec<_>>(),
        [&reason],
        "{:?}",
        report.totals
    );
    let hooks = &report.totals.baseline_incomplete_hooks[&reason];
    assert_eq!(
        hooks.hooks,
        [ReasonHook::chosen(rule, "fresh-association")],
        "{:?}",
        report.totals
    );
}

/// The witness's added end: the kill kind and the mutant side's final configurations.
fn added_end(report: &FuzzReport) -> String {
    let witness = report.witness().expect("a kill");
    assert_eq!(witness.first.kill, Some(KillKind::AddedEnd), "{witness:?}");
    witness.first.sides[1].final_configurations.join("\n")
}

/// F-REORDER (engine review B1): the mutant writes the baseline's one two-name rule with its
/// cells in the other order, which is the same K rule. k-rust numbers the names by first
/// occurrence, so the mutant ends with `<a> 1 <b> 0` where the baseline ends with `<a> 0 <b> 1`;
/// another admissible numbering of either side swaps them. No kill: the baseline's ends rest on
/// the association, so every case is `baseline-incomplete` (`implementation-chosen-value`), and
/// the reason names the rule with the class `fresh-association`. At the base of FZ-FRESH the
/// anchor was killed by an added end.
#[test]
fn a_rule_reordered_with_two_fresh_names_is_never_killed() {
    let report = report_of(&FRESH_BASE, &FRESH_MUT, PathMode::OnePath);
    assert_fresh_baseline_incomplete(
        &report,
        UnjudgedReason::ImplementationChosenValue,
        &rule_id(&FRESH_BASE, "mk"),
    );
}

/// F-REORDER-LIT (FZ-FRESH fix round, review B1): as F-REORDER, with a cell `<c> 2 </c>` that the
/// rule matches as the literal 2. Term-construction minimization, which runs after the fresh
/// names are numbered, then compiles the counter advance as a variable bound to that 2 on the
/// left-hand side; k-rust reads the advance through the binding, so the step is marked all the
/// same and every case is `baseline-incomplete`. Before the fix round the rule went unmarked and
/// the anchor was killed by an added end (`<a> 1 <b> 0` against `<a> 0 <b> 1`).
#[test]
fn a_reordered_rule_whose_left_hand_side_holds_its_advance_is_never_killed() {
    let report = report_of(&FRESH_LIT, &FRESH_LIT_M, PathMode::OnePath);
    assert_fresh_baseline_incomplete(
        &report,
        UnjudgedReason::ImplementationChosenValue,
        &rule_id(&FRESH_LIT, "mk"),
    );
}

/// Every case of `report` is `unsupported` with `reason`, no witness is found, and the reason's
/// hooks are `hooks`.
fn assert_unsupported(report: &FuzzReport, reason: UnjudgedReason, hooks: &[ReasonHook]) {
    assert!(report.witness().is_none(), "{:?}", report.outcome);
    assert_eq!(
        report.totals.classes,
        BTreeMap::from([(OutcomeClass::Unsupported, 8)]),
        "{:?}",
        report.totals
    );
    assert_eq!(
        report.totals.unsupported_reasons,
        BTreeMap::from([(reason, 8)]),
        "{:?}",
        report.totals
    );
    assert_eq!(
        report.totals.unsupported_hooks[&reason].hooks, hooks,
        "{:?}",
        report.totals
    );
}

/// F-MUTANT (FZ-FRESH fix round, review S1): the baseline `swap.k` writes the constants
/// `<a> 1 <b> 0` and is unmarked; the mutant is `base.k`'s two-name rule, whose end is
/// `<a> 0 <b> 1` under k-rust's numbering and the baseline's end under the other. The mutant's
/// end outside the baseline's set carries the mark itself, so it is no end that can kill: every
/// case is `unsupported` with the leaf's reason, `implementation-chosen-value`, naming the rule
/// with the class `fresh-association`, in both path modes.
#[test]
fn a_mutant_end_through_a_rule_with_two_fresh_names_is_never_killed() {
    let hooks = [ReasonHook::chosen(
        &rule_id(&FRESH_BASE, "mk"),
        "fresh-association",
    )];
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        let report = report_of(&FRESH_SWAP, &FRESH_BASE, paths);
        assert_unsupported(&report, UnjudgedReason::ImplementationChosenValue, &hooks);
    }
}

/// F-MUTANT-OFF-LEAF (FZ-FRESH fix round, review S1): the baseline `rb0.k` ends in `<r> 8 <s> 7`;
/// the mutant `rb1.k`'s two-name candidate `div` vanishes under k-rust's numbering, beside its
/// plain sibling, and its one end `<r> 7 <s> 7` would kill. Another numbering also gives the end
/// `<r> 10 <s> 0`, so the mutant's result is no evidence, under a depth bound and no work bound:
/// - on all paths the end's path is clean and the mark is on the run's list only, so the would-be
///   kill is `kill-without-evidence` (condition 3 read on the whole result);
/// - on one path the end rests on which candidate survived to be the first, so the leaf carries
///   the mark and is no end that can kill: `implementation-chosen-value`.
#[test]
fn a_mutant_whose_run_is_marked_off_its_killing_end_is_no_evidence() {
    let hooks = [ReasonHook::chosen(
        &rule_id(&FRESH_RB1, "div"),
        "fresh-association",
    )];
    for (paths, reason) in [
        (PathMode::AllPaths, UnjudgedReason::KillWithoutEvidence),
        (PathMode::OnePath, UnjudgedReason::ImplementationChosenValue),
    ] {
        let mut bounded = spec(&FRESH_RB0, &FRESH_RB1, paths);
        bounded.options.max_depth = Some(100);
        let report = Campaign::new(bounded)
            .expect("valid")
            .run(Budget::Cases(8), None);
        assert!(
            report.engine_defects.is_empty(),
            "{:?}",
            report.engine_defects
        );
        assert_unsupported(&report, reason, &hooks);
    }
}

/// F-CMP: as F-REORDER, with a later rule that compares the two minted values (`<r> X <Int Y`):
/// the two numberings give `<r> true` and `<r> false`, which no renaming of the minted values
/// relates, so a comparison up to renaming would kill the same K rule. No kill.
#[test]
fn a_comparison_of_two_fresh_values_of_one_rule_is_never_killed() {
    let report = report_of(&FRESH_CMPB, &FRESH_CMPM, PathMode::OnePath);
    assert_fresh_baseline_incomplete(
        &report,
        UnjudgedReason::ImplementationChosenValue,
        &rule_id(&FRESH_CMPB, "mk"),
    );
}

/// F-ROLLBACK (design probe P-RB): under k-rust's numbering the baseline's two-name candidate
/// `div` divides by `!A` = 0, is undefined and vanishes beside `plain`, so the baseline has the
/// one end `<r> 7 <s> 7`; the mutant, the same rule with its cells in the other order, also ends
/// with `<r> 10 <s> 0`. The baseline's other numbering has that end too, so the set of baseline
/// ends rests on the association: every case is `baseline-incomplete`. Under a depth bound and
/// no work bound the leaf is unmarked and the mark is on the run's list only
/// (`run-fact-off-leaves`); under the default work bound, which makes every leaf rest on what
/// the run met, the leaf carries it (`implementation-chosen-value`). At the base of FZ-FRESH the
/// anchor was killed by the added end `<r> 10`.
#[test]
fn a_vanished_two_name_candidate_makes_the_baseline_incomplete() {
    let rule = rule_id(&FRESH_RB1, "div");
    let mut bounded = spec(&FRESH_RB1, &FRESH_RB2, PathMode::AllPaths);
    bounded.options.max_depth = Some(100);
    let report = Campaign::new(bounded)
        .expect("valid")
        .run(Budget::Cases(8), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    assert_fresh_baseline_incomplete(&report, UnjudgedReason::RunFactOffLeaves, &rule);
    let report = report_of(&FRESH_RB1, &FRESH_RB2, PathMode::AllPaths);
    assert_fresh_baseline_incomplete(&report, UnjudgedReason::ImplementationChosenValue, &rule);
}

/// F-COUNTER (design probe P-DISC): the mutant mints a value and discards it, so its end differs
/// from the baseline's only in `<generatedCounter>` (1 against 0). The counter is no part of an
/// end, so every case is a `miss`. At the base of FZ-FRESH the anchor was killed on the counter
/// alone.
#[test]
fn a_difference_only_in_the_generated_counter_is_no_kill() {
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        let report = report_of(&FRESH_DISC0, &FRESH_DISC1, paths);
        assert!(
            report.witness().is_none(),
            "{paths:?}: {:?}",
            report.outcome
        );
        assert_eq!(
            report.totals.classes,
            BTreeMap::from([(OutcomeClass::Miss, 8)]),
            "{paths:?}: {:?}",
            report.totals
        );
    }
}

/// G-MINT-VISIBLE: the mutant mints one more value, in a second one-name step, into the declared
/// cell `<b>` (`<b> 1` where the baseline keeps `<b> 7`). One-name rules have one numbering, and
/// the minted value is in a declared cell, so the kill stays. The witness keeps the full
/// configuration, counter included.
#[test]
fn a_minted_value_in_a_declared_cell_still_kills() {
    let end = added_end(&report_of(&FRESH_MINT, &FRESH_MINT2, PathMode::OnePath));
    assert!(
        end.contains(r#"Lbl'-LT-'b'-GT-'{}(\dv{SortInt{}}("1"))"#)
            && end.contains(r#"Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("2"))"#),
        "{end}"
    );
}

/// G-SHIFT: the mutant mints and discards a value before the mint `<a>` receives, so `<a>` is 1
/// where the baseline's is 0. The counter's start and every rule's advance are fixed by the
/// contract, so every numbering shows the shift: the kill stays.
#[test]
fn a_shifted_fresh_value_still_kills() {
    let end = added_end(&report_of(&FRESH_MINT, &FRESH_SHIFT, PathMode::OnePath));
    assert!(
        end.contains(r#"Lbl'-LT-'a'-GT-'{}(\dv{SortInt{}}("1"))"#),
        "{end}"
    );
}

/// G-FRESH-FOR-CONSTANT: a mutant that writes a fresh value where the baseline writes the
/// constant 5 still kills (`<a> 0` against `<a> 5`). Against the constant 0, the value every
/// numbering mints first, the ends differ only in the counter, so it is a `miss`: a pinned
/// boundary (killed on the counter alone at the base of FZ-FRESH).
#[test]
fn a_fresh_value_for_a_constant_kills_unless_it_is_the_constant() {
    let end = added_end(&report_of(&FRESH_CONST5, &FRESH_MINT, PathMode::OnePath));
    assert!(
        end.contains(r#"Lbl'-LT-'a'-GT-'{}(\dv{SortInt{}}("0"))"#),
        "{end}"
    );
    let boundary = report_of(&FRESH_CONST0, &FRESH_MINT, PathMode::OnePath);
    assert!(boundary.witness().is_none(), "{:?}", boundary.outcome);
    assert_eq!(
        boundary.totals.classes,
        BTreeMap::from([(OutcomeClass::Miss, 8)]),
        "{:?}",
        boundary.totals
    );
}
