//! Rule and pattern targets (ARCHITECTURE 4.1, 4.2): catalog resolution and its refusals, the
//! requests each mode needs, the per-mode reach judgement, and the class of a case.
//!
//! The catalog mirrors the RULES fixture's (`tests/data/rules/rules.k`, whose catalog shape
//! `tests/fixtures.rs` pins), and the case results mirror its runs: `div(10, 0)` is an undefined
//! step whose rule is in coverage `applied` but on no leaf's path; `check(7)` reaches the guard
//! of `check-hit`, which fails, and ends naturally through `check-miss`.

use k_rust::{
    backend::{
        CompiledRuleKind, CompiledRuleOriginOutput, CompiledRuleOutput, HaltReasonOutput,
        RunCoverageOutput,
    },
    kore::parser::parse_pattern,
};

use super::{
    Judgement, Resolved, ResolvedTarget, RuleMode, RuleRef, Target, TargetKind, pattern_reached,
    rule::{blocked, resolve_rule, rule_needs, rule_reached},
};
use crate::{
    error::TargetProblem,
    exec::{CaseResult, LeafReport, OutcomeClass, TargetNeeds, UncleanReason},
};

const SOURCE: &str = "Source(rules/rules.k)";

fn entry(id: &str, label: Option<&str>, kind: CompiledRuleKind, line: u32) -> CompiledRuleOutput {
    CompiledRuleOutput {
        id: id.to_owned(),
        kind,
        executable: true,
        label: label.map(|label| format!("RULES.{label}")),
        priority: 50,
        origins: vec![CompiledRuleOriginOutput {
            source: Some(SOURCE.to_owned()),
            location: Some(format!("Location({line},3,{line},60)")),
            sentence: None,
        }],
        shared_identity: false,
    }
}

/// The RULES fixture's catalog, with an `UNKNOWN` generated axiom, a simplification and a
/// second module's `div` added.
fn catalog() -> Vec<CompiledRuleOutput> {
    use CompiledRuleKind::{Definedness, FunctionEquation, Rewrite, Simplification};
    let mut twin_a = entry("id-twin", Some("twin-a"), Rewrite, 36);
    twin_a.shared_identity = true;
    let mut twin_b = entry("id-twin", Some("twin-b"), Rewrite, 37);
    twin_b.shared_identity = true;
    let mut dormant = entry("id-dormant", Some("dormant"), FunctionEquation, 38);
    dormant.executable = false;
    let mut other_div = entry("id-other-div", None, Rewrite, 3);
    other_div.label = Some("OTHER.div".to_owned());
    other_div.origins[0].source = Some("Source(other/other.k)".to_owned());
    vec![
        entry("id-double", Some("double"), FunctionEquation, 30),
        entry("id-div", Some("div"), Rewrite, 32),
        entry("id-check-hit", Some("check-hit"), Rewrite, 33),
        entry("id-check-miss", Some("check-miss"), Rewrite, 34),
        entry("id-twice", Some("twice"), Rewrite, 35),
        twin_a,
        twin_b,
        dormant,
        entry("id-simp", Some("simp"), Simplification, 40),
        entry("id-ceil", None, Definedness, 41),
        entry("UNKNOWN", Some("generated"), Rewrite, 42),
        entry("id-same-line-a", Some("same-line-a"), Rewrite, 44),
        entry("id-same-line-b", Some("same-line-b"), Rewrite, 44),
        other_div,
    ]
}

fn label(label: &str) -> RuleRef {
    RuleRef::Label(label.to_owned())
}

fn source(source: &str, line: u32) -> RuleRef {
    RuleRef::Source {
        source: source.to_owned(),
        line,
    }
}

#[test]
fn a_rule_resolves_by_label_unique_id_or_source_position() {
    let catalog = catalog();
    let resolve = |rule: RuleRef| resolve_rule(&catalog, &rule);
    assert_eq!(resolve(label("RULES.div")), Ok("id-div".to_owned()));
    // A label without its module resolves when one entry carries it.
    assert_eq!(resolve(label("check-hit")), Ok("id-check-hit".to_owned()));
    assert_eq!(
        resolve(RuleRef::UniqueId("id-twice".to_owned())),
        Ok("id-twice".to_owned())
    );
    // The source as the catalog writes it, as the path inside it, or as a suffix of that path
    // at a directory boundary.
    for written in [SOURCE, "rules/rules.k", "rules.k"] {
        assert_eq!(
            resolve(source(written, 34)),
            Ok("id-check-miss".to_owned()),
            "{written}"
        );
    }
}

#[test]
fn an_unknown_or_ambiguous_reference_is_refused() {
    let catalog = catalog();
    let resolve = |rule: RuleRef| resolve_rule(&catalog, &rule);
    assert_eq!(
        resolve(label("RULES.nothing")),
        Err(TargetProblem::UnknownRule)
    );
    assert_eq!(
        resolve(RuleRef::UniqueId("id-nothing".to_owned())),
        Err(TargetProblem::UnknownRule)
    );
    assert_eq!(
        resolve(source("rules/rules.k", 31)),
        Err(TargetProblem::UnknownRule)
    );
    // `les.k` is not a path suffix of `rules/rules.k` at a directory boundary.
    assert_eq!(
        resolve(source("les.k", 34)),
        Err(TargetProblem::UnknownRule)
    );
    // `div` is written in two modules.
    assert_eq!(
        resolve(label("div")),
        Err(TargetProblem::AmbiguousRule(vec![
            "id-div".to_owned(),
            "id-other-div".to_owned()
        ]))
    );
    assert_eq!(
        resolve(source("rules.k", 44)),
        Err(TargetProblem::AmbiguousRule(vec![
            "id-same-line-a".to_owned(),
            "id-same-line-b".to_owned()
        ]))
    );
}

#[test]
fn entries_whose_coverage_may_come_from_elsewhere_are_refused() {
    let catalog = catalog();
    let resolve = |rule: RuleRef| resolve_rule(&catalog, &rule);
    assert_eq!(resolve(label("twin-a")), Err(TargetProblem::SharedIdentity));
    // Two entries share the id, so the id names neither; it is not an ambiguity of the
    // reference.
    assert_eq!(
        resolve(RuleRef::UniqueId("id-twin".to_owned())),
        Err(TargetProblem::SharedIdentity)
    );
    assert_eq!(resolve(label("dormant")), Err(TargetProblem::NotExecutable));
    assert_eq!(resolve(label("double")), Err(TargetProblem::Equation));
    assert_eq!(resolve(label("simp")), Err(TargetProblem::Equation));
    assert_eq!(resolve(source("rules.k", 41)), Err(TargetProblem::Equation));
    assert_eq!(resolve(label("generated")), Err(TargetProblem::UnknownId));
}

#[test]
fn fired_asks_for_the_rule_as_only_stop_rule_or_for_traces_under_run_to_completion() {
    assert_eq!(
        rule_needs("id-div", RuleMode::Fired, false),
        TargetNeeds {
            terminal_rules: vec!["id-div".to_owned()],
            ..TargetNeeds::default()
        }
    );
    assert_eq!(
        rule_needs("id-div", RuleMode::Fired, true),
        TargetNeeds {
            trace: true,
            ..TargetNeeds::default()
        }
    );
    for mode in [RuleMode::Covered, RuleMode::ConditionReached] {
        for run_to_completion in [false, true] {
            assert_eq!(
                rule_needs("id-div", mode, run_to_completion),
                TargetNeeds::default(),
                "{mode:?}"
            );
        }
    }
}

fn leaf(halt: HaltReasonOutput, unclean: Vec<UncleanReason>, natural_end: bool) -> LeafReport {
    LeafReport {
        halt,
        depth: 1,
        state: parse_pattern(r"\top{SortGeneratedTopCell{}}()").expect("a KORE pattern"),
        unclean,
        natural_end,
        matches: Vec::new(),
        rewrites: Vec::new(),
        constructor_only: None,
    }
}

fn natural_end() -> LeafReport {
    leaf(HaltReasonOutput::Stuck, Vec::new(), true)
}

fn case(leaves: Vec<LeafReport>, applied: &[&str], matched: &[&str]) -> CaseResult {
    let ids = |ids: &[&str]| ids.iter().map(|id| (*id).to_owned()).collect();
    CaseResult {
        leaves,
        work: 3,
        coverage: Some(RunCoverageOutput {
            applied: ids(applied),
            matched: ids(matched),
            offered: None,
        }),
        stack_stops: 0,
        smt_unknowns: 0,
        run_allowance_refusals: 0,
        load_records: Vec::new(),
        safety_limit_hit: false,
        failure: None,
    }
}

/// `div(10, 0)` on one path: the undefined step leaves the state before it as a `trivial` leaf,
/// not on whose path the step is, while coverage `applied` records the rule that built the
/// undefined-step entry.
fn undefined_div() -> CaseResult {
    case(
        vec![leaf(
            HaltReasonOutput::Trivial,
            vec![UncleanReason::Halt],
            false,
        )],
        &["id-div"],
        &["id-div"],
    )
}

/// `check(7)`: `check-hit`'s guard is entered and fails; `check-miss` fires and the run ends
/// naturally.
fn failing_guard() -> CaseResult {
    let mut end = natural_end();
    end.rewrites = vec!["id-check-miss".to_owned()];
    case(
        vec![end],
        &["id-check-miss"],
        &["id-check-hit", "id-check-miss"],
    )
}

#[test]
fn fired_and_covered_differ_on_an_undefined_step() {
    let result = undefined_div();
    for run_to_completion in [false, true] {
        assert_eq!(
            rule_reached("id-div", RuleMode::Fired, run_to_completion, &result),
            [false]
        );
        assert_eq!(
            rule_reached("id-div", RuleMode::Covered, run_to_completion, &result),
            [true]
        );
        assert_eq!(
            rule_reached(
                "id-div",
                RuleMode::ConditionReached,
                run_to_completion,
                &result
            ),
            [true]
        );
    }
    assert!(!blocked("id-div", result.coverage.as_ref()));
}

#[test]
fn condition_reached_holds_on_a_failing_guard_and_fired_and_covered_do_not() {
    let result = failing_guard();
    assert_eq!(
        rule_reached("id-check-hit", RuleMode::ConditionReached, false, &result),
        [true]
    );
    assert_eq!(
        rule_reached("id-check-hit", RuleMode::Covered, false, &result),
        [false]
    );
    assert_eq!(
        rule_reached("id-check-hit", RuleMode::Fired, true, &result),
        [false]
    );
    assert!(blocked("id-check-hit", result.coverage.as_ref()));
    assert!(!blocked("id-check-miss", result.coverage.as_ref()));
    assert!(!blocked("id-check-hit", None));
    // The rule that fired is on the leaf's trace.
    assert_eq!(
        rule_reached("id-check-miss", RuleMode::Fired, true, &result),
        [true]
    );
}

#[test]
fn a_terminal_halt_reaches_only_when_the_rule_is_the_only_stop_rule() {
    let terminal = || leaf(HaltReasonOutput::Terminal, Vec::new(), false);
    let result = case(vec![terminal(), natural_end()], &["id-div"], &["id-div"]);
    // Without run-to-completion the request's only terminal rule is the target's.
    assert_eq!(
        rule_reached("id-div", RuleMode::Fired, false, &result),
        [true, false]
    );
    // Under run-to-completion the request has no terminal rule, so a terminal halt names no
    // rule and only the trace counts.
    assert_eq!(
        rule_reached("id-div", RuleMode::Fired, true, &result),
        [false, false]
    );
}

#[test]
fn coverage_modes_attribute_the_run_to_a_leaf_only_when_every_leaf_could_carry_the_hit() {
    let stopped = || leaf(HaltReasonOutput::Stuck, Vec::new(), false);
    let undefined = || leaf(HaltReasonOutput::Trivial, vec![UncleanReason::Halt], false);
    // One leaf: the run is that leaf's path.
    let one = case(vec![stopped()], &["id-div"], &["id-div"]);
    for run_to_completion in [false, true] {
        assert_eq!(
            rule_reached("id-div", RuleMode::Covered, run_to_completion, &one),
            [true]
        );
    }
    // Several leaves, every one clean: every leaf reaches.
    let clean = case(vec![natural_end(), stopped()], &["id-div"], &["id-div"]);
    assert_eq!(
        rule_reached("id-div", RuleMode::Covered, false, &clean),
        [true, true]
    );
    // Under run-to-completion every leaf must also end naturally; the abnormal stop is the
    // only leaf the reach may be attributed to.
    assert_eq!(
        rule_reached("id-div", RuleMode::ConditionReached, true, &clean),
        [false, true]
    );
    // A leaf that is not clean may be the covering path: only it reaches, so no clean leaf
    // carries a hit.
    let mixed = case(vec![natural_end(), undefined()], &["id-div"], &["id-div"]);
    assert_eq!(
        rule_reached("id-div", RuleMode::Covered, false, &mixed),
        [false, true]
    );
    assert_eq!(
        rule_reached("id-check-hit", RuleMode::Covered, false, &mixed),
        [false, false]
    );
    let failed = CaseResult {
        coverage: None,
        failure: Some("stack segment refused".to_owned()),
        ..case(Vec::new(), &[], &[])
    };
    assert!(rule_reached("id-div", RuleMode::Covered, false, &failed).is_empty());
    assert!(rule_reached("id-div", RuleMode::Fired, false, &failed).is_empty());
}

#[test]
fn a_pattern_at_final_is_reached_by_every_matching_leaf() {
    let with_match = |mut leaf: LeafReport, matched: bool| {
        leaf.matches = vec![matched];
        leaf
    };
    let abnormal = leaf(HaltReasonOutput::Stuck, Vec::new(), false);
    let result = case(
        vec![
            with_match(natural_end(), true),
            with_match(natural_end(), false),
            with_match(abnormal, true),
        ],
        &[],
        &[],
    );
    assert_eq!(pattern_reached(&result), Ok(vec![true, false, true]));
    let unjudged = case(vec![natural_end()], &[], &[]);
    assert!(pattern_reached(&unjudged).is_err());
}

fn rule_target(id: &str, mode: RuleMode, run_to_completion: bool) -> ResolvedTarget {
    ResolvedTarget {
        target: Target {
            kind: TargetKind::Rule(super::RuleTarget {
                rule: RuleRef::UniqueId(id.to_owned()),
                mode,
            }),
            run_to_completion,
            negated_property: false,
        },
        resolved: Resolved::Rule {
            id: id.to_owned(),
            mode,
        },
        matchers: Vec::new(),
    }
}

fn judge(target: &ResolvedTarget, result: &CaseResult) -> Judgement {
    target.judge(result).expect("no engine defect")
}

#[test]
fn needs_follow_the_resolved_rule() {
    assert_eq!(
        rule_target("id-div", RuleMode::Fired, false).needs(),
        rule_needs("id-div", RuleMode::Fired, false)
    );
    assert_eq!(
        rule_target("id-div", RuleMode::Covered, true).needs(),
        TargetNeeds::default()
    );
}

#[test]
fn the_undefined_step_is_undefined_when_fired_and_an_unclean_reach_when_covered() {
    let result = undefined_div();
    let fired = judge(&rule_target("id-div", RuleMode::Fired, false), &result);
    assert_eq!(fired.class, OutcomeClass::Undefined);
    assert_eq!(fired.hit_leaf, None);
    // Covered reaches the rule, but on a leaf that is not clean: never a hit.
    let covered = judge(&rule_target("id-div", RuleMode::Covered, false), &result);
    assert_eq!(covered.class, OutcomeClass::Unsupported);
    assert_eq!(covered.hit_leaf, None);
    assert!(!covered.blocked);
}

#[test]
fn a_failing_guard_is_a_condition_reached_hit_and_a_blocked_miss_otherwise() {
    let result = failing_guard();
    let reached = judge(
        &rule_target("id-check-hit", RuleMode::ConditionReached, false),
        &result,
    );
    assert_eq!(
        reached,
        Judgement {
            class: OutcomeClass::Hit,
            hit_leaf: Some(0),
            blocked: true,
        }
    );
    for mode in [RuleMode::Fired, RuleMode::Covered] {
        let judgement = judge(&rule_target("id-check-hit", mode, true), &result);
        assert_eq!(judgement.class, OutcomeClass::Miss, "{mode:?}");
        assert!(judgement.blocked, "{mode:?}");
    }
}

#[test]
fn run_to_completion_needs_a_natural_end_and_a_bounded_reach_is_reached_unfinished() {
    let mut bounded = leaf(
        HaltReasonOutput::DepthBound,
        vec![UncleanReason::Halt],
        false,
    );
    bounded.rewrites = vec!["id-div".to_owned()];
    let cut = case(vec![bounded], &["id-div"], &["id-div"]);
    let unfinished = judge(&rule_target("id-div", RuleMode::Fired, true), &cut);
    assert_eq!(unfinished.class, OutcomeClass::ReachedUnfinished);
    assert_eq!(unfinished.hit_leaf, None);

    let mut stopped = leaf(HaltReasonOutput::Stuck, Vec::new(), false);
    stopped.rewrites = vec!["id-div".to_owned()];
    let result = case(vec![stopped], &["id-div"], &["id-div"]);
    let finished = judge(&rule_target("id-div", RuleMode::Fired, true), &result);
    assert_ne!(finished.class, OutcomeClass::Hit);
    assert_eq!(finished.hit_leaf, None);
    // Without run-to-completion a clean abnormal stop on the rule's path is a hit.
    let covered = judge(&rule_target("id-div", RuleMode::Covered, false), &result);
    assert_eq!(covered.class, OutcomeClass::Hit);
    assert_eq!(covered.hit_leaf, Some(0));
}

#[test]
fn a_coverage_hit_over_several_leaves_needs_every_leaf_clean() {
    let undefined = leaf(HaltReasonOutput::Trivial, vec![UncleanReason::Halt], false);
    let mixed = case(vec![natural_end(), undefined], &["id-div"], &["id-div"]);
    let judgement = judge(&rule_target("id-div", RuleMode::Covered, false), &mixed);
    assert_eq!(judgement.class, OutcomeClass::Unsupported);
    assert_eq!(judgement.hit_leaf, None);

    let clean = case(vec![natural_end(), natural_end()], &["id-div"], &["id-div"]);
    let judgement = judge(&rule_target("id-div", RuleMode::Covered, true), &clean);
    assert_eq!(judgement.class, OutcomeClass::Hit);
    assert_eq!(judgement.hit_leaf, Some(0));
}

fn pattern_target(run_to_completion: bool) -> ResolvedTarget {
    ResolvedTarget {
        target: Target {
            kind: TargetKind::Pattern(super::PatternTarget {
                pattern: "<out> 0 </out>".to_owned(),
                at: super::PatternAt::Final,
            }),
            run_to_completion,
            negated_property: false,
        },
        resolved: Resolved::PatternFinal,
        matchers: Vec::new(),
    }
}

#[test]
fn a_pattern_at_final_is_hit_by_a_clean_end_and_unsupported_on_an_unclean_match() {
    let mut abnormal = leaf(HaltReasonOutput::Stuck, Vec::new(), false);
    abnormal.matches = vec![true];
    let stopped = case(vec![abnormal], &[], &[]);
    let judgement = judge(&pattern_target(false), &stopped);
    assert_eq!(judgement.class, OutcomeClass::Hit);
    assert_eq!(judgement.hit_leaf, Some(0));
    assert!(!judgement.blocked);
    assert_ne!(
        judge(&pattern_target(true), &stopped).class,
        OutcomeClass::Hit
    );

    let mut chosen = leaf(
        HaltReasonOutput::Stuck,
        vec![UncleanReason::ImplementationChosenValue],
        false,
    );
    chosen.matches = vec![true];
    let unclean = case(vec![chosen], &[], &[]);
    assert_eq!(
        judge(&pattern_target(false), &unclean).class,
        OutcomeClass::Unsupported
    );
    assert_eq!(pattern_target(false).needs(), TargetNeeds::default());
}

#[test]
fn a_differential_target_is_not_judged_here() {
    let target = ResolvedTarget {
        target: Target {
            kind: TargetKind::Differential(super::DifferentialTarget {}),
            run_to_completion: false,
            negated_property: false,
        },
        resolved: Resolved::Differential,
        matchers: Vec::new(),
    };
    assert!(target.judge(&failing_guard()).is_err());
    assert_eq!(target.needs(), TargetNeeds::default());
}
