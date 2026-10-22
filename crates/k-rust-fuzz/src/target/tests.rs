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
    HitSite, Judgement, Resolved, ResolvedTarget, RuleMode, RuleRef, Target, TargetKind,
    pattern_reached,
    rule::{blocked, resolve_rule, rule_needs, rule_reached},
};
use crate::{
    error::TargetProblem,
    exec::{CaseResult, LeafReport, OutcomeClass, TargetNeeds, UncleanReason},
    spec::PathMode,
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
    // k-rust accepts `non-executable` only on function equations, but a KORE rewrite axiom
    // may carry it, and the catalog then reports the rewrite rule as not executable.
    let mut frozen = entry("id-frozen", Some("frozen"), Rewrite, 39);
    frozen.executable = false;
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
        frozen,
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
    assert_eq!(resolve(label("frozen")), Err(TargetProblem::NotExecutable));
    // A non-executable equation is refused as an equation, the refusal no attribute lifts.
    assert_eq!(resolve(label("dormant")), Err(TargetProblem::Equation));
    assert_eq!(resolve(label("double")), Err(TargetProblem::Equation));
    assert_eq!(resolve(label("simp")), Err(TargetProblem::Equation));
    assert_eq!(resolve(source("rules.k", 41)), Err(TargetProblem::Equation));
    assert_eq!(resolve(label("generated")), Err(TargetProblem::UnknownId));
}

#[test]
fn fired_always_traces_and_stops_early_without_run_to_completion() {
    let traced = TargetNeeds {
        trace: true,
        ..TargetNeeds::default()
    };
    // The early stop applies in both path modes (D18); the needs do not depend on the mode.
    assert_eq!(
        rule_needs("id-div", RuleMode::Fired, false),
        TargetNeeds {
            terminal_rules: vec!["id-div".to_owned()],
            ..traced.clone()
        }
    );
    assert_eq!(rule_needs("id-div", RuleMode::Fired, true), traced);
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
            conditions: None,
            applied_counts: None,
        }),
        stack_stops: 0,
        smt_unknowns: 0,
        run_allowance_refusals: 0,
        load_records: Vec::new(),
        safety_limit_hit: false,
        failure: None,
        run_facts_off_leaves: false,
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
fn fired_is_judged_from_the_trace_and_a_terminal_halt_decides_nothing_by_itself() {
    let terminal = || leaf(HaltReasonOutput::Terminal, Vec::new(), false);
    let mut stopped_on_rule = terminal();
    stopped_on_rule.rewrites = vec!["id-check-miss".to_owned(), "id-div".to_owned()];
    // A terminal halt whose trace does not end with the rule (another stop rule of some other
    // request shape) does not reach it; the early stop's trace ends with the rule's entry.
    let result = case(
        vec![terminal(), stopped_on_rule, natural_end()],
        &["id-div"],
        &["id-div"],
    );
    for run_to_completion in [false, true] {
        assert_eq!(
            rule_reached("id-div", RuleMode::Fired, run_to_completion, &result),
            [false, true, false]
        );
    }
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
    // An `Err` result has no leaf and no coverage.
    let failed = CaseResult {
        coverage: None,
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
        rule_target("id-div", RuleMode::Fired, false).needs(PathMode::AllPaths),
        rule_needs("id-div", RuleMode::Fired, false)
    );
    assert_eq!(
        rule_target("id-div", RuleMode::Fired, false).needs(PathMode::OnePath),
        rule_needs("id-div", RuleMode::Fired, false)
    );
    assert_eq!(
        rule_target("id-div", RuleMode::Covered, true).needs(PathMode::OnePath),
        TargetNeeds::default()
    );
}

#[test]
fn the_undefined_step_is_undefined_when_fired_and_an_unclean_reach_when_covered() {
    let result = undefined_div();
    let fired = judge(&rule_target("id-div", RuleMode::Fired, false), &result);
    assert_eq!(fired.class, OutcomeClass::Undefined);
    assert_eq!(fired.hit_site, None);
    // Covered reaches the rule, but on a leaf that is not clean: never a hit.
    let covered = judge(&rule_target("id-div", RuleMode::Covered, false), &result);
    assert_eq!(covered.class, OutcomeClass::Unsupported);
    assert_eq!(covered.hit_site, None);
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
            hit_site: Some(HitSite::Leaf(0)),
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
    assert_eq!(unfinished.hit_site, None);

    let mut stopped = leaf(HaltReasonOutput::Stuck, Vec::new(), false);
    stopped.rewrites = vec!["id-div".to_owned()];
    let result = case(vec![stopped], &["id-div"], &["id-div"]);
    let finished = judge(&rule_target("id-div", RuleMode::Fired, true), &result);
    assert_ne!(finished.class, OutcomeClass::Hit);
    assert_eq!(finished.hit_site, None);
    // Without run-to-completion a clean abnormal stop on the rule's path is a hit.
    let covered = judge(&rule_target("id-div", RuleMode::Covered, false), &result);
    assert_eq!(covered.class, OutcomeClass::Hit);
    assert_eq!(covered.hit_site, Some(HitSite::Leaf(0)));
}

#[test]
fn a_coverage_hit_over_several_leaves_needs_every_leaf_clean() {
    let undefined = leaf(HaltReasonOutput::Trivial, vec![UncleanReason::Halt], false);
    let mixed = case(vec![natural_end(), undefined], &["id-div"], &["id-div"]);
    let judgement = judge(&rule_target("id-div", RuleMode::Covered, false), &mixed);
    assert_eq!(judgement.class, OutcomeClass::Unsupported);
    assert_eq!(judgement.hit_site, None);

    // Every leaf clean: a hit of the run, which names no leaf (D13, D16).
    let clean = case(vec![natural_end(), natural_end()], &["id-div"], &["id-div"]);
    let judgement = judge(&rule_target("id-div", RuleMode::Covered, true), &clean);
    assert_eq!(judgement.class, OutcomeClass::Hit);
    assert_eq!(judgement.hit_site, Some(HitSite::Run));
}

#[test]
fn a_coverage_hit_on_all_paths_names_no_leaf_even_with_one_leaf_left() {
    // Phase-1 review N7: under all paths a sibling whose successor vanished may have put the
    // rule in coverage, so the one leaf left need not be on the reaching path.
    let one = case(vec![natural_end()], &["id-div"], &["id-div"]);
    for mode in [RuleMode::Covered, RuleMode::ConditionReached] {
        let target = rule_target("id-div", mode, false);
        let all_paths = target.judge_run(&one, true).expect("no engine defect");
        assert_eq!(all_paths.class, OutcomeClass::Hit, "{mode:?}");
        assert_eq!(all_paths.hit_site, Some(HitSite::Run), "{mode:?}");
        // On one path the run is the leaf's path.
        let one_path = target.judge_run(&one, false).expect("no engine defect");
        assert_eq!(one_path.hit_site, Some(HitSite::Leaf(0)), "{mode:?}");
    }
    // A fired target is judged from the leaf's own trace in both modes.
    let mut traced = natural_end();
    traced.rewrites = vec!["id-div".to_owned()];
    let fired = rule_target("id-div", RuleMode::Fired, false)
        .judge_run(&case(vec![traced], &["id-div"], &[]), true)
        .expect("no engine defect");
    assert_eq!(fired.hit_site, Some(HitSite::Leaf(0)));
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
    assert_eq!(judgement.hit_site, Some(HitSite::Leaf(0)));
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
    assert_eq!(
        pattern_target(false).needs(PathMode::AllPaths),
        TargetNeeds::default()
    );
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
    assert_eq!(target.needs(PathMode::OnePath), TargetNeeds::default());
}

#[test]
fn a_pattern_match_on_a_cut_leaf_does_not_reach_a_final_target() {
    let mut cut = leaf(
        HaltReasonOutput::DepthBound,
        vec![UncleanReason::Halt],
        false,
    );
    cut.matches = vec![true];
    let mut undefined = leaf(HaltReasonOutput::Trivial, vec![UncleanReason::Halt], false);
    undefined.matches = vec![true];
    let mut terminal = leaf(HaltReasonOutput::Terminal, Vec::new(), false);
    terminal.matches = vec![true];
    let ends = case(vec![cut.clone(), undefined, terminal], &[], &[]);
    assert_eq!(pattern_reached(&ends), Ok(vec![false, true, true]));

    let bounded = case(vec![cut], &[], &[]);
    for run_to_completion in [false, true] {
        let judgement = judge(&pattern_target(run_to_completion), &bounded);
        assert_eq!(
            judgement.class,
            OutcomeClass::DepthBound,
            "{run_to_completion}"
        );
        assert_eq!(judgement.hit_site, None);
    }
}

#[test]
fn a_coverage_hit_needs_every_run_fact_on_a_leaf() {
    // One clean natural end, coverage holding the rule, and a run fact (a vanished candidate's
    // chosen value or contradicted claim) on no leaf: the coverage may rest on that work.
    let mut end = natural_end();
    end.rewrites = vec!["id-div".to_owned()];
    for leaves in [vec![end.clone()], vec![end.clone(), end.clone()]] {
        let result = CaseResult {
            run_facts_off_leaves: true,
            ..case(leaves, &["id-div"], &["id-div"])
        };
        for mode in [RuleMode::Covered, RuleMode::ConditionReached] {
            let judgement = judge(&rule_target("id-div", mode, false), &result);
            assert_eq!(judgement.class, OutcomeClass::Unsupported, "{mode:?}");
            assert_eq!(judgement.hit_site, None);
        }
        // `fired` rests on the leaf's own trace, which the off-leaf facts do not touch.
        let fired = judge(&rule_target("id-div", RuleMode::Fired, true), &result);
        assert_eq!(fired.class, OutcomeClass::Hit);
    }
}

#[test]
fn a_stopped_leaf_reaches_a_coverage_target_only_from_its_rewrites() {
    // The step that built a work-bound, timeout or cancelled leaf's state is in coverage, but
    // that state is not a reached configuration (classify's cut-leaf contract, review 2 S1).
    for halt in [
        HaltReasonOutput::WorkBound,
        HaltReasonOutput::Timeout,
        HaltReasonOutput::Cancelled,
    ] {
        let stopped = leaf(halt, vec![UncleanReason::Halt], false);
        let halt_class = if halt == HaltReasonOutput::WorkBound {
            OutcomeClass::WorkBound
        } else {
            OutcomeClass::Timeout
        };
        // One leaf: coverage alone does not mark it, so it takes its halt's class.
        let alone = case(vec![stopped.clone()], &["id-div"], &["id-div"]);
        for mode in [RuleMode::Covered, RuleMode::ConditionReached] {
            for run_to_completion in [false, true] {
                assert_eq!(
                    rule_reached("id-div", mode, run_to_completion, &alone),
                    [false],
                    "{halt:?} {mode:?}"
                );
                let judgement = judge(&rule_target("id-div", mode, run_to_completion), &alone);
                assert_eq!(judgement.class, halt_class, "{halt:?} {mode:?}");
            }
        }
        // Several leaves, one of them stopped: the stopped leaf is not marked either, and no
        // clean leaf carries the run's fact.
        let mixed = case(
            vec![natural_end(), stopped.clone()],
            &["id-div"],
            &["id-div"],
        );
        for mode in [RuleMode::Covered, RuleMode::ConditionReached] {
            assert_eq!(
                rule_reached("id-div", mode, false, &mixed),
                [false, false],
                "{halt:?} {mode:?}"
            );
            let judgement = judge(&rule_target("id-div", mode, false), &mixed);
            assert_eq!(judgement.class, halt_class, "{halt:?} {mode:?}");
        }
        // An established step of the rule (the trace's last entry is already left out) marks
        // the leaf in both coverage modes, so it is `reached-unfinished` under
        // run-to-completion.
        let mut traced = stopped.clone();
        traced.rewrites = vec!["id-div".to_owned()];
        let established = case(vec![traced], &["id-div"], &["id-div"]);
        for mode in [RuleMode::Covered, RuleMode::ConditionReached] {
            assert_eq!(rule_reached("id-div", mode, true, &established), [true]);
            let judgement = judge(&rule_target("id-div", mode, true), &established);
            assert_eq!(
                judgement.class,
                OutcomeClass::ReachedUnfinished,
                "{halt:?} {mode:?}"
            );
        }
    }
    // A depth-bound leaf holds a normalized state, so coverage still marks it.
    let bounded = leaf(
        HaltReasonOutput::DepthBound,
        vec![UncleanReason::Halt],
        false,
    );
    let one = case(vec![bounded], &["id-div"], &["id-div"]);
    assert_eq!(
        rule_reached("id-div", RuleMode::Covered, true, &one),
        [true]
    );
}

#[test]
fn a_relative_source_names_its_own_file_and_an_absolute_one_falls_back_to_a_suffix() {
    let at = |id: &str, source: &str, line: u32| {
        let mut entry = entry(id, Some(id), CompiledRuleKind::Rewrite, line);
        entry.origins[0].source = Some(format!("Source({source})"));
        entry
    };
    let catalog = vec![
        at("top-12", "rules.k", 12),
        at("lib-12", "lib/rules.k", 12),
        at("lib-20", "lib/rules.k", 20),
        at("top-30", "rules.k", 30),
    ];
    let resolve = |given: &str, line| resolve_rule(&catalog, &source(given, line));
    // `lib/rules.k` names only the file `lib/rules.k`, never `rules.k`.
    assert_eq!(resolve("lib/rules.k", 12), Ok("lib-12".to_owned()));
    assert_eq!(resolve("lib/rules.k", 30), Err(TargetProblem::UnknownRule));
    assert_eq!(resolve("Source(lib/rules.k)", 20), Ok("lib-20".to_owned()));
    // `rules.k` is a suffix of both paths at a `/`.
    assert_eq!(
        resolve("rules.k", 12),
        Err(TargetProblem::AmbiguousRule(vec![
            "lib-12".to_owned(),
            "top-12".to_owned()
        ]))
    );
    // An absolute path ends with the catalog's relative path.
    assert_eq!(
        resolve("/work/defs/lib/rules.k", 20),
        Ok("lib-20".to_owned())
    );
    assert_eq!(resolve("/work/defs/rules.k", 30), Ok("top-30".to_owned()));
    // At line 12 both relative paths are suffixes of the absolute one: refused, not guessed.
    assert!(matches!(
        resolve("/work/defs/lib/rules.k", 12),
        Err(TargetProblem::AmbiguousRule(_))
    ));
}
