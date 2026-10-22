//! Tests of execution and classification (FZ-04): the request shape, the clean-leaf rule, the
//! natural end, the leaf matcher, every halt's class, the precedence and the determinism
//! counters.
//!
//! The executor and the classifier are crate-private, so these are unit tests. They run FZ-FIX's
//! fixture definitions through the crate's test-only `support` module (`tests/support`).

use k_rust::{
    backend::{
        CancellationToken, ExecutionStrategy, HaltReasonOutput, ResultModalityOutput, StopCause,
    },
    kore::{ast::Pattern as KorePattern, parser::parse_pattern, printer::Printer as KorePrinter},
};

use super::{run::PatternCompiler, *};
use crate::{error::CampaignError, spec::DEFAULT_MAX_WORK};

use crate::support::{self, Compiled};

// ---------------------------------------------------------------- fixtures

fn imp() -> &'static Compiled {
    support::IMP.compiled()
}

fn rules() -> &'static Compiled {
    support::RULES.compiled()
}

fn chosen() -> &'static Compiled {
    support::CHOSEN.compiled()
}

fn loadclaim() -> &'static Compiled {
    support::LOADCLAIM.compiled()
}

fn taint() -> &'static Compiled {
    support::TAINT.compiled()
}

/// The default options, under the default work bound, and options without any work budget
/// (`max_depth` only), under which a leaf carries only its own path facts.
fn budgets() -> [CaseOptions; 2] {
    [
        CaseOptions::default(),
        CaseOptions {
            max_depth: Some(10_000),
            ..CaseOptions::default()
        },
    ]
}

const DIV_IMP: &str = include_str!("../../tests/data/imp/div.imp");
const LOOP_IMP: &str = include_str!("../../tests/data/imp/loop.imp");

/// Running FZ-FIX's compiled fixtures through the executor.
trait Run {
    /// The initial configuration of `text`, as `krun --io off` assembles it.
    fn initial_of(&self, text: &str) -> KorePattern;
    fn executor(&self, options: &CaseOptions) -> Executor;
    /// Run `text` with `options` and `needs`, judging the leaves against `patterns`.
    fn run_with(
        &self,
        text: &str,
        options: &CaseOptions,
        needs: &TargetNeeds,
        patterns: &[&str],
    ) -> CaseResult;
    fn run(&self, text: &str) -> CaseResult {
        self.run_with(text, &CaseOptions::default(), &TargetNeeds::default(), &[])
    }
}

impl Run for Compiled {
    fn initial_of(&self, text: &str) -> KorePattern {
        self.assemble("program", text, &[])
            .unwrap_or_else(|error| panic!("{text} does not assemble: {error}"))
    }

    fn executor(&self, options: &CaseOptions) -> Executor {
        Executor::with_backend(
            self.source_backend(),
            &self.grammar,
            &self.definition(),
            options,
        )
        .expect("the executor builds")
    }

    fn run_with(
        &self,
        text: &str,
        options: &CaseOptions,
        needs: &TargetNeeds,
        patterns: &[&str],
    ) -> CaseResult {
        let definition = self.definition();
        let mut executor = self.executor(options);
        let matchers: Vec<LeafMatcher> = patterns
            .iter()
            .map(|pattern| {
                LeafMatcher::compile_with(&mut executor, &self.grammar, &definition, pattern)
                    .unwrap_or_else(|error| panic!("{pattern} does not compile: {error}"))
            })
            .collect();
        let matchers: Vec<&LeafMatcher> = matchers.iter().collect();
        let shape = CaseRequestShape::new(options, needs);
        executor
            .run(&self.initial_of(text), &shape, &matchers, None)
            .expect("no solver prelude fails")
    }
}

fn only_leaf(result: &CaseResult) -> &LeafReport {
    assert!(result.failure.is_none(), "{:?}", result.failure);
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    &result.leaves[0]
}

fn class(result: &CaseResult, reached: &[bool], run_to_completion: bool) -> OutcomeClass {
    classify(result, reached, run_to_completion).expect("no engine defect")
}

// ---------------------------------------------------------------- the request (5.1)

#[test]
fn the_request_follows_the_options_and_the_target_needs() {
    let shape = CaseRequestShape::new(&CaseOptions::default(), &TargetNeeds::default());
    let request = &shape.request;
    assert!(matches!(request.strategy, ExecutionStrategy::Any));
    assert_eq!(request.result_modality, ResultModalityOutput::PathSet);
    assert_eq!(request.max_depth, None);
    assert_eq!(request.max_work, Some(DEFAULT_MAX_WORK));
    assert_eq!(request.max_breadth, None);
    assert!(request.collect_coverage);
    assert!(!request.collect_offered);
    assert!(!request.collect_counts);
    let counting = shape.with_counts();
    assert!(counting.request.collect_counts && counting.request.collect_coverage);
    assert!(!request.trace);
    assert!(request.terminal_rules.is_empty());
    assert!(!request.stop_at_branch);
    assert!(request.cut_point_rules.is_empty());
    assert_eq!(request.step_timeout_ms, None);
    assert!(!request.moving_average_timeout);
    assert!(!request.assume_state_defined);
    assert_eq!(request.module_name, None);
    assert!(!shape.constructor_only);

    let options = CaseOptions {
        max_depth: Some(5),
        max_simplification_iterations: 7,
        ..CaseOptions::default()
    };
    let needs = TargetNeeds {
        trace: true,
        terminal_rules: vec!["rule-id".to_owned()],
        constructor_only: true,
        paths: Some(PathMode::AllPaths),
    };
    let shape = CaseRequestShape::new(&options, &needs);
    let state = parse_pattern(r"\top{SortGeneratedTopCell{}}()").expect("a pattern");
    let request = shape.request(state.clone());
    assert_eq!(request.state, state);
    assert!(matches!(request.strategy, ExecutionStrategy::All));
    assert_eq!(request.max_depth, Some(5));
    assert_eq!(request.max_work, None);
    assert_eq!(request.max_simplification_iterations, 7);
    assert!(request.trace);
    assert_eq!(request.terminal_rules, ["rule-id"]);
    assert!(shape.constructor_only);
}

// ---------------------------------------------------------------- clean leaves (5.2)

#[test]
fn an_imp_natural_end_with_three_state_entries_is_clean_and_a_miss() {
    let result = imp().run(DIV_IMP);
    let leaf = only_leaf(&result);
    assert_eq!(leaf.halt, HaltReasonOutput::Stuck);
    let text = KorePrinter::compact().print_pattern(&leaf.state);
    assert_eq!(
        text.matches(r"Lbl'UndsPipe'-'-GT-Unds'{}").count(),
        3,
        "{text}"
    );
    assert!(leaf.unclean.is_empty(), "{:?}", leaf.unclean);
    assert!(leaf.natural_end);
    assert_eq!(class(&result, &[false], false), OutcomeClass::Miss);
    assert_eq!(class(&result, &[true], true), OutcomeClass::Hit);
    assert!(result.determinism_breaks().is_empty());
    assert!(result.load_records.is_empty());
    assert!(result.work > 0);
    assert!(result.coverage.is_some());
}

#[test]
fn a_leaf_holding_a_lookup_of_a_missing_key_is_not_ceil_free() {
    let result = imp().run(DIV_IMP);
    let end = KorePrinter::compact().print_pattern(&only_leaf(&result).state);
    // `<k> .Map [ 1 ] </k>`: `Map:lookup` is a partial function, undefined on a missing key.
    let lookup = r#"kseq{}(LblMap'Coln'lookup{}(Lbl'Stop'Map{}(), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1"))), dotk{}())"#;
    assert_eq!(end.matches("dotk{}()").count(), 1, "{end}");
    let partial = parse_pattern(&end.replace("dotk{}()", lookup)).expect("the edited state");
    let mut executor = imp().executor(&CaseOptions::default());
    let reasons = executor.judge_stuck_state(partial);
    assert!(reasons.contains(&UncleanReason::NotCeilFree), "{reasons:?}");
    // The unedited end is ceil-free.
    let reasons = executor.judge_stuck_state(only_leaf(&result).state.clone());
    assert!(reasons.is_empty(), "{reasons:?}");
}

#[test]
fn a_natural_looking_end_holding_a_partial_application_is_not_ceil_free() {
    // With the default work bound every leaf carries every run fact; without a budget only
    // the leaf's own diagnostics count (review S5).
    for options in budgets() {
        // `get(2)`: `find(1 |-> 10, 2)` stays unevaluated on a `stuck` leaf with an empty `<k>`, no
        // constraint and no diagnostic; the other leaf is the undefined step.
        let result = taint().run_with("get(2)", &options, &TargetNeeds::default(), &[]);
        assert!(result.failure.is_none(), "{:?}", result.failure);
        let stuck: Vec<&LeafReport> = result
            .leaves
            .iter()
            .filter(|leaf| leaf.halt == HaltReasonOutput::Stuck)
            .collect();
        assert_eq!(stuck.len(), 1, "{result:#?}");
        assert_eq!(stuck[0].unclean, [UncleanReason::NotCeilFree]);
        assert!(!stuck[0].natural_end);
        for run_to_completion in [false, true] {
            for reached in [false, true] {
                let reached = vec![reached; result.leaves.len()];
                assert_eq!(
                    class(&result, &reached, run_to_completion),
                    OutcomeClass::Unsupported
                );
            }
        }
        let anchor = taint().run_with("get(1)", &options, &TargetNeeds::default(), &[]);
        assert!(only_leaf(&anchor).natural_end);
    }
}

#[test]
fn a_leaf_carrying_a_run_observed_contradicted_claim_is_unsupported() {
    // With the default work bound every leaf carries every run fact; without a budget only
    // the leaf's own diagnostics count (review S5).
    for options in budgets() {
        let result = taint().run_with("guard(0)", &options, &TargetNeeds::default(), &[]);
        let leaf = only_leaf(&result);
        assert_eq!(leaf.halt, HaltReasonOutput::Stuck);
        assert_eq!(leaf.unclean, [UncleanReason::ContradictedClaim]);
        assert!(!leaf.natural_end);
        for reached in [false, true] {
            assert_eq!(class(&result, &[reached], false), OutcomeClass::Unsupported);
        }
        let anchor = taint().run_with("guard(5)", &options, &TargetNeeds::default(), &[]);
        assert!(only_leaf(&anchor).natural_end);
        assert_eq!(class(&anchor, &[true], true), OutcomeClass::Hit);
    }
}

#[test]
fn a_division_by_zero_is_a_clean_abnormal_stop() {
    let result = imp().run(&DIV_IMP.replace("y = 2;", "y = 0;"));
    let leaf = only_leaf(&result);
    assert_eq!(leaf.halt, HaltReasonOutput::Stuck);
    assert!(leaf.is_clean(), "{:?}", leaf.unclean);
    assert!(!leaf.natural_end);
    assert_eq!(class(&result, &[false], false), OutcomeClass::Stuck);
    assert_eq!(class(&result, &[true], false), OutcomeClass::Hit);
    assert_eq!(
        class(&result, &[true], true),
        OutcomeClass::ReachedUnfinished
    );
}

#[test]
fn small_depth_and_work_bounds_class_as_depth_bound_and_work_bound() {
    let depth = CaseOptions {
        max_depth: Some(20),
        ..CaseOptions::default()
    };
    let result = imp().run_with(LOOP_IMP, &depth, &TargetNeeds::default(), &[]);
    let leaf = only_leaf(&result);
    assert_eq!(leaf.halt, HaltReasonOutput::DepthBound);
    assert_eq!(leaf.unclean, [UncleanReason::Halt]);
    assert_eq!(class(&result, &[false], false), OutcomeClass::DepthBound);
    assert_eq!(class(&result, &[true], false), OutcomeClass::Unsupported);
    assert_eq!(
        class(&result, &[true], true),
        OutcomeClass::ReachedUnfinished
    );

    let work = CaseOptions {
        max_work: Some(20),
        ..CaseOptions::default()
    };
    let result = imp().run_with(LOOP_IMP, &work, &TargetNeeds::default(), &[]);
    let leaf = only_leaf(&result);
    assert_eq!(leaf.halt, HaltReasonOutput::WorkBound);
    assert_eq!(class(&result, &[false], false), OutcomeClass::WorkBound);
    assert_eq!(result.work, 20);

    let result = imp().run(LOOP_IMP);
    let leaf = only_leaf(&result);
    assert!(leaf.natural_end, "{:?}", leaf.unclean);
    assert_eq!(class(&result, &[false], false), OutcomeClass::Miss);
}

#[test]
fn an_undefined_step_is_undefined_and_never_a_hit() {
    let result = rules().run("div(10, 0)");
    let leaf = only_leaf(&result);
    assert_eq!(leaf.halt, HaltReasonOutput::Trivial);
    assert_eq!(leaf.unclean, [UncleanReason::Halt]);
    assert_eq!(class(&result, &[false], false), OutcomeClass::Undefined);
    // Reaching the target and then an undefined step: unfinished under run-to-completion, a
    // target-reaching leaf that is not clean otherwise.
    assert_eq!(class(&result, &[true], false), OutcomeClass::Unsupported);
    assert_eq!(
        class(&result, &[true], true),
        OutcomeClass::ReachedUnfinished
    );
    let anchor = rules().run("div(10, 2)");
    assert!(only_leaf(&anchor).natural_end);
}

#[test]
fn a_chosen_value_leaf_is_unsupported_never_a_miss_or_a_hit() {
    // With the default work bound every leaf carries every run fact; without a budget only
    // the leaf's own diagnostics count (review S5).
    for options in budgets() {
        let result = chosen().run_with("listKeys(1, 2)", &options, &TargetNeeds::default(), &[]);
        let leaf = only_leaf(&result);
        assert_eq!(leaf.halt, HaltReasonOutput::Stuck);
        assert!(
            leaf.unclean
                .contains(&UncleanReason::ImplementationChosenValue),
            "{:?}",
            leaf.unclean
        );
        assert!(!leaf.natural_end);
        for reached in [false, true] {
            for run_to_completion in [false, true] {
                assert_eq!(
                    class(&result, &[reached], run_to_completion),
                    OutcomeClass::Unsupported
                );
            }
        }
        let set = chosen().run_with("listSet(1, 2)", &options, &TargetNeeds::default(), &[]);
        assert_eq!(class(&set, &[false], false), OutcomeClass::Unsupported);
        // One key: the listing is determined, no mark.
        let determined =
            chosen().run_with("listKeys(1, 1)", &options, &TargetNeeds::default(), &[]);
        assert!(only_leaf(&determined).natural_end);
        assert_eq!(class(&determined, &[false], false), OutcomeClass::Miss);
    }
}

#[test]
fn records_the_load_observed_do_not_taint_leaves() {
    let result = loadclaim().run_with(
        "go(101)",
        &CaseOptions::default(),
        &TargetNeeds::default(),
        &["<out> 1 </out>"],
    );
    let leaf = only_leaf(&result);
    assert!(
        result
            .load_records
            .iter()
            .any(|record| record.kind == "contradicted-claim"),
        "{:?}",
        result.load_records
    );
    assert!(leaf.is_clean(), "{:?}", leaf.unclean);
    assert!(leaf.natural_end);
    assert_eq!(leaf.matches, [true]);
    assert!(result.determinism_breaks().is_empty());
    assert_eq!(class(&result, &leaf.matches, false), OutcomeClass::Hit);
}

#[test]
fn a_terminal_halt_on_the_only_stop_rule_is_a_clean_hit_candidate() {
    let fixture = rules();
    let id = fixture
        .source_backend()
        .rule_catalog(None)
        .expect("a catalog")
        .into_iter()
        .find(|entry| {
            entry
                .label
                .as_deref()
                .is_some_and(|label| label.ends_with("div"))
        })
        .expect("the div rule")
        .id;
    let needs = TargetNeeds {
        terminal_rules: vec![id],
        ..TargetNeeds::default()
    };
    let result = fixture.run_with("div(10, 2)", &CaseOptions::default(), &needs, &[]);
    let leaf = only_leaf(&result);
    assert_eq!(leaf.halt, HaltReasonOutput::Terminal);
    assert!(leaf.is_clean(), "{:?}", leaf.unclean);
    assert!(!leaf.natural_end);
    assert_eq!(class(&result, &[true], false), OutcomeClass::Hit);
    assert!(classify(&result, &[false], false).is_err());
}

// ---------------------------------------------------------------- the leaf matcher

#[test]
fn a_pattern_target_is_matched_with_its_requires() {
    let result = imp().run_with(
        DIV_IMP,
        &CaseOptions::default(),
        &TargetNeeds::default(),
        &[
            "<state> M </state> requires size(M) ==Int 3",
            "<state> M </state> requires size(M) ==Int 4",
            "<k> .K </k>",
        ],
    );
    let leaf = only_leaf(&result);
    assert!(leaf.is_clean(), "{:?}", leaf.unclean);
    assert_eq!(leaf.matches, [true, false, true]);
}

#[test]
fn a_match_that_rests_on_an_implementation_chosen_value_is_undecided() {
    // `Set2List` of a two-element set lists it in an order the definition leaves open; the
    // execution-mode match reads k-rust's order, and the proof-mode match does not decide. The
    // leaf itself (`listKeys(1, 1)`, one key) carries no mark.
    let result = chosen().run_with(
        "listKeys(1, 1)",
        &CaseOptions::default(),
        &TargetNeeds::default(),
        &[
            "<out> L </out> requires size(Set2List(List2Set(L ListItem(2)))) ==Int 2",
            "<out> L </out> requires size(L) ==Int 1",
        ],
    );
    let leaf = only_leaf(&result);
    assert!(
        leaf.unclean.contains(&UncleanReason::UndecidedMatch),
        "{:?}",
        leaf.unclean
    );
    assert_eq!(leaf.matches, [false, true]);
    assert!(!leaf.natural_end);
    assert_eq!(class(&result, &[false], false), OutcomeClass::Unsupported);
}

#[test]
fn matches_are_judged_on_unclean_decidable_leaves() {
    let result = chosen().run_with(
        "listKeys(1, 2)",
        &CaseOptions::default(),
        &TargetNeeds::default(),
        &["<k> .K </k>"],
    );
    let leaf = only_leaf(&result);
    assert!(!leaf.is_clean());
    assert_eq!(leaf.matches, [true]);
    assert_eq!(
        class(&result, &leaf.matches, false),
        OutcomeClass::Unsupported
    );
}

#[test]
fn constructor_only_is_judged_when_asked() {
    let needs = TargetNeeds {
        constructor_only: true,
        ..TargetNeeds::default()
    };
    let result = rules().run_with("div(10, 2)", &CaseOptions::default(), &needs, &[]);
    assert_eq!(only_leaf(&result).constructor_only, Some(true));
    let result = rules().run("div(10, 2)");
    assert_eq!(only_leaf(&result).constructor_only, None);
}

#[test]
fn a_normal_end_pattern_that_does_not_compile_is_refused() {
    let options = CaseOptions {
        normal_end_pattern: Some("<nosuchcell> .K </nosuchcell>".to_owned()),
        ..CaseOptions::default()
    };
    let error = Executor::with_backend(
        imp().source_backend(),
        &imp().grammar,
        &imp().definition(),
        &options,
    )
    .err()
    .expect("the pattern is refused");
    assert!(
        matches!(error, CampaignError::NormalEndPattern { .. }),
        "{error:?}"
    );
}

#[test]
fn a_supplied_normal_end_pattern_decides_natural_ends() {
    let options = CaseOptions {
        normal_end_pattern: Some("<k> .K </k> <out> 5 </out>".to_owned()),
        ..CaseOptions::default()
    };
    let five = rules().run_with("div(10, 2)", &options, &TargetNeeds::default(), &[]);
    assert!(only_leaf(&five).natural_end);
    let four = rules().run_with("div(8, 2)", &options, &TargetNeeds::default(), &[]);
    assert!(!only_leaf(&four).natural_end);
    assert_eq!(class(&four, &[false], false), OutcomeClass::Stuck);
}

// ---------------------------------------------------------------- stops and refusals

#[test]
fn a_cancelled_caller_makes_the_case_a_timeout_outside_the_contract() {
    let fixture = imp();
    let options = CaseOptions::default();
    let mut executor = fixture.executor(&options);
    let shape = CaseRequestShape::new(&options, &TargetNeeds::default());
    let token = CancellationToken::new();
    token.cancel();
    let result = executor
        .run(&fixture.initial_of(DIV_IMP), &shape, &[], Some(&token))
        .expect("no solver prelude fails");
    let reached = vec![false; result.leaves.len()];
    assert_eq!(class(&result, &reached, false), OutcomeClass::Timeout);
    assert!(
        result
            .determinism_breaks()
            .contains(&DeterminismBreak::Clock)
    );
    assert!(!result.safety_limit_hit);
}

#[test]
fn a_safety_limit_that_does_not_fire_changes_nothing() {
    let options = CaseOptions {
        safety_limit_ms: Some(600_000),
        ..CaseOptions::default()
    };
    let result = imp().run_with(DIV_IMP, &options, &TargetNeeds::default(), &[]);
    assert!(!result.safety_limit_hit);
    assert!(only_leaf(&result).natural_end);
    assert_eq!(class(&result, &[false], false), OutcomeClass::Miss);
    assert!(result.determinism_breaks().is_empty());
}

#[test]
fn a_state_the_backend_refuses_is_rejected() {
    let fixture = imp();
    let options = CaseOptions::default();
    let mut executor = fixture.executor(&options);
    let shape = CaseRequestShape::new(&options, &TargetNeeds::default());
    let state = parse_pattern(r"LblNoSuchSymbol'Unds'{}()").expect("a pattern");
    let result = executor
        .run(&state, &shape, &[], None)
        .expect("no solver prelude fails");
    let failure = result.failure.as_ref().expect("the state is refused");
    assert_eq!(failure.cause, FailureCause::StateRefused, "{failure:?}");
    assert_eq!(class(&result, &[], false), OutcomeClass::Rejected);
}

// ---------------------------------------------------------------- classification (5.3)

fn leaf(halt: HaltReasonOutput, unclean: &[UncleanReason], natural_end: bool) -> LeafReport {
    LeafReport {
        halt,
        depth: 3,
        state: parse_pattern(r"\top{SortGeneratedTopCell{}}()").expect("a pattern"),
        unclean: unclean.to_vec(),
        natural_end,
        matches: Vec::new(),
        rewrites: Vec::new(),
        constructor_only: None,
    }
}

fn natural() -> LeafReport {
    leaf(HaltReasonOutput::Stuck, &[], true)
}

fn abnormal() -> LeafReport {
    leaf(HaltReasonOutput::Stuck, &[], false)
}

fn halted(halt: HaltReasonOutput) -> LeafReport {
    leaf(halt, &[UncleanReason::Halt], false)
}

fn result(leaves: Vec<LeafReport>) -> CaseResult {
    CaseResult {
        leaves,
        work: 1,
        coverage: None,
        stack_stops: 0,
        smt_unknowns: 0,
        run_allowance_refusals: 0,
        load_records: Vec::new(),
        safety_limit_hit: false,
        failure: None,
        run_facts_off_leaves: false,
    }
}

#[test]
fn every_halt_has_a_class() {
    use HaltReasonOutput as H;
    for halt in H::ALL {
        let expected = match halt {
            H::Cancelled | H::Timeout => Some(OutcomeClass::Timeout),
            H::Stuck => Some(OutcomeClass::Stuck),
            H::Trivial => Some(OutcomeClass::Undefined),
            H::Vacuous | H::Indeterminate | H::UnsupportedHook | H::SimplificationError => {
                Some(OutcomeClass::Unsupported)
            }
            H::DepthBound | H::BreadthBound => Some(OutcomeClass::DepthBound),
            H::WorkBound => Some(OutcomeClass::WorkBound),
            H::Branch | H::CutPoint | H::Terminal => None,
        };
        let leaf = if halt == H::Stuck {
            abnormal()
        } else {
            halted(halt)
        };
        let got = classify(&result(vec![leaf]), &[false], false).ok();
        assert_eq!(got, expected, "{halt:?}");
    }
    // `vacuous` at depth 0 on every leaf: the initial state has no instance.
    let mut initial = halted(H::Vacuous);
    initial.depth = 0;
    assert_eq!(
        class(&result(vec![initial.clone()]), &[false], false),
        OutcomeClass::Rejected
    );
    assert_eq!(
        class(&result(Vec::new()), &[], false),
        OutcomeClass::Rejected
    );
    assert_eq!(
        class(&result(vec![initial, natural()]), &[false, false], false),
        OutcomeClass::Unsupported
    );
}

#[test]
fn branch_cut_point_and_an_unreached_terminal_are_engine_defects() {
    for halt in [HaltReasonOutput::Branch, HaltReasonOutput::CutPoint] {
        assert!(classify(&result(vec![halted(halt)]), &[true], false).is_err());
    }
    let terminal = leaf(HaltReasonOutput::Terminal, &[], false);
    assert!(classify(&result(vec![terminal.clone()]), &[false], false).is_err());
    assert_eq!(
        class(&result(vec![terminal]), &[true], false),
        OutcomeClass::Hit
    );
    assert!(classify(&result(vec![natural()]), &[], false).is_err());
}

#[test]
fn a_leaf_unclean_beyond_its_halt_is_unsupported_whether_or_not_it_reaches() {
    use UncleanReason as U;
    let reasons = [
        U::Undecided,
        U::NotCeilFree,
        U::ImplementationChosenValue,
        U::ContradictedClaim,
        U::IterationExhaustion,
        U::StackStops,
        U::SmtUnknowns,
        U::AllowanceRefusal,
        U::Internalization("x".to_owned()),
        U::SimplificationFailure,
        U::UndecidedMatch,
        U::UnsupportedHook,
    ];
    for reason in reasons {
        for halt in [HaltReasonOutput::Stuck, HaltReasonOutput::DepthBound] {
            let mut unclean = vec![reason.clone()];
            if halt != HaltReasonOutput::Stuck {
                unclean.insert(0, U::Halt);
            }
            for reached in [false, true] {
                for run_to_completion in [false, true] {
                    let case = result(vec![leaf(halt, &unclean, false), natural()]);
                    assert_eq!(
                        class(&case, &[reached, false], run_to_completion),
                        OutcomeClass::Unsupported,
                        "{reason:?} {halt:?} {reached} {run_to_completion}"
                    );
                }
            }
        }
    }
}

#[test]
fn the_precedence_is_d13s() {
    use HaltReasonOutput as H;
    // From the strongest down: each case has the class's leaf and every weaker one.
    let ladder: [(LeafReport, bool, OutcomeClass); 9] = [
        (natural(), true, OutcomeClass::Hit),
        (halted(H::Indeterminate), false, OutcomeClass::Unsupported),
        (halted(H::DepthBound), true, OutcomeClass::ReachedUnfinished),
        (halted(H::Timeout), false, OutcomeClass::Timeout),
        (halted(H::WorkBound), false, OutcomeClass::WorkBound),
        (halted(H::BreadthBound), false, OutcomeClass::DepthBound),
        (halted(H::Trivial), false, OutcomeClass::Undefined),
        (abnormal(), false, OutcomeClass::Stuck),
        (natural(), false, OutcomeClass::Miss),
    ];
    for start in 0..ladder.len() {
        let rest = &ladder[start..];
        let leaves = rest.iter().map(|(leaf, _, _)| leaf.clone()).collect();
        let reached: Vec<bool> = rest.iter().map(|(_, reached, _)| *reached).collect();
        // Under run-to-completion the reaching natural end is still a hit candidate, and the
        // reaching depth-bound leaf is `reached-unfinished`. The timeout leaf breaks the
        // determinism contract, so the hit candidate counts as `timeout` and the `unsupported`
        // leaf wins; a hit is checked separately below.
        let case = result(leaves);
        let expected = rest[0].2;
        let expected = if expected == OutcomeClass::Hit {
            OutcomeClass::Unsupported
        } else {
            expected
        };
        assert_eq!(
            class(&case, &reached, true),
            expected,
            "from {:?}",
            rest[0].2
        );
    }
    let hit = result(vec![natural(), halted(H::Indeterminate)]);
    assert_eq!(class(&hit, &[true, false], true), OutcomeClass::Hit);
    // `reached-unfinished` needs run-to-completion; without it the reaching cut leaf is
    // `unsupported` (a target-reaching leaf that is not clean).
    let cut = result(vec![halted(H::DepthBound), natural()]);
    assert_eq!(
        class(&cut, &[true, false], false),
        OutcomeClass::Unsupported
    );
    assert_eq!(
        class(&cut, &[true, false], true),
        OutcomeClass::ReachedUnfinished
    );
    // Under run-to-completion a reaching clean leaf that is not a natural end is unfinished.
    let stopped = result(vec![abnormal()]);
    assert_eq!(
        class(&stopped, &[true], true),
        OutcomeClass::ReachedUnfinished
    );
    assert_eq!(class(&stopped, &[true], false), OutcomeClass::Hit);
    // `unsupported` wins over `reached-unfinished`.
    let both = result(vec![halted(H::DepthBound), halted(H::UnsupportedHook)]);
    assert_eq!(
        class(&both, &[true, false], true),
        OutcomeClass::Unsupported
    );
}

#[test]
fn a_hit_outside_the_determinism_contract_is_not_a_hit() {
    let mut cancelled = result(vec![natural(), halted(HaltReasonOutput::Cancelled)]);
    assert_eq!(
        class(&cancelled, &[true, false], false),
        OutcomeClass::Timeout
    );
    cancelled.leaves.pop();
    cancelled.safety_limit_hit = true;
    assert_eq!(class(&cancelled, &[true], false), OutcomeClass::Timeout);
    assert_eq!(class(&cancelled, &[false], false), OutcomeClass::Timeout);

    let mut load = result(vec![natural()]);
    load.load_records.push(LoadRecord {
        kind: LOAD_STACK_STOP.to_owned(),
        detail: "1".to_owned(),
    });
    assert_eq!(class(&load, &[true], false), OutcomeClass::Unsupported);
    assert_eq!(class(&load, &[false], false), OutcomeClass::Miss);
    // Other load records are facts about the definition (T-5).
    load.load_records[0].kind = "contradicted-claim".to_owned();
    assert_eq!(class(&load, &[true], false), OutcomeClass::Hit);
}

#[test]
fn an_err_result_is_classed_by_its_cause() {
    let failed = |cause: FailureCause| CaseResult {
        failure: Some(CaseFailure {
            message: "m".to_owned(),
            cause,
        }),
        ..result(Vec::new())
    };
    let cases = [
        (
            FailureCause::Stop(StopCause::Cancelled),
            OutcomeClass::Timeout,
        ),
        (FailureCause::StateRefused, OutcomeClass::Rejected),
        (FailureCause::Other, OutcomeClass::Unsupported),
    ];
    for (cause, expected) in cases {
        assert_eq!(
            class(&failed(cause.clone()), &[], false),
            expected,
            "{cause:?}"
        );
    }
    let mut limited = failed(FailureCause::Other);
    limited.safety_limit_hit = true;
    assert_eq!(class(&limited, &[], false), OutcomeClass::Timeout);
    assert_eq!(
        failed(FailureCause::Stop(StopCause::Cancelled)).determinism_breaks(),
        [DeterminismBreak::Clock]
    );
    assert!(failed(FailureCause::Other).determinism_breaks().is_empty());
    assert_eq!(CaseFailure::other("x").cause, FailureCause::Other);
}

#[test]
fn determinism_breaks_name_every_source() {
    assert!(result(vec![natural()]).determinism_breaks().is_empty());
    let mut all = result(vec![halted(HaltReasonOutput::Timeout)]);
    all.smt_unknowns = 1;
    all.stack_stops = 2;
    all.run_allowance_refusals = 1;
    assert_eq!(
        all.determinism_breaks(),
        [
            DeterminismBreak::Clock,
            DeterminismBreak::SmtUnknowns,
            DeterminismBreak::StackStops,
            DeterminismBreak::AllowanceRefusal,
        ]
    );
    let mut limit = result(vec![natural()]);
    limit.safety_limit_hit = true;
    assert_eq!(limit.determinism_breaks(), [DeterminismBreak::Clock]);
    let mut load = result(vec![natural()]);
    load.load_records.push(LoadRecord {
        kind: LOAD_STACK_STOP.to_owned(),
        detail: String::new(),
    });
    assert_eq!(load.determinism_breaks(), [DeterminismBreak::StackStops]);
}

#[test]
fn the_class_names_and_key_order_are_fixed() {
    // The report's maps are keyed by the derived order, which is declaration order (FZ-01
    // review S14): a reordering changes report bytes.
    let names: Vec<&str> = OutcomeClass::ALL.iter().map(|class| class.name()).collect();
    assert_eq!(
        names,
        [
            "hit",
            "miss",
            "stuck",
            "reached-unfinished",
            "depth-bound",
            "work-bound",
            "timeout",
            "undefined",
            "unsupported",
            "rejected",
            "baseline-incomplete",
        ]
    );
    let mut sorted = OutcomeClass::ALL;
    sorted.sort();
    assert_eq!(sorted, OutcomeClass::ALL);
    for class in OutcomeClass::ALL {
        assert_eq!(
            serde_json::to_value(class).expect("a class serializes"),
            class.name()
        );
    }
}

// ---------------------------------------------------------------- fix round (review, D16)

#[test]
fn a_no_match_that_rests_on_an_implementation_chosen_value_is_undecided() {
    // Review B1: `Set2List` of `{1, 2}` lists its items in an order the definition leaves
    // open. Whichever order the target names, one mode decides and the other does not, so
    // neither direction may give `NotMatched` (a `miss`) or `Matched`.
    for options in budgets() {
        let result = chosen().run_with(
            "listKeys(1, 1)",
            &options,
            &TargetNeeds::default(),
            &[
                "<out> L </out> requires {Set2List(List2Set(L ListItem(2))) [ 0 ]}:>Int ==Int 2",
                "<out> L </out> requires {Set2List(List2Set(L ListItem(2))) [ 0 ]}:>Int ==Int 1",
            ],
        );
        let leaf = only_leaf(&result);
        assert_eq!(leaf.unclean, [UncleanReason::UndecidedMatch]);
        assert_eq!(leaf.matches, [false, false]);
        for reached in [false, true] {
            assert_eq!(class(&result, &[reached], false), OutcomeClass::Unsupported);
        }
    }
}

#[test]
fn a_leaf_of_an_initial_configuration_defined_only_under_obligations_is_undecided() {
    // Review B2: the initial `<out>` holds `find(1 |-> 10, 2)`, a partial application whose
    // definedness the simplifier cannot decide; `get(1)` discards it. The leaf is a natural
    // end with no constraint, but the run exists only where `find(1 |-> 10, 2)` is defined.
    let fixture = taint();
    // The initial configuration in normal form: the state of a run cut at depth 0.
    let at_start = CaseOptions {
        max_depth: Some(0),
        ..CaseOptions::default()
    };
    let start = fixture.run_with("get(1)", &at_start, &TargetNeeds::default(), &[]);
    let anchor = KorePrinter::compact().print_pattern(&only_leaf(&start).state);
    let out = r"Lbl'-LT-'out'-GT-'{}(dotk{}())";
    assert_eq!(anchor.matches(out).count(), 1, "{anchor}");
    let find = r#"Lbl'-LT-'out'-GT-'{}(kseq{}(Lblfind{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("10"))), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("2"))), dotk{}()))"#;
    let initial = parse_pattern(&anchor.replace(out, find)).expect("the edited configuration");
    for options in budgets() {
        let mut executor = fixture.executor(&options);
        let shape = CaseRequestShape::new(&options, &TargetNeeds::default());
        let result = executor
            .run(&initial, &shape, &[], None)
            .expect("no solver prelude fails");
        let leaf = only_leaf(&result);
        // Without a solver the step under the obligation is `indeterminate`; with Z3 it runs and
        // the leaf is the natural-looking end the review describes. Either way the path carries
        // `undefined-initial-instances`. Whether k-rust has a solver is its own feature, which a
        // workspace build turns on even when this crate's `z3` feature is off.
        let expected = if k_rust::Z3_INFERENCE {
            HaltReasonOutput::Stuck
        } else {
            HaltReasonOutput::Indeterminate
        };
        assert_eq!(leaf.halt, expected);
        assert!(
            leaf.unclean.contains(&UncleanReason::Undecided),
            "{:?}",
            leaf.unclean
        );
        assert!(!leaf.natural_end);
        for reached in [false, true] {
            assert_eq!(class(&result, &[reached], false), OutcomeClass::Unsupported);
        }
    }
}

#[test]
fn run_facts_on_no_leaf_are_found() {
    use k_rust::backend::{BackendDiagnosticOutput, ChosenValueOutput};
    let chosen = |hook: &str| ChosenValueOutput {
        hook: hook.to_owned(),
        class: "order".to_owned(),
    };
    let mark = |hook: &str| BackendDiagnosticOutput::ImplementationChosenValue {
        hook: hook.to_owned(),
        class: "order".to_owned(),
    };
    let none: [BackendDiagnosticOutput; 0] = [];
    assert!(!run::facts_off_leaves(&[], &[], || none.iter()));
    let on_a_leaf = [mark("MAP.keys_list")];
    assert!(!run::facts_off_leaves(
        &[chosen("MAP.keys_list")],
        &[],
        || on_a_leaf.iter()
    ));
    // A vanished candidate read `SET.set2list`; no leaf carries it.
    assert!(run::facts_off_leaves(
        &[chosen("MAP.keys_list"), chosen("SET.set2list")],
        &[],
        || on_a_leaf.iter()
    ));
    assert!(run::facts_off_leaves(
        &[chosen("MAP.keys_list")],
        &[],
        || none.iter()
    ));
}

#[test]
fn run_facts_on_no_leaf_block_miss_and_stuck_only() {
    let flagged = |leaves: Vec<LeafReport>| CaseResult {
        run_facts_off_leaves: true,
        ..result(leaves)
    };
    assert_eq!(
        class(&flagged(vec![natural()]), &[false], false),
        OutcomeClass::Unsupported
    );
    assert_eq!(
        class(&flagged(vec![abnormal()]), &[false], false),
        OutcomeClass::Unsupported
    );
    // A hit on a clean, unmarked leaf is a leaf of every model on its own path.
    assert_eq!(
        class(&flagged(vec![natural()]), &[true], false),
        OutcomeClass::Hit
    );
    assert_eq!(
        class(
            &flagged(vec![halted(HaltReasonOutput::DepthBound)]),
            &[false],
            false
        ),
        OutcomeClass::DepthBound
    );
    // The flag is not a determinism break.
    assert!(flagged(vec![natural()]).determinism_breaks().is_empty());
    // Every fixture run in one path carries its facts on its leaf.
    for options in budgets() {
        let one_path = chosen().run_with("listKeys(1, 2)", &options, &TargetNeeds::default(), &[]);
        assert!(!one_path.run_facts_off_leaves);
    }
}

#[test]
fn a_cut_leaf_is_judged_and_reaches_unfinished_only_when_clean_apart_from_its_halt() {
    // Review S1: `get(2)` cut at depth 1 holds the unevaluated partial `find(1 |-> 10, 2)`.
    let options = CaseOptions {
        max_depth: Some(1),
        ..CaseOptions::default()
    };
    let result = taint().run_with("get(2)", &options, &TargetNeeds::default(), &[]);
    let cut: Vec<&LeafReport> = result
        .leaves
        .iter()
        .filter(|leaf| leaf.halt == HaltReasonOutput::DepthBound)
        .collect();
    assert_eq!(cut.len(), 1, "{result:#?}");
    assert_eq!(
        cut[0].unclean,
        [UncleanReason::Halt, UncleanReason::NotCeilFree]
    );
    let reached: Vec<bool> = result
        .leaves
        .iter()
        .map(|leaf| leaf.halt == HaltReasonOutput::DepthBound)
        .collect();
    assert_eq!(class(&result, &reached, true), OutcomeClass::Unsupported);
    // A cut leaf is not a final state: no matcher is judged on it (D16).
    let matched = imp().run_with(
        LOOP_IMP,
        &CaseOptions {
            max_depth: Some(20),
            ..CaseOptions::default()
        },
        &TargetNeeds::default(),
        &["<k> _ </k>"],
    );
    let leaf = only_leaf(&matched);
    assert_eq!(leaf.unclean, [UncleanReason::Halt]);
    assert_eq!(leaf.matches, [false]);
}

#[test]
fn a_pre_cancelled_caller_is_a_timeout_under_the_safety_limit_too() {
    // Review S2: the caller's cancellation takes effect before the watchdog thread runs.
    let fixture = imp();
    let options = CaseOptions {
        safety_limit_ms: Some(600_000),
        ..CaseOptions::default()
    };
    let mut executor = fixture.executor(&options);
    let shape = CaseRequestShape::new(&options, &TargetNeeds::default());
    let token = CancellationToken::new();
    token.cancel();
    for _ in 0..20 {
        let result = executor
            .run(&fixture.initial_of(DIV_IMP), &shape, &[], Some(&token))
            .expect("no solver prelude fails");
        let reached = vec![false; result.leaves.len()];
        assert_eq!(class(&result, &reached, false), OutcomeClass::Timeout);
        assert!(
            result
                .determinism_breaks()
                .contains(&DeterminismBreak::Clock)
        );
        assert!(!result.safety_limit_hit);
    }
}

#[test]
fn a_load_time_allowance_refusal_is_a_determinism_break() {
    // Review S3.
    let mut load = result(vec![natural()]);
    load.load_records.push(LoadRecord {
        kind: LOAD_ALLOWANCE_REFUSAL.to_owned(),
        detail: "BYTES.padRight: refused".to_owned(),
    });
    assert_eq!(
        load.determinism_breaks(),
        [DeterminismBreak::AllowanceRefusal]
    );
    assert_eq!(class(&load, &[true], false), OutcomeClass::Unsupported);
    assert_eq!(class(&load, &[false], false), OutcomeClass::Miss);
}

#[test]
fn an_undecided_natural_end_matters_only_where_the_natural_end_does() {
    // FZ-05 review N6: without run-to-completion a reaching leaf needs no natural end.
    let undecided = leaf(
        HaltReasonOutput::Stuck,
        &[UncleanReason::NaturalEndUndecided],
        false,
    );
    assert!(undecided.is_clean());
    assert!(!undecided.unclean_beyond_halt());
    let case = result(vec![undecided]);
    assert_eq!(class(&case, &[true], false), OutcomeClass::Hit);
    assert_eq!(class(&case, &[true], true), OutcomeClass::Unsupported);
    // Without a reach it is neither `miss` nor `stuck`.
    assert_eq!(class(&case, &[false], false), OutcomeClass::Unsupported);
}

// ---------------------------------------------------------------- round 3 (review 2, D21)

fn steer() -> &'static Compiled {
    support::STEER.compiled()
}

/// [`budgets`] in both path modes.
fn modes_and_budgets() -> Vec<CaseOptions> {
    let mut all = Vec::new();
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        for options in budgets() {
            all.push(CaseOptions { paths, ..options });
        }
    }
    all
}

#[test]
fn an_end_steered_by_an_unsupported_hook_is_never_clean() {
    // D21, FZ-08 review 2: `fa`'s condition `1 <<Int 33554432 >Int 0` is not computed, so the
    // equation evaluator takes `fb` and the run ends with a clean-looking `<out> 2`, where a
    // backend that computes the shift ends with 1. Only `unsupportedHooks` records it.
    for options in modes_and_budgets() {
        let result = steer().run_with(
            include_str!("../../tests/data/steer/big.pgm"),
            &options,
            &TargetNeeds::default(),
            &[],
        );
        assert!(result.failure.is_none(), "{:?}", result.failure);
        assert!(!result.leaves.is_empty());
        for leaf in &result.leaves {
            assert!(
                leaf.unclean.contains(&UncleanReason::UnsupportedHook),
                "{:?} {:?}",
                options.paths,
                leaf.unclean
            );
            assert!(!leaf.is_clean());
            assert!(!leaf.natural_end);
        }
        for reached in [false, true] {
            let reached = vec![reached; result.leaves.len()];
            for run_to_completion in [false, true] {
                assert_eq!(
                    class(&result, &reached, run_to_completion),
                    OutcomeClass::Unsupported,
                    "{:?}",
                    options.paths
                );
            }
        }
        // The value is computed: `fa` applies, a clean natural end.
        let computed = steer().run_with(
            include_str!("../../tests/data/steer/go.pgm"),
            &options,
            &TargetNeeds::default(),
            &[],
        );
        let leaf = only_leaf(&computed);
        assert!(leaf.is_clean(), "{:?}", leaf.unclean);
        assert!(leaf.natural_end);
    }
}

#[test]
fn a_vanished_candidate_s_chosen_value_flags_the_all_paths_run() {
    // Review B3 and S5, VANISH `pick(1, 2)`: `split` reads `keys_list` and vanishes beside
    // `plain`. Without a work budget under all paths the surviving leaf is clean and the flag
    // is set; with the budget the leaf carries the mark; on one path the step marks the leaf.
    let fixture = support::VANISH.compiled();
    let text = include_str!("../../tests/data/vanish/pick.pgm");
    let unbudgeted = CaseOptions {
        paths: PathMode::AllPaths,
        max_depth: Some(10_000),
        ..CaseOptions::default()
    };
    let result = fixture.run_with(text, &unbudgeted, &TargetNeeds::default(), &[]);
    let leaf = only_leaf(&result);
    assert!(leaf.is_clean(), "{:?}", leaf.unclean);
    assert!(leaf.natural_end);
    assert!(result.run_facts_off_leaves);
    assert_eq!(class(&result, &[false], false), OutcomeClass::Unsupported);
    assert_eq!(class(&result, &[true], false), OutcomeClass::Hit);

    let budgeted = CaseOptions {
        paths: PathMode::AllPaths,
        ..CaseOptions::default()
    };
    let result = fixture.run_with(text, &budgeted, &TargetNeeds::default(), &[]);
    let leaf = only_leaf(&result);
    assert!(
        leaf.unclean
            .contains(&UncleanReason::ImplementationChosenValue),
        "{:?}",
        leaf.unclean
    );
    assert!(!result.run_facts_off_leaves);
    assert_eq!(class(&result, &[false], false), OutcomeClass::Unsupported);

    for options in budgets() {
        let one_path = fixture.run_with(text, &options, &TargetNeeds::default(), &[]);
        let leaf = only_leaf(&one_path);
        assert!(
            leaf.unclean
                .contains(&UncleanReason::ImplementationChosenValue),
            "{:?}",
            leaf.unclean
        );
        assert!(!one_path.run_facts_off_leaves);
    }
}

#[test]
fn a_solver_unknown_while_matching_is_counted() {
    // Review 2, NI-2: an `unknown` depends on the clock.
    use k_rust::k_rust_backend::{search::PatternMatchError, smt::SmtError};
    let unknown = run::verdict(Ok(Err(PatternMatchError::Smt(SmtError::Unknown(
        "timeout".to_owned(),
    )))))
    .expect("not a stop");
    assert_eq!(unknown, (run::MatchVerdict::Undecided, true));
    let unavailable =
        run::verdict(Ok(Err(PatternMatchError::Smt(SmtError::Unavailable)))).expect("not a stop");
    assert_eq!(unavailable, (run::MatchVerdict::Undecided, false));
    assert_eq!(
        run::verdict(Ok(Ok(Vec::new()))).expect("not a stop"),
        (run::MatchVerdict::NotMatched, false)
    );
    // Counted with the run's unknowns, they are a determinism break.
    let mut case = result(vec![natural()]);
    case.smt_unknowns = 1;
    assert_eq!(case.determinism_breaks(), [DeterminismBreak::SmtUnknowns]);
}

#[test]
fn the_last_step_of_a_stopped_unnormalised_leaf_is_not_established() {
    // Review 2, S1.
    let leaf = |reason: &str| -> k_rust::backend::ExecutionLeaf {
        serde_json::from_value(serde_json::json!({
            "state": {},
            "depth": 2,
            "reason": reason,
            "trace": [
                {"depth": 0, "kind": "rewrite", "uniqueId": "a"},
                {"depth": 1, "kind": "simplification", "uniqueId": "s"},
                {"depth": 1, "kind": "rewrite", "uniqueId": "b"},
            ],
        }))
        .expect("an execution leaf")
    };
    for halt in ["work-bound", "timeout", "cancelled"] {
        assert_eq!(run::established_rewrites(&leaf(halt)), ["a"], "{halt}");
    }
    for halt in ["stuck", "depth-bound", "trivial", "terminal"] {
        assert_eq!(run::established_rewrites(&leaf(halt)), ["a", "b"], "{halt}");
    }
    // A work-bound run: the leaf's established rewrites are a prefix of the trace's.
    let options = CaseOptions {
        max_work: Some(20),
        ..CaseOptions::default()
    };
    let needs = TargetNeeds {
        trace: true,
        ..TargetNeeds::default()
    };
    let cut = imp().run_with(LOOP_IMP, &options, &needs, &[]);
    let leaf = only_leaf(&cut);
    assert_eq!(leaf.halt, HaltReasonOutput::WorkBound);
    let full = imp().run_with(
        LOOP_IMP,
        &CaseOptions {
            max_work: Some(21),
            ..CaseOptions::default()
        },
        &needs,
        &[],
    );
    let longer = &only_leaf(&full).rewrites;
    assert!(longer.len() > leaf.rewrites.len());
    assert_eq!(longer[..leaf.rewrites.len()], leaf.rewrites[..]);
}

#[test]
fn an_observed_run_judges_the_same_leaves_and_returns_them() {
    // FZ-10's request: one run, under the executor's limits.
    let fixture = imp();
    for options in [
        CaseOptions::default(),
        CaseOptions {
            safety_limit_ms: Some(600_000),
            ..CaseOptions::default()
        },
    ] {
        let mut executor = fixture.executor(&options);
        let shape = CaseRequestShape::new(&options, &TargetNeeds::default());
        let initial = fixture.initial_of(DIV_IMP);
        let plain = executor
            .run(&initial, &shape, &[], None)
            .expect("no solver prelude fails");
        let (observed, leaves) = executor
            .run_observed(&initial, &shape, &[], None, Some(Vec::new()))
            .expect("no solver prelude fails");
        assert_eq!(leaves.len(), observed.leaves.len());
        assert_eq!(observed.leaves.len(), plain.leaves.len());
        assert_eq!(observed.work, plain.work);
        for (judged, raw) in observed.leaves.iter().zip(&leaves) {
            assert_eq!(judged.halt, raw.reason);
        }
        assert!(
            !leaves[0].branch.is_empty(),
            "branch identities are retained"
        );
        assert_eq!(only_leaf(&observed).unclean, only_leaf(&plain).unclean);
        assert_eq!(
            only_leaf(&observed).natural_end,
            only_leaf(&plain).natural_end
        );
    }
}

#[test]
fn patterns_compiled_once_prepare_on_fresh_backends() {
    // FZ-06's request: compile once per campaign, prepare per backend.
    let fixture = imp();
    let definition = fixture.definition();
    let options = CaseOptions::default();
    let compiler = PatternCompiler::new(&definition).expect("the execution definition resolves");
    let normal_end = compiler
        .normal_end(&fixture.grammar, &options)
        .expect("the default compiles");
    let target = compiler
        .compile(
            &fixture.grammar,
            "<state> M </state> requires size(M) ==Int 3",
        )
        .expect("the target compiles");
    let shape = CaseRequestShape::new(&options, &TargetNeeds::default());
    let initial = fixture.initial_of(DIV_IMP);
    for _ in 0..2 {
        let mut executor =
            Executor::with_normal_end(fixture.source_backend(), &normal_end, &options)
                .expect("the executor builds");
        let matcher = LeafMatcher::prepare(&mut executor, &target).expect("the target prepares");
        let result = executor
            .run(&initial, &shape, &[&matcher], None)
            .expect("no solver prelude fails");
        let leaf = only_leaf(&result);
        assert!(leaf.natural_end);
        assert_eq!(leaf.matches, [true]);
        // A later surface pattern still compiles on such an executor.
        let late =
            LeafMatcher::compile_with(&mut executor, &fixture.grammar, &definition, "<k> .K </k>")
                .expect("compiles");
        let result = executor
            .run(&initial, &shape, &[&late], None)
            .expect("no solver prelude fails");
        assert_eq!(only_leaf(&result).matches, [true]);
    }
    let refused = CaseOptions {
        normal_end_pattern: Some("<nosuchcell> .K </nosuchcell>".to_owned()),
        ..CaseOptions::default()
    };
    assert!(matches!(
        compiler.normal_end(&fixture.grammar, &refused),
        Err(CampaignError::NormalEndPattern { .. })
    ));
}
