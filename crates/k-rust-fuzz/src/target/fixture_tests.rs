//! Rule and pattern targets on real runs (ARCHITECTURE 4.1, 4.2, 5.3): FZ-FIX's fixtures
//! (`tests/support`) compiled in-process, resolved through a real [`Executor`]'s rule catalog,
//! executed through `Backend::execute` and judged by [`ResolvedTarget::judge`].
//!
//! - RULES `div(A, B)`: rule `div`'s right-hand side `A /Int B` is undefined for `B = 0`.
//! - RULES `check(A)`: rule `check-hit`'s guard `A ==Int 42` fails on the anchor `check(7)`,
//!   which ends through `check-miss`.
//! - IMP `le.imp` ends with `r |-> 1` on its anchor and `r |-> 0` for `x > y`; `div.imp` with
//!   `y = 0` is a clean abnormal stop (`10 / 0` on `<k>`).
//! - COIN `flip(3)` under all paths: one step with two candidates, `heads` (ending with
//!   `<out> 3 </out>`) and `tails` (`<out> 4 </out>`), so the backend applies no stop rule there.

#[path = "../../tests/support/mod.rs"]
mod support;

use k_rust::kore::printer::Printer;
use support::{COIN, Compiled, IMP, RULES};

use super::{
    HitSite, Judgement, PatternAt, PatternTarget, Resolved, ResolvedTarget, RuleMode, RuleRef,
    RuleTarget,
};
use crate::{
    Target, TargetKind,
    assemble::ProgramAssembly,
    error::{CampaignError, TargetProblem},
    exec::{CaseRequestShape, CaseResult, Executor, OutcomeClass},
    spec::{CaseOptions, CompiledDefinition, PathMode},
};

/// A target with its definition, assembly and executor, as a campaign builds them.
struct Harness {
    compiled: &'static Compiled,
    definition: CompiledDefinition,
    assembly: ProgramAssembly,
    executor: Executor,
    options: CaseOptions,
}

impl Harness {
    fn new(compiled: &'static Compiled) -> Self {
        Self::on(compiled, compiled.definition())
    }

    fn on(compiled: &'static Compiled, definition: CompiledDefinition) -> Self {
        Self::with(compiled, definition, CaseOptions::default())
    }

    /// Every path, with `normal_end_pattern` when given.
    fn all_paths(compiled: &'static Compiled, normal_end_pattern: Option<&str>) -> Self {
        let options = CaseOptions {
            paths: PathMode::AllPaths,
            normal_end_pattern: normal_end_pattern.map(str::to_owned),
            ..CaseOptions::default()
        };
        Self::with(compiled, compiled.definition(), options)
    }

    fn with(
        compiled: &'static Compiled,
        definition: CompiledDefinition,
        options: CaseOptions,
    ) -> Self {
        let assembly = ProgramAssembly::new(&definition).expect("the definition assembles");
        let executor =
            Executor::new(&definition, &assembly, &options).expect("the executor builds");
        Self {
            compiled,
            definition,
            assembly,
            executor,
            options,
        }
    }

    fn resolve(&mut self, target: &Target) -> Result<ResolvedTarget, CampaignError> {
        ResolvedTarget::resolve(target, &mut self.executor, &self.definition, &self.assembly)
    }

    /// Run the program `file` with `find` replaced by `replace` (once) and judge it.
    fn judge(&mut self, target: &Target, file: &str, find: &str, replace: &str) -> Judgement {
        self.run(target, file, find, replace).0
    }

    /// [`Self::judge`], with the case's result.
    fn run(
        &mut self,
        target: &Target,
        file: &str,
        find: &str,
        replace: &str,
    ) -> (Judgement, CaseResult) {
        let resolved = self.resolve(target).expect("the target resolves");
        let program = self.compiled.fixture.program(file);
        assert_eq!(program.text.matches(find).count(), 1, "{find} in {file}");
        let text = program.text.replacen(find, replace, 1);
        let initial = self
            .compiled
            .assemble(program.file, &text, program.bindings)
            .unwrap_or_else(|error| panic!("{text} does not assemble: {error}"));
        let shape = CaseRequestShape::new(&self.options, &resolved.needs(self.options.paths));
        let result = self
            .executor
            .run(&initial, &shape, &resolved.matchers(), None)
            .expect("no abort");
        let judgement = resolved
            .judge(&result)
            .unwrap_or_else(|defect| panic!("{defect:?}: {result:#?}"));
        (judgement, result)
    }
}

fn rule(label: &str, mode: RuleMode, run_to_completion: bool) -> Target {
    Target {
        kind: TargetKind::Rule(RuleTarget {
            rule: RuleRef::Label(label.to_owned()),
            mode,
        }),
        run_to_completion,
        negated_property: false,
    }
}

fn pattern(pattern: &str, run_to_completion: bool) -> Target {
    Target {
        kind: TargetKind::Pattern(PatternTarget {
            pattern: pattern.to_owned(),
            at: PatternAt::Final,
        }),
        run_to_completion,
        negated_property: false,
    }
}

fn class(judgement: &Judgement) -> OutcomeClass {
    judgement.class
}

#[test]
fn fired_and_covered_differ_on_the_undefined_right_hand_side() {
    let mut rules = Harness::new(RULES.compiled());
    let undefined = |rules: &mut Harness, mode, run_to_completion| {
        rules.judge(
            &rule("div", mode, run_to_completion),
            "rules/div.pgm",
            "2)",
            "0)",
        )
    };
    for run_to_completion in [false, true] {
        // The undefined step is on no leaf's path: the rule did not fire.
        let fired = undefined(&mut rules, RuleMode::Fired, run_to_completion);
        assert_eq!(class(&fired), OutcomeClass::Undefined, "{fired:?}");
        // Coverage `applied` holds the rule, but the only leaf is an undefined step, which
        // cannot carry a hit: `unsupported` (a reaching leaf that is not clean), and under
        // run-to-completion `reached-unfinished`, since the leaf is clean in every respect
        // except its halt and that halt is an undefined step (ARCHITECTURE 5.3, step 2).
        let covered = undefined(&mut rules, RuleMode::Covered, run_to_completion);
        let expected = if run_to_completion {
            OutcomeClass::ReachedUnfinished
        } else {
            OutcomeClass::Unsupported
        };
        assert_eq!(class(&covered), expected, "{covered:?}");
        assert_eq!(covered.hit_site, None);
    }
    // On the anchor `div(10, 2)` the rule fires: a terminal halt on it as the only stop rule,
    // or its `Rewrite` entry on the trace of the natural end.
    for run_to_completion in [false, true] {
        for mode in [RuleMode::Fired, RuleMode::Covered] {
            let judgement = rules.judge(
                &rule("RULES.div", mode, run_to_completion),
                "rules/div.pgm",
                "2)",
                "2)",
            );
            assert_eq!(
                class(&judgement),
                OutcomeClass::Hit,
                "{mode:?} {judgement:?}"
            );
            assert_eq!(judgement.hit_site, Some(HitSite::Leaf(0)));
        }
    }
}

#[test]
fn condition_reached_holds_on_a_failing_guard() {
    let mut rules = Harness::new(RULES.compiled());
    let reached = rules.judge(
        &rule("check-hit", RuleMode::ConditionReached, true),
        "rules/check.pgm",
        "7",
        "7",
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
        for run_to_completion in [false, true] {
            let judgement = rules.judge(
                &rule("check-hit", mode, run_to_completion),
                "rules/check.pgm",
                "7",
                "7",
            );
            assert_eq!(
                class(&judgement),
                OutcomeClass::Miss,
                "{mode:?} {judgement:?}"
            );
            assert!(judgement.blocked, "{mode:?}");
        }
    }
    // The guard holds for 42.
    for mode in [
        RuleMode::Fired,
        RuleMode::Covered,
        RuleMode::ConditionReached,
    ] {
        let judgement = rules.judge(
            &rule("check-hit", mode, false),
            "rules/check.pgm",
            "7",
            "42",
        );
        assert_eq!(
            class(&judgement),
            OutcomeClass::Hit,
            "{mode:?} {judgement:?}"
        );
        assert!(!judgement.blocked, "{mode:?}");
    }
}

#[test]
fn the_real_catalog_refuses_shared_non_executable_and_equation_entries() {
    let mut rules = Harness::new(RULES.compiled());
    let refusal = |rules: &mut Harness, label: &str| {
        rules
            .resolve(&rule(label, RuleMode::Fired, false))
            .err()
            .unwrap_or_else(|| panic!("{label} resolves"))
    };
    assert_eq!(
        refusal(&mut rules, "twin-a"),
        CampaignError::Target(TargetProblem::SharedIdentity)
    );
    assert_eq!(
        refusal(&mut rules, "double"),
        CampaignError::Target(TargetProblem::Equation)
    );
    // A non-executable equation: the equation refusal comes first.
    assert_eq!(
        refusal(&mut rules, "dormant"),
        CampaignError::Target(TargetProblem::Equation)
    );
    assert_eq!(
        refusal(&mut rules, "nothing"),
        CampaignError::Target(TargetProblem::UnknownRule)
    );
    let by_label = rules
        .resolve(&rule("check-hit", RuleMode::Fired, false))
        .expect("check-hit resolves");
    let source = rules.resolve(&Target {
        kind: TargetKind::Rule(RuleTarget {
            rule: RuleRef::Source {
                source: "rules.k".to_owned(),
                line: source_line(RULES.compiled(), "rule [check-hit]:"),
            },
            mode: RuleMode::Fired,
        }),
        run_to_completion: false,
        negated_property: false,
    });
    let source = source.expect("the source position resolves");
    assert!(
        matches!(&by_label.resolved, Resolved::Rule { .. }),
        "{:?}",
        by_label.resolved
    );
    // The same id as the label's, not merely some rule.
    assert_eq!(source.resolved, by_label.resolved);

    // A rewrite rule marked non-executable in caller KORE (kink's route).
    let compiled = RULES.compiled();
    let mut frozen = Harness::on(
        compiled,
        compiled.definition_with_non_executable("check-hit"),
    );
    assert_eq!(
        refusal(&mut frozen, "check-hit"),
        CampaignError::Target(TargetProblem::NotExecutable)
    );
}

/// The one-based line of `compiled`'s source on which `text` starts.
fn source_line(compiled: &Compiled, text: &str) -> u32 {
    let index = compiled
        .fixture
        .source
        .lines()
        .position(|line| line.trim_start().starts_with(text))
        .unwrap_or_else(|| panic!("{text} in {}", compiled.fixture.file));
    u32::try_from(index + 1).expect("a small file")
}

#[test]
fn a_pattern_at_final_is_hit_by_a_matching_clean_end() {
    let mut imp = Harness::new(IMP.compiled());
    let ends_zero = r#"<state> #token("r", "Id") |-> 0 _ </state>"#;
    let counterexample = imp.judge(&pattern(ends_zero, true), "imp/le.imp", "x = 3;", "x = 7;");
    assert_eq!(
        class(&counterexample),
        OutcomeClass::Hit,
        "{counterexample:?}"
    );
    assert_eq!(counterexample.hit_site, Some(HitSite::Leaf(0)));
    let anchor = imp.judge(&pattern(ends_zero, true), "imp/le.imp", "x = 3;", "x = 3;");
    assert_eq!(class(&anchor), OutcomeClass::Miss, "{anchor:?}");

    // `y = 0` leaves `10 / 0` on `<k>`: a clean abnormal stop. It is a clean end, so a pattern
    // matching it is reached; under run-to-completion it is not a natural end, so the case is
    // reached-unfinished (ARCHITECTURE 5.3, step 2).
    let stopped = "<state> M </state> requires size(M) ==Int 3";
    let end = imp.judge(&pattern(stopped, false), "imp/div.imp", "y = 2;", "y = 0;");
    assert_eq!(class(&end), OutcomeClass::Hit, "{end:?}");
    let unfinished = imp.judge(&pattern(stopped, true), "imp/div.imp", "y = 2;", "y = 0;");
    assert_eq!(
        class(&unfinished),
        OutcomeClass::ReachedUnfinished,
        "{unfinished:?}"
    );
    assert_eq!(unfinished.hit_site, None);
}

/// The index of the leaf of `result` whose `<out>` cell holds `value`.
fn leaf_with_out(result: &CaseResult, value: i64) -> usize {
    let cell = format!("Lbl'-LT-'out'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"{value}\"))");
    let printed: Vec<String> = result
        .leaves
        .iter()
        .map(|leaf| Printer::compact().print_pattern(&leaf.state))
        .collect();
    let found: Vec<usize> = (0..printed.len())
        .filter(|index| printed[*index].contains(&cell))
        .collect();
    let [index] = found.as_slice() else {
        panic!("one leaf with {cell}: {printed:#?}");
    };
    *index
}

#[test]
fn fired_at_a_branching_step_under_all_paths_is_a_hit_on_the_firing_leaf() {
    let mut coin = Harness::all_paths(COIN.compiled(), None);
    for (label, out) in [("heads", 3), ("tails", 4)] {
        for run_to_completion in [false, true] {
            let (judgement, result) = coin.run(
                &rule(label, RuleMode::Fired, run_to_completion),
                "coin/flip.pgm",
                "3",
                "3",
            );
            assert_eq!(result.leaves.len(), 2, "{result:#?}");
            assert_eq!(
                class(&judgement),
                OutcomeClass::Hit,
                "{label} {judgement:?}"
            );
            assert_eq!(
                judgement.hit_site,
                Some(HitSite::Leaf(leaf_with_out(&result, out))),
                "{label}"
            );
        }
    }
}

#[test]
fn a_coverage_hit_over_several_clean_leaves_is_the_runs() {
    let mut coin = Harness::all_paths(COIN.compiled(), None);
    for mode in [RuleMode::Covered, RuleMode::ConditionReached] {
        for label in ["heads", "tails"] {
            for run_to_completion in [false, true] {
                let judgement = coin.judge(
                    &rule(label, mode, run_to_completion),
                    "coin/flip.pgm",
                    "3",
                    "3",
                );
                assert_eq!(
                    judgement,
                    Judgement {
                        class: OutcomeClass::Hit,
                        hit_site: Some(HitSite::Run),
                        blocked: false,
                    },
                    "{mode:?} {label}"
                );
            }
        }
    }
}

#[test]
fn a_coverage_reach_over_several_leaves_is_no_hit_unless_every_leaf_qualifies() {
    // Only the `heads` end (`<out> 3 </out>`) is a natural end; the `tails` end is a clean
    // abnormal stop. Coverage holds both rules but names neither leaf.
    let mut coin = Harness::all_paths(COIN.compiled(), Some("<k> .K </k> <out> 3 </out>"));
    for label in ["heads", "tails"] {
        // Under run-to-completion the `tails` end does not qualify, so the reach is attributed
        // to it alone: reached but not finished.
        let unfinished = coin.judge(
            &rule(label, RuleMode::Covered, true),
            "coin/flip.pgm",
            "3",
            "3",
        );
        assert_eq!(
            class(&unfinished),
            OutcomeClass::ReachedUnfinished,
            "{label} {unfinished:?}"
        );
        assert_eq!(unfinished.hit_site, None);
        // Without run-to-completion both leaves are clean ends: the run's hit.
        let hit = coin.judge(
            &rule(label, RuleMode::Covered, false),
            "coin/flip.pgm",
            "3",
            "3",
        );
        assert_eq!(class(&hit), OutcomeClass::Hit, "{label}");
        assert_eq!(hit.hit_site, Some(HitSite::Run));
    }
    // `fired` names the leaf: `heads` ends naturally, `tails` does not.
    let heads = coin.judge(
        &rule("heads", RuleMode::Fired, true),
        "coin/flip.pgm",
        "3",
        "3",
    );
    assert_eq!(class(&heads), OutcomeClass::Hit, "{heads:?}");
    let tails = coin.judge(
        &rule("tails", RuleMode::Fired, true),
        "coin/flip.pgm",
        "3",
        "3",
    );
    assert_eq!(class(&tails), OutcomeClass::ReachedUnfinished, "{tails:?}");
}

#[test]
fn a_pattern_match_cut_by_a_bound_keeps_the_bound_class() {
    // `div.imp` cut once its declarations ran: the cut state already holds x, y and q, as the
    // pattern asks, but it is not a final state.
    let declared = "<state> M </state> requires size(M) ==Int 3";
    let mut cut_matches = 0;
    for depth in 1..=12 {
        let mut imp = Harness::with(
            IMP.compiled(),
            IMP.compiled().definition(),
            CaseOptions {
                max_depth: Some(depth),
                ..CaseOptions::default()
            },
        );
        for run_to_completion in [false, true] {
            let (judgement, result) = imp.run(
                &pattern(declared, run_to_completion),
                "imp/div.imp",
                "y = 2;",
                "y = 2;",
            );
            let [leaf] = result.leaves.as_slice() else {
                panic!("one path: {result:#?}");
            };
            // The cut state holds the three declared variables, so the pattern would match it
            // were it an end.
            let entries = Printer::compact()
                .print_pattern(&leaf.state)
                .matches("Lbl'UndsPipe'-'-GT-Unds'")
                .count();
            if leaf.halt == k_rust::backend::HaltReasonOutput::DepthBound && entries == 3 {
                cut_matches += 1;
                assert_eq!(
                    class(&judgement),
                    OutcomeClass::DepthBound,
                    "depth {depth}, run-to-completion {run_to_completion}"
                );
                assert_eq!(judgement.hit_site, None);
            }
        }
    }
    assert!(cut_matches > 0, "no depth cut a matching state");
}
