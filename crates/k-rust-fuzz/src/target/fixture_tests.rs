//! Rule and pattern targets on real runs (ARCHITECTURE 4.1, 4.2, 5.3): FZ-FIX's fixtures
//! (`tests/support`) compiled in-process, resolved through a real [`Executor`]'s rule catalog,
//! executed through `Backend::execute` and judged by [`ResolvedTarget::judge`].
//!
//! - RULES `div(A, B)`: rule `div`'s right-hand side `A /Int B` is undefined for `B = 0`.
//! - RULES `check(A)`: rule `check-hit`'s guard `A ==Int 42` fails on the anchor `check(7)`,
//!   which ends through `check-miss`.
//! - IMP `le.imp` ends with `r |-> 1` on its anchor and `r |-> 0` for `x > y`; `div.imp` with
//!   `y = 0` is a clean abnormal stop (`10 / 0` on `<k>`).

#[path = "../../tests/support/mod.rs"]
mod support;

use support::{Compiled, IMP, RULES};

use super::{Judgement, PatternAt, PatternTarget, ResolvedTarget, RuleMode, RuleRef, RuleTarget};
use crate::{
    Target, TargetKind,
    assemble::ProgramAssembly,
    error::{CampaignError, TargetProblem},
    exec::{CaseRequestShape, Executor, OutcomeClass},
    spec::{CaseOptions, CompiledDefinition},
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
        let options = CaseOptions::default();
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
        let resolved = self.resolve(target).expect("the target resolves");
        let program = self.compiled.fixture.program(file);
        assert_eq!(program.text.matches(find).count(), 1, "{find} in {file}");
        let text = program.text.replacen(find, replace, 1);
        let initial = self
            .compiled
            .assemble(program.file, &text, program.bindings)
            .unwrap_or_else(|error| panic!("{text} does not assemble: {error}"));
        let shape = CaseRequestShape::new(&self.options, &resolved.needs());
        let result = self
            .executor
            .run(&initial, &shape, &resolved.matchers(), None)
            .expect("no abort");
        resolved
            .judge(&result)
            .unwrap_or_else(|defect| panic!("{defect:?}: {result:#?}"))
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
        assert_eq!(covered.hit_leaf, None);
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
            assert_eq!(judgement.hit_leaf, Some(0));
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
            hit_leaf: Some(0),
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
    assert_eq!(
        refusal(&mut rules, "dormant"),
        CampaignError::Target(TargetProblem::NotExecutable)
    );
    assert_eq!(
        refusal(&mut rules, "nothing"),
        CampaignError::Target(TargetProblem::UnknownRule)
    );
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
    assert!(source.is_ok(), "{:?}", source.err());

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
    assert_eq!(counterexample.hit_leaf, Some(0));
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
    assert_eq!(unfinished.hit_leaf, None);
}
