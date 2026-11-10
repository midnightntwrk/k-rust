//! A test's run that matches its states under a campaign's stop (`Stop::execute_result_matching`)
//! answers whether the truncated system reaches a state a pattern matches
//! (`testdata/k/clock.k`, a free-running clock whose `frame` step comes every fourth step, so no
//! run of `clock(0, 0)` ends on its own).
//!
//! - A state reached on the way to a path's last stop, or at it, is a hit.
//! - A state only past the last stop is no state of the truncated system: the answer is `no`,
//!   although the program never ends without the stop (its run without one is cut by the depth
//!   bound, and answers `unknown`).
//! - A run that passed a stop answers `unknown`, never `no` and never a hit.
//! - A condition left undecided at an arrival loses a `no`, not a hit; a refused one makes every
//!   answer `unknown`; one that always holds answers as the stop without it.
//! - A `no` needs every count of undecided solver answers to be 0, and the request's proof
//!   agreement: without it each state was refuted in execution mode alone. The clock's targets
//!   evaluate nothing (no constraint, free constructors and integers), so agreement changes no
//!   hit.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::num::NonZeroU64;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions, PassedStopOutput};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_campaign::{MatchAnswer, MatchUnknown, Stop, StopOracle, StopWhen, judge_matches};
use kink_native::NativeValidator;
use kink_native::exclusion::DefinitionExclusions;
use kink_native::execution::{
    DefinitionTables, ExecutionAdapter, ExecutionBudget, HaltClass, ResultRun, SolverProfile,
    StateMatchRequest, StopArrival, StopCondition, StopDecision, StopRules,
};

/// The clock's backend and its definition exclusions, loaded as a campaign loads a side.
struct Clock {
    backend: Backend,
    tables: DefinitionTables,
    exclusions: DefinitionExclusions,
}

impl Clock {
    fn load() -> Self {
        let side = NativeValidator::bind(
            support::load_path(&Path::new(support::DIR).join("clock.k"), "CLOCK"),
            CompileOptions::default(),
        )
        .compile_baseline()
        .expect("the clock compiles");
        let kore = parse_definition(&side.artifacts().definition_kore).expect("KORE");
        let mut backend =
            Backend::from_definition(kore.clone(), "CLOCK", BackendOptions::default())
                .expect("the clock loads");
        let selected = backend.select_definition(None).expect("its module");
        let exclusions = DefinitionExclusions::of(
            &kore,
            &selected,
            &side.compile_options().builtin_source_prefixes,
        );
        assert_eq!(exclusions.definition_exclusion(), None);
        Self {
            backend,
            tables: DefinitionTables::new(),
            exclusions,
        }
    }

    /// The answer of the run of `clock(n, phase)` under `stop`, matching `target`.
    fn answer(&mut self, stop: Stop, start: (i64, i64), target: &Pattern) -> MatchAnswer {
        self.matching(stop, start, target).answer
    }

    fn matching(
        &mut self,
        stop: Stop,
        start: (i64, i64),
        target: &Pattern,
    ) -> kink_campaign::StoppedMatch {
        self.matching_agreed(stop, start, target, true)
    }

    /// The run of `clock(n, phase)` under `stop`, matching `target` with proof agreement when
    /// `proof_agreement`.
    fn matching_agreed(
        &mut self,
        stop: Stop,
        (n, phase): (i64, i64),
        target: &Pattern,
        proof_agreement: bool,
    ) -> kink_campaign::StoppedMatch {
        stop.execute_result_matching(
            &ExecutionAdapter::with_profile(SolverProfile::BUILD),
            &mut self.backend,
            &mut self.tables,
            "clock",
            &clock(n, phase),
            BUDGET,
            ResultRun::default(),
            &StateMatchRequest {
                pattern: target.clone(),
                proof_agreement,
                chain: None,
            },
            &self.exclusions,
        )
        .expect("the run is made")
    }
}

/// The configuration `<k> clock(n, phase) </k>`.
fn clock(n: i64, phase: i64) -> Pattern {
    support::initial_state(
        support::app("Lblclock", vec![support::int(n), support::int(phase)]),
        "SortClock",
    )
}

/// Each path's depth bound, which cuts the run without a stop; a clock that fires only on a test
/// that fails anyway.
const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(600),
    max_simplification_iterations: 10_000,
    max_depth: Some(64),
    max_breadth: None,
};

const FRAME: &str = "CLOCK.frame";

/// The stop after (`after`) or before the `count`th frame.
fn frame(after: bool, count: u64) -> Stop {
    let rules = vec![FRAME.to_owned()];
    let rules = if after {
        StopRules {
            before: Vec::new(),
            after: rules,
        }
    } else {
        StopRules {
            before: rules,
            after: Vec::new(),
        }
    };
    Stop::new(rules, NonZeroU64::new(count).unwrap()).unwrap()
}

/// A stop condition that answers `decide` at every arrival.
struct Always {
    cells: Vec<Vec<String>>,
    decide: fn() -> StopDecision,
}

impl StopOracle for Always {
    fn cells(&self) -> &[Vec<String>] {
        &self.cells
    }

    fn with_condition(&self, body: &mut dyn FnMut(&mut dyn StopCondition)) -> Result<(), String> {
        let decide = self.decide;
        let mut condition = move |_: &StopArrival<'_>| decide();
        body(&mut condition);
        Ok(())
    }
}

fn when(stop: Stop, name: &str, decide: fn() -> StopDecision) -> Stop {
    stop.with_when(StopWhen::new(
        serde_json::json!({ "condition": name }),
        Arc::new(Always {
            cells: Vec::new(),
            decide,
        }),
    ))
}

fn hit_at(answer: &MatchAnswer) -> Option<(u64, Pattern)> {
    match answer {
        MatchAnswer::Hit(reach) => Some((reach.depth, reach.state.clone())),
        _ => None,
    }
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// After the first frame the clock is at `clock(4, 0)`, depth 4; before it at `clock(3, 3)`,
/// depth 3. Each state on the way, and the stop's own state, is a hit.
#[test]
fn a_state_reached_before_the_stop_is_a_hit() {
    on_a_big_stack(|| {
        let mut clock_run = Clock::load();
        for (stop, target, depth) in [
            (frame(true, 1), clock(2, 2), 2),
            (frame(true, 1), clock(4, 0), 4),
            (frame(false, 1), clock(3, 3), 3),
            (frame(true, 2), clock(5, 1), 5),
        ] {
            assert_eq!(
                hit_at(&clock_run.answer(stop, (0, 0), &target)),
                Some((depth, target.clone())),
                "{stop:?} {target:?}"
            );
            assert_eq!(
                hit_at(
                    &clock_run
                        .matching_agreed(stop, (0, 0), &target, false)
                        .answer
                ),
                Some((depth, target.clone())),
                "{stop:?} {target:?} without agreement"
            );
        }
    });
}

/// A state only past the last stop answers `no`: the truncated system's every path ends at its
/// stop, and the matcher refuted every state it reached. Without the stop the program never
/// ends, so its run is cut by the depth bound and the same question is `unknown`.
#[test]
fn a_state_only_past_the_stop_is_no_in_a_program_that_never_ends_without_it() {
    on_a_big_stack(|| {
        let mut clock_run = Clock::load();
        for (stop, target) in [
            (frame(true, 1), clock(5, 1)),
            (frame(true, 1), clock(100, 0)),
            // The cut-point step's proposed successor is no state of the truncated system.
            (frame(false, 1), clock(4, 0)),
            (frame(true, 2), clock(9, 1)),
        ] {
            let matched = clock_run.matching(stop, (0, 0), &target);
            assert_eq!(matched.answer, MatchAnswer::No, "{stop:?} {target:?}");
            assert_eq!(
                clock_run
                    .matching_agreed(stop, (0, 0), &target, false)
                    .answer,
                MatchAnswer::Unknown(MatchUnknown::ExecutionModeRefutation),
                "{stop:?} {target:?} without agreement"
            );
            let execution = matched.execution.expect("the run has a result");
            assert_eq!(execution.undecided_answers(), 0);
            // The no needs every count of undecided answers at 0: one undecided answer of the
            // leaves' feasibility questions makes it unknown.
            assert_eq!(
                judge_matches(
                    &execution.clone().with_decider_smt_unknowns(1),
                    &clock_run.exclusions,
                    None
                ),
                MatchAnswer::Unknown(MatchUnknown::UndecidedAnswers {
                    run: 0,
                    feasibility: 1,
                    matcher: 0,
                })
            );
        }
        assert_eq!(
            clock_run.answer(Stop::NONE, (0, 0), &clock(100, 0)),
            MatchAnswer::Unknown(MatchUnknown::Incomplete {
                halt: HaltClass::DepthBound,
                leaves: 1,
            })
        );
        assert_eq!(
            hit_at(&clock_run.answer(Stop::NONE, (0, 0), &clock(5, 1))),
            Some((5, clock(5, 1)))
        );
    });
}

/// From `clock(-1, 3)` both `frame` and `warp` apply: the first frame is a step of the stop rule
/// with another successor, so the run goes on past it through both. Its states on that branch
/// need not be states of the truncated system, so neither a match there (`clock(0, 0)`, frame's
/// successor) nor the lack of one (`clock(1000, 0)`) is an answer.
#[test]
fn a_passed_stop_makes_the_answer_unknown() {
    on_a_big_stack(|| {
        let mut clock_run = Clock::load();
        for target in [clock(0, 0), clock(1000, 0)] {
            assert_eq!(
                clock_run.answer(frame(true, 1), (-1, 3), &target),
                MatchAnswer::Unknown(MatchUnknown::PassedStop(vec![PassedStopOutput {
                    rule: FRAME.to_owned(),
                    depth: 0,
                }])),
                "{target:?}"
            );
        }
    });
}

/// A condition left undecided at the first frame's arrival ends the path there,
/// `stop-undecided`: the state is reached either way, so a hit before it stands, and the path is
/// no end of the truncated system, so a `no` is lost. A refused condition leaves the stop
/// undefined on the run. A condition that always holds answers as the stop without one.
#[test]
fn a_stop_condition_answers_as_its_arrivals_were_decided() {
    on_a_big_stack(|| {
        let mut clock_run = Clock::load();
        let undecided = when(frame(true, 1), "undecided", || {
            StopDecision::Undecided("a test's budget".to_owned())
        });
        let refused = when(frame(true, 1), "refused", || {
            StopDecision::Refused("a test's refusal".to_owned())
        });
        let holds = when(frame(true, 1), "holds", || StopDecision::Holds);
        assert_eq!(
            hit_at(&clock_run.answer(undecided, (0, 0), &clock(2, 2))),
            Some((2, clock(2, 2)))
        );
        match clock_run.answer(undecided, (0, 0), &clock(5, 1)) {
            MatchAnswer::Unknown(MatchUnknown::StopConditionUndecided(Some(reason))) => {
                assert!(reason.contains("a test's budget"), "{reason}");
            }
            other => panic!("{other:?}"),
        }
        for target in [clock(2, 2), clock(5, 1)] {
            match clock_run.matching(refused, (0, 0), &target) {
                kink_campaign::StoppedMatch {
                    answer: MatchAnswer::Unknown(MatchUnknown::StopConditionRefused(reason)),
                    execution: None,
                } => assert!(reason.contains("a test's refusal"), "{reason}"),
                other => panic!("{other:?}"),
            }
            assert_eq!(
                clock_run.answer(holds, (0, 0), &target),
                clock_run.answer(frame(true, 1), (0, 0), &target),
                "{target:?}"
            );
        }
    });
}
