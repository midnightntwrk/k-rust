//! Whether a test's run reaches a state a pattern matches, in the system a campaign's stop
//! states ([`Stop::execute_result_matching`], [`judge_matches`]).
//!
//! The question is existential: does some path of the test's system, from its initial state,
//! reach a configuration the pattern matches? With a stop ([`Stop`]) the system is the truncated
//! one, whose every path ends at its `N`th stop event or at its own end, whichever comes first.
//! A state past a path's last stop event is no state of that system, so a match there is no
//! answer; and an exploration that reached every end of the truncated system without a match is
//! a complete answer, also for a program whose untruncated run never ends.
//!
//! The run is the request a campaign makes for the test ([`Stop::execute_result`]: the stop's
//! rules, the test's count and the stop's condition, in one request), which also matches every
//! state it reaches against the pattern (kink-native `ExecutionAdapter::execute_result_probed`
//! with a match request; k-rust `match_states`). k-rust merges a state of a counted run only into
//! one whose path passed as many arrivals (and, under a condition, as many events), so the states
//! the run matches are the states of the truncated system its paths reached.
//!
//! The answer ([`MatchAnswer`]) is one of three:
//! - `Hit`: some reached state is matched, decided, shown to exist and reached on a path whose
//!   existence rests on nothing undecided. A value the definition leaves open on that path
//!   (`implementation-chosen-value`) does not refuse it: the value k-rust chose is one model of
//!   the definition, and the claim is existential.
//! - `No`: in every model of the definition, no state of the truncated system matches. The
//!   matcher refuted every state the run reached in execution mode and in proof mode, and the
//!   run is a complete and decided exploration of the truncated system: every leaf an end of it
//!   and free of diagnostics, no stop passed, no exclusion of the run, no stack stop of the run
//!   or of the matcher, and no undecided solver answer in the run's decisions, the matcher's or
//!   the adapter's questions about the leaves' feasibility.
//! - `Unknown`, with its cause ([`MatchUnknown`]) otherwise.
//!
//! A `No` needs both modes because matching is isolated from the run: a value the definition
//! leaves open that the matcher reads in execution mode is recorded nowhere, so a refutation in
//! that mode alone holds of k-rust's choice of the value, and in another model the state may
//! match. In proof mode such a value stays unevaluated, so a refutation there rests on no
//! choice of it. The request asks for both with `proof_agreement`; without it every answer that would be
//! a `No` is unknown ([`MatchUnknown::ExecutionModeRefutation`]). A target with no constraint
//! whose every application has a free-constructor head evaluates nothing, so both modes give it
//! the same verdict and agreement costs it only the second match; whether a target is one is a
//! fact of the definition's symbols, which the run's result does not carry, so the answer reads
//! only the request's flag. Agreement costs a hit only where the two modes disagree: such a
//! state is undecided rather than reached.
//!
//! A leaf that carries a diagnostic need not be an end of the truncated system even when it is
//! stuck: a rule whose condition was left unsimplified, failed to simplify or exhausted the
//! simplification budget may have been left unapplied, and an undecided condition or predicate
//! leaves the step or the state open. A leaf's diagnostics hold those of its whole path, so a
//! `No` needs every leaf free of them ([`kink_native::bridge::diagnosed`]), as a campaign keeps
//! a diagnosed leaf's run incomplete.
//!
//! Some causes make every answer unknown, a hit included:
//! - the clock: a run the watchdog cancelled has no states to read;
//! - a stop condition that refused or could not be asked: the stop is not defined on this run;
//! - a passed stop, a step of a stop rule that had another successor: the run went on through
//!   every successor where the truncated system would end the path, so the states it reached on
//!   that branch need not be states of the truncated system.
//!
//! A path the condition left undecided (`stop-undecided`) ends at a state the truncated system
//! reaches either way: before the step at a cut-point rule, after it at a terminal rule. A reach
//! found on any path therefore stands, and only a `No` is lost.
//!
//! Each answer here is a fact of the run. A caller that answers for a program also judges what
//! the run cannot show: the facts of the definition's data and of the program's initial state,
//! and for a `No` that the program's baseline run is complete.

use k_rust::backend::{Backend, BackendDiagnosticOutput, PassedStopOutput};
use k_rust::kore::ast::Pattern;
use kink_native::bridge::diagnosed;
use kink_native::exclusion::{DefinitionExclusions, Exclusion, allowance_refusal};
use kink_native::execution::{
    AdaptedExecution, DefinitionTables, ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget,
    HaltClass, MatchedState, ResultRun, StateMatchRequest, UndecidedMatchReasonOutput,
};

use crate::runner::Stop;

/// The answer of one run that matched its states ([`judge_matches`]).
#[derive(Clone, Debug, PartialEq)]
pub enum MatchAnswer {
    /// A state the run reached matches: the reach k-rust reported, with its depth, its state and
    /// the diagnostics of its path up to it (none, or only `implementation-chosen-value`).
    Hit(MatchedState),
    /// In every model of the definition, no state of the truncated system matches.
    No,
    /// Neither is shown.
    Unknown(MatchUnknown),
}

/// Why a run's answer is [`MatchAnswer::Unknown`]: the first missing premise, in the order
/// [`judge_matches`] reads them.
#[derive(Clone, Debug, PartialEq)]
pub enum MatchUnknown {
    /// The watchdog fired before the run ended, so its states are not read.
    Clock,
    /// The stop's condition refused at an arrival, or could not be given to the run: the stop is
    /// not defined on this run, so neither is its system.
    StopConditionRefused(String),
    /// The run went on past a step of a stop rule that had another successor (k-rust
    /// `passedStops`): on that branch its states need not be states of the truncated system.
    PassedStop(Vec<PassedStopOutput>),
    /// The first reach rests on its path's diagnostics up to it, which carry more than values the
    /// definition leaves open: the path may not exist.
    DirtyReach(MatchedState),
    /// Every reach's term holds a term-level `\and`, which is no configuration of the
    /// definition's own making.
    TermConjunction(MatchedState),
    /// The run left an application unevaluated, as an unsupported hook or a `Bytes` result the
    /// memory allowance refused: where it is undefined, the state holding it denotes no
    /// configuration, which k-rust did not compute.
    UnevaluatedHook,
    /// The matcher left the verdict of some reached state undecided, for each reason the first
    /// count k-rust reported.
    UndecidedMatch(Vec<(UndecidedMatchReasonOutput, u64)>),
    /// A path ended at an arrival at a stop where the condition was left undecided
    /// (`stop-undecided`), with the reason of the last such arrival when one was recorded: the
    /// path is no end of the truncated system.
    StopConditionUndecided(Option<String>),
    /// A path ended where the truncated system does not end it (a bound, an indeterminate step,
    /// a simplification error, an unsupported hook leaf), with the first such leaf's halt and
    /// how many there were.
    Incomplete { halt: HaltClass, leaves: usize },
    /// The run is excluded ([`DefinitionExclusions::run_exclusion`]).
    Exclusion(Exclusion),
    /// A leaf carries a diagnostic on its step, a candidate or its remainder
    /// ([`kink_native::bridge::diagnosed`]), which its path's diagnostics include: a rule may
    /// have been left unapplied or a condition left open there, so the leaf need not be an end of
    /// the truncated system. The first such leaf's halt and how many there were.
    DiagnosedLeaf { halt: HaltClass, leaves: usize },
    /// The matcher stopped for lack of native stack, which leaves its match undecided and puts
    /// the summary outside k-rust's determinism contract.
    MatcherStackStop(usize),
    /// Some decision the exploration rests on may rest on an undecided solver answer: the run's
    /// own (`run`), the adapter's about the leaves' feasibility (`feasibility`), the matcher's
    /// (`matcher`).
    UndecidedAnswers {
        run: usize,
        feasibility: usize,
        matcher: usize,
    },
    /// The run did not match its states (it was made without a match request).
    Unmatched,
    /// Every premise of a `No` holds but one: the request did not ask for proof agreement
    /// (`StateMatchRequest::proof_agreement`), so each state was refuted in execution mode
    /// alone, where the matcher may have read a value the definition leaves open without the run
    /// recording it (module documentation).
    ExecutionModeRefutation,
}

impl MatchUnknown {
    /// A short name of the cause.
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            Self::Clock => "clock",
            Self::StopConditionRefused(_) | Self::StopConditionUndecided(_) => "stop-condition",
            Self::PassedStop(_) => "passed-stop",
            Self::DirtyReach(_) => "dirty-reach",
            Self::TermConjunction(_) => "term-conjunction",
            Self::UnevaluatedHook => "unevaluated-hook",
            Self::UndecidedMatch(_) => "undecided-match",
            Self::Incomplete { .. } => "incomplete",
            Self::Exclusion(exclusion) => exclusion.name(),
            Self::DiagnosedLeaf { .. } => "diagnosed-leaf",
            Self::MatcherStackStop(_) => "matcher-stack-stop",
            Self::UndecidedAnswers { .. } => "undecided-answers",
            Self::Unmatched => "unmatched",
            Self::ExecutionModeRefutation => "execution-mode-refutation",
        }
    }
}

/// One test's run that matched its states ([`Stop::execute_result_matching`]): its answer, and
/// the execution it was read from, `None` where the run has no result (its condition refused).
#[derive(Clone, Debug, PartialEq)]
pub struct StoppedMatch {
    pub answer: MatchAnswer,
    pub execution: Option<AdaptedExecution>,
}

impl Stop {
    /// The result run of the test `test_id` from `initial`, as a campaign makes it
    /// ([`Self::execute_result`]: the stop's rules, the test's count and the stop's condition in
    /// one request), matching every state it reaches against `target`, and its answer
    /// ([`judge_matches`]) on a definition whose exclusions are `exclusions`. `tables` holds
    /// `backend`'s definition tables, which the caller keeps beside `backend` for all its runs
    /// ([`DefinitionTables`]). With [`Self::NONE`] the run is the test's run without a stop.
    ///
    /// # Errors
    ///
    /// The adapter's failure of the request, except a refused or unaskable stop condition, which
    /// is the answer [`MatchUnknown::StopConditionRefused`].
    #[expect(
        clippy::too_many_arguments,
        reason = "Self::execute_result's inputs, the backend's tables, the pattern and the \
                  definition's exclusions the answer is judged with"
    )]
    pub fn execute_result_matching(
        self,
        adapter: &ExecutionAdapter,
        backend: &mut Backend,
        tables: &mut DefinitionTables,
        test_id: &str,
        initial: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
        target: &StateMatchRequest,
        exclusions: &DefinitionExclusions,
    ) -> Result<StoppedMatch, ExecutionAdapterFailure> {
        let (execution, undecided) = self.execute_matching(
            adapter,
            backend,
            tables,
            test_id,
            initial,
            budget,
            run,
            None,
            Some(target),
        );
        match execution {
            Ok(execution) => Ok(StoppedMatch {
                answer: judge_matches(&execution, exclusions, undecided.as_deref()),
                execution: Some(execution),
            }),
            Err(ExecutionAdapterFailure::StopCondition(reason)) => Ok(StoppedMatch {
                answer: MatchAnswer::Unknown(MatchUnknown::StopConditionRefused(reason)),
                execution: None,
            }),
            Err(failure) => Err(failure),
        }
    }
}

/// Whether a diagnostic of a reach's path leaves the path's existence decided: only a value the
/// definition leaves open does, since the value k-rust chose is one model of the definition.
const fn open_value(diagnostic: &BackendDiagnosticOutput<Pattern>) -> bool {
    matches!(
        diagnostic,
        BackendDiagnosticOutput::ImplementationChosenValue { .. }
    )
}

/// Whether a leaf of halt `halt` is an end of the truncated system: a state with no successor
/// (`stuck`), an undefined step or state (`trivial`, `vacuous`), or a path's last stop event
/// (`cut-point`, `terminal`). Every other halt cuts its path where the system goes on.
const fn system_end(halt: HaltClass) -> bool {
    matches!(
        halt,
        HaltClass::Stuck
            | HaltClass::Trivial
            | HaltClass::Vacuous
            | HaltClass::CutPoint
            | HaltClass::TerminalRule
    )
}

/// The answer of `execution`, a run that matched its states (module documentation), on a
/// definition whose exclusions are `exclusions`; `undecided` is the reason of the last arrival
/// at which the stop's condition was left undecided, when one was recorded.
#[must_use]
pub fn judge_matches(
    execution: &AdaptedExecution,
    exclusions: &DefinitionExclusions,
    undecided: Option<&str>,
) -> MatchAnswer {
    let unknown = MatchAnswer::Unknown;
    if execution.timed_out() {
        return unknown(MatchUnknown::Clock);
    }
    let facts = execution.facts();
    if !facts.passed_stops.is_empty() {
        return unknown(MatchUnknown::PassedStop(facts.passed_stops.clone()));
    }
    let Some(matches) = execution.state_matches() else {
        return unknown(MatchUnknown::Unmatched);
    };
    let unevaluated = !facts.unsupported_hooks.is_empty()
        || !facts.allowance_refusals.is_empty()
        || execution.leaves().iter().any(allowance_refusal);
    let clean = matches.first_clean_reach.as_ref();
    let open = matches
        .first_dirty_reach
        .as_ref()
        .filter(|reach| reach.diagnostics.iter().all(open_value));
    if let Some(reach) = clean
        .into_iter()
        .chain(open)
        .find(|reach| !reach.term_conjunction)
    {
        return if unevaluated {
            unknown(MatchUnknown::UnevaluatedHook)
        } else {
            MatchAnswer::Hit(reach.clone())
        };
    }
    if let Some(reach) = clean.or(open) {
        return unknown(MatchUnknown::TermConjunction(reach.clone()));
    }
    if let Some(reach) = &matches.first_dirty_reach {
        return unknown(MatchUnknown::DirtyReach(reach.clone()));
    }
    if !matches.undecided.is_empty() || !matches.all_refuted() {
        return unknown(MatchUnknown::UndecidedMatch(
            matches
                .undecided
                .iter()
                .map(|undecided| (undecided.reason, undecided.count))
                .collect(),
        ));
    }
    let leaves = execution.leaves();
    if leaves
        .iter()
        .any(|leaf| leaf.halt == HaltClass::StopUndecided)
    {
        return unknown(MatchUnknown::StopConditionUndecided(
            undecided.map(str::to_owned),
        ));
    }
    let mut cut = leaves.iter().filter(|leaf| !system_end(leaf.halt));
    if let Some(first) = cut.next() {
        return unknown(MatchUnknown::Incomplete {
            halt: first.halt,
            leaves: 1 + cut.count(),
        });
    }
    if let Some(exclusion) = exclusions.run_exclusion(execution) {
        return unknown(MatchUnknown::Exclusion(exclusion));
    }
    let mut diagnosed_leaves = leaves.iter().filter(|leaf| diagnosed(leaf));
    if let Some(first) = diagnosed_leaves.next() {
        return unknown(MatchUnknown::DiagnosedLeaf {
            halt: first.halt,
            leaves: 1 + diagnosed_leaves.count(),
        });
    }
    if matches.stack_stops > 0 {
        return unknown(MatchUnknown::MatcherStackStop(matches.stack_stops));
    }
    if execution.undecided_answers() > 0 {
        return unknown(MatchUnknown::UndecidedAnswers {
            run: facts.smt_unknowns,
            feasibility: facts.decider_smt_unknowns,
            matcher: matches.smt_unknowns,
        });
    }
    if !matches.proof_agreement {
        return unknown(MatchUnknown::ExecutionModeRefutation);
    }
    MatchAnswer::No
}

/// Each premise of [`judge_matches`] on a result built by hand, one leaf at a time: each test
/// changes one field of a run whose answer is `No` and names the cause it then gives.
#[cfg(test)]
mod tests {
    use std::time::Duration;

    use k_rust::backend::{
        BackendDiagnosticOutput, BudgetSubjectOutput, ChosenValueOutput, ExecutionLeaf,
        ExecutionResult, HaltReasonOutput, KoreExecutionResult, ObservedInOutput,
        ResultModalityOutput, SearchFailureOutput, StateMatchOutput, StateMatchesOutput,
        UndecidedMatchReasonOutput, UndecidedStateMatchesOutput, UnevaluatedHookOutput,
    };
    use k_rust::kompile::initial_configuration::kore_sort;
    use kink_native::exclusion::{DefinitionExclusions, Exclusion};
    use kink_native::execution::{
        ExecutionAdapter, ExecutionBudget, HaltClass, RecordedRun, StateMatchRequest,
    };
    use kink_native::feasibility::LeafFeasibility;

    use super::{MatchAnswer, MatchUnknown, Pattern, judge_matches};

    const BUDGET: ExecutionBudget = ExecutionBudget {
        time: Duration::from_secs(60),
        max_simplification_iterations: 100,
        max_depth: None,
        max_breadth: None,
    };

    fn int(value: i64) -> Pattern {
        Pattern::DomainValue {
            sort: kore_sort("SortInt"),
            value: value.to_string().into(),
        }
    }

    fn reach(
        depth: u64,
        diagnostics: Vec<BackendDiagnosticOutput<Pattern>>,
    ) -> StateMatchOutput<Pattern> {
        StateMatchOutput {
            depth,
            state: int(i64::try_from(depth).unwrap()),
            diagnostics,
            term_conjunction: false,
        }
    }

    /// A run of one stuck leaf at depth 2 whose three states the matcher refuted: its answer is
    /// `No` under proof agreement.
    fn refuted() -> KoreExecutionResult {
        ExecutionResult {
            modality: ResultModalityOutput::PathSet,
            leaves: vec![ExecutionLeaf {
                state: int(2),
                diagnostics: Vec::new(),
                candidates: None,
                remainder: None,
                depth: 2,
                reason: HaltReasonOutput::Stuck,
                rule_id: None,
                rule_label: None,
                contradicted_total: None,
                cause: None,
                detail: None,
                trace: Vec::new(),
                branch: Vec::new(),
                effects: Vec::new(),
                observations: Vec::new(),
                stops: None,
                arrivals: None,
            }],
            effects: Vec::new(),
            discarded: Vec::new(),
            coverage: None,
            work: 3,
            expanded: 2,
            polls: 0,
            stack_stops: 0,
            smt_unknowns: 0,
            implementation_chosen_values: Vec::new(),
            contradicted_claims: Vec::new(),
            allowance_refusals: Vec::new(),
            unsupported_hooks: Vec::new(),
            short_circuit_readings: Vec::new(),
            passed_stops: Vec::new(),
            state_matches: Some(StateMatchesOutput {
                first_clean_reach: None,
                first_dirty_reach: None,
                dirty_reaches: 0,
                undecided: Vec::new(),
                matched: 3,
                refuted: 3,
                smt_unknowns: 0,
                stack_stops: 0,
                chain: None,
            }),
        }
    }

    fn matches(result: &mut KoreExecutionResult) -> &mut StateMatchesOutput<Pattern> {
        result.state_matches.as_mut().unwrap()
    }

    fn judge_with(result: KoreExecutionResult, proof_agreement: bool) -> MatchAnswer {
        let feasibility = vec![LeafFeasibility::Syntactic; result.leaves.len()];
        let execution = ExecutionAdapter::adapt_matching_result(
            result,
            false,
            &BUDGET,
            feasibility,
            RecordedRun {
                short_circuit_readings: true,
                ground: true,
            },
            &StateMatchRequest {
                pattern: int(7),
                proof_agreement,
                chain: None,
            },
        )
        .expect("the result is adapted");
        judge_matches(&execution, &DefinitionExclusions::default(), None)
    }

    fn judge(result: KoreExecutionResult) -> MatchAnswer {
        judge_with(result, true)
    }

    fn unknown(cause: MatchUnknown) -> MatchAnswer {
        MatchAnswer::Unknown(cause)
    }

    fn unsimplified() -> BackendDiagnosticOutput<Pattern> {
        BackendDiagnosticOutput::RuleConditionUnsimplified {
            rule_id: "R".to_owned(),
            origin: None,
            limit: 100,
        }
    }

    fn chosen() -> BackendDiagnosticOutput<Pattern> {
        BackendDiagnosticOutput::ImplementationChosenValue {
            hook: "INT.rand".to_owned(),
            class: "unspecified".to_owned(),
        }
    }

    /// The base run answers `No` with proof agreement; without it every state was refuted in
    /// execution mode alone, which may rest on a value the definition leaves open.
    #[test]
    fn a_no_needs_proof_agreement() {
        assert_eq!(judge(refuted()), MatchAnswer::No);
        assert_eq!(
            judge_with(refuted(), false),
            unknown(MatchUnknown::ExecutionModeRefutation)
        );
    }

    /// A stuck leaf that carries a diagnostic, on its own step, a candidate or its remainder,
    /// need not be an end: a rule may have been left unapplied there.
    #[test]
    fn a_diagnosed_leaf_loses_a_no() {
        for diagnostic in [
            unsimplified(),
            BackendDiagnosticOutput::RuleConditionFailed {
                rule_id: "R".to_owned(),
                origin: None,
                failure: SearchFailureOutput::StackExhausted,
            },
            BackendDiagnosticOutput::SimplificationBudgetExhausted {
                limit: 100,
                subject: BudgetSubjectOutput::Predicates,
            },
        ] {
            let mut result = refuted();
            result.leaves[0].diagnostics.push(diagnostic.clone());
            assert_eq!(
                judge(result),
                unknown(MatchUnknown::DiagnosedLeaf {
                    halt: HaltClass::Stuck,
                    leaves: 1,
                }),
                "{diagnostic:?}"
            );
        }
    }

    /// A reach whose path read only values the definition leaves open is a hit; one whose path
    /// also carries another diagnostic is not, and is named.
    #[test]
    fn a_dirty_reach_is_a_hit_only_on_open_values() {
        let mut result = refuted();
        matches(&mut result).first_dirty_reach = Some(reach(1, vec![chosen()]));
        matches(&mut result).dirty_reaches = 1;
        assert_eq!(
            judge(result),
            MatchAnswer::Hit(super::MatchedState {
                depth: 1,
                state: int(1),
                diagnostics: vec![chosen()],
                term_conjunction: false,
            })
        );
        let mut result = refuted();
        matches(&mut result).first_dirty_reach = Some(reach(1, vec![chosen(), unsimplified()]));
        matches(&mut result).dirty_reaches = 1;
        assert!(matches!(
            judge(result),
            MatchAnswer::Unknown(MatchUnknown::DirtyReach(reach))
                if reach.diagnostics == [chosen(), unsimplified()]
        ));
    }

    /// A clean reach is a hit; with a term-level `\and` it is named; in a run that left an
    /// application unevaluated it is no hit.
    #[test]
    fn a_clean_reach_is_a_hit_unless_its_term_or_run_leaves_it_open() {
        let mut result = refuted();
        matches(&mut result).first_clean_reach = Some(reach(1, Vec::new()));
        assert!(matches!(judge(result), MatchAnswer::Hit(reach) if reach.depth == 1));
        let mut result = refuted();
        matches(&mut result).first_clean_reach = Some(StateMatchOutput {
            term_conjunction: true,
            ..reach(1, Vec::new())
        });
        assert!(matches!(
            judge(result),
            MatchAnswer::Unknown(MatchUnknown::TermConjunction(reach)) if reach.term_conjunction
        ));
        let mut result = refuted();
        matches(&mut result).first_clean_reach = Some(reach(1, Vec::new()));
        result.unsupported_hooks.push(UnevaluatedHookOutput {
            hook: "BYTES.x".to_owned(),
            reason: "unsupported".to_owned(),
            observed_in: ObservedInOutput::Run,
        });
        assert_eq!(judge(result), unknown(MatchUnknown::UnevaluatedHook));
    }

    /// An undecided verdict, listed or only counted, loses a `No`.
    #[test]
    fn an_undecided_match_loses_a_no() {
        let mut result = refuted();
        matches(&mut result)
            .undecided
            .push(UndecidedStateMatchesOutput {
                reason: UndecidedMatchReasonOutput::NotCeilFree,
                count: 2,
                first: reach(1, Vec::new()),
            });
        assert_eq!(
            judge(result),
            unknown(MatchUnknown::UndecidedMatch(vec![(
                UndecidedMatchReasonOutput::NotCeilFree,
                2
            )]))
        );
        let mut result = refuted();
        matches(&mut result).refuted = 2;
        assert_eq!(
            judge(result),
            unknown(MatchUnknown::UndecidedMatch(Vec::new()))
        );
    }

    /// An exclusion of the run, a stack stop of the matcher, and an undecided answer of the run
    /// or of the matcher each lose a `No`, and each count is named apart.
    #[test]
    fn exclusions_stack_stops_and_undecided_answers_lose_a_no() {
        let mut result = refuted();
        result.stack_stops = 1;
        assert_eq!(
            judge(result),
            unknown(MatchUnknown::Exclusion(Exclusion::StackStop))
        );
        let mut result = refuted();
        result.implementation_chosen_values.push(ChosenValueOutput {
            hook: "INT.rand".to_owned(),
            class: "unspecified".to_owned(),
        });
        assert_eq!(
            judge(result),
            unknown(MatchUnknown::Exclusion(
                Exclusion::ImplementationChosenValue
            ))
        );
        let mut result = refuted();
        matches(&mut result).stack_stops = 1;
        assert_eq!(judge(result), unknown(MatchUnknown::MatcherStackStop(1)));
        let mut result = refuted();
        result.smt_unknowns = 2;
        assert_eq!(
            judge(result),
            unknown(MatchUnknown::UndecidedAnswers {
                run: 2,
                feasibility: 0,
                matcher: 0,
            })
        );
        let mut result = refuted();
        matches(&mut result).smt_unknowns = 3;
        assert_eq!(
            judge(result),
            unknown(MatchUnknown::UndecidedAnswers {
                run: 0,
                feasibility: 0,
                matcher: 3,
            })
        );
    }

    /// A timed-out run's states are not read; a run without a match request matched none.
    #[test]
    fn a_timed_out_or_unmatched_run_is_unknown() {
        let mut result = refuted();
        result.state_matches = None;
        let execution = ExecutionAdapter::adapt_matching_result(
            result.clone(),
            true,
            &BUDGET,
            vec![LeafFeasibility::Syntactic],
            RecordedRun {
                short_circuit_readings: true,
                ground: true,
            },
            &StateMatchRequest {
                pattern: int(7),
                proof_agreement: true,
                chain: None,
            },
        )
        .expect("the result is adapted");
        assert_eq!(
            judge_matches(&execution, &DefinitionExclusions::default(), None),
            unknown(MatchUnknown::Clock)
        );
        let execution = ExecutionAdapter::adapt_result(
            result,
            false,
            &BUDGET,
            vec![LeafFeasibility::Syntactic],
            RecordedRun {
                short_circuit_readings: true,
                ground: true,
            },
        )
        .expect("the result is adapted");
        assert_eq!(
            judge_matches(&execution, &DefinitionExclusions::default(), None),
            unknown(MatchUnknown::Unmatched)
        );
    }
}
