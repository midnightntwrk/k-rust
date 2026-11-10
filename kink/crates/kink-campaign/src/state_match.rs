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
//!
//! A chain `P1, [U2] P2, …, [Un] Pn` asks the same question of a path instead of a state: does
//! some path of the truncated system have states `s1`, …, `sn`, each at or after the previous
//! one, matching the steps under one assignment of the variables they share, with no state
//! strictly between `s(i-1)` and `si` matching `Ui`? The run matches the chain along each of its
//! paths ([`Stop::execute_result_chain_matching`], k-rust `StateMatchRequest::chain`), and
//! [`judge_chain_matches`] reads the chain's summary as [`judge_matches`] reads a pattern's: a
//! completion is a hit on the terms a reach is, and a `No` needs every premise above, with the
//! chain's matcher in the matcher's place, and in addition that no path's partial occurrences
//! overflowed the cap the request names ([`CHAIN_PARTIAL_CAP`] by default). An overflow evicts
//! occurrences a later state could have completed, so it loses a `No`, and since an evicted
//! occurrence completes nothing, it never makes a hit. The run merges two states only when
//! their paths' chain progress agrees, so it can spend more work than the run without the chain,
//! and a work budget can cut it where that run completes: that is the work budget's cause
//! ([`MatchUnknown::Incomplete`]), not the chain's.

use k_rust::backend::{Backend, BackendDiagnosticOutput, PassedStopOutput};
use k_rust::kore::ast::Pattern;
use kink_native::bridge::diagnosed;
use kink_native::exclusion::{DefinitionExclusions, Exclusion, allowance_refusal};
use kink_native::execution::{
    AdaptedExecution, ChainCompletion, ChainPartOutput, ChainRequest, DefinitionTables,
    ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget, HaltClass, MatchedState, ResultRun,
    StateMatchRequest, UndecidedMatchReasonOutput,
};

use crate::runner::Stop;

/// The default most partial occurrences of a chain one path of a run keeps
/// ([`ChainRequest::partial_cap`]). A count, never a clock: beyond it the run evicts partial
/// occurrences and reports the path overflowed, which can turn a `No` into
/// [`MatchUnknown::ChainPartialCap`] and never creates a hit. A key that names a chain's answer
/// names the cap its request was made with.
pub const CHAIN_PARTIAL_CAP: usize = 256;

/// The answer of one run that matched its states ([`judge_matches`]), or a chain along its
/// paths ([`judge_chain_matches`]); `R` is what a hit is: a reached state ([`MatchedState`]) for
/// a pattern, a completion ([`ChainCompletion`]) for a chain.
#[derive(Clone, Debug, PartialEq)]
pub enum MatchAnswer<R = MatchedState> {
    /// A state the run reached matches, or a path of the run completes the chain: the reach or
    /// the completion k-rust reported, with every step's depth, state and bindings, and the
    /// diagnostics of its path up to its last state (none, or only
    /// `implementation-chosen-value`).
    Hit(R),
    /// In every model of the definition, no state of the truncated system matches, or no path of
    /// it completes the chain.
    No,
    /// Neither is shown.
    Unknown(MatchUnknown<R>),
}

/// Why some matches of a run were undecided ([`MatchUnknown::UndecidedMatch`]): for a pattern,
/// k-rust's reason a reached state's verdict was undecided; for a chain, the part whose match
/// was undecided, with k-rust's reason.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UndecidedReason {
    /// A reached state's verdict was undecided, for k-rust's reason.
    State(UndecidedMatchReasonOutput),
    /// `undecided-step`: the match of the chain's step `step` (from 1) at a state, against some
    /// partial occurrence (or at the start, for step 1), was undecided for k-rust's reason: the
    /// state has a constraint, is not shown to exist, the match was undecided or under
    /// constraints, the modes disagreed or a bound stopped it. The occurrence is extended only by
    /// the ways that were decided, so a completion may have been missed.
    Step {
        step: usize,
        reason: UndecidedMatchReasonOutput,
    },
    /// `undecided-unless`: the match of the `unless` of the chain's step `step` (from 1) at a
    /// state after the previous step's, for k-rust's reason, was undecided. The occurrence is
    /// dropped, since keeping it could complete a chain the `unless` excludes, so a completion
    /// may have been missed.
    Unless {
        step: usize,
        reason: UndecidedMatchReasonOutput,
    },
}

impl UndecidedReason {
    /// A short name: k-rust's name of the reason for a state, the part's for a chain.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::State(reason) => match reason {
                UndecidedMatchReasonOutput::UndecidedState => "undecided-state",
                UndecidedMatchReasonOutput::NotCeilFree => "not-ceil-free",
                UndecidedMatchReasonOutput::UndecidedMatch => "undecided-match",
                UndecidedMatchReasonOutput::PlacementBound => "placement-bound",
            },
            Self::Step { .. } => "undecided-step",
            Self::Unless { .. } => "undecided-unless",
        }
    }

    /// k-rust's reason.
    #[must_use]
    pub const fn reason(self) -> UndecidedMatchReasonOutput {
        match self {
            Self::State(reason) | Self::Step { reason, .. } | Self::Unless { reason, .. } => reason,
        }
    }
}

/// Why a run's answer is [`MatchAnswer::Unknown`]: the first missing premise, in the order
/// [`judge_matches`] and [`judge_chain_matches`] read them; `R` is the answer's hit.
#[derive(Clone, Debug, PartialEq)]
pub enum MatchUnknown<R = MatchedState> {
    /// The watchdog fired before the run ended, so its states are not read.
    Clock,
    /// The stop's condition refused at an arrival, or could not be given to the run: the stop is
    /// not defined on this run, so neither is its system.
    StopConditionRefused(String),
    /// The run went on past a step of a stop rule that had another successor (k-rust
    /// `passedStops`): on that branch its states need not be states of the truncated system.
    PassedStop(Vec<PassedStopOutput>),
    /// The first reach (or completion) rests on its path's diagnostics up to it, which carry
    /// more than values the definition leaves open: the path may not exist.
    DirtyReach(R),
    /// Every reach's term (or some step state's term of every completion) holds a term-level
    /// `\and`, which is no configuration of the definition's own making.
    TermConjunction(R),
    /// The run left an application unevaluated, as an unsupported hook or a `Bytes` result the
    /// memory allowance refused: where it is undefined, the state holding it denotes no
    /// configuration, which k-rust did not compute.
    UnevaluatedHook,
    /// The matcher left the verdict of some reached state undecided, or a chain's matcher left a
    /// step's or an `unless`'s match undecided, for each reason the count k-rust reported, in
    /// k-rust's order.
    UndecidedMatch(Vec<(UndecidedReason, u64)>),
    /// A chain's matcher evicted partial occurrences beyond its cap
    /// ([`ChainRequest::partial_cap`]) on this many paths, so a completion may have been missed
    /// on them.
    ChainPartialCap(u64),
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
    /// The matcher (a chain's, for a chain) stopped for lack of native stack, which leaves its
    /// match undecided and puts the summary outside k-rust's determinism contract.
    MatcherStackStop(usize),
    /// Some decision the exploration rests on may rest on an undecided solver answer: the run's
    /// own (`run`), the adapter's about the leaves' feasibility (`feasibility`), the matcher's
    /// (`matcher`; a chain's, for a chain).
    UndecidedAnswers {
        run: usize,
        feasibility: usize,
        matcher: usize,
    },
    /// The run did not match its states (it was made without a match request), or, for a
    /// chain, did not match a chain (its request had none).
    Unmatched,
    /// Every premise of a `No` holds but one: the request did not ask for proof agreement
    /// (`StateMatchRequest::proof_agreement`), so each state was refuted in execution mode
    /// alone, where the matcher may have read a value the definition leaves open without the run
    /// recording it (module documentation).
    ExecutionModeRefutation,
}

impl<R> MatchUnknown<R> {
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
            Self::ChainPartialCap(_) => "chain-partial-cap",
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

/// One test's run that matched its states ([`Stop::execute_result_matching`]) or a chain
/// ([`Stop::execute_result_chain_matching`]): its answer, and the execution it was read from,
/// `None` where the run has no result (its condition refused).
#[derive(Clone, Debug, PartialEq)]
pub struct StoppedMatch<R = MatchedState> {
    pub answer: MatchAnswer<R>,
    pub execution: Option<AdaptedExecution>,
}

impl Stop {
    /// The result run of the test `test_id` from `initial`, as a campaign makes it
    /// ([`Self::execute_result`]: the stop's rules, the test's count and the stop's condition in
    /// one request), matching every state it reaches against `target`, and its answer
    /// ([`judge_matches`]) on a definition whose exclusions are `exclusions`. `tables` holds
    /// `backend`'s definition tables, which the caller keeps beside `backend` for all its runs
    /// ([`DefinitionTables`]). With [`Self::NONE`] the run is the test's run without a stop.
    /// The answer is `target`'s pattern's: a chain `target` carries is matched but not judged
    /// ([`Self::execute_result_chain_matching`] judges one).
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
        stopped(execution, |execution| {
            judge_matches(execution, exclusions, undecided.as_deref())
        })
    }

    /// The result run of the test `test_id` from `initial`, as [`Self::execute_result_matching`]
    /// makes it, matching the chain `chain` along its paths, and the chain's answer
    /// ([`judge_chain_matches`]). The request's own pattern is the chain's first step, matched
    /// apart and not judged; every part of the chain is matched in both modes when
    /// `proof_agreement`, which a `No` needs. With [`Self::NONE`] the run is the test's run
    /// without a stop, whose every path ends where it ends. A chain run may merge fewer states
    /// than the run without it, since it merges two states only when their paths' chain
    /// progress agrees, so it may spend more work, and a work budget can then cut it
    /// ([`MatchUnknown::Incomplete`]).
    ///
    /// # Errors
    ///
    /// The adapter's failure of the request, a chain without steps among them (k-rust refuses a
    /// chain whose steps do not classify its variables consistently), except a refused or
    /// unaskable stop condition, which is the answer [`MatchUnknown::StopConditionRefused`].
    #[expect(
        clippy::too_many_arguments,
        reason = "Self::execute_result's inputs, the backend's tables, the chain, its modes and \
                  the definition's exclusions the answer is judged with"
    )]
    pub fn execute_result_chain_matching(
        self,
        adapter: &ExecutionAdapter,
        backend: &mut Backend,
        tables: &mut DefinitionTables,
        test_id: &str,
        initial: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
        chain: ChainRequest,
        proof_agreement: bool,
        exclusions: &DefinitionExclusions,
    ) -> Result<StoppedMatch<ChainCompletion>, ExecutionAdapterFailure> {
        let Some(first) = chain.steps.first() else {
            return Err(ExecutionAdapterFailure::Backend(
                "a chain has at least one step".to_owned(),
            ));
        };
        let target = StateMatchRequest {
            pattern: first.pattern.clone(),
            proof_agreement,
            chain: Some(chain),
        };
        let (execution, undecided) = self.execute_matching(
            adapter,
            backend,
            tables,
            test_id,
            initial,
            budget,
            run,
            None,
            Some(&target),
        );
        stopped(execution, |execution| {
            judge_chain_matches(execution, exclusions, undecided.as_deref())
        })
    }
}

/// The answer `judge` gives `execution`, and the execution, or the answer of a refused or
/// unaskable stop condition, which has no execution.
fn stopped<R>(
    execution: Result<AdaptedExecution, ExecutionAdapterFailure>,
    judge: impl FnOnce(&AdaptedExecution) -> MatchAnswer<R>,
) -> Result<StoppedMatch<R>, ExecutionAdapterFailure> {
    match execution {
        Ok(execution) => Ok(StoppedMatch {
            answer: judge(&execution),
            execution: Some(execution),
        }),
        Err(ExecutionAdapterFailure::StopCondition(reason)) => Ok(StoppedMatch {
            answer: MatchAnswer::Unknown(MatchUnknown::StopConditionRefused(reason)),
            execution: None,
        }),
        Err(failure) => Err(failure),
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

/// What a hit is read from: a reached state, or a chain's completion.
trait Reached: Clone {
    /// The diagnostics of the path up to the reach, or up to the completion's last state.
    fn diagnostics(&self) -> &[BackendDiagnosticOutput<Pattern>];
    /// Whether the state's term, or some step state's term of the completion, holds a
    /// term-level `\and`.
    fn term_conjunction(&self) -> bool;
}

impl Reached for MatchedState {
    fn diagnostics(&self) -> &[BackendDiagnosticOutput<Pattern>] {
        &self.diagnostics
    }

    fn term_conjunction(&self) -> bool {
        self.term_conjunction
    }
}

impl Reached for ChainCompletion {
    fn diagnostics(&self) -> &[BackendDiagnosticOutput<Pattern>] {
        &self.diagnostics
    }

    fn term_conjunction(&self) -> bool {
        self.term_conjunction
    }
}

/// The answer the reaches give, where they give one: the first clean reach, else the first
/// dirty reach whose path carries only values the definition leaves open, whose term holds no
/// term-level `\and`, is a hit, unless the run left an application unevaluated (`unevaluated`);
/// such a reach whose term holds one is [`MatchUnknown::TermConjunction`]; any other dirty
/// reach is [`MatchUnknown::DirtyReach`]. `None` when there is no reach.
fn reached<R: Reached>(
    clean: Option<&R>,
    dirty: Option<&R>,
    unevaluated: bool,
) -> Option<MatchAnswer<R>> {
    let open = dirty.filter(|reach| reach.diagnostics().iter().all(open_value));
    if let Some(reach) = clean
        .into_iter()
        .chain(open)
        .find(|reach| !reach.term_conjunction())
    {
        return Some(if unevaluated {
            MatchAnswer::Unknown(MatchUnknown::UnevaluatedHook)
        } else {
            MatchAnswer::Hit(reach.clone())
        });
    }
    if let Some(reach) = clean.or(open) {
        return Some(MatchAnswer::Unknown(MatchUnknown::TermConjunction(
            reach.clone(),
        )));
    }
    dirty.map(|reach| MatchAnswer::Unknown(MatchUnknown::DirtyReach(reach.clone())))
}

/// Whether the run left an application unevaluated, as an unsupported hook or a result its
/// memory allowance refused, in the run or on a leaf.
fn unevaluated(execution: &AdaptedExecution) -> bool {
    let facts = execution.facts();
    !facts.unsupported_hooks.is_empty()
        || !facts.allowance_refusals.is_empty()
        || execution.leaves().iter().any(allowance_refusal)
}

/// The premises of a `No` that are facts of the run's exploration, in order: no path ended at
/// an arrival where the stop's condition was left undecided, every leaf is an end of the
/// truncated system, the run is not excluded, and no leaf carries a diagnostic. The first that
/// fails, as its cause.
fn explored<R>(
    execution: &AdaptedExecution,
    exclusions: &DefinitionExclusions,
    undecided: Option<&str>,
) -> Result<(), MatchUnknown<R>> {
    let leaves = execution.leaves();
    if leaves
        .iter()
        .any(|leaf| leaf.halt == HaltClass::StopUndecided)
    {
        return Err(MatchUnknown::StopConditionUndecided(
            undecided.map(str::to_owned),
        ));
    }
    let mut cut = leaves.iter().filter(|leaf| !system_end(leaf.halt));
    if let Some(first) = cut.next() {
        return Err(MatchUnknown::Incomplete {
            halt: first.halt,
            leaves: 1 + cut.count(),
        });
    }
    if let Some(exclusion) = exclusions.run_exclusion(execution) {
        return Err(MatchUnknown::Exclusion(exclusion));
    }
    let mut diagnosed_leaves = leaves.iter().filter(|leaf| diagnosed(leaf));
    if let Some(first) = diagnosed_leaves.next() {
        return Err(MatchUnknown::DiagnosedLeaf {
            halt: first.halt,
            leaves: 1 + diagnosed_leaves.count(),
        });
    }
    Ok(())
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
    if let Some(answer) = reached(
        matches.first_clean_reach.as_ref(),
        matches.first_dirty_reach.as_ref(),
        unevaluated(execution),
    ) {
        return answer;
    }
    if !matches.undecided.is_empty() || !matches.all_refuted() {
        return unknown(MatchUnknown::UndecidedMatch(
            matches
                .undecided
                .iter()
                .map(|undecided| (UndecidedReason::State(undecided.reason), undecided.count))
                .collect(),
        ));
    }
    if let Err(cause) = explored(execution, exclusions, undecided) {
        return unknown(cause);
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

/// The answer of `execution`, a run that matched a chain along its paths
/// ([`Stop::execute_result_chain_matching`]), on a definition whose exclusions are
/// `exclusions`; `undecided` is the reason of the last arrival at which the stop's condition
/// was left undecided, when one was recorded.
///
/// It is [`judge_matches`] with the chain's summary in place of the pattern's:
/// - a hit is the first clean completion, else the first dirty completion whose path carries
///   only values the definition leaves open, no step state of which holds a term-level `\and`,
///   in a run that left no application unevaluated;
/// - a `No` needs, beyond the premises of the run's exploration, that the chain's matcher
///   completed no chain, left no step's and no `unless`'s match undecided, evicted no partial
///   occurrence beyond its cap ([`MatchUnknown::ChainPartialCap`]), stopped for no lack of
///   stack, and received no undecided solver answer, as the run itself and the adapter's
///   questions about the leaves' feasibility did not, all under proof agreement.
///
/// Nothing is read of the request's own pattern's summary (the chain's first step, matched
/// apart): the chain's matcher matches the first step itself at every state, so no answer of the
/// chain rests on that summary's verdicts, its undecided solver answers or its stack stops,
/// which k-rust counts apart from the chain's.
#[must_use]
pub fn judge_chain_matches(
    execution: &AdaptedExecution,
    exclusions: &DefinitionExclusions,
    undecided: Option<&str>,
) -> MatchAnswer<ChainCompletion> {
    let unknown = MatchAnswer::Unknown;
    if execution.timed_out() {
        return unknown(MatchUnknown::Clock);
    }
    let facts = execution.facts();
    if !facts.passed_stops.is_empty() {
        return unknown(MatchUnknown::PassedStop(facts.passed_stops.clone()));
    }
    let Some(chain) = execution
        .state_matches()
        .and_then(|matches| matches.chain.as_ref())
    else {
        return unknown(MatchUnknown::Unmatched);
    };
    if let Some(answer) = reached(
        chain.first_clean_completion.as_ref(),
        chain.first_dirty_completion.as_ref(),
        unevaluated(execution),
    ) {
        return answer;
    }
    if !chain.undecided.is_empty() || chain.dirty_completions > 0 {
        return unknown(MatchUnknown::UndecidedMatch(
            chain
                .undecided
                .iter()
                .map(|undecided| {
                    let (step, reason) = (undecided.step, undecided.reason);
                    let part = match undecided.part {
                        ChainPartOutput::Step => UndecidedReason::Step { step, reason },
                        ChainPartOutput::Unless => UndecidedReason::Unless { step, reason },
                    };
                    (part, undecided.count)
                })
                .collect(),
        ));
    }
    if chain.overflowed_paths > 0 {
        return unknown(MatchUnknown::ChainPartialCap(chain.overflowed_paths));
    }
    if let Err(cause) = explored(execution, exclusions, undecided) {
        return unknown(cause);
    }
    if chain.stack_stops > 0 {
        return unknown(MatchUnknown::MatcherStackStop(chain.stack_stops));
    }
    let answers = facts
        .smt_unknowns
        .saturating_add(facts.decider_smt_unknowns)
        .saturating_add(chain.smt_unknowns);
    if answers > 0 {
        return unknown(MatchUnknown::UndecidedAnswers {
            run: facts.smt_unknowns,
            feasibility: facts.decider_smt_unknowns,
            matcher: chain.smt_unknowns,
        });
    }
    let agreed = execution
        .state_matches()
        .is_some_and(|matches| matches.proof_agreement);
    if !agreed {
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
        BackendDiagnosticOutput, BindingOutput, BudgetSubjectOutput, ChainCompletionOutput,
        ChainMatchesOutput, ChainPartOutput, ChainStepMatchOutput, ChainUndecidedOutput,
        ChosenValueOutput, ExecutionLeaf, ExecutionResult, HaltReasonOutput, KoreExecutionResult,
        ObservedInOutput, ResultModalityOutput, SearchFailureOutput, StateMatchOutput,
        StateMatchesOutput, UndecidedMatchReasonOutput, UndecidedStateMatchesOutput,
        UnevaluatedHookOutput,
    };
    use k_rust::kompile::initial_configuration::kore_sort;
    use k_rust::kore::ast::{Variable, VariableKind};
    use kink_native::exclusion::{DefinitionExclusions, Exclusion};
    use kink_native::execution::{
        AdaptedExecution, ChainBinding, ChainCompletion, ChainRequest, ChainStepMatch,
        ChainStepRequest, ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget, HaltClass,
        RecordedRun, RunBounds, StateMatchRequest,
    };
    use kink_native::feasibility::LeafFeasibility;

    use super::{
        CHAIN_PARTIAL_CAP, MatchAnswer, MatchUnknown, Pattern, UndecidedReason,
        judge_chain_matches, judge_matches,
    };

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
                UndecidedReason::State(UndecidedMatchReasonOutput::NotCeilFree),
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

    fn variable_p() -> Variable {
        Variable {
            kind: VariableKind::Element,
            name: "VarP".to_owned(),
            sort: kore_sort("SortInt"),
        }
    }

    /// A completion of two steps at `depths`, each binding `P` to its depth, on a path whose
    /// diagnostics up to the last step's state are `diagnostics`.
    fn completion(
        depths: [u64; 2],
        diagnostics: Vec<BackendDiagnosticOutput<Pattern>>,
    ) -> ChainCompletionOutput<Pattern> {
        ChainCompletionOutput {
            steps: (1..)
                .zip(depths)
                .map(|(step, depth)| ChainStepMatchOutput {
                    step,
                    depth,
                    state: int(i64::try_from(depth).unwrap()),
                    bindings: vec![BindingOutput {
                        variable: Pattern::Variable(variable_p()),
                        value: int(i64::try_from(depth).unwrap()),
                    }],
                })
                .collect(),
            diagnostics,
            term_conjunction: false,
        }
    }

    /// [`completion`] as kink-native converts it.
    fn completed(
        depths: [u64; 2],
        diagnostics: Vec<BackendDiagnosticOutput<Pattern>>,
    ) -> ChainCompletion {
        ChainCompletion {
            steps: (1..)
                .zip(depths)
                .map(|(step, depth)| ChainStepMatch {
                    step,
                    depth,
                    state: int(i64::try_from(depth).unwrap()),
                    bindings: vec![ChainBinding {
                        variable: Pattern::Variable(variable_p()),
                        value: int(i64::try_from(depth).unwrap()),
                    }],
                })
                .collect(),
            diagnostics,
            term_conjunction: false,
        }
    }

    /// [`refuted`] whose request also matched a chain, which no path completed and which left
    /// nothing undecided, evicted nothing, and met no stop or undecided answer: its answer is
    /// `No` under proof agreement.
    fn chain_refuted() -> KoreExecutionResult {
        let mut result = refuted();
        matches(&mut result).chain = Some(ChainMatchesOutput {
            first_clean_completion: None,
            first_dirty_completion: None,
            dirty_completions: 0,
            undecided: Vec::new(),
            overflowed_paths: 0,
            peak_partials: 1,
            states: 3,
            evaluations: 5,
            smt_unknowns: 0,
            stack_stops: 0,
        });
        result
    }

    fn chain(result: &mut KoreExecutionResult) -> &mut ChainMatchesOutput<Pattern> {
        matches(result).chain.as_mut().unwrap()
    }

    /// The request of a chain `P` then `P` at the default cap.
    fn chain_request(proof_agreement: bool) -> StateMatchRequest {
        let step = |imports: Vec<Variable>, exports: Vec<Variable>| ChainStepRequest {
            pattern: Pattern::Variable(variable_p()),
            imports,
            exports,
            unless: None,
        };
        StateMatchRequest {
            pattern: Pattern::Variable(variable_p()),
            proof_agreement,
            chain: Some(ChainRequest {
                steps: vec![
                    step(Vec::new(), vec![variable_p()]),
                    step(vec![variable_p()], Vec::new()),
                ],
                partial_cap: CHAIN_PARTIAL_CAP,
            }),
        }
    }

    /// `result` as the run of [`chain_request`] under `bounds`.
    fn adapt_chain(
        result: KoreExecutionResult,
        bounds: RunBounds,
        proof_agreement: bool,
    ) -> AdaptedExecution {
        let feasibility = vec![LeafFeasibility::Syntactic; result.leaves.len()];
        ExecutionAdapter::adapt_bounded_matching_result(
            result,
            false,
            &BUDGET,
            bounds,
            feasibility,
            RecordedRun {
                short_circuit_readings: true,
                ground: true,
            },
            &chain_request(proof_agreement),
        )
        .expect("the result is adapted")
    }

    fn judge_chain_bounded(
        result: KoreExecutionResult,
        bounds: RunBounds,
        proof_agreement: bool,
    ) -> MatchAnswer<ChainCompletion> {
        let execution = adapt_chain(result, bounds, proof_agreement);
        judge_chain_matches(&execution, &DefinitionExclusions::default(), None)
    }

    fn judge_chain(result: KoreExecutionResult) -> MatchAnswer<ChainCompletion> {
        judge_chain_bounded(result, RunBounds::NONE, true)
    }

    fn chain_unknown(cause: MatchUnknown<ChainCompletion>) -> MatchAnswer<ChainCompletion> {
        MatchAnswer::Unknown(cause)
    }

    /// The base chain run answers `No` with proof agreement, and without it is refuted in
    /// execution mode alone; a run whose request asked for no chain answers nothing about one.
    #[test]
    fn a_chain_no_needs_proof_agreement_and_a_chain() {
        assert_eq!(judge_chain(chain_refuted()), MatchAnswer::No);
        assert_eq!(
            judge_chain_bounded(chain_refuted(), RunBounds::NONE, false),
            chain_unknown(MatchUnknown::ExecutionModeRefutation)
        );
        let execution = ExecutionAdapter::adapt_matching_result(
            refuted(),
            false,
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
            judge_chain_matches(&execution, &DefinitionExclusions::default(), None),
            chain_unknown(MatchUnknown::Unmatched)
        );
        // A result reports a chain exactly when its request asked for one.
        for (result, request) in [
            (refuted(), chain_request(true)),
            (
                chain_refuted(),
                StateMatchRequest {
                    pattern: int(7),
                    proof_agreement: true,
                    chain: None,
                },
            ),
        ] {
            assert!(matches!(
                ExecutionAdapter::adapt_matching_result(
                    result,
                    false,
                    &BUDGET,
                    vec![LeafFeasibility::Syntactic],
                    RecordedRun {
                        short_circuit_readings: true,
                        ground: true,
                    },
                    &request,
                ),
                Err(ExecutionAdapterFailure::Backend(_))
            ));
        }
    }

    /// The chain's answer reads nothing of the request's own pattern's summary: a reach of the
    /// first step, an undecided verdict, a stack stop and undecided answers there leave the
    /// chain's `No`, and the pattern's own `No` ignores the chain's counts.
    #[test]
    fn the_chain_and_its_first_step_are_judged_apart() {
        let mut result = chain_refuted();
        let own = matches(&mut result);
        own.first_clean_reach = Some(reach(1, Vec::new()));
        own.undecided.push(UndecidedStateMatchesOutput {
            reason: UndecidedMatchReasonOutput::UndecidedMatch,
            count: 1,
            first: reach(1, Vec::new()),
        });
        own.stack_stops = 1;
        own.smt_unknowns = 2;
        assert_eq!(judge_chain(result), MatchAnswer::No);
        let mut result = chain_refuted();
        chain(&mut result).smt_unknowns = 2;
        chain(&mut result).stack_stops = 1;
        chain(&mut result).overflowed_paths = 1;
        let execution = adapt_chain(result, RunBounds::NONE, true);
        assert_eq!(
            judge_matches(&execution, &DefinitionExclusions::default(), None),
            MatchAnswer::No
        );
    }

    /// A clean completion is a hit, carrying every step's depth, state and bindings.
    #[test]
    fn a_clean_completion_is_a_hit() {
        let mut result = chain_refuted();
        chain(&mut result).first_clean_completion = Some(completion([1, 2], Vec::new()));
        assert_eq!(
            judge_chain(result),
            MatchAnswer::Hit(completed([1, 2], Vec::new()))
        );
    }

    /// A completion on a path that read only values the definition leaves open is a hit; one
    /// whose path carries another diagnostic is the dirty completion, named.
    #[test]
    fn a_dirty_completion_is_a_hit_only_on_open_values() {
        let mut result = chain_refuted();
        chain(&mut result).first_dirty_completion = Some(completion([1, 2], vec![chosen()]));
        chain(&mut result).dirty_completions = 1;
        assert_eq!(
            judge_chain(result),
            MatchAnswer::Hit(completed([1, 2], vec![chosen()]))
        );
        let mut result = chain_refuted();
        chain(&mut result).first_dirty_completion =
            Some(completion([1, 2], vec![chosen(), unsimplified()]));
        chain(&mut result).dirty_completions = 1;
        assert_eq!(
            judge_chain(result),
            chain_unknown(MatchUnknown::DirtyReach(completed(
                [1, 2],
                vec![chosen(), unsimplified()]
            )))
        );
    }

    /// A completion some step state of which holds a term-level `\and` is named, not a hit.
    #[test]
    fn a_term_conjunction_completion_is_no_hit() {
        let mut result = chain_refuted();
        chain(&mut result).first_clean_completion = Some(ChainCompletionOutput {
            term_conjunction: true,
            ..completion([1, 2], Vec::new())
        });
        assert_eq!(
            judge_chain(result),
            chain_unknown(MatchUnknown::TermConjunction(ChainCompletion {
                term_conjunction: true,
                ..completed([1, 2], Vec::new())
            }))
        );
    }

    /// A run that left an application unevaluated gives no hit, the completion clean or not.
    #[test]
    fn an_unevaluated_hook_loses_a_chain_hit() {
        let mut result = chain_refuted();
        chain(&mut result).first_clean_completion = Some(completion([1, 2], Vec::new()));
        result.unsupported_hooks.push(UnevaluatedHookOutput {
            hook: "BYTES.x".to_owned(),
            reason: "unsupported".to_owned(),
            observed_in: ObservedInOutput::Run,
        });
        assert_eq!(
            judge_chain(result),
            chain_unknown(MatchUnknown::UnevaluatedHook)
        );
    }

    fn undecided_part(
        part: ChainPartOutput,
        step: usize,
        count: u64,
    ) -> ChainUndecidedOutput<Pattern> {
        ChainUndecidedOutput {
            part,
            step,
            reason: UndecidedMatchReasonOutput::UndecidedMatch,
            count,
            first: reach(1, Vec::new()),
            bindings: Vec::new(),
        }
    }

    /// An undecided step match loses a `No`, as `undecided-step`.
    #[test]
    fn an_undecided_step_loses_a_chain_no() {
        let mut result = chain_refuted();
        chain(&mut result)
            .undecided
            .push(undecided_part(ChainPartOutput::Step, 2, 3));
        let answer = judge_chain(result);
        assert_eq!(
            answer,
            chain_unknown(MatchUnknown::UndecidedMatch(vec![(
                UndecidedReason::Step {
                    step: 2,
                    reason: UndecidedMatchReasonOutput::UndecidedMatch,
                },
                3
            )]))
        );
        let MatchAnswer::Unknown(MatchUnknown::UndecidedMatch(undecided)) = answer else {
            unreachable!()
        };
        assert_eq!(undecided[0].0.name(), "undecided-step");
    }

    /// An undecided `unless` match loses a `No`, as `undecided-unless`.
    #[test]
    fn an_undecided_unless_loses_a_chain_no() {
        let mut result = chain_refuted();
        chain(&mut result)
            .undecided
            .push(undecided_part(ChainPartOutput::Unless, 2, 1));
        let answer = judge_chain(result);
        assert_eq!(
            answer,
            chain_unknown(MatchUnknown::UndecidedMatch(vec![(
                UndecidedReason::Unless {
                    step: 2,
                    reason: UndecidedMatchReasonOutput::UndecidedMatch,
                },
                1
            )]))
        );
        let MatchAnswer::Unknown(MatchUnknown::UndecidedMatch(undecided)) = answer else {
            unreachable!()
        };
        assert_eq!(undecided[0].0.name(), "undecided-unless");
    }

    /// A path whose partial occurrences overflowed the cap loses a `No`.
    #[test]
    fn an_overflow_is_the_chain_partial_cap() {
        let mut result = chain_refuted();
        chain(&mut result).overflowed_paths = 2;
        let answer = judge_chain(result);
        assert_eq!(answer, chain_unknown(MatchUnknown::ChainPartialCap(2)));
        let MatchAnswer::Unknown(cause) = answer else {
            unreachable!()
        };
        assert_eq!(cause.name(), "chain-partial-cap");
    }

    /// An undecided answer of the chain's matcher loses a `No`, named as the matcher's.
    #[test]
    fn a_chain_smt_unknown_loses_a_chain_no() {
        let mut result = chain_refuted();
        chain(&mut result).smt_unknowns = 3;
        assert_eq!(
            judge_chain(result),
            chain_unknown(MatchUnknown::UndecidedAnswers {
                run: 0,
                feasibility: 0,
                matcher: 3,
            })
        );
        let mut result = chain_refuted();
        result.smt_unknowns = 2;
        assert_eq!(
            judge_chain(result),
            chain_unknown(MatchUnknown::UndecidedAnswers {
                run: 2,
                feasibility: 0,
                matcher: 0,
            })
        );
    }

    /// A stack stop of the chain's matcher loses a `No`.
    #[test]
    fn a_chain_stack_stop_loses_a_chain_no() {
        let mut result = chain_refuted();
        chain(&mut result).stack_stops = 1;
        assert_eq!(
            judge_chain(result),
            chain_unknown(MatchUnknown::MatcherStackStop(1))
        );
    }

    /// A run the work budget cut (which a chain run reaches sooner, since it merges fewer
    /// states) is the budget's cause, not the chain's.
    #[test]
    fn a_work_budget_cut_is_the_budgets_cause() {
        let mut result = chain_refuted();
        result.leaves[0].reason = HaltReasonOutput::WorkBound;
        let answer = judge_chain_bounded(result, RunBounds::work(Some(3)), true);
        assert_eq!(
            answer,
            chain_unknown(MatchUnknown::Incomplete {
                halt: HaltClass::WorkBound,
                leaves: 1,
            })
        );
        let MatchAnswer::Unknown(cause) = answer else {
            unreachable!()
        };
        assert_eq!(cause.name(), "incomplete");
    }
}
