//! A stop condition: a question an in-process caller answers at each arrival at a stop, so that a
//! path ends at the `stop_count`th arrival where the answer is yes
//! ([`ExecutionOptions::stop_count`](super::ExecutionOptions::stop_count)).
//!
//! # Meaning
//!
//! An *arrival* is a step by a selected cut-point or terminal rule that is its state's one
//! successor, whose successor is defined. Its *stop state* is the state the path would end at
//! there: the state before the step for a cut-point rule, the step's normalized successor for a
//! terminal rule. A *stop event* is an arrival whose stop state the condition holds of; without a
//! condition every arrival is an event. A path ends at its `stop_count`th event, and takes every
//! other arrival as any other step: a cut-point rule's step is committed, a terminal rule's path
//! goes on. So a condition that holds everywhere changes nothing, and the run to the Nth event is
//! one path, which keeps its structural sharing, its memos and its trace through every arrival.
//!
//! The condition is asked only at arrivals, each once, and only of their stop states. A step by
//! a stop rule with several successors is no arrival whatever the condition says: it stays a
//! passed stop (`ExecutionResult::passed_stops`), and the condition is not asked there. A step
//! by a stop rule is an arrival only once its successor is shown defined, so the successor is
//! normalized within the step before the condition is asked, on either side, and a successor
//! that goes on takes that normalization instead of repeating it. A step whose successor is
//! undefined is therefore no arrival: it is not asked about, so it is never an undecided stop
//! ([`StopDecision::Undecided`]) and never a refusal ([`StopDecision::Refused`]). Asked within
//! the step, the condition costs the run no state visit, so a condition that always holds does
//! not change the run's work either.
//!
//! Each path counts its arrivals and its events: [`ExecutionLeaf::arrivals`](super::ExecutionLeaf::arrivals)
//! and [`ExecutionLeaf::stops`](super::ExecutionLeaf::stops). Under `state-set` a state merges
//! only into a state of the same counts. The condition must be a function of the stop state's
//! configuration, so a cut point merges by configuration and a terminal leaf by arrival as
//! without a condition.
//!
//! An undecided answer ends the path at the arrival with a [`HaltReason::StopUndecided`](super::HaltReason::StopUndecided) leaf,
//! the stop state: continuing would run past a possible stop, and stopping would claim an event
//! that was not shown. A refused answer (the observation does not exist at that state) fails the
//! request ([`StopConditionRefusal`]).
//!
//! # Isolation
//!
//! The condition is asked from the stepping loop, between two phases of a state's expansion,
//! never inside a simplification or a rewrite. Its work is isolated from the run
//! (`coverage::isolated`): it reports to no coverage set, emits no diagnostic into the run,
//! notes no path fact, fills none of the run's memos and is recorded by no operation record of
//! the run; it runs off the run's clock, so a step deadline neither stops it nor is charged
//! with its time, in a proof evaluation scope without a console and outside the run's definition
//! scope. A computation it runs (another definition's simplification) opens its own operation,
//! poll budget, stack measurement and record inside it. A cancellation of the request stays
//! visible inside it and ends the run at its next poll.
//!
//! # Successors read by the caller
//!
//! Whether a step by a stop rule is its state's one successor rests on the step's other
//! candidates. The backend reads a candidate whose condition it leaves open (a condition over
//! an application no equation it tried reduced) as a successor: in some model of the
//! definition the condition holds. A caller that reads the definition more closely gives the
//! run a [`SuccessorReading`], with or without a condition ([`InProcess`]); KRS, for one, reads
//! a ground application of a partial function defined by its equations alone, which no equation
//! reduced, as having no value, so that a condition over it does not hold. The backend asks the
//! reading about each candidate of a step that holds a selected stop rule's candidate, and about
//! its remainder, and a candidate the reading says denotes no state is no successor of that
//! step: the step goes on without it, so a stop rule's candidate left alone is an arrival. The
//! reading decides nothing at any other step. Where it would leave a step no candidate and no
//! remainder, it contradicts the step the backend built, and the step is taken as built.
//!
//! The reading is asked with the candidate's path condition as the step built it and with
//! whether the run so far left a hook unevaluated ([`Candidate::hooks_unevaluated`]). An
//! application the backend did not reduce was tried within the step that built the candidate,
//! so every hook that trial left unevaluated is noted before the reading is asked: a hook the
//! run leaves unevaluated later reads no condition the reading decided.

use k_rust_kore::kore::ast as kore;

use crate::term::{Term, TermKind};

/// Where an arrival's stop state lies relative to the stop rule's step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StopSide {
    /// A cut-point rule: the stop state is the state before the step.
    Before,
    /// A terminal rule: the stop state is the step's normalized successor.
    After,
}

/// What a [`StopCondition`] answers of an arrival's stop state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StopDecision {
    /// The condition holds: the arrival is a stop event.
    Holds,
    /// The condition does not hold: the arrival is taken as any other step.
    Fails,
    /// Whether the condition holds is not known (a budget of its evaluation ran out, or its
    /// solver answered `Unknown`): the path ends at the arrival, `stop-undecided`, with this
    /// reason.
    Undecided(String),
    /// The condition has no value at the stop state, so the stop criterion is undefined on this
    /// run: the request fails, naming this reason.
    Refused(String),
}

/// A question asked at each arrival at a stop of an in-process execution
/// ([module documentation](self)).
pub trait StopCondition {
    /// Answer `arrival`. Must be a function of the arrival's stop state's configuration, so
    /// that the same configuration gets the same answer wherever it is met.
    fn decide(&mut self, arrival: &Arrival<'_>) -> StopDecision;
}

impl<F: FnMut(&Arrival<'_>) -> StopDecision> StopCondition for F {
    fn decide(&mut self, arrival: &Arrival<'_>) -> StopDecision {
        self(arrival)
    }
}

/// How an in-process caller reads a step's candidates where the backend leaves their conditions
/// open ([module documentation](self), "Successors read by the caller").
pub trait SuccessorReading {
    /// Whether `candidate` denotes no state under the caller's reading of the definition: `true`
    /// makes it no successor of its step; `false` leaves it one, as the backend reads it. Must be
    /// a function of the candidate's path condition and of [`Candidate::hooks_unevaluated`].
    fn denotes_no_state(&self, candidate: &Candidate<'_>) -> bool;
}

/// A candidate of a step, or its remainder, as a [`SuccessorReading`] is asked about it.
pub struct Candidate<'a> {
    pub(crate) path_condition: &'a [kore::Pattern],
    pub(crate) hooks_unevaluated: bool,
}

impl Candidate<'_> {
    /// The conjuncts of the candidate's path condition, as KORE predicates: the state's path
    /// condition and what the step added to it (the rule's condition, or for the remainder the
    /// negation of the candidates').
    #[must_use]
    pub fn path_condition(&self) -> &[kore::Pattern] {
        self.path_condition
    }

    /// Whether the run, its definition's load included, left a hook unevaluated before the
    /// question (`ExecutionResult::unsupported_hooks` so far).
    #[must_use]
    pub fn hooks_unevaluated(&self) -> bool {
        self.hooks_unevaluated
    }
}

/// What an in-process caller adds to an execution ([`super::execute_in_process`]): a stop
/// condition, a reading of the step's candidates, both or neither.
#[derive(Default)]
pub struct InProcess<'a> {
    /// The stop condition asked at each arrival ([`StopCondition`]).
    pub condition: Option<&'a mut dyn StopCondition>,
    /// The reading of a stop rule's step's candidates ([`SuccessorReading`]).
    pub reading: Option<&'a dyn SuccessorReading>,
}

/// An arrival at a stop, as a [`StopCondition`] is asked about it.
pub struct Arrival<'a> {
    pub(crate) rule: &'a str,
    pub(crate) side: StopSide,
    pub(crate) depth: u64,
    pub(crate) term: &'a Term,
}

impl Arrival<'_> {
    /// The stop rule, by the name the request selected it by.
    #[must_use]
    pub fn rule(&self) -> &str {
        self.rule
    }

    /// Whether the stop state is before the rule's step or after it.
    #[must_use]
    pub fn side(&self) -> StopSide {
        self.side
    }

    /// The depth of the stop state on its path.
    #[must_use]
    pub fn depth(&self) -> u64 {
        self.depth
    }

    /// The stop state's whole configuration (its term, without its constraints), as KORE. Its
    /// cost is the size of the configuration; [`Self::cell`] converts one cell.
    #[must_use]
    pub fn configuration(&self) -> kore::Pattern {
        crate::externalize::term(self.term)
    }

    /// The cell at `path` of the stop state's configuration, as KORE, or `None` where the
    /// configuration holds no such cell.
    ///
    /// `path` names cell symbols from the configuration's top cell down: `path[0]` is the
    /// configuration's own symbol, and each further symbol is that of a cell the previous one
    /// holds as a direct argument. Only that cell is converted, so the cost is the walk down the
    /// path and the size of the cell, not of the configuration.
    #[must_use]
    pub fn cell(&self, path: &[&str]) -> Option<kore::Pattern> {
        let (first, below) = path.split_first()?;
        let mut current = self.term;
        if application_symbol(current)? != *first {
            return None;
        }
        for symbol in below {
            let TermKind::Application { arguments, .. } = current.kind() else {
                return None;
            };
            current = arguments
                .iter()
                .find(|argument| application_symbol(argument) == Some(symbol))?;
        }
        Some(crate::externalize::term(current))
    }
}

fn application_symbol(term: &Term) -> Option<&str> {
    match term.kind() {
        TermKind::Application { symbol, .. } => Some(&symbol.name),
        _ => None,
    }
}

/// Why a request with a stop condition failed: the condition refused at an arrival
/// ([`StopDecision::Refused`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StopConditionRefusal {
    /// The stop rule, by the name the request selected it by.
    pub rule: String,
    /// Whether the stop state was before the rule's step or after it.
    pub side: StopSide,
    /// The depth of the stop state.
    pub depth: u64,
    /// The condition's reason.
    pub reason: String,
}

impl std::fmt::Display for StopConditionRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "the stop condition has no value at the arrival {} `{}` at depth {}: {}",
            match self.side {
                StopSide::Before => "before",
                StopSide::After => "after",
            },
            self.rule,
            self.depth,
            self.reason
        )
    }
}

impl std::error::Error for StopConditionRefusal {}

/// Ask `condition` about `arrival`, isolated from the run ([module documentation](self)).
pub(super) fn ask(condition: &mut dyn StopCondition, arrival: &Arrival<'_>) -> StopDecision {
    let (decision, _) = crate::coverage::isolated(u64::MAX, || {
        let _proof =
            crate::evaluation::EvaluationScope::enter(crate::evaluation::EvaluationMode::Proof);
        crate::term::domain::outside_definition_scopes(|| condition.decide(arrival))
    });
    decision
}
