//! Why a case could not be judged: the reason a case is `unsupported` or `baseline-incomplete`
//! (FZ-UNSUPPORTED; ARCHITECTURE 5.2, 5.3, 4.3).
//!
//! The engine already decides every such case from a fact it read: an unclean leaf's
//! [`UncleanReason`], an unsupported halt, an `Err` result's [`CaseFailure`], a determinism break
//! that demoted a hit candidate, a run fact on no leaf, or, for a differential case, the judge's
//! refusal to compare two ends. This module names those facts ([`UnjudgedReason`]) so that the
//! report can count cases per reason ([`crate::report::Totals::unsupported_reasons`],
//! [`crate::report::Totals::incomplete_reasons`]) and say what to do next.
//!
//! A case is counted once, under one reason: of the reasons that each make it unjudged, the
//! first in [`UnjudgedReason`]'s declaration order. The order runs from the facts of the run as a
//! whole (an `Err`, a bound, a halt) through the facts of a leaf's state to the facts of a
//! judgement (the natural end, the target, the differential comparison), so the reason named is
//! the one nearest the backend; a case may have further reasons, which only show once that one
//! is gone.

use k_rust::backend::{HaltReasonOutput, StopCause};
use serde::{Deserialize, Serialize};

use super::{CaseFailure, CaseResult, DeterminismBreak, FailureCause, LeafReport, UncleanReason};

/// Why a case could not be judged: `unsupported` (a hit, a miss or a stuck end may hide behind
/// it) or `baseline-incomplete` (the baseline's set of ends is not known, so no kill can be
/// judged). Its report name is the kebab-case variant name. The declaration order is the order in
/// which one reason is chosen for a case with several, and the report's key order.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum UnjudgedReason {
    /// The backend answered `Err` for a reason other than a clock, a lack of stack or a refused
    /// initial state ([`FailureCause::Other`]); the engine defects or the message say why.
    BackendError,
    /// The run stopped for lack of stack ([`StopCause::StackExhausted`]).
    StackExhausted,
    /// A clock stopped the run or a path: the per-case safety limit, a step deadline or a
    /// cancellation (`baseline-incomplete` only; such a case is otherwise `timeout`).
    Clock,
    /// A path stopped at `max-work` (`baseline-incomplete` only; otherwise `work-bound`).
    WorkBound,
    /// A path stopped at `max-depth` or the breadth bound (`baseline-incomplete` only;
    /// otherwise `depth-bound`).
    DepthBound,
    /// A leaf halted `indeterminate`: a step needed a value or condition k-rust could not decide.
    HaltIndeterminate,
    /// A leaf halted on a hook k-rust does not implement (`unsupported-hook`).
    HaltUnsupportedHook,
    /// A leaf halted on a simplification error.
    HaltSimplificationError,
    /// A leaf halted `vacuous` after depth 0: its state has no instance.
    HaltVacuous,
    /// A leaf halted where no request asks it to (`branch`, `cut-point`, or a `terminal` halt on
    /// the baseline of a differential case).
    HaltUnexpected,
    /// A leaf's configuration holds an application of a partial function (or a malformed map or
    /// set), so it may denote no value (`ceil_free` fails, T-1). It precedes
    /// [`Self::UndecidedState`]: a sibling leaf's open constraint is often the complementary
    /// condition of the same undefined application (the step's `#Not(#Ceil(...))`), and this
    /// reason names the function.
    NotCeilFree,
    /// A leaf has constraints or variables, or its initial configuration is defined only where
    /// obligations hold (`undefined-initial-instances`): not a decided state.
    UndecidedState,
    /// A leaf could not be internalized in its definition.
    InternalizationFailed,
    /// A leaf rests on a value k-rust chose where the definition leaves it open (an
    /// `implementation-chosen-value` mark).
    ImplementationChosenValue,
    /// A leaf rests on a contradicted claim (a `total`, `functional` or `preserves-definedness`
    /// attribute the run found false).
    ContradictedClaim,
    /// A leaf's simplification ran out of iterations (`max-simplification-iterations`).
    IterationExhaustion,
    /// A rule's side condition failed to simplify on a leaf's path (`rule-condition-failed`).
    SimplificationFailure,
    /// A leaf pattern (a pattern target's) was undecided on a leaf: undecided, matched only
    /// under constraints, or matched only through an implementation-chosen value.
    UndecidedMatch,
    /// The run stopped some work for lack of stack (`stackStops`), or the definition's load did.
    StackStops,
    /// The solver answered `unknown` in the run or in a leaf's matching.
    SmtUnknowns,
    /// The memory allowance refused a result in the run or in the definition's load.
    AllowanceRefusal,
    /// The run left an application unevaluated as an unsupported hook, which may have steered
    /// the equations applied (D21).
    UnsupportedHook,
    /// The run noted an implementation-chosen value or a contradicted claim that no leaf
    /// carries, so another model of the definition may have another leaf (D16).
    RunFactOffLeaves,
    /// The target was reached on a leaf that took an undefined step (a `trivial` halt), which
    /// is no end; without `run-to-completion` that is no hit.
    ReachedUndefinedStep,
    /// The target was reached on a path a bound or a clock cut, which is no end; without
    /// `run-to-completion` that is no hit.
    ReachedCutPath,
    /// Whether a `stuck` leaf is a natural end (the program finished) or an abnormal stop could
    /// not be decided: the normal-end pattern's match was undecided, or no default applies.
    NaturalEndUndecided,
    /// An observer target could not be shown a configuration on the path, which may lead to
    /// the target.
    Unobservable,
    /// Differential: an added or removed end exists, but the mutant's result rests on an
    /// implementation-chosen value or a fact off its leaves (condition 3).
    KillOnChosenValue,
    /// Differential: an end of the mutant that the baseline does not reach, or the mutant's set
    /// against which a baseline end would be removed, holds an end that is not data (an
    /// unevaluated function application, or an overloaded production's application k-rust does
    /// not count as data; condition 4), so the ends cannot be compared.
    MutantEndNotData,
    /// Differential: the baseline's set, against which a mutant end would be added, or a
    /// baseline end the mutant does not reach, holds an end that is not data (condition 4).
    BaselineEndNotData,
    /// A candidate's confirmation on a fresh backend disagreed or failed (an engine defect).
    Unconfirmed,
    /// The engine met a defect judging the case (see the report's engine defects).
    EngineDefect,
}

impl UnjudgedReason {
    /// The reason's report name (`"natural-end-undecided"`, …).
    #[must_use]
    pub fn name(self) -> String {
        serde_json::to_value(self)
            .ok()
            .and_then(|value| value.as_str().map(str::to_owned))
            .unwrap_or_default()
    }

    /// What to do about a case with this reason, as one sentence, when the campaign or the
    /// program can do something; `None` when the reason is a fact of the definition or of
    /// k-rust that no option changes.
    #[must_use]
    pub fn remedy(self) -> Option<&'static str> {
        Some(match self {
            Self::NaturalEndUndecided => {
                "set normal-end-pattern to a pattern of the configuration a finished program ends \
                 in (the default reads only the <k> cells)"
            }
            Self::NotCeilFree => {
                "a leaf holds an undefined application of a partial function (see the warnings \
                 for its symbol): give the function an equation for that argument, mark it \
                 total if it is, or choose values for which the program avoids it"
            }
            Self::Clock => "raise or remove the safety limit",
            Self::WorkBound => "raise max-work",
            Self::DepthBound => "raise max-depth",
            Self::IterationExhaustion => "raise max-simplification-iterations",
            Self::ReachedUndefinedStep => {
                "the target matched the state before an undefined step; with run-to-completion \
                 such a case is reached-unfinished instead"
            }
            Self::ReachedCutPath => "raise the bound that cut the reaching path",
            Self::UndecidedMatch => {
                "make the target pattern decidable on the leaves: avoid function applications \
                 and open values in it"
            }
            Self::MutantEndNotData | Self::BaselineEndNotData => {
                "the end is not data (it holds an unevaluated function application, or an \
                 application of an overloaded production that k-rust does not count as data), \
                 so the two ends cannot be compared: choose a program whose ends hold only \
                 constructors and builtin values, or add the equations that evaluate the \
                 application"
            }
            Self::KillOnChosenValue | Self::ImplementationChosenValue => {
                "the result depends on a value k-rust chose where the definition leaves it open \
                 (map or set order, say): avoid that operation on this path"
            }
            Self::SmtUnknowns => "raise the solver's smt-timeout-ms",
            Self::BackendError
            | Self::StackExhausted
            | Self::HaltIndeterminate
            | Self::HaltUnsupportedHook
            | Self::HaltSimplificationError
            | Self::HaltVacuous
            | Self::HaltUnexpected
            | Self::UndecidedState
            | Self::InternalizationFailed
            | Self::ContradictedClaim
            | Self::SimplificationFailure
            | Self::StackStops
            | Self::AllowanceRefusal
            | Self::UnsupportedHook
            | Self::RunFactOffLeaves
            | Self::Unobservable
            | Self::Unconfirmed
            | Self::EngineDefect => return None,
        })
    }

    /// The reason a leaf's [`UncleanReason`] stands for; `None` for [`UncleanReason::Halt`],
    /// whose reason depends on the halt ([`Self::of_halt`]).
    #[must_use]
    pub fn of_unclean(reason: &UncleanReason) -> Option<Self> {
        Some(match reason {
            UncleanReason::Halt => return None,
            UncleanReason::Undecided => Self::UndecidedState,
            UncleanReason::NotCeilFree(_) => Self::NotCeilFree,
            UncleanReason::ImplementationChosenValue => Self::ImplementationChosenValue,
            UncleanReason::ContradictedClaim => Self::ContradictedClaim,
            UncleanReason::IterationExhaustion => Self::IterationExhaustion,
            UncleanReason::StackStops => Self::StackStops,
            UncleanReason::SmtUnknowns => Self::SmtUnknowns,
            UncleanReason::AllowanceRefusal => Self::AllowanceRefusal,
            UncleanReason::UnsupportedHook => Self::UnsupportedHook,
            UncleanReason::Internalization(_) => Self::InternalizationFailed,
            UncleanReason::SimplificationFailure => Self::SimplificationFailure,
            UncleanReason::UndecidedMatch => Self::UndecidedMatch,
            UncleanReason::NaturalEndUndecided => Self::NaturalEndUndecided,
        })
    }

    /// The reason a halt that is not an end stands for: an unsupported halt, a bound, a clock,
    /// or a halt no request asks for. `None` for the ends `stuck` and `trivial` (an undefined
    /// step).
    #[must_use]
    pub fn of_halt(halt: HaltReasonOutput) -> Option<Self> {
        use HaltReasonOutput as H;
        Some(match halt {
            H::Indeterminate => Self::HaltIndeterminate,
            H::UnsupportedHook => Self::HaltUnsupportedHook,
            H::SimplificationError => Self::HaltSimplificationError,
            H::Vacuous => Self::HaltVacuous,
            H::WorkBound => Self::WorkBound,
            H::DepthBound | H::BreadthBound => Self::DepthBound,
            H::Timeout | H::Cancelled => Self::Clock,
            H::Terminal | H::Branch | H::CutPoint => Self::HaltUnexpected,
            H::Stuck | H::Trivial => return None,
        })
    }

    /// The reason an `Err` result stands for, when it makes the case unjudged.
    #[must_use]
    pub fn of_failure(failure: &CaseFailure) -> Self {
        match &failure.cause {
            FailureCause::Stop(StopCause::StackExhausted(_)) => Self::StackExhausted,
            FailureCause::Stop(StopCause::Cancelled | StopCause::Deadline(_)) => Self::Clock,
            FailureCause::Stop(StopCause::SolverPrelude(_))
            | FailureCause::StateRefused
            | FailureCause::Other => Self::BackendError,
        }
    }

    /// The reason a determinism break stands for.
    #[must_use]
    pub fn of_break(fact: DeterminismBreak) -> Self {
        match fact {
            DeterminismBreak::Clock => Self::Clock,
            DeterminismBreak::SmtUnknowns => Self::SmtUnknowns,
            DeterminismBreak::StackStops => Self::StackStops,
            DeterminismBreak::AllowanceRefusal => Self::AllowanceRefusal,
        }
    }
}

/// The first, in declaration order, of a leaf's reasons beyond its halt (D13): what makes a leaf
/// `unsupported` whatever it reaches. `None` for a leaf unclean by its halt alone or clean.
pub(crate) fn beyond_halt(leaf: &LeafReport) -> Option<UnjudgedReason> {
    leaf.unclean
        .iter()
        .filter(|reason| {
            !matches!(
                reason,
                UncleanReason::Halt | UncleanReason::NaturalEndUndecided
            )
        })
        .filter_map(UnjudgedReason::of_unclean)
        .min()
}

/// Why a differential side's all-paths run is not complete (ARCHITECTURE 4.3 condition 1): the
/// first fact, in declaration order, among those that refuse it, read as
/// `target::differential::complete_ends` reads them. `None` when the run is complete.
pub(crate) fn incomplete(result: &CaseResult) -> Option<UnjudgedReason> {
    let mut reasons = Vec::new();
    if let Some(failure) = &result.failure {
        reasons.push(UnjudgedReason::of_failure(failure));
    }
    if result.safety_limit_hit {
        reasons.push(UnjudgedReason::Clock);
    }
    if result.run_facts_off_leaves {
        reasons.push(UnjudgedReason::RunFactOffLeaves);
    }
    reasons.extend(
        result
            .determinism_breaks()
            .into_iter()
            .map(UnjudgedReason::of_break),
    );
    if result.stack_stops > 0 {
        reasons.push(UnjudgedReason::StackStops);
    }
    if result.smt_unknowns > 0 {
        reasons.push(UnjudgedReason::SmtUnknowns);
    }
    if result.run_allowance_refusals > 0 {
        reasons.push(UnjudgedReason::AllowanceRefusal);
    }
    if result.failure.is_none() && result.leaves.is_empty() {
        reasons.push(UnjudgedReason::HaltVacuous);
    }
    for leaf in &result.leaves {
        reasons.extend(incomplete_leaf(leaf));
    }
    reasons.into_iter().min()
}

/// Why one leaf is not an end a complete set may hold: a clean `stuck` leaf, or an undefined
/// step unclean only by its halt.
fn incomplete_leaf(leaf: &LeafReport) -> Option<UnjudgedReason> {
    match UnjudgedReason::of_halt(leaf.halt) {
        None => beyond_halt(leaf),
        Some(halt) => Some(beyond_halt(leaf).map_or(halt, |reason| reason.min(halt))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reason_names_are_kebab_case_and_read_back() {
        for (reason, name) in [
            (UnjudgedReason::NaturalEndUndecided, "natural-end-undecided"),
            (UnjudgedReason::NotCeilFree, "not-ceil-free"),
            (UnjudgedReason::MutantEndNotData, "mutant-end-not-data"),
            (UnjudgedReason::WorkBound, "work-bound"),
        ] {
            assert_eq!(reason.name(), name);
            let back: UnjudgedReason =
                serde_json::from_value(serde_json::json!(name)).expect("reads back");
            assert_eq!(back, reason);
        }
    }

    #[test]
    fn a_leaf_reason_beyond_the_halt_is_chosen_by_declaration_order() {
        let leaf = LeafReport {
            halt: HaltReasonOutput::Stuck,
            depth: 1,
            state: k_rust::kore::parser::parse_pattern(r"\top{SortK{}}()").expect("parses"),
            unclean: vec![
                UncleanReason::NotCeilFree(None),
                UncleanReason::SmtUnknowns,
                UncleanReason::NaturalEndUndecided,
            ],
            natural_end: false,
            matches: Vec::new(),
            rewrites: Vec::new(),
            constructor_only: None,
        };
        assert_eq!(beyond_halt(&leaf), Some(UnjudgedReason::NotCeilFree));
    }
}
