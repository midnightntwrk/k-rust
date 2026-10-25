//! Why a case could not be judged: the reason a case is `unsupported` or `baseline-incomplete`
//! (FZ-UNSUPPORTED; ARCHITECTURE 5.2, 5.3, 4.3).
//!
//! The engine already decides every such case from a fact it read: an unclean leaf's
//! [`UncleanReason`], an unsupported halt, an `Err` result's [`CaseFailure`], a determinism break
//! that demoted a hit candidate, a run fact on no leaf, or, for a differential case, the judge's
//! refusal to compare two ends. This module names those facts ([`UnjudgedReason`]) so that the
//! report can count cases per reason ([`crate::report::Totals::unsupported_reasons`],
//! [`crate::report::Totals::baseline_incomplete_reasons`]) and say what to do next.
//!
//! A case is counted once, under one reason: of the reasons that each make it unjudged, the
//! first in [`UnjudgedReason`]'s declaration order. The order runs from the facts of the run as a
//! whole (an `Err`, a bound, a halt) through the facts of a leaf's state to the facts of a
//! judgement (the natural end, the target, the differential comparison), so the reason named is
//! the one nearest the backend; a case may have further reasons, which only show once that one
//! is gone.

use k_rust::backend::{
    BuiltinFailureOutput, HaltReasonOutput, SatisfiabilityOutput, SearchFailureOutput,
    SmtFailureOutput, StopCause,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::{
    CaseFailure, CaseResult, ComparableCondition, DeterminismBreak, FailureCause, HaltCause,
    InternalHalt, LeafReport, UncleanReason,
};
use crate::crash::{BUILTIN_SITE, INVALID_BUILTIN_RESULT_SYMBOL_SITE, cause_site};

/// Why a case could not be judged: `unsupported` (a hit, a miss or a stuck end may hide behind
/// it) or `baseline-incomplete` (the baseline's set of ends is not known, so no kill can be
/// judged). Its report name is the kebab-case variant name, and for the two reasons that name a
/// condition ([`Self::EndNotComparable`], [`Self::QueryNotConfirmable`]) that name, a colon and
/// the condition's name (`end-not-comparable:work-bound`). The declaration order is the order in
/// which one reason is chosen for a case with several, and the report's key order; the two
/// reasons that name a condition come last (serde reads a name without a condition first), and
/// each is the only reason of its case: it demotes a hit.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum UnjudgedReason {
    /// The run or its judgement panicked ([`FailureCause::Panic`]): a defect of k-rust or of the
    /// engine, reported among the report's `crashes`.
    Panic,
    /// The backend answered an error without a typed kind that is not a clock, a lack of stack
    /// or a refused initial state ([`FailureCause::Other`]): a defect of k-rust or of the engine,
    /// reported among the report's `crashes`.
    InternalError,
    /// A leaf halted on a cause no correct k-rust gives ([`InternalHalt`], FZ-CRASH-CAUSE): a
    /// builtin hook's failure or an invalid builtin result symbol (a hook declaration k-rust
    /// should have refused, or a defect of k-rust), a solver failure of k-rust's own making, a
    /// macro or alias at run time, or a `simplification-error` halt without its cause. Reported
    /// among the report's `crashes`; a leaf on any path of either side makes the case unjudged.
    InternalHalt,
    /// The request is nested deeper than the largest stack the backend provides for one
    /// operation ([`FailureCause::TooDeep`]): a bound the build fixes, a function of the input.
    TooDeep,
    /// The host refused to map a stack segment ([`FailureCause::StackMappingRefused`]): the
    /// environment, outside the determinism contract.
    StackMappingRefused,
    /// The run stopped for lack of stack ([`StopCause::StackExhausted`]).
    StackExhausted,
    /// A clock stopped the run or a path: the per-case safety limit or a step deadline
    /// (`baseline-incomplete` only; such a case is otherwise `timeout`).
    Clock,
    /// The caller cancelled the run (a watchdog's or a client's cancellation token) while the
    /// case ran (`baseline-incomplete` only; such a case is otherwise `timeout`).
    Cancelled,
    /// A path stopped at `max-work` (`baseline-incomplete` only; otherwise `work-bound`).
    WorkBound,
    /// A path stopped at `max-depth` or the breadth bound (`baseline-incomplete` only;
    /// otherwise `depth-bound`).
    DepthBound,
    /// A leaf halted `indeterminate`: a step needed a value or condition k-rust could not decide.
    HaltIndeterminate,
    /// A leaf halted on a hook k-rust does not implement (`unsupported-hook`).
    HaltUnsupportedHook,
    /// A leaf's simplification ended at `max-simplification-iterations`: an option bound
    /// (cause `iteration-limit` or `predicate-iteration-limit`).
    HaltIterationLimit,
    /// A step needed a solver answer it did not get (an SMT failure as the cause of a
    /// `simplification-error` or `indeterminate` halt): the query does not translate to
    /// SMT-LIB, the build has no solver, the solver answered `unknown`, or it rejected a script
    /// that holds text the definition or a user prelude supplied.
    HaltSmt,
    /// A leaf's simplification met a construct k-rust leaves undecided by design: equations of
    /// one priority that give different results (`conflicting-results`), or an unsupported hook.
    HaltUnsupportedConstruct,
    /// A leaf halted `vacuous` after depth 0: its state has no instance.
    HaltVacuous,
    /// A leaf halted where no request asks it to (`branch`, `cut-point`, or a `terminal` halt on
    /// the baseline of a differential case).
    HaltUnexpected,
    /// A leaf's configuration is not shown to exist (k-rust's `ground_defined` fails, T-1): it
    /// holds an application of a partial function that no ceil equation or `value-production`
    /// discharges, or map keys or set elements not shown apart, so it may denote no value. It precedes
    /// [`Self::UndecidedState`]: a sibling leaf's open constraint is often the complementary
    /// condition of the same undefined application (the step's `#Not(#Ceil(...))`), and this
    /// reason names the function. At `any-state`, also a reached state the target pattern
    /// matches (k-rust's `not-ceil-free` state match).
    NotCeilFree,
    /// A leaf has constraints or variables, or its initial configuration is defined only where
    /// obligations hold (`undefined-initial-instances`): not a decided state. At `any-state`,
    /// also a reached state with constraints or variables (k-rust's `undecided-state`), or a
    /// reach whose prefix's initial definedness was left open.
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
    /// A leaf pattern (a pattern target's) was undecided on a leaf, or at `any-state` on a
    /// reached state: undecided, matched only under constraints, or matched only through an
    /// implementation-chosen value (the two evaluation modes disagree).
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
    /// An all-paths `fired` target (a state-set run, FZ-STATESET B1): some explored path fired
    /// the target rule (it is in the run's committed transitions, FZ-STATESET-MATCH), but no
    /// retained leaf's trace or terminal halt shows it on a path that ends as the target needs,
    /// so the case would be `miss`, `stuck` or `reached-unfinished`, and the leaves decide
    /// neither way (not every leaf can carry a hit of the whole run, and some path ends
    /// naturally). A state set keeps one arrival per distinct configuration of a depth and drops
    /// the trace of every other, so the rule may have fired on a path that ends cleanly (and
    /// naturally, under `run-to-completion`), or on no such path: neither a hit nor one of those
    /// classes is shown.
    FiredOffTrace,
    /// A pattern target `at: any-state` under `run-to-completion` (FZ-STATESET-MATCH, S4): a
    /// configuration the pattern matches was reached on a clean path, but the hit also needs
    /// that path to end cleanly and naturally (and in data, with `data-end`), and a reached
    /// state is attributed to no leaf; so every leaf of the run must be such an end, and this
    /// run's are not (some leaf is cut, an abnormal stop, an undefined step or unclean), while
    /// some is a natural end, so the class `reached-unfinished` is not shown either.
    AnyStateUnattributed,
    /// The target was reached on a leaf that took an undefined step (a `trivial` halt), which
    /// is no end; without `run-to-completion` that is no hit.
    ReachedUndefinedStep,
    /// The target was reached on a path a bound or a clock cut, which is no end; without
    /// `run-to-completion` that is no hit for a target read at a leaf. (A pattern target
    /// `at: any-state` reads the reached state, which a later cut cannot unmake: a hit,
    /// FZ-STATESET-MATCH, CUT-PATH-HIT.)
    ReachedCutPath,
    /// The target was reached on a natural end that is not data (a rule or pattern target with
    /// `run-to-completion` and `data-end`, `crate::Target::data_end`): the witness would become
    /// a test whose end no differential can compare, so it is no hit.
    ReachedEndNotData,
    /// Whether a `stuck` leaf is a natural end (the program finished) or an abnormal stop could
    /// not be decided: the normal-end pattern's match was undecided, or no default applies.
    NaturalEndUndecided,
    /// An observer target could not be shown a configuration on the path, which may lead to
    /// the target. (A pattern target `at: any-state` no longer gives it: k-rust matches every
    /// reached state inside the run, FZ-STATESET-MATCH.)
    Unobservable,
    /// Differential: an added or removed end exists, but the mutant's result is no evidence
    /// (condition 3): some leaf, or the result's lists (a fact off the leaves, which under state
    /// sets holds the marks of merged arrivals), carry an implementation-chosen value or a
    /// contradicted claim. A chosen value makes the result depend on a choice k-rust made; a
    /// contradicted claim makes the definition inconsistent on this input, so none of its ends
    /// is a fact of the definition.
    KillWithoutEvidence,
    /// A compared or reaching end is not data because a definition of the case (the baseline,
    /// or the mutant) has no data: its full critical-pair check reports a pair it does not join,
    /// an equation the evaluator does not apply to every subject it describes, or a violated
    /// precondition (`k_rust_backend::data_term`), so no end of it is data. Chosen in place of
    /// the not-data reasons below whenever a side's definition has no data. A campaign whose
    /// definition has no data ends `not-comparable` before its first case (the report's
    /// `definition-findings` list the findings), so no campaign counts a case under it.
    DefinitionNotConfluent,
    /// Differential: an end of the mutant that the baseline does not reach, or the mutant's set
    /// against which a baseline end would be removed, holds an end that is not data in both
    /// definitions (condition 4): an unevaluated function application, an overload application
    /// an overload equation could still lower, one whose overload family is broken, or one the
    /// other definition's equations, overload members or subsorts would rewrite. So the ends
    /// cannot be compared.
    MutantEndNotData,
    /// Differential: the baseline's set, against which a mutant end would be added, or a
    /// baseline end the mutant does not reach, holds an end that is not data (condition 4).
    BaselineEndNotData,
    /// A candidate's confirmation on a fresh backend disagreed or failed (an engine defect).
    Unconfirmed,
    /// The engine met a defect judging the case (see the report's engine defects).
    EngineDefect,
    /// A candidate hit the client's witness filter refused (`crate::filter`, FZ-COMPARABLE-B):
    /// the client would not accept the case as a witness, for the cause the report's
    /// `totals.filter` counts it under. Judged before the case's confirmation, so the hit it
    /// demotes is unconfirmed; it is the only reason of its case.
    ClientRefused,
    /// A rule or pattern hit under `comparable-end` (`crate::Target::comparable`) whose witness
    /// program's run of every path is not comparable: it fails the named condition, the first
    /// in [`ComparableCondition`]'s order (`crate::exec::comparable::end_conditions`).
    #[serde(untagged)]
    EndNotComparable(EndNotComparable),
    /// A pattern hit under `query-confirmable` (`crate::Target::query_confirmable`) that kink's
    /// query could not confirm: the run fails the named condition, the first in
    /// [`ComparableCondition`]'s order (`crate::exec::comparable::query_conditions`).
    #[serde(untagged)]
    QueryNotConfirmable(QueryNotConfirmable),
}

/// Defines a reason payload that names a [`ComparableCondition`] and reads and writes as
/// `PREFIX:CONDITION`.
macro_rules! condition_reason {
    ($(#[$meta:meta])* $name:ident, $prefix:literal) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(pub ComparableCondition);

        impl Serialize for $name {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                serializer.collect_str(&format_args!(concat!($prefix, ":{}"), self.0.name()))
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                let name = String::deserialize(deserializer)?;
                name.strip_prefix(concat!($prefix, ":"))
                    .and_then(ComparableCondition::of_name)
                    .map(Self)
                    .ok_or_else(|| {
                        serde::de::Error::custom(format!(
                            "`{name}` is not `{}:` and a condition",
                            $prefix
                        ))
                    })
            }
        }
    };
}

condition_reason!(
    /// The condition of [`UnjudgedReason::EndNotComparable`], named `end-not-comparable:CONDITION`.
    EndNotComparable,
    "end-not-comparable"
);

condition_reason!(
    /// The condition of [`UnjudgedReason::QueryNotConfirmable`], named
    /// `query-not-confirmable:CONDITION`.
    QueryNotConfirmable,
    "query-not-confirmable"
);

/// The remedy of [`UnjudgedReason::MutantEndNotData`] and [`UnjudgedReason::BaselineEndNotData`].
const NOT_DATA_REMEDY: &str = concat!(
    "the end is not data in both definitions: it holds an application of a function that no",
    " equation evaluates, an overload application that an overload equation could still ",
    "lower, an application of a symbol of a broken overload family, or one the other ",
    "definition's equations, overload members or subsorts would rewrite, so the two ends ",
    "cannot be compared and this case cannot be judged; a program or hole range whose ends ",
    "hold only constructors, builtin values and irreducible overload applications can be",
);

/// The remedy of [`UnjudgedReason::DefinitionNotConfluent`].
const DEFINITION_NOT_CONFLUENT_REMEDY: &str = concat!(
    "a definition of the case has no data: its full critical-pair check reports a pair it ",
    "does not join, an equation the evaluator does not apply to every subject it describes,",
    " or a violated precondition (the report's warnings name each one, ",
    "`definition-not-confluent`), so no end of it can be compared and no case of this ",
    "definition pair can be judged, whatever the budget, bounds or values; a pair the check",
    " reports may also be one it cannot decide, so read each finding before changing an ",
    "equation",
);

/// The remedy of [`UnjudgedReason::ReachedEndNotData`].
const REACHED_END_NOT_DATA_REMEDY: &str = concat!(
    "the target was reached on a natural end that is not data, so the witness's end could ",
    "not be compared with a mutant's; choose a program or hole range whose ends hold only ",
    "constructors, builtin values and irreducible overload applications, or accept such ",
    "ends (campaign key `data-end = false`, command line `--no-data-end`, library ",
    "`Target::data_end`); a negated property is exempt",
);

/// The remedy of [`UnjudgedReason::HaltSmt`].
const HALT_SMT_REMEDY: &str = concat!(
    "a step needed a solver answer it did not get: the query does not translate to SMT-LIB, ",
    "this build has no solver, the solver answered unknown, or it rejected SMT text the ",
    "definition or a user prelude supplies; a build with Z3, or a larger time limit per query ",
    "(campaign key `smt-timeout-ms`, command line `--smt-timeout`, library ",
    "`CaseOptions::backend.smt_timeout_ms`), may decide it, or choose a program or hole range ",
    "whose runs avoid that query",
);

/// The remedy of [`UnjudgedReason::FiredOffTrace`].
const FIRED_OFF_TRACE_REMEDY: &str = concat!(
    "the target rule fired in the run of every path, but on no path the result keeps that ",
    "ends as the target needs: the state set kept another path to the same configuration, so ",
    "whether a path that fired it ends that way is not shown; ",
    "target mode `covered` (campaign key `mode`, command line `--rule-mode`, library ",
    "`RuleMode::Covered`) asks whether any explored step applied the rule, and another program ",
    "or hole range may fire it on a path the result keeps",
);

/// The remedy of [`UnjudgedReason::AnyStateUnattributed`].
const ANY_STATE_UNATTRIBUTED_REMEDY: &str = concat!(
    "a configuration the pattern matches was reached on a clean path, but under ",
    "run-to-completion the hit needs that path to end cleanly and naturally, and a reached ",
    "configuration names no leaf, so every leaf of the run must be a clean natural end; ",
    "without run-to-completion (campaign key `run-to-completion = false`, command line ",
    "`--no-run-to-completion`, library `Target::run_to_completion`) the reach alone is a hit, ",
    "and a program or hole range whose every path ends cleanly can be one with it",
);

/// The remedy of [`UnjudgedReason::ClientRefused`].
const CLIENT_REFUSED_REMEDY: &str = concat!(
    "the client's witness filter refused the hit (the report's client-refusals give each ",
    "cause's first case, the client's detail and remedy); another program or hole range may ",
    "give a hit the client accepts",
);

/// The remedy of [`UnjudgedReason::EndNotComparable`].
const END_NOT_COMPARABLE_REMEDY: &str = concat!(
    "the target was reached, but the witness program's run of every path is not one kink can ",
    "compare (it is cut, stops abnormally, is undecided, ends in a term that is not data, or ",
    "carries a diagnostic or a definition fact the reason names), so the hit is refused; a ",
    "program or hole range whose every path ends cleanly in data can be a hit, or accept such ",
    "hits (campaign key ",
    "`comparable = false`, command line `--no-comparable`, library `Target::comparable`)",
);

/// The remedy of [`UnjudgedReason::QueryNotConfirmable`].
const QUERY_NOT_CONFIRMABLE_REMEDY: &str = concat!(
    "the pattern was matched, but the run carries a diagnostic or a run fact the reason names, ",
    "which kink's query reads on the matching state (its search absorbs converging paths), so ",
    "the hit is refused; a program or hole range whose run carries none can be a hit (library ",
    "`Target::query_confirmable`, which has no command-line flag)",
);

impl UnjudgedReason {
    /// Every reason that names no condition, in declaration order: the reasons that name one
    /// ([`Self::EndNotComparable`], [`Self::QueryNotConfirmable`]) are one per
    /// [`ComparableCondition`].
    pub const ALL: [Self; 44] = [
        Self::Panic,
        Self::InternalError,
        Self::InternalHalt,
        Self::TooDeep,
        Self::StackMappingRefused,
        Self::StackExhausted,
        Self::Clock,
        Self::Cancelled,
        Self::WorkBound,
        Self::DepthBound,
        Self::HaltIndeterminate,
        Self::HaltUnsupportedHook,
        Self::HaltIterationLimit,
        Self::HaltSmt,
        Self::HaltUnsupportedConstruct,
        Self::HaltVacuous,
        Self::HaltUnexpected,
        Self::NotCeilFree,
        Self::UndecidedState,
        Self::InternalizationFailed,
        Self::ImplementationChosenValue,
        Self::ContradictedClaim,
        Self::IterationExhaustion,
        Self::SimplificationFailure,
        Self::UndecidedMatch,
        Self::StackStops,
        Self::SmtUnknowns,
        Self::AllowanceRefusal,
        Self::UnsupportedHook,
        Self::RunFactOffLeaves,
        Self::FiredOffTrace,
        Self::AnyStateUnattributed,
        Self::ReachedUndefinedStep,
        Self::ReachedCutPath,
        Self::ReachedEndNotData,
        Self::NaturalEndUndecided,
        Self::Unobservable,
        Self::KillWithoutEvidence,
        Self::DefinitionNotConfluent,
        Self::MutantEndNotData,
        Self::BaselineEndNotData,
        Self::Unconfirmed,
        Self::EngineDefect,
        Self::ClientRefused,
    ];

    /// The reason's report name (`"natural-end-undecided"`, …).
    #[must_use]
    pub fn name(self) -> String {
        serde_json::to_value(self)
            .ok()
            .and_then(|value| value.as_str().map(str::to_owned))
            .unwrap_or_default()
    }

    /// What to do about a case with this reason, or why nothing can be done, as one sentence;
    /// `None` when the reason is a fact of the definition or of k-rust that the reason's name
    /// already states. A remedy suggests only actions that keep every verdict sound: a bound or
    /// limit, a normal-end or target pattern (the campaign's own statement of what it asks), or
    /// another program or hole range. It never suggests changing the definition's claims (such
    /// as `total`): k-rust trusts a claim it cannot refute, so a false one would turn an
    /// unjudged case into a silent `miss`. Options are named by campaign key, command-line flag
    /// and library field where they differ.
    #[must_use]
    pub fn remedy(self) -> Option<&'static str> {
        Some(match self {
            Self::NaturalEndUndecided => {
                "whether the program finished could not be decided from the <k> cells; state the \
                 finished configuration with a normal-end pattern (campaign key \
                 `normal-end-pattern`, command line `--normal-end`, library \
                 `CaseOptions::normal_end_pattern`)"
            }
            Self::NotCeilFree => {
                "a leaf holds an application of a partial function that no equation evaluates and \
                 whose definedness k-rust does not show (as one an `anywhere` rule of its head \
                 still matches), or map keys not shown apart, so the configuration may denote no \
                 value and this case cannot be judged; a warning names the function when it is \
                 known; choose a program or hole range whose runs do not reach that application"
            }
            Self::MutantEndNotData | Self::BaselineEndNotData => NOT_DATA_REMEDY,
            Self::DefinitionNotConfluent => DEFINITION_NOT_CONFLUENT_REMEDY,
            Self::ReachedEndNotData => REACHED_END_NOT_DATA_REMEDY,
            Self::Clock => {
                "raise or remove the per-case safety limit (campaign key \
                 `safety-limit-seconds` or `no-safety-limit`, command line `--safety-limit` or \
                 `--no-safety-limit`, library `CaseOptions::safety_limit_ms`)"
            }
            Self::Cancelled => {
                "the caller cancelled the run (a watchdog or a stop request), so this case was \
                 not judged; no campaign option changes that"
            }
            Self::WorkBound => {
                "raise the work bound (campaign key `max-work`, command line `--max-work`, \
                 library `CaseOptions::max_work`)"
            }
            Self::DepthBound => {
                "raise the depth bound (campaign key `max-depth`, command line `--max-depth`, \
                 library `CaseOptions::max_depth`)"
            }
            Self::IterationExhaustion | Self::HaltIterationLimit => {
                "raise the simplification iteration bound (campaign key \
                 `max-simplification-iterations`, which has no command-line flag; library \
                 `CaseOptions::max_simplification_iterations`)"
            }
            Self::HaltSmt => HALT_SMT_REMEDY,
            Self::ReachedUndefinedStep => {
                "the target matched the state before an undefined step, which is no end, so \
                 this case cannot be a hit (with run-to-completion it is reached-unfinished, \
                 no hit either); an undefined step is not a target yet"
            }
            Self::ReachedCutPath => "raise the bound or limit that cut the reaching path",
            Self::FiredOffTrace => FIRED_OFF_TRACE_REMEDY,
            Self::AnyStateUnattributed => ANY_STATE_UNATTRIBUTED_REMEDY,
            Self::UndecidedMatch => {
                "the target pattern could not be decided on a leaf (or, at any-state, on a \
                 configuration); a pattern without function applications or values left open by \
                 the definition can be"
            }
            Self::KillWithoutEvidence => {
                "the mutant's ends differ from the baseline's, but its result rests on a value \
                 k-rust chose where the definition leaves it open (such as map or set order), or \
                 contradicts an attribute the mutant asserts of a function or a rule, so its \
                 ends are no evidence and this case cannot be judged; a program or hole range \
                 whose runs avoid both can be"
            }
            Self::ImplementationChosenValue => {
                "the result depends on a value k-rust chose where the definition leaves it open \
                 (such as map or set order), so this case cannot be judged; a program or hole \
                 range whose path does not read such a value can be"
            }
            Self::SmtUnknowns => {
                "raise the solver's time limit per query (campaign key `smt-timeout-ms`, \
                 command line `--smt-timeout`, library \
                 `CaseOptions::backend.smt_timeout_ms`)"
            }
            Self::EndNotComparable(_) => END_NOT_COMPARABLE_REMEDY,
            Self::QueryNotConfirmable(_) => QUERY_NOT_CONFIRMABLE_REMEDY,
            Self::ClientRefused => CLIENT_REFUSED_REMEDY,
            Self::TooDeep => {
                "the case's configuration is nested deeper than the backend's stack holds; \
                 choose a smaller hole range or program, or run krust-fuzz on a thread with a \
                 larger stack (library `CallerIdentity::thread_stack_size`)"
            }
            Self::Panic
            | Self::InternalError
            | Self::InternalHalt
            | Self::StackMappingRefused
            | Self::StackExhausted
            | Self::HaltIndeterminate
            | Self::HaltUnsupportedHook
            | Self::HaltUnsupportedConstruct
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

    /// The reason a halt that is not an end stands for, without its structured cause: an
    /// unsupported halt, a bound, a clock, or a halt no request asks for. `None` for the ends
    /// `stuck` and `trivial` (an undefined step). A `simplification-error` halt is read by its
    /// cause ([`halt_cause`]); one without a cause is k-rust's broken contract, an internal
    /// halt.
    #[must_use]
    pub fn of_halt(halt: HaltReasonOutput) -> Option<Self> {
        use HaltReasonOutput as H;
        Some(match halt {
            H::Indeterminate => Self::HaltIndeterminate,
            H::UnsupportedHook => Self::HaltUnsupportedHook,
            H::SimplificationError => Self::InternalHalt,
            H::Vacuous => Self::HaltVacuous,
            H::WorkBound => Self::WorkBound,
            H::DepthBound | H::BreadthBound => Self::DepthBound,
            H::Timeout => Self::Clock,
            H::Cancelled => Self::Cancelled,
            H::Terminal | H::Branch | H::CutPoint => Self::HaltUnexpected,
            H::Stuck | H::Trivial => return None,
        })
    }

    /// The reason a leaf's halt stands for: its structured cause's ([`LeafReport::halt_cause`])
    /// when it has one, the halt's otherwise ([`Self::of_halt`]).
    #[must_use]
    pub fn of_leaf_halt(leaf: &LeafReport) -> Option<Self> {
        match &leaf.halt_cause {
            Some(HaltCause::Unjudged(reason)) => Some(*reason),
            Some(HaltCause::Internal(_)) => Some(Self::InternalHalt),
            None => Self::of_halt(leaf.halt),
        }
    }

    /// The reason an `Err` result stands for, when it makes the case unjudged.
    #[must_use]
    ///
    /// A refused state and a failed solver prelude make no case unjudged (the first is
    /// `rejected`, the second aborts the campaign); they read as an internal error.
    pub fn of_failure(failure: &CaseFailure) -> Self {
        match &failure.cause {
            FailureCause::Stop(StopCause::StackExhausted(_)) => Self::StackExhausted,
            FailureCause::Stop(StopCause::Deadline(_)) => Self::Clock,
            FailureCause::Stop(StopCause::Cancelled) => Self::Cancelled,
            FailureCause::TooDeep => Self::TooDeep,
            FailureCause::StackMappingRefused => Self::StackMappingRefused,
            FailureCause::Panic(_) => Self::Panic,
            FailureCause::Stop(StopCause::SolverPrelude(_))
            | FailureCause::StateRefused
            | FailureCause::Other => Self::InternalError,
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
    // A clock break is named above (the safety limit) or by the leaves' and the failure's own
    // halts and causes, which tell a deadline from a cancellation.
    reasons.extend(
        result
            .determinism_breaks()
            .into_iter()
            .filter(|fact| *fact != DeterminismBreak::Clock)
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
    match UnjudgedReason::of_leaf_halt(leaf) {
        None => beyond_halt(leaf),
        Some(halt) => Some(beyond_halt(leaf).map_or(halt, |reason| reason.min(halt))),
    }
}

/// What a leaf's structured cause (`ExecutionLeaf::cause`) says of its halt `halt`
/// (FZ-CRASH-CAUSE), read from the typed cause and never from the leaf's text; `detail` (the
/// leaf's text) only words an internal halt's message. `None` when the halt's own reason stands
/// ([`UnjudgedReason::of_halt`]).
///
/// - A `simplification-error` halt: `iteration-limit` and `predicate-iteration-limit` are the
///   option bound ([`UnjudgedReason::HaltIterationLimit`]); `stack-exhausted` a lack of stack;
///   `conflicting-results` and `unsupported-hook` constructs k-rust leaves undecided by design
///   ([`UnjudgedReason::HaltUnsupportedConstruct`]); a solver failure is read as below. A
///   `builtin` failure or an `invalid-builtin-result-symbol` is internal: terms are sort-checked,
///   so a builtin hook meets arguments it does not take, or a result symbol it cannot build,
///   only when a hook was declared at a signature (or in a definition) its builtin does not fit
///   and k-rust did not refuse it, or when k-rust built the application wrong; a `Float` value
///   outside `FLOAT-SYNTAX` (`invalid-float-token`) is not one k-rust admits as a value either.
///   Any other cause, and no cause at all, breaks k-rust's contract for the halt: internal.
/// - An `indeterminate` halt: a macro or alias at run time (`surviving-macro-or-alias`) is
///   internal, since macros and aliases are expanded when the definition is compiled and
///   validation refuses one in the initial state; a solver failure (`smt`, or a `remainder`
///   whose satisfiability is an error) is read as below; any other cause keeps
///   [`UnjudgedReason::HaltIndeterminate`].
/// - A solver failure: no answer for the query ([`UnjudgedReason::HaltSmt`]) when it does not
///   translate, the build has no solver, the solver answered `unknown`, or it rejected a script
///   not blamed on k-rust's translation (the definition's or the user's SMT text may be at
///   fault); internal when the ground truth k-rust passed is inconsistent, the rejected script
///   holds only k-rust's own text (`translationBlamed`), or the model k-rust asked for is
///   missing or unreadable.
#[must_use]
pub fn halt_cause(
    halt: HaltReasonOutput,
    cause: Option<&SearchFailureOutput>,
    detail: Option<&str>,
) -> Option<HaltCause> {
    use SearchFailureOutput as F;
    let internal = |site: String| {
        let message = detail.map_or_else(|| site.clone(), str::to_owned);
        Some(HaltCause::Internal(InternalHalt { site, message }))
    };
    match halt {
        HaltReasonOutput::SimplificationError => {
            let Some(cause) = cause else {
                return internal(cause_site("missing-cause", &["simplification-error"]));
            };
            match cause {
                F::StackExhausted => Some(HaltCause::Unjudged(UnjudgedReason::StackExhausted)),
                F::IterationLimit { .. } | F::PredicateIterationLimit { .. } => {
                    Some(HaltCause::Unjudged(UnjudgedReason::HaltIterationLimit))
                }
                F::ConflictingResults { .. } | F::UnsupportedHook { .. } => Some(
                    HaltCause::Unjudged(UnjudgedReason::HaltUnsupportedConstruct),
                ),
                F::Smt { error, .. } | F::SmtPredicate { error, .. } => {
                    Some(smt_cause(error, detail))
                }
                F::Builtin { error } => internal(builtin_site(error)),
                F::InvalidBuiltinResultSymbol { hook, symbol } => internal(cause_site(
                    INVALID_BUILTIN_RESULT_SYMBOL_SITE,
                    &[hook, symbol],
                )),
                F::SurvivingMacroOrAlias { .. }
                | F::InconsistentGroundTruth { .. }
                | F::Match { .. }
                | F::Instantiation { .. }
                | F::Requires { .. }
                | F::Concreteness { .. }
                | F::Remainder { .. } => internal(cause_site(
                    "unexpected-cause",
                    &["simplification-error", &cause_kind(cause)],
                )),
            }
        }
        HaltReasonOutput::Indeterminate => match cause? {
            F::SurvivingMacroOrAlias { symbol } => {
                internal(cause_site("surviving-macro-or-alias", &[symbol]))
            }
            F::Smt { error, .. }
            | F::SmtPredicate { error, .. }
            | F::Remainder {
                satisfiability: SatisfiabilityOutput::Error { error },
                ..
            } => Some(smt_cause(error, detail)),
            F::StackExhausted
            | F::Builtin { .. }
            | F::ConflictingResults { .. }
            | F::InconsistentGroundTruth { .. }
            | F::IterationLimit { .. }
            | F::PredicateIterationLimit { .. }
            | F::InvalidBuiltinResultSymbol { .. }
            | F::UnsupportedHook { .. }
            | F::Match { .. }
            | F::Instantiation { .. }
            | F::Requires { .. }
            | F::Concreteness { .. }
            | F::Remainder { .. } => None,
        },
        HaltReasonOutput::Stuck
        | HaltReasonOutput::Trivial
        | HaltReasonOutput::Vacuous
        | HaltReasonOutput::Branch
        | HaltReasonOutput::CutPoint
        | HaltReasonOutput::Terminal
        | HaltReasonOutput::DepthBound
        | HaltReasonOutput::BreadthBound
        | HaltReasonOutput::WorkBound
        | HaltReasonOutput::UnsupportedHook
        | HaltReasonOutput::Timeout
        | HaltReasonOutput::Cancelled => None,
    }
}

/// What a solver failure says of a halt ([`halt_cause`]).
fn smt_cause(error: &SmtFailureOutput, detail: Option<&str>) -> HaltCause {
    let site = match error {
        SmtFailureOutput::Translation { .. }
        | SmtFailureOutput::Unavailable
        | SmtFailureOutput::Unknown { .. }
        // An unsatisfiable path condition shows the state empty, not k-rust wrong: a state
        // keeps a condition whose earlier checks the solver left undecided.
        | SmtFailureOutput::InconsistentGroundTruth
        | SmtFailureOutput::MalformedScript {
            translation_blamed: false,
            ..
        } => return HaltCause::Unjudged(UnjudgedReason::HaltSmt),
        SmtFailureOutput::MalformedScript {
            translation_blamed: true,
            ..
        } => "malformed-script",
        SmtFailureOutput::MissingModel => "missing-model",
        SmtFailureOutput::MissingModelValue { .. } => "missing-model-value",
        SmtFailureOutput::InvalidModelValue { .. } => "invalid-model-value",
    };
    let site = cause_site("smt", &[site]);
    let message = detail.map_or_else(|| site.clone(), str::to_owned);
    HaltCause::Internal(InternalHalt { site, message })
}

/// The site of a builtin hook's failure: its kind and the hook it names, when it names one.
fn builtin_site(error: &BuiltinFailureOutput) -> String {
    match error {
        BuiltinFailureOutput::WrongArity { hook, .. } => {
            cause_site(BUILTIN_SITE, &["wrong-arity", hook])
        }
        BuiltinFailureOutput::UnexpectedSort { hook, .. } => {
            cause_site(BUILTIN_SITE, &["unexpected-sort", hook])
        }
        BuiltinFailureOutput::AlternativeSortsDiffer { .. } => {
            cause_site(BUILTIN_SITE, &["alternative-sorts-differ"])
        }
        BuiltinFailureOutput::IncompatibleMapSorts { .. } => {
            cause_site(BUILTIN_SITE, &["incompatible-map-sorts"])
        }
        BuiltinFailureOutput::InvalidFloatToken { hook, .. } => {
            cause_site(BUILTIN_SITE, &["invalid-float-token", hook])
        }
    }
}

/// A search failure's kind, its wire name (`match`, `requires`, ...).
fn cause_kind(cause: &SearchFailureOutput) -> String {
    serde_json::to_value(cause)
        .ok()
        .and_then(|value| match value {
            Value::Object(fields) => fields
                .get("kind")
                .and_then(Value::as_str)
                .map(str::to_owned),
            _ => None,
        })
        .unwrap_or_else(|| "unknown".to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_reason_is_listed_once_in_order_and_no_remedy_suggests_a_claim() {
        assert!(UnjudgedReason::ALL.windows(2).all(|pair| pair[0] < pair[1]));
        for reason in UnjudgedReason::ALL.into_iter().chain(with_conditions()) {
            let Some(remedy) = reason.remedy() else {
                continue;
            };
            // A false claim goes undetected and turns an unjudged case into a silent `miss`
            // (review S1): no remedy may suggest adding one, nor an equation to the definition.
            for forbidden in ["total", "functional", "claim", "add the", "equation for"] {
                assert!(!remedy.contains(forbidden), "{}: {remedy}", reason.name());
            }
            // An option is named by its campaign key and its command-line flag (review S2).
            if remedy.contains("campaign key") {
                assert!(
                    remedy.contains("command line") || remedy.contains("no command-line flag"),
                    "{}: {remedy}",
                    reason.name()
                );
            }
        }
    }

    /// The reasons that name a condition, one per condition each.
    fn with_conditions() -> impl Iterator<Item = UnjudgedReason> {
        ComparableCondition::ALL.into_iter().flat_map(|condition| {
            [
                UnjudgedReason::EndNotComparable(EndNotComparable(condition)),
                UnjudgedReason::QueryNotConfirmable(QueryNotConfirmable(condition)),
            ]
        })
    }

    /// A reason that names a condition reads and writes as `PREFIX:CONDITION`, as a value and as
    /// a report's map key, sorts after every other reason, and no other text reads as one.
    #[test]
    fn a_reason_that_names_a_condition_reads_back_from_its_name() {
        assert!(
            ComparableCondition::ALL
                .windows(2)
                .all(|pair| pair[0] < pair[1])
        );
        for reason in with_conditions() {
            let name = reason.name();
            let (prefix, condition) = name.split_once(':').expect("a prefixed name");
            assert!(
                ["end-not-comparable", "query-not-confirmable"].contains(&prefix),
                "{name}"
            );
            assert!(ComparableCondition::of_name(condition).is_some(), "{name}");
            let back: UnjudgedReason =
                serde_json::from_value(serde_json::json!(name)).expect("reads back");
            assert_eq!(back, reason);
            assert!(UnjudgedReason::ALL.iter().all(|other| *other < reason));
        }
        let counts = std::collections::BTreeMap::from([
            (
                UnjudgedReason::EndNotComparable(EndNotComparable(ComparableCondition::WorkBound)),
                2_u64,
            ),
            (UnjudgedReason::WorkBound, 1),
        ]);
        let text = serde_json::to_string(&counts).expect("serializes");
        assert_eq!(
            text,
            r#"{"work-bound":1,"end-not-comparable:work-bound":2}"#
        );
        let back: std::collections::BTreeMap<UnjudgedReason, u64> =
            serde_json::from_str(&text).expect("reads back");
        assert_eq!(back, counts);
        for refused in [
            "end-not-comparable",
            "end-not-comparable:",
            "end-not-comparable:no-such-condition",
            "query-not-confirmable:work_bound",
            "work-bound:end-not-comparable",
        ] {
            assert!(
                serde_json::from_value::<UnjudgedReason>(serde_json::json!(refused)).is_err(),
                "{refused}"
            );
        }
    }

    #[test]
    fn a_cancellation_is_told_from_a_clock() {
        let leaf = |halt| LeafReport {
            halt,
            halt_cause: None,
            depth: 1,
            state: k_rust::kore::parser::parse_pattern(r"\top{SortK{}}()").expect("parses"),
            unclean: vec![UncleanReason::Halt],
            natural_end: false,
            matches: Vec::new(),
            rewrites: Vec::new(),
            data_end: None,
            diagnostics: Vec::new(),
            term_conjunction: false,
            undefined_rule: None,
            hooks: crate::exec::LeafHooks::default(),
        };
        let result = |halt, safety_limit_hit| CaseResult {
            leaves: vec![leaf(halt)],
            work: 1,
            coverage: None,
            stack_stops: 0,
            smt_unknowns: 0,
            run_allowance_refusals: 0,
            load_records: Vec::new(),
            safety_limit_hit,
            failure: None,
            run_facts_off_leaves: false,
            hooks: crate::exec::RunHooks::default(),
        };
        assert_eq!(
            incomplete(&result(HaltReasonOutput::Cancelled, false)),
            Some(UnjudgedReason::Cancelled)
        );
        // The safety limit cancels through the case's own token.
        assert_eq!(
            incomplete(&result(HaltReasonOutput::Cancelled, true)),
            Some(UnjudgedReason::Clock)
        );
        assert_eq!(
            incomplete(&result(HaltReasonOutput::Timeout, false)),
            Some(UnjudgedReason::Clock)
        );
    }

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
            halt_cause: None,
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
            data_end: None,
            diagnostics: Vec::new(),
            term_conjunction: false,
            undefined_rule: None,
            hooks: crate::exec::LeafHooks::default(),
        };
        assert_eq!(beyond_halt(&leaf), Some(UnjudgedReason::NotCeilFree));
    }
}
