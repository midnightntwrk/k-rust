//! The conditions kink's verdicts rest on, read from k-rust's facts on a case result
//! (P7-ADDENDUM section 4; FZ-COMPARABLE-A and -Q).
//!
//! kink compares a program's ends only when its all-paths run is *comparable*: complete (every
//! leaf an end or an undefined step, no bound, stop or timeout), decided, every leaf's term a
//! value, with no diagnostic of any kind on any leaf (`kink-native` `bridge.rs`, a diagnosed
//! leaf is `BackendLimit`), and no stack stop, chosen value, contradicted claim, allowance
//! refusal or unsupported hook in the run or the definition's load. kink's query confirms a pattern hit only on a match with no
//! diagnostic on the match or on the matching state, whose facts include those of converging
//! paths its search absorbed, on a state with no term-level `\and`.
//!
//! These are facts of the k-rust result the fuzz already holds, so the fuzz reads them here; it
//! does not re-implement kink's own rules (its census exclusions and TV-01, which reach the fuzz
//! through kink itself, FZ-COMPARABLE-B). Each condition is read conservatively:
//! - [`end_conditions`] names every fact of a result that keeps it from being a comparable
//!   all-paths run (conditions P1 to P5, and `smtUnknowns`, P8, which kink reports but the
//!   fuzz's determinism contract refuses). P3, every leaf's term a value, is judged by k-rust's
//!   data judgement ([`super::LeafReport::data_end`], `BackendDefinition::is_data`) on every end
//!   and undefined step: two ends are compared by their terms, which is sound only for terms
//!   that denote themselves and differ from every other value (an irreducible application such
//!   as `g(3)` may equal another term in another theory of `g`). kink judges P3 by its own TV-01,
//!   which reaches the fuzz through kink (FZ-COMPARABLE-B). Its refusals include those of the differential
//!   judge's complete run (`target::differential`), except the fuzz's own judgements of a leaf
//!   (a target's undecided match, an undecided natural end), which are no k-rust facts.
//! - [`query_conditions`] names every diagnostic or run-level fact anywhere in the result, and a
//!   term-level `\and` in the matched state (conditions Q2', Q4', Q5'). It reads the whole run
//!   because kink's search absorbs the facts of converging paths (P7-ADDENDUM review S2), which
//!   no leaf's own facts show. It is necessary for kink's hit, not sufficient: kink's search
//!   stops at its first match (Q6'), which the fuzz cannot decide.
//!
//! The fuzz is stricter than kink in places (a vacuous or solver-refuted leaf kink discards,
//! `smtUnknowns`, every budget copy of a fact), which is safe: a comparable fuzz result is
//! comparable for kink up to kink's own rules, never the other way round.

use k_rust::backend::{BackendDiagnosticOutput, ExecutionLeaf, HaltReasonOutput, StopCause};
use serde::{Deserialize, Serialize};

use super::{CaseResult, FailureCause, LOAD_ALLOWANCE_REFUSAL, LOAD_STACK_STOP, UncleanReason};

/// The kind of one diagnostic a leaf carries ([`super::LeafReport::diagnostics`]): the backend's
/// diagnostic kinds, and the `contradictedTotal` record of an undefined step.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum LeafDiagnostic {
    /// `undecided-condition`: an equation's condition left undecided.
    UndecidedCondition,
    /// `undecided-predicate`.
    UndecidedPredicate,
    /// `simplification-budget-exhausted`.
    SimplificationBudgetExhausted,
    /// `rule-condition-unsimplified`.
    RuleConditionUnsimplified,
    /// `rule-condition-failed`.
    RuleConditionFailed,
    /// `unsupported-hook-unevaluated`.
    UnsupportedHookUnevaluated,
    /// `undefined-initial-instances`.
    UndefinedInitialInstances,
    /// `implementation-chosen-value`.
    ImplementationChosenValue,
    /// `contradicted-claim`.
    ContradictedClaim,
    /// The leaf's `contradictedTotal`: an undefined step through an equation of a `total`
    /// symbol whose result is undefined.
    ContradictedTotal,
}

impl LeafDiagnostic {
    /// The kinds of `leaf`'s diagnostics, sorted, each once.
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(crate) fn of_leaf(leaf: &ExecutionLeaf) -> Vec<Self> {
        let mut kinds: Vec<Self> = leaf
            .diagnostics
            .iter()
            .map(|diagnostic| match diagnostic {
                BackendDiagnosticOutput::UndecidedCondition { .. } => Self::UndecidedCondition,
                BackendDiagnosticOutput::UndecidedPredicate { .. } => Self::UndecidedPredicate,
                BackendDiagnosticOutput::SimplificationBudgetExhausted { .. } => {
                    Self::SimplificationBudgetExhausted
                }
                BackendDiagnosticOutput::RuleConditionUnsimplified { .. } => {
                    Self::RuleConditionUnsimplified
                }
                BackendDiagnosticOutput::RuleConditionFailed { .. } => Self::RuleConditionFailed,
                BackendDiagnosticOutput::UnsupportedHookUnevaluated { .. } => {
                    Self::UnsupportedHookUnevaluated
                }
                BackendDiagnosticOutput::UndefinedInitialInstances { .. } => {
                    Self::UndefinedInitialInstances
                }
                BackendDiagnosticOutput::ImplementationChosenValue { .. } => {
                    Self::ImplementationChosenValue
                }
                BackendDiagnosticOutput::ContradictedClaim(_) => Self::ContradictedClaim,
            })
            .collect();
        if leaf.contradicted_total.is_some() {
            kinds.push(Self::ContradictedTotal);
        }
        kinds.sort_unstable();
        kinds.dedup();
        kinds
    }

    /// The condition this diagnostic fails.
    fn condition(self) -> ComparableCondition {
        use ComparableCondition as C;
        match self {
            Self::UndecidedCondition => C::UndecidedCondition,
            Self::UndecidedPredicate => C::UndecidedPredicate,
            Self::SimplificationBudgetExhausted => C::SimplificationBudgetExhausted,
            Self::RuleConditionUnsimplified => C::RuleConditionUnsimplified,
            Self::RuleConditionFailed => C::RuleConditionFailed,
            Self::UnsupportedHookUnevaluated => C::UnsupportedHookUnevaluated,
            Self::UndefinedInitialInstances => C::UndefinedInitialInstances,
            Self::ImplementationChosenValue => C::ImplementationChosenValue,
            Self::ContradictedClaim | Self::ContradictedTotal => C::ContradictedClaim,
        }
    }
}

/// One condition kink's comparability or query hit rests on that a case result fails
/// (module documentation). Its report name is the kebab-case variant name; the declaration
/// order, from the run as a whole through a leaf's state and diagnostics to the run's and the
/// load's lists, is the order in which the first failing condition is chosen.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ComparableCondition {
    /// P1: the run answered `Err` for a reason other than a clock, a lack of stack or a crash.
    RunFailed,
    /// P1: the run or its judgement crashed (a panic or an internal error of k-rust or of the
    /// engine, FZ-CRASH): the report's `crashes` hold it.
    Crash,
    /// P1: a clock or a cancellation stopped the run or a path (the per-case safety limit, a
    /// step deadline, a cancelled token).
    Clock,
    /// P1: a path stopped at `max-work`. A run with no `work-bound` leaf is the unbudgeted
    /// run's result (the prefix contract), so the budget itself is no condition.
    WorkBound,
    /// P1: a path stopped at `max-depth` or the breadth bound.
    DepthBound,
    /// P1: a leaf halted neither `stuck` nor at an undefined step (`trivial`): `indeterminate`,
    /// `unsupported-hook`, `simplification-error`, `vacuous`, `terminal`, ...; or the run has no
    /// leaf.
    Halt,
    /// P2: a leaf has constraints or variables, so it is not ground and decided.
    UndecidedState,
    /// P2: a leaf's term is not shown to exist (k-rust's `ground_defined`): it may denote no
    /// value.
    NotCeilFree,
    /// P2: a leaf could not be internalized in its definition.
    InternalizationFailed,
    /// Q4': the matched state holds a term-level `\and`, which kink's query refuses even with
    /// equal sides.
    TermConjunction,
    /// P1: a leaf carries an `undefined-initial-instances` diagnostic.
    UndefinedInitialInstances,
    /// P1: a leaf carries a `simplification-budget-exhausted` diagnostic.
    SimplificationBudgetExhausted,
    /// P1: a leaf carries a `rule-condition-unsimplified` diagnostic.
    RuleConditionUnsimplified,
    /// P1: a leaf carries a `rule-condition-failed` diagnostic.
    RuleConditionFailed,
    /// P1: a leaf carries an `undecided-condition` diagnostic, which the fuzz's clean-leaf rule
    /// ignores (a total application it leaves unevaluated is ceil-free) and kink does not.
    UndecidedCondition,
    /// P1: a leaf carries an `undecided-predicate` diagnostic, likewise.
    UndecidedPredicate,
    /// P1: a leaf carries an `unsupported-hook-unevaluated` diagnostic, likewise.
    UnsupportedHookUnevaluated,
    /// P3: a decided end or undefined step whose term is not data
    /// ([`super::LeafReport::data_end`]): it may not denote itself, or may equal another value,
    /// so it cannot be compared by its term. It comes after the diagnostics, which often say why
    /// an application stayed unevaluated. Every end of a definition whose full critical-pair
    /// check reports a finding is not data.
    EndNotData,
    /// P8: the solver answered `unknown` in the run or in a leaf's matching. Not a kink
    /// condition; the fuzz's determinism contract refuses it.
    SmtUnknowns,
    /// P4: the run, or the definition's load, stopped work for lack of stack.
    StackStops,
    /// P5: a leaf carries an implementation-chosen value.
    ImplementationChosenValue,
    /// P5: a leaf carries a contradicted claim, or the definition's load observed one.
    ContradictedClaim,
    /// P5: the run noted an implementation-chosen value or a contradicted claim that no leaf
    /// carries.
    RunFactOffLeaves,
    /// P5: the memory allowance refused a result in the run or in the definition's load.
    AllowanceRefusal,
    /// P5: the run or the definition's load left an application unevaluated as an unsupported
    /// hook.
    UnsupportedHook,
}

impl ComparableCondition {
    /// Every condition, in declaration order.
    pub const ALL: [Self; 25] = [
        Self::RunFailed,
        Self::Crash,
        Self::Clock,
        Self::WorkBound,
        Self::DepthBound,
        Self::Halt,
        Self::UndecidedState,
        Self::NotCeilFree,
        Self::InternalizationFailed,
        Self::TermConjunction,
        Self::UndefinedInitialInstances,
        Self::SimplificationBudgetExhausted,
        Self::RuleConditionUnsimplified,
        Self::RuleConditionFailed,
        Self::UndecidedCondition,
        Self::UndecidedPredicate,
        Self::UnsupportedHookUnevaluated,
        Self::EndNotData,
        Self::SmtUnknowns,
        Self::StackStops,
        Self::ImplementationChosenValue,
        Self::ContradictedClaim,
        Self::RunFactOffLeaves,
        Self::AllowanceRefusal,
        Self::UnsupportedHook,
    ];

    /// The condition's report name (`"work-bound"`, …).
    #[must_use]
    pub fn name(self) -> String {
        serde_json::to_value(self)
            .ok()
            .and_then(|value| value.as_str().map(str::to_owned))
            .unwrap_or_default()
    }

    /// The condition named `name`, if any.
    #[must_use]
    pub fn of_name(name: &str) -> Option<Self> {
        serde_json::from_value(serde_json::Value::String(name.to_owned())).ok()
    }

    /// Whether this condition is a fact that puts its run outside the determinism contract
    /// (ARCHITECTURE 5.4; [`CaseResult::determinism_breaks`]): a clock, a solver `unknown`, a stop
    /// for lack of stack or an allowance refusal. [`end_conditions`] names one of these exactly
    /// when its result has a determinism break, so a judgement that names none is a function of
    /// the case's input and repeats on every run of it, and one that names one may differ on
    /// another run, in the conditions it names as in whether it holds.
    #[must_use]
    pub fn breaks_determinism(self) -> bool {
        matches!(
            self,
            Self::Clock | Self::SmtUnknowns | Self::StackStops | Self::AllowanceRefusal
        )
    }
}

/// Every condition of a comparable all-paths run (P1 to P5 and P8; module documentation) that
/// `result` fails, sorted, each once; empty when `result` is a comparable run of every path.
/// `result` must be an all-paths run without terminal rules for the answer to be about the
/// program: a one-path run or one stopped by the target's rule is not the program's run. P3 reads
/// each decided end's and undefined step's [`super::LeafReport::data_end`], so `result` must
/// carry the data judgement; a decided end without one counts as not data.
#[must_use]
pub fn end_conditions(result: &CaseResult) -> Vec<ComparableCondition> {
    use ComparableCondition as C;
    let mut conditions = Vec::new();
    if let Some(failure) = &result.failure {
        conditions.push(match &failure.cause {
            FailureCause::Stop(StopCause::Cancelled | StopCause::Deadline(_)) => C::Clock,
            FailureCause::Stop(StopCause::StackExhausted(_))
            | FailureCause::StackMappingRefused => C::StackStops,
            FailureCause::Panic(_) | FailureCause::Other => C::Crash,
            FailureCause::Stop(StopCause::SolverPrelude(_))
            | FailureCause::StateRefused
            | FailureCause::TooDeep => C::RunFailed,
        });
    } else if result.leaves.is_empty() {
        conditions.push(C::Halt);
    }
    if result.safety_limit_hit {
        conditions.push(C::Clock);
    }
    for leaf in &result.leaves {
        conditions.extend(halt_condition(leaf.halt));
        conditions.extend(leaf.unclean.iter().filter_map(unclean_condition));
        conditions.extend(leaf.diagnostics.iter().map(|kind| kind.condition()));
        if not_data(leaf) {
            conditions.push(C::EndNotData);
        }
    }
    conditions.extend(run_conditions(result));
    for record in &result.load_records {
        conditions.push(match record.kind.as_str() {
            LOAD_STACK_STOP => C::StackStops,
            LOAD_ALLOWANCE_REFUSAL => C::AllowanceRefusal,
            "unsupported-hook" => C::UnsupportedHook,
            // `contradicted-claim`, and any record kind added later: a fact of the load, which
            // kink's exclusions read (D-6).
            _ => C::ContradictedClaim,
        });
    }
    conditions.sort_unstable();
    conditions.dedup();
    conditions
}

/// Every condition of a confirmable query hit (Q2', Q4', Q5'; module documentation) that
/// `result` fails, read over the whole run, sorted, each once: a diagnostic of any kind on any
/// leaf, a fact of the run's lists, a stop for lack of stack in the run or the load, and
/// [`ComparableCondition::TermConjunction`] when `term_conjunction` says that the matched state
/// holds a term-level `\and`. Empty when nothing refuses the hit; that is necessary for kink's
/// hit, not sufficient (Q6').
#[must_use]
pub fn query_conditions(result: &CaseResult, term_conjunction: bool) -> Vec<ComparableCondition> {
    use ComparableCondition as C;
    let mut conditions = Vec::new();
    if term_conjunction {
        conditions.push(C::TermConjunction);
    }
    for leaf in &result.leaves {
        conditions.extend(leaf.diagnostics.iter().map(|kind| kind.condition()));
        conditions.extend(leaf.unclean.iter().filter_map(|reason| {
            unclean_condition(reason).filter(|condition| {
                matches!(
                    condition,
                    C::SmtUnknowns
                        | C::StackStops
                        | C::ImplementationChosenValue
                        | C::ContradictedClaim
                        | C::AllowanceRefusal
                        | C::UnsupportedHook
                )
            })
        }));
    }
    conditions.extend(run_conditions(result));
    if result
        .load_records
        .iter()
        .any(|record| record.kind == LOAD_STACK_STOP)
    {
        conditions.push(C::StackStops);
    }
    conditions.sort_unstable();
    conditions.dedup();
    conditions
}

/// P3 on `leaf`: it is an end (`stuck`) or an undefined step (`trivial`) whose state was
/// decided (it internalized, with no constraint and no variable; otherwise P2 names it) and whose
/// term is not shown to be data.
fn not_data(leaf: &super::LeafReport) -> bool {
    matches!(
        leaf.halt,
        HaltReasonOutput::Stuck | HaltReasonOutput::Trivial
    ) && !leaf.unclean.iter().any(|reason| {
        matches!(
            reason,
            UncleanReason::Undecided | UncleanReason::Internalization(_)
        )
    }) && leaf.data_end != Some(true)
}

/// The conditions a leaf's halt fails: none for an end (`stuck`) or an undefined step
/// (`trivial`).
fn halt_condition(halt: HaltReasonOutput) -> Option<ComparableCondition> {
    use ComparableCondition as C;
    use HaltReasonOutput as H;
    Some(match halt {
        H::Stuck | H::Trivial => return None,
        H::WorkBound => C::WorkBound,
        H::DepthBound | H::BreadthBound => C::DepthBound,
        H::Timeout | H::Cancelled => C::Clock,
        H::Indeterminate
        | H::UnsupportedHook
        | H::SimplificationError
        | H::Vacuous
        | H::Terminal
        | H::Branch
        | H::CutPoint => C::Halt,
    })
}

/// The condition a leaf's unclean reason stands for; `None` for its halt (read from the halt
/// itself) and for the fuzz's own judgements of the leaf (a target's undecided match, an
/// undecided natural end), which are no k-rust facts.
fn unclean_condition(reason: &UncleanReason) -> Option<ComparableCondition> {
    use ComparableCondition as C;
    Some(match reason {
        UncleanReason::Halt
        | UncleanReason::UndecidedMatch
        | UncleanReason::NaturalEndUndecided => {
            return None;
        }
        UncleanReason::Undecided => C::UndecidedState,
        UncleanReason::NotCeilFree(_) => C::NotCeilFree,
        UncleanReason::Internalization(_) => C::InternalizationFailed,
        UncleanReason::ImplementationChosenValue => C::ImplementationChosenValue,
        UncleanReason::ContradictedClaim => C::ContradictedClaim,
        // The diagnostics that give these reasons are named by their own kinds.
        UncleanReason::IterationExhaustion => C::SimplificationBudgetExhausted,
        UncleanReason::SimplificationFailure => C::RuleConditionFailed,
        UncleanReason::StackStops => C::StackStops,
        UncleanReason::SmtUnknowns => C::SmtUnknowns,
        UncleanReason::AllowanceRefusal => C::AllowanceRefusal,
        UncleanReason::UnsupportedHook => C::UnsupportedHook,
    })
}

/// The conditions the run's own counters and lists fail, and the determinism breaks of the
/// load that the counters do not show.
fn run_conditions(result: &CaseResult) -> Vec<ComparableCondition> {
    use ComparableCondition as C;
    let mut conditions = Vec::new();
    if result.run_facts_off_leaves {
        conditions.push(C::RunFactOffLeaves);
    }
    if result.stack_stops > 0 {
        conditions.push(C::StackStops);
    }
    if result.smt_unknowns > 0 {
        conditions.push(C::SmtUnknowns);
    }
    if result.run_allowance_refusals > 0 {
        conditions.push(C::AllowanceRefusal);
    }
    conditions
}

#[cfg(test)]
mod tests {
    use k_rust::backend::HaltReasonOutput;

    use super::{ComparableCondition as C, LeafDiagnostic as D, *};
    use crate::{
        exec::{CaseFailure, LeafReport},
        report::LoadRecord,
    };

    fn leaf(halt: HaltReasonOutput, unclean: Vec<UncleanReason>) -> LeafReport {
        LeafReport {
            halt,
            halt_cause: None,
            depth: 1,
            state: k_rust::kore::parser::parse_pattern(r"\top{SortK{}}()").expect("parses"),
            unclean,
            natural_end: false,
            matches: vec![false],
            rewrites: Vec::new(),
            data_end: Some(true),
            diagnostics: Vec::new(),
            term_conjunction: false,
            undefined_rule: None,
        }
    }

    fn end() -> LeafReport {
        leaf(HaltReasonOutput::Stuck, Vec::new())
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
    fn a_complete_run_of_clean_ends_and_undefined_steps_is_comparable() {
        let undefined = leaf(HaltReasonOutput::Trivial, vec![UncleanReason::Halt]);
        let run = result(vec![end(), undefined]);
        assert_eq!(end_conditions(&run), []);
        assert_eq!(query_conditions(&run, false), []);
        // The fuzz's own judgements of a leaf are no k-rust facts.
        let judged = leaf(
            HaltReasonOutput::Stuck,
            vec![
                UncleanReason::UndecidedMatch,
                UncleanReason::NaturalEndUndecided,
            ],
        );
        assert_eq!(end_conditions(&result(vec![judged])), []);
    }

    /// P1 includes "no diagnostic of any kind on any leaf" (P7-ADDENDUM review S4): the kinds the
    /// clean-leaf rule ignores refuse comparability, and every kind refuses a query hit.
    #[test]
    fn a_diagnostic_of_any_kind_on_any_leaf_refuses_both() {
        for (kind, condition) in [
            (D::UndecidedCondition, C::UndecidedCondition),
            (D::UndecidedPredicate, C::UndecidedPredicate),
            (D::UnsupportedHookUnevaluated, C::UnsupportedHookUnevaluated),
            (
                D::SimplificationBudgetExhausted,
                C::SimplificationBudgetExhausted,
            ),
            (D::RuleConditionUnsimplified, C::RuleConditionUnsimplified),
            (D::RuleConditionFailed, C::RuleConditionFailed),
            (D::UndefinedInitialInstances, C::UndefinedInitialInstances),
            (D::ImplementationChosenValue, C::ImplementationChosenValue),
            (D::ContradictedClaim, C::ContradictedClaim),
            (D::ContradictedTotal, C::ContradictedClaim),
        ] {
            let mut diagnosed = end();
            diagnosed.diagnostics = vec![kind];
            // On a sibling of a clean end: both readings are whole-run.
            let run = result(vec![end(), diagnosed]);
            assert_eq!(end_conditions(&run), [condition], "{kind:?}");
            assert_eq!(query_conditions(&run, false), [condition], "{kind:?}");
        }
    }

    #[test]
    fn every_halt_but_an_end_or_an_undefined_step_refuses_comparability() {
        use HaltReasonOutput as H;
        for (halt, condition) in [
            (H::WorkBound, C::WorkBound),
            (H::DepthBound, C::DepthBound),
            (H::BreadthBound, C::DepthBound),
            (H::Timeout, C::Clock),
            (H::Cancelled, C::Clock),
            (H::Indeterminate, C::Halt),
            (H::Vacuous, C::Halt),
            (H::Terminal, C::Halt),
            (H::UnsupportedHook, C::Halt),
            (H::SimplificationError, C::Halt),
        ] {
            let run = result(vec![end(), leaf(halt, vec![UncleanReason::Halt])]);
            assert_eq!(end_conditions(&run), [condition], "{halt:?}");
            // A query hit is not about the run's completeness.
            assert_eq!(query_conditions(&run, false), [], "{halt:?}");
        }
        assert_eq!(end_conditions(&result(Vec::new())), [C::Halt]);
        let failed = CaseResult {
            failure: Some(CaseFailure::other("no".to_owned())),
            ..result(Vec::new())
        };
        assert_eq!(end_conditions(&failed), [C::Crash]);
        let too_deep = CaseResult {
            failure: Some(CaseFailure::new(
                "deep",
                FailureCause::TooDeep,
                crate::report::CrashStage::Execute,
            )),
            ..result(Vec::new())
        };
        assert_eq!(end_conditions(&too_deep), [C::RunFailed]);
    }

    /// The load's records refuse comparability (kink D-6), though they taint no fuzz leaf (T-5);
    /// a query hit reads the load's stop for lack of stack only (Q5').
    #[test]
    fn the_load_refuses_comparability_and_its_stack_stop_a_query_hit() {
        for (kind, condition) in [
            ("contradicted-claim", C::ContradictedClaim),
            (LOAD_ALLOWANCE_REFUSAL, C::AllowanceRefusal),
            ("unsupported-hook", C::UnsupportedHook),
            (LOAD_STACK_STOP, C::StackStops),
        ] {
            let run = CaseResult {
                load_records: vec![LoadRecord {
                    kind: kind.to_owned(),
                    detail: String::new(),
                }],
                ..result(vec![end()])
            };
            assert_eq!(end_conditions(&run), [condition], "{kind}");
            let query: &[C] = if kind == LOAD_STACK_STOP {
                &[C::StackStops]
            } else {
                &[]
            };
            assert_eq!(query_conditions(&run, false), query, "{kind}");
        }
    }

    #[test]
    fn the_run_s_lists_and_leaf_states_are_read() {
        let off = CaseResult {
            run_facts_off_leaves: true,
            ..result(vec![end()])
        };
        assert_eq!(end_conditions(&off), [C::RunFactOffLeaves]);
        assert_eq!(query_conditions(&off, false), [C::RunFactOffLeaves]);
        let counted = CaseResult {
            stack_stops: 1,
            smt_unknowns: 1,
            run_allowance_refusals: 1,
            ..result(vec![end()])
        };
        assert_eq!(
            end_conditions(&counted),
            [C::SmtUnknowns, C::StackStops, C::AllowanceRefusal]
        );
        let undecided = leaf(
            HaltReasonOutput::Stuck,
            vec![
                UncleanReason::Undecided,
                UncleanReason::NotCeilFree(None),
                UncleanReason::Internalization("x".to_owned()),
            ],
        );
        let run = result(vec![end(), undecided]);
        assert_eq!(
            end_conditions(&run),
            [C::UndecidedState, C::NotCeilFree, C::InternalizationFailed]
        );
        // A sibling's undecided state is no diagnostic: the query reads only the matched state's.
        assert_eq!(query_conditions(&run, false), []);
        assert_eq!(query_conditions(&run, true), [C::TermConjunction]);
    }

    /// P3 (INT9 review S3): an end or an undefined step is compared by its term, so its term
    /// must be data; a leaf whose state was not decided is named by P2 alone, and a leaf cut by a
    /// bound by its halt.
    #[test]
    fn an_end_or_undefined_step_that_is_not_data_refuses_comparability() {
        for halt in [HaltReasonOutput::Stuck, HaltReasonOutput::Trivial] {
            for data_end in [Some(false), None] {
                let mut value = leaf(halt, Vec::new());
                value.data_end = data_end;
                let run = result(vec![end(), value]);
                assert_eq!(
                    end_conditions(&run),
                    [C::EndNotData],
                    "{halt:?} {data_end:?}"
                );
                // kink's query compares no ends.
                assert_eq!(query_conditions(&run, false), [], "{halt:?} {data_end:?}");
            }
        }
        let mut undecided = leaf(HaltReasonOutput::Stuck, vec![UncleanReason::Undecided]);
        undecided.data_end = None;
        assert_eq!(
            end_conditions(&result(vec![undecided])),
            [C::UndecidedState]
        );
        let mut cut = leaf(HaltReasonOutput::WorkBound, vec![UncleanReason::Halt]);
        cut.data_end = None;
        assert_eq!(end_conditions(&result(vec![cut])), [C::WorkBound]);
        // An end that is not data because an application stayed unevaluated: the diagnostic that
        // says why comes first.
        let mut diagnosed = leaf(HaltReasonOutput::Stuck, Vec::new());
        diagnosed.data_end = Some(false);
        diagnosed.diagnostics = vec![D::UndecidedCondition];
        assert_eq!(
            end_conditions(&result(vec![diagnosed])),
            [C::UndecidedCondition, C::EndNotData]
        );
    }

    /// A judgement names a condition that breaks determinism exactly when its run is outside the
    /// determinism contract, so a judgement that names none repeats (INT9 review S2).
    #[test]
    fn a_judgement_names_a_determinism_break_exactly_when_its_run_has_one() {
        use HaltReasonOutput as H;
        let record = |kind: &str| LoadRecord {
            kind: kind.to_owned(),
            detail: String::new(),
        };
        let runs = [
            result(vec![end()]),
            result(vec![end(), leaf(H::Timeout, vec![UncleanReason::Halt])]),
            result(vec![leaf(H::Cancelled, vec![UncleanReason::Halt])]),
            result(vec![leaf(H::WorkBound, vec![UncleanReason::Halt])]),
            CaseResult {
                safety_limit_hit: true,
                ..result(vec![end()])
            },
            CaseResult {
                smt_unknowns: 2,
                ..result(vec![end()])
            },
            CaseResult {
                stack_stops: 1,
                ..result(vec![end()])
            },
            CaseResult {
                run_allowance_refusals: 1,
                ..result(vec![end()])
            },
            CaseResult {
                load_records: vec![record(LOAD_STACK_STOP)],
                ..result(vec![end()])
            },
            CaseResult {
                load_records: vec![record(LOAD_ALLOWANCE_REFUSAL)],
                ..result(vec![end()])
            },
            CaseResult {
                load_records: vec![record("contradicted-claim"), record("unsupported-hook")],
                ..result(vec![end()])
            },
            CaseResult {
                failure: Some(CaseFailure::other("no".to_owned())),
                ..result(Vec::new())
            },
        ];
        for run in runs {
            assert_eq!(
                end_conditions(&run)
                    .iter()
                    .any(|condition| condition.breaks_determinism()),
                !run.determinism_breaks().is_empty(),
                "{run:?}"
            );
        }
    }

    #[test]
    fn condition_names_read_back() {
        for condition in C::ALL {
            assert_eq!(C::of_name(&condition.name()), Some(condition));
        }
        assert_eq!(C::WorkBound.name(), "work-bound");
        assert_eq!(C::UndecidedCondition.name(), "undecided-condition");
        assert_eq!(C::of_name("work_bound"), None);
    }
}
