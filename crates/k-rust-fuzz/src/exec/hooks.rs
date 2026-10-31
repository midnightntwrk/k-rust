//! The hooks behind an unjudged reason or a failed comparable condition (UNNAMED-HOOK).
//!
//! A reason such as `implementation-chosen-value` or `end-not-comparable:unsupported-hook` says
//! what kind of fact kept a case from a verdict, but a reader can act on it only knowing where
//! the fact comes from: which hook read the value the definition leaves open, or which hook
//! k-rust left unevaluated. k-rust's records name that hook in a typed field (an
//! `implementation-chosen-value` mark's `hook` and `class`, an unsupported hook's `hook` in a
//! halt's cause, a diagnostic, or the run's and the load's `unsupportedHooks`), so the hook is
//! read from those fields, never from a record's text.
//!
//! A leaf keeps the hooks of its own facts ([`LeafHooks`]) and a run those of its facts that lie
//! on no leaf ([`RunHooks`]); [`reason_hooks`] and [`condition_hooks`] then give the hooks of the
//! facts a reason or condition reads, over the run that reason or condition was read from. Each
//! is a set, so the hooks a report names are a function of the run, not of the order in which
//! the backend listed its records.

use std::collections::BTreeSet;

use k_rust::backend::{
    BackendDiagnosticOutput, ExecutionLeaf, ExecutionResult, ObservedInOutput, SearchFailureOutput,
    StateMatchOutput,
};

use super::{CaseResult, ComparableCondition, HaltCause, LeafReport, UnjudgedReason};
use crate::report::ReasonHook;

/// The hooks a leaf's own facts name (UNNAMED-HOOK). Each list is sorted and holds each hook
/// once.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LeafHooks {
    /// The hook of the leaf's halt cause when the cause is an unsupported hook
    /// (`SearchFailureOutput::UnsupportedHook`): an `unsupported-hook` halt, or a
    /// `simplification-error` halt that met a hook k-rust does not evaluate.
    pub halt: Option<String>,
    /// The hooks of the leaf's `unsupported-hook-unevaluated` diagnostics.
    pub unevaluated: Vec<String>,
    /// The hook and class of each of the leaf's `implementation-chosen-value` marks.
    pub chosen: Vec<ReasonHook>,
}

impl LeafHooks {
    /// The hooks `leaf`'s cause and diagnostics name.
    #[must_use]
    pub fn of_leaf(leaf: &ExecutionLeaf) -> Self {
        let halt = match &leaf.cause {
            Some(SearchFailureOutput::UnsupportedHook { hook, .. }) => Some(hook.clone()),
            _ => None,
        };
        let mut unevaluated = BTreeSet::new();
        let mut chosen = BTreeSet::new();
        for diagnostic in &leaf.diagnostics {
            match diagnostic {
                BackendDiagnosticOutput::UnsupportedHookUnevaluated { hook, .. } => {
                    unevaluated.insert(hook.clone());
                }
                BackendDiagnosticOutput::ImplementationChosenValue { hook, class } => {
                    chosen.insert(ReasonHook::chosen(hook, class));
                }
                _ => {}
            }
        }
        Self {
            halt,
            unevaluated: unevaluated.into_iter().collect(),
            chosen: chosen.into_iter().collect(),
        }
    }
}

/// The hooks a run's own facts name that no leaf's facts carry (UNNAMED-HOOK). Each list is
/// sorted and holds each hook once.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RunHooks {
    /// The hooks of the applications the run left unevaluated as unsupported hooks
    /// (`ExecutionResult::unsupported_hooks`, `observedIn: run`), the fact of
    /// [`super::UncleanReason::UnsupportedHook`].
    pub unsupported: Vec<String>,
    /// The same, observed in the definition's load (`observedIn: load`), a load record.
    pub load_unsupported: Vec<String>,
    /// The implementation-chosen values the run read that no leaf's marks carry
    /// (`ExecutionResult::implementation_chosen_values`), the chosen half of
    /// [`CaseResult::run_facts_off_leaves`].
    pub chosen_off_leaves: Vec<ReasonHook>,
    /// For a run that matched its states (`at: any-state`), the implementation-chosen values on
    /// the prefix of its first reach that was not clean, when the case's judgement read that
    /// reach (no clean reach, inside the determinism contract; `target::any_state`), where it
    /// is a reason of the case beside its leaves'; empty otherwise. Filled by the any-state
    /// judgement, not by the run.
    pub chosen_on_reach: Vec<ReasonHook>,
}

impl RunHooks {
    /// The hooks `result`'s own lists name.
    #[must_use]
    pub fn of_result(result: &ExecutionResult) -> Self {
        let unsupported = |observed: ObservedInOutput| -> Vec<String> {
            result
                .unsupported_hooks
                .iter()
                .filter(|hook| hook.observed_in == observed)
                .map(|hook| hook.hook.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        };
        let chosen_off_leaves = result
            .implementation_chosen_values
            .iter()
            .filter(|value| {
                !result
                    .leaves
                    .iter()
                    .flat_map(|leaf| &leaf.diagnostics)
                    .any(|diagnostic| {
                        matches!(
                            diagnostic,
                            BackendDiagnosticOutput::ImplementationChosenValue { hook, class }
                                if *hook == value.hook && *class == value.class
                        )
                    })
            })
            .map(|value| ReasonHook::chosen(&value.hook, &value.class))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        Self {
            unsupported: unsupported(ObservedInOutput::Run),
            load_unsupported: unsupported(ObservedInOutput::Load),
            chosen_off_leaves,
            chosen_on_reach: Vec::new(),
        }
    }

    /// The implementation-chosen values on `reach`'s prefix, for [`Self::chosen_on_reach`].
    #[must_use]
    pub fn chosen_on(reach: &StateMatchOutput) -> Vec<ReasonHook> {
        reach
            .diagnostics
            .iter()
            .filter_map(|diagnostic| match diagnostic {
                BackendDiagnosticOutput::ImplementationChosenValue { hook, class } => {
                    Some(ReasonHook::chosen(hook, class))
                }
                _ => None,
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
}

/// The hooks the facts behind `reason` name in `result`, the run the reason was read from
/// (for a differential case the side it names; for `end-not-comparable:*` the run of every path
/// that was judged). Empty for a reason whose facts name no hook.
#[must_use]
pub fn reason_hooks(result: &CaseResult, reason: UnjudgedReason) -> BTreeSet<ReasonHook> {
    let mut hooks = BTreeSet::new();
    match reason {
        UnjudgedReason::HaltUnsupportedHook | UnjudgedReason::HaltUnsupportedConstruct => {
            // Only the leaves whose halt stands for this reason: a `simplification-error` halt
            // over conflicting equations names no hook, and an `unsupported-hook` halt is the
            // other reason.
            hooks.extend(
                result
                    .leaves
                    .iter()
                    .filter(|leaf| UnjudgedReason::of_leaf_halt(leaf) == Some(reason))
                    .filter_map(halt_hook),
            );
        }
        UnjudgedReason::UnsupportedHook => {
            hooks.extend(
                result
                    .hooks
                    .unsupported
                    .iter()
                    .map(|hook| ReasonHook::unsupported(hook)),
            );
        }
        UnjudgedReason::ImplementationChosenValue => {
            hooks.extend(leaf_chosen(result));
            hooks.extend(result.hooks.chosen_on_reach.iter().cloned());
        }
        UnjudgedReason::RunFactOffLeaves => {
            hooks.extend(result.hooks.chosen_off_leaves.iter().cloned());
        }
        // Condition 3 on the mutant: a chosen value on a leaf, or one the run read off them.
        UnjudgedReason::KillWithoutEvidence => {
            hooks.extend(leaf_chosen(result));
            hooks.extend(result.hooks.chosen_off_leaves.iter().cloned());
        }
        UnjudgedReason::EndNotComparable(condition) => {
            hooks = condition_hooks(result, condition.0);
        }
        UnjudgedReason::QueryNotConfirmable(condition) => {
            hooks = query_condition_hooks(result, condition.0);
        }
        _ => {}
    }
    hooks
}

/// The hooks the facts behind the comparable `condition` of an all-paths end judgement name in
/// `result` (`crate::exec::comparable::end_conditions`): `unsupported-hook` reads the run's and
/// the load's records. Empty for a condition whose facts name no hook.
#[must_use]
pub fn condition_hooks(
    result: &CaseResult,
    condition: ComparableCondition,
) -> BTreeSet<ReasonHook> {
    hooks_of_condition(result, condition, true)
}

/// The hooks the facts behind the comparable `condition` of a query judgement name in `result`
/// (`crate::exec::comparable::query_conditions`): as [`condition_hooks`], except that
/// `unsupported-hook` reads the run's records only, since the query condition reads no load
/// record of an unsupported hook.
#[must_use]
pub fn query_condition_hooks(
    result: &CaseResult,
    condition: ComparableCondition,
) -> BTreeSet<ReasonHook> {
    hooks_of_condition(result, condition, false)
}

/// [`condition_hooks`] (`load` true) or [`query_condition_hooks`] (`load` false).
fn hooks_of_condition(
    result: &CaseResult,
    condition: ComparableCondition,
    load: bool,
) -> BTreeSet<ReasonHook> {
    let mut hooks = BTreeSet::new();
    match condition {
        ComparableCondition::Halt => hooks.extend(result.leaves.iter().filter_map(halt_hook)),
        ComparableCondition::UnsupportedHookUnevaluated => hooks.extend(
            result
                .leaves
                .iter()
                .flat_map(|leaf| &leaf.hooks.unevaluated)
                .map(|hook| ReasonHook::unsupported(hook)),
        ),
        ComparableCondition::ImplementationChosenValue => hooks.extend(leaf_chosen(result)),
        ComparableCondition::RunFactOffLeaves => {
            hooks.extend(result.hooks.chosen_off_leaves.iter().cloned());
        }
        ComparableCondition::UnsupportedHook => hooks.extend(
            result
                .hooks
                .unsupported
                .iter()
                .chain(result.hooks.load_unsupported.iter().filter(|_| load))
                .map(|hook| ReasonHook::unsupported(hook)),
        ),
        _ => {}
    }
    hooks
}

/// The unsupported hook `leaf` halted on, when its halt's cause names one.
fn halt_hook(leaf: &LeafReport) -> Option<ReasonHook> {
    // An internal halt is a crash, named by its site; it is never an unsupported hook.
    if matches!(leaf.halt_cause, Some(HaltCause::Internal(_))) {
        return None;
    }
    leaf.hooks.halt.as_deref().map(ReasonHook::unsupported)
}

/// The hooks of every leaf's implementation-chosen-value marks.
fn leaf_chosen(result: &CaseResult) -> impl Iterator<Item = ReasonHook> + '_ {
    result
        .leaves
        .iter()
        .flat_map(|leaf| &leaf.hooks.chosen)
        .cloned()
}

#[cfg(test)]
mod tests {
    use k_rust::backend::HaltReasonOutput;

    use super::*;
    use crate::{
        exec::{InternalHalt, UncleanReason, reasons::EndNotComparable},
        report::{LISTED_HOOKS, ReasonHooks},
    };

    fn leaf(halt: HaltReasonOutput, halt_cause: Option<HaltCause>, hooks: LeafHooks) -> LeafReport {
        LeafReport {
            halt,
            halt_cause,
            depth: 1,
            state: k_rust::kore::parser::parse_pattern(r"\top{SortK{}}()").expect("parses"),
            unclean: vec![UncleanReason::Halt],
            natural_end: false,
            matches: Vec::new(),
            rewrites: Vec::new(),
            data_end: None,
            undeclared_in_other: false,
            diagnostics: Vec::new(),
            term_conjunction: false,
            undefined_rule: None,
            hooks,
        }
    }

    fn halted_on(hook: &str) -> LeafHooks {
        LeafHooks {
            halt: Some(hook.to_owned()),
            ..LeafHooks::default()
        }
    }

    fn result(leaves: Vec<LeafReport>, hooks: RunHooks) -> CaseResult {
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
            hooks,
            definition_data: Some(true),
        }
    }

    fn names(hooks: &BTreeSet<ReasonHook>) -> Vec<String> {
        hooks.iter().map(ToString::to_string).collect()
    }

    /// A halt reason names the hooks of the leaves whose halt stands for it only: an
    /// `unsupported-hook` halt's hook under `halt-unsupported-hook`, a `simplification-error`
    /// halt's under `halt-unsupported-construct`, and never an internal halt's (a crash, named by
    /// its site).
    #[test]
    fn a_halt_reason_names_the_hooks_of_its_own_leaves() {
        let construct = HaltCause::Unjudged(UnjudgedReason::HaltUnsupportedConstruct);
        let internal = HaltCause::Internal(InternalHalt {
            site: "builtin:wrong-arity:INT.add".to_owned(),
            message: String::new(),
        });
        let run = result(
            vec![
                leaf(HaltReasonOutput::UnsupportedHook, None, halted_on("WASM.a")),
                leaf(
                    HaltReasonOutput::SimplificationError,
                    Some(construct),
                    halted_on("WASM.b"),
                ),
                leaf(
                    HaltReasonOutput::SimplificationError,
                    Some(internal),
                    halted_on("WASM.c"),
                ),
            ],
            RunHooks::default(),
        );
        assert_eq!(
            names(&reason_hooks(&run, UnjudgedReason::HaltUnsupportedHook)),
            ["WASM.a"]
        );
        assert_eq!(
            names(&reason_hooks(
                &run,
                UnjudgedReason::HaltUnsupportedConstruct
            )),
            ["WASM.b"]
        );
        assert_eq!(
            names(&condition_hooks(&run, ComparableCondition::Halt)),
            ["WASM.a", "WASM.b"]
        );
        assert!(reason_hooks(&run, UnjudgedReason::InternalHalt).is_empty());
    }

    /// Chosen values: a leaf reason reads the leaves' marks (and an any-state reach's), the
    /// run-level reason the marks no leaf carries, and `kill-without-evidence` both; the
    /// unsupported-hook condition reads the run's and the load's records.
    #[test]
    fn each_reason_reads_the_facts_it_rests_on() {
        let marked = LeafHooks {
            chosen: vec![ReasonHook::chosen("MAP.choice", "item")],
            ..LeafHooks::default()
        };
        let run = result(
            vec![leaf(HaltReasonOutput::Stuck, None, marked)],
            RunHooks {
                unsupported: vec!["INT.shl".to_owned()],
                load_unsupported: vec!["KRYPTO.keccak256".to_owned()],
                chosen_off_leaves: vec![ReasonHook::chosen("MAP.keys_list", "order")],
                chosen_on_reach: vec![ReasonHook::chosen("SET.choice", "item")],
            },
        );
        assert_eq!(
            names(&reason_hooks(
                &run,
                UnjudgedReason::ImplementationChosenValue
            )),
            ["MAP.choice [item]", "SET.choice [item]"]
        );
        assert_eq!(
            names(&reason_hooks(&run, UnjudgedReason::RunFactOffLeaves)),
            ["MAP.keys_list [order]"]
        );
        assert_eq!(
            names(&reason_hooks(&run, UnjudgedReason::KillWithoutEvidence)),
            ["MAP.choice [item]", "MAP.keys_list [order]"]
        );
        assert_eq!(
            names(&reason_hooks(&run, UnjudgedReason::UnsupportedHook)),
            ["INT.shl"]
        );
        assert_eq!(
            names(&reason_hooks(
                &run,
                UnjudgedReason::EndNotComparable(EndNotComparable(
                    ComparableCondition::UnsupportedHook
                ))
            )),
            ["INT.shl", "KRYPTO.keccak256"]
        );
        assert!(reason_hooks(&run, UnjudgedReason::ContradictedClaim).is_empty());
    }

    /// (Review S2) The query condition `unsupported-hook` reads the run's records only, the end
    /// condition the load's too: the hooks follow each reading.
    #[test]
    fn the_query_condition_names_no_hook_of_the_load() {
        use crate::{
            exec::{
                comparable::{end_conditions, query_conditions},
                reasons::QueryNotConfirmable,
            },
            report::LoadRecord,
        };
        let load = || LoadRecord {
            kind: "unsupported-hook".to_owned(),
            detail: "KRYPTO.keccak256: no evaluator".to_owned(),
        };
        let mut loaded = result(
            vec![leaf(HaltReasonOutput::Stuck, None, LeafHooks::default())],
            RunHooks {
                load_unsupported: vec!["KRYPTO.keccak256".to_owned()],
                ..RunHooks::default()
            },
        );
        loaded.leaves[0].unclean.clear();
        loaded.leaves[0].data_end = Some(true);
        loaded.load_records.push(load());
        assert!(!query_conditions(&loaded, false).contains(&ComparableCondition::UnsupportedHook));
        assert!(end_conditions(&loaded).contains(&ComparableCondition::UnsupportedHook));
        let mut run = loaded.clone();
        run.hooks.unsupported = vec!["INT.shl".to_owned()];
        run.leaves[0].unclean = vec![UncleanReason::UnsupportedHook];
        assert!(query_conditions(&run, false).contains(&ComparableCondition::UnsupportedHook));
        let query = UnjudgedReason::QueryNotConfirmable(QueryNotConfirmable(
            ComparableCondition::UnsupportedHook,
        ));
        let end = UnjudgedReason::EndNotComparable(EndNotComparable(
            ComparableCondition::UnsupportedHook,
        ));
        assert_eq!(names(&reason_hooks(&run, query)), ["INT.shl"]);
        assert_eq!(
            names(&reason_hooks(&run, end)),
            ["INT.shl", "KRYPTO.keccak256"]
        );
    }

    /// A set of hooks lists its first [`LISTED_HOOKS`] in order and counts the rest, so the
    /// listing is a function of the set.
    #[test]
    fn a_set_of_hooks_is_listed_sorted_and_capped() {
        let many: BTreeSet<ReasonHook> = (0..LISTED_HOOKS + 2)
            .rev()
            .map(|index| ReasonHook::unsupported(&format!("H.{index:02}")))
            .collect();
        let listed = ReasonHooks::of(&many).expect("hooks");
        assert_eq!(listed.hooks.len(), LISTED_HOOKS);
        assert_eq!(listed.hooks[0], ReasonHook::unsupported("H.00"));
        assert_eq!(listed.omitted, 2);
        assert!(listed.describe().starts_with("hooks H.00, H.01"));
        assert!(listed.describe().ends_with(" and 2 more"));
        let one = ReasonHooks::of(&BTreeSet::from([ReasonHook::chosen(
            "MAP.keys_list",
            "order",
        )]))
        .expect("a hook");
        assert_eq!(one.describe(), "hook MAP.keys_list [order]");
        assert!(ReasonHooks::of(&BTreeSet::new()).is_none());
    }
}
