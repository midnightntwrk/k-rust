//! Request-local diagnostics emitted by backend operations.

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    builtin::UnsupportedHookReason,
    rule::Predicate,
    simplify::{BudgetSubject, ConditionIndeterminacy},
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum BackendDiagnostic {
    UndecidedCondition {
        rule_id: String,
        reason: ConditionIndeterminacy,
        predicates: Vec<Predicate>,
    },
    UndecidedPredicate {
        predicate: Predicate,
        reason: ConditionIndeterminacy,
    },
    SimplificationBudgetExhausted {
        limit: usize,
        subject: BudgetSubject,
    },
    /// The side conditions of an application attempt of the rule `rule_id` (its `requires`,
    /// the definedness obligations of its bindings, or its `ensures`) exhausted the budget
    /// `limit` while being simplified and were decided in their unsimplified form, so the rule
    /// may be left unapplied for lack of budget rather than because its condition is open.
    /// Always recorded in a collection right after the `SimplificationBudgetExhausted` with
    /// subject `Predicates` that it qualifies; in an execution path's list, which keeps each
    /// distinct diagnostic once, it follows that exhaustion but not necessarily directly.
    RuleConditionUnsimplified { rule_id: String, limit: usize },
    UnsupportedHookUnevaluated {
        hook: String,
        reason: UnsupportedHookReason,
    },
}

/// One emission recorded in a collection, kept in the form it was emitted in so that forwarding
/// it to an enclosing collection applies exactly the rule a direct emission would meet there.
#[derive(Clone, Debug)]
enum Emission {
    /// `emit(diagnostic)`.
    Single(BackendDiagnostic),
    /// `emit_rule_condition_budget_exhausted(rule_id, limit)`: the budget exhaustion over
    /// `Predicates` followed by the `RuleConditionUnsimplified` qualifying it.
    RuleConditionBudgetExhausted { rule_id: String, limit: usize },
}

impl Emission {
    fn records_rule_condition(&self, rule_id: &str, limit: usize) -> bool {
        match self {
            Self::Single(BackendDiagnostic::RuleConditionUnsimplified {
                rule_id: existing_rule,
                limit: existing_limit,
            })
            | Self::RuleConditionBudgetExhausted {
                rule_id: existing_rule,
                limit: existing_limit,
            } => existing_rule == rule_id && *existing_limit == limit,
            Self::Single(_) => false,
        }
    }
}

thread_local! {
    static SINK: RefCell<Option<Vec<Emission>>> = const { RefCell::new(None) };
}

/// Record a diagnostic when the current thread has an active collector.
pub fn emit(diagnostic: BackendDiagnostic) {
    record_in_sink(Emission::Single(diagnostic));
}

/// Record that simplifying the side conditions of `rule_id` exhausted the budget `limit`: a
/// `SimplificationBudgetExhausted` over `Predicates` qualified by `RuleConditionUnsimplified`.
///
/// The simplifier re-attempts a rule each time it meets the same redex, so the pair is recorded
/// once per rule and limit in a collection; repeated attempts report the same fact.
pub(crate) fn emit_rule_condition_budget_exhausted(rule_id: &str, limit: usize) {
    record_in_sink(Emission::RuleConditionBudgetExhausted {
        rule_id: rule_id.to_owned(),
        limit,
    });
}

fn record_in_sink(emission: Emission) {
    SINK.with(|sink| {
        if let Some(emissions) = sink.borrow_mut().as_mut() {
            record(emissions, emission);
        }
    });
}

/// Append `emission` to a collection under the collection's rules: an unevaluated hook is
/// reported once per hook, whatever the reason given at later calls; a rule-condition budget
/// exhaustion once per rule and limit (a `RuleConditionUnsimplified` already in the collection,
/// however emitted, reports it); every other diagnostic is appended as emitted.
fn record(emissions: &mut Vec<Emission>, emission: Emission) {
    let duplicate = match &emission {
        Emission::Single(BackendDiagnostic::UnsupportedHookUnevaluated { hook, .. }) => {
            emissions.iter().any(|existing| {
                matches!(
                    existing,
                    Emission::Single(BackendDiagnostic::UnsupportedHookUnevaluated {
                        hook: existing_hook,
                        ..
                    }) if existing_hook == hook
                )
            })
        }
        Emission::RuleConditionBudgetExhausted { rule_id, limit } => emissions
            .iter()
            .any(|existing| existing.records_rule_condition(rule_id, *limit)),
        Emission::Single(_) => false,
    };
    if !duplicate {
        emissions.push(emission);
    }
}

fn diagnostics_of(emissions: Vec<Emission>) -> Vec<BackendDiagnostic> {
    let mut diagnostics = Vec::with_capacity(emissions.len());
    for emission in emissions {
        match emission {
            Emission::Single(diagnostic) => diagnostics.push(diagnostic),
            Emission::RuleConditionBudgetExhausted { rule_id, limit } => {
                diagnostics.push(BackendDiagnostic::SimplificationBudgetExhausted {
                    limit,
                    subject: BudgetSubject::Predicates,
                });
                diagnostics.push(BackendDiagnostic::RuleConditionUnsimplified { rule_id, limit });
            }
        }
    }
    diagnostics
}

/// Collect diagnostics emitted while `action` runs.
///
/// Collections nest: when `action` returns or unwinds, the enclosing collector (if any) is
/// restored and receives each collected emission as if it had been emitted into it directly,
/// under its own rules, so a caller collecting around an operation sees every diagnostic
/// whatever the operation collects inside, in emission order.
pub fn collect<T>(action: impl FnOnce() -> T) -> (T, Vec<BackendDiagnostic>) {
    let collection = Collection::open();
    let result = action();
    (result, diagnostics_of(collection.close()))
}

/// An open collection; closing it, or dropping it while unwinding, restores the enclosing
/// collector and forwards the collection to it.
struct Collection {
    enclosing: Option<Option<Vec<Emission>>>,
}

impl Collection {
    fn open() -> Self {
        let enclosing = SINK.with(|sink| sink.replace(Some(Vec::new())));
        Self {
            enclosing: Some(enclosing),
        }
    }

    fn close(mut self) -> Vec<Emission> {
        let enclosing = self.enclosing.take().expect("a collection is closed once");
        restore_and_forward(enclosing)
    }
}

impl Drop for Collection {
    fn drop(&mut self) {
        if let Some(enclosing) = self.enclosing.take() {
            restore_and_forward(enclosing);
        }
    }
}

fn restore_and_forward(mut enclosing: Option<Vec<Emission>>) -> Vec<Emission> {
    SINK.with(|sink| {
        let mut sink = sink.borrow_mut();
        let inner = sink.take().unwrap_or_default();
        if let Some(enclosing) = enclosing.as_mut() {
            for emission in &inner {
                record(enclosing, emission.clone());
            }
        }
        *sink = enclosing;
        inner
    })
}

/// Append each diagnostic of `diagnostics` that `list` does not hold yet, in order.
pub(crate) fn extend_distinct(
    list: &mut Vec<BackendDiagnostic>,
    diagnostics: &[BackendDiagnostic],
) {
    for diagnostic in diagnostics {
        if !list.contains(diagnostic) {
            list.push(diagnostic.clone());
        }
    }
}

/// The distinct diagnostics of one execution request, numbered in first-seen order, shared by
/// every path of the request.
#[derive(Default)]
struct Interner {
    ids: HashMap<Rc<BackendDiagnostic>, u32>,
}

impl Interner {
    fn intern(&mut self, diagnostic: &BackendDiagnostic) -> (u32, Rc<BackendDiagnostic>) {
        if let Some((shared, id)) = self.ids.get_key_value(diagnostic) {
            return (*id, Rc::clone(shared));
        }
        let id = u32::try_from(self.ids.len()).expect("fewer than 2^32 distinct diagnostics");
        let shared = Rc::new(diagnostic.clone());
        self.ids.insert(Rc::clone(&shared), id);
        (id, shared)
    }
}

/// A persistent set of interned diagnostic ids: blocks of 4,096 bits shared between the paths
/// that forked from a common prefix, copied only when a path inserts into a shared block.
#[derive(Clone, Default)]
struct IdSet {
    blocks: Rc<Vec<Option<Rc<[u64; 64]>>>>,
}

impl IdSet {
    fn position(id: u32) -> (usize, usize, u32) {
        let id = id as usize;
        (id / 4096, id % 4096 / 64, (id % 64) as u32)
    }

    fn contains(&self, id: u32) -> bool {
        let (block, word, bit) = Self::position(id);
        self.blocks
            .get(block)
            .and_then(Option::as_ref)
            .is_some_and(|words| words[word] >> bit & 1 == 1)
    }

    fn insert(&mut self, id: u32) {
        let (block, word, bit) = Self::position(id);
        let blocks = Rc::make_mut(&mut self.blocks);
        if blocks.len() <= block {
            blocks.resize(block + 1, None);
        }
        let words = blocks[block].get_or_insert_with(|| Rc::new([0; 64]));
        Rc::make_mut(words)[word] |= 1 << bit;
    }
}

struct PathNode {
    diagnostic: Rc<BackendDiagnostic>,
    parent: Option<Rc<PathNode>>,
}

/// The diagnostics of one execution path so far: each distinct diagnostic once, in the order
/// the path first met it.
///
/// A path shares its list with the paths it forks into: cloning is constant time, appending a
/// diagnostic the path already holds is a constant-time lookup, and a new one adds one node.
/// The list is materialised once, when the path ends in a leaf.
#[derive(Clone)]
pub(crate) struct PathDiagnostics {
    interner: Rc<RefCell<Interner>>,
    newest: Option<Rc<PathNode>>,
    members: IdSet,
}

impl PathDiagnostics {
    /// The empty list of a request's first path; every path forked from it shares its numbering.
    pub(crate) fn new_request() -> Self {
        Self {
            interner: Rc::default(),
            newest: None,
            members: IdSet::default(),
        }
    }

    /// An empty list numbered like `self`, for another path of the same request.
    pub(crate) fn empty_like(&self) -> Self {
        Self {
            interner: Rc::clone(&self.interner),
            newest: None,
            members: IdSet::default(),
        }
    }

    pub(crate) fn extend(&mut self, diagnostics: &[BackendDiagnostic]) {
        if diagnostics.is_empty() {
            return;
        }
        let mut interner = self.interner.borrow_mut();
        for diagnostic in diagnostics {
            let (id, shared) = interner.intern(diagnostic);
            if !self.members.contains(id) {
                self.members.insert(id);
                self.newest = Some(Rc::new(PathNode {
                    diagnostic: shared,
                    parent: self.newest.take(),
                }));
            }
        }
    }

    pub(crate) fn to_vec(&self) -> Vec<BackendDiagnostic> {
        let mut diagnostics = Vec::new();
        let mut node = self.newest.as_deref();
        while let Some(current) = node {
            diagnostics.push(BackendDiagnostic::clone(&current.diagnostic));
            node = current.parent.as_deref();
        }
        diagnostics.reverse();
        diagnostics
    }
}

impl Drop for PathNode {
    /// Unlink a long unshared chain iteratively rather than by recursive drops.
    fn drop(&mut self) {
        let mut parent = self.parent.take();
        while let Some(node) = parent {
            match Rc::try_unwrap(node) {
                Ok(mut node) => parent = node.parent.take(),
                Err(_) => break,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn term_exhausted(limit: usize) -> BackendDiagnostic {
        BackendDiagnostic::SimplificationBudgetExhausted {
            limit,
            subject: BudgetSubject::Term,
        }
    }

    fn predicates_exhausted(limit: usize) -> BackendDiagnostic {
        BackendDiagnostic::SimplificationBudgetExhausted {
            limit,
            subject: BudgetSubject::Predicates,
        }
    }

    fn rule_condition(rule_id: &str, limit: usize) -> BackendDiagnostic {
        BackendDiagnostic::RuleConditionUnsimplified {
            rule_id: rule_id.to_owned(),
            limit,
        }
    }

    fn hook(hook: &str, reason: UnsupportedHookReason) -> BackendDiagnostic {
        BackendDiagnostic::UnsupportedHookUnevaluated {
            hook: hook.to_owned(),
            reason,
        }
    }

    fn out_of_range() -> UnsupportedHookReason {
        UnsupportedHookReason::ArgumentOutOfRange {
            detail: "second call".to_owned(),
        }
    }

    /// The emissions every nesting below performs, in order: two batches, each of which a nested
    /// collection may capture.
    fn first_batch() {
        emit(hook("INT.pow", UnsupportedHookReason::NotImplemented));
        emit(term_exhausted(3));
        emit_rule_condition_budget_exhausted("r1", 3);
        emit(predicates_exhausted(3));
    }

    fn second_batch() {
        emit(hook("INT.pow", out_of_range()));
        emit(term_exhausted(3));
        emit_rule_condition_budget_exhausted("r1", 3);
        emit(predicates_exhausted(3));
        emit_rule_condition_budget_exhausted("r2", 3);
        emit(hook("INT.log2", UnsupportedHookReason::NotImplemented));
    }

    #[test]
    fn nested_collection_forwards_to_the_enclosing_collector_under_its_rules() {
        let ((), direct) = collect(|| {
            first_batch();
            second_batch();
        });
        let expected = vec![
            hook("INT.pow", UnsupportedHookReason::NotImplemented),
            term_exhausted(3),
            predicates_exhausted(3),
            rule_condition("r1", 3),
            predicates_exhausted(3),
            term_exhausted(3),
            predicates_exhausted(3),
            predicates_exhausted(3),
            rule_condition("r2", 3),
            hook("INT.log2", UnsupportedHookReason::NotImplemented),
        ];
        assert_eq!(direct, expected);

        let ((inner_first, inner_second), outer) = collect(|| {
            let ((), first) = collect(first_batch);
            let (second, _) = collect(|| collect(second_batch).1);
            (first, second)
        });
        assert_eq!(
            outer, expected,
            "the enclosing collector sees the direct list"
        );
        assert_eq!(
            inner_first,
            vec![
                hook("INT.pow", UnsupportedHookReason::NotImplemented),
                term_exhausted(3),
                predicates_exhausted(3),
                rule_condition("r1", 3),
                predicates_exhausted(3),
            ]
        );
        assert_eq!(
            inner_second,
            vec![
                hook("INT.pow", out_of_range()),
                term_exhausted(3),
                predicates_exhausted(3),
                rule_condition("r1", 3),
                predicates_exhausted(3),
                predicates_exhausted(3),
                rule_condition("r2", 3),
                hook("INT.log2", UnsupportedHookReason::NotImplemented),
            ],
            "an inner collection applies its rules to its own emissions only"
        );
    }

    #[test]
    fn a_collection_without_an_enclosing_collector_forwards_nothing() {
        let ((), inner) = collect(first_batch);
        assert_eq!(inner.len(), 5);
        emit(term_exhausted(1));
        let ((), after) = collect(|| {});
        assert!(after.is_empty(), "no collector outlives its collection");
    }

    #[test]
    fn a_collection_unwinding_through_a_panic_still_forwards_its_emissions() {
        let (caught, outer) = collect(|| {
            std::panic::catch_unwind(|| {
                collect(|| {
                    emit(term_exhausted(7));
                    emit(hook("INT.pow", UnsupportedHookReason::NotImplemented));
                    panic!("the action unwinds after emitting");
                })
            })
        });
        assert!(caught.is_err());
        assert_eq!(
            outer,
            vec![
                term_exhausted(7),
                hook("INT.pow", UnsupportedHookReason::NotImplemented),
            ]
        );
        let ((), after) = collect(|| emit(term_exhausted(1)));
        assert_eq!(after, vec![term_exhausted(1)], "the sink is restored");
    }

    /// A budget exhaustion and a `RuleConditionUnsimplified` emitted separately are two plain
    /// emissions, not the pair: forwarding keeps both where direct emission keeps both, although
    /// the enclosing collection already holds the pair for that rule and limit.
    #[test]
    fn separately_emitted_rule_condition_diagnostics_forward_as_they_were_emitted() {
        let emissions = || {
            emit_rule_condition_budget_exhausted("r1", 3);
            emit(predicates_exhausted(3));
            emit(rule_condition("r1", 3));
            emit_rule_condition_budget_exhausted("r1", 3);
        };
        let ((), direct) = collect(emissions);
        let expected = vec![
            predicates_exhausted(3),
            rule_condition("r1", 3),
            predicates_exhausted(3),
            rule_condition("r1", 3),
        ];
        assert_eq!(direct, expected);

        let ((), forwarded) = collect(|| {
            emit_rule_condition_budget_exhausted("r1", 3);
            collect(|| {
                emit(predicates_exhausted(3));
                emit(rule_condition("r1", 3));
            });
            collect(|| emit_rule_condition_budget_exhausted("r1", 3));
        });
        assert_eq!(forwarded, expected);
    }

    #[test]
    fn a_path_records_each_diagnostic_once_in_first_occurrence_order() {
        let mut parent = PathDiagnostics::new_request();
        parent.extend(&[term_exhausted(3)]);
        let mut left = parent.clone();
        let mut right = parent.clone();
        left.extend(&[
            predicates_exhausted(3),
            rule_condition("r1", 3),
            term_exhausted(3),
            predicates_exhausted(3),
            rule_condition("r2", 3),
        ]);
        left.extend(&[term_exhausted(3), rule_condition("r1", 3)]);
        right.extend(&[rule_condition("r2", 3)]);
        assert_eq!(
            left.to_vec(),
            vec![
                term_exhausted(3),
                predicates_exhausted(3),
                rule_condition("r1", 3),
                rule_condition("r2", 3),
            ]
        );
        assert_eq!(
            right.to_vec(),
            vec![term_exhausted(3), rule_condition("r2", 3)],
            "a fork shares its parent's prefix, not its sibling's additions"
        );
        assert_eq!(parent.to_vec(), vec![term_exhausted(3)]);
        assert!(parent.empty_like().to_vec().is_empty());
    }

    #[test]
    fn path_membership_spans_several_blocks() {
        let mut path = PathDiagnostics::new_request();
        let many = (0..10_000).map(term_exhausted).collect::<Vec<_>>();
        path.extend(&many);
        let fork = path.clone();
        path.extend(&[term_exhausted(9_999), term_exhausted(10_000)]);
        assert_eq!(path.to_vec().len(), 10_001);
        assert_eq!(fork.to_vec().len(), 10_000);
    }
}
