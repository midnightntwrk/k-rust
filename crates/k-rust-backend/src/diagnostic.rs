//! Request-local diagnostics emitted by backend operations.

use std::{
    borrow::Cow,
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet, HashMap},
    rc::Rc,
};

use k_rust_kore::measure::{self, Counter};
use rustc_hash::FxHashSet;

use crate::{
    builtin::UnsupportedHookReason,
    rule::{Predicate, RuleOrigin, collect_all_variables, rename_predicates},
    simplify::{BudgetSubject, ConditionIndeterminacy, SimplificationError},
    term::{
        Term, TermKind, Variable,
        names::{
            FreshMarker, encode_variable_name, rule_variable_definition_name, with_fresh_marker,
        },
    },
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum BackendDiagnostic {
    /// A condition of an application attempt of the equation `rule_id` was left undecided for
    /// `reason`. `predicates` are the condition as decided, one of two:
    ///
    /// - The equation's `requires`, instantiated by the match; the equation is not used on this
    ///   subject. A variable the left-hand side binds is replaced by the term it matched. A
    ///   variable it does not bind stays a variable of the equation, named with the backend's
    ///   marker (`Eq#Y`, printed `Eq-hY`, or `Eq#Y!apart0` when renamed apart from the subject).
    /// - Once the `requires` held, the definedness of the terms the match bound (`\ceil(t)` for
    ///   each such term `t`); the equation is used, and its result carries these predicates as
    ///   constraints.
    ///
    /// The reasons are a solver that was asked and could not answer (`SmtUnknown`,
    /// `Untranslatable`, `InconsistentPathCondition`), for either condition, and, for the
    /// `requires` only, an equation whose right-hand side or `ensures` has variables its
    /// left-hand side does not bind (`UnboundResultVariables`) and whose `requires` was not
    /// refuted: its instance names no value for them, so it is not used.
    ///
    /// Like every diagnostic emitted during an equation attempt, it is reported only with an
    /// outcome the simplification keeps (`buffer`): the equation applied, or the attempt was
    /// indeterminate and no other equation rewrote the subject, which was left unevaluated, and
    /// the result of the simplification still holds that subject (`retract_dropped`), as does
    /// the outcome of the rewrite rule attempt that made the simplification, if any. An attempt
    /// whose `requires` was refuted, one that another equation superseded, one whose subject a
    /// later part of the same simplification or rule attempt dropped, and one made while
    /// simplifying the condition of an enclosing attempt that was itself refuted, superseded or
    /// dropped report nothing.
    UndecidedCondition {
        rule_id: String,
        /// The first written sentence of the equation's axiom
        /// ([`origins`](crate::rule::RuleAttributes::origins)). Axioms that carry neither a
        /// label nor a `UNIQUE_ID` share the `rule_id` `UNKNOWN`, and no two axioms of a
        /// definition share a first sentence, so the origin names the axiom the condition
        /// belongs to where the id does not.
        origin: Option<RuleOrigin>,
        reason: ConditionIndeterminacy,
        predicates: Vec<Predicate>,
        /// The variables of the equation that are free in `predicates`, as the attempt names
        /// them: those its left-hand side does not bind. Membership is a fact of the attempt,
        /// not of a name's shape; a variable of the subject is never listed, even one that is
        /// another equation's variable (an enclosing equation's `Eq#Z`, which reached this
        /// subject while that equation's `requires` was simplified). The definedness of bound
        /// terms has none. [`printable_condition`] gives each one's name in the definition.
        rule_variables: Vec<Variable>,
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
    /// Simplifying the side conditions of an application attempt of the rule `rule_id` failed
    /// with `failure`, so they were decided in their unsimplified form. They are the same
    /// condition, so the decision is sound, but it may be weaker: the rule may be left unapplied
    /// because simplifying its condition failed rather than because the condition is open.
    /// Recorded once per rule and failure in a collection, as every attempt of the rule on the
    /// same instance fails the same way.
    RuleConditionFailed {
        rule_id: String,
        failure: SimplificationError,
    },
    UnsupportedHookUnevaluated {
        hook: String,
        reason: UnsupportedHookReason,
    },
}

/// A free variable of an [`BackendDiagnostic::UndecidedCondition`]'s predicates that is a
/// variable of its equation, which the equation's left-hand side does not bind.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConditionRuleVariable {
    /// The variable as the printable predicates name it.
    pub variable: Variable,
    /// Its name as the definition writes it in the equation (`VarY` for `Eq#VarY`).
    pub definition_name: String,
}

/// The predicates of an [`BackendDiagnostic::UndecidedCondition`] as a response prints them,
/// and each of its `rule_variables` that they name free, with the name the definition gives it.
///
/// Printing keeps a name read from KORE and escapes a backend name (`Eq#Y` prints `Eq-hY`), so
/// a variable of the request spelled like the escape of a variable of the equation would print
/// alike in the same predicates. The equation's variable is bound by the equation, so it is
/// renamed for printing, to `{name}!apart{counter}` with the least counter whose spelling no
/// variable of the predicates has; the request's variable keeps its name. Without such a
/// clash the predicates are returned unchanged.
pub fn printable_condition<'a>(
    predicates: &'a [Predicate],
    rule_variables: &[Variable],
) -> (Cow<'a, [Predicate]>, Vec<ConditionRuleVariable>) {
    if rule_variables.is_empty() {
        return (Cow::Borrowed(predicates), Vec::new());
    }
    let free = predicates
        .iter()
        .flat_map(Predicate::free_variables)
        .collect::<BTreeSet<_>>();
    let rule_variables = rule_variables
        .iter()
        .filter(|variable| free.contains(*variable))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|variable| (variable, rule_variable_definition_name(&variable.name)))
        .collect::<Vec<_>>();
    if rule_variables.is_empty() {
        return (Cow::Borrowed(predicates), Vec::new());
    }
    // Another free variable prints alike: distinct names print alike only when one of them is
    // read from KORE and spelled like the escape of the other.
    let clashes = |variable: &Variable| {
        let spelling = encode_variable_name(&variable.name);
        free.iter().any(|other| {
            other.name != variable.name && encode_variable_name(&other.name) == spelling
        })
    };
    let mut renaming = BTreeMap::new();
    if rule_variables.iter().any(|(variable, _)| clashes(variable)) {
        let mut all = BTreeSet::new();
        collect_all_variables(predicates, &mut all);
        let mut taken = all
            .iter()
            .map(|variable| encode_variable_name(&variable.name))
            .collect::<BTreeSet<_>>();
        let mut counter = 0;
        for (variable, _) in &rule_variables {
            if !clashes(variable) {
                continue;
            }
            // The marker and the definition's name, without an earlier `!apart` suffix.
            let base = variable
                .name
                .split_once('!')
                .map_or(variable.name.as_ref(), |(base, _)| base);
            let renamed = loop {
                let name = with_fresh_marker(base, FreshMarker::Apart, counter);
                counter += 1;
                if taken.insert(encode_variable_name(&name)) {
                    break variable.with_name(name);
                }
            };
            renaming.insert((*variable).clone(), renamed);
        }
    }
    let explained = rule_variables
        .into_iter()
        .map(|(variable, definition_name)| ConditionRuleVariable {
            variable: renaming
                .get(variable)
                .cloned()
                .unwrap_or_else(|| variable.clone()),
            definition_name,
        })
        .collect();
    if renaming.is_empty() {
        return (Cow::Borrowed(predicates), explained);
    }
    let printable = rename_predicates(predicates, |variable| {
        renaming
            .get(variable)
            .cloned()
            .unwrap_or_else(|| variable.clone())
    });
    (Cow::Owned(printable), explained)
}

/// One emission recorded in a collection, kept in the form it was emitted in so that forwarding
/// it to an enclosing collection applies exactly the rule a direct emission would meet there,
/// with its position in the thread's emission order.
#[derive(Clone, Debug)]
struct Emission {
    position: u64,
    kind: EmissionKind,
    /// The subject the emission explains, when it was raised during an equation attempt that was
    /// passed over and left that subject unevaluated ([`Buffered::commit_kept`]); `None` for
    /// every other emission. It is kept only while the subject is ([`retract_dropped`]).
    subject: Option<Subject>,
}

/// What a report raised during a passed-over equation attempt explains: the term, or for a ceil
/// or predicate equation the predicate, that the attempt left unevaluated at its node.
///
/// Such a report tells a client why the result keeps that subject unevaluated. If a later part of
/// the same simplification drops the subject, the result does not depend on its value (an
/// equation that drops an argument holds for every value of it, a condition decided without it
/// holds whatever it is, and a definedness that is not provable stays in the result as `⌈t⌉`, so
/// the subject then still occurs), and the report explains nothing the client receives.
#[derive(Clone, Debug)]
pub(crate) enum Subject {
    Term(Term),
    Predicate(Predicate),
}

#[derive(Clone, Debug)]
enum EmissionKind {
    /// `emit(diagnostic)`.
    Single(BackendDiagnostic),
    /// `emit_rule_condition_budget_exhausted(rule_id, limit)`: the budget exhaustion over
    /// `Predicates` followed by the `RuleConditionUnsimplified` qualifying it.
    RuleConditionBudgetExhausted { rule_id: String, limit: usize },
}

impl EmissionKind {
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
    static SINK: RefCell<Option<Sink>> = const { RefCell::new(None) };
    static NEXT_POSITION: Cell<u64> = const { Cell::new(0) };
}

/// A collected diagnostic with its position in the thread's emission order, so that lists
/// collected separately can be merged in the order their diagnostics were emitted.
#[derive(Clone, Debug)]
pub(crate) struct Sequenced {
    pub(crate) position: u64,
    pub(crate) diagnostic: BackendDiagnostic,
}

/// Record a diagnostic when the current thread has an active collector.
pub fn emit(diagnostic: BackendDiagnostic) {
    record_in_sink(EmissionKind::Single(diagnostic));
}

/// Record that simplifying the side conditions of `rule_id` exhausted the budget `limit`: a
/// `SimplificationBudgetExhausted` over `Predicates` qualified by `RuleConditionUnsimplified`.
///
/// The simplifier re-attempts a rule each time it meets the same redex, so the pair is recorded
/// once per rule and limit in a collection; repeated attempts report the same fact.
pub(crate) fn emit_rule_condition_budget_exhausted(rule_id: &str, limit: usize) {
    record_in_sink(EmissionKind::RuleConditionBudgetExhausted {
        rule_id: rule_id.to_owned(),
        limit,
    });
}

/// The emissions of one open collection. A unit collection (`collect_unit`) records every
/// emission as emitted, for attribution; any other applies the collection rules of `record`.
struct Sink {
    unit: bool,
    emissions: Vec<Emission>,
}

impl Sink {
    fn record(&mut self, emission: Emission) {
        if self.unit {
            self.emissions.push(emission);
        } else {
            record(&mut self.emissions, emission);
        }
    }
}

fn record_in_sink(kind: EmissionKind) {
    SINK.with(|sink| {
        if let Some(sink) = sink.borrow_mut().as_mut() {
            let position = NEXT_POSITION.with(|next| next.replace(next.get() + 1));
            sink.record(Emission {
                position,
                kind,
                subject: None,
            });
        }
    });
}

/// How many emissions the current collection holds, for [`discard_since`]; `None` without a
/// collector.
#[derive(Clone, Copy, Debug)]
pub(crate) struct EmissionMark(Option<usize>);

/// The current collection's extent now ([`EmissionMark`]).
pub(crate) fn mark() -> EmissionMark {
    EmissionMark(SINK.with(|sink| sink.borrow().as_ref().map(|sink| sink.emissions.len())))
}

/// Drop what the current collection recorded since `mark`, which must have been taken in the
/// same collection: the work that emitted it was undone, and the collection is as if it had
/// never run. Every collection rule (one report per hook, say) only declines an emission that
/// an earlier one already records, so the emissions kept, and what later ones meet, are those
/// before `mark`.
pub(crate) fn discard_since(mark: EmissionMark) {
    let EmissionMark(Some(len)) = mark else {
        return;
    };
    SINK.with(|sink| {
        if let Some(sink) = sink.borrow_mut().as_mut() {
            sink.emissions.truncate(len);
        }
    });
}

/// The position the next emission on this thread will take: every emission of a unit of work
/// that starts at `a` and ends at `b` has a position in `a..b`.
pub(crate) fn next_position() -> u64 {
    NEXT_POSITION.with(Cell::get)
}

/// Append `emission` to a collection under the collection's rules: an unevaluated hook is
/// reported once per hook, whatever the reason given at later calls; a rule-condition budget
/// exhaustion once per rule and limit (a `RuleConditionUnsimplified` already in the collection,
/// however emitted, reports it); a rule-condition failure once per rule and failure; every other
/// diagnostic is appended as emitted.
fn record(emissions: &mut Vec<Emission>, emission: Emission) {
    let duplicate = match &emission.kind {
        EmissionKind::Single(BackendDiagnostic::UnsupportedHookUnevaluated { hook, .. }) => {
            emissions.iter().any(|existing| {
                matches!(
                    &existing.kind,
                    EmissionKind::Single(BackendDiagnostic::UnsupportedHookUnevaluated {
                        hook: existing_hook,
                        ..
                    }) if existing_hook == hook
                )
            })
        }
        EmissionKind::RuleConditionBudgetExhausted { rule_id, limit } => emissions
            .iter()
            .any(|existing| existing.kind.records_rule_condition(rule_id, *limit)),
        EmissionKind::Single(failed @ BackendDiagnostic::RuleConditionFailed { .. }) => {
            emissions.iter().any(
                |existing| matches!(&existing.kind, EmissionKind::Single(other) if other == failed),
            )
        }
        EmissionKind::Single(_) => false,
    };
    if !duplicate {
        emissions.push(emission);
    }
}

fn sequenced(emissions: Vec<Emission>) -> Vec<Sequenced> {
    let mut diagnostics = Vec::with_capacity(emissions.len());
    for Emission { position, kind, .. } in emissions {
        match kind {
            EmissionKind::Single(diagnostic) => diagnostics.push(Sequenced {
                position,
                diagnostic,
            }),
            EmissionKind::RuleConditionBudgetExhausted { rule_id, limit } => {
                diagnostics.push(Sequenced {
                    position,
                    diagnostic: BackendDiagnostic::SimplificationBudgetExhausted {
                        limit,
                        subject: BudgetSubject::Predicates,
                    },
                });
                diagnostics.push(Sequenced {
                    position,
                    diagnostic: BackendDiagnostic::RuleConditionUnsimplified { rule_id, limit },
                });
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
    let collection = Collection::open(false);
    let result = action();
    (
        result,
        sequenced(collection.close())
            .into_iter()
            .map(|sequenced| sequenced.diagnostic)
            .collect(),
    )
}

/// Collect every diagnostic one unit of work emits, as emitted and with its position in the
/// thread's emission order, for attributing the unit's work to the paths its result belongs
/// to; the enclosing collector receives them under its own rules as with `collect`.
pub(crate) fn collect_unit<T>(action: impl FnOnce() -> T) -> (T, Vec<Sequenced>) {
    let collection = Collection::open(true);
    let result = action();
    (result, sequenced(collection.close()))
}

/// Concatenate lists collected by `collect_unit` in emission order.
pub(crate) fn merge_units(lists: &[&[Sequenced]]) -> Vec<Sequenced> {
    let mut merged = lists
        .iter()
        .flat_map(|list| list.iter().cloned())
        .collect::<Vec<_>>();
    merged.sort_by_key(|sequenced| sequenced.position);
    merged
}

/// The diagnostics of several separately collected lists in the order they were emitted, each
/// distinct diagnostic once.
pub(crate) fn in_emission_order<'a>(
    lists: impl IntoIterator<Item = &'a [Sequenced]>,
) -> Vec<BackendDiagnostic> {
    let mut merged = lists.into_iter().flatten().collect::<Vec<_>>();
    // Stable: the two diagnostics of one rule-condition emission share a position.
    merged.sort_by_key(|sequenced| sequenced.position);
    let mut seen = std::collections::HashSet::with_capacity(merged.len());
    merged
        .into_iter()
        .filter(|sequenced| seen.insert(&sequenced.diagnostic))
        .map(|sequenced| sequenced.diagnostic.clone())
        .collect()
}

/// An open collection; closing it, or dropping it while unwinding, restores the enclosing
/// collector and forwards the collection to it.
struct Collection {
    enclosing: Option<Option<Sink>>,
}

impl Collection {
    fn open(unit: bool) -> Self {
        let enclosing = SINK.with(|sink| {
            sink.replace(Some(Sink {
                unit,
                emissions: Vec::new(),
            }))
        });
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

fn restore_and_forward(mut enclosing: Option<Sink>) -> Vec<Emission> {
    SINK.with(|sink| {
        let mut sink = sink.borrow_mut();
        let inner = sink.take().map(|inner| inner.emissions).unwrap_or_default();
        if let Some(enclosing) = enclosing.as_mut() {
            for emission in &inner {
                enclosing.record(emission.clone());
            }
        }
        *sink = enclosing;
        inner
    })
}

/// Run `action` as an attempt whose diagnostics count only if `keep` accepts its result.
///
/// An attempt whose result the caller discards and redoes reports nothing, so the redone work
/// is reported once. Accepted emissions reach the enclosing collector, under its rules, as if
/// emitted into it directly; without an enclosing collector nothing is recorded either way.
pub(crate) fn attempt<T>(action: impl FnOnce() -> T, keep: impl FnOnce(&T) -> bool) -> T {
    let (result, buffered) = buffer(action);
    if keep(&result) {
        buffered.commit();
    }
    result
}

/// The diagnostics a speculative piece of work emitted, held apart from every collector until
/// the caller knows whether the work's outcome is kept.
///
/// A diagnostic is a claim about the result the work contributes to. While that is undecided
/// (an equation attempt whose subject another equation may still rewrite, or whose `requires`
/// belongs to an enclosing attempt that may still be refuted), its diagnostics are held here:
/// [`Buffered::commit`] records them once the outcome is kept, and dropping the buffer discards
/// them with the outcome. Buffers nest: one committed while another is open records into it, so
/// an outcome kept inside an enclosing attempt that is then discarded is discarded with it.
#[must_use = "a buffer is committed when its outcome is kept and dropped when it is not"]
pub(crate) struct Buffered(Vec<Emission>);

impl Buffered {
    /// Record the held emissions in the current collector, under its rules, as if they were
    /// emitted into it directly, with their original positions; nothing without a collector.
    pub(crate) fn commit(self) {
        if self.0.is_empty() {
            return;
        }
        SINK.with(|sink| {
            if let Some(sink) = sink.borrow_mut().as_mut() {
                for emission in self.0 {
                    sink.record(emission);
                }
            }
        });
    }

    /// Whether nothing is held.
    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The held emissions of an attempt that was passed over, whose `subject` its node keeps:
    /// [`Self::commit`] them, each now explaining `subject`.
    ///
    /// They stand or fall with it: the attempt's own report says why the subject is kept, and a
    /// report raised while its condition was simplified (of a term inside the `requires`, say)
    /// says why that condition stayed open. A subject an inner node gave an emission is replaced,
    /// since the inner term matters to the result only through this attempt's subject.
    pub(crate) fn commit_kept(mut self, subject: &Subject) {
        for emission in &mut self.0 {
            emission.subject = Some(subject.clone());
        }
        self.commit();
    }
}

/// Run a simplifier entry, keeping each report that explains a subject
/// ([`Buffered::commit_kept`]) only if the entry's result still holds that subject.
///
/// `occurrences` gives what the caller receives (the simplified term with the conditions it
/// carries, or the simplified predicates), or `None` for a failure or a stop, which keeps every
/// report, as no result replaced the work they describe. It is called only when some report
/// explains a subject, and the result is then searched for those subjects only
/// ([`Occurrences::holding`]). Every other emission, and the order and positions of all of them,
/// are as if `action` had emitted into the current collector directly. A report that survives
/// keeps its subject, so an enclosing entry that drops the subject in turn retracts it there.
///
/// ```toml algorithm-site
/// id = "backend.simplify.term"
/// role = "part"
/// sites = ["retract_dropped", "Occurrences::holding"]
/// ```
pub(crate) fn retract_dropped<T>(
    action: impl FnOnce() -> T,
    occurrences: impl FnOnce(&T) -> Option<Occurrences<'_>>,
) -> T {
    retract_dropped_reporting(action, occurrences).0
}

/// [`retract_dropped`] for a scope whose units of work attribute their own diagnostics inside it
/// ([`collect_unit`]): it also returns which reports it retracted, so the caller takes them out
/// of the lists those units hold ([`Retracted::remove_from`]).
///
/// Such a unit records each emission in the scope as it records it in its own list, so the scope
/// decides on every report the unit raised, and a report it retracts reaches no path through
/// either.
pub(crate) fn retract_dropped_reporting<T>(
    action: impl FnOnce() -> T,
    occurrences: impl FnOnce(&T) -> Option<Occurrences<'_>>,
) -> (T, Retracted) {
    let (result, mut held) = buffer(action);
    let mut retracted = Retracted::default();
    if held.0.iter().any(|emission| emission.subject.is_some())
        && let Some(occurrences) = occurrences(&result)
    {
        let subjects = held
            .0
            .iter()
            .filter_map(|emission| emission.subject.as_ref())
            .collect::<Vec<_>>();
        let found = occurrences.holding(&subjects);
        held.0.retain(|emission| {
            let kept = emission
                .subject
                .as_ref()
                .is_none_or(|subject| found.contains(subject));
            if !kept {
                retracted.0.insert(emission.position);
            }
            kept
        });
    }
    held.commit();
    (result, retracted)
}

/// The reports a [`retract_dropped_reporting`] scope retracted, by their positions in the
/// thread's emission order; a position names one emission wherever it is forwarded.
#[derive(Debug, Default)]
pub(crate) struct Retracted(FxHashSet<u64>);

impl Retracted {
    /// Take the retracted reports out of `list`, a unit's own list of the scope's emissions.
    pub(crate) fn remove_from(&self, list: &mut Vec<Sequenced>) {
        if !self.0.is_empty() {
            list.retain(|sequenced| !self.0.contains(&sequenced.position));
        }
    }
}

/// What a simplifier entry returns, its terms and predicates, to be searched for the subjects of
/// its reports ([`retract_dropped`]).
pub(crate) struct Occurrences<'a> {
    terms: Vec<&'a Term>,
    predicates: Vec<&'a Predicate>,
}

/// The subjects a search found ([`Occurrences::holding`]).
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct Found {
    terms: FxHashSet<Term>,
    predicates: FxHashSet<Predicate>,
}

impl Found {
    fn contains(&self, subject: &Subject) -> bool {
        match subject {
            Subject::Term(term) => self.terms.contains(term),
            Subject::Predicate(predicate) => self.predicates.contains(predicate),
        }
    }
}

impl<'a> Occurrences<'a> {
    /// The terms `terms` and the predicates `predicates`, with every term the predicates carry.
    pub(crate) fn of(
        terms: impl IntoIterator<Item = &'a Term>,
        predicates: impl IntoIterator<Item = &'a Predicate>,
    ) -> Self {
        Self {
            terms: terms.into_iter().collect(),
            predicates: predicates.into_iter().collect(),
        }
    }

    /// Which of `subjects` occur here, as a subterm of a term or of a predicate's term, or as a
    /// sub-predicate.
    ///
    /// The search skips every subtree whose root carries the `evaluated` attribute, unless some
    /// subject carries it too. That loses no occurrence:
    /// - the attribute is hereditary: a node has it only if its children do (`ChildShape::add`
    ///   for every kind; the mark `Term::with_evaluated_cache` puts on an application requires
    ///   arguments that carry it), so an occurrence inside such a subtree carries it;
    /// - no term equal to a subject that lacks the attribute carries it. Without the mark, the
    ///   attribute is a function of the kind, and equal terms have equal kinds. The mark is
    ///   certified only on a ground term at which every equation of the definition failed to
    ///   match, a fact of the term alone; a subject is a term at which an equation attempt was
    ///   indeterminate (`IndeterminateAttempts`), which a failed match is not, and matching a
    ///   ground term is deterministic, so its equal twin is never certified.
    ///
    /// Debug builds compare the answer with the search that skips nothing.
    ///
    /// Cost: one walk of the predicates, and of the terms' nodes that lack the `evaluated`
    /// attribute (the part the simplifier itself walks), each shared node once, stopping as soon
    /// as every subject is found.
    pub(crate) fn holding(&self, subjects: &[&Subject]) -> Found {
        let (found, visited) = self.search(subjects, true);
        measure::add(Counter::SimplifyRetractionNodes, visited);
        debug_assert_eq!(
            found,
            self.search(subjects, false).0,
            "skipping evaluated subtrees loses no occurrence of a subject"
        );
        found
    }

    /// The subjects found, and the number of term nodes visited.
    fn search(&self, subjects: &[&Subject], skip_evaluated: bool) -> (Found, u64) {
        let mut missing_terms = FxHashSet::default();
        let mut missing_predicates = FxHashSet::default();
        for subject in subjects {
            match subject {
                Subject::Term(term) => {
                    missing_terms.insert(term);
                }
                Subject::Predicate(predicate) => {
                    missing_predicates.insert(predicate);
                }
            }
        }
        let skip_evaluated = skip_evaluated
            && missing_terms
                .iter()
                .all(|term| !term.attributes().evaluated);
        let mut found = Found::default();
        let mut pending_terms = self.terms.clone();
        if !missing_predicates.is_empty() || !missing_terms.is_empty() {
            let mut pending_predicates = self.predicates.clone();
            while let Some(predicate) = pending_predicates.pop() {
                if missing_predicates.remove(predicate) {
                    found.predicates.insert(predicate.clone());
                }
                match predicate {
                    Predicate::True | Predicate::False => {}
                    Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => {
                        pending_terms.push(term);
                    }
                    Predicate::Equals(left, right) | Predicate::In(left, right) => {
                        pending_terms.extend([left, right]);
                    }
                    Predicate::Absent(absence) => {
                        pending_terms.extend([absence.key(), absence.rest(), absence.joined()]);
                    }
                    Predicate::Not(inner)
                    | Predicate::Exists(_, inner)
                    | Predicate::Forall(_, inner) => {
                        pending_predicates.push(inner);
                    }
                    Predicate::And(inner) | Predicate::Or(inner) => {
                        pending_predicates.extend(inner);
                    }
                    Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
                        pending_predicates.extend([&**left, &**right]);
                    }
                }
            }
        }
        // Invariant: a node's children are pushed only the first time a node equal to it is
        // visited, so a subterm shared by several parents is walked once.
        let mut visited = FxHashSet::<&Term>::default();
        let mut count = 0;
        while !missing_terms.is_empty()
            && let Some(term) = pending_terms.pop()
        {
            if (skip_evaluated && term.attributes().evaluated) || !visited.insert(term) {
                continue;
            }
            count += 1;
            if missing_terms.remove(term) {
                found.terms.insert(term.clone());
            }
            if skip_evaluated {
                // The `evaluated` children would be skipped when popped: a collection's are
                // passed over through its trees' summaries instead.
                pending_terms.extend(crate::term::children_lacking(
                    term.kind(),
                    crate::term::Flag::Evaluated,
                ));
                continue;
            }
            match term.kind() {
                TermKind::And(left, right) => pending_terms.extend([left, right]),
                TermKind::Application { arguments, .. } => pending_terms.extend(arguments),
                TermKind::Injection { term, .. } => pending_terms.push(term),
                TermKind::Map { entries, rest, .. } => {
                    pending_terms.extend(entries.iter().flat_map(|(key, value)| [key, value]));
                    pending_terms.extend(rest);
                }
                TermKind::List { heads, rest, .. } => {
                    pending_terms.extend(heads);
                    if let Some((middle, tails)) = rest {
                        pending_terms.push(middle);
                        pending_terms.extend(tails);
                    }
                }
                TermKind::Set { elements, rest, .. } => {
                    pending_terms.extend(elements);
                    pending_terms.extend(rest);
                }
                TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
            }
        }
        (found, count)
    }
}

/// Run `action` with its emissions held in a [`Buffered`] instead of the current collector.
///
/// Without a current collector nothing is recorded either way, and the buffer is empty. If
/// `action` unwinds, its emissions are discarded and the current collector is restored.
pub(crate) fn buffer<T>(action: impl FnOnce() -> T) -> (T, Buffered) {
    struct Restore(Option<Sink>);
    impl Drop for Restore {
        fn drop(&mut self) {
            if let Some(enclosing) = self.0.take() {
                SINK.with(|sink| *sink.borrow_mut() = Some(enclosing));
            }
        }
    }
    let Some(enclosing) = SINK.with(|sink| {
        let mut sink = sink.borrow_mut();
        let enclosing = sink.take()?;
        *sink = Some(Sink {
            unit: true,
            emissions: Vec::new(),
        });
        Some(enclosing)
    }) else {
        return (action(), Buffered(Vec::new()));
    };
    let mut restore = Restore(Some(enclosing));
    let result = action();
    let inner = SINK
        .with(|sink| sink.borrow_mut().take())
        .map(|inner| inner.emissions)
        .unwrap_or_default();
    let enclosing = restore
        .0
        .take()
        .expect("the enclosing collector is restored once");
    SINK.with(|sink| *sink.borrow_mut() = Some(enclosing));
    (result, Buffered(inner))
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

    fn condition_failed(rule_id: &str, alternatives: usize) -> BackendDiagnostic {
        BackendDiagnostic::RuleConditionFailed {
            rule_id: rule_id.to_owned(),
            failure: SimplificationError::DisjunctiveResult {
                rule_id: "or-equation".to_owned(),
                alternatives,
            },
        }
    }

    /// A buffer records its emissions when it is committed, under the collector's rules; a
    /// dropped buffer records nothing, and neither does a nested buffer committed into it.
    /// Without a collector a buffer holds nothing.
    #[test]
    fn a_buffer_records_its_emissions_only_when_committed() {
        let ((), recorded) = collect(|| {
            emit(term_exhausted(1));
            let ((), kept) = buffer(|| {
                emit(term_exhausted(2));
                let ((), inner) = buffer(|| emit(term_exhausted(3)));
                inner.commit();
            });
            let ((), dropped) = buffer(|| {
                emit(term_exhausted(4));
                let ((), inner) = buffer(|| emit(term_exhausted(5)));
                inner.commit();
            });
            emit(term_exhausted(6));
            drop(dropped);
            kept.commit();
        });
        assert_eq!(
            recorded,
            [
                term_exhausted(1),
                term_exhausted(6),
                term_exhausted(2),
                term_exhausted(3)
            ]
        );

        let ((), held) = buffer(|| emit(term_exhausted(7)));
        assert!(held.0.is_empty());
        let ((), recorded) = collect(|| held.commit());
        assert!(recorded.is_empty());

        // A committed buffer is forwarded under the collector's rules: an unevaluated hook once.
        let ((), recorded) = collect(|| {
            emit(hook("H", UnsupportedHookReason::NotImplemented));
            let ((), repeated) = buffer(|| emit(hook("H", out_of_range())));
            repeated.commit();
        });
        assert_eq!(recorded, [hook("H", UnsupportedHookReason::NotImplemented)]);
    }

    /// A report committed for a kept subject survives a simplifier entry only if the entry's
    /// result holds the subject, as a subterm or inside a predicate; reports without a subject
    /// always survive, and a failed entry keeps every report. The outermost kept subject decides:
    /// a report raised inside an attempt whose own subject is then kept explains that subject.
    #[test]
    fn a_report_of_a_kept_subject_is_retracted_when_the_result_drops_it() {
        let variable =
            |name: &str| Term::variable(Variable::new(name, crate::term::Sort::simple("SortInt")));
        let (x, y) = (variable("X"), variable("Y"));
        let kept = |limit, subject: &Term| {
            let ((), held) = buffer(|| emit(term_exhausted(limit)));
            held.commit_kept(&Subject::Term(subject.clone()));
        };
        let entry = |result: Option<Predicate>| {
            collect(|| {
                retract_dropped(
                    || {
                        emit(term_exhausted(1));
                        kept(2, &x);
                        kept(3, &y);
                        // `Y` explained inside an attempt whose subject `X` is kept.
                        let ((), outer) = buffer(|| kept(4, &y));
                        outer.commit_kept(&Subject::Term(x.clone()));
                        result
                    },
                    |result| {
                        result
                            .as_ref()
                            .map(|predicate| Occurrences::of([], [predicate]))
                    },
                )
            })
            .1
        };
        let x_only = Predicate::Not(Box::new(Predicate::Ceil(x.clone())));
        assert_eq!(
            entry(Some(x_only)),
            [term_exhausted(1), term_exhausted(2), term_exhausted(4)]
        );
        assert_eq!(entry(Some(Predicate::True)), [term_exhausted(1)]);
        assert_eq!(
            entry(None),
            [
                term_exhausted(1),
                term_exhausted(2),
                term_exhausted(3),
                term_exhausted(4)
            ]
        );
        // A survivor keeps its subject, so an enclosing entry that drops it retracts it.
        let ((), recorded) = collect(|| {
            retract_dropped(
                || {
                    retract_dropped(
                        || {
                            kept(5, &x);
                            x.clone()
                        },
                        |result| Some(Occurrences::of([result], [])),
                    );
                    y.clone()
                },
                |result| Some(Occurrences::of([result], [])),
            );
        });
        assert!(recorded.is_empty(), "{recorded:?}");
    }

    /// Repeated attempts of a rule whose condition fails the same way report one fact; another
    /// rule, or another failure of the same rule, is another fact. Forwarding a nested collection
    /// applies the same rule.
    #[test]
    fn a_rule_condition_failure_is_recorded_once_per_rule_and_failure() {
        let emit_failures = || {
            emit(condition_failed("r1", 2));
            emit(condition_failed("r1", 2));
            emit(condition_failed("r2", 2));
            emit(condition_failed("r1", 3));
            emit(condition_failed("r2", 2));
        };
        let expected = [
            condition_failed("r1", 2),
            condition_failed("r2", 2),
            condition_failed("r1", 3),
        ];

        let ((), direct) = collect(emit_failures);
        assert_eq!(direct, expected);

        let (((), inner), outer) = collect(|| {
            emit(condition_failed("r1", 2));
            collect(emit_failures)
        });
        assert_eq!(inner, expected);
        assert_eq!(outer, expected);
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
    fn separately_collected_lists_merge_in_emission_order() {
        let ((first, second), _) = collect(|| {
            let ((), first) = collect_unit(|| {
                emit(term_exhausted(1));
                collect_unit(|| emit(term_exhausted(2)));
                emit_rule_condition_budget_exhausted("r1", 3);
            });
            let ((), second) = collect_unit(|| emit(hook("H", out_of_range())));
            (first, second)
        });
        // `first` holds 1, 2 and the pair in order; `second` was emitted after all of them.
        let owned_second = first
            .iter()
            .filter(|sequenced| sequenced.diagnostic == term_exhausted(2))
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(
            in_emission_order([second.as_slice(), first.as_slice(), owned_second.as_slice()]),
            vec![
                term_exhausted(1),
                term_exhausted(2),
                predicates_exhausted(3),
                rule_condition("r1", 3),
                hook("H", out_of_range()),
            ]
        );
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

    fn variable(name: &str) -> Variable {
        Variable::new(name, crate::term::Sort::simple("SortS"))
    }

    fn equals(left: &str, right: &str) -> Predicate {
        Predicate::Equals(
            crate::term::Term::variable(variable(left)),
            crate::term::Term::variable(variable(right)),
        )
    }

    fn explained(rule_variables: &[ConditionRuleVariable]) -> Vec<(String, String)> {
        rule_variables
            .iter()
            .map(|rule_variable| {
                (
                    encode_variable_name(&rule_variable.variable.name),
                    rule_variable.definition_name.clone(),
                )
            })
            .collect()
    }

    /// Each variable of the attempt's list that the predicates name free is explained with its
    /// definition name. Membership comes from the list: a variable of the subject that carries
    /// an equation's marker (`Eq#VarZ`, another equation's variable), a mint, and a request
    /// variable are not explained, and a listed variable the predicates only bind is not either.
    #[test]
    fn a_condition_names_the_equation_variables_it_mentions() {
        let predicates = [
            equals("Eq#VarY", "VarZ"),
            equals("Eq#VarW!apart2", "Rule#X!3"),
            equals("Eq#VarZ", "Eq#VarY"),
            Predicate::Exists(variable("Eq#VarB"), Box::new(equals("Eq#VarB", "VarZ"))),
        ];
        let listed = [
            variable("Eq#VarY"),
            variable("Eq#VarW!apart2"),
            variable("Eq#VarB"),
        ];
        let (printable, rule_variables) = printable_condition(&predicates, &listed);
        assert!(matches!(printable, Cow::Borrowed(_)));
        assert_eq!(
            explained(&rule_variables),
            [
                ("Eq-hVarW-bapart2".to_owned(), "VarW".to_owned()),
                ("Eq-hVarY".to_owned(), "VarY".to_owned()),
            ]
        );

        // Nothing listed: the same predicates explain nothing, whatever their names look like.
        let (printable, rule_variables) = printable_condition(&predicates, &[]);
        assert!(matches!(printable, Cow::Borrowed(_)));
        assert!(rule_variables.is_empty());
    }

    /// A request variable spelled like the escape of an equation variable keeps its name; the
    /// equation variable is renamed apart for printing, avoiding every spelling in the
    /// predicates, free or bound.
    #[test]
    fn an_equation_variable_printed_like_a_request_variable_is_renamed_apart() {
        let predicates = [
            equals("Eq#VarY", "Eq-hVarY"),
            Predicate::Exists(
                variable("Eq-hVarY-bapart0"),
                Box::new(equals("Eq-hVarY-bapart0", "Eq#VarY")),
            ),
        ];
        let (printable, rule_variables) = printable_condition(&predicates, &[variable("Eq#VarY")]);
        assert_eq!(
            explained(&rule_variables),
            [("Eq-hVarY-bapart1".to_owned(), "VarY".to_owned())]
        );
        assert_eq!(
            printable.as_ref(),
            [
                equals("Eq#VarY!apart1", "Eq-hVarY"),
                Predicate::Exists(
                    variable("Eq-hVarY-bapart0"),
                    Box::new(equals("Eq-hVarY-bapart0", "Eq#VarY!apart1")),
                ),
            ]
        );
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
