//! Bindings of fired instances: for each axiom, the symbols a request names that were the head
//! of a value an instance of it took as an operand, and the values selected template binders
//! were bound to.
//!
//! A run that collects coverage and asks for bindings (`rewrite::ExecutionOptions::
//! collect_bindings`, a [`BindingCollection`]) reads, at every fired instance, the substitution
//! its match produced:
//! - a rewrite rule's instance is fired where the run committed to its successor, the site of
//!   `committed` (`rewrite::execute`'s `note_committed`): the substitution is read where the step
//!   built the successor (`rewrite::apply`'s `apply_rhs_alternative`), carried with the
//!   successor, and recorded only when its own normalization showed it defined, so a candidate
//!   the step rolled back, an undefined-step entry, a cut-point rule's proposed successor and a
//!   successor a stop or the work budget cut before its normalization finished record nothing;
//! - a term equation's instance (function, `anywhere`, overload or simplification) is fired
//!   where it gave a result, at the sites of `applied` that have its substitution: the
//!   simplifier's equation result (`simplify::equation_instance_result`, including a subject
//!   stated empty by a refuted binding obligation and a `\bottom` result), and the definedness
//!   decisions' one function-equation step that gave a value or decided an operand
//!   (`deferred`: D1 and D4).
//!
//! Ceil, predicate and `#Top` equations record nothing: they state a predicate about a term
//! (its definedness or its truth), not a step of its evaluation. A matched instance whose
//! condition was refuted, left undecided or stopped gave no result and records nothing.
//!
//! # Operand heads
//!
//! For each variable `x` the left-hand side binds (a variable of the axiom that is not among
//! the ones only its condition, right-hand side or `ensures` mention), the head of `θ(x)` is
//! read through injections: the symbol of the first application below any number of
//! `inj{_, _}`. It is recorded for the axiom when the collection names it
//! ([`BindingCollection::symbols`]). A domain value, a variable, a collection or a term-level
//! conjunction has no head and records nothing. A continuation variable binds a sequence, whose
//! head is the sequence's own constructor, so the rest of a program is never recorded unless
//! the request names that constructor.
//!
//! # Template binder values
//!
//! A request selects binders as (axiom, variable, cap) ([`BindingCollection::binders`]): the
//! axiom by its `UNIQUE_ID` or label, the variable by its name as the definition writes it
//! (`term::names::rule_variable_definition_name`: without the marker of a rule's or an
//! equation's own variable and without the suffix of a renaming apart from a subject). At a
//! fired instance of the axiom, an `Int` literal bound to the variable (through injections) is
//! inserted into the binder's set; any other value
//! (a term with variables or applications, or a value of another sort) sets
//! [`BinderValues::nonliteral`]. The set keeps the least `cap` values in the order of the
//! integers and [`BinderValues::truncated`] says whether a further value was left out, so what
//! is kept is a function of the full set, never of the order the instances came in.
//!
//! # Determinism and cost
//!
//! Every field is a union over the run's fired instances of a function of the instance, so it
//! depends on neither the multiplicity nor the order of the instances, and it is a deterministic
//! function of the same inputs as `applied` and `committed`. What a memo serves records as
//! `applied` does: a condition verdict the memo of verdicts serves (`simplify::ConditionMemo`,
//! which keeps only refuted and undecided verdicts, and none in an execution) records nothing
//! of the equations its decision applied, which recorded when the verdict was decided in the
//! same scope.
//!
//! The collection adds no evaluation: it reads the substitution the step's match already made
//! and evaluates, simplifies, matches and decides nothing. Per fired equation instance, and per
//! candidate a rewrite step builds (also one later rolled back, whose reading is dropped), it
//! costs one pass over the substitution: for each binding, two lookups in the axiom's variable
//! sets, a walk down injections, and one hash lookup of the head; for a selected binder, one
//! insert into its ordered set, O(log cap). That is at most linear in the bindings the run's
//! matches produced, so the collection's cost is bounded by a constant factor of the run's
//! matching work. Asking for bindings changes no other field of the result.

use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use num_bigint::BigInt;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    definition::BackendDefinition,
    rule::RuleAttributes,
    substitution::Substitution,
    term::{DomainKind, Name, Term, TermKind, Variable, names::rule_variable_definition_name},
};

/// What a run's binding collection records: the symbols whose occurrence as the head of an
/// operand is recorded, and the selected template binders with their caps.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BindingCollection {
    /// The symbols recorded as operand heads, by KORE name (`Lbl...`).
    pub symbols: BTreeSet<String>,
    /// The selected binders, each with the most values it keeps.
    pub binders: BTreeMap<BinderKey, usize>,
}

impl BindingCollection {
    /// The symbols `symbols`, with no binder selected.
    pub fn new<S: Into<String>>(symbols: impl IntoIterator<Item = S>) -> Self {
        Self {
            symbols: symbols.into_iter().map(Into::into).collect(),
            binders: BTreeMap::new(),
        }
    }

    /// Select the binder `variable` of `axiom`, keeping its least `cap` values.
    #[must_use]
    pub fn with_binder(
        mut self,
        axiom: impl Into<String>,
        variable: impl Into<String>,
        cap: usize,
    ) -> Self {
        self.binders.insert(
            BinderKey {
                axiom: axiom.into(),
                variable: variable.into(),
            },
            cap,
        );
        self
    }
}

/// A template binder: a variable of an axiom.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinderKey {
    /// The axiom, by its `UNIQUE_ID` or its label, as the request names it.
    pub axiom: String,
    /// The variable, by its name as the definition writes it.
    pub variable: String,
}

/// What a run's fired instances bound ([`super::RunCoverage::bindings`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub struct RunBindings {
    /// Per axiom with at least one recorded head, the named symbols that were the head of an
    /// operand of a fired instance of it, sorted by axiom id.
    pub operands: Vec<AxiomOperands>,
    /// Per selected binder bound at some fired instance, the values it took, sorted by binder.
    pub binders: Vec<BinderValues>,
}

/// The operand heads of one axiom's fired instances.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct AxiomOperands {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The named symbols that were the head of a value bound to a left-hand-side variable.
    pub symbols: BTreeSet<String>,
}

/// The values one selected binder took at the fired instances of its axiom.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct BinderValues {
    /// The binder, as the request names it.
    pub binder: BinderKey,
    /// The `Int` literals bound to it: the least `cap` of them, ascending.
    pub values: Vec<BigInt>,
    /// Whether a further literal was bound that the cap left out.
    pub truncated: bool,
    /// Whether some fired instance bound it to a value that is no `Int` literal.
    pub nonliteral: bool,
}

/// What one fired instance bound, read from its substitution ([`read`]) and recorded once the
/// instance fired ([`note`]): the named heads of its operands and the values of its selected
/// binders, by binder slot.
#[derive(Debug)]
pub(crate) struct Fired {
    heads: Vec<Name>,
    values: Vec<(usize, Option<BigInt>)>,
}

/// A fired instance's reading carried with a rewrite step's successor until the run commits to
/// it (`rewrite::AppliedRule`). It describes how the run was observed, not the step: equality
/// ignores it, so collecting bindings changes no compared field.
#[derive(Clone, Default)]
pub(crate) struct CarriedBindings(pub(crate) Option<Arc<Fired>>);

impl PartialEq for CarriedBindings {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for CarriedBindings {}

impl std::fmt::Debug for CarriedBindings {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(if self.0.is_some() { "Some(..)" } else { "None" })
    }
}

thread_local! {
    /// Whether the innermost open coverage collection collects bindings.
    static RECORDING: Cell<bool> = const { Cell::new(false) };
    /// What it has collected.
    static SINK: RefCell<Option<Sink>> = const { RefCell::new(None) };
}

/// The bindings of one collection.
pub(super) struct Sink {
    symbols: FxHashSet<String>,
    /// The selected binders in key order, with their caps; a slot is a position here.
    binders: Vec<(BinderKey, usize)>,
    /// The binder slots of an axiom, by `UNIQUE_ID`, resolved on its first fired instance.
    resolved: FxHashMap<String, Arc<[usize]>>,
    operands: FxHashMap<String, FxHashSet<Name>>,
    values: Vec<Slot>,
}

/// What a binder's instances bound so far.
#[derive(Default)]
struct Slot {
    bound: bool,
    values: BTreeSet<BigInt>,
    truncated: bool,
    nonliteral: bool,
}

impl Sink {
    pub(super) fn new(collection: BindingCollection) -> Self {
        let binders = collection.binders.into_iter().collect::<Vec<_>>();
        let values = binders.iter().map(|_| Slot::default()).collect();
        Self {
            symbols: collection.symbols.into_iter().collect(),
            binders,
            resolved: FxHashMap::default(),
            operands: FxHashMap::default(),
            values,
        }
    }

    pub(super) fn finish(self) -> RunBindings {
        let mut operands = self
            .operands
            .into_iter()
            .filter(|(_, symbols)| !symbols.is_empty())
            .map(|(axiom, symbols)| AxiomOperands {
                axiom,
                symbols: symbols.iter().map(|symbol| symbol.to_string()).collect(),
            })
            .collect::<Vec<_>>();
        operands.sort_by(|left, right| left.axiom.cmp(&right.axiom));
        let binders = self
            .binders
            .into_iter()
            .zip(self.values)
            .filter(|(_, slot)| slot.bound)
            .map(|((binder, _), slot)| BinderValues {
                binder,
                values: slot.values.into_iter().collect(),
                truncated: slot.truncated,
                nonliteral: slot.nonliteral,
            })
            .collect();
        RunBindings { operands, binders }
    }

    /// The binder slots of the axiom `attributes` names.
    fn slots(&mut self, attributes: &RuleAttributes) -> Arc<[usize]> {
        if self.binders.is_empty() {
            return Arc::from([]);
        }
        if let Some(slots) = self.resolved.get(&attributes.unique_id) {
            return Arc::clone(slots);
        }
        let slots = self
            .binders
            .iter()
            .enumerate()
            .filter(|(_, (binder, _))| {
                binder.axiom == attributes.unique_id
                    || attributes.label.as_deref() == Some(binder.axiom.as_str())
            })
            .map(|(slot, _)| slot)
            .collect::<Arc<[usize]>>();
        self.resolved
            .insert(attributes.unique_id.clone(), Arc::clone(&slots));
        slots
    }

    fn note(&mut self, axiom: &str, fired: &Fired) {
        if !fired.heads.is_empty() {
            let heads = if let Some(heads) = self.operands.get_mut(axiom) {
                heads
            } else {
                self.operands.entry(axiom.to_owned()).or_default()
            };
            for head in &fired.heads {
                if !heads.contains(head) {
                    heads.insert(Arc::clone(head));
                }
            }
        }
        for (slot, value) in &fired.values {
            let cap = self.binders[*slot].1;
            let slot = &mut self.values[*slot];
            slot.bound = true;
            match value {
                None => slot.nonliteral = true,
                Some(value) => {
                    if slot.values.contains(value) {
                        continue;
                    }
                    slot.values.insert(value.clone());
                    if slot.values.len() > cap {
                        slot.values.pop_last();
                        slot.truncated = true;
                    }
                }
            }
        }
    }
}

/// Install `sink` as the innermost collection's bindings, returning the enclosing one's.
pub(super) fn replace(sink: Option<Sink>) -> Option<Sink> {
    RECORDING.set(sink.is_some());
    SINK.replace(sink)
}

/// Whether the innermost open collection collects bindings.
#[inline]
pub(super) fn recording() -> bool {
    RECORDING.get()
}

/// Read what an instance of the axiom `attributes` names, whose variables are `variables` of
/// which `unbound` are not bound by its left-hand side, bound under `substitution`: the named
/// heads of its operands and the values of its selected binders. `None` when it bound nothing
/// the collection records. The caller has checked that the open collection collects bindings.
pub(super) fn read(
    definition: &BackendDefinition,
    attributes: &RuleAttributes,
    variables: &BTreeSet<Variable>,
    unbound: &BTreeSet<Variable>,
    substitution: &Substitution,
) -> Option<Fired> {
    SINK.with_borrow_mut(|sink| {
        let sink = sink.as_mut()?;
        let slots = sink.slots(attributes);
        let mut heads = Vec::new();
        let mut values = Vec::new();
        for (variable, value) in substitution {
            if !variables.contains(variable) || unbound.contains(variable) {
                continue;
            }
            if let Some(head) = head(value)
                && sink.symbols.contains(&**head)
            {
                heads.push(Arc::clone(head));
            }
            if slots.is_empty() {
                continue;
            }
            let written = rule_variable_definition_name(&variable.name);
            for &slot in slots.iter() {
                if sink.binders[slot].0.variable == written {
                    values.push((slot, int_literal(definition, value)));
                }
            }
        }
        (!heads.is_empty() || !values.is_empty()).then_some(Fired { heads, values })
    })
}

/// Record `fired`, read from an instance of the axiom `axiom` that fired, into the open
/// collection.
pub(super) fn note(axiom: &str, fired: &Fired) {
    SINK.with_borrow_mut(|sink| {
        if let Some(sink) = sink.as_mut() {
            sink.note(axiom, fired);
        }
    });
}

/// The head of `term` through injections: the symbol of its first application below them.
fn head(term: &Term) -> Option<&Name> {
    let mut term = term;
    loop {
        match term.kind() {
            TermKind::Injection { term: inner, .. } => term = inner,
            TermKind::Application { symbol, .. } => return Some(&symbol.name),
            _ => return None,
        }
    }
}

/// The integer `term` is through injections, when it is an `Int` literal.
fn int_literal(definition: &BackendDefinition, term: &Term) -> Option<BigInt> {
    let mut term = term;
    loop {
        match term.kind() {
            TermKind::Injection { term: inner, .. } => term = inner,
            TermKind::DomainValue { sort, value }
                if definition.domain_kind(sort) == Some(DomainKind::Int) =>
            {
                return std::str::from_utf8(value.as_bytes()).ok()?.parse().ok();
            }
            _ => return None,
        }
    }
}
