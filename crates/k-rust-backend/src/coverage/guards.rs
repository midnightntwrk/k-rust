//! Guard outcomes: for the rules and equations a run names, which outcomes each node of their
//! `requires` took on the entries the run made, where the node was reached.
//!
//! A run that collects coverage and names axioms (`rewrite::ExecutionOptions::collect_guards`)
//! evaluates, at every site that notes an axiom `matched` for a condition it decides (a rewrite
//! rule's `requires` phase, an equation's condition evaluation, the definedness decision's
//! one-step selection), the written `requires` under the entry's bindings, with the evaluation
//! condition records use (`conditions::Evaluation`: isolated from the run, solver-free,
//! bottom-up, off the run's clock and bounded by a budget of polls). It keeps no record per
//! entry. It folds each entry into per-node sets of reached outcomes, a set of guard outcomes,
//! and a bounded set of valuation combinations, all per axiom ([`AxiomGuard`]).
//!
//! # Untried entries
//!
//! An equation states its value at the arguments its left-hand side matches where its
//! `requires` holds and no equation of a higher priority group applies. So its guard decides
//! something at exactly the applications its left-hand side matches whose deciding group (the
//! first, in priority order, that applies or blocks) is its own. A function scan tries the
//! equations of a group in an order the definition does not state and stops at the first that
//! applies, so the tried entries alone would depend on that order: of two equations
//! `f(A) = .. requires A <Int 32768` and `f(A) = .. requires A >=Int 32768`, the one tried
//! second would never be seen false.
//!
//! Where a function scan applies an equation, each named equation of the same group after it
//! therefore gets an untried entry for each instance whose matching is decided
//! (`simplify::scan::enter_untried_guards`, [`enter_untried`]). The equations before it were
//! tried, and a group that blocks was tried in full, so every equation of the deciding group
//! whose left-hand side matches has an entry, whatever the order. A lower group, `owise`
//! included, states nothing where a higher group applies, and gets none. An untried entry is
//! evaluated as a tried one is, with the same bounds and the same cache, so an entry's outcomes
//! do not depend on whether the run tried it first. Its guard outcome is read from that
//! evaluation, since there is no attempt: the first conjunct that is not `true` decides it,
//! `held` where there is none, refuted where it is `false` or undefined (whatever the later
//! conjuncts are), and `undecided` with cause [`AttemptCause::Untried`] where it is undecided.
//! No solver is asked: the evaluation shares no solver state with the run.
//!
//! A function applied inside an untried entry's evaluation is applied by the record, not by the
//! run: the evaluation is isolated (`coverage::isolated`), so it reports to no coverage set and
//! makes no entry of its own, as for a tried entry. The matching that finds the instances is
//! isolated as a probe is (`coverage::offer`). Equations holding a literal whose element the
//! definition leaves open are skipped, since their attempt rests on an element the run marks
//! and an untried entry cannot.
//!
//! # Reached outcomes
//!
//! A node's outcome counts for an entry only where the node is reached, in written order, the
//! same way for every connective:
//! - an operand of a conjunction (`andBool`, `andThenBool`, `\and`, and the conjuncts of the
//!   `requires` itself) is reached where its conjunction is and every operand written before it
//!   is `true`;
//! - an operand of a disjunction (`orBool`, `orElseBool`, `\or`) where every operand before it
//!   is `false`;
//! - the right operand of `impliesBool` and `\implies`, read as `notBool A orBool B`, where the
//!   left one is `true`;
//! - both operands of `xorBool` and `\iff`, and the operand of `notBool`, `\not` and
//!   `\equals(b, literal)`, where their node is.
//!
//! K reads `andBool` and `andThenBool` alike wherever either is defined (both are strict, the
//! definedness of the operand `andThenBool` does not evaluate is still required), so two
//! notations of one function give one report. With this rule the set of reached outcomes of
//! each node encodes the short-circuit outcome classes of every connective: for `A && B`, "A
//! false" is A's `false`, "A true and B false" is B's `false`, and "both true" is the
//! conjunction's `true`. An outcome the evaluation computed for a node that was not reached
//! decided nothing in the run's reading and is discarded.
//!
//! An undecided node adds `undecided` with a cause read from the entry
//! ([`OperandCause`]), and its later siblings in a conjunction or disjunction are not reached: no
//! outcome is claimed that was not decided.
//!
//! # Guard outcomes
//!
//! The guard outcome of a tried entry is the verdict of the attempt, the run's own decision with
//! the solver where it used one ([`GuardOutcome`]); a refutation is split by the record's root
//! truth ([`Refutation`]). An untried entry's is read from its evaluation (above). An entry adds
//! its node outcomes, its guard outcome and its combination when the site reports its verdict, so
//! an entry whose condition completed its match and re-entered the attempt adds nothing (it decided
//! nothing: its re-entry, with the bindings the condition gave, is an entry of its own), and
//! neither does an entry an unwinding leaves without a verdict.
//!
//! # Valuation combinations
//!
//! Each entry with a guard outcome also adds one [`Combination`]: the truth of every atom of
//! the written condition under the entry (also an atom the short-circuit reading did not reach,
//! as the strict reading defines it) with the guard outcome. A pair of combinations that differ
//! only in one atom and in their outcome shows that atom deciding the guard by itself, which a
//! reader can compute from the stored set without a run. The set kept is the least
//! [`GuardCollection::combination_limit`] combinations in their order, so it is a function of
//! the full set, whatever order the entries came in, and [`AxiomGuard::combinations_truncated`]
//! says whether any was left out.
//!
//! # Determinism and cost
//!
//! The sets are a deterministic function of the same inputs as `matched`: each is a union over
//! the run's distinct entries of a function of the entry, so it does not depend on an entry's
//! multiplicity, the run's order, memo hits or state-set merges. The untried entries are a
//! function of the applications the run decides, the equations of their groups and the
//! instances their left-hand sides give; an application whose untried entries were made is
//! recognized by a bounded cache of its own ([`untried_application`]), which changes only the
//! cost. Entries are recognized by a
//! bounded per-run cache ([`GuardCollection::cache_keys`]): a repeated entry is not evaluated
//! again, and a miss (the cache is cleared when full, and an entry whose key holds more than
//! [`GuardCollection::max_value_size`] term nodes is never cached) costs one more evaluation,
//! never a lost or changed outcome. Nothing of an entry is kept past the cache, so a long run
//! holds no state alive through it. Asking for guards changes no other field of the result.
//!
//! Each distinct entry costs one evaluation of its condition, of at most
//! [`GuardCollection::record_polls`] polls. The evaluation is isolated, so it shares no work with
//! the run's own decision of the condition nor with another entry's evaluation (an execution
//! keeps no normal forms, and the condition memo is set aside): a condition that applies
//! functions pays for their evaluation again. Where a function's condition reads its own
//! application on a smaller argument (`f(N) = .. requires f(N -Int 1) >Int 0`), a run that
//! evaluates `f` to depth `n` makes `n` entries whose evaluations apply `f` about `n²/2` times,
//! where the run applies it `n` times. The bound is per entry: the collection costs at most the
//! run's distinct entries of the named axioms times `record_polls` polls. An untried entry
//! counts as any other: a decided application adds at most one per instance of each matching
//! equation after the applied one in its group, and an untried guard whose evaluation diverges
//! where an earlier equation applies (one that recurses on an argument an earlier conjunct
//! guards against) costs its `record_polls` polls and reads `undecided: stopped` past the
//! operands it decided.
//!
//! A verdict is reported by entry handle ([`GuardHandle`]), not through a thread-local slot:
//! deciding one equation's condition applies other equations, so decisions nest.

use std::{cell::Cell, cell::RefCell, collections::BTreeSet, num::NonZeroU32};

use rustc_hash::{FxHashMap, FxHashSet};

use super::conditions::{
    ConditionNode, Connective, EntryKey, Evaluation, RecordedValue, SharedEvaluation, Truth,
    is_boolean, nodes_up_to, written,
};
use crate::{
    definition::BackendDefinition,
    rule::{Predicate, RuleAttributes},
    simplify::SimplificationOptions,
    substitution::{Substitution, substitute},
    term::{Term, TermKind, Variable},
};

/// The entries a run's guard cache recognizes unless the request says otherwise
/// ([`GuardCollection::cache_keys`]).
pub const DEFAULT_GUARD_CACHE_KEYS: usize = 4_096;

/// The valuation combinations a run keeps per axiom unless the request says otherwise
/// ([`GuardCollection::combination_limit`]).
pub const DEFAULT_COMBINATION_LIMIT: usize = 256;

/// Which axioms' guard outcomes a run collects, and its bounds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GuardCollection {
    /// The rules and equations whose entries are folded, each named by its `UNIQUE_ID` or its
    /// label. A name that is neither, or an axiom with an empty `requires`, collects nothing.
    pub axioms: BTreeSet<String>,
    /// The largest entry key, in term nodes, the cache keeps; a larger entry is evaluated every
    /// time the run makes it. Also the cap on the values the evaluation classifies, which only
    /// tells a symbolic operand from an unevaluated one.
    pub max_value_size: usize,
    /// The most polls one entry's evaluation may make: its work bound, since it runs off the
    /// run's clock (`coverage::isolated`). What the bound stops is `undecided: stopped`.
    pub record_polls: u64,
    /// The most entries the cache recognizes before it is cleared.
    pub cache_keys: usize,
    /// The most valuation combinations kept per axiom: the least ones in their order.
    pub combination_limit: usize,
}

impl GuardCollection {
    /// The axioms `axioms`, with the default bounds.
    pub fn new<S: Into<String>>(axioms: impl IntoIterator<Item = S>) -> Self {
        Self {
            axioms: axioms.into_iter().map(Into::into).collect(),
            max_value_size: super::DEFAULT_MAX_VALUE_SIZE,
            record_polls: super::DEFAULT_RECORD_POLLS,
            cache_keys: DEFAULT_GUARD_CACHE_KEYS,
            combination_limit: DEFAULT_COMBINATION_LIMIT,
        }
    }

    fn selects(&self, attributes: &RuleAttributes) -> bool {
        self.axioms.contains(&attributes.unique_id)
            || attributes
                .label
                .as_ref()
                .is_some_and(|label| self.axioms.contains(label))
    }
}

/// The guard outcomes of one axiom ([`super::RunCoverage::guards`]).
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct AxiomGuard {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The nodes of the written `requires`, in preorder, each with its reached outcomes.
    pub nodes: Vec<GuardNode>,
    /// The guard outcomes of the entries.
    pub outcomes: BTreeSet<GuardOutcome>,
    /// The valuation combinations, the least [`GuardCollection::combination_limit`] in their
    /// order.
    pub combinations: Vec<Combination>,
    /// Whether the run made a further combination that the limit left out.
    pub combinations_truncated: bool,
}

/// A node of the written `requires`.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct GuardNode {
    /// The node's position: the conjunct's index, then the index of each operand on the way
    /// down.
    pub path: Vec<u32>,
    pub shape: GuardShape,
    /// The outcomes the node took on the entries where it was reached.
    pub reached: BTreeSet<NodeOutcome>,
}

/// What a node is, as written. Variables are named as the axiom writes them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GuardShape {
    /// A connective; its operands are the next nodes whose path extends this one's by one.
    Connective(Connective),
    /// `\equals(b, literal)` of a Boolean term `b`; a K `requires b` is `\equals(b, true)`.
    Equals(bool),
    /// A Boolean term that is no connective.
    Term(Term),
    /// A predicate that is no connective and no `\equals(b, literal)`.
    Predicate(Predicate),
}

impl GuardShape {
    /// Whether the node is an atom (no connective, no `\equals(b, literal)`).
    pub fn is_atom(&self) -> bool {
        matches!(self, Self::Term(_) | Self::Predicate(_))
    }
}

/// An outcome of a reached node under one entry.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NodeOutcome {
    True,
    False,
    /// A Boolean node denotes no value under the entry.
    Undefined,
    /// The solver-free evaluation left the node undecided.
    Undecided(OperandCause),
}

/// Why the evaluation left a node undecided.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OperandCause {
    /// The node's instance has variables (a variable the match left unbound, or bound to a term
    /// with variables), so its truth depends on the path.
    Symbolic,
    /// The instance is variable-free but holds an application no equation evaluated.
    Unevaluated,
    /// The evaluation's own budget of polls or its stack ran out (or a cancellation came).
    Stopped,
}

/// The guard outcome of one entry: what the attempt decided about the condition.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum GuardOutcome {
    /// The condition holds for the instance.
    Held,
    /// The condition does not hold for the instance.
    Refuted(Refutation),
    /// The attempt could not decide the condition.
    Undecided(AttemptCause),
    /// A stop ended the attempt while it decided the condition.
    Stopped,
}

/// How a refuted entry's own evaluation reads its condition.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Refutation {
    /// The first reached conjunct that is false is false.
    False,
    /// The first reached conjunct that is false is `\equals(b, literal)` of an undefined `b`.
    Undefined,
    /// The evaluation found no conjunct false: the attempt's solver or its path condition
    /// refuted the condition.
    Decided,
}

/// Why an attempt left its condition undecided.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AttemptCause {
    /// The run has no solver.
    NoSolver,
    /// The solver answered unknown.
    SolverUnknown,
    /// The solver cannot translate the condition.
    Untranslatable,
    /// The path condition is inconsistent with the solver's ground truth.
    InconsistentPath,
    /// The solver failed otherwise.
    SolverError,
    /// The simplification of the condition failed.
    Simplification,
    /// The attempt goes on under the condition left open (an implication left undecided, a
    /// binding that is not functional, result variables the match does not bind), or a decision
    /// that only evaluates left it open.
    Open,
    /// The run did not try the entry (an untried entry, see the module documentation) and its
    /// solver-free evaluation left the condition open.
    Untried,
}

/// What an attempt decided about its condition, as a site reports it ([`verdict`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Decided {
    Held,
    Refuted,
    Undecided(AttemptCause),
    Stopped,
    /// The condition completed the match and the attempt re-entered with it.
    Reentered,
}

impl Decided {
    /// The verdict of a condition record (`conditions::Verdict`).
    pub(crate) fn verdict(self) -> super::Verdict {
        match self {
            Self::Held => super::Verdict::Held,
            Self::Refuted => super::Verdict::Refuted,
            Self::Undecided(_) => super::Verdict::Undecided,
            Self::Stopped => super::Verdict::Stopped,
            Self::Reentered => super::Verdict::Reentered,
        }
    }
}

/// One valuation of a guard's atoms with the entry's guard outcome.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Combination {
    /// The truth of each atom ([`GuardShape::is_atom`]), in preorder.
    pub atoms: Vec<Truth>,
    pub outcome: GuardOutcome,
}

/// An open entry, until its verdict ([`verdict`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct GuardHandle(NonZeroU32);

thread_local! {
    /// Whether the innermost open coverage collection collects guards.
    static RECORDING: Cell<bool> = const { Cell::new(false) };
    /// What it has collected.
    static SINK: RefCell<Option<Sink>> = const { RefCell::new(None) };
}

/// The guard outcomes of one collection.
pub(super) struct Sink {
    collection: GuardCollection,
    axioms: FxHashMap<String, Slot>,
    cache: FxHashMap<(String, EntryKey), Folded>,
    /// The applications whose untried entries were made ([`untried_application`]).
    applications: FxHashSet<ApplicationKey>,
    open: Vec<Option<(String, Folded)>>,
    free: Vec<usize>,
}

/// What the untried entries of a function application are a function of: the application, the
/// path conditions, and the position in its group of the equation that applied.
#[derive(Eq, Hash, PartialEq)]
struct ApplicationKey {
    term: Term,
    knowledge: Vec<Predicate>,
    applied: usize,
}

impl ApplicationKey {
    /// Whether the key holds more than `cap` term nodes, counting the application and every
    /// term of the path conditions, as an entry's key counts its own ([`EntryKey::exceeds`]).
    fn exceeds(&self, cap: usize) -> bool {
        let mut nodes = nodes_up_to(&self.term, cap);
        for predicate in &self.knowledge {
            predicate.visit_terms(&mut |term| {
                if nodes <= cap {
                    nodes += nodes_up_to(term, cap - nodes);
                }
            });
        }
        nodes > cap
    }
}

/// What an axiom's entries gave so far.
struct Slot {
    nodes: Vec<GuardNode>,
    /// The written variables of each node, in preorder.
    variables: Vec<BTreeSet<Variable>>,
    outcomes: BTreeSet<GuardOutcome>,
    combinations: BTreeSet<Combination>,
    truncated: bool,
}

/// What an entry's evaluation gave, which its verdict folds into its axiom's slot.
#[derive(Clone)]
struct Folded {
    /// The outcome of each reached node, by preorder index.
    reached: Vec<(usize, NodeOutcome)>,
    refutation: Refutation,
    atoms: Vec<Truth>,
    /// The guard outcome of the entry where the run did not try it: read from the evaluation
    /// alone ([`enter_untried`]).
    untried: GuardOutcome,
}

impl Sink {
    pub(super) fn new(collection: GuardCollection) -> Self {
        Self {
            collection,
            axioms: FxHashMap::default(),
            cache: FxHashMap::default(),
            applications: FxHashSet::default(),
            open: Vec::new(),
            free: Vec::new(),
        }
    }

    /// The outcomes by axiom id.
    pub(super) fn finish(self) -> Vec<AxiomGuard> {
        let mut axioms = self
            .axioms
            .into_iter()
            .map(|(axiom, slot)| AxiomGuard {
                axiom,
                nodes: slot.nodes,
                outcomes: slot.outcomes,
                combinations: slot.combinations.into_iter().collect(),
                combinations_truncated: slot.truncated,
            })
            .collect::<Vec<_>>();
        axioms.sort_by(|left, right| left.axiom.cmp(&right.axiom));
        axioms
    }

    fn open(&mut self, axiom: String, folded: Folded) -> Option<GuardHandle> {
        let position = if let Some(position) = self.free.pop() {
            self.open[position] = Some((axiom, folded));
            position
        } else {
            self.open.push(Some((axiom, folded)));
            self.open.len() - 1
        };
        u32::try_from(position + 1)
            .ok()
            .and_then(NonZeroU32::new)
            .map(GuardHandle)
    }

    fn close(&mut self, handle: GuardHandle, decided: Decided) {
        let position = handle.0.get() as usize - 1;
        let Some((axiom, folded)) = self.open.get_mut(position).and_then(Option::take) else {
            return;
        };
        self.free.push(position);
        let outcome = match decided {
            Decided::Held => GuardOutcome::Held,
            Decided::Refuted => GuardOutcome::Refuted(folded.refutation),
            Decided::Undecided(cause) => GuardOutcome::Undecided(cause),
            Decided::Stopped => GuardOutcome::Stopped,
            Decided::Reentered => return,
        };
        self.add(&axiom, folded, outcome);
    }

    /// Fold an entry of `axiom` with the guard outcome `outcome` into its slot.
    fn add(&mut self, axiom: &str, folded: Folded, outcome: GuardOutcome) {
        let limit = self.collection.combination_limit;
        let Some(slot) = self.axioms.get_mut(axiom) else {
            return;
        };
        for (index, reached) in folded.reached {
            if let Some(node) = slot.nodes.get_mut(index) {
                node.reached.insert(reached);
            }
        }
        slot.outcomes.insert(outcome);
        let combination = Combination {
            atoms: folded.atoms,
            outcome,
        };
        if slot.combinations.contains(&combination) {
            return;
        }
        slot.combinations.insert(combination);
        if slot.combinations.len() > limit {
            slot.combinations.pop_last();
            slot.truncated = true;
        }
    }
}

/// The skeleton of the written `requires` of every rewrite rule and function equation of
/// `definition` that `axioms` names by `UNIQUE_ID` or label and whose `requires` is not empty:
/// each axiom's nodes as a run that enters it reports them, none reached, with no outcome and no
/// combination, by `UNIQUE_ID`. A run reports an axiom only once it entered its condition, so
/// this is what tells a reader the nodes of a guard no run entered: the skeleton is a function of
/// the axiom's written `requires` alone, the same predicates every entry site folds
/// ([`enter`]), so it is the skeleton a run that enters the axiom reports. An axiom that
/// several left-hand side alternatives compile to has one skeleton.
pub fn skeletons(definition: &BackendDefinition, axioms: &BTreeSet<String>) -> Vec<AxiomGuard> {
    let collection = GuardCollection::new(axioms.iter().cloned());
    let rewrites = definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .map(|rule| rule.rule.as_ref());
    let equations = definition
        .function_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .map(|rule| rule.as_ref());
    let mut found = std::collections::BTreeMap::new();
    for rule in rewrites.chain(equations) {
        let requires = rule.requires.conjuncts();
        if requires.is_empty() || !collection.selects(&rule.attributes) {
            continue;
        }
        found
            .entry(rule.attributes.unique_id.clone())
            .or_insert_with(|| Slot::of(requires).nodes);
    }
    found
        .into_iter()
        .map(|(axiom, nodes)| AxiomGuard {
            axiom,
            nodes,
            outcomes: BTreeSet::new(),
            combinations: Vec::new(),
            combinations_truncated: false,
        })
        .collect()
}

/// Install `sink` as the innermost collection's guards, returning the enclosing one's.
pub(super) fn replace(sink: Option<Sink>) -> Option<Sink> {
    RECORDING.set(sink.is_some());
    SINK.replace(sink)
}

/// Whether the innermost open collection collects guards.
#[inline]
pub(super) fn recording() -> bool {
    RECORDING.get()
}

/// Fold the entry of the axiom `attributes` names, whose written `requires` is `requires`,
/// under `substitution`, with the path and match conditions `knowledge`, when the open
/// collection names it; `shared` is the evaluation a condition record of the same entry made,
/// read when its caps are this collection's. Returns the entry's handle, which the site passes
/// to [`verdict`] once it has decided.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
pub(super) fn enter(
    definition: &BackendDefinition,
    attributes: &RuleAttributes,
    requires: &[Predicate],
    substitution: &Substitution,
    knowledge: &[Predicate],
    options: SimplificationOptions,
    shared: Option<SharedEvaluation>,
) -> Option<GuardHandle> {
    let (axiom, folded) = entry(
        definition,
        attributes,
        requires,
        substitution,
        knowledge,
        options,
        shared,
    )?;
    SINK.with_borrow_mut(|sink| sink.as_mut()?.open(axiom, folded))
}

/// The entry of [`enter`], evaluated or recognized by the cache, and its axiom's id; `None` when
/// the open collection does not name the axiom or its `requires` is empty.
fn entry(
    definition: &BackendDefinition,
    attributes: &RuleAttributes,
    requires: &[Predicate],
    substitution: &Substitution,
    knowledge: &[Predicate],
    options: SimplificationOptions,
    shared: Option<SharedEvaluation>,
) -> Option<(String, Folded)> {
    if requires.is_empty() {
        return None;
    }
    let caps = SINK.with_borrow(|sink| {
        sink.as_ref()
            .filter(|sink| sink.collection.selects(attributes))
            .map(|sink| {
                (
                    sink.collection.max_value_size,
                    sink.collection.record_polls,
                    sink.collection.cache_keys,
                )
            })
    });
    let (max_value_size, record_polls, cache_keys) = caps?;
    let axiom = attributes.unique_id.clone();
    let key = EntryKey::of(requires, substitution, knowledge);
    let cacheable = !key.exceeds(max_value_size);
    let cache_key = (axiom, key);
    if cacheable {
        let cached = SINK.with_borrow(|sink| {
            sink.as_ref()
                .and_then(|sink| sink.cache.get(&cache_key).cloned())
        });
        if let Some(folded) = cached {
            let (axiom, _) = cache_key;
            return Some((axiom, folded));
        }
    }
    let (axiom, key) = cache_key;
    let condition = match shared {
        Some(shared)
            if shared.max_value_size == max_value_size && shared.record_polls == record_polls =>
        {
            shared.condition
        }
        _ => {
            let evaluation = Evaluation {
                definition,
                substitution,
                knowledge,
                options,
                max_value_size,
                bound: &key.bindings,
            };
            evaluation.condition(requires, record_polls).0
        }
    };
    SINK.with_borrow_mut(|sink| {
        let sink = sink.as_mut()?;
        let slot = sink
            .axioms
            .entry(axiom.clone())
            .or_insert_with(|| Slot::of(requires));
        let folded = slot.fold(&condition, &key.bindings);
        if cacheable {
            if sink.cache.len() >= cache_keys {
                sink.cache.clear();
            }
            sink.cache.insert((axiom.clone(), key), folded.clone());
        }
        Some((axiom, folded))
    })
}

/// Report what the attempt of the entry `handle` decided; nothing without a handle.
#[inline(never)]
pub(super) fn verdict(handle: GuardHandle, decided: Decided) {
    SINK.with_borrow_mut(|sink| {
        if let Some(sink) = sink.as_mut() {
            sink.close(handle, decided);
        }
    });
}

/// Whether the open collection names the axiom `attributes` names.
pub(crate) fn collects_guard_of(attributes: &RuleAttributes) -> bool {
    SINK.with_borrow(|sink| {
        sink.as_ref()
            .is_some_and(|sink| sink.collection.selects(attributes))
    })
}

/// Make the untried entries of the function application `term`, decided under the path
/// conditions `knowledge` by the equation at position `applied` of its group: `enter` makes
/// them ([`enter_untried`]), isolated from the run as an offer probe is (`super::offer`), so
/// that the matching it does reports to no coverage set, counts no work, emits no diagnostic,
/// notes no path fact and leaves the counter of renamed-apart names as it was. `cacheable` says
/// whether the entries are a function of the key alone; where they are, an application whose
/// entries were made already is recognized by a bounded cache, as entries are, and makes none
/// again: entering them again would fold the same entries into the same sets.
pub(crate) fn untried_application(
    term: &Term,
    knowledge: &[Predicate],
    applied: usize,
    cacheable: bool,
    enter: impl FnOnce(),
) {
    let caps = SINK.with_borrow(|sink| {
        sink.as_ref()
            .map(|sink| (sink.collection.max_value_size, sink.collection.cache_keys))
    });
    let Some((max_value_size, cache_keys)) = caps else {
        return;
    };
    let key = cacheable
        .then(|| ApplicationKey {
            term: term.clone(),
            knowledge: knowledge.to_vec(),
            applied,
        })
        .filter(|key| !key.exceeds(max_value_size));
    if let Some(key) = key {
        let seen = SINK.with_borrow_mut(|sink| {
            let Some(sink) = sink.as_mut() else {
                return true;
            };
            if sink.applications.contains(&key) {
                return true;
            }
            if sink.applications.len() >= cache_keys {
                sink.applications.clear();
            }
            sink.applications.insert(key);
            false
        });
        if seen {
            return;
        }
    }
    super::suspend(|| {
        k_rust_kore::measure::without_counting(|| {
            crate::diagnostic::discarded(|| {
                crate::path_facts::discarded(|| crate::rule::with_apart_names_restored(enter))
            })
        })
    });
}

/// Fold the entry of the axiom `attributes` names into `requires` under `substitution`, with
/// the path and match conditions `knowledge`, as [`enter`] does, where the run did not try it:
/// its guard outcome is the one its evaluation gives (the first conjunct that is not `true`
/// decides it), with `undecided: untried` where that conjunct is undecided. One evaluation
/// serves both kinds of entry, with the same bounds and the same cache, so an entry's outcomes
/// do not depend on whether the run tried it first.
pub(crate) fn enter_untried(
    definition: &BackendDefinition,
    attributes: &RuleAttributes,
    requires: &[Predicate],
    substitution: &Substitution,
    knowledge: &[Predicate],
    options: SimplificationOptions,
) {
    let Some((axiom, folded)) = entry(
        definition,
        attributes,
        requires,
        substitution,
        knowledge,
        options,
        None,
    ) else {
        return;
    };
    SINK.with_borrow_mut(|sink| {
        if let Some(sink) = sink.as_mut() {
            let outcome = folded.untried;
            sink.add(&axiom, folded, outcome);
        }
    });
}

impl Slot {
    /// The skeleton of the written `requires`, every node not yet reached.
    fn of(requires: &[Predicate]) -> Self {
        let mut slot = Self {
            nodes: Vec::new(),
            variables: Vec::new(),
            outcomes: BTreeSet::new(),
            combinations: BTreeSet::new(),
            truncated: false,
        };
        for (index, predicate) in requires.iter().enumerate() {
            slot.predicate(predicate, vec![index as u32]);
        }
        slot
    }

    fn push(&mut self, path: Vec<u32>, shape: GuardShape, variables: BTreeSet<Variable>) {
        self.nodes.push(GuardNode {
            path,
            shape,
            reached: BTreeSet::new(),
        });
        self.variables.push(variables);
    }

    /// The skeleton of a predicate node, as `conditions::Evaluation::predicate` reads it.
    fn predicate(&mut self, predicate: &Predicate, path: Vec<u32>) {
        let mut variables = BTreeSet::new();
        predicate.visit_terms(&mut |term| {
            variables.extend(term.attributes().variables.iter().map(written));
        });
        let child = |index: usize| {
            let mut path = path.clone();
            path.push(index as u32);
            path
        };
        match predicate {
            Predicate::Equals(left, right) => {
                for (literal, operand) in [(right, left), (left, right)] {
                    for value in [true, false] {
                        if is_boolean(operand) && *literal == Term::bool(value) {
                            self.push(path.clone(), GuardShape::Equals(value), variables);
                            self.boolean(operand, child(0));
                            return;
                        }
                    }
                }
                self.push(
                    path,
                    GuardShape::Predicate(as_written(predicate)),
                    variables,
                );
            }
            Predicate::Term(term) => {
                self.push(path.clone(), GuardShape::Equals(true), variables);
                self.boolean(term, child(0));
            }
            Predicate::Not(inner) => {
                self.push(
                    path.clone(),
                    GuardShape::Connective(Connective::Not),
                    variables,
                );
                self.predicate(inner, child(0));
            }
            Predicate::And(operands) | Predicate::Or(operands) => {
                let connective = if matches!(predicate, Predicate::And(_)) {
                    Connective::And
                } else {
                    Connective::Or
                };
                self.push(path.clone(), GuardShape::Connective(connective), variables);
                for (index, operand) in operands.iter().enumerate() {
                    self.predicate(operand, child(index));
                }
            }
            Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
                let connective = if matches!(predicate, Predicate::Implies(..)) {
                    Connective::Implies
                } else {
                    Connective::Iff
                };
                self.push(path.clone(), GuardShape::Connective(connective), variables);
                self.predicate(left, child(0));
                self.predicate(right, child(1));
            }
            Predicate::True
            | Predicate::False
            | Predicate::Ceil(_)
            | Predicate::Defined(_)
            | Predicate::Floor(_)
            | Predicate::In(..)
            | Predicate::Absent(_)
            | Predicate::Exists(..)
            | Predicate::Forall(..) => {
                self.push(
                    path,
                    GuardShape::Predicate(as_written(predicate)),
                    variables,
                );
            }
        }
    }

    /// The skeleton of a Boolean node, as `conditions::Evaluation::boolean` reads it.
    fn boolean(&mut self, term: &Term, path: Vec<u32>) {
        let variables = term.attributes().variables.iter().map(written).collect();
        if let TermKind::Application {
            symbol, arguments, ..
        } = term.kind()
            && let Some(connective) = symbol
                .attributes
                .hook
                .as_deref()
                .and_then(Connective::of_hook)
        {
            self.push(path.clone(), GuardShape::Connective(connective), variables);
            for (index, argument) in arguments.iter().enumerate() {
                let mut path = path.clone();
                path.push(index as u32);
                self.boolean(argument, path);
            }
            return;
        }
        self.push(path, GuardShape::Term(term_as_written(term)), variables);
    }

    /// Read one entry's evaluated `condition` over the slot's skeleton: the outcome of each
    /// node it reached, its refutation and its valuation, which its verdict folds into the slot
    /// ([`Sink::close`]). `bound` are the entry's bindings, by written variable.
    fn fold(&self, condition: &[ConditionNode], bound: &[(Variable, Term)]) -> Folded {
        let mut fold = Fold {
            slot: self,
            bound,
            index: 0,
            reached: Vec::new(),
            atoms: Vec::new(),
        };
        let mut reached = true;
        for conjunct in condition {
            fold.node(conjunct, reached);
            reached = reached && conjunct.value() == Truth::True;
        }
        let refutation = condition
            .iter()
            .find(|conjunct| conjunct.value() != Truth::True)
            .filter(|conjunct| conjunct.value() == Truth::False)
            .map_or(Refutation::Decided, |conjunct| match conjunct {
                ConditionNode::Equals { child, .. } if child.value() == Truth::Undefined => {
                    Refutation::Undefined
                }
                _ => Refutation::False,
            });
        // The first conjunct that is not `true` decides the condition where the run did not
        // try it: none holds it, a `false` or `undefined` one refutes it whatever the later
        // conjuncts are, and an undecided one leaves it open, the later conjuncts unreached.
        let untried = match condition
            .iter()
            .find(|conjunct| conjunct.value() != Truth::True)
            .map(ConditionNode::value)
        {
            None => GuardOutcome::Held,
            Some(Truth::False) => GuardOutcome::Refuted(refutation),
            Some(Truth::Undefined) => GuardOutcome::Refuted(Refutation::Undefined),
            Some(Truth::True | Truth::Undecided) => GuardOutcome::Undecided(AttemptCause::Untried),
        };
        Folded {
            reached: fold.reached,
            refutation,
            atoms: fold.atoms,
            untried,
        }
    }
}

/// One entry's fold over a slot's preorder.
struct Fold<'a> {
    slot: &'a Slot,
    bound: &'a [(Variable, Term)],
    index: usize,
    reached: Vec<(usize, NodeOutcome)>,
    atoms: Vec<Truth>,
}

impl Fold<'_> {
    fn node(&mut self, node: &ConditionNode, reached: bool) {
        let index = self.index;
        self.index += 1;
        if index >= self.slot.nodes.len() {
            // The evaluation follows the written condition, so this does not happen; an entry
            // that would disagree adds nothing past the skeleton.
            return;
        }
        if self.slot.nodes[index].shape.is_atom() {
            self.atoms.push(node.value());
        }
        if reached {
            let outcome = match node.value() {
                Truth::True => NodeOutcome::True,
                Truth::False => NodeOutcome::False,
                Truth::Undefined => NodeOutcome::Undefined,
                Truth::Undecided => NodeOutcome::Undecided(self.cause(node, index)),
            };
            self.reached.push((index, outcome));
        }
        match node {
            ConditionNode::Atom(_) => {}
            ConditionNode::Equals { child, .. } => self.node(child, reached),
            ConditionNode::Connective {
                connective,
                children,
                ..
            } => {
                let mut open = reached;
                for (position, child) in children.iter().enumerate() {
                    let child_reached = match connective {
                        Connective::AndBool | Connective::AndThenBool | Connective::And => open,
                        Connective::OrBool | Connective::OrElseBool | Connective::Or => open,
                        Connective::ImpliesBool | Connective::Implies => {
                            if position == 0 {
                                reached
                            } else {
                                open
                            }
                        }
                        Connective::NotBool
                        | Connective::Not
                        | Connective::XorBool
                        | Connective::Iff => reached,
                    };
                    self.node(child, child_reached);
                    open = open
                        && match connective {
                            Connective::AndBool
                            | Connective::AndThenBool
                            | Connective::And
                            | Connective::ImpliesBool
                            | Connective::Implies => child.value() == Truth::True,
                            Connective::OrBool | Connective::OrElseBool | Connective::Or => {
                                child.value() == Truth::False
                            }
                            Connective::NotBool
                            | Connective::Not
                            | Connective::XorBool
                            | Connective::Iff => true,
                        };
                }
            }
        }
    }

    /// Why the node at `index`, which `node` evaluated, is undecided.
    fn cause(&self, node: &ConditionNode, index: usize) -> OperandCause {
        if stopped(node) {
            return OperandCause::Stopped;
        }
        let symbolic = self.slot.variables[index].iter().any(|variable| {
            self.bound
                .iter()
                .find(|(bound, _)| bound == variable)
                .is_none_or(|(_, value)| !value.attributes().variables.is_empty())
        });
        if symbolic {
            OperandCause::Symbolic
        } else {
            OperandCause::Unevaluated
        }
    }
}

/// Whether a stop interrupted the evaluation of an operand below `node`.
fn stopped(node: &ConditionNode) -> bool {
    match node {
        ConditionNode::Atom(atom) => atom
            .operands
            .iter()
            .any(|operand| matches!(operand, RecordedValue::Stopped)),
        ConditionNode::Equals { child, .. } => stopped(child),
        ConditionNode::Connective { children, .. } => children.iter().any(stopped),
    }
}

/// The renaming of `variables`, variables of an axiom inside an attempt, to the names the axiom
/// writes.
fn renaming<'v>(variables: impl Iterator<Item = &'v Variable>) -> Substitution {
    variables
        .filter_map(|variable| {
            let written = written(variable);
            (written != *variable).then(|| (variable.clone(), Term::variable(written)))
        })
        .collect()
}

fn term_as_written(term: &Term) -> Term {
    let renaming = renaming(term.attributes().variables.iter());
    if renaming.is_empty() {
        term.clone()
    } else {
        substitute(term, &renaming)
    }
}

fn as_written(predicate: &Predicate) -> Predicate {
    let mut variables = BTreeSet::new();
    predicate
        .visit_terms(&mut |term| variables.extend(term.attributes().variables.iter().cloned()));
    let renaming = renaming(variables.iter());
    if renaming.is_empty() {
        return predicate.clone();
    }
    #[expect(
        clippy::disallowed_methods,
        reason = "a renaming of variables to variables, for printing; no definedness is decided from it"
    )]
    let renamed = crate::rewrite::substitute_predicates(std::slice::from_ref(predicate), &renaming);
    renamed
        .into_iter()
        .next()
        .unwrap_or_else(|| predicate.clone())
}
