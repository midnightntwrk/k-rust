//! Condition records: for the rewrite rules a run names, what each entry into a rule's
//! `requires` saw, and what the attempt then decided (G-7).
//!
//! A run that collects coverage and names rules (`rewrite::ExecutionOptions::collect_conditions`)
//! records, where the backend enters a named rule's `requires` phase for a matched instance
//! (`rewrite::apply`, P11, the place `RunCoverage::matched` notes the rule), the instance's
//! bindings of the variables the condition reads and the condition's structure with every node
//! evaluated under the instance, and then the attempt's verdict on the condition. A caller that
//! measures how far an instance was from satisfying the condition (a branch distance), collects
//! values the run compared against, or asks which inputs a failing atom depends on reads them
//! here; the run itself never does.
//!
//! The record's evaluation is isolated from the run ([`super::isolated`]): it reports to no
//! coverage set, emits no diagnostic, notes no path fact, takes no fresh or renamed-apart name,
//! counts no work, fills no memo the run reads, and uses no solver, so asking for records changes
//! nothing else in the result. It runs inside the run's step but off its clock: the step deadline
//! neither stops it nor is charged with its time, and its own work is bounded by a budget of polls
//! ([`ConditionCollection::record_polls`]); what a stop of its own (that budget, its stack, a
//! cancellation) interrupted is reported as such ([`Truth::Undecided`], [`RecordedValue::Stopped`]).
//! It evaluates each subterm of the condition once, bottom-up, so it costs about one more
//! evaluation of the condition per recorded entry, in wall time only.

use std::{
    cell::{Cell, RefCell},
    collections::BTreeSet,
};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    condition::Condition,
    definition::BackendDefinition,
    rewrite::{Truth as PredicateTruth, predicates_truth},
    rule::{Predicate, RewriteRule},
    simplify::{SimplificationOptions, simplify_predicates_with_solver, simplify_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{Term, TermKind, Variable, names::rule_variable_definition_name},
};

/// The records a run keeps per rule unless the request says otherwise
/// ([`ConditionCollection::limit`]).
pub const DEFAULT_CONDITION_LIMIT: usize = 32;

/// The largest value, in term nodes, a record holds unless the request says otherwise
/// ([`ConditionCollection::max_value_size`]).
pub const DEFAULT_MAX_VALUE_SIZE: usize = 256;

/// The most polls one record's evaluation may make unless the request says otherwise
/// ([`ConditionCollection::record_polls`]).
pub const DEFAULT_RECORD_POLLS: u64 = 1_000_000;

/// Which rules' condition entries a run records, and how much it keeps.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConditionCollection {
    /// The rewrite rules whose entries are recorded, each named by its `UNIQUE_ID` or its label.
    /// A name that is neither, or that names an equation, records nothing.
    pub rules: BTreeSet<String>,
    /// The most records kept per rule: the first `limit` distinct entries in the run's order,
    /// whatever they are (no entry is preferred, so an entry closer to satisfying the condition
    /// that the run makes later can be left out); a rule with a further distinct entry is marked
    /// [`RuleConditions::truncated`].
    pub limit: usize,
    /// The largest value a record holds, in term nodes (each application, domain value,
    /// variable, injection and collection item counts one); a larger one is
    /// [`RecordedValue::Omitted`].
    pub max_value_size: usize,
    /// The most polls the evaluation of one record may make (the simplifier polls at each of
    /// its steps): a bound on the record's work that is a function of the work alone, since the
    /// record runs off the run's clock (`coverage::isolated`). An operand or node whose
    /// evaluation the bound stops is [`RecordedValue::Stopped`] or [`Truth::Undecided`].
    ///
    /// Since the step deadline does not stop a record, a run with a step timeout may exceed
    /// it in wall time by at most (rules recorded × [`Self::limit`]) records of up to this many
    /// polls each, with the work between polls. A caller that uses the step timeout as an
    /// overall wall-clock guard lowers this bound, names fewer rules, or cancels the request,
    /// which still interrupts a record.
    pub record_polls: u64,
}

impl ConditionCollection {
    /// The rules `rules`, with the default caps.
    pub fn new<S: Into<String>>(rules: impl IntoIterator<Item = S>) -> Self {
        Self {
            rules: rules.into_iter().map(Into::into).collect(),
            limit: DEFAULT_CONDITION_LIMIT,
            max_value_size: DEFAULT_MAX_VALUE_SIZE,
            record_polls: DEFAULT_RECORD_POLLS,
        }
    }

    fn selects(&self, rule: &RewriteRule) -> bool {
        self.rules.contains(&rule.attributes.unique_id)
            || rule
                .attributes
                .label
                .as_ref()
                .is_some_and(|label| self.rules.contains(label))
    }
}

/// The records of one rule ([`super::RunCoverage::conditions`]).
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct RuleConditions {
    /// The rule's `UNIQUE_ID`.
    pub rule: String,
    /// The distinct entries, in the order the run first made them, at most
    /// [`ConditionCollection::limit`].
    pub records: Vec<ConditionRecord>,
    /// Whether the run made a further distinct entry that the limit left out.
    pub truncated: bool,
}

/// One entry into a rule's `requires` for a matched instance.
///
/// Two entries are the same when they bind the condition's variables to the same terms under the
/// same path and match conditions; the run records the first, with its attempt's verdict. Every
/// term in a record is a term of the run, marked as what it is ([`RecordedValue`]).
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct ConditionRecord {
    /// The instance's binding of each variable of the `requires` that the match bound, as the
    /// match bound it (not simplified), sorted by variable. Each variable is named as the rule
    /// is written (`term::names::rule_variable_definition_name`), not as an attempt renamed it
    /// apart from the state's variables. A variable the match left unbound (one that only the
    /// condition binds) is absent.
    pub bindings: Vec<(Variable, RecordedValue)>,
    /// The `requires` as written, one node per conjunct, every node evaluated under the
    /// instance. The condition holds exactly when every conjunct holds.
    pub condition: Vec<ConditionNode>,
    /// What the attempt decided about the condition ([`Verdict`]): present on every entry whose
    /// attempt reached a decision, a stop, or a re-entry ([`Verdict::Reentered`]).
    pub verdict: Option<Verdict>,
    /// Whether a value the definition leaves open (an implementation-chosen value) was read by
    /// the run before the entry, on any path, or by the record's own evaluation: the record's
    /// terms may then be one model's.
    pub chosen: bool,
}

/// What a rule attempt decided about its instantiated `requires`, with the solver the run uses.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Verdict {
    /// The condition holds for the instance (on the path, under the match conditions), and the
    /// attempt goes on to build the rule's successor, which can still fail: the instantiation of
    /// the right-hand side can be indeterminate, give no successor, or meet an error, and the
    /// rule is then in `matched` but not `applied`.
    Held,
    /// The condition does not hold for the instance: false, undefined, or contradicted by the
    /// path. The rule does not apply to the instance.
    Refuted,
    /// The attempt could not decide the condition: without a solver, by an undecided solver
    /// answer, or by a condition the solver cannot translate. Depending on why, the attempt is
    /// indeterminate or applies the rule under the condition left open.
    Undecided,
    /// A stop (lack of stack, a step deadline, a cancellation) ended the attempt while it
    /// decided the condition.
    Stopped,
    /// The condition completed an incomplete match: it bound variables of the left-hand side the
    /// match left unbound, and the attempt re-entered with them, which is a further entry with
    /// those bindings (and its own verdict). This entry's operands over those variables are
    /// symbolic even on a concrete state; the further entry is the complete one.
    Reentered,
}

/// The truth of a node of a condition under the instance, as the record's own evaluation
/// decides it, under the path and match conditions and without a solver.
///
/// `True` and `False` are decisions: the node holds, or does not, for the instance, in every
/// model of the definition (unless the record is [`ConditionRecord::chosen`]). `Undefined`, only
/// on a K Boolean node, says the node's term denotes no value (`\bottom`) for the instance: a
/// partial operation it does not discard is outside its domain. `Undecided` decides nothing: the
/// node may be true, false or (for a Boolean node) undefined; the evaluation left an application
/// it cannot evaluate, the instance is symbolic, or a stop interrupted it. The attempt itself may
/// decide what the record left undecided, with the solver ([`ConditionRecord::verdict`]).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Truth {
    True,
    False,
    Undefined,
    Undecided,
}

/// The connectives of a condition, each with its own semantics.
///
/// The K Boolean connectives are functions on the sort `Bool`, by their `BOOL` hooks, and strict
/// (docs/compatibility.md, "Conditionals and Boolean connectives are strict"): a node is
/// undefined wherever an operand is, also the operand `andThenBool` or `orElseBool` does not
/// evaluate (`false andThenBool B` is `false` under the definedness of `B`); so `notBool` of an
/// undefined operand is undefined. The matching-logic connectives combine predicates, which are
/// two-valued: `\not P` holds exactly where `P` does not.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Connective {
    /// `notBool` (`BOOL.not`), one operand.
    NotBool,
    /// `andBool` (`BOOL.and`), two operands, both evaluated.
    AndBool,
    /// `andThenBool` (`BOOL.andThen`), two operands; the second is not evaluated when the first
    /// is `false`, and its definedness is still required.
    AndThenBool,
    /// `orBool` (`BOOL.or`), two operands, both evaluated.
    OrBool,
    /// `orElseBool` (`BOOL.orElse`), two operands; the second is not evaluated when the first is
    /// `true`, and its definedness is still required.
    OrElseBool,
    /// `impliesBool` (`BOOL.implies`), two operands.
    ImpliesBool,
    /// `xorBool` (`BOOL.xor`), two operands.
    XorBool,
    /// `\not`, one predicate.
    Not,
    /// `\and`, any number of predicates.
    And,
    /// `\or`, any number of predicates.
    Or,
    /// `\implies`, two predicates.
    Implies,
    /// `\iff`, two predicates.
    Iff,
}

impl Connective {
    /// Whether the connective is a K Boolean function (its node is a `Bool` term) rather than a
    /// matching-logic connective (its node is a predicate).
    pub fn is_boolean(self) -> bool {
        matches!(
            self,
            Self::NotBool
                | Self::AndBool
                | Self::AndThenBool
                | Self::OrBool
                | Self::OrElseBool
                | Self::ImpliesBool
                | Self::XorBool
        )
    }

    fn of_hook(hook: &str) -> Option<Self> {
        match hook {
            "BOOL.not" => Some(Self::NotBool),
            "BOOL.and" => Some(Self::AndBool),
            "BOOL.andThen" => Some(Self::AndThenBool),
            "BOOL.or" => Some(Self::OrBool),
            "BOOL.orElse" => Some(Self::OrElseBool),
            "BOOL.implies" => Some(Self::ImpliesBool),
            "BOOL.xor" => Some(Self::XorBool),
            _ => None,
        }
    }
}

/// A node of a condition, as written, with its truth under the instance.
///
/// A node is either a K Boolean node (a term of sort `Bool`: a Boolean connective, or an atom
/// that is a `Bool` term) or a predicate (a matching-logic connective, an [`Self::Equals`], or
/// a predicate atom). A conjunct of the `requires` is a predicate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConditionNode {
    /// A connective and its operands, in order.
    Connective {
        connective: Connective,
        children: Vec<ConditionNode>,
        value: Truth,
    },
    /// The predicate `\equals(b, literal)` of a Boolean term `b`: it holds exactly where `b` is
    /// defined and equal to `literal`, so an undefined `b` makes it false. A K `requires b` is
    /// written `\equals(b, true)`.
    Equals {
        literal: bool,
        child: Box<ConditionNode>,
        value: Truth,
    },
    /// Anything else.
    Atom(ConditionAtom),
}

impl ConditionNode {
    /// The node's truth under the instance.
    pub fn value(&self) -> Truth {
        match self {
            Self::Connective { value, .. } | Self::Equals { value, .. } => *value,
            Self::Atom(atom) => atom.value,
        }
    }
}

/// An atom of a condition, evaluated under the instance.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct ConditionAtom {
    /// The symbol of a Boolean application (such as `Lbl'-LT-'Int'Unds'`); the matching-logic
    /// connective of a predicate atom (`\equals` of two terms that are not a Boolean term and a
    /// Boolean literal, `\ceil`, `\floor`, `\in`, `\exists`, `\forall`, `\top`, `\bottom`), or
    /// `absent` for the absence of a key from a map or a set (operands: the key and the
    /// collection), the written form of a `\ceil` of that key joined to it; or `None` for a
    /// Boolean term that is no application (a variable or a literal).
    pub head: Option<String>,
    /// The `hook` of the symbol, when it has one (such as `INT.lt`).
    pub hook: Option<String>,
    /// The operands, each simplified under the instance and the path and match conditions: the
    /// arguments of an application, the terms of `\equals`, `\ceil`, `\floor` and `\in`, the key
    /// and collection of an absence, the term itself when it is no application, and none for a
    /// quantifier, `\top` or `\bottom`.
    pub operands: Vec<RecordedValue>,
    /// The positions in [`ConditionRecord::bindings`] of the variables the atom mentions, in
    /// order: the bound values its operands depend on. A variable the match left unbound has no
    /// position.
    pub reads: Vec<usize>,
    /// The atom's truth under the instance ([`Truth`]): a Boolean atom may be `Undefined`, a
    /// predicate atom never is.
    pub value: Truth,
}

/// A term of a record, marked by what it denotes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RecordedValue {
    /// A ground value: built from constructors, injections, domain values, and maps, sets and
    /// lists of them, with no function application left (`TermAttributes::constructor_like`).
    /// Its KORE means the same in every model of the definition, unless the record is
    /// [`ConditionRecord::chosen`].
    Value(Term),
    /// Variable-free, but holding an application the evaluation left as it is (a function with
    /// no applicable equation, a partial function outside its domain that the evaluation did not
    /// find undefined, an operation the simplification failed on): not a value, and its meaning
    /// depends on the definition.
    Unevaluated(Term),
    /// A term with variables: a set of values.
    Symbolic(Term),
    /// The evaluation found the operand undefined (`\bottom`) under the instance.
    Undefined,
    /// A stop (lack of stack, a step deadline, a cancellation) interrupted the operand's
    /// evaluation; nothing is known of its value.
    Stopped,
    /// Larger than [`ConditionCollection::max_value_size`] nodes.
    Omitted,
}

thread_local! {
    /// Whether the innermost open coverage collection records conditions.
    static RECORDING: Cell<bool> = const { Cell::new(false) };
    /// What it has recorded.
    static SINK: RefCell<Option<Sink>> = const { RefCell::new(None) };
    /// The record made by the attempt under way, by rule id and position, until its verdict.
    static PENDING: RefCell<Option<(String, usize)>> = const { RefCell::new(None) };
}

/// The records of one collection.
pub(super) struct Sink {
    collection: ConditionCollection,
    rules: FxHashMap<String, Slot>,
}

#[derive(Default)]
struct Slot {
    keys: FxHashSet<EntryKey>,
    records: Vec<ConditionRecord>,
    truncated: bool,
}

/// What a record is a function of: the bindings it reports and the path and match conditions
/// its atoms are evaluated under.
#[derive(Clone, Eq, Hash, PartialEq)]
struct EntryKey {
    bindings: Vec<(Variable, Term)>,
    knowledge: Vec<Predicate>,
}

impl Sink {
    pub(super) fn new(collection: ConditionCollection) -> Self {
        Self {
            collection,
            rules: FxHashMap::default(),
        }
    }

    /// The records by rule id.
    pub(super) fn finish(self) -> Vec<RuleConditions> {
        let mut rules = self
            .rules
            .into_iter()
            .map(|(rule, slot)| RuleConditions {
                rule,
                records: slot.records,
                truncated: slot.truncated,
            })
            .collect::<Vec<_>>();
        rules.sort_by(|left, right| left.rule.cmp(&right.rule));
        rules
    }

    /// Whether the entry `key` of `rule` is to be recorded: it is new and the rule's limit is
    /// not reached. A new entry past the limit marks the rule truncated.
    fn admit(&mut self, rule: &RewriteRule, key: &EntryKey) -> bool {
        let limit = self.collection.limit;
        let slot = self
            .rules
            .entry(rule.attributes.unique_id.clone())
            .or_default();
        if slot.keys.contains(key) {
            return false;
        }
        if slot.records.len() >= limit {
            slot.truncated = true;
            return false;
        }
        true
    }

    /// Keep `record`, returning its position among the rule's records.
    fn push(&mut self, rule: &RewriteRule, key: EntryKey, record: ConditionRecord) -> usize {
        let slot = self
            .rules
            .entry(rule.attributes.unique_id.clone())
            .or_default();
        slot.keys.insert(key);
        slot.records.push(record);
        slot.records.len() - 1
    }
}

/// Install `sink` as the innermost collection's records, returning the enclosing one's.
pub(super) fn replace(sink: Option<Sink>) -> Option<Sink> {
    RECORDING.set(sink.is_some());
    PENDING.take();
    SINK.replace(sink)
}

/// Whether the innermost open collection records conditions.
#[inline]
pub(super) fn recording() -> bool {
    RECORDING.get()
}

/// Record the entry of `rule`'s `requires` under `substitution`, the match's bindings, with the
/// path and match conditions `knowledge`, when the open collection names the rule: P11 of a rule
/// attempt calls it where it notes the rule matched (`super::records_conditions` first). The
/// attempt then reports its verdict ([`verdict`]).
pub(crate) fn record(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    substitution: &Substitution,
    knowledge: &[Predicate],
    options: SimplificationOptions,
) {
    // A verdict reported from here on belongs to this entry, or to none.
    PENDING.take();
    let selected = SINK.with_borrow(|sink| {
        sink.as_ref().map(|sink| {
            (
                sink.collection.selects(rule),
                sink.collection.max_value_size,
                sink.collection.record_polls,
            )
        })
    });
    let Some((true, max_value_size, record_polls)) = selected else {
        return;
    };
    let mut read = BTreeSet::new();
    for predicate in rule.requires.iter() {
        predicate.visit_terms(&mut |term| read.extend(term.attributes().variables.iter().cloned()));
    }
    let mut bindings = read
        .iter()
        .filter_map(|variable| {
            substitution
                .get(variable)
                .map(|value| (written(variable), value.clone()))
        })
        .collect::<Vec<_>>();
    bindings.sort();
    let key = EntryKey {
        bindings,
        knowledge: knowledge.to_vec(),
    };
    if !SINK.with_borrow_mut(|sink| sink.as_mut().is_some_and(|sink| sink.admit(rule, &key))) {
        return;
    }
    let before = crate::path_facts::run_read_chosen_value();
    let evaluation = Evaluation {
        definition,
        substitution,
        knowledge,
        options,
        max_value_size,
        bound: &key.bindings,
    };
    let (condition, read_chosen) = super::isolated(record_polls, || {
        rule.requires
            .iter()
            .map(|predicate| evaluation.predicate(predicate))
            .collect::<Vec<_>>()
    });
    let record = ConditionRecord {
        bindings: key
            .bindings
            .iter()
            .map(|(variable, value)| (variable.clone(), evaluation.value(value.clone())))
            .collect(),
        condition,
        verdict: None,
        chosen: before || read_chosen,
    };
    let id = rule.attributes.unique_id.clone();
    let position =
        SINK.with_borrow_mut(|sink| sink.as_mut().map(|sink| sink.push(rule, key, record)));
    if let Some(position) = position {
        PENDING.set(Some((id, position)));
    }
}

/// Report the verdict of the attempt whose entry was recorded last ([`record`]); nothing when
/// that entry was not recorded or already has its verdict. The attempt reports once, where it
/// decides its condition (`rewrite::apply`, P11 and P12).
pub(crate) fn verdict(verdict: Verdict) {
    let Some((rule, position)) = PENDING.take() else {
        return;
    };
    SINK.with_borrow_mut(|sink| {
        if let Some(record) = sink
            .as_mut()
            .and_then(|sink| sink.rules.get_mut(&rule))
            .and_then(|slot| slot.records.get_mut(position))
        {
            record.verdict = Some(verdict);
        }
    });
}

/// `variable`, a variable of a rule inside an attempt, named as the rule is written.
fn written(variable: &Variable) -> Variable {
    Variable {
        name: rule_variable_definition_name(&variable.name).into(),
        ..variable.clone()
    }
}

/// The evaluation of one record's condition.
struct Evaluation<'a> {
    definition: &'a BackendDefinition,
    substitution: &'a Substitution,
    knowledge: &'a [Predicate],
    options: SimplificationOptions,
    max_value_size: usize,
    /// The record's bindings, by written variable.
    bound: &'a [(Variable, Term)],
}

fn is_boolean(term: &Term) -> bool {
    term.sort()
        .is_builtin(k_rust_kore::names::BuiltinSort::Bool)
}

/// A term of the condition evaluated under the instance: its record, and the term its parent
/// is rebuilt from (the simplified term; the instance where the evaluation failed; none where
/// it found the term undefined or was stopped, so that the parent evaluates the instance
/// there, by its own semantics).
struct Evaluated {
    value: RecordedValue,
    term: Option<Term>,
}

/// Kleene's three-valued reading of a matching-logic connective over its operands' truths: a
/// predicate is two-valued, and `Undecided` stands for either value.
fn predicate_connective(connective: Connective, children: &[ConditionNode]) -> Truth {
    let values = children
        .iter()
        .map(ConditionNode::value)
        .collect::<Vec<_>>();
    let not = |value: Truth| match value {
        Truth::True => Truth::False,
        Truth::False => Truth::True,
        Truth::Undefined | Truth::Undecided => Truth::Undecided,
    };
    let and = |values: &[Truth]| {
        if values.contains(&Truth::False) {
            Truth::False
        } else if values.iter().all(|value| *value == Truth::True) {
            Truth::True
        } else {
            Truth::Undecided
        }
    };
    let or = |values: &[Truth]| not(and(&values.iter().copied().map(not).collect::<Vec<_>>()));
    match (connective, values.as_slice()) {
        (Connective::Not, [value]) => not(*value),
        (Connective::And, values) => and(values),
        (Connective::Or, values) => or(values),
        (Connective::Implies, [left, right]) => or(&[not(*left), *right]),
        (Connective::Iff, [left, right]) => match (left, right) {
            (Truth::True | Truth::False, Truth::True | Truth::False) => {
                if left == right {
                    Truth::True
                } else {
                    Truth::False
                }
            }
            _ => Truth::Undecided,
        },
        _ => Truth::Undecided,
    }
}

/// The truth of `\equals(b, literal)` from the truth of `b`: it holds exactly where `b` is
/// defined and equal to `literal`.
fn equals_literal(literal: bool, value: Truth) -> Truth {
    match (literal, value) {
        (true, Truth::True) | (false, Truth::False) => Truth::True,
        (true, Truth::False) | (false, Truth::True) | (_, Truth::Undefined) => Truth::False,
        (_, Truth::Undecided) => Truth::Undecided,
    }
}

impl Evaluation<'_> {
    /// One conjunct of the condition, or a predicate below one. The recursion follows the
    /// condition as written, whose depth is the rule's. A connective's truth and an
    /// `\equals(b, literal)`'s follow from their operands' by their semantics, with no
    /// evaluation of their own.
    fn predicate(&self, predicate: &Predicate) -> ConditionNode {
        let connective = |connective: Connective, children: Vec<ConditionNode>| {
            let value = predicate_connective(connective, &children);
            ConditionNode::Connective {
                connective,
                children,
                value,
            }
        };
        let equals = |literal: bool, operand: &Term| {
            let (child, _) = self.boolean(operand);
            ConditionNode::Equals {
                literal,
                value: equals_literal(literal, child.value()),
                child: Box::new(child),
            }
        };
        match predicate {
            Predicate::Equals(left, right) => {
                for (literal, operand) in [(right, left), (left, right)] {
                    for value in [true, false] {
                        if is_boolean(operand) && *literal == Term::bool(value) {
                            return equals(value, operand);
                        }
                    }
                }
                self.predicate_atom(r"\equals", &[left, right], predicate)
            }
            // A Boolean term read as a predicate states that it is `true`.
            Predicate::Term(term) => equals(true, term),
            Predicate::Not(inner) => connective(Connective::Not, vec![self.predicate(inner)]),
            Predicate::And(conjuncts) => connective(
                Connective::And,
                conjuncts
                    .iter()
                    .map(|conjunct| self.predicate(conjunct))
                    .collect(),
            ),
            Predicate::Or(disjuncts) => connective(
                Connective::Or,
                disjuncts
                    .iter()
                    .map(|disjunct| self.predicate(disjunct))
                    .collect(),
            ),
            Predicate::Implies(left, right) => connective(
                Connective::Implies,
                vec![self.predicate(left), self.predicate(right)],
            ),
            Predicate::Iff(left, right) => connective(
                Connective::Iff,
                vec![self.predicate(left), self.predicate(right)],
            ),
            Predicate::True => self.predicate_atom(r"\top", &[], predicate),
            Predicate::False => self.predicate_atom(r"\bottom", &[], predicate),
            Predicate::Ceil(term) | Predicate::Defined(term) => {
                self.predicate_atom(r"\ceil", &[term], predicate)
            }
            Predicate::Floor(term) => self.predicate_atom(r"\floor", &[term], predicate),
            Predicate::In(left, right) => self.predicate_atom(r"\in", &[left, right], predicate),
            Predicate::Absent(absence) => {
                self.predicate_atom("absent", &[absence.key(), absence.rest()], predicate)
            }
            Predicate::Exists(..) => self.predicate_atom(r"\exists", &[], predicate),
            Predicate::Forall(..) => self.predicate_atom(r"\forall", &[], predicate),
        }
    }

    /// A Boolean term of the condition, evaluated bottom-up: its operands first, then the term
    /// rebuilt from their results, so each subterm is evaluated once (the application itself is
    /// one more step: a hook on values, or the equations of a Boolean function). A `BOOL`
    /// connective is a node, anything else an atom; each has the truth of its own term
    /// ([`Self::truth`]). Returns the node and the term its parent is rebuilt from.
    ///
    /// An application one of whose operands the record found undefined is undefined, with no
    /// evaluation of its own: a symbol applied to `\bottom` denotes `\bottom` (the application
    /// is the pointwise image of its arguments' sets, and one of them is empty). This holds for
    /// every Boolean function and connective, `andThenBool` and `orElseBool` too: the variable
    /// their discarding equation (`false andThenBool _ => false`) leaves unread ranges over
    /// defined elements, so the equation never applies to an undefined operand. The record
    /// decides this from the operand's own undefinedness, also where reading the rebuilt term's
    /// truth would leave it undecided (an operand undefined through a function's equation,
    /// under the operand `andThenBool` discards).
    fn boolean(&self, term: &Term) -> (ConditionNode, Option<Term>) {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = term.kind()
        else {
            let evaluated = self.operand(term);
            let value = match &evaluated.value {
                RecordedValue::Undefined => Truth::Undefined,
                _ if evaluated.term.as_ref() == Some(&Term::bool(true)) => Truth::True,
                _ if evaluated.term.as_ref() == Some(&Term::bool(false)) => Truth::False,
                _ => Truth::Undecided,
            };
            let node = ConditionNode::Atom(ConditionAtom {
                head: None,
                hook: None,
                operands: vec![evaluated.value],
                reads: self.reads(term.attributes().variables.iter()),
                value,
            });
            return (node, evaluated.term);
        };
        let hook = symbol.attributes.hook.as_deref();
        let rebuild = |terms: Vec<Option<Term>>| {
            let arguments = terms
                .into_iter()
                .zip(arguments)
                .map(|(evaluated, argument)| {
                    evaluated.unwrap_or_else(|| substitute(argument, self.substitution))
                })
                .collect();
            Term::application(symbol.clone(), *sort_arguments, arguments)
        };
        if let Some(connective) = hook.and_then(Connective::of_hook) {
            let (children, terms): (Vec<_>, Vec<_>) = arguments
                .iter()
                .map(|argument| self.boolean(argument))
                .unzip();
            let undefined = children
                .iter()
                .any(|child| child.value() == Truth::Undefined);
            let (value, evaluated) = if undefined {
                (Truth::Undefined, None)
            } else {
                self.truth(&rebuild(terms))
            };
            let node = ConditionNode::Connective {
                connective,
                children,
                value,
            };
            return (node, evaluated);
        }
        let (operands, terms): (Vec<_>, Vec<_>) = arguments
            .iter()
            .map(|argument| {
                let evaluated = self.operand(argument);
                (evaluated.value, evaluated.term)
            })
            .unzip();
        let undefined = operands
            .iter()
            .any(|operand| matches!(operand, RecordedValue::Undefined));
        let (value, evaluated) = if undefined {
            (Truth::Undefined, None)
        } else {
            self.truth(&rebuild(terms))
        };
        let node = ConditionNode::Atom(ConditionAtom {
            head: Some(symbol.name.to_string()),
            hook: hook.map(str::to_owned),
            operands,
            reads: self.reads(term.attributes().variables.iter()),
            value,
        });
        (node, evaluated)
    }

    /// A predicate atom: its operands evaluated, and its truth decided on the predicate rebuilt
    /// from them ([`Self::predicate_truth`]).
    fn predicate_atom(
        &self,
        head: &str,
        operands: &[&Term],
        predicate: &Predicate,
    ) -> ConditionNode {
        let mut variables = BTreeSet::new();
        predicate.visit_terms(&mut |term| {
            variables.extend(term.attributes().variables.iter().cloned());
        });
        let evaluated = operands
            .iter()
            .map(|operand| self.operand(operand))
            .collect::<Vec<_>>();
        let term = |position: usize, written: &Term| {
            evaluated[position]
                .term
                .clone()
                .unwrap_or_else(|| substitute(written, self.substitution))
        };
        // The predicate over the operands' results; the others are taken as written.
        let instance = match predicate {
            Predicate::Equals(left, right) => Predicate::Equals(term(0, left), term(1, right)),
            Predicate::In(left, right) => Predicate::In(term(0, left), term(1, right)),
            Predicate::Ceil(inner) => Predicate::Ceil(term(0, inner)),
            Predicate::Defined(inner) => Predicate::Defined(term(0, inner)),
            Predicate::Floor(inner) => Predicate::Floor(term(0, inner)),
            Predicate::Absent(absence) => {
                let (key, rest) = (term(0, absence.key()), term(1, absence.rest()));
                crate::rule::Absence::predicate(absence.collection(), key, rest)
            }
            other => {
                return ConditionNode::Atom(ConditionAtom {
                    head: Some(head.to_owned()),
                    hook: None,
                    operands: Vec::new(),
                    reads: self.reads(variables.iter()),
                    value: self.predicate_truth(other, self.substitution),
                });
            }
        };
        ConditionNode::Atom(ConditionAtom {
            head: Some(head.to_owned()),
            hook: None,
            operands: evaluated
                .into_iter()
                .map(|evaluated| evaluated.value)
                .collect(),
            reads: self.reads(variables.iter()),
            value: self.predicate_truth(&instance, &Substitution::new()),
        })
    }

    /// The positions in the record's bindings of `variables`, variables of the condition inside
    /// the attempt.
    fn reads<'v>(&self, variables: impl Iterator<Item = &'v Variable>) -> Vec<usize> {
        let written = variables.map(written).collect::<BTreeSet<_>>();
        self.bound
            .iter()
            .enumerate()
            .filter(|(_, (variable, _))| written.contains(variable))
            .map(|(position, _)| position)
            .collect()
    }

    /// `term` of the condition, instantiated and simplified under the path and match
    /// conditions.
    fn operand(&self, term: &Term) -> Evaluated {
        let instance = substitute(term, self.substitution);
        match simplify_with_solver(
            self.definition,
            &instance,
            self.knowledge,
            self.options,
            &NoSolver,
        ) {
            Ok(Ok(simplified))
                if simplified.undefined_term.is_some() || simplified.bottom.is_some() =>
            {
                Evaluated {
                    value: RecordedValue::Undefined,
                    term: None,
                }
            }
            Ok(Ok(simplified)) => Evaluated {
                value: self.value(simplified.term.clone()),
                term: Some(simplified.term),
            },
            // The simplification failed (a budget, an unsupported hook): the instance as it is,
            // marked by what it holds.
            Ok(Err(_)) => Evaluated {
                value: self.value(instance.clone()),
                term: Some(instance),
            },
            Err(stop) => {
                // The record only describes the run, and an operand it did not finish evaluating
                // is reported as such: the record's own stack or budget ran out, or a
                // cancellation came, which stays raised and ends the run at its next poll.
                stop.forgo_refinement();
                Evaluated {
                    value: RecordedValue::Stopped,
                    term: None,
                }
            }
        }
    }

    /// The truth of `term`, a Boolean term rebuilt from its evaluated operands, and the term its
    /// parent is rebuilt from. The truth is read off the predicates `\equals(term, true)` and
    /// `\equals(term, false)` ([`Self::predicate_truth`]), so the term is read as the run's
    /// conditions read it, with its definedness stated as theirs is (strict connectives, deferred
    /// obligations for the operands `andThenBool`, `orElseBool` and `#if` do not evaluate).
    /// `true` where the first holds, `false` where the second does, undefined where both are
    /// refuted (a defined `Bool` is one of the two), and undecided otherwise.
    fn truth(&self, term: &Term) -> (Truth, Option<Term>) {
        let empty = Substitution::new();
        let equals = |literal: bool| {
            self.predicate_truth(
                &Predicate::Equals(term.clone(), Term::bool(literal)),
                &empty,
            )
        };
        match equals(true) {
            Truth::True => (Truth::True, Some(Term::bool(true))),
            Truth::False => match equals(false) {
                Truth::True => (Truth::False, Some(Term::bool(false))),
                Truth::False => (Truth::Undefined, None),
                Truth::Undefined | Truth::Undecided => (Truth::Undecided, Some(term.clone())),
            },
            Truth::Undefined | Truth::Undecided => (Truth::Undecided, Some(term.clone())),
        }
    }

    /// The truth of `predicate` under `substitution`: its instance, with the definedness of its
    /// terms stated, simplified under the path and match conditions without a solver. A
    /// predicate is never undefined.
    fn predicate_truth(&self, predicate: &Predicate, substitution: &Substitution) -> Truth {
        let instance = Condition::new(vec![predicate.clone()]).instantiate(substitution);
        let simplified = instance.simplify(
            self.definition,
            self.knowledge,
            self.knowledge,
            |conditions, known, _| {
                simplify_predicates_with_solver(
                    self.definition,
                    &conditions,
                    known,
                    self.options,
                    &NoSolver,
                )
            },
        );
        match simplified {
            Ok(Ok(predicates)) => match predicates_truth(&predicates) {
                PredicateTruth::True => Truth::True,
                PredicateTruth::False => Truth::False,
                PredicateTruth::Unknown => Truth::Undecided,
            },
            Ok(Err(_)) => Truth::Undecided,
            Err(stop) => {
                // As for an operand: the record reports the predicate undecided.
                stop.forgo_refinement();
                Truth::Undecided
            }
        }
    }

    /// `term`, marked by what it denotes, or omitted when it is larger than the cap.
    fn value(&self, term: Term) -> RecordedValue {
        if exceeds(&term, self.max_value_size) {
            RecordedValue::Omitted
        } else if term.attributes().constructor_like {
            RecordedValue::Value(term)
        } else if term.attributes().variables.is_empty() {
            RecordedValue::Unevaluated(term)
        } else {
            RecordedValue::Symbolic(term)
        }
    }
}

/// Whether `term` has more than `cap` nodes; it visits at most `cap + 1`, from a work list.
fn exceeds(term: &Term, cap: usize) -> bool {
    let mut nodes = 0usize;
    let mut pending = vec![term];
    while let Some(next) = pending.pop() {
        nodes += 1;
        if nodes > cap {
            return true;
        }
        pending.extend(crate::deferred::children(next));
    }
    false
}
