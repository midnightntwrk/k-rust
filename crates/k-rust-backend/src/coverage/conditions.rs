//! Condition records: for the rewrite rules a run names, what each entry into a rule's
//! `requires` saw (G-7).
//!
//! A run that collects coverage and names rules (`rewrite::ExecutionOptions::collect_conditions`)
//! records, where the backend enters a named rule's `requires` phase for a matched instance
//! (`rewrite::apply`, P11, the place `RunCoverage::matched` notes the rule), the instance's
//! bindings of the variables the condition reads and the condition's Boolean structure with each
//! atom's operands evaluated under the instance. A caller that measures how far an instance was
//! from satisfying the condition (a branch distance), collects values the run compared against,
//! or asks which inputs the failing atom depends on reads them here; the run itself never does.
//!
//! The record is taken on entry, before the condition is decided, and whatever the attempt then
//! decides (held, refuted, undecided, or cut short). Its evaluation is isolated from the run
//! ([`super::isolated`]): it reports to no coverage set, emits no diagnostic, notes no path fact,
//! takes no fresh or renamed-apart name, counts no work, fills no memo the run reads, and uses no
//! solver, so asking for records changes nothing else in the result.

use std::{
    cell::{Cell, RefCell},
    collections::BTreeSet,
};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    condition::Condition,
    definition::BackendDefinition,
    rewrite::{Truth, predicates_truth},
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

/// Which rules' condition entries a run records, and how much it keeps.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConditionCollection {
    /// The rewrite rules whose entries are recorded, each named by its `UNIQUE_ID` or its label.
    /// A name that is neither, or that names an equation, records nothing.
    pub rules: BTreeSet<String>,
    /// The most records kept per rule: the first `limit` distinct entries in the run's order;
    /// a rule with a further distinct entry is marked [`RuleConditions::truncated`].
    pub limit: usize,
    /// The largest value a record holds, in term nodes (each application, domain value,
    /// variable, injection and collection item counts one); a larger one is
    /// [`RecordedValue::Omitted`].
    pub max_value_size: usize,
}

impl ConditionCollection {
    /// The rules `rules`, with the default caps.
    pub fn new<S: Into<String>>(rules: impl IntoIterator<Item = S>) -> Self {
        Self {
            rules: rules.into_iter().map(Into::into).collect(),
            limit: DEFAULT_CONDITION_LIMIT,
            max_value_size: DEFAULT_MAX_VALUE_SIZE,
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
/// same path and match conditions; the run records the first. Every term in a record is a term of
/// the run, marked as what it is ([`RecordedValue`]).
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct ConditionRecord {
    /// The instance's binding of each variable of the `requires` that the match bound, as the
    /// match bound it (not simplified), sorted by variable. Each variable is named as the rule
    /// is written (`term::names::rule_variable_definition_name`), not as an attempt renamed it
    /// apart from the state's variables. A variable the match left unbound (one that only the
    /// condition binds) is absent.
    pub bindings: Vec<(Variable, RecordedValue)>,
    /// The `requires` as written, one node per conjunct, each atom evaluated under the instance.
    pub condition: Vec<ConditionNode>,
    /// Whether a value the definition leaves open (an implementation-chosen value) was read by
    /// the run before the entry, on any path, or by the record's own evaluation: the record's
    /// terms may then be one model's.
    pub chosen: bool,
}

/// The Boolean structure of a condition, as written.
///
/// A conjunct `\equals(b, true)` of a Boolean term `b` (how a K `requires b` is written) is read
/// as `b`, and `\equals(b, false)` as `not b`; the K connectives `andBool`, `andThenBool`,
/// `orBool`, `orElseBool`, `notBool` and `impliesBool` (by their `BOOL` hooks) and the
/// matching-logic `\and`, `\or`, `\not` and `\implies` are nodes; everything else is an atom.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConditionNode {
    And(Vec<ConditionNode>),
    Or(Vec<ConditionNode>),
    Not(Box<ConditionNode>),
    Implies(Box<ConditionNode>, Box<ConditionNode>),
    Atom(ConditionAtom),
}

/// An atom of a condition, evaluated under the instance.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct ConditionAtom {
    /// The symbol of a Boolean application (such as `Lbl'-LT-'Int'Unds'`), the matching-logic
    /// connective of a predicate atom (`\equals`, `\ceil`, `\floor`, `\in`, `\iff`, `\exists`,
    /// `\forall`, `\top`, `\bottom`), or `None` for a Boolean term that is no application (a
    /// variable or a literal).
    pub head: Option<String>,
    /// The `hook` of the symbol, when it has one (such as `INT.lt`).
    pub hook: Option<String>,
    /// The operands, each simplified under the instance and the path and match conditions: the
    /// arguments of an application, the terms of `\equals`, `\ceil`, `\floor` and `\in`, the
    /// term itself when it is no application, and none for the other connectives.
    pub operands: Vec<RecordedValue>,
    /// The positions in [`ConditionRecord::bindings`] of the variables the atom mentions, in
    /// order: the bound values its operands depend on. A variable the match left unbound has no
    /// position.
    pub reads: Vec<usize>,
    /// The atom's truth under the instance, as the simplifier decides it without a solver:
    /// `Some(true)` where it holds, `Some(false)` where it is refuted (false, or undefined),
    /// `None` where it is left undecided.
    pub value: Option<bool>,
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
    /// no applicable equation, a partial function outside its domain): its meaning depends on
    /// the definition.
    Ground(Term),
    /// A term with variables: a set of values.
    Symbolic(Term),
    /// The evaluation found the operand undefined (`\bottom`) under the instance.
    Undefined,
    /// Larger than [`ConditionCollection::max_value_size`] nodes.
    Omitted,
}

thread_local! {
    /// Whether the innermost open coverage collection records conditions.
    static RECORDING: Cell<bool> = const { Cell::new(false) };
    /// What it has recorded.
    static SINK: RefCell<Option<Sink>> = const { RefCell::new(None) };
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

    fn push(&mut self, rule: &RewriteRule, key: EntryKey, record: ConditionRecord) {
        let slot = self
            .rules
            .entry(rule.attributes.unique_id.clone())
            .or_default();
        slot.keys.insert(key);
        slot.records.push(record);
    }
}

/// Install `sink` as the innermost collection's records, returning the enclosing one's.
pub(super) fn replace(sink: Option<Sink>) -> Option<Sink> {
    RECORDING.set(sink.is_some());
    SINK.replace(sink)
}

/// Whether the innermost open collection records conditions.
#[inline]
pub(super) fn recording() -> bool {
    RECORDING.get()
}

/// Record the entry of `rule`'s `requires` under `substitution`, the match's bindings, with the
/// path and match conditions `knowledge`, when the open collection names the rule: P11 of a rule
/// attempt calls it where it notes the rule matched (`super::records_conditions` first).
pub(crate) fn record(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    substitution: &Substitution,
    knowledge: &[Predicate],
    options: SimplificationOptions,
) {
    let selected = SINK.with_borrow(|sink| {
        sink.as_ref().map(|sink| {
            (
                sink.collection.selects(rule),
                sink.collection.max_value_size,
            )
        })
    });
    let Some((true, max_value_size)) = selected else {
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
    let (condition, read_chosen) = super::isolated(|| {
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
        chosen: before || read_chosen,
    };
    SINK.with_borrow_mut(|sink| {
        if let Some(sink) = sink {
            sink.push(rule, key, record);
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

/// The `BOOL` hooks read as nodes, and the node each builds.
#[derive(Clone, Copy)]
enum Connective {
    And,
    Or,
    Not,
    Implies,
}

fn connective(hook: &str) -> Option<Connective> {
    match hook {
        "BOOL.and" | "BOOL.andThen" => Some(Connective::And),
        "BOOL.or" | "BOOL.orElse" => Some(Connective::Or),
        "BOOL.not" => Some(Connective::Not),
        "BOOL.implies" => Some(Connective::Implies),
        _ => None,
    }
}

fn is_boolean(term: &Term) -> bool {
    term.sort()
        .is_builtin(k_rust_kore::names::BuiltinSort::Bool)
}

impl Evaluation<'_> {
    /// One conjunct of the condition, or a predicate below one. The recursion follows the
    /// condition as written, whose depth is the rule's.
    fn predicate(&self, predicate: &Predicate) -> ConditionNode {
        match predicate {
            Predicate::Equals(left, right) => {
                for (literal, operand) in [(right, left), (left, right)] {
                    if is_boolean(operand) && *literal == Term::bool(true) {
                        return self.boolean(operand);
                    }
                    if is_boolean(operand) && *literal == Term::bool(false) {
                        return ConditionNode::Not(Box::new(self.boolean(operand)));
                    }
                }
                self.predicate_atom(r"\equals", &[left, right], predicate)
            }
            Predicate::Term(term) => self.boolean(term),
            Predicate::Not(inner) => ConditionNode::Not(Box::new(self.predicate(inner))),
            Predicate::And(conjuncts) => ConditionNode::And(
                conjuncts
                    .iter()
                    .map(|conjunct| self.predicate(conjunct))
                    .collect(),
            ),
            Predicate::Or(disjuncts) => ConditionNode::Or(
                disjuncts
                    .iter()
                    .map(|disjunct| self.predicate(disjunct))
                    .collect(),
            ),
            Predicate::Implies(left, right) => ConditionNode::Implies(
                Box::new(self.predicate(left)),
                Box::new(self.predicate(right)),
            ),
            Predicate::True => self.predicate_atom(r"\top", &[], predicate),
            Predicate::False => self.predicate_atom(r"\bottom", &[], predicate),
            Predicate::Ceil(term) | Predicate::Defined(term) => {
                self.predicate_atom(r"\ceil", &[term], predicate)
            }
            Predicate::Floor(term) => self.predicate_atom(r"\floor", &[term], predicate),
            Predicate::In(left, right) => self.predicate_atom(r"\in", &[left, right], predicate),
            Predicate::Absent(_) => self.predicate_atom(r"\ceil", &[], predicate),
            Predicate::Iff(..) => self.predicate_atom(r"\iff", &[], predicate),
            Predicate::Exists(..) => self.predicate_atom(r"\exists", &[], predicate),
            Predicate::Forall(..) => self.predicate_atom(r"\forall", &[], predicate),
        }
    }

    /// A Boolean term of the condition: a node for a `BOOL` connective, an atom otherwise.
    fn boolean(&self, term: &Term) -> ConditionNode {
        if let TermKind::Application {
            symbol, arguments, ..
        } = term.kind()
        {
            let hook = symbol.attributes.hook.as_deref();
            match (hook.and_then(connective), arguments.as_slice()) {
                (Some(Connective::And), [left, right]) => {
                    return ConditionNode::And(vec![self.boolean(left), self.boolean(right)]);
                }
                (Some(Connective::Or), [left, right]) => {
                    return ConditionNode::Or(vec![self.boolean(left), self.boolean(right)]);
                }
                (Some(Connective::Not), [operand]) => {
                    return ConditionNode::Not(Box::new(self.boolean(operand)));
                }
                (Some(Connective::Implies), [left, right]) => {
                    return ConditionNode::Implies(
                        Box::new(self.boolean(left)),
                        Box::new(self.boolean(right)),
                    );
                }
                _ => {}
            }
            return ConditionNode::Atom(ConditionAtom {
                head: Some(symbol.name.to_string()),
                hook: hook.map(str::to_owned),
                operands: arguments
                    .iter()
                    .map(|argument| self.operand(argument))
                    .collect(),
                reads: self.reads(term.attributes().variables.iter()),
                value: self.truth(Predicate::Equals(term.clone(), Term::bool(true))),
            });
        }
        ConditionNode::Atom(ConditionAtom {
            head: None,
            hook: None,
            operands: vec![self.operand(term)],
            reads: self.reads(term.attributes().variables.iter()),
            value: self.truth(Predicate::Equals(term.clone(), Term::bool(true))),
        })
    }

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
        ConditionNode::Atom(ConditionAtom {
            head: Some(head.to_owned()),
            hook: None,
            operands: operands
                .iter()
                .map(|operand| self.operand(operand))
                .collect(),
            reads: self.reads(variables.iter()),
            value: self.truth(predicate.clone()),
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
    /// conditions. Where the simplification stops or fails, the instance as it is.
    fn operand(&self, term: &Term) -> RecordedValue {
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
                RecordedValue::Undefined
            }
            Ok(Ok(simplified)) => self.value(simplified.term),
            Ok(Err(_)) | Err(_) => self.value(instance),
        }
    }

    /// The truth of `predicate`, a predicate of the condition, under the instance: its instance,
    /// with the definedness of its terms stated, simplified under the path and match conditions
    /// without a solver. A stop or a failure leaves it undecided.
    fn truth(&self, predicate: Predicate) -> Option<bool> {
        let instance = Condition::new(vec![predicate]).instantiate(self.substitution);
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
                Truth::True => Some(true),
                Truth::False => Some(false),
                Truth::Unknown => None,
            },
            Ok(Err(_)) | Err(_) => None,
        }
    }

    /// `term`, marked by what it denotes, or omitted when it is larger than the cap.
    fn value(&self, term: Term) -> RecordedValue {
        if exceeds(&term, self.max_value_size) {
            RecordedValue::Omitted
        } else if term.attributes().constructor_like {
            RecordedValue::Value(term)
        } else if term.attributes().variables.is_empty() {
            RecordedValue::Ground(term)
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
