//! What the check reads from the conditions of a pair, after the simplifier has simplified their
//! conjunction with every claim withheld.
//!
//! The simplifier refutes a conjunction it evaluates to `\bottom`. Two propositional facts it does
//! not use are decided here, on the conjuncts it leaves. A conjunct states a Boolean literal when
//! it requires a term equal to a domain value of a sort whose domain kind is the Booleans
//! (`\equals(b, true)`), its negation, or a Bool-sorted term itself. A sort of that kind
//! (`SortBool`, or a sort hooked `BOOL.Bool`; `DomainKind::of_declared_sort`) has exactly the
//! domain values `true` and `false`, so a term of it equal to neither is no value, and the two
//! requirements on one term are complementary. A domain value of any other sort is never read as
//! a Boolean, whatever its spelling: a token or a `String` spelled `"true"` is one value of its
//! sort among others.
//!
//! - **complementary literals**: a Boolean atom required true by one conjunct and false by another
//!   (`N >Int M` beside `N <=Int M`, `notBool B` beside `B`). Comparisons are read up to their
//!   arithmetic identities (`a >Int b` is `b <Int a`, `a <=Int b` is `notBool (b <Int a)`,
//!   `a =/=Int b` is `notBool (a ==Int b)`), so the conjunction holds on no instance;
//! - **atoms true on every instance where they are defined**: `K in keys(M)` (`SET.in` of
//!   `MAP.keys`, or `MAP.in_keys`) where `K` is the key of an entry of the map term `M`, and
//!   `A ==K A`. Required false, such an atom makes the conjunction false wherever it is defined,
//!   and undefined elsewhere: a condition holds only where it is defined and true;
//! - **integer bounds**: the conjuncts that compare one integer term, the *key*, up to literal
//!   offsets (`key +Int c`, `c +Int key`, `key -Int c`, nested), with an integer literal state
//!   that the key lies in an interval with optional ends minus finitely many points. `Int` is the
//!   unbounded integers and `INT.lt`, `le`, `gt`, `ge`, `eq`, `ne` are total and exact, and
//!   `+Int` and `-Int` are total, so `key +Int c` is defined exactly where the key is and the set
//!   is exact; over the integers it is empty exactly when the interval is empty, or finite with
//!   every point excluded. The conjunction is refuted when one key's set is empty. Keys are
//!   decided independently, and a comparison of two non-literal terms bounds neither: sound, not
//!   complete for related keys (`X <Int Y` beside `Y <Int X` is not refuted). An integer
//!   literal is a domain value of a sort whose domain kind is the integers (`SortInt`, or a sort
//!   hooked `INT.Int`), read as the integer it denotes: the `INT` hooks interpret their operands
//!   as integers whatever the sort is named.
//!
//! Definedness of a key: a conjunct requiring a comparison atom true or false (`\equals(b, true)`,
//! `\equals(b, false)`, or `b` itself) holds only where `b` is defined, hence where the key is;
//! so does an ML `\equals(t, c)` with an integer literal `c`. A `\not(...)` of such a conjunct
//! also holds where the key is undefined, so its bound is used only when the key is `ceil_free`
//! or another conjunct shows it defined; ignoring a conjunct only weakens the conjunction.
//! After simplification the definedness of a partial key often arrives as a sibling conjunct
//! that no syntactic rule links to the key (`Y =/=Int 0` for `X /Int Y`), so
//! `notBool (X /Int Y >Int 5)` beside `notBool (X /Int Y <Int 6)` is not refuted: a known
//! non-refutation, sound.
//!
//! - **equality classes**: the terms the conjuncts require equal form classes: the operands of an
//!   equality atom (`INT.eq`, `KEQUAL.eq`, `BOOL.eq`, `STRING.eq`, or a negated `ne`) required
//!   true, and the two sides of an ML `\equals(t, u)` neither of which is a Boolean literal. Such
//!   an atom holds only where both operands are defined, and then exactly when they are the same
//!   value (each hook is equality on its domain), and `\equals` is equality of patterns; equality
//!   is an equivalence relation. A class holding two different domain values of one sort (two
//!   different elements: the unifier reads them as a clash too) holds on no instance, nor does a
//!   class two of whose members a negative equality (the atom required false, or `\not` of the
//!   `\equals`) relates. The operands of `KEQUAL.eq` that are one-element sequences of injections
//!   from one sort are compared by their items (`kseq` is a free constructor, `inj` injective).
//!   A class with exactly one domain value gives each of its other members that value on every
//!   instance where the conjuncts hold, so each conjunct with the members replaced by the value
//!   holds there too (symbols denote functions: congruence); `Context::conditions` simplifies the
//!   rewritten conjunction once more and refutes it when that gives `\bottom` or a contradiction
//!   (`substring(S, I, I +Int 1) ==String "t"` beside `findChar(HEX, substring(S, I, I +Int 1), 0)
//!   =/=Int -1` becomes `findChar(HEX, "t", 0) =/=Int -1`, which evaluates to false).
//!
//! Every remaining conjunct `X = t` (a variable equal to a term without `X`) is an equality every
//! instance satisfying the conditions has, which the join may apply (`confluence.rs`).

use std::collections::BTreeSet;

use num_bigint::BigInt;
use rustc_hash::FxHashMap;

use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    substitution::{Substitution, substitute},
    term::{DomainKind, Term, TermKind},
};

/// A Boolean atom up to the arithmetic identities above.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Atom {
    /// `left <Int right`.
    Less(Term, Term),
    /// `left == right` (`INT.eq`, `KEQUAL.eq`, `BOOL.eq`, `STRING.eq`), arguments in term order.
    Equal(Term, Term),
    Other(Term),
}

/// Whether the conjuncts are contradictory by complementary literals, by an atom required false
/// that holds wherever it is defined, or by the integer bounds of one key, the domain kinds of
/// their sorts read in `definition`.
pub(super) fn contradictory(definition: &BackendDefinition, conjuncts: &[Predicate]) -> bool {
    let mut seen = FxHashMap::<Atom, bool>::default();
    for conjunct in conjuncts {
        let Some((term, polarity)) = literal(definition, conjunct) else {
            continue;
        };
        let (atom, polarity) = atom(&term, polarity);
        if !polarity && holds_where_defined(&atom) {
            return true;
        }
        if polarity && fails_where_defined(&atom) {
            return true;
        }
        match seen.get(&atom) {
            Some(known) if *known != polarity => return true,
            Some(_) => {}
            None => {
                seen.insert(atom, polarity);
            }
        }
    }
    let merging = super::switches::active().misread_literal_classes;
    Classes::of(definition, conjuncts, merging).is_none()
        || integer_bounds_empty(definition, conjuncts)
}

/// The classes of the terms the conjuncts require equal (module documentation, "equality
/// classes"), with a union-find over the terms.
struct Classes {
    index: FxHashMap<Term, usize>,
    terms: Vec<Term>,
    parent: Vec<usize>,
}

impl Classes {
    fn node(&mut self, term: &Term) -> usize {
        if let Some(index) = self.index.get(term) {
            return *index;
        }
        let index = self.terms.len();
        self.index.insert(term.clone(), index);
        self.terms.push(term.clone());
        self.parent.push(index);
        index
    }

    fn find(&mut self, mut index: usize) -> usize {
        while self.parent[index] != index {
            self.parent[index] = self.parent[self.parent[index]];
            index = self.parent[index];
        }
        index
    }

    fn union(&mut self, left: &Term, right: &Term) {
        let (left, right) = (self.node(left), self.node(right));
        let (left, right) = (self.find(left), self.find(right));
        self.parent[left] = right;
    }

    /// The classes of the positive equalities among `conjuncts`, or `None` when the conjuncts
    /// are contradictory by them: a class holds two different domain values of one sort, or a
    /// negative equality relates two members of one class. `merging` also merges the operands
    /// of each negative equality (a defect switch).
    fn of(definition: &BackendDefinition, conjuncts: &[Predicate], merging: bool) -> Option<Self> {
        let mut classes = Self {
            index: FxHashMap::default(),
            terms: Vec::new(),
            parent: Vec::new(),
        };
        let mut apart = Vec::new();
        for conjunct in conjuncts {
            let Some((left, right, positive)) = equality(definition, conjunct) else {
                continue;
            };
            if positive || merging {
                classes.union(&left, &right);
            } else {
                apart.push((left, right));
            }
        }
        for (left, right) in apart {
            let (left, right) = (classes.node(&left), classes.node(&right));
            if classes.find(left) == classes.find(right) {
                return None;
            }
        }
        let mut literals = FxHashMap::<usize, Vec<Term>>::default();
        for index in 0..classes.terms.len() {
            if matches!(classes.terms[index].kind(), TermKind::DomainValue { .. }) {
                let root = classes.find(index);
                literals
                    .entry(root)
                    .or_default()
                    .push(classes.terms[index].clone());
            }
        }
        let clash = literals.values().any(|values| {
            values.iter().enumerate().any(|(position, value)| {
                values[position + 1..]
                    .iter()
                    .any(|other| other.sort() == value.sort() && other != value)
            })
        });
        (!clash).then_some(classes)
    }
}

/// The equality or disequality a conjunct states between two terms, and whether it is positive:
/// an equality atom (`INT.eq`, `KEQUAL.eq`, `BOOL.eq`, `STRING.eq` and their negations) required
/// true or false, an ML `\equals(t, u)` neither of whose sides is a Boolean literal, or its
/// `\not`. The operands of `KEQUAL.eq` that are one-element sequences of an injection from one
/// sort are compared by the injected items: `kseq` is a free constructor and `inj` injective.
fn equality(definition: &BackendDefinition, conjunct: &Predicate) -> Option<(Term, Term, bool)> {
    let plain = |predicate: &Predicate| match predicate {
        Predicate::Equals(left, right)
            if boolean(definition, left).is_none() && boolean(definition, right).is_none() =>
        {
            Some((left.clone(), right.clone()))
        }
        _ => None,
    };
    if let Some((left, right)) = plain(conjunct) {
        return Some((left, right, true));
    }
    if let Predicate::Not(inner) = conjunct
        && let Some((left, right)) = plain(inner)
    {
        return Some((left, right, false));
    }
    let (term, polarity) = literal(definition, conjunct)?;
    let (Atom::Equal(left, right), polarity) = atom(&term, polarity) else {
        return None;
    };
    let (left, right) = match (sequence_item(&left), sequence_item(&right)) {
        (Some(left), Some(right)) if left.sort() == right.sort() => (left, right),
        _ => (left, right),
    };
    Some((left, right, polarity))
}

/// The item of a one-element `K` sequence `kseq(inj{S, KItem}(item), dotk)`.
fn sequence_item(term: &Term) -> Option<Term> {
    let item = crate::builtin::k_sequence_item(term)?;
    match item.kind() {
        TermKind::Injection { term, .. } => Some(term.clone()),
        _ => None,
    }
}

/// The values the conjuncts give terms: each member of an equality class that holds exactly one
/// domain value, other than that value, with the value (module documentation, "equality
/// classes"). Empty when the conjuncts are contradictory by their classes.
pub(super) fn literal_values(
    definition: &BackendDefinition,
    conjuncts: &[Predicate],
) -> Vec<(Term, Term)> {
    let merging = super::switches::active().substitute_without_class;
    let Some(mut classes) = Classes::of(definition, conjuncts, merging) else {
        return Vec::new();
    };
    let mut literal_of = FxHashMap::<usize, Option<Term>>::default();
    for index in 0..classes.terms.len() {
        let term = classes.terms[index].clone();
        if matches!(term.kind(), TermKind::DomainValue { .. }) {
            let root = classes.find(index);
            let entry = literal_of.entry(root).or_insert(Some(term.clone()));
            if entry.as_ref() != Some(&term) {
                *entry = None;
            }
        }
    }
    let mut values = Vec::new();
    for index in 0..classes.terms.len() {
        let root = classes.find(index);
        let term = &classes.terms[index];
        if let Some(Some(literal)) = literal_of.get(&root)
            && term != literal
            && term.sort() == literal.sort()
        {
            values.push((term.clone(), literal.clone()));
        }
    }
    values.sort_by(|left, right| left.0.cmp(&right.0));
    values
}

/// `conjuncts` with every maximal occurrence of a term of `values` replaced by its value, outside
/// quantifiers; `None` when nothing is replaced.
pub(super) fn substituted(
    values: &[(Term, Term)],
    conjuncts: &[Predicate],
) -> Option<Vec<Predicate>> {
    if values.is_empty() {
        return None;
    }
    let map = values.iter().cloned().collect::<FxHashMap<_, _>>();
    let mut changed = false;
    let rewritten = conjuncts
        .iter()
        .map(|conjunct| replace_in_predicate(conjunct, &map, &mut changed))
        .collect();
    changed.then_some(rewritten)
}

fn replace_in_term(term: &Term, map: &FxHashMap<Term, Term>, changed: &mut bool) -> Term {
    if let Some(value) = map.get(term) {
        *changed = true;
        return value.clone();
    }
    let mut local = false;
    let replaced = super::children(term)
        .iter()
        .map(|child| replace_in_term(child, map, &mut local))
        .collect();
    if !local {
        return term.clone();
    }
    *changed = true;
    super::with_children(term, replaced)
}

fn replace_in_predicate(
    predicate: &Predicate,
    map: &FxHashMap<Term, Term>,
    changed: &mut bool,
) -> Predicate {
    let term = |term: &Term, changed: &mut bool| replace_in_term(term, map, changed);
    let arc = |inner: &std::sync::Arc<Predicate>, changed: &mut bool| {
        std::sync::Arc::new(replace_in_predicate(inner, map, changed))
    };
    match predicate {
        Predicate::Term(inner) => Predicate::Term(term(inner, changed)),
        Predicate::Equals(left, right) => {
            Predicate::Equals(term(left, changed), term(right, changed))
        }
        Predicate::Ceil(inner) => Predicate::Ceil(term(inner, changed)),
        Predicate::Floor(inner) => Predicate::Floor(term(inner, changed)),
        Predicate::Defined(inner) => Predicate::Defined(term(inner, changed)),
        Predicate::In(left, right) => Predicate::In(term(left, changed), term(right, changed)),
        Predicate::Not(inner) => Predicate::Not(arc(inner, changed)),
        Predicate::Implies(left, right) => {
            Predicate::Implies(arc(left, changed), arc(right, changed))
        }
        Predicate::Iff(left, right) => Predicate::Iff(arc(left, changed), arc(right, changed)),
        Predicate::And(items) => Predicate::And(
            items
                .iter()
                .map(|item| replace_in_predicate(item, map, changed))
                .collect(),
        ),
        Predicate::Or(items) => Predicate::Or(
            items
                .iter()
                .map(|item| replace_in_predicate(item, map, changed))
                .collect(),
        ),
        // Under a binder a member may mention the bound variable; leaving it as written only
        // decides less.
        Predicate::True
        | Predicate::False
        | Predicate::Exists(..)
        | Predicate::Forall(..)
        | Predicate::Absent(_) => predicate.clone(),
    }
}

/// The integers a key may take under the conjuncts that compare it with literals: an interval
/// with optional ends, minus finitely many excluded points.
#[derive(Default)]
struct Bounds {
    lower: Option<BigInt>,
    upper: Option<BigInt>,
    excluded: BTreeSet<BigInt>,
}

impl Bounds {
    fn constrain(&mut self, relation: Relation, value: BigInt) {
        let at_least = |bounds: &mut Self, value: BigInt| {
            if bounds.lower.as_ref().is_none_or(|lower| *lower < value) {
                bounds.lower = Some(value);
            }
        };
        let at_most = |bounds: &mut Self, value: BigInt| {
            if bounds.upper.as_ref().is_none_or(|upper| *upper > value) {
                bounds.upper = Some(value);
            }
        };
        match relation {
            Relation::Less => at_most(self, value - 1),
            Relation::LessEqual => at_most(self, value),
            Relation::Greater => at_least(self, value + 1),
            Relation::GreaterEqual => at_least(self, value),
            Relation::Equal => {
                at_least(self, value.clone());
                at_most(self, value);
            }
            Relation::NotEqual => {
                self.excluded.insert(value);
            }
        }
    }

    /// Whether no integer is within the bounds: the interval is empty, or finite with each of its
    /// points excluded. The walk over the points runs only when the interval has at most as many
    /// points as are excluded.
    fn empty(&self) -> bool {
        let (Some(lower), Some(upper)) = (&self.lower, &self.upper) else {
            return false;
        };
        if lower > upper {
            return true;
        }
        if BigInt::from(self.excluded.len()) < upper - lower + 1 {
            return false;
        }
        let mut point = lower.clone();
        while &point <= upper {
            if !self.excluded.contains(&point) {
                return false;
            }
            point += 1;
        }
        true
    }
}

/// `key <relation> literal`.
#[derive(Clone, Copy, Debug)]
enum Relation {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
}

impl Relation {
    /// The relation that holds exactly where this one fails, on defined operands.
    fn negated(self) -> Self {
        match self {
            Self::Less => Self::GreaterEqual,
            Self::LessEqual => Self::Greater,
            Self::Greater => Self::LessEqual,
            Self::GreaterEqual => Self::Less,
            Self::Equal => Self::NotEqual,
            Self::NotEqual => Self::Equal,
        }
    }

    /// The relation with its operands swapped: `a < b` is `b > a`.
    fn mirrored(self) -> Self {
        match self {
            Self::Less => Self::Greater,
            Self::LessEqual => Self::GreaterEqual,
            Self::Greater => Self::Less,
            Self::GreaterEqual => Self::LessEqual,
            Self::Equal | Self::NotEqual => self,
        }
    }
}

/// The integer an integer literal denotes: a domain value of a sort whose domain kind in
/// `definition` is the integers, whose canonical text is its decimal (`DomainKind::Int`).
fn integer(definition: &BackendDefinition, term: &Term) -> Option<BigInt> {
    match term.kind() {
        TermKind::DomainValue { sort, value }
            if definition.domain_kind(sort) == Some(DomainKind::Int) =>
        {
            value.as_utf8().ok()?.parse().ok()
        }
        _ => None,
    }
}

/// `term` as `key + offset`, peeling `+Int` with an integer literal on either side and `-Int`
/// with one on the right (both total, so the sum is defined exactly where `key` is); `None` for
/// an integer literal, which has no key.
fn shifted(definition: &BackendDefinition, term: &Term) -> Option<(Term, BigInt)> {
    if integer(definition, term).is_some() {
        return None;
    }
    let peeled = match hooked(term) {
        Some(("INT.add", [left, right])) => {
            match (integer(definition, left), integer(definition, right)) {
                (None, Some(value)) => Some((left, value)),
                (Some(value), None) => Some((right, value)),
                _ => None,
            }
        }
        Some(("INT.sub", [left, right])) => integer(definition, right).map(|value| (left, -value)),
        _ => None,
    };
    match peeled {
        Some((inner, offset)) => {
            let (key, inner_offset) = shifted(definition, inner)?;
            Some((key, inner_offset + offset))
        }
        None => Some((term.clone(), BigInt::from(0))),
    }
}

/// `left <relation> right` as `key <relation'> literal`, when one side is an integer literal and
/// the other a shifted key; `None` when both or neither are literals.
fn compared(
    definition: &BackendDefinition,
    left: &Term,
    relation: Relation,
    right: &Term,
) -> Option<(Term, Relation, BigInt)> {
    match (integer(definition, left), integer(definition, right)) {
        (None, Some(value)) => {
            let (key, offset) = shifted(definition, left)?;
            Some((key, relation, value - offset))
        }
        (Some(value), None) => {
            let (key, offset) = shifted(definition, right)?;
            Some((key, relation.mirrored(), value - offset))
        }
        _ => None,
    }
}

/// The integer constraint `key <relation> literal` a conjunct states, and whether the conjunct
/// holding shows its key defined (module documentation, "Definedness of a key").
fn integer_constraint(
    definition: &BackendDefinition,
    conjunct: &Predicate,
) -> Option<(Term, Relation, BigInt, bool)> {
    let (mut term, mut polarity) = match conjunct {
        Predicate::Not(inner) => {
            let (key, relation, value, _) = integer_constraint(definition, inner)?;
            return Some((key, relation.negated(), value, false));
        }
        Predicate::Equals(left, right) => {
            match (boolean(definition, left), boolean(definition, right)) {
                (Some(value), None) => (right.clone(), value),
                (None, Some(value)) => (left.clone(), value),
                (None, None) => {
                    let (key, relation, value) =
                        compared(definition, left, Relation::Equal, right)?;
                    return Some((key, relation, value, true));
                }
                (Some(_), Some(_)) => return None,
            }
        }
        Predicate::Term(term) => (term.clone(), true),
        _ => return None,
    };
    while let Some(("BOOL.not", [inner])) = hooked(&term) {
        let inner = inner.clone();
        term = inner;
        polarity = !polarity;
    }
    let Some((hook, [left, right])) = hooked(&term) else {
        return None;
    };
    let relation = match hook {
        "INT.lt" if super::switches::active().misread_interval_bound => Relation::LessEqual,
        "INT.lt" => Relation::Less,
        "INT.le" => Relation::LessEqual,
        "INT.gt" => Relation::Greater,
        "INT.ge" => Relation::GreaterEqual,
        "INT.eq" => Relation::Equal,
        "INT.ne" => Relation::NotEqual,
        _ => return None,
    };
    let relation = if polarity {
        relation
    } else {
        relation.negated()
    };
    let (key, relation, value) = compared(definition, left, relation, right)?;
    Some((key, relation, value, true))
}

/// Whether the conjuncts that compare one integer key with integer literals leave that key no
/// integer value (module documentation, "integer bounds"). A key's constraints are used only
/// when some conjunct shows it defined or it is `ceil_free`: otherwise a `\not` constraint also
/// holds where the key is undefined, which no interval describes.
fn integer_bounds_empty(definition: &BackendDefinition, conjuncts: &[Predicate]) -> bool {
    let mut constraints = FxHashMap::<Term, (bool, Vec<(Relation, BigInt)>)>::default();
    for conjunct in conjuncts {
        let Some((key, relation, value, shows_defined)) = integer_constraint(definition, conjunct)
        else {
            continue;
        };
        let entry = constraints.entry(key).or_default();
        entry.0 |= shows_defined;
        entry.1.push((relation, value));
    }
    constraints
        .into_iter()
        .any(|(key, (shown_defined, found))| {
            if !shown_defined && !key.attributes().ceil_free() {
                return false;
            }
            let mut bounds = Bounds::default();
            for (relation, value) in found {
                bounds.constrain(relation, value);
            }
            bounds.empty()
        })
}

/// The equalities `X = t` among the conjuncts, as one idempotent substitution: each conjunct
/// `\equals(X, t)` (either orientation) with `X` not in `t`, applied to the ones found before.
pub(super) fn equalities(conjuncts: &[Predicate]) -> Substitution {
    let mut substitution = Substitution::new();
    for conjunct in conjuncts {
        let Predicate::Equals(left, right) = conjunct else {
            continue;
        };
        let (left, right) = (
            substitute(left, &substitution),
            substitute(right, &substitution),
        );
        let (variable, value) = match (left.kind(), right.kind()) {
            (TermKind::Variable(variable), _) => (variable.clone(), right.clone()),
            (_, TermKind::Variable(variable)) => (variable.clone(), left.clone()),
            _ => continue,
        };
        if value.attributes().variables.contains(&variable) {
            continue;
        }
        let single = Substitution::from([(variable.clone(), value.clone())]);
        for bound in substitution.values_mut() {
            *bound = substitute(bound, &single);
        }
        substitution.insert(variable, value);
    }
    substitution
}

/// The Boolean term a conjunct requires, and whether it requires it true.
fn literal(definition: &BackendDefinition, conjunct: &Predicate) -> Option<(Term, bool)> {
    match conjunct {
        Predicate::Equals(left, right) => {
            match (boolean(definition, left), boolean(definition, right)) {
                (Some(value), None) => Some((right.clone(), value)),
                (None, Some(value)) => Some((left.clone(), value)),
                _ => None,
            }
        }
        Predicate::Term(term) => Some((term.clone(), true)),
        Predicate::Not(inner) => {
            literal(definition, inner).map(|(term, polarity)| (term, !polarity))
        }
        _ => None,
    }
}

/// The value of a Boolean literal: a domain value of a sort whose domain kind in `definition` is
/// [`DomainKind::Bool`], which has exactly the values `true` and `false`. A domain value of any
/// other sort is one value of that sort whatever its spelling (a token or a `String` may read
/// `"true"`), so it is not a literal, and a conjunct comparing a term with it states no Boolean.
fn boolean(definition: &BackendDefinition, term: &Term) -> Option<bool> {
    match term.kind() {
        TermKind::DomainValue { sort, value }
            if definition.domain_kind(sort) == Some(DomainKind::Bool) =>
        {
            match value.as_bytes() {
                b"true" => Some(true),
                b"false" => Some(false),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The hook of an application's symbol, and its arguments.
fn hooked(term: &Term) -> Option<(&str, &[Term])> {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => symbol
            .attributes
            .hook
            .as_deref()
            .map(|hook| (hook, arguments.as_slice())),
        _ => None,
    }
}

/// The atom of `term` required with `polarity`, up to negation and the comparison identities.
fn atom(term: &Term, polarity: bool) -> (Atom, bool) {
    let ordered = |left: &Term, right: &Term| {
        if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        }
    };
    match hooked(term) {
        Some(("BOOL.not", [inner])) => atom(inner, !polarity),
        Some(("INT.lt", [left, right])) => (Atom::Less(left.clone(), right.clone()), polarity),
        Some(("INT.gt", [left, right])) => (Atom::Less(right.clone(), left.clone()), polarity),
        Some(("INT.le", [left, right])) if super::switches::active().misread_int_le => {
            (Atom::Less(left.clone(), right.clone()), !polarity)
        }
        Some(("INT.le", [left, right])) => (Atom::Less(right.clone(), left.clone()), !polarity),
        Some(("INT.ge", [left, right])) => (Atom::Less(left.clone(), right.clone()), !polarity),
        Some(("INT.eq" | "KEQUAL.eq" | "BOOL.eq" | "STRING.eq", [left, right])) => {
            let (left, right) = ordered(left, right);
            (Atom::Equal(left, right), polarity)
        }
        Some(("INT.ne" | "KEQUAL.ne" | "BOOL.ne" | "STRING.ne", [left, right])) => {
            let (left, right) = ordered(left, right);
            (Atom::Equal(left, right), !polarity)
        }
        _ => (Atom::Other(term.clone()), polarity),
    }
}

/// Whether the atom is true on every instance where it is defined.
fn holds_where_defined(atom: &Atom) -> bool {
    match atom {
        Atom::Equal(left, right) => left == right,
        Atom::Less(..) => false,
        Atom::Other(term) => match hooked(term) {
            Some(("SET.in", [key, set])) => {
                matches!(hooked(set), Some(("MAP.keys", [map])) if has_key(map, key))
            }
            Some(("MAP.in_keys", [key, map])) => has_key(map, key),
            _ => false,
        },
    }
}

/// Whether the atom is false on every instance where it is defined.
fn fails_where_defined(atom: &Atom) -> bool {
    matches!(atom, Atom::Less(left, right) if left == right)
}

/// Whether the map term `map` has an entry with the key `key`.
fn has_key(map: &Term, key: &Term) -> bool {
    matches!(map.kind(), TermKind::Map { entries, .. } if entries.iter().any(|(entry, _)| entry == key))
}

#[cfg(test)]
mod tests;
