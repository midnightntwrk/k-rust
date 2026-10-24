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
//! - **linear integer arithmetic**: each comparison of integer terms (and each ML `\equals`
//!   between them) is read as a linear form `Σ c·a + k` over *atoms*, the maximal integer
//!   subterms that are not `+Int`, `-Int`, `*Int` by a literal or an integer literal (all total
//!   and exact on the unbounded integers, so the form denotes the comparison exactly where its
//!   atoms are defined), compared with 0. A constant form decides its conjunct; a form `a + k`,
//!   `-a + k` or `a - b + k` is a difference constraint `x - y <= w` (strict comparisons tighten
//!   by 1 over the integers); any other form is ignored. The atoms' range facts, theorems of their
//!   hooks wherever the atom is defined, are added: `STRING.length`, `BYTES.length`, `LIST.size`,
//!   `MAP.size`, `SET.size` and `INT.abs` are at least 0, `INT.abs(x)` and `INT.max(x, y)` at
//!   least each operand of the form `atom + k`, `INT.min(x, y)` at most each. Difference
//!   constraints over the integers have a solution exactly when their graph has no negative cycle
//!   (Floyd and Warshall), and a disequality `x - y =/= k` fails where the closure forces
//!   `x - y = k`; then the conjunction is refuted. A conjunct is used only when it shows its atoms
//!   defined (a comparison required true or false, or an `\equals` with a `ceil_free` side), or
//!   every atom it mentions is `ceil_free` or shown defined by another conjunct: a `\not` holds
//!   also where an atom is undefined. Two variables the closure forces equal are an equality the
//!   join may apply. The bounds above are the special case of one atom; they are kept for their
//!   excluded points;
//! - **literals under `\not`**: a `\not` of a literal holds also where its term is undefined, so
//!   it is read as the negated literal only where the term is defined on every instance where the
//!   conjunction holds: it is `ceil_free`, another conjunct requires the same atom, or its only
//!   partial subterms are integer quotients and remainders by divisors another conjunct states
//!   nonzero (`X /Int Y` beside `\not(\equals(Y, 0))`, the definedness the simplifier states for
//!   a condition as a sibling conjunct);
//! - **disjunctions**: a conjunct `\or(d1, ..., dk)`, `a orBool b` or `a orElseBool b` required
//!   true, or `a andBool b` or `a andThenBool b` required false (not under `\not`), holds only
//!   where one of its disjuncts holds (`a` or `b` true, respectively false), so the conjunction is
//!   refuted when, for every choice of one disjunct per such conjunct, the choices with the other
//!   conjuncts are refuted by the rules above; at most three such conjuncts and 16 choices are
//!   split, beyond that the disjunctions are not read;
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
    contradictory_without_cases(definition, conjuncts) || cases_contradictory(definition, conjuncts)
}

/// The most disjunctive conjuncts, and the most combinations of their disjuncts, that
/// [`cases_contradictory`] splits on.
const DISJUNCTIONS: usize = 3;
const DISJUNCT_CASES: usize = 16;

/// The disjuncts of a conjunct that holds only where one of them does: an ML `\or`, or a
/// connective required true or false not under `\not` (`a orBool b` or `a orElseBool b`
/// required true holds only where `a` or `b` is `true`; `a andBool b` or `a andThenBool b`
/// required false, also written `notBool (a andBool b)`, only where one is `false`).
fn disjuncts(definition: &BackendDefinition, conjunct: &Predicate) -> Option<Vec<Predicate>> {
    if let Predicate::Or(items) = conjunct {
        return Some(items.to_vec());
    }
    if matches!(conjunct, Predicate::Not(_)) {
        return None;
    }
    let (mut term, mut polarity) = literal(definition, conjunct)?;
    while let Some(("BOOL.not", [inner])) = hooked(&term) {
        let inner = inner.clone();
        term = inner;
        polarity = !polarity;
    }
    let (value, [left, right]) = (match hooked(&term)? {
        ("BOOL.or" | "BOOL.orElse", operands) if polarity => Some((true, operands)),
        ("BOOL.and" | "BOOL.andThen", operands) if !polarity => Some((false, operands)),
        _ => None,
    })?
    else {
        return None;
    };
    let side = |operand: &Term| {
        let literal = definition
            .domain_value(operand.sort(), if value { "true" } else { "false" })
            .ok()?;
        Some(Predicate::Equals(operand.clone(), literal))
    };
    Some(vec![side(left)?, side(right)?])
}

/// Whether the conjuncts are contradictory by cases: for at most [`DISJUNCTIONS`] disjunctive
/// conjuncts and [`DISJUNCT_CASES`] combinations of their disjuncts, every combination with the
/// other conjuncts is contradictory ([`contradictory_without_cases`]). A disjunctive conjunct
/// holds only where one of its disjuncts does, so the conjunction holds only where one of the
/// combinations does.
fn cases_contradictory(definition: &BackendDefinition, conjuncts: &[Predicate]) -> bool {
    let mut split = Vec::new();
    let mut rest = Vec::new();
    for conjunct in conjuncts {
        match disjuncts(definition, conjunct) {
            Some(disjuncts) if split.len() < DISJUNCTIONS => split.push(disjuncts),
            _ => rest.push(conjunct.clone()),
        }
    }
    let cases = split.iter().map(Vec::len).product::<usize>();
    if split.is_empty() || cases > DISJUNCT_CASES {
        return false;
    }
    let misread = super::switches::active().misread_disjunction;
    let mut refuted = 0;
    for case in 0..cases {
        let mut conjunction = rest.clone();
        let mut index = case;
        for disjuncts in &split {
            let mut chosen = BTreeSet::new();
            super::flatten(disjuncts[index % disjuncts.len()].clone(), &mut chosen);
            conjunction.extend(chosen);
            index /= disjuncts.len();
        }
        if conjunction.contains(&Predicate::False)
            || contradictory_without_cases(definition, &conjunction)
        {
            refuted += 1;
            if misread {
                return true;
            }
        }
    }
    refuted == cases
}

/// [`contradictory`] without splitting disjunctions.
fn contradictory_without_cases(definition: &BackendDefinition, conjuncts: &[Predicate]) -> bool {
    let mut seen = FxHashMap::<Atom, bool>::default();
    // A literal under `\not` holds also where its term is undefined: it is read only where the
    // term is `ceil_free` or a literal not under `\not` requires the same atom (which shows it
    // defined wherever the conjunction holds).
    // A literal not under `\not` that requires `d =/=Int 0` shows `d` nonzero, so a quotient or
    // remainder by `d` is defined wherever the conjunction holds.
    let zero = |term: &Term| integer(definition, term) == Some(BigInt::from(0));
    let nonzero = conjuncts
        .iter()
        .filter_map(|conjunct| {
            // `\not(\equals(d, 0))`: `d` is nonzero wherever it is defined, which a quotient by
            // it also needs (`defined_given` asks both).
            if let Predicate::Not(inner) = conjunct {
                return match &**inner {
                    Predicate::Equals(left, right) if zero(right) => Some(left.clone()),
                    Predicate::Equals(left, right) if zero(left) => Some(right.clone()),
                    _ => None,
                };
            }
            let (term, polarity) = literal(definition, conjunct)?;
            match atom(&term, polarity) {
                (Atom::Equal(left, right), false) => {
                    match (integer(definition, &left), integer(definition, &right)) {
                        (Some(zero), None) if zero == BigInt::from(0) => Some(right),
                        (None, Some(zero)) if zero == BigInt::from(0) => Some(left),
                        _ => None,
                    }
                }
                _ => None,
            }
        })
        .collect::<BTreeSet<_>>();
    let read = conjuncts
        .iter()
        .filter_map(|conjunct| {
            let (term, polarity) = literal(definition, conjunct)?;
            let defined = !matches!(conjunct, Predicate::Not(_)) || defined_given(&term, &nonzero);
            let (atom, polarity) = atom(&term, polarity);
            Some((atom, polarity, defined))
        })
        .collect::<Vec<_>>();
    let shown = read
        .iter()
        .filter(|(_, _, defined)| *defined)
        .map(|(atom, _, _)| atom.clone())
        .collect::<rustc_hash::FxHashSet<_>>();
    for (atom, polarity, defined) in read {
        if !defined && !shown.contains(&atom) {
            continue;
        }
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
        || Differences::of(definition, conjuncts).is_none()
}

/// Whether `term` is defined on every instance where each term of `nonzero` is a nonzero integer:
/// it is `ceil_free`, or an application of a total symbol (or a constructor) to such terms, or an
/// integer quotient or remainder (`INT.tdiv`, `tmod`, `ediv`, `emod`, each defined exactly where
/// its divisor is nonzero) of such terms by a term of `nonzero`.
fn defined_given(term: &Term, nonzero: &BTreeSet<Term>) -> bool {
    use crate::term::{FunctionType, SymbolType};
    if term.attributes().ceil_free() {
        return true;
    }
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return false;
    };
    let arguments_defined = || {
        arguments
            .iter()
            .all(|argument| defined_given(argument, nonzero))
    };
    match (symbol.attributes.hook.as_deref(), arguments.as_slice()) {
        (Some("INT.tdiv" | "INT.tmod" | "INT.ediv" | "INT.emod"), [_, divisor]) => {
            nonzero.contains(divisor) && arguments_defined()
        }
        _ => {
            matches!(
                symbol.attributes.symbol_type,
                SymbolType::Constructor | SymbolType::Function(FunctionType::Total)
            ) && symbol.attributes.collection.is_none()
                && arguments_defined()
        }
    }
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
/// true or false (not under `\not`), an ML `\equals(t, u)` neither of whose sides is a Boolean
/// literal, or its `\not`. The operands of `KEQUAL.eq` that are one-element sequences of an injection from one
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
    // An atom required true or false holds only where its operands are defined; a `\not` of
    // such a requirement holds also where one is undefined, which no class describes.
    if matches!(conjunct, Predicate::Not(_)) {
        return None;
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

/// A linear integer form `constant + Σ coefficient · atom` over atoms, the maximal subterms of
/// integer kind that are not `+Int`, `-Int`, `*Int` by a literal, or an integer literal.
#[derive(Clone, Debug, Default)]
struct Linear {
    constant: BigInt,
    atoms: std::collections::BTreeMap<Term, BigInt>,
    /// Every atom the terms mention, also those whose coefficients cancel: the form denotes the
    /// terms only where all of them are defined.
    mentioned: BTreeSet<Term>,
}

impl Linear {
    fn atom(term: &Term) -> Self {
        Self {
            constant: BigInt::from(0),
            atoms: [(term.clone(), BigInt::from(1))].into(),
            mentioned: [term.clone()].into(),
        }
    }

    fn add(mut self, other: Self, sign: i32) -> Self {
        self.mentioned.extend(other.mentioned);
        self.constant += BigInt::from(sign) * other.constant;
        for (atom, coefficient) in other.atoms {
            *self.atoms.entry(atom).or_default() += BigInt::from(sign) * coefficient;
        }
        self.atoms
            .retain(|_, coefficient| *coefficient != BigInt::from(0));
        self
    }

    fn scale(mut self, factor: &BigInt) -> Self {
        self.constant *= factor;
        for coefficient in self.atoms.values_mut() {
            *coefficient *= factor;
        }
        self.atoms
            .retain(|_, coefficient| *coefficient != BigInt::from(0));
        self
    }
}

/// `term`, of integer kind, as a linear form: `+Int`, `-Int` and `*Int` by an integer literal
/// are total and exact on the unbounded integers, so the form denotes the term exactly where its
/// atoms are defined.
fn linear(definition: &BackendDefinition, term: &Term) -> Linear {
    if let Some(value) = integer(definition, term) {
        return Linear {
            constant: value,
            ..Linear::default()
        };
    }
    match hooked(term) {
        Some(("INT.add", [left, right])) => {
            linear(definition, left).add(linear(definition, right), 1)
        }
        Some(("INT.sub", [left, right])) => {
            linear(definition, left).add(linear(definition, right), -1)
        }
        Some(("INT.mul", [left, right])) => {
            let (left, right) = (linear(definition, left), linear(definition, right));
            if left.mentioned.is_empty() {
                right.scale(&left.constant)
            } else if right.mentioned.is_empty() {
                left.scale(&right.constant)
            } else {
                Linear::atom(term)
            }
        }
        _ => Linear::atom(term),
    }
}

/// The linear constraint `form <relation> 0` a conjunct states between two integer terms, and
/// whether the conjunct holding shows its atoms defined: a comparison required true or false (or
/// written as a term), and an ML `\equals` with a `ceil_free` side; a `\not` of either holds also
/// where an atom is undefined.
fn linear_constraint(
    definition: &BackendDefinition,
    conjunct: &Predicate,
) -> Option<(Linear, Relation, bool)> {
    let is_int = |term: &Term| definition.domain_kind(&term.sort()) == Some(DomainKind::Int);
    let (mut term, mut polarity) = match conjunct {
        Predicate::Not(inner) => {
            let (form, relation, _) = linear_constraint(definition, inner)?;
            return Some((form, relation.negated(), false));
        }
        Predicate::Equals(left, right) => {
            match (boolean(definition, left), boolean(definition, right)) {
                (Some(value), None) => (right.clone(), value),
                (None, Some(value)) => (left.clone(), value),
                (None, None) if is_int(left) && is_int(right) => {
                    let form = linear(definition, left).add(linear(definition, right), -1);
                    let shows = left.attributes().ceil_free() || right.attributes().ceil_free();
                    return Some((form, Relation::Equal, shows));
                }
                _ => return None,
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
    let (hook, [left, right]) = hooked(&term)? else {
        return None;
    };
    let relation = match hook {
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
    let form = linear(definition, left).add(linear(definition, right), -1);
    Some((form, relation, true))
}

/// The difference constraints `x - y <= w` between the atoms of the conjuncts' linear
/// constraints (and a zero node), closed by Floyd and Warshall (module documentation, "linear
/// integer arithmetic").
struct Differences {
    atoms: Vec<Term>,
    /// `bound[i][j]`: an upper bound of `atom i - atom j` (index 0 is the constant 0).
    bound: Vec<Vec<Option<BigInt>>>,
}

impl Differences {
    fn index(&mut self, atom: &Term) -> usize {
        if let Some(position) = self.atoms.iter().position(|known| known == atom) {
            return position + 1;
        }
        self.atoms.push(atom.clone());
        for row in &mut self.bound {
            row.push(None);
        }
        self.bound.push(vec![None; self.atoms.len() + 1]);
        self.atoms.len()
    }

    /// Record `x - y <= weight`.
    fn edge(&mut self, x: usize, y: usize, weight: BigInt) {
        let cell = &mut self.bound[x][y];
        if cell.as_ref().is_none_or(|known| *known > weight) {
            *cell = Some(weight);
        }
    }

    /// The node and sign of a unit term of a form: `None` for any other coefficient.
    fn unit(&mut self, atom: &Term, coefficient: &BigInt) -> Option<(usize, bool)> {
        let positive = *coefficient == BigInt::from(1);
        (positive || *coefficient == BigInt::from(-1)).then(|| (self.index(atom), positive))
    }

    /// The nodes `(x, y)` and constant `k` with `form = x - y + k`, when the form is a unit or a
    /// difference form (`y` or `x` the zero node for a unit form).
    fn difference(&mut self, form: &Linear) -> Option<(usize, usize, BigInt)> {
        let terms = form.atoms.iter().collect::<Vec<_>>();
        let (x, y) = match terms.as_slice() {
            [(atom, coefficient)] => {
                let (node, positive) = self.unit(atom, coefficient)?;
                if positive { (node, 0) } else { (0, node) }
            }
            [(first, a), (second, b)] => {
                let (first, first_positive) = self.unit(first, a)?;
                let (second, second_positive) = self.unit(second, b)?;
                match (first_positive, second_positive) {
                    (true, false) => (first, second),
                    (false, true) => (second, first),
                    _ => return None,
                }
            }
            _ => return None,
        };
        Some((x, y, form.constant.clone()))
    }

    /// The closure of the conjuncts' difference constraints, with the range facts of their atoms;
    /// `None` when they leave no integer valuation: a constant form false, a negative cycle, or a
    /// disequality the closure forces to fail.
    fn of(definition: &BackendDefinition, conjuncts: &[Predicate]) -> Option<Self> {
        let constraints = conjuncts
            .iter()
            .filter_map(|conjunct| linear_constraint(definition, conjunct))
            .collect::<Vec<_>>();
        // An atom is defined on every instance where the conjunction holds when a conjunct that
        // shows its atoms defined mentions it, or it is `ceil_free`.
        let mut defined = BTreeSet::new();
        for (form, _, shows) in &constraints {
            if *shows {
                defined.extend(form.mentioned.iter().cloned());
            }
        }
        let guard = !super::switches::active().drop_dbm_definedness_guard;
        let mut differences = Self {
            atoms: Vec::new(),
            bound: vec![vec![None]],
        };
        let mut apart = Vec::new();
        for (form, relation, shows) in constraints {
            let usable = shows
                || !guard
                || form
                    .mentioned
                    .iter()
                    .all(|atom| defined.contains(atom) || atom.attributes().ceil_free());
            if !usable {
                continue;
            }
            if form.atoms.is_empty() {
                let zero = BigInt::from(0);
                let holds = match relation {
                    Relation::Less => form.constant < zero,
                    Relation::LessEqual => form.constant <= zero,
                    Relation::Greater => form.constant > zero,
                    Relation::GreaterEqual => form.constant >= zero,
                    Relation::Equal => form.constant == zero,
                    Relation::NotEqual => form.constant != zero,
                };
                if !holds {
                    return None;
                }
                continue;
            }
            let Some((x, y, k)) = differences.difference(&form) else {
                continue;
            };
            // x - y + k <relation> 0.
            match relation {
                Relation::Less => differences.edge(x, y, -k - 1),
                Relation::LessEqual => differences.edge(x, y, -k),
                Relation::Greater => differences.edge(y, x, k - 1),
                Relation::GreaterEqual => differences.edge(y, x, k),
                Relation::Equal => {
                    differences.edge(x, y, -k.clone());
                    differences.edge(y, x, k);
                }
                Relation::NotEqual => apart.push((x, y, -k)),
            }
        }
        differences.range_facts(definition);
        let nodes = differences.bound.len();
        for via in 0..nodes {
            for from in 0..nodes {
                let Some(first) = differences.bound[from][via].clone() else {
                    continue;
                };
                for to in 0..nodes {
                    if let Some(second) = differences.bound[via][to].clone() {
                        differences.edge(from, to, first.clone() + second);
                    }
                }
            }
        }
        if (0..nodes).any(|node| {
            differences.bound[node][node]
                .as_ref()
                .is_some_and(|weight| *weight < BigInt::from(0))
        }) {
            return None;
        }
        for (x, y, value) in apart {
            let at_most = differences.bound[x][y].as_ref() == Some(&value);
            let at_least = differences.bound[y][x].as_ref() == Some(&-value.clone());
            if at_most && at_least {
                return None;
            }
        }
        Some(differences)
    }

    /// The range facts of the atoms (module documentation): each holds wherever its atom is
    /// defined, and every atom here occurs in a constraint that holds only where it is defined.
    fn range_facts(&mut self, definition: &BackendDefinition) {
        let misread = super::switches::active().misread_range_fact;
        let lowest = BigInt::from(if misread { 1 } else { 0 });
        let mut index = 0;
        while index < self.atoms.len() {
            let atom = self.atoms[index].clone();
            let node = index + 1;
            index += 1;
            match hooked(&atom) {
                Some((
                    "STRING.length" | "BYTES.length" | "LIST.size" | "MAP.size" | "SET.size",
                    _,
                )) => self.edge(0, node, -lowest.clone()),
                Some(("INT.abs", [operand])) => {
                    self.edge(0, node, -lowest.clone());
                    self.below(definition, node, operand);
                }
                Some(("INT.max", [left, right])) => {
                    self.below(definition, node, left);
                    self.below(definition, node, right);
                }
                Some(("INT.min", [left, right])) => {
                    self.above(definition, node, left);
                    self.above(definition, node, right);
                }
                _ => {}
            }
        }
    }

    /// Record `operand <= atom node`, when the operand is a unit form.
    fn below(&mut self, definition: &BackendDefinition, node: usize, operand: &Term) {
        let form = linear(definition, operand);
        // operand = x + k (a positive unit form) <= node: x - node <= -k. A negative unit form
        // `k - y <= node` bounds a sum, which is no difference constraint.
        if let Some((x, 0, k)) = self.difference(&form)
            && x != 0
        {
            self.edge(x, node, -k);
        }
    }

    /// Record `atom node <= operand`, when the operand is a unit form.
    fn above(&mut self, definition: &BackendDefinition, node: usize, operand: &Term) {
        let form = linear(definition, operand);
        // node <= x + k: node - x <= k.
        if let Some((x, 0, k)) = self.difference(&form)
            && x != 0
        {
            self.edge(node, x, k);
        }
    }

    /// The pairs of atoms that are variables the closure forces equal.
    fn forced_equal(&self) -> Vec<(Term, Term)> {
        let mut pairs = Vec::new();
        for (i, left) in self.atoms.iter().enumerate() {
            for (j, right) in self.atoms.iter().enumerate().skip(i + 1) {
                let zero = Some(BigInt::from(0));
                if matches!(left.kind(), TermKind::Variable(_))
                    && matches!(right.kind(), TermKind::Variable(_))
                    && self.bound[i + 1][j + 1] == zero
                    && self.bound[j + 1][i + 1] == zero
                {
                    pairs.push((left.clone(), right.clone()));
                }
            }
        }
        pairs
    }
}

/// [`equalities`] of the conjuncts and of the equalities between variables their difference
/// constraints force (`X <=Int Y` beside `Y <=Int X`).
pub(super) fn equalities_with_bounds(
    definition: &BackendDefinition,
    conjuncts: &[Predicate],
) -> Substitution {
    let mut all = conjuncts.to_vec();
    if let Some(differences) = Differences::of(definition, conjuncts) {
        all.extend(
            differences
                .forced_equal()
                .into_iter()
                .map(|(left, right)| Predicate::Equals(left, right)),
        );
    }
    equalities(&all)
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
