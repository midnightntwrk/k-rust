//! What the check reads from the conditions of a pair, after the simplifier has simplified their
//! conjunction with every claim withheld.
//!
//! The simplifier refutes a conjunction it evaluates to `\bottom`. Two propositional facts it does
//! not use are decided here, on the conjuncts it leaves:
//!
//! - **complementary literals**: a Boolean atom required true by one conjunct and false by another
//!   (`N >Int M` beside `N <=Int M`, `notBool B` beside `B`). Comparisons are read up to their
//!   arithmetic identities (`a >Int b` is `b <Int a`, `a <=Int b` is `notBool (b <Int a)`,
//!   `a =/=Int b` is `notBool (a ==Int b)`), so the conjunction holds on no instance;
//! - **atoms true on every instance where they are defined**: `K in keys(M)` (`SET.in` of
//!   `MAP.keys`, or `MAP.in_keys`) where `K` is the key of an entry of the map term `M`, and
//!   `A ==K A`. Required false, such an atom makes the conjunction false wherever it is defined,
//!   and undefined elsewhere: a condition holds only where it is defined and true.
//!
//! Every remaining conjunct `X = t` (a variable equal to a term without `X`) is an equality every
//! instance satisfying the conditions has, which the join may apply (`confluence.rs`).

use rustc_hash::FxHashMap;

use crate::{
    rule::Predicate,
    substitution::{Substitution, substitute},
    term::{Term, TermKind},
};

/// A Boolean atom up to the arithmetic identities above.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Atom {
    /// `left <Int right`.
    Less(Term, Term),
    /// `left == right` (`INT.eq`, `KEQUAL.eq`, `BOOL.eq`), arguments in term order.
    Equal(Term, Term),
    Other(Term),
}

/// Whether the conjuncts are contradictory by complementary literals or by an atom required false
/// that holds wherever it is defined.
pub(super) fn contradictory(conjuncts: &[Predicate]) -> bool {
    let mut seen = FxHashMap::<Atom, bool>::default();
    for conjunct in conjuncts {
        let Some((term, polarity)) = literal(conjunct) else {
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
    false
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
fn literal(conjunct: &Predicate) -> Option<(Term, bool)> {
    match conjunct {
        Predicate::Equals(left, right) => match (boolean(left), boolean(right)) {
            (Some(value), None) => Some((right.clone(), value)),
            (None, Some(value)) => Some((left.clone(), value)),
            _ => None,
        },
        Predicate::Term(term) => Some((term.clone(), true)),
        Predicate::Not(inner) => literal(inner).map(|(term, polarity)| (term, !polarity)),
        _ => None,
    }
}

/// The value of a Boolean domain value.
fn boolean(term: &Term) -> Option<bool> {
    match term.kind() {
        TermKind::DomainValue { value, .. } => match value.as_bytes() {
            b"true" => Some(true),
            b"false" => Some(false),
            _ => None,
        },
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
        Some(("INT.le", [left, right])) => (Atom::Less(right.clone(), left.clone()), !polarity),
        Some(("INT.ge", [left, right])) => (Atom::Less(left.clone(), right.clone()), !polarity),
        Some(("INT.eq" | "KEQUAL.eq" | "BOOL.eq", [left, right])) => {
            let (left, right) = ordered(left, right);
            (Atom::Equal(left, right), polarity)
        }
        Some(("INT.ne" | "KEQUAL.ne" | "BOOL.ne", [left, right])) => {
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
