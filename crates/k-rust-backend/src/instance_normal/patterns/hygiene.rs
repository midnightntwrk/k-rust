//! Keeping apart the variables of the terms the pattern facts build.
//!
//! Each axiom quantifies its variables on its own, and so does the pattern being read. A term
//! the facts build from material of a second source (another equation's sides, a stored
//! representative or value root, another narrowing's result) must denote every instance of the
//! combination; were two independent variables to share a name, it would denote only the
//! instances where they are equal, and the readers that see variable identity (instance
//! normality's unification, which binds consistently, and the joins' matching and equality)
//! would answer for those only.
//!
//! So every variable of a built term is either one of the read term's own (shared with its
//! context on purpose) or was minted for that one use, and this module is the only place that
//! makes either kind of name:
//!
//! - an [`Apart`] is a term whose variables other than the read term's were minted for it
//!   alone. It is made only by [`Apart::copy`] / [`Apart::copies`] (every variable renamed
//!   fresh: another equation's left-hand side, the instance of a peak) and by
//!   [`Completion::apply`] (an equation's side under a narrowing's bindings, every variable they
//!   leave unbound minted fresh: a reduct, a composed narrowing);
//! - a [`Stored`] is a term kept across uses (an overlapped instance, an overlap
//!   representative, a value root). Its variables are all renamed canonically, so that two
//!   copies that differ only in their names are one stored term, and it can be read only
//!   through [`Stored::fresh`], an [`Apart`] copy for that one use.
//!
//! Fresh names are `{base}!narrow{n}`, `n` drawn from one process-wide counter: no KORE
//! identifier has a `!`, and no two uses share a number, so names minted in different calls
//! never meet, however deeply their results are later nested into one another. Canonical names
//! are `{base}!rep{i}`. Built terms are compared up to the minted names ([`shape_hash`],
//! [`renamed_from`]); those comparisons read, they never combine.

use std::{
    hash::{Hash, Hasher},
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_hash::FxHasher;

use super::super::token;
use crate::{
    substitution::{Substitution, substitute},
    term::{Term, TermKind, Variable},
};

/// A term whose variables, other than those of the term being read, carry names minted for it
/// alone ([module documentation](self)).
#[derive(Clone, Debug)]
pub(super) struct Apart(Term);

impl Apart {
    /// `term` with every variable renamed fresh: an independent copy, for a term of a second
    /// source that a narrowing reads beside the term being read.
    pub(super) fn copy(term: &Term) -> Self {
        Self(substitute(term, &fresh_names(&term.attributes().variables)))
    }

    /// The terms `terms` renamed fresh by one renaming: independent of every other term, and
    /// sharing among themselves exactly the variables they shared before.
    pub(super) fn copies<const N: usize>(terms: [&Term; N]) -> [Self; N] {
        let variables = terms
            .iter()
            .flat_map(|term| term.attributes().variables.iter())
            .collect::<std::collections::BTreeSet<_>>();
        let renaming = fresh_names(variables);
        terms.map(|term| Self(substitute(term, &renaming)))
    }

    pub(super) fn term(&self) -> &Term {
        &self.0
    }

    pub(super) fn into_term(self) -> Term {
        self.0
    }
}

/// A substitution for every variable of one equation: the bindings a narrowing found for them,
/// each to a subterm of the term read, and a name minted for this use for each variable the
/// narrowing left unbound. An instance of a side of that equation under it shares no name with
/// anything but the term read.
#[derive(Debug)]
pub(super) struct Completion(Substitution);

impl Completion {
    /// `binding`, a narrowing's bindings of an equation's variables, completed over
    /// `variables`, the variables of the equation's sides that will be instantiated.
    pub(super) fn of<'a>(
        mut binding: Substitution,
        variables: impl IntoIterator<Item = &'a Variable>,
    ) -> Self {
        let unbound = variables
            .into_iter()
            .filter(|variable| !binding.contains_key(*variable))
            .collect::<Vec<_>>();
        binding.extend(fresh_names(unbound));
        Self(binding)
    }

    /// The instance of `side`, a term over the completed variables (and names minted for the
    /// representatives a narrowing bound them to). Substitution is
    /// simultaneous, so a bound term that holds a variable named like one of the equation's
    /// keeps it as the read term's.
    pub(super) fn apply(&self, side: &Term) -> Apart {
        debug_assert!(
            side.attributes()
                .variables
                .iter()
                .all(|variable| self.0.contains_key(variable) || minted(variable)),
            "every variable of the equation in an instantiated side is completed"
        );
        Apart(substitute(side, &self.0))
    }
}

/// A term kept across uses, every variable renamed canonically `{base}!rep{i}` (numbered in
/// order of first occurrence, outermost and leftmost first). The renaming is one-to-one by
/// construction and keeps no name, since nothing outside a stored term shares one of its
/// variables: copies that differ only in their names are one stored term, which is what the
/// rounds of the pattern facts compare, and every use reads a fresh copy ([`Stored::fresh`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Stored(Term);

impl Stored {
    pub(super) fn new(term: &Term) -> Self {
        fn visit(term: &Term, order: &mut Vec<Variable>) {
            match term.kind() {
                TermKind::Variable(variable) => {
                    if !order.contains(variable) {
                        order.push(variable.clone());
                    }
                }
                _ => {
                    token::every_immediate_subterm(term, |subterm| {
                        visit(subterm, order);
                        true
                    });
                }
            }
        }
        if term.attributes().variables.is_empty() {
            return Self(term.clone());
        }
        let mut order = Vec::new();
        visit(term, &mut order);
        let renaming = order
            .into_iter()
            .enumerate()
            .map(|(index, variable)| {
                let renamed = variable.with_name(format!("{}!rep{index}", base(&variable)));
                (variable, Term::variable(renamed))
            })
            .collect::<Substitution>();
        Self(substitute(term, &renaming))
    }

    /// A copy for one use, apart from every other term.
    pub(super) fn fresh(&self) -> Apart {
        Apart::copy(&self.0)
    }
}

/// The counter of the names [`fresh_names`] mints. One counter for the process, so no two
/// uses mint the same name, however the terms they build are later nested into one another.
static MINTED: AtomicU64 = AtomicU64::new(0);

/// The marker between the base and the counter of a name [`fresh_names`] mints.
const MINTED_MARKER: &str = "!narrow";

/// A variable's name before any `!`: its KORE name.
fn base(variable: &Variable) -> &str {
    variable.name.split('!').next().unwrap_or_default()
}

/// Each of `variables` mapped to a variable of its kind and sort named `{base}!narrow{n}`, `n`
/// drawn from [`MINTED`]: a name no KORE identifier spells (they have no `!`) and no other use
/// of this function mints.
fn fresh_names<'a>(variables: impl IntoIterator<Item = &'a Variable>) -> Substitution {
    variables
        .into_iter()
        .map(|variable| {
            let counter = MINTED.fetch_add(1, Ordering::Relaxed);
            let fresh = variable.with_name(format!("{}{MINTED_MARKER}{counter}", base(variable)));
            (variable.clone(), Term::variable(fresh))
        })
        .collect()
}

/// Whether `variable` is one [`fresh_names`] minted.
pub(super) fn minted(variable: &Variable) -> bool {
    variable.name.contains(MINTED_MARKER)
}

/// A hash of `term` that two terms differing only in the names of the variables `kept` does not
/// keep share: those variables count by their sort and the order of their first occurrence.
/// A collection counts by its own hash, so collections that differ in such names hash apart,
/// which only makes [`renamed_from`] asked less often.
pub(super) fn shape_hash(term: &Term, kept: &dyn Fn(&Variable) -> bool) -> u64 {
    fn walk<'a>(
        term: &'a Term,
        kept: &dyn Fn(&Variable) -> bool,
        order: &mut Vec<&'a Variable>,
        hasher: &mut FxHasher,
    ) {
        match term.kind() {
            TermKind::Variable(variable) if kept(variable) => {
                0u8.hash(hasher);
                variable.hash(hasher);
            }
            TermKind::Variable(variable) => {
                1u8.hash(hasher);
                variable.kind.hash(hasher);
                variable.sort.hash(hasher);
                match order.iter().position(|known| *known == variable) {
                    Some(index) => index.hash(hasher),
                    None => {
                        order.len().hash(hasher);
                        order.push(variable);
                    }
                }
            }
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } => {
                2u8.hash(hasher);
                symbol.name.hash(hasher);
                sort_arguments.hash(hasher);
                arguments.len().hash(hasher);
                for argument in arguments {
                    walk(argument, kept, order, hasher);
                }
            }
            TermKind::Injection {
                source,
                target,
                term,
            } => {
                3u8.hash(hasher);
                source.hash(hasher);
                target.hash(hasher);
                walk(term, kept, order, hasher);
            }
            TermKind::And(first, second) => {
                4u8.hash(hasher);
                walk(first, kept, order, hasher);
                walk(second, kept, order, hasher);
            }
            TermKind::DomainValue { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => {
                5u8.hash(hasher);
                term.hash(hasher);
            }
        }
    }
    let mut hasher = FxHasher::default();
    walk(term, kept, &mut Vec::new(), &mut hasher);
    hasher.finish()
}

/// Whether `second` is `first` with the variables `kept` does not keep renamed one-to-one. A
/// collection is compared as written, which only answers `false` more often.
pub(super) fn renamed_from(first: &Term, second: &Term, kept: &dyn Fn(&Variable) -> bool) -> bool {
    fn walk<'a>(
        first: &'a Term,
        second: &'a Term,
        kept: &dyn Fn(&Variable) -> bool,
        renaming: &mut Vec<(&'a Variable, &'a Variable)>,
    ) -> bool {
        match (first.kind(), second.kind()) {
            (TermKind::Variable(left), TermKind::Variable(right)) => {
                if kept(left) || kept(right) {
                    return left == right;
                }
                match renaming.iter().find(|(from, _)| *from == left) {
                    Some((_, to)) => *to == right,
                    None if renaming.iter().any(|(_, to)| *to == right) => false,
                    None => {
                        renaming.push((left, right));
                        true
                    }
                }
            }
            (
                TermKind::Application {
                    symbol: first_symbol,
                    sort_arguments: first_sorts,
                    arguments: first_arguments,
                },
                TermKind::Application {
                    symbol: second_symbol,
                    sort_arguments: second_sorts,
                    arguments: second_arguments,
                },
            ) => {
                first_symbol.name == second_symbol.name
                    && first_sorts == second_sorts
                    && first_arguments.len() == second_arguments.len()
                    && first_arguments
                        .iter()
                        .zip(second_arguments)
                        .all(|(first, second)| walk(first, second, kept, renaming))
            }
            (
                TermKind::Injection {
                    source: first_source,
                    target: first_target,
                    term: first,
                },
                TermKind::Injection {
                    source: second_source,
                    target: second_target,
                    term: second,
                },
            ) => {
                first_source == second_source
                    && first_target == second_target
                    && walk(first, second, kept, renaming)
            }
            (TermKind::And(first_left, first_right), TermKind::And(second_left, second_right)) => {
                walk(first_left, second_left, kept, renaming)
                    && walk(first_right, second_right, kept, renaming)
            }
            _ => first == second,
        }
    }
    walk(first, second, kept, &mut Vec::new())
}
