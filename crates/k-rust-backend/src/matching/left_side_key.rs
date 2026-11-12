//! The part of an equation's left-hand side that decides, from the roots of a subject's
//! arguments alone, that the left-hand side does not match the subject.
//!
//! Equation selection files an equation under the root of its left-hand side
//! (`rule::term_index`), so every equation rooted at a symbol is offered to every application of
//! that symbol. A left-hand side says more than its root: `kseq(inj{S, KItem}(P), dotk())`
//! matches only a sequence of one item that is a value of `S`. [`LeftSideKey`] keeps what the
//! arguments of the left-hand side say in that way, and [`LeftSideKey::refutes`] reads it
//! against a subject before the equation is attempted, so that an equation is attempted only
//! on a term the key does not exclude.
//!
//! # What a key states
//!
//! A key refutes a subject only where no instance of the subject is an instance of the
//! left-hand side, which is what [`MatchFailed`] states. It rests on three facts.
//!
//! 1. Arguments. The left-hand side and the subject are applications `f(p1, .., pn)` and
//!    `f(t1, .., tn)` of one symbol with equal sort arguments. Where `f` is a free
//!    constructor, two applications are equal exactly when their arguments are. Where `f` is a
//!    function no algebraic axiom identifies applications of, the equation is applied to the
//!    application as it is written, by an instance of its arguments. In both cases the
//!    left-hand side matches only if every `pi` matches `ti`, so one argument pair that cannot
//!    match refutes the equation at the subject, whatever the other pairs are. No key is kept
//!    for any other root: an equation head, a function with algebraic axioms, an
//!    uninterpreted symbol, a macro or an alias.
//! 2. Constructors. Two applications of free constructors with different symbols, neither in
//!    an overload relation, denote different values on every valuation: no instance of one is
//!    an instance of the other. An overloaded production is excluded because an overload
//!    equation may identify it with an application of another production.
//! 3. Injections. `inj{S, T}(p)` denotes values of `T` that are values of `S`. A domain value
//!    of sort `S'`, and an application of a free constructor of `S'` outside every overload
//!    relation, is a value of exactly the sorts `S'` is below. So `inj{S', T}(t)` with such an
//!    operand `t` is an instance of `inj{S, T}(p)` only if `S'` is `S` or below it. Where the
//!    subsort order decides that it is neither, the pair is refuted whatever `p` is: `p` may be
//!    a variable or a function application, since the refutation reads the sort `p` has and not
//!    its value.
//!
//! A subject argument whose root does not fix its value this way (a variable, a function
//! application, an equation head, a conjunction, a collection) is never read as a refutation:
//! it may denote a value the left-hand side's argument matches, so the equation stays offered.
//! The key reads no domain value's text, so it is the same in every model of a literal whose
//! element the definition leaves open (`crate::literal`).
//!
//! # Agreement with the matcher
//!
//! Every pair a key refutes is one `Matcher::match_one` fails: two free constructors of
//! different symbols by the root policy (`refutes_another_symbol`), and two injections of
//! different source sorts by `match_differing_injections`, whose arms for a subject operand
//! that is a domain value or a non-overloaded free-constructor application all fail when the
//! order is `Below` or `Incomparable`. The matcher reaches each argument pair of a decomposed
//! root unless an earlier pair failed, and a failed pair fails the match. One outcome differs:
//! where another pair of the same match decomposes two applications of a function with
//! algebraic axioms, the matcher reports the whole match as open rather than failed. The key's
//! refutation holds there too, by fact 1: the refuted pair is an argument of the root, not of
//! that function.

use std::sync::Arc;

use super::{MatchFailed, SortGraph, SortOrder};
use crate::{
    definition::{BackendDefinition, OverloadGraph},
    term::{HeadRole, Name, Sort, Sorts, SymbolType, Term, TermKind, head::Shape},
};

/// What the arguments of an equation's left-hand side state about the roots of a matching
/// subject's arguments (the module documentation); empty for a left-hand side that states
/// nothing a subject's roots decide. A function of the left-hand side and of the definition's
/// symbol roles and overload relations: renaming the equation's variables keeps it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LeftSideKey(Option<Arc<RootKey>>);

#[derive(Debug, Eq, PartialEq)]
struct RootKey {
    symbol: Name,
    sort_arguments: Sorts,
    arguments: Box<[ArgumentKey]>,
}

/// What one argument of a left-hand side states about the subject's argument at its position.
#[derive(Debug, Eq, PartialEq)]
enum ArgumentKey {
    /// Nothing the subject's root decides.
    Open,
    /// An application of this free constructor, which is in no overload relation.
    Constructor(Name),
    /// An injection from `source` into `target`, both closed sorts, of an operand with the key
    /// `operand`.
    Injection {
        source: Sort,
        target: Sort,
        operand: Box<ArgumentKey>,
    },
}

impl LeftSideKey {
    /// The key of the left-hand side `lhs` of a function or simplification equation of
    /// `definition`, whose symbol declarations and overload relations are loaded.
    #[must_use]
    pub(crate) fn of(definition: &BackendDefinition, lhs: &Term) -> Self {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = lhs.kind()
        else {
            return Self::default();
        };
        if !compares_arguments(symbol.attributes.head_role(), symbol.attributes.symbol_type) {
            return Self::default();
        }
        let arguments = arguments
            .iter()
            .map(|argument| ArgumentKey::of(definition.overloads(), argument))
            .collect::<Box<[_]>>();
        if arguments.iter().all(|key| matches!(key, ArgumentKey::Open)) {
            return Self::default();
        }
        Self(Some(Arc::new(RootKey {
            symbol: symbol.name.clone(),
            sort_arguments: *sort_arguments,
            arguments,
        })))
    }

    /// Whether the key decides that the left-hand side it was built from does not match
    /// `subject`: `subject` is an application of the left-hand side's symbol with its sort
    /// arguments and arity, and some argument pair cannot match (the module documentation).
    /// `None` states nothing: the equation is attempted.
    #[inline]
    #[must_use]
    pub fn refutes(&self, definition: &BackendDefinition, subject: &Term) -> Option<MatchFailed> {
        let key = self.0.as_deref()?;
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = subject.kind()
        else {
            return None;
        };
        if symbol.name != key.symbol
            || *sort_arguments != key.sort_arguments
            || arguments.len() != key.arguments.len()
        {
            return None;
        }
        key.arguments
            .iter()
            .zip(arguments)
            .any(|(key, argument)| {
                key.refutes(definition.sort_graph(), definition.overloads(), argument)
            })
            .then_some(MatchFailed(()))
    }
}

/// Whether a left-hand side rooted at a symbol with this role matches a subject application of
/// the symbol only argument by argument (fact 1 of the module documentation).
#[deny(clippy::wildcard_enum_match_arm)]
fn compares_arguments(role: HeadRole, symbol_type: SymbolType) -> bool {
    match role {
        HeadRole::FreeConstructor => true,
        HeadRole::Function {
            refutable_arguments,
            ..
        } => refutable_arguments && matches!(symbol_type, SymbolType::Function(_)),
        HeadRole::EquationHead | HeadRole::Residual | HeadRole::Uninterpreted => false,
    }
}

/// The name of the free constructor `term` is an application of, when that constructor is in no
/// overload relation: the root of every value `term` denotes.
fn free_constructor<'t>(overloads: &OverloadGraph, term: &'t Term) -> Option<&'t Name> {
    let TermKind::Application { symbol, .. } = term.kind() else {
        return None;
    };
    (term.shape() == Shape::Application(HeadRole::FreeConstructor)
        && !overloads.is_overloaded(&symbol.name))
    .then_some(&symbol.name)
}

impl ArgumentKey {
    fn of(overloads: &OverloadGraph, pattern: &Term) -> Self {
        match pattern.kind() {
            TermKind::Injection {
                source,
                target,
                term,
            } if !source.has_variable() && !target.has_variable() => Self::Injection {
                source: *source,
                target: *target,
                operand: Box::new(Self::of(overloads, term)),
            },
            _ => free_constructor(overloads, pattern)
                .map_or(Self::Open, |name| Self::Constructor(name.clone())),
        }
    }

    /// Whether no instance of `subject` is an instance of the argument this key was built from
    /// (facts 2 and 3 of the module documentation).
    fn refutes(&self, sorts: &SortGraph, overloads: &OverloadGraph, subject: &Term) -> bool {
        match self {
            Self::Open => false,
            Self::Constructor(name) => {
                free_constructor(overloads, subject).is_some_and(|subject| subject != name)
            }
            Self::Injection {
                source,
                target,
                operand,
            } => {
                let TermKind::Injection {
                    source: subject_source,
                    target: subject_target,
                    term: subject_operand,
                } = subject.kind()
                else {
                    return false;
                };
                if target != subject_target {
                    return false;
                }
                if source == subject_source {
                    return operand.refutes(sorts, overloads, subject_operand);
                }
                // The operand is a value of exactly the sorts its own sort is below, and the
                // order decides that the left-hand side's source is not one of them.
                (subject_operand.shape() == Shape::DomainValue
                    || free_constructor(overloads, subject_operand).is_some())
                    && matches!(
                        sorts.order(source, subject_source),
                        SortOrder::Below | SortOrder::Incomparable
                    )
            }
        }
    }
}
