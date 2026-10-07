//! This definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Shared traversal rules for K's LHS/RHS-sensitive terms.
//!
//! A position records whether a subterm is matched (`lhs`), built (`rhs`), or both, as a term
//! outside every rewrite of a rule body is. The one walk that decides it, [`scoped_children`],
//! also decides which scope each argument of a local function belongs to; the definition checks
//! and the lowering of local functions (`kompile::passes::resolve_fun`) both read it.
//!
//! Local functions. `#fun(P => B)(E)` (`#fun2(P => B, E)`, or `#fun3(P, B, E)` when the rewrite
//! changes the sort) and `#let P = E #in B` (`#let(P, E, B)`) are each lowered to the application
//! of a generated function `λ(E, C1, .., Cn)` defined by the single equation
//! `λ(P, C1, .., Cn) => B`, whose extra parameters `Ci` are the variables `B` reads from the
//! enclosing term. So:
//!
//! - the pattern `P` and the body `B` form the function's own scope ([`Scope::Lambda`]): `P` is
//!   matched (LHS) and binds its variables in `B` only, and `B` is built (RHS);
//! - the argument `E` is evaluated where the construct stands, in the enclosing scope
//!   ([`Scope::Enclosing`]) and at the construct's own position; `P` does not bind in `E`.
//!
//! `#fun2`'s first argument is the function's whole equation, so it sits at `BODY`, the position
//! of a rule body: the parts outside its rewrites are both the pattern and the result of the
//! equation.

use crate::kast::{InternalLabel, Term};

#[derive(Clone, Copy)]
pub(super) struct TermPosition {
    pub(super) lhs: bool,
    pub(super) rhs: bool,
}

impl TermPosition {
    pub(super) const BODY: Self = Self {
        lhs: true,
        rhs: true,
    };
    pub(super) const CONDITION: Self = Self {
        lhs: false,
        rhs: true,
    };
    pub(super) const LHS: Self = Self {
        lhs: true,
        rhs: false,
    };
    pub(super) const RHS: Self = Self {
        lhs: false,
        rhs: true,
    };
}

/// The scope an argument of a term is evaluated in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Scope {
    /// The scope of the term itself: every child of a term other than a local function, and the
    /// argument `E` of a local function.
    Enclosing,
    /// The local function's own scope, whose pattern binds its variables in its body only.
    Lambda,
}

/// The children of `term` with their positions, for walks that do not track scopes.
pub(super) fn positioned_children(
    term: &Term,
    position: TermPosition,
) -> Vec<(&Term, TermPosition)> {
    scoped_children(term, position)
        .into_iter()
        .map(|(child, position, _)| (child, position))
        .collect()
}

/// The children of `term` in argument order, each with its position and its scope (module docs).
pub(super) fn scoped_children<'t>(
    term: &'t Term,
    position: TermPosition,
) -> Vec<(&'t Term, TermPosition, Scope)> {
    let enclosing = |child: &'t Term| (child, position, Scope::Enclosing);
    match term.unannotated() {
        Term::Rewrite { left, right } => vec![
            (
                left,
                TermPosition {
                    lhs: position.lhs,
                    rhs: false,
                },
                Scope::Enclosing,
            ),
            (right, TermPosition::RHS, Scope::Enclosing),
        ],
        Term::As { pattern, alias } => vec![enclosing(pattern), enclosing(alias)],
        Term::Sequence(items) => items.iter().map(enclosing).collect(),
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Fun2) && arguments.len() >= 2 =>
        {
            let mut children = vec![(&arguments[0], TermPosition::BODY, Scope::Lambda)];
            children.extend(arguments[1..].iter().map(enclosing));
            children
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Fun3) && arguments.len() >= 3 =>
        {
            let mut children = vec![
                (&arguments[0], TermPosition::LHS, Scope::Lambda),
                (&arguments[1], TermPosition::RHS, Scope::Lambda),
            ];
            children.extend(arguments[2..].iter().map(enclosing));
            children
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Let) && arguments.len() >= 3 =>
        {
            let mut children = vec![
                (&arguments[0], TermPosition::LHS, Scope::Lambda),
                enclosing(&arguments[1]),
                (&arguments[2], TermPosition::RHS, Scope::Lambda),
            ];
            children.extend(arguments[3..].iter().map(enclosing));
            children
        }
        Term::Apply { arguments, .. } => arguments.iter().map(enclosing).collect(),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Vec::new(),
        Term::Annotated { .. } => unreachable!(),
    }
}
