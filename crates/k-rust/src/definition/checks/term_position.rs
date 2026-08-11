//! Shared traversal rules for K's LHS/RHS-sensitive terms.

use crate::kast::Term;

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

pub(super) fn positioned_children(
    term: &Term,
    position: TermPosition,
) -> Vec<(&Term, TermPosition)> {
    match term.unannotated() {
        Term::Rewrite { left, right } => vec![
            (
                left,
                TermPosition {
                    lhs: position.lhs,
                    rhs: false,
                },
            ),
            (right, TermPosition::RHS),
        ],
        Term::As { pattern, alias } => vec![(pattern, position), (alias, position)],
        Term::Sequence(items) => items.iter().map(|item| (item, position)).collect(),
        Term::Apply { label, arguments } if label.name == "#fun2" && arguments.len() >= 2 => {
            let mut children = vec![
                (&arguments[0], TermPosition::BODY),
                (&arguments[1], position),
            ];
            children.extend(arguments[2..].iter().map(|argument| (argument, position)));
            children
        }
        Term::Apply { label, arguments }
            if matches!(label.name.as_str(), "#fun3" | "#let") && arguments.len() >= 3 =>
        {
            let mut children = vec![
                (&arguments[0], TermPosition::LHS),
                (&arguments[1], TermPosition::RHS),
                (&arguments[2], position),
            ];
            children.extend(arguments[3..].iter().map(|argument| (argument, position)));
            children
        }
        Term::Apply { arguments, .. } => arguments
            .iter()
            .map(|argument| (argument, position))
            .collect(),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Vec::new(),
        Term::Annotated { .. } => unreachable!(),
    }
}
