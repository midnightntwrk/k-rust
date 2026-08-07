//! Priority and associativity filtering over production-bearing parse trees.

use std::collections::BTreeSet;

use super::{Grammar, Item, ParseError, ParsedTerm, Production, lower_term};
use crate::kast::Term;

impl Grammar {
    pub(super) fn priority_violation(&self, term: &ParsedTerm) -> Option<ParseError> {
        let ParsedTerm::Production {
            production,
            children,
        } = term
        else {
            return None;
        };
        let parent = &self.productions[*production];
        if parent.syntactic_subsort {
            return children
                .iter()
                .find_map(|child| self.priority_violation(child));
        }

        let checked = parent.apply_priority.clone().unwrap_or_else(|| {
            let mut positions = BTreeSet::new();
            if matches!(parent.items.first(), Some(Item::NonTerminal(_))) {
                positions.insert(1);
            }
            if matches!(parent.items.last(), Some(Item::NonTerminal(_))) {
                positions.insert(children.len());
            }
            positions
        });
        for position in checked {
            let Some(child) = children.get(position.saturating_sub(1)) else {
                continue;
            };
            let side =
                if position == 1 && matches!(parent.items.first(), Some(Item::NonTerminal(_))) {
                    Side::Left
                } else if position == children.len()
                    && matches!(parent.items.last(), Some(Item::NonTerminal(_)))
                {
                    Side::Right
                } else {
                    Side::Middle
                };
            if let Some(error) = self.child_violation(parent, child, side) {
                return Some(error);
            }
        }
        children
            .iter()
            .find_map(|child| self.priority_violation(child))
    }

    fn child_violation(
        &self,
        parent: &Production,
        child: &ParsedTerm,
        side: Side,
    ) -> Option<ParseError> {
        let ParsedTerm::Production {
            production: child, ..
        } = child
        else {
            return None;
        };
        let child = &self.productions[*child];
        if child.syntactic_subsort {
            return None;
        }
        let (Some(parent_label), Some(child_label)) = (&parent.parse_label, &child.parse_label)
        else {
            return None;
        };
        if self.priorities.less_than(parent_label, child_label) {
            return Some(ParseError::Priority {
                parent: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if side == Side::Right
            && self
                .associativities
                .left
                .contains(&(parent_label.clone(), child_label.clone()))
        {
            return Some(ParseError::Associativity {
                parent: parent_label.clone(),
                child: child_label.clone(),
                side: "right",
            });
        }
        if side == Side::Left
            && self
                .associativities
                .right
                .contains(&(parent_label.clone(), child_label.clone()))
        {
            return Some(ParseError::Associativity {
                parent: parent_label.clone(),
                child: child_label.clone(),
                side: "left",
            });
        }
        None
    }

    pub(super) fn lower(&self, term: ParsedTerm) -> Term {
        match term {
            ParsedTerm::Term(term) => term,
            ParsedTerm::Production {
                production,
                children,
            } => {
                let production = &self.productions[production];
                let children = children
                    .into_iter()
                    .map(|child| self.lower(child))
                    .collect::<Vec<_>>();
                lower_term(production, &children)
            }
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Side {
    Left,
    Right,
    Middle,
}

pub(super) fn parse_apply_priority(source: &str) -> Result<BTreeSet<usize>, ParseError> {
    source
        .split(|character: char| character == ',' || character.is_ascii_whitespace())
        .filter(|piece| !piece.is_empty())
        .map(|piece| {
            piece
                .parse::<usize>()
                .map_err(|_| ParseError::InvalidApplyPriority {
                    value: source.to_owned(),
                    position: piece.to_owned(),
                })
        })
        .collect()
}
