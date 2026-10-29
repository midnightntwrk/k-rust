//! Static rewriting modes: alias and desugar clauses (KF-028).
//!
//! A production marked `#[k::alias]` or `#[k::desugar]` (K's `alias` or
//! `macro`, `-rec` when `recursive`) is expanded before anything runs by the
//! clauses written for it. A clause takes its production's mode: an
//! `#[k::alias]` clause expands an alias production and a `#[k::desugar]`
//! clause a desugar production. An alias or desugar production that no clause
//! expands is reported, because nothing would ever replace it.
//!
//! An alias clause also runs backwards: when a result is printed, each term its result matches
//! prints as its subject, built from what the match bound. So below its root the subject holds
//! nothing printing cannot build (`reversible_subject`); the constructs the expander's walker
//! refuses by their spelling are refused there.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{ApplicationRef, NodeOrigin, ProductionAttribute, SentenceKind, StableItemId};
use krs_ir_levels::{IrTermKind, MapOperands, SemanticModule, SemanticTerm, SetOperands};

use super::error::DescriptorLoweringError;
use crate::partition::production_display_name;

/// The static mode of a production marker, with its attribute origin.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Mode {
    Alias,
    Desugar,
}

impl Mode {
    const fn attribute(self) -> &'static str {
        match self {
            Self::Alias => "#[k::alias]",
            Self::Desugar => "#[k::desugar]",
        }
    }

    const fn recursive_attribute(self) -> &'static str {
        match self {
            Self::Alias => "#[k::alias(recursive)]",
            Self::Desugar => "#[k::desugar(recursive)]",
        }
    }

    const fn clause(self) -> &'static str {
        match self {
            Self::Alias => "alias",
            Self::Desugar => "desugar",
        }
    }
}

/// Checks every alias and desugar clause against its head production, and
/// every alias and desugar production for a clause, in stable module order.
pub(super) fn check_static_clauses(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    let mut modes = BTreeMap::<&StableItemId, (Mode, &NodeOrigin)>::new();
    for production in modules.iter().flat_map(SemanticModule::productions) {
        for attribute in production.attributes() {
            let mode = match attribute {
                ProductionAttribute::Alias { .. } => Mode::Alias,
                ProductionAttribute::Desugar { .. } => Mode::Desugar,
                _ => continue,
            };
            modes.insert(production.id(), (mode, attribute.origin()));
        }
    }
    let mut expanded = BTreeSet::<&StableItemId>::new();
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        let clause = match rule.kind() {
            SentenceKind::Alias => Mode::Alias,
            SentenceKind::Desugar => Mode::Desugar,
            _ => continue,
        };
        let head = rule.body().and_then(|body| match body.from().kind() {
            IrTermKind::Application {
                application: ApplicationRef::Declared(production),
                ..
            } => Some(production),
            _ => None,
        });
        let name = rule.id().item_name();
        // The clause's root is the production it expands, so a root that is none is the root's
        // mistake: it is reported there, or at the clause when the root has no range of its own.
        let at = rule
            .body()
            .map(|body| body.from().origin())
            .filter(|origin| origin.origin().exact_authored_range().is_some())
            .unwrap_or_else(|| rule.origin());
        let Some(head) = head else {
            return Err(invalid(
                rule.id(),
                format!(
                    "{} clause `{name}` must have a production marked `{}` at the head of its pattern",
                    clause.clause(),
                    clause.attribute(),
                ),
                at,
            ));
        };
        match modes.get(head) {
            Some((mode, _)) if *mode == clause => {
                expanded.insert(head);
                if clause == Mode::Alias
                    && let Some(body) = rule.body()
                {
                    reversible_subject(rule.id(), body.from(), &modes)?;
                }
            }
            Some((mode, _)) => {
                return Err(invalid(
                    rule.id(),
                    format!(
                        "{} clause `{name}` expands `{}`, which is marked `{}`: a clause takes its production's mode, so write `{}` on the clause, or `{}` on the production",
                        clause.clause(),
                        production_display_name(head),
                        mode.attribute(),
                        mode.attribute(),
                        clause.attribute(),
                    ),
                    at,
                ));
            }
            None => {
                return Err(invalid(
                    rule.id(),
                    format!(
                        "{} clause `{name}` expands `{}`, which is not marked `{}`; mark the production `{}` or `{}`",
                        clause.clause(),
                        production_display_name(head),
                        clause.attribute(),
                        clause.attribute(),
                        clause.recursive_attribute(),
                    ),
                    at,
                ));
            }
        }
    }
    for (production, (mode, origin)) in &modes {
        if !expanded.contains(production) {
            return Err(invalid(
                production,
                format!(
                    "`{}` is marked `{}` but no `{}` clause expands it, so nothing expands it; add a `{} fn` whose pattern is headed by `{}`",
                    production_display_name(production),
                    mode.attribute(),
                    mode.attribute(),
                    mode.attribute(),
                    production_display_name(production),
                ),
                origin,
            ));
        }
    }
    Ok(())
}

/// What an alias clause's subject holds below its root must be built from what the clause's
/// result matched in a printed term (the module documentation), so it refuses, at the term, in
/// preorder:
/// - a set's concatenation `set::concat(a, b)` (K's `A B`), and a map's of more than one entry:
///   forward the clause matches only a term whose parts are disjoint, a test of the term; the
///   printed alias writes the parts the match bound, which may overlap, and a concatenation of
///   overlapping parts denotes no set or map. A list's concatenation is defined for any two lists,
///   and a single element or entry and the empty collection are no concatenation;
/// - an application of an alias or desugar production: forward expansion replaces it before the
///   clause can apply, so the clause never applies, and printing writes it unexpanded.
fn reversible_subject(
    clause: &StableItemId,
    root: &SemanticTerm,
    modes: &BTreeMap<&StableItemId, (Mode, &NodeOrigin)>,
) -> Result<(), DescriptorLoweringError> {
    let name = clause.item_name();
    let mut pending = root.children();
    pending.reverse();
    while let Some(term) = pending.pop() {
        let refusal = match term.kind() {
            IrTermKind::Set(operands) if matches!(**operands, SetOperands::Concat { .. }) => {
                Some(format!(
                    "alias clause `{name}`: a set's concatenation matches only a set whose parts are disjoint, a test the backward reading cannot make: when a result is printed, each term the clause's result matches prints as its subject, built from what the match bound, and parts that overlap print as a concatenation that denotes no set (`SetItem ( 1 ) SetItem ( 1 )`); write `#[k::desugar]` for an expansion that runs one way"
                ))
            }
            IrTermKind::Map(operands) if matches!(&**operands, MapOperands::Items(entries) if entries.len() > 1) => {
                Some(format!(
                    "alias clause `{name}`: a map's concatenation of entries matches only a map whose keys are distinct, a test the backward reading cannot make: when a result is printed, each term the clause's result matches prints as its subject, built from what the match bound, and keys that coincide print as a concatenation that denotes no map; write `#[k::desugar]` for an expansion that runs one way"
                ))
            }
            IrTermKind::Application {
                application: ApplicationRef::Declared(production),
                ..
            } if modes.contains_key(production) => {
                let (mode, _) = modes[production];
                Some(format!(
                    "alias clause `{name}`: `{}` is marked `{}`, so forward its application is expanded before this clause is tried, and the clause never applies; backward, the term its result matches would print with `{}` unexpanded, as no term the clause expands to: write the term `{}` expands to instead, or `#[k::desugar]` for an expansion that runs one way",
                    production_display_name(production),
                    mode.attribute(),
                    production_display_name(production),
                    production_display_name(production),
                ))
            }
            _ => None,
        };
        if let Some(reason) = refusal {
            return Err(DescriptorLoweringError::IrreversibleAlias {
                reason,
                range: term.origin().origin().exact_authored_range().map(Box::new),
                item: Some(Box::new(clause.clone())),
            });
        }
        let mut children = term.children();
        children.reverse();
        pending.extend(children);
    }
    Ok(())
}

fn invalid(item: &StableItemId, reason: String, origin: &NodeOrigin) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidStaticClause {
        reason,
        range: origin.origin().exact_authored_range().map(Box::new),
        item: Some(Box::new(item.clone())),
    }
}
