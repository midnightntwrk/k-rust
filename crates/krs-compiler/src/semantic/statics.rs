//! Static rewriting modes: alias and desugar clauses (KF-028).
//!
//! A production marked `#[k::alias]` or `#[k::desugar]` (K's `alias` or
//! `macro`, `-rec` when `recursive`) is expanded before anything runs by the
//! clauses written for it. A clause takes its production's mode: an
//! `#[k::alias]` clause expands an alias production and a `#[k::desugar]`
//! clause a desugar production. An alias or desugar production that no clause
//! expands is reported, because nothing would ever replace it.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{ApplicationRef, NodeOrigin, ProductionAttribute, SentenceKind, StableItemId};
use krs_ir_levels::{IrTermKind, SemanticModule};

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
        let Some(head) = head else {
            return Err(invalid(
                format!(
                    "{} clause `{name}` must have a production marked `{}` at the head of its pattern",
                    clause.clause(),
                    clause.attribute(),
                ),
                rule.origin(),
            ));
        };
        match modes.get(head) {
            Some((mode, _)) if *mode == clause => {
                expanded.insert(head);
            }
            Some((mode, _)) => {
                return Err(invalid(
                    format!(
                        "{} clause `{name}` expands `{}`, which is marked `{}`: a clause takes its production's mode, so write `{}` on the clause, or `{}` on the production",
                        clause.clause(),
                        production_display_name(head),
                        mode.attribute(),
                        mode.attribute(),
                        clause.attribute(),
                    ),
                    rule.origin(),
                ));
            }
            None => {
                return Err(invalid(
                    format!(
                        "{} clause `{name}` expands `{}`, which is not marked `{}`; mark the production `{}` or `{}`",
                        clause.clause(),
                        production_display_name(head),
                        clause.attribute(),
                        clause.attribute(),
                        clause.recursive_attribute(),
                    ),
                    rule.origin(),
                ));
            }
        }
    }
    for (production, (mode, origin)) in &modes {
        if !expanded.contains(production) {
            return Err(invalid(
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

fn invalid(reason: String, origin: &NodeOrigin) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidStaticClause {
        reason,
        range: origin.origin().exact_authored_range().map(Box::new),
    }
}
