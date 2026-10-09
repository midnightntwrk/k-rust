//! Whole-theory checks of `overload` families (KF-038).
//!
//! K relates two productions with `overload(key)` when they share the key;
//! KRS writes the key as the target production. A member must specialise its
//! target: same arity, and a result sort and argument sorts that are each a
//! subsort of the target's, with at least one strict (K's `user_manual.md`,
//! "overload"). Targets chain to one root, which supplies the family key.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{GrammarProductionItemKind, ProductionAttribute, StableItemId};
use krs_ir_levels::{SemanticModule, SemanticProduction, SemanticSortRef};

use super::catalog::semantic_is_subsort;
use super::error::DescriptorLoweringError;
use crate::partition::production_display_name;

/// Checks every `overload` key of the theory, in stable member order.
pub(super) fn check_overloads(
    modules: &[SemanticModule],
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<(), DescriptorLoweringError> {
    let productions = modules
        .iter()
        .flat_map(SemanticModule::productions)
        .map(|production| (production.id(), production))
        .collect::<BTreeMap<_, _>>();
    let targets = productions
        .values()
        .filter_map(|production| overload(production).map(|edge| (production.id(), edge)))
        .collect::<BTreeMap<_, _>>();
    for (member, (origin, target)) in &targets {
        let fail = |reason: String| DescriptorLoweringError::InvalidOverload {
            production: Box::new((*member).clone()),
            reason,
            range: origin.origin().exact_authored_range().map(Box::new),
        };
        let member_name = production_display_name(member);
        let target_name = production_display_name(target);
        let mut chain = vec![*member];
        let mut current = Some(*target);
        while let Some(next) = current {
            if chain.contains(&next) {
                chain.push(next);
                return Err(fail(format!(
                    "the overload targets form a cycle: {}",
                    chain
                        .iter()
                        .map(|id| format!("`{}`", production_display_name(id)))
                        .collect::<Vec<_>>()
                        .join(" -> ")
                )));
            }
            chain.push(next);
            current = targets.get(next).map(|(_, target)| *target);
        }
        let Some(target_production) = productions.get(target) else {
            return Err(fail(format!(
                "the target `{target_name}` of `{member_name}` is not a production of this definition"
            )));
        };
        if is_function(target_production) {
            return Err(fail(format!(
                "the target `{target_name}` of `{member_name}` is a function; `overload` relates constructor productions"
            )));
        }
        let member_production = productions[member];
        let member_arguments = arguments(member_production);
        let target_arguments = arguments(target_production);
        if member_arguments.len() != target_arguments.len() {
            return Err(fail(format!(
                "`{member_name}` takes {} but its target `{target_name}` takes {}; an overload has the target's arity",
                arguments_text(member_arguments.len()),
                arguments_text(target_arguments.len())
            )));
        }
        let pairs = std::iter::once((
            member_production.result_sort(),
            target_production.result_sort(),
        ))
        .chain(member_arguments.into_iter().zip(target_arguments));
        let mut strict = false;
        for (specific, general) in pairs {
            if !semantic_is_subsort(specific, general, parents) {
                return Err(fail(format!(
                    "`{member_name}` does not specialise `{target_name}`: its sort `{}` is not a subsort of `{}`",
                    sort_name(specific),
                    sort_name(general)
                )));
            }
            strict |= specific != general;
        }
        if !strict {
            return Err(fail(format!(
                "`{member_name}` has the same result and argument sorts as `{target_name}`; an overload must make at least one sort strictly smaller"
            )));
        }
    }
    Ok(())
}

fn overload(production: &SemanticProduction) -> Option<(&krs_ir::NodeOrigin, &StableItemId)> {
    production
        .attributes()
        .iter()
        .find_map(|attribute| match attribute {
            ProductionAttribute::Overload { origin, target } => Some((origin, target)),
            _ => None,
        })
}

fn is_function(production: &SemanticProduction) -> bool {
    production
        .attributes()
        .iter()
        .any(|attribute| matches!(attribute, ProductionAttribute::Function { .. }))
}

fn arguments(production: &SemanticProduction) -> Vec<&SemanticSortRef> {
    production
        .items()
        .iter()
        .filter_map(|item| match item.kind() {
            GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort),
            GrammarProductionItemKind::Terminal { .. }
            | GrammarProductionItemKind::RegexTerminal { .. } => None,
        })
        .collect()
}

fn arguments_text(count: usize) -> String {
    if count == 1 {
        "1 argument".to_owned()
    } else {
        format!("{count} arguments")
    }
}

pub(super) fn sort_name(sort: &SemanticSortRef) -> String {
    match sort {
        SemanticSortRef::Declared(id) => id.item_name().to_owned(),
        SemanticSortRef::Builtin(sort) => sort.k_name().to_owned(),
        SemanticSortRef::Cell(id) => format!("{}Cell", id.item_name()),
        SemanticSortRef::Parameter(name) => name.to_string(),
    }
}
