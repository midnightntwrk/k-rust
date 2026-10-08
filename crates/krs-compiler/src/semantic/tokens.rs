//! Whole-theory checks of token sorts (KF-003).
//!
//! A `#[k::token]` struct declares a closed sort whose values are its
//! tokens; a `#[k::token]` type alias adds token productions to a user sort
//! or to the builtin `Id`. K's Haskell backend rejects a constructor on a
//! sort that has domain values, so a sort with token productions has no
//! constructor productions, and one sort never declares the same token twice.

use std::collections::BTreeMap;

use krs_ir::{BuiltinSort, GrammarProductionItemKind, ProductionAttribute};
use krs_ir_levels::{SemanticModule, SemanticProduction, SemanticSortRef};

use super::error::DescriptorLoweringError;
use super::overload::sort_name;
use crate::partition::production_display_name;

/// Checks every token production and every constructor of a token sort, in
/// stable production order.
pub(super) fn check_token_sorts(modules: &[SemanticModule]) -> Result<(), DescriptorLoweringError> {
    let productions = modules
        .iter()
        .flat_map(SemanticModule::productions)
        .collect::<Vec<_>>();
    let mut tokens = BTreeMap::<(&SemanticSortRef, bool, &str), &SemanticProduction>::new();
    for production in productions
        .iter()
        .copied()
        .filter(|production| is_token(production))
    {
        let sort = production.result_sort();
        if let SemanticSortRef::Builtin(builtin) = sort
            && *builtin != BuiltinSort::Id
        {
            return Err(fail(
                production,
                format!(
                    "a `#[k::token]` type alias adds token productions to a user sort or to builtin `Id`; `{}` has its own domain values, written as literals",
                    builtin.k_name()
                ),
            ));
        }
        let Some((terminal, text)) = content(production) else {
            continue;
        };
        if tokens.insert((sort, terminal, text), production).is_some() {
            let kind = if terminal { "terminal" } else { "regex" };
            return Err(fail(
                production,
                format!(
                    "the token {kind} {text:?} is declared twice on sort `{}`; each token production of a sort is declared once",
                    sort_name(sort)
                ),
            ));
        }
    }
    for production in productions {
        let sort = production.result_sort();
        if !is_token(production)
            && !has(production, |attribute| {
                matches!(
                    attribute,
                    ProductionAttribute::Function { .. } | ProductionAttribute::Bracket { .. }
                )
            })
            && matches!(sort, SemanticSortRef::Declared(_))
            && tokens.keys().any(|(token_sort, _, _)| *token_sort == sort)
        {
            return Err(fail(
                production,
                format!(
                    "`{}` is a constructor of `{}`, a token sort: a sort with domain values has no constructors; give the constructor another sort, or use a function",
                    production_display_name(production.id()),
                    sort_name(sort)
                ),
            ));
        }
    }
    Ok(())
}

fn fail(production: &SemanticProduction, reason: String) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidTokenSort {
        item: Box::new(production.id().clone()),
        reason,
        range: production
            .origin()
            .origin()
            .exact_authored_range()
            .map(Box::new),
    }
}

fn has(
    production: &SemanticProduction,
    predicate: impl Fn(&ProductionAttribute<SemanticSortRef, krs_ir::StableItemId>) -> bool,
) -> bool {
    production.attributes().iter().any(predicate)
}

fn is_token(production: &SemanticProduction) -> bool {
    has(production, |attribute| {
        matches!(attribute, ProductionAttribute::Token { .. })
    })
}

/// Whether the token is a terminal, and its text.
fn content(production: &SemanticProduction) -> Option<(bool, &str)> {
    match production.items() {
        [item] => match item.kind() {
            GrammarProductionItemKind::Terminal { text } => Some((true, text)),
            GrammarProductionItemKind::RegexTerminal { regex, .. } => Some((false, regex)),
            GrammarProductionItemKind::NonTerminal { .. } => None,
        },
        _ => None,
    }
}
