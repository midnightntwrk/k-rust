//! Whole-theory checks of fresh values (KF-022).
//!
//! A `#[k::fresh(l: Loc)]` binder is K's `!L:Loc`: the step fills it by
//! calling the sort's `freshGenerator` function on the next value of the
//! shared `<generatedCounter>`. K declares the generators of Int and Id
//! (`freshInt`, `freshId`); every other sort needs exactly one total
//! `#[k::function(fresh_generator, ..)]` of one Int argument that returns the
//! sort.

use std::collections::BTreeMap;

use krs_ir::{BuiltinSort, GrammarProductionItemKind, ProductionAttribute, SourceRange};
use krs_ir_levels::{SemanticModule, SemanticProduction, SemanticSortRef};

use super::error::{DescriptorLoweringError, FreshProblem};
use super::overload::sort_name;
use crate::partition::production_display_name;

/// Checks every `fresh_generator` function, then every fresh binder's sort.
pub(super) fn check_fresh_generators(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    let mut generators = BTreeMap::<&SemanticSortRef, &SemanticProduction>::new();
    for production in modules.iter().flat_map(SemanticModule::productions) {
        if !is_generator(production) {
            continue;
        }
        let range = generator_range(production);
        let name = production_display_name(production.id());
        let sort = production.result_sort();
        if !production
            .attributes()
            .iter()
            .any(|attribute| matches!(attribute, ProductionAttribute::Total { .. }))
        {
            return Err(fail(
                FreshProblem::InvalidGenerator,
                format!(
                    "`{name}` is a `fresh_generator`, so it must be `total`: K calls it on every counter value"
                ),
                range,
            ));
        }
        let arguments = production
            .items()
            .iter()
            .filter_map(|item| match item.kind() {
                GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort),
                GrammarProductionItemKind::Terminal { .. }
                | GrammarProductionItemKind::RegexTerminal { .. } => None,
            })
            .collect::<Vec<_>>();
        if !matches!(
            arguments.as_slice(),
            [SemanticSortRef::Builtin(BuiltinSort::Int)]
        ) {
            return Err(fail(
                FreshProblem::InvalidGenerator,
                format!(
                    "`{name}` is a `fresh_generator`, so it takes exactly one Int field: the counter value K passes it"
                ),
                range,
            ));
        }
        if let SemanticSortRef::Builtin(builtin) = sort {
            let problem = if matches!(builtin, BuiltinSort::Int | BuiltinSort::Id) {
                FreshProblem::DuplicateGenerator
            } else {
                FreshProblem::InvalidGenerator
            };
            return Err(fail(
                problem,
                format!(
                    "`{name}` is a `fresh_generator` of builtin `{}`; a generator returns a sort of this definition (K's own freshInt and freshId generate Int and Id)",
                    builtin.k_name()
                ),
                range,
            ));
        }
        if let Some(previous) = generators.insert(sort, production) {
            return Err(fail(
                FreshProblem::DuplicateGenerator,
                format!(
                    "sort `{}` has two `fresh_generator` functions, `{}` and `{name}`; K draws its fresh values from exactly one",
                    sort_name(sort),
                    production_display_name(previous.id())
                ),
                range,
            ));
        }
    }
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        for binder in rule.fresh() {
            let sort = binder.sort();
            if matches!(
                sort,
                SemanticSortRef::Builtin(BuiltinSort::Int | BuiltinSort::Id)
            ) || generators.contains_key(sort)
            {
                continue;
            }
            return Err(fail(
                FreshProblem::NoGenerator,
                format!(
                    "fresh binder `{}` has sort `{}`, which has no generator; declare `#[k::function(total, fresh_generator, sort = {}, syntax = \"..\")]` with one Int field (Int and Id have K's own)",
                    binder.id().as_str(),
                    sort_name(sort),
                    sort_name(sort)
                ),
                binder.sort_origin().origin().exact_authored_range(),
            ));
        }
    }
    Ok(())
}

fn is_generator(production: &SemanticProduction) -> bool {
    production
        .attributes()
        .iter()
        .any(|attribute| matches!(attribute, ProductionAttribute::FreshGenerator { .. }))
}

/// The authored range of a generator's `fresh_generator` flag, or of the production.
fn generator_range(production: &SemanticProduction) -> Option<SourceRange> {
    production
        .attributes()
        .iter()
        .find(|attribute| matches!(attribute, ProductionAttribute::FreshGenerator { .. }))
        .and_then(|attribute| attribute.origin().origin().exact_authored_range())
        .or_else(|| production.origin().origin().exact_authored_range())
}

fn fail(
    problem: FreshProblem,
    reason: String,
    range: Option<SourceRange>,
) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidFresh {
        problem,
        reason,
        range: range.map(Box::new),
    }
}
