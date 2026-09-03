//! Sort and user-list checks performed while K constructs outer modules.

use super::super::{
    ProductionItem, ResolvedDefinition, ResolvedModule, Sentence, SortCatalog, SortHead,
};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::Sort;

const MINT_SORT: &str = "MInt";
const USER_LIST_ATTRIBUTE: &str = "userList";

/// Java `Module.checkSorts` (`outer.scala:486-516`).
pub fn check_sorts(module: &ResolvedModule, sorts: &SortCatalog<'_>) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    for sentence in &module.local_sentences {
        match sentence {
            Sentence::SyntaxSort { sort, .. } => {
                check_parametric_sort(sort, sentence, &mut diagnostics);
            }
            Sentence::SortSynonym { new_sort, .. } => {
                check_parametric_sort(new_sort, sentence, &mut diagnostics);
            }
            Sentence::Production {
                parameters,
                sort,
                items,
                ..
            } => {
                check_parametric_sort(sort, sentence, &mut diagnostics);

                let missing = items
                    .iter()
                    .filter_map(|item| {
                        let ProductionItem::NonTerminal { sort, .. } = item else {
                            return None;
                        };
                        let head = SortHead::from(sort);
                        let missing_head = !parameters.contains(sort)
                            && !sorts.defined_heads().contains(&head)
                            && !sorts.synonym_map().contains_key(sort);
                        let missing_instantiation = !sort.parameters.is_empty()
                            && sort
                                .parameters
                                .iter()
                                .all(|parameter| !parameters.contains(parameter))
                            && !sorts
                                .instantiations()
                                .get(&head)
                                .is_some_and(|instances| instances.contains(sort));
                        (missing_head || missing_instantiation).then_some(sort)
                    })
                    .collect::<Vec<_>>();

                if !missing.is_empty() {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::UndefinedSort,
                        format!(
                            "Could not find sorts: [{}]",
                            missing
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                        sentence,
                    ));
                }
            }
            _ => {}
        }
    }

    diagnostics
}

fn check_parametric_sort(sort: &Sort, sentence: &Sentence, diagnostics: &mut Vec<Diagnostic>) {
    if !sort.parameters.is_empty() && sort.name != MINT_SORT {
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::UnsupportedParametricSort,
            format!("User-defined parametric sorts are currently unsupported: {sort}"),
            sentence,
        ));
    }
}

/// Java `Module.checkUserLists` (`outer.scala:518-534`).
pub fn check_user_lists(module: &ResolvedModule, visible: &[&Sentence]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    // Start with local declarations so an imported declaration retained by sentence deduplication can still be compared with its equivalent local declaration.
    // Also inspect non-local visible declarations to reject conflicts between sibling imports before rule grammar construction.
    let candidates = module
        .local_sentences
        .iter()
        .chain(visible.iter().copied().filter(|candidate| {
            !module
                .local_sentences
                .iter()
                .any(|local| std::ptr::eq(local, *candidate))
        }));
    for sentence in candidates {
        let Sentence::Production {
            sort, attributes, ..
        } = sentence
        else {
            continue;
        };
        if attributes.get(USER_LIST_ATTRIBUTE).is_none() {
            continue;
        }

        let own_origin = (attributes.source(), attributes.location());
        let previous = visible.iter().copied().find(|candidate| {
            let Sentence::Production {
                sort: candidate_sort,
                attributes: candidate_attributes,
                ..
            } = candidate
            else {
                return false;
            };
            candidate_sort == sort
                && candidate_attributes.get(USER_LIST_ATTRIBUTE).is_some()
                && (
                    candidate_attributes.source(),
                    candidate_attributes.location(),
                ) != own_origin
        });
        let Some(previous) = previous else {
            continue;
        };
        let (Some(source), Some(location)) = (
            previous.attributes().source(),
            previous.attributes().location(),
        ) else {
            continue;
        };
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::DuplicateUserList,
            format!(
                "Sort {sort} previously declared as a user list at Source({source}) and Location({},{},{},{})",
                location.start_line,
                location.start_column,
                location.end_line,
                location.end_column
            ),
            sentence,
        ));
    }

    diagnostics
}

/// Run both outer-module checks over every module in dependency order.
pub fn check_outer_modules(definition: &ResolvedDefinition) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for (module_id, module) in definition.modules() {
        let visible = definition.sentences(module_id);
        let sorts = definition.sort_catalog(module_id);
        diagnostics.extend(check_sorts(module, &sorts));
        diagnostics.extend(check_user_lists(module, &visible));
    }
    diagnostics
}
