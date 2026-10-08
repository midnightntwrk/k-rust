//! Whole-theory checks of syntactic lists (KF-020).
//!
//! A `#[k::syntax_list]` enum declares a closed sort: its cons and terminator
//! variants are the sort's only constructors, as K's `List{Elem, "sep"}`
//! sentence is the whole definition of the list sort. Membership in open
//! sorts still goes through `k::sorts!` `impl` lines, which make the list a
//! subsort of another sort, never the reverse.

use std::collections::BTreeMap;

use krs_ir::{GrammarProductionItemKind, ProductionAttribute, StableItemId};
use krs_ir_levels::{SemanticModule, SemanticProduction, SemanticSortRef};

use super::error::DescriptorLoweringError;
use super::overload::sort_name;
use crate::partition::production_display_name;

/// Checks every syntactic list against the rest of the definition, in stable
/// module and production order.
pub(super) fn check_syntax_lists(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    let productions = modules
        .iter()
        .flat_map(SemanticModule::productions)
        .collect::<Vec<_>>();
    let lists = list_sorts(&productions)?;
    if lists.is_empty() {
        return Ok(());
    }
    check_closed(&productions, &lists)?;
    check_subsorts(modules, &lists)?;
    check_terminators(&productions)
}

/// Maps each list sort to its cons production, rejecting a list whose
/// elements have the list's own sort.
fn list_sorts<'a>(
    productions: &[&'a SemanticProduction],
) -> Result<BTreeMap<&'a StableItemId, &'a SemanticProduction>, DescriptorLoweringError> {
    let mut lists = BTreeMap::new();
    for production in productions.iter().copied() {
        if !is_cons(production) {
            continue;
        }
        let SemanticSortRef::Declared(sort) = production.result_sort() else {
            continue;
        };
        if let Some(head) = production.items().first()
            && let GrammarProductionItemKind::NonTerminal { sort: element, .. } = head.kind()
            && element == production.result_sort()
        {
            return Err(fail(
                production,
                format!(
                    "the elements of syntactic list `{}` have the list's own sort; K's `List{{{0}, ..}}` needs a different element sort",
                    sort.item_name()
                ),
            ));
        }
        lists.insert(sort, production);
    }
    Ok(lists)
}

/// Rejects every other constructor of a list sort.
fn check_closed(
    productions: &[&SemanticProduction],
    lists: &BTreeMap<&StableItemId, &SemanticProduction>,
) -> Result<(), DescriptorLoweringError> {
    for production in productions {
        let SemanticSortRef::Declared(sort) = production.result_sort() else {
            continue;
        };
        let Some(cons) = lists.get(sort) else {
            continue;
        };
        if is_cons(production)
            || is_terminator(production)
            || production.attributes().iter().any(|attribute| {
                matches!(
                    attribute,
                    ProductionAttribute::Function { .. } | ProductionAttribute::Bracket { .. }
                )
            })
        {
            continue;
        }
        return Err(fail(
            production,
            format!(
                "`{}` constructs `{}`, a syntactic list: a `#[k::syntax_list]` enum is the whole definition of its sort, so the list has no other constructors; give the constructor another sort, or use a function",
                production_display_name(production.id()),
                list_name(cons)
            ),
        ));
    }
    Ok(())
}

/// Rejects a subsort into a list sort.
fn check_subsorts(
    modules: &[SemanticModule],
    lists: &BTreeMap<&StableItemId, &SemanticProduction>,
) -> Result<(), DescriptorLoweringError> {
    for module in modules {
        for subsort in module.subsorts() {
            let SemanticSortRef::Declared(sort) = subsort.supersort() else {
                continue;
            };
            if let Some(cons) = lists.get(sort) {
                return Err(DescriptorLoweringError::InvalidSyntaxList {
                    item: Box::new(cons.id().clone()),
                    reason: format!(
                        "`{}` is declared a subsort of `{}`, a syntactic list: a list sort is closed, so no sort joins it",
                        sort_name(subsort.subsort()),
                        list_name(cons)
                    ),
                    range: subsort
                        .origin()
                        .origin()
                        .exact_authored_range()
                        .map(Box::new),
                });
            }
        }
    }
    Ok(())
}

/// K generates the terminator `.Sort` as a terminal of the definition, so no
/// other production may spell it.
fn check_terminators(productions: &[&SemanticProduction]) -> Result<(), DescriptorLoweringError> {
    let terminators = productions
        .iter()
        .filter(|production| is_terminator(production))
        .filter_map(|production| terminal(production).map(|text| (text, *production)))
        .collect::<BTreeMap<_, _>>();
    for production in productions {
        if is_terminator(production) {
            continue;
        }
        for item in production.items() {
            if let GrammarProductionItemKind::Terminal { text } = item.kind()
                && let Some(terminator) = terminators.get(text.as_str())
            {
                return Err(fail(
                    production,
                    format!(
                        "`{}` spells the terminal `{text}`, which K generates as the empty-list terminator of syntactic list `{}`; rename one of them",
                        production_display_name(production.id()),
                        sort_name(terminator.result_sort())
                    ),
                ));
            }
        }
    }
    Ok(())
}

fn list_name(cons: &SemanticProduction) -> String {
    sort_name(cons.result_sort())
}

fn fail(production: &SemanticProduction, reason: String) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidSyntaxList {
        item: Box::new(production.id().clone()),
        reason,
        range: production
            .origin()
            .origin()
            .exact_authored_range()
            .map(Box::new),
    }
}

fn is_cons(production: &SemanticProduction) -> bool {
    production
        .attributes()
        .iter()
        .any(|attribute| matches!(attribute, ProductionAttribute::ListCons { .. }))
}

fn is_terminator(production: &SemanticProduction) -> bool {
    production
        .attributes()
        .iter()
        .any(|attribute| matches!(attribute, ProductionAttribute::ListTerminator { .. }))
}

fn terminal(production: &SemanticProduction) -> Option<&str> {
    match production.items() {
        [item] => match item.kind() {
            GrammarProductionItemKind::Terminal { text } => Some(text),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use krs_ir::{
        ItemKind, ModuleId, NodeOrigin, PackageId, ProductionAttribute, ProductionFieldId,
        StableItemId, testing,
    };
    use krs_ir_levels::{
        SemanticModule, SemanticProduction, SemanticProductionItem, SemanticSort, SemanticSortRef,
        SemanticSubsort,
    };

    use super::check_syntax_lists;

    fn package() -> PackageId {
        testing::package("KRS-LISTS", "lists")
    }

    fn item(name: &str, kind: ItemKind) -> StableItemId {
        testing::item_in(package(), "lists", name, kind)
    }

    fn origin(key: &str) -> NodeOrigin {
        testing::origin_in(
            key,
            package(),
            "src/lib.rs",
            testing::digest_with("4".repeat(64)),
            0,
            1,
        )
    }

    fn ints() -> SemanticSortRef {
        SemanticSortRef::Declared(item("Ints", ItemKind::Sort))
    }

    /// `Ints` with elements of sort `element`.
    fn list(element: SemanticSortRef) -> Vec<SemanticProduction> {
        let cons = item("Cons", ItemKind::Constructor);
        let nil = item("Nil", ItemKind::Constructor);
        vec![
            SemanticProduction::new(
                origin("cons"),
                cons.clone(),
                ints(),
                vec![
                    SemanticProductionItem::non_terminal(
                        origin("head"),
                        ProductionFieldId::new("head").unwrap(),
                        element,
                    ),
                    SemanticProductionItem::terminal(origin("separator"), ",").unwrap(),
                    SemanticProductionItem::non_terminal(
                        origin("tail"),
                        ProductionFieldId::new("tail").unwrap(),
                        ints(),
                    ),
                ],
                vec![ProductionAttribute::ListCons {
                    origin: origin("list"),
                    separator: ",".to_owned(),
                    non_empty: false,
                    terminator: nil.clone(),
                }],
            )
            .unwrap(),
            SemanticProduction::new(
                origin("nil"),
                nil,
                ints(),
                vec![SemanticProductionItem::terminal(origin("terminator"), ".Ints").unwrap()],
                vec![ProductionAttribute::ListTerminator {
                    origin: origin("list-terminator"),
                    cons,
                }],
            )
            .unwrap(),
        ]
    }

    fn module(
        productions: Vec<SemanticProduction>,
        subsorts: Vec<SemanticSubsort>,
    ) -> SemanticModule {
        SemanticModule::new(
            origin("module"),
            ModuleId::new("KRS-LISTS").unwrap(),
            vec![],
            vec![
                SemanticSort::new(origin("ints"), item("Ints", ItemKind::Sort)),
                SemanticSort::new(origin("other"), item("Other", ItemKind::Sort)),
            ],
            subsorts,
            productions,
            vec![],
            vec![],
            None,
            vec![],
        )
    }

    fn error(modules: &[SemanticModule]) -> String {
        check_syntax_lists(modules).unwrap_err().to_string()
    }

    #[test]
    fn a_well_formed_list_passes() {
        check_syntax_lists(&[module(list(SemanticSortRef::int()), vec![])]).unwrap();
    }

    #[test]
    fn the_element_sort_differs_from_the_list() {
        assert!(error(&[module(list(ints()), vec![])]).contains("the list's own sort"));
    }

    #[test]
    fn no_sort_joins_a_list() {
        let subsort = SemanticSubsort::new(
            origin("subsort"),
            SemanticSortRef::Declared(item("Other", ItemKind::Sort)),
            ints(),
        );
        let message = error(&[module(list(SemanticSortRef::int()), vec![subsort])]);
        assert!(message.contains("a list sort is closed"), "{message}");
    }

    #[test]
    fn no_other_terminal_spells_the_terminator() {
        let mut productions = list(SemanticSortRef::int());
        productions.push(
            SemanticProduction::new(
                origin("stop"),
                item("Stop", ItemKind::Constructor),
                SemanticSortRef::Declared(item("Other", ItemKind::Sort)),
                vec![SemanticProductionItem::terminal(origin("stop.terminal"), ".Ints").unwrap()],
                vec![],
            )
            .unwrap(),
        );
        let message = error(&[module(productions, vec![])]);
        assert!(message.contains("empty-list terminator"), "{message}");
    }
}
