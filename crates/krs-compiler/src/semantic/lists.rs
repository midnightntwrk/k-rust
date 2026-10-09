//! Whole-theory checks of syntactic lists (KF-020).
//!
//! A `#[k::syntax_list]` enum declares a closed sort: its cons and terminator
//! variants are the sort's only constructors, as K's `List{Elem, "sep"}`
//! sentence is the whole definition of the list sort. Membership in open
//! sorts still goes through `k::sorts!` `impl` lines, which make the list a
//! subsort of another sort.
//!
//! One sort may join a list: the value list of a strict list (KF-020), K's
//! idiom `syntax Vals ::= List{Val, ","}`, `syntax Exps ::= Vals`,
//! `syntax KResult ::= Vals` for `syntax Exps ::= List{Exp, ","} [strict]`.
//! Lowering gives the two lists K's `overload` key, so an evaluated `Exps`
//! is a `Vals` and its strictness stops heating it.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{GrammarProductionItemKind, ProductionAttribute, StableItemId};
use krs_ir_levels::{SemanticModule, SemanticProduction, SemanticSortRef, SemanticSubsort};

use super::catalog::semantic_is_subsort;
use super::error::DescriptorLoweringError;
use super::overload::sort_name;
use crate::partition::production_display_name;

/// Checks every syntactic list against the rest of the definition, in stable
/// module and production order.
pub(super) fn check_syntax_lists(
    modules: &[SemanticModule],
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
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
    check_subsorts(modules, &lists, parents)?;
    check_terminators(&productions)
}

/// The `overload` edges of every value list, member first: the value list's
/// cons to the strict list's cons, and its terminator to the strict list's
/// terminator. K relates them through the strict list's overload key, which
/// both lists carry on both productions; the semantic pass has checked that
/// every subsort between two list sorts is a value list.
pub(crate) fn value_list_overloads(
    modules: &[SemanticModule],
) -> Vec<(StableItemId, StableItemId)> {
    let productions = modules
        .iter()
        .flat_map(SemanticModule::productions)
        .collect::<Vec<_>>();
    let mut lists = BTreeMap::new();
    for production in &productions {
        if let (SemanticSortRef::Declared(sort), Some(terminator)) =
            (production.result_sort(), cons_terminator(production))
        {
            lists.insert(sort, (production.id(), terminator));
        }
    }
    let mut edges = Vec::new();
    for subsort in modules.iter().flat_map(SemanticModule::subsorts) {
        if let (SemanticSortRef::Declared(member), SemanticSortRef::Declared(list)) =
            (subsort.subsort(), subsort.supersort())
            && let (Some((member_cons, member_nil)), Some((list_cons, list_nil))) =
                (lists.get(member), lists.get(list))
        {
            edges.push(((*member_cons).clone(), (*list_cons).clone()));
            edges.push(((*member_nil).clone(), (*list_nil).clone()));
        }
    }
    edges
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
        if let Some(element) = element(production)
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

/// Rejects a subsort into a list sort, except one value list per strict
/// list (KF-020): a non-strict syntactic list with the strict list's
/// separator and `non_empty` flag, whose elements are a subsort of the
/// strict list's elements, and which, with its elements, is a subsort of
/// the strict list's result sort.
fn check_subsorts(
    modules: &[SemanticModule],
    lists: &BTreeMap<&StableItemId, &SemanticProduction>,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<(), DescriptorLoweringError> {
    let mut value_lists = BTreeMap::<&StableItemId, &StableItemId>::new();
    let mut strict_lists = BTreeMap::<&StableItemId, &StableItemId>::new();
    for subsort in modules.iter().flat_map(SemanticModule::subsorts) {
        let SemanticSortRef::Declared(sort) = subsort.supersort() else {
            continue;
        };
        let Some(cons) = lists.get(sort) else {
            continue;
        };
        let reject = |reason: String| subsort_error(subsort, cons, reason);
        let member_name = sort_name(subsort.subsort());
        let list = list_name(cons);
        let member = match subsort.subsort() {
            SemanticSortRef::Declared(member) => {
                lists.get(member).map(|member_cons| (member, *member_cons))
            }
            _ => None,
        };
        let Some((member, member_cons)) = member else {
            return Err(reject(format!(
                "`{member_name}` is declared a subsort of `{list}`, a syntactic list: a list sort is closed, so no sort joins it except the value list of a strict list, itself a `#[k::syntax_list]`"
            )));
        };
        let Some(result) = strictness_result(cons) else {
            return Err(reject(format!(
                "`{member_name}` is declared a subsort of `{list}`, a syntactic list that is not strict: only a strict list admits a subsort, its value list"
            )));
        };
        if strictness_result(member_cons).is_some() {
            return Err(reject(format!(
                "`{member_name}`, the value list of `{list}`, is strict: a value list holds evaluated elements, so its cons variant takes no strictness attribute"
            )));
        }
        if list_shape(member_cons) != list_shape(cons) {
            return Err(reject(format!(
                "`{member_name}`, the value list of `{list}`, needs the separator and `non_empty` flag of `{list}`: K overloads the two lists, so they print alike"
            )));
        }
        let (Some(member_element), Some(list_element)) = (element(member_cons), element(cons))
        else {
            continue;
        };
        if !semantic_is_subsort(member_element, list_element, parents) {
            return Err(reject(format!(
                "the elements of `{member_name}`, the value list of `{list}`, have sort `{}`, which is not a subsort of `{}`, the elements of `{list}`",
                sort_name(member_element),
                sort_name(list_element)
            )));
        }
        for (sort, what) in [
            (subsort.subsort(), format!("`{member_name}`")),
            (
                member_element,
                format!("its elements' sort `{}`", sort_name(member_element)),
            ),
        ] {
            if !semantic_is_subsort(sort, result, parents) {
                return Err(reject(format!(
                    "`{member_name}` is the value list of `{list}`, but {what} is not a subsort of `{}`, the strictness result of `{list}`: declare it in `k::sorts!`, as in `impl {} for {member_name};`",
                    sort_name(result),
                    sort_name(result)
                )));
            }
        }
        if let Some(previous) = value_lists.insert(sort, member) {
            return Err(reject(format!(
                "`{list}` already has the value list `{}`; a strict list has one value list",
                previous.item_name()
            )));
        }
        if let Some(previous) = strict_lists.insert(member, sort) {
            return Err(reject(format!(
                "`{member_name}` is already the value list of `{}`; a value list serves one strict list",
                previous.item_name()
            )));
        }
    }
    Ok(())
}

fn subsort_error(
    subsort: &SemanticSubsort,
    cons: &SemanticProduction,
    reason: String,
) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidSyntaxList {
        item: Box::new(cons.id().clone()),
        reason,
        range: subsort
            .origin()
            .origin()
            .exact_authored_range()
            .map(Box::new),
    }
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

/// The element sort of a cons production: its first nonterminal.
fn element(cons: &SemanticProduction) -> Option<&SemanticSortRef> {
    cons.items().first().and_then(|head| match head.kind() {
        GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort),
        _ => None,
    })
}

/// The strictness result sort of a cons production, when it is strict.
fn strictness_result(cons: &SemanticProduction) -> Option<&SemanticSortRef> {
    cons.attributes()
        .iter()
        .find_map(|attribute| match attribute {
            ProductionAttribute::Strictness { result_sort, .. } => Some(result_sort.sort()),
            _ => None,
        })
}

/// The separator and `non_empty` flag of a cons production.
fn list_shape(cons: &SemanticProduction) -> Option<(&str, bool)> {
    cons.attributes()
        .iter()
        .find_map(|attribute| match attribute {
            ProductionAttribute::ListCons {
                separator,
                non_empty,
                ..
            } => Some((separator.as_str(), *non_empty)),
            _ => None,
        })
}

/// The terminator of a cons production.
fn cons_terminator(production: &SemanticProduction) -> Option<&StableItemId> {
    production
        .attributes()
        .iter()
        .find_map(|attribute| match attribute {
            ProductionAttribute::ListCons { terminator, .. } => Some(terminator),
            _ => None,
        })
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use krs_ir::{
        ItemKind, ModuleId, NodeOrigin, PackageId, ProductionAttribute, ProductionFieldId,
        ProductionFieldReference, ProductionResultSort, StableItemId, StrictnessKind, testing,
    };
    use krs_ir_levels::{
        SemanticModule, SemanticProduction, SemanticProductionItem, SemanticSort, SemanticSortRef,
        SemanticSubsort,
    };

    use super::{check_syntax_lists, value_list_overloads};

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

    /// The subsort graph of the modules' subsort edges.
    fn parents(modules: &[SemanticModule]) -> BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>> {
        let mut parents = BTreeMap::<_, BTreeSet<_>>::new();
        for subsort in modules.iter().flat_map(SemanticModule::subsorts) {
            parents
                .entry(subsort.subsort().clone())
                .or_default()
                .insert(subsort.supersort().clone());
        }
        parents
    }

    fn check(modules: &[SemanticModule]) -> Result<(), super::DescriptorLoweringError> {
        check_syntax_lists(modules, &parents(modules))
    }

    fn error(modules: &[SemanticModule]) -> String {
        check(modules).unwrap_err().to_string()
    }

    fn sort(name: &str) -> SemanticSortRef {
        SemanticSortRef::Declared(item(name, ItemKind::Sort))
    }

    fn subsort(sub: &str, sup: &str) -> SemanticSubsort {
        SemanticSubsort::new(origin(&format!("{sub}<{sup}")), sort(sub), sort(sup))
    }

    /// The list `name` of `element`, strict with result `strict` when given.
    fn named_list(
        name: &str,
        element: SemanticSortRef,
        separator: &str,
        strict: Option<&str>,
    ) -> Vec<SemanticProduction> {
        let cons = item(&format!("{name}Cons"), ItemKind::Constructor);
        let nil = item(&format!("{name}Nil"), ItemKind::Constructor);
        let mut attributes = vec![ProductionAttribute::ListCons {
            origin: origin(&format!("{name}.list")),
            separator: separator.to_owned(),
            non_empty: false,
            terminator: nil.clone(),
        }];
        if let Some(result) = strict {
            attributes.push(ProductionAttribute::Strictness {
                origin: origin(&format!("{name}.strict")),
                kind: StrictnessKind::SeqStrict,
                using: None,
                fields: ["head", "tail"]
                    .into_iter()
                    .map(|field| {
                        ProductionFieldReference::new(
                            origin(&format!("{name}.strict.{field}")),
                            ProductionFieldId::new(field).unwrap(),
                        )
                    })
                    .collect(),
                result_sort: ProductionResultSort::new(
                    origin(&format!("{name}.strict.result")),
                    sort(result),
                ),
            });
        }
        vec![
            SemanticProduction::new(
                origin(&format!("{name}.cons")),
                cons.clone(),
                sort(name),
                vec![
                    SemanticProductionItem::non_terminal(
                        origin(&format!("{name}.head")),
                        ProductionFieldId::new("head").unwrap(),
                        element,
                    ),
                    SemanticProductionItem::terminal(
                        origin(&format!("{name}.separator")),
                        separator,
                    )
                    .unwrap(),
                    SemanticProductionItem::non_terminal(
                        origin(&format!("{name}.tail")),
                        ProductionFieldId::new("tail").unwrap(),
                        sort(name),
                    ),
                ],
                attributes,
            )
            .unwrap(),
            SemanticProduction::new(
                origin(&format!("{name}.nil")),
                nil,
                sort(name),
                vec![
                    SemanticProductionItem::terminal(
                        origin(&format!("{name}.terminator")),
                        format!(".{name}"),
                    )
                    .unwrap(),
                ],
                vec![ProductionAttribute::ListTerminator {
                    origin: origin(&format!("{name}.list-terminator")),
                    cons,
                }],
            )
            .unwrap(),
        ]
    }

    /// K's `Vals` idiom: `Exps ::= List{Exp, ","} [seqstrict]` and its value
    /// list `Vals ::= List{Val, ","}`, with the given changes.
    fn value_list(
        exps_strict: Option<&str>,
        vals_strict: Option<&str>,
        vals_separator: &str,
        subsorts: &[(&str, &str)],
    ) -> SemanticModule {
        let mut productions = named_list("Exps", sort("Exp"), ",", exps_strict);
        productions.extend(named_list("Vals", sort("Val"), vals_separator, vals_strict));
        module(
            productions,
            subsorts
                .iter()
                .map(|(sub, sup)| subsort(sub, sup))
                .collect(),
        )
    }

    const IDIOM: &[(&str, &str)] = &[
        ("Val", "Exp"),
        ("Val", "KResult"),
        ("Vals", "Exps"),
        ("Vals", "KResult"),
    ];

    #[test]
    fn a_well_formed_list_passes() {
        check(&[module(list(SemanticSortRef::int()), vec![])]).unwrap();
    }

    #[test]
    fn a_value_list_joins_its_strict_list() {
        let modules = [value_list(Some("KResult"), None, ",", IDIOM)];
        check(&modules).unwrap();
        let name = |id: &StableItemId| id.item_name().to_owned();
        let edges = value_list_overloads(&modules)
            .iter()
            .map(|(member, target)| (name(member), name(target)))
            .collect::<Vec<_>>();
        assert_eq!(
            edges,
            [
                ("ValsCons".to_owned(), "ExpsCons".to_owned()),
                ("ValsNil".to_owned(), "ExpsNil".to_owned()),
            ]
        );
    }

    #[test]
    fn only_a_strict_list_has_a_value_list() {
        let message = error(&[value_list(None, None, ",", IDIOM)]);
        assert!(message.contains("that is not strict"), "{message}");
    }

    #[test]
    fn a_value_list_is_not_strict() {
        let message = error(&[value_list(Some("KResult"), Some("KResult"), ",", IDIOM)]);
        assert!(message.contains("is strict"), "{message}");
    }

    #[test]
    fn a_value_list_has_the_strict_list_separator() {
        let message = error(&[value_list(Some("KResult"), None, ";", IDIOM)]);
        assert!(message.contains("separator"), "{message}");
    }

    #[test]
    fn value_list_elements_specialise_the_strict_list_elements() {
        let message = error(&[value_list(
            Some("KResult"),
            None,
            ",",
            &[("Val", "KResult"), ("Vals", "Exps"), ("Vals", "KResult")],
        )]);
        assert!(message.contains("not a subsort of `Exp`"), "{message}");
    }

    #[test]
    fn a_value_list_is_a_strictness_result() {
        let message = error(&[value_list(
            Some("KResult"),
            None,
            ",",
            &[("Val", "Exp"), ("Val", "KResult"), ("Vals", "Exps")],
        )]);
        assert!(message.contains("impl KResult for Vals"), "{message}");
        let message = error(&[value_list(
            Some("KResult"),
            None,
            ",",
            &[("Val", "Exp"), ("Vals", "Exps"), ("Vals", "KResult")],
        )]);
        assert!(message.contains("its elements' sort `Val`"), "{message}");
    }

    #[test]
    fn a_strict_list_has_one_value_list() {
        let mut productions = named_list("Exps", sort("Exp"), ",", Some("KResult"));
        productions.extend(named_list("Vals", sort("Val"), ",", None));
        productions.extend(named_list("Rets", sort("Val"), ",", None));
        let mut subsorts = IDIOM.to_vec();
        subsorts.extend([("Rets", "Exps"), ("Rets", "KResult")]);
        let modules = [module(
            productions,
            subsorts
                .iter()
                .map(|(sub, sup)| subsort(sub, sup))
                .collect(),
        )];
        let message = error(&modules);
        assert!(
            message.contains("`Exps` already has the value list"),
            "{message}"
        );
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
        assert!(
            message.contains("the value list of a strict list"),
            "{message}"
        );
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
