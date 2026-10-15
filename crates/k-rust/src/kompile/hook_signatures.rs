//! A hooked symbol whose declaration denotes no value of its result sort is rejected where it is
//! declared, before its KORE is emitted.
//!
//! A hooked symbol `f : S1 ... Sn -> S` denotes a value of `S` whatever computes it. Whether the
//! hook gives one, on arguments of the declared sorts, is the rule of
//! [`k_rust_backend::builtin::collection_hook_misfit`], which the backend also applies to every
//! definition it loads. A definition is decided here by that same rule, over the facts the
//! emitted declarations state: the emitted symbol's argument and result sorts are the production's
//! non-terminal and result sorts, a collection sort's element (key, value) sorts are the argument
//! sorts of the symbol its `element` attribute names, and the subsort order is the one the
//! emitted subsort axioms state, which has no pair into `K`. So a definition that compiles
//! declares no symbol the backend refuses to load, and the error names the production rather than
//! its KORE symbol.
//!
//! The same holds for a collection sort's unit, element and concat symbols: each must have its
//! role's signature ([`k_rust_backend::builtin::collection_role_misfit`], which the backend
//! applies to every collection sort it loads), decided here over the declarations emission
//! writes ([`collection_role_misfit_diagnostics`]).
//!
//! An element (key, value) sort may be a closed instance of a parametric sort such as `MInt{64}`:
//! the emitted element symbol takes that instance, which is one sort, and the subsort order
//! relates it like any other sort.

use std::collections::{BTreeMap, BTreeSet};

use k_rust_backend::builtin::{
    CollectionKind, CollectionRole, CollectionShape, RoleDeclaration, SortFacts,
    collection_hook_misfit, collection_role_misfit,
};
use k_rust_kore::names::BuiltinSort;

use super::module_to_kore::{collection_concatenation, emitted_subsort_pair, interpreted_hook};
use crate::{
    definition::{
        AttributeKey, LabelHead, PartialOrder, ProductionCatalog, ProductionItem,
        ResolvedDefinition, Sentence, production_kind::ProductionKind,
    },
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::Sort,
};

/// The collection sorts and the subsort order of the main module.
struct FrontendSorts<'a> {
    collections: BTreeMap<Sort, CollectionShape<Sort>>,
    subsorts: &'a PartialOrder<Sort>,
}

impl SortFacts for FrontendSorts<'_> {
    type Sort = Sort;

    fn collection(&self, sort: &Sort) -> Option<CollectionShape<Sort>> {
        self.collections.get(sort).cloned()
    }

    fn below(&self, sub: &Sort, sup: &Sort) -> bool {
        self.subsorts.less_than_eq(sub, sup)
    }

    fn builtin(&self, sort: BuiltinSort) -> Sort {
        Sort::builtin(sort)
    }

    fn render(&self, sort: &Sort) -> String {
        sort.to_string()
    }
}

fn non_terminal_sorts(items: &[ProductionItem]) -> Vec<Sort> {
    items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
            ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
        })
        .collect()
}

/// One error for every production of the main module that declares a hooked symbol (a
/// `function` whose hook namespace is builtin or in `admitted`) under whose declaration the hook
/// gives no value of the symbol's result sort.
pub(super) fn collection_hook_misfit_diagnostics(
    definition: &ResolvedDefinition,
    admitted: &[String],
) -> Vec<Diagnostic> {
    let module = definition.main_module_id();
    let productions = definition.production_catalog(module);
    // The order the emitted subsort axioms state; a cyclic relation is reported by emission.
    let Ok(subsorts) = PartialOrder::new(
        productions
            .productions()
            .filter_map(|(_, production)| emitted_subsort_pair(production))
            .map(|(child, parent)| (child.clone(), parent.clone())),
    ) else {
        return Vec::new();
    };
    let sorts = definition.sort_catalog(module);
    let mut collections = BTreeMap::new();
    for (head, attributes) in sorts.attributes_by_head() {
        let hook = attributes.string(AttributeKey::Hook);
        if head.parameters() != 0 || !matches!(hook, Some("LIST.List" | "SET.Set" | "MAP.Map")) {
            continue;
        }
        // A collection sort whose declaration names no element symbol of one production is
        // rejected by emission.
        let Some(Sentence::Production { attributes, .. }) =
            collection_concatenation(head, &productions)
        else {
            continue;
        };
        let Some(element) = attributes.string(AttributeKey::Element) else {
            continue;
        };
        let [id] = productions.productions_for(&LabelHead::new(element)) else {
            continue;
        };
        let Sentence::Production { items, .. } = productions.production(*id) else {
            continue;
        };
        let shape = match (hook, non_terminal_sorts(items).as_slice()) {
            (Some("LIST.List"), [element]) => CollectionShape::List(element.clone()),
            (Some("SET.Set"), [element]) => CollectionShape::Set(element.clone()),
            (Some("MAP.Map"), [key, value]) => CollectionShape::Map {
                key: key.clone(),
                value: value.clone(),
            },
            _ => continue,
        };
        collections.insert(Sort::new(head.as_str()), shape);
    }
    let facts = FrontendSorts {
        collections,
        subsorts: &subsorts,
    };
    let mut reported = BTreeSet::new();
    let mut diagnostics = Vec::new();
    // Invariant: `diagnostics` has one error for every label before `production` that declares a
    // hooked symbol whose declaration `collection_hook_misfit` rejects.
    for (_, production) in productions.productions() {
        let Sentence::Production {
            label: Some(label),
            sort,
            items,
            attributes,
            ..
        } = production
        else {
            continue;
        };
        if !ProductionKind::of(production).declares_symbol(true)
            || interpreted_hook(attributes, admitted).is_none()
        {
            continue;
        }
        let Some(hook) = attributes.string(AttributeKey::Hook) else {
            continue;
        };
        let Some(reason) = collection_hook_misfit(hook, &non_terminal_sorts(items), sort, &facts)
        else {
            continue;
        };
        if !reported.insert(label.name.clone()) {
            continue;
        }
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidAttribute,
            format!(
                "Production {} is hooked to {hook}, but its declaration denotes no value of its result sort {sort}: {reason}.",
                label.name
            ),
            production,
        ));
    }
    diagnostics
}

/// One error for each role symbol of a `LIST`, `SET` or `MAP` collection sort of the main
/// module whose emitted declaration does not have its role's signature
/// (`collection_role_misfit`), decided over exactly the declarations emission writes for the
/// sort: the concat is the production `collection_concatenation` chooses, the unit and element
/// are the single productions its `unit` and `element` attributes name, each symbol's argument
/// and result sorts are its production's non-terminal and result sorts, and its hook is the one
/// emission writes (`interpreted_hook`: a `function`'s hook whose namespace is builtin or in
/// `admitted`). So kcompile refuses a definition here only when the loader would refuse the KORE
/// it emits (as a role misfit, or a map element of the wrong arity as a malformed collection), and
/// it refuses every definition whose KORE the loader would refuse as a role misfit. Each error is
/// located at the concat production, which writes the attributes, and names the unit or element
/// production with its own position. A sort with parameters, a role production with parameters,
/// and a label naming no single production are refused by emission or the parametric checks and
/// are skipped here.
pub(super) fn collection_role_misfit_diagnostics(
    definition: &ResolvedDefinition,
    admitted: &[String],
) -> Vec<Diagnostic> {
    let module = definition.main_module_id();
    let productions = definition.production_catalog(module);
    let sorts = definition.sort_catalog(module);
    let mut diagnostics = Vec::new();
    for (head, sort_attributes) in sorts.attributes_by_head() {
        let Some(kind) = sort_attributes
            .string(AttributeKey::Hook)
            .and_then(CollectionKind::of_sort_hook)
        else {
            continue;
        };
        if head.parameters() != 0 {
            continue;
        }
        let Some(
            concat @ Sentence::Production {
                label: Some(label),
                attributes,
                ..
            },
        ) = collection_concatenation(head, &productions)
        else {
            continue;
        };
        let collection = Sort::new(head.as_str());
        let roles = [
            (
                CollectionRole::Unit,
                attributes
                    .string(AttributeKey::Unit)
                    .and_then(|name| single_production(&productions, name)),
            ),
            (
                CollectionRole::Element,
                attributes
                    .string(AttributeKey::Element)
                    .and_then(|name| single_production(&productions, name)),
            ),
            (CollectionRole::Concat, Some((label.name.as_str(), concat))),
        ];
        for (role, named) in roles {
            let Some((
                name,
                production @ Sentence::Production {
                    parameters,
                    sort: result_sort,
                    items,
                    attributes: role_attributes,
                    ..
                },
            )) = named
            else {
                continue;
            };
            if !parameters.is_empty() {
                continue;
            }
            let argument_sorts = non_terminal_sorts(items);
            let hook = interpreted_hook(role_attributes, admitted)
                .and_then(|_| role_attributes.string(AttributeKey::Hook));
            let declaration = RoleDeclaration {
                sort_parameters: 0,
                argument_sorts: &argument_sorts,
                result_sort,
                hook,
            };
            let Some(reason) =
                collection_role_misfit(kind, role, &collection, &declaration, ToString::to_string)
            else {
                continue;
            };
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidAttribute,
                role_misfit_message(
                    kind,
                    role,
                    &collection,
                    &label.name,
                    name,
                    production,
                    &argument_sorts,
                    result_sort,
                    &reason,
                ),
                concat,
            ));
        }
    }
    diagnostics
}

/// `name` with the one production labelled `name`, if exactly one is.
fn single_production<'a>(
    productions: &'a ProductionCatalog<'_>,
    name: &'a str,
) -> Option<(&'a str, &'a Sentence)> {
    match productions.productions_for(&LabelHead::new(name)) {
        [id] => Some((name, productions.production(*id))),
        _ => None,
    }
}

/// The message of a role misfit: the role, the named production with its signature and, for a
/// unit or element, its own position, what does not fit, and what the role requires.
#[allow(clippy::too_many_arguments)]
fn role_misfit_message(
    kind: CollectionKind,
    role: CollectionRole,
    collection: &Sort,
    concat: &str,
    name: &str,
    production: &Sentence,
    argument_sorts: &[Sort],
    result_sort: &Sort,
    reason: &str,
) -> String {
    let signature = argument_sorts
        .iter()
        .map(ToString::to_string)
        .chain(["->".to_owned(), result_sort.to_string()])
        .collect::<Vec<_>>()
        .join(" ");
    let arguments = match role {
        CollectionRole::Unit => "no argument".to_owned(),
        CollectionRole::Element if kind.element_arity() == 1 => "one argument".to_owned(),
        CollectionRole::Element => "two arguments, a key and a value".to_owned(),
        CollectionRole::Concat => format!("two arguments of sort {collection}"),
    };
    let own = format!("{}.{}", kind.namespace(), role.name());
    let required = format!(
        "the {role} of collection sort {collection} must have result sort {collection} and {arguments}, with no hook or {own}"
    );
    match role {
        CollectionRole::Unit | CollectionRole::Element => {
            let attributes = production.attributes();
            let position = match (attributes.source(), attributes.location()) {
                (Some(source), Some(location)) => format!(
                    " ({source}:{}:{})",
                    location.start_line, location.start_column
                ),
                (None, Some(location)) => {
                    format!(" ({}:{})", location.start_line, location.start_column)
                }
                (Some(_) | None, None) => String::new(),
            };
            format!(
                "The {role} attribute of production {concat} names {name}{position} : {signature}, which {reason}; {required}."
            )
        }
        CollectionRole::Concat => format!(
            "Production {concat} : {signature} carries the element attribute, which makes it the concat of collection sort {collection}; it {reason}; {required}."
        ),
    }
}
