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
//! The backend also refuses a collection whose element symbol takes an instance of a parametric
//! sort (`MInt{64}`), because it names element (key, value) sorts by sort name; such an element
//! symbol is rejected here too, at its production, until the backend carries those sorts whole.

use std::collections::{BTreeMap, BTreeSet};

use k_rust_backend::builtin::{CollectionShape, SortFacts, collection_hook_misfit};

use super::module_to_kore::{collection_concatenation, emitted_subsort_pair, interpreted_hook};
use crate::{
    definition::{
        AttributeKey, LabelHead, PartialOrder, ProductionItem, ResolvedDefinition, Sentence,
        production_kind::ProductionKind,
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

/// One error for every element symbol of a collection sort of the main module that takes an
/// instance of a parametric sort, and one for every production of the main module that declares
/// a hooked symbol (a `function` whose hook namespace is builtin or in `admitted`) under whose
/// declaration the hook gives no value of the symbol's result sort.
pub(super) fn collection_hook_diagnostics(
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
    let mut diagnostics = Vec::new();
    // The collection sorts rejected for a parametric element sort, whose shape is not decided.
    let mut undecided = BTreeSet::new();
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
        let element_sorts = non_terminal_sorts(items);
        // A closed instance of a parametric sort such as `MInt{64}` is one sort, and the backend
        // loads a collection over it; compiling one is still refused until the compiled form of
        // such a collection is checked from source to load.
        if let Some(applied) = element_sorts
            .iter()
            .find(|sort| !sort.parameters.is_empty())
        {
            let (kind, roles) = if hook == Some("MAP.Map") {
                ("map", "key and value")
            } else {
                ("collection", "element")
            };
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::UnsupportedParametricSort,
                format!(
                    "Production {element} is the element symbol of collection sort {}, but its {roles} sorts include the parametric sort instance {applied}: parametric {kind} element sorts are not supported.",
                    head.as_str()
                ),
                productions.production(*id),
            ));
            undecided.insert(Sort::new(head.as_str()));
            continue;
        }
        let shape = match (hook, element_sorts.as_slice()) {
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
    // Invariant: besides the parametric element errors, `diagnostics` has one error for every
    // label before `production` that declares a hooked symbol whose declaration
    // `collection_hook_misfit` rejects.
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
        let arguments = non_terminal_sorts(items);
        // Whether a hook fits a collection sort of undecided shape is not decided.
        if undecided.contains(sort) || arguments.iter().any(|sort| undecided.contains(sort)) {
            continue;
        }
        let Some(reason) = collection_hook_misfit(hook, &arguments, sort, &facts) else {
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
