//! Collection metadata names one symbol for each role, so a production schema cannot fill it.

#![deny(clippy::wildcard_enum_match_arm)]

use crate::definition::production_kind::{UnitInstance, UnitInstanceError, mentions_parameter};
use crate::definition::{
    AttributeKey, LabelHead, ProductionCatalog, ProductionItem, Sentence, SortCatalog, SortHead,
};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::Sort;

const COLLECTION_ROLES: [&str; 15] = [
    "LIST.element",
    "LIST.concat",
    "LIST.unit",
    "SET.element",
    "SET.concat",
    "SET.unit",
    "MAP.element",
    "MAP.concat",
    "MAP.unit",
    "BAG.element",
    "BAG.concat",
    "BAG.unit",
    "RANGEMAP.elementRng",
    "RANGEMAP.concat",
    "RANGEMAP.unit",
];
const COLLECTION_SORTS: [&str; 5] = [
    "MAP.Map",
    "SET.Set",
    "LIST.List",
    "BAG.Bag",
    "RANGEMAP.RangeMap",
];

pub(crate) fn check_collection_productions(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let (label, parameters, sort, items, attributes) = match sentence {
            Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes,
            } => (label, parameters, sort, items, attributes),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => continue,
        };
        let name = label
            .as_ref()
            .map_or("<unlabelled>", |label| label.name.as_str());
        let hook = attributes.string(AttributeKey::Hook);
        if !parameters.is_empty()
            && let Some(hook) = hook.filter(|hook| COLLECTION_ROLES.contains(hook))
        {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::UnsupportedParametricSort,
                format!(
                    "Production {name} fills the {hook} role of a hooked collection with sort parameters {{{}}}; a hooked collection names one symbol per role and fixes one key and value sort, so a family of symbols cannot fill it; declare it for each instance instead.",
                    parameter_names(parameters),
                ),
                sentence,
            ));
        }
        for key in [
            AttributeKey::Element,
            AttributeKey::Update,
            AttributeKey::WrapElement,
        ] {
            let Some(named) = attributes.string(key) else {
                continue;
            };
            let Some(named_parameters) = single_parameters(productions, named) else {
                continue;
            };
            if !named_parameters.is_empty() {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::UnsupportedParametricSort,
                    format!(
                        "The {} attribute of production {name} names {named} with sort parameters {{{}}}; the attribute names one symbol, but a production schema is a family of symbols; declare it for each instance instead.",
                        key.as_str(), parameter_names(named_parameters),
                    ),
                    sentence,
                ));
            }
        }
        if let Some(unit) = attributes.string(AttributeKey::Unit)
            && single_parameters(productions, unit).is_some_and(|parameters| !parameters.is_empty())
        {
            let collection_hook = sorts
                .attributes_for(&SortHead::from(sort))
                .and_then(|attributes| attributes.string(AttributeKey::Hook))
                .filter(|hook| COLLECTION_SORTS.contains(hook));
            let reason = if let Some(hook) = collection_hook {
                Some(format!(
                    "sort {sort} has collection hook {hook}, whose unit is rebuilt by symbol name without sort arguments"
                ))
            } else if let Err(UnitInstanceError::Unbound { parameters }) =
                UnitInstance::of(productions, unit, sort)
            {
                Some(format!(
                    "matching its result sort against {sort} does not bind all of its sort parameters {{{}}}",
                    parameter_names(&parameters)
                ))
            } else {
                None
            };
            if let Some(reason) = reason {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidUnitAttribute,
                    format!("The unit attribute of production {name} names schematic production {unit}, but {reason}."),
                    sentence,
                ));
            }
        }
        if hook == Some("MAP.in_keys")
            && items
                .iter()
                .filter_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => Some(sort),
                    ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
                })
                .nth(1)
                .is_some_and(|sort| mentions_parameter(sort, parameters))
        {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::UnsupportedParametricSort,
                format!(
                    "The MAP.in_keys production {name} has a map argument mentioning its sort parameters {{{}}}; the generated map axioms require one fixed collection sort.",
                    parameter_names(parameters),
                ),
                sentence,
            ));
        }
    }
    diagnostics
}

fn parameter_names(parameters: &[Sort]) -> String {
    parameters
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

fn single_parameters<'a>(productions: &'a ProductionCatalog<'_>, name: &str) -> Option<&'a [Sort]> {
    let [id] = productions.productions_for(&LabelHead::new(name)) else {
        return None;
    };
    match productions.production(*id) {
        Sentence::Production { parameters, .. } => Some(parameters),
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => None,
    }
}
