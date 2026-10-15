//! Collection metadata names one symbol for each role, so a production schema cannot fill it,
//! and that symbol must have its role's signature (`builtin::collection_role_misfit`).

#![deny(clippy::wildcard_enum_match_arm)]

use crate::definition::production_kind::{UnitInstance, UnitInstanceError, mentions_parameter};
use crate::definition::{
    AttributeKey, LabelHead, ProductionCatalog, ProductionItem, Sentence, SortCatalog, SortHead,
};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::Sort;
use k_rust_backend::builtin::{
    CollectionKind, CollectionRole, RoleDeclaration, collection_role_misfit,
};

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
        diagnostics.extend(role_misfits(sentence, productions, sorts));
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

/// One error for each role symbol of a `LIST`, `SET` or `MAP` collection sort, named by
/// `sentence` (the production that carries the `element` attribute, which is the sort's concat),
/// whose production does not have its role's signature. kcompile emits each production as a
/// symbol whose sorts are its sorts' KORE names and whose hook is its hook, so this decides
/// exactly what the loader decides on the emitted KORE; the error is reported at the production
/// that writes the attributes. A role production with sort parameters, or a label naming no single
/// production, is reported elsewhere and skipped here.
fn role_misfits(
    sentence: &Sentence,
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> Vec<Diagnostic> {
    let Sentence::Production {
        label,
        parameters,
        sort,
        attributes,
        ..
    } = sentence
    else {
        return Vec::new();
    };
    let Some(element) = attributes.string(AttributeKey::Element) else {
        return Vec::new();
    };
    let Some(kind) = sorts
        .attributes_for(&SortHead::from(sort))
        .and_then(|attributes| attributes.string(AttributeKey::Hook))
        .and_then(CollectionKind::of_sort_hook)
    else {
        return Vec::new();
    };
    if !parameters.is_empty() || !sort.parameters.is_empty() {
        return Vec::new();
    }
    let concat = label
        .as_ref()
        .map_or("<unlabelled>", |label| label.name.as_str());
    let named = |name: &str| single_production(productions, name);
    let roles = [
        (
            CollectionRole::Unit,
            attributes
                .string(AttributeKey::Unit)
                .and_then(|unit| Some((unit, named(unit)?))),
        ),
        (
            CollectionRole::Element,
            named(element).map(|production| (element, production)),
        ),
        (CollectionRole::Concat, Some((concat, sentence))),
    ];
    let mut diagnostics = Vec::new();
    for (role, named) in roles {
        let Some((
            name,
            Sentence::Production {
                parameters: role_parameters,
                sort: result_sort,
                items,
                attributes: role_attributes,
                ..
            },
        )) = named
        else {
            continue;
        };
        if !role_parameters.is_empty() {
            continue;
        }
        let argument_sorts = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
            })
            .collect::<Vec<_>>();
        let hook = role_attributes.string(AttributeKey::Hook);
        let declaration = RoleDeclaration {
            sort_parameters: 0,
            argument_sorts: &argument_sorts,
            result_sort,
            hook,
        };
        let Some(reason) =
            collection_role_misfit(kind, role, sort, &declaration, ToString::to_string)
        else {
            continue;
        };
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
            CollectionRole::Concat => format!("two arguments of sort {sort}"),
        };
        let own = format!("{}.{}", kind.namespace(), role.name());
        let required = format!(
            "the {role} of collection sort {sort} must have result sort {sort} and {arguments}, with no hook or {own}"
        );
        let message = match role {
            CollectionRole::Unit | CollectionRole::Element => format!(
                "The {role} attribute of production {concat} names {name} : {signature}, which {reason}; {required}."
            ),
            CollectionRole::Concat => format!(
                "Production {concat} : {signature} carries the element attribute, so it is the concat of collection sort {sort}, but it {reason}; {required}."
            ),
        };
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidAttribute,
            message,
            sentence,
        ));
    }
    diagnostics
}

/// The one production labelled `name`, if exactly one is.
fn single_production<'a>(
    productions: &'a ProductionCatalog<'_>,
    name: &str,
) -> Option<&'a Sentence> {
    let [id] = productions.productions_for(&LabelHead::new(name)) else {
        return None;
    };
    Some(productions.production(*id))
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
