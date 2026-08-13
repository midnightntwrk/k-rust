//! Definition-wide KLabel integrity checks.

use std::collections::{BTreeMap, BTreeSet};

use super::Sentence;
use crate::definition::{
    LabelHead, ModuleId, ProductionCatalog, ProductionItem, ResolvedDefinition, SortCatalog,
    match_rule_label,
};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::Term;

const FIXED_INTERNAL_LABELS: [&str; 13] = [
    "#cells",
    "#dots",
    "#noDots",
    "#Or",
    "#fun2",
    "#fun3",
    "#let",
    "#withConfig",
    "#OuterCast",
    "<generatedTop>",
    "#SemanticCastToBag",
    "_:=K_",
    "_:/=K_",
];

pub(super) fn internal_labels(
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> BTreeSet<String> {
    let mut labels: BTreeSet<String> = FIXED_INTERNAL_LABELS
        .map(str::to_owned)
        .into_iter()
        .collect();
    for sort in sorts.all_sorts() {
        labels.insert(format!("#SemanticCastTo{sort}"));
        labels.insert(format!("project:{sort}"));
        labels.insert(format!("is{sort}"));
    }
    for id in productions.ids() {
        let Sentence::Production {
            label: Some(label),
            items,
            ..
        } = productions.production(id)
        else {
            continue;
        };
        for item in items {
            if let ProductionItem::NonTerminal {
                name: Some(name), ..
            } = item
            {
                labels.insert(format!("project:{}:{name}", label.name));
            }
        }
    }
    labels
}

pub fn check_klabels(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> Vec<Diagnostic> {
    let defined = productions
        .productions()
        .filter_map(|(_, production)| match production {
            Sentence::Production {
                label: Some(label), ..
            } => Some(LabelHead::from(label)),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let internal = internal_labels(productions, sorts);
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        for term in label_checked_terms(sentence) {
            term.visit_preorder(&mut |term| {
                let label = match term {
                    Term::Apply { label, .. } | Term::InjectedLabel(label) => label,
                    _ => return,
                };
                if !defined.contains(&LabelHead::from(label)) && !internal.contains(&label.name) {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::UndefinedKLabel,
                        format!("Found klabel {} not defined in any production.", label.name),
                        sentence,
                    ));
                }
            });
        }
    }
    diagnostics
}

pub fn check_duplicate_klabels(definition: &ResolvedDefinition) -> Vec<Diagnostic> {
    let visible_modules = main_module_closure(definition);
    let mut previous = BTreeMap::<String, &Sentence>::new();
    let mut diagnostics = Vec::new();
    for module in definition
        .dependency_order()
        .iter()
        .filter(|module| visible_modules.contains(module))
    {
        let productions = definition
            .module(*module)
            .local_sentences
            .iter()
            .filter(|sentence| matches!(sentence, Sentence::Production { .. }))
            .collect::<Vec<_>>();
        for production in productions {
            let Sentence::Production {
                label: Some(label), ..
            } = production
            else {
                continue;
            };
            if let Some(previous) = previous.get(&label.name)
                && label.name != "#EmptyK"
            {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::DuplicateKLabel,
                    format!(
                        "Symbol {} is not unique. Previously defined as: {previous:?}",
                        label.name
                    ),
                    production,
                ));
            }
            previous.insert(label.name.clone(), production);
        }
    }
    diagnostics
}

pub fn check_function_rule_attributes(definition: &ResolvedDefinition) -> Vec<Diagnostic> {
    let module = definition.main_module_id();
    let productions = definition.production_catalog(module);
    let rules = definition.rule_catalog(module);
    let mut diagnostics = Vec::new();

    for function in productions.function_labels() {
        let function_rules = rules
            .rules()
            .filter(|(_, rule)| LabelHead::from(&match_rule_label(rule)) == *function)
            .map(|(_, rule)| rule)
            .collect::<Vec<_>>();
        let all_concrete = function_rules.iter().all(|rule| {
            has_no_arg(rule, "concrete") || rule.attributes().get("simplification").is_some()
        });
        let all_symbolic = function_rules.iter().all(|rule| {
            has_no_arg(rule, "symbolic") || rule.attributes().get("simplification").is_some()
        });
        for rule in function_rules {
            let attributes = rule.attributes();
            if (has_no_arg(rule, "concrete") && attributes.get("symbolic").is_some())
                || (has_no_arg(rule, "symbolic") && attributes.get("concrete").is_some())
            {
                diagnostics.push(both_concrete_and_symbolic(rule));
            }
            if attributes.get("concrete").is_some()
                && !all_concrete
                && attributes.get("simplification").is_none()
            {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InconsistentFunctionRuleAttributes,
                    "Found concrete attribute without simplification attribute on function with one or more non-concrete rules.",
                    rule,
                ));
            }
            if attributes.get("symbolic").is_some()
                && !all_symbolic
                && attributes.get("simplification").is_none()
            {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InconsistentFunctionRuleAttributes,
                    "Found symbolic attribute without simplification attribute on function with one or more non-symbolic rules.",
                    rule,
                ));
            }
        }
    }

    for (_, rule) in rules.rules() {
        let attributes = rule.attributes();
        if attributes.get("simplification").is_none()
            || attributes.get("concrete").is_none()
            || attributes.get("symbolic").is_none()
        {
            continue;
        }
        let concrete = attribute_names(rule, "concrete");
        let symbolic = attribute_names(rule, "symbolic");
        if concrete.is_empty() || symbolic.is_empty() {
            diagnostics.push(both_concrete_and_symbolic(rule));
            continue;
        }
        let overlap = concrete
            .intersection(&symbolic)
            .cloned()
            .collect::<Vec<_>>();
        if !overlap.is_empty() {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InconsistentFunctionRuleAttributes,
                format!(
                    "Rule cannot be both concrete and symbolic in the same variable: [{}]",
                    overlap.join(", ")
                ),
                rule,
            ));
        }
    }
    diagnostics
}

fn label_checked_terms(sentence: &Sentence) -> Vec<&Term> {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => vec![body, requires],
        _ => Vec::new(),
    }
}

fn main_module_closure(definition: &ResolvedDefinition) -> BTreeSet<ModuleId> {
    let mut modules = definition
        .transitive_imports(definition.main_module_id())
        .into_iter()
        .collect::<BTreeSet<_>>();
    modules.insert(definition.main_module_id());
    modules
}

fn has_no_arg(rule: &Sentence, attribute: &str) -> bool {
    rule.attributes().get_str(attribute) == Some("")
}

fn attribute_names(rule: &Sentence, attribute: &str) -> BTreeSet<String> {
    // Keep empty names: Java's `String.split`/`CollectionUtils.intersection`
    // combination reports two empty attributes as the overlap `[]`.
    rule.attributes()
        .get_str(attribute)
        .into_iter()
        .flat_map(|names| names.split(','))
        .map(str::trim)
        .map(str::to_owned)
        .collect()
}

fn both_concrete_and_symbolic(rule: &Sentence) -> Diagnostic {
    Diagnostic::error(
        DiagnosticCode::InconsistentFunctionRuleAttributes,
        "Rule cannot be both concrete and symbolic in the same variable.",
        rule,
    )
}
