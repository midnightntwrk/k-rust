//! Initializer totality is decided after written equations and macro expansions are available.
//! For I initializer labels and T RHS nodes, the least fixed point takes at most I changing
//! rounds, O(I x (I + T) x log P) plus the main-module EquationTotality judgement and resolution.
#![deny(clippy::wildcard_enum_match_arm)]

use crate::definition::head_totality::{EquationTotality, term_is_defined};
use crate::definition::totality::TotalityWitness;
use crate::definition::{
    AttributeKey, Definition, ProductionItem, ResolveError, Sentence, match_rule_label,
};
use crate::kast::{InternalLabel, Label, Term};
use crate::provenance::GeneratingPass;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn declare_initializer_totality_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    let main = resolved.main_module_id();
    let productions = resolved.production_catalog(main);
    let rules = resolved.rule_catalog(main);
    let totality = resolved
        .overloads(main)
        .ok()
        .map(|overloads| EquationTotality::judge(&productions, &rules, &overloads));
    let mut initializer_rules = BTreeMap::<String, Vec<InitializerRule>>::new();
    let mut cells = BTreeSet::new();
    let mut defined = BTreeSet::new();
    // Generation receipts separate configuration products from source-written markers.
    // Signatures separate nullary initializers from configuration-map readers.
    // Collect every constructor and unit before judging any initializer dependency.
    for (_, production) in productions.productions() {
        let Sentence::Production {
            label: Some(label),
            items,
            attributes,
            ..
        } = production
        else {
            continue;
        };
        if !configuration_generated(production) {
            continue;
        }
        if attributes.has(AttributeKey::Cell) {
            cells.insert(label.name.clone());
            defined.insert(label.name.clone());
        }
        if (attributes.has(AttributeKey::Cell) || attributes.has(AttributeKey::CellCollection))
            && let Some(unit) = attributes.string(AttributeKey::Unit)
        {
            defined.insert(unit.to_owned());
        }
        if attributes.has(AttributeKey::Initializer)
            && attributes.has(AttributeKey::Function)
            && matches!(items.as_slice(), [ProductionItem::Terminal(_)])
        {
            initializer_rules.entry(label.name.clone()).or_default();
        }
    }
    for (_, rule) in rules.rules() {
        let Sentence::Rule { body, ensures, .. } = rule else {
            unreachable!("rule catalogs contain rules")
        };
        let label = match_rule_label(rule);
        if let Some(equations) = initializer_rules.get_mut(&label.name) {
            let rule_right = match body.unannotated() {
                Term::Rewrite { right, .. } => (**right).clone(),
                Term::As { .. }
                | Term::Apply { .. }
                | Term::Sequence(_)
                | Term::Variable { .. }
                | Term::Token { .. }
                | Term::InjectedLabel(_) => body.clone(),
                Term::Annotated { .. } => unreachable!("unannotated terms carry no annotation"),
            };
            equations.push(InitializerRule {
                rule_right,
                ensures: ensures.clone(),
            });
        }
    }
    let proven = proven_initializers(&initializer_rules, &cells, &defined, totality.as_ref());
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            let Sentence::Production {
                label: Some(label),
                items,
                attributes,
                ..
            } = &**sentence
            else {
                continue;
            };
            if !configuration_generated(sentence)
                || productions.find_equivalent(sentence).is_none()
                || !attributes.has(AttributeKey::Initializer)
                || !attributes.has(AttributeKey::Function)
                || !matches!(items.as_slice(), [ProductionItem::Terminal(_)])
                || !proven.contains(&label.name)
            {
                continue;
            }
            // Only the complete all-equations judgement can mint evidence, after its fixed point.
            let evidence =
                defined_initializer(&initializer_rules[&label.name], &cells, &mut |label| {
                    initializer_label_is_defined(
                        label,
                        &initializer_rules,
                        &proven,
                        &defined,
                        totality.as_ref(),
                    )
                })
                .expect("the fixed point established every initializer equation");
            crate::definition::sentence_mut(sentence)
                .attributes_mut()
                .declare_total(TotalityWitness::nullary_initializer(evidence));
        }
    }
    Ok(output)
}

// Fresh-constant resolution expands the generated counter configuration and restamps its
// new productions. Existing configuration productions retain their expansion receipts.
fn configuration_generated(sentence: &Sentence) -> bool {
    sentence.attributes().origin_record().is_some_and(|origin| {
        matches!(
            origin.pass,
            GeneratingPass::ConfigurationExpansion | GeneratingPass::ResolveFreshConstants
        )
    })
}

/// Evidence that every generated equation of a nullary initializer builds a defined value.
pub(crate) struct DefinedInitializer(());

struct InitializerRule {
    rule_right: Term,
    ensures: Term,
}

fn initializer_rules_are_defined(
    rules: &[InitializerRule],
    generated_cells: &BTreeSet<String>,
    defined: &mut dyn FnMut(&Label) -> bool,
) -> bool {
    !rules.is_empty()
        && rules.iter().all(|rule| {
            matches!(rule.ensures.unannotated(), Term::Token { token, sort }
                    if token == "true" && *sort == crate::kast::Sort::builtin(crate::names::BuiltinSort::Bool))
                && term_is_defined(
                    &without_initializer_frames(&rule.rule_right, generated_cells),
                    defined,
                )
        })
}

fn defined_initializer(
    rules: &[InitializerRule],
    generated_cells: &BTreeSet<String>,
    defined: &mut dyn FnMut(&Label) -> bool,
) -> Option<DefinedInitializer> {
    if initializer_rules_are_defined(rules, generated_cells, defined) {
        Some(DefinedInitializer(()))
    } else {
        None
    }
}

/// Before cell closing, boundary #noDots applications describe the absence of a frame.
/// Erase only that positional syntax so the shared term judgement still checks every content term.
fn without_initializer_frames(term: &Term, generated_cells: &BTreeSet<String>) -> Term {
    match term.unannotated() {
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .enumerate()
                .filter(|(index, argument)| {
                    let boundary = generated_cells.contains(&label.name)
                        && (*index == 0 || *index + 1 == arguments.len());
                    let marker = matches!(argument.unannotated(), Term::Apply { label, arguments }
                        if label.is(InternalLabel::NoDots) && arguments.is_empty());
                    !(boundary && marker)
                })
                .map(|(_, argument)| without_initializer_frames(argument, generated_cells))
                .collect(),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| without_initializer_frames(item, generated_cells))
                .collect(),
        ),
        Term::Variable { .. }
        | Term::Token { .. }
        | Term::InjectedLabel(_)
        | Term::Rewrite { .. }
        | Term::As { .. } => term.unannotated().clone(),
        Term::Annotated { .. } => unreachable!("unannotated terms carry no annotation"),
    }
}

fn proven_initializers(
    rules: &BTreeMap<String, Vec<InitializerRule>>,
    generated_cells: &BTreeSet<String>,
    generated_defined_labels: &BTreeSet<String>,
    totality: Option<&EquationTotality>,
) -> BTreeSet<String> {
    let mut proven = BTreeSet::new();
    // Every changing round admits at least one label, and admission only grows.
    // Thus at most |rules| changing rounds precede the fixed point; cycles cannot prove themselves.
    loop {
        let before = proven.len();
        for (label, equations) in rules {
            if !proven.contains(label)
                && initializer_rules_are_defined(equations, generated_cells, &mut |label| {
                    initializer_label_is_defined(
                        label,
                        rules,
                        &proven,
                        generated_defined_labels,
                        totality,
                    )
                })
            {
                proven.insert(label.clone());
            }
        }
        if proven.len() == before {
            return proven;
        }
    }
}

fn initializer_label_is_defined(
    label: &Label,
    rules: &BTreeMap<String, Vec<InitializerRule>>,
    proven: &BTreeSet<String>,
    generated_defined_labels: &BTreeSet<String>,
    totality: Option<&EquationTotality>,
) -> bool {
    // Expansion's equations decide generated initializer labels, even if a source declaration
    // already names one; an earlier declaration cannot bypass the all-equations judgement.
    if rules.contains_key(&label.name) {
        proven.contains(&label.name)
    } else {
        generated_defined_labels.contains(&label.name)
            || label.is(InternalLabel::Cells)
            || totality.is_some_and(|t| t.label_is_defined(label))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kast::Sort;
    use crate::names::BuiltinSort;
    fn truth() -> Term {
        Term::Token {
            token: "true".into(),
            sort: Sort::builtin(BuiltinSort::Bool),
        }
    }
    fn incomplete_cell(label: &str, content: Term) -> Term {
        let marker = Term::apply(InternalLabel::NoDots.as_str(), vec![]);
        Term::apply(label, vec![marker.clone(), content, marker])
    }
    #[test]
    fn initializer_frame_markers_are_only_syntax_at_generated_cell_boundaries() {
        let cells = BTreeSet::from(["<n>".to_owned()]);
        let marker = Term::apply(InternalLabel::NoDots.as_str(), vec![]);
        let value = truth();
        let judge = |term: &Term| {
            let rule = InitializerRule {
                rule_right: term.clone(),
                ensures: truth(),
            };
            defined_initializer(&[rule], &cells, &mut |label| {
                cells.contains(&label.name) || label.name == "content"
            })
            .is_some()
        };
        assert!(judge(&incomplete_cell("<n>", value.clone())));
        assert!(!judge(&marker));
        assert!(!judge(&incomplete_cell("<n>", marker.clone())));
        assert!(!judge(&Term::apply(
            "content",
            vec![marker.clone(), value.clone(), marker.clone()],
        )));
        assert!(!judge(&incomplete_cell(
            "<n>",
            Term::apply("content", vec![marker.clone()]),
        )));
        assert!(!judge(&Term::apply(
            "<n>",
            vec![
                Term::apply(InternalLabel::NoDots.as_str(), vec![value.clone()]),
                value,
                marker
            ],
        )));
    }

    #[test]
    fn initializer_cycles_cannot_prove_themselves_even_with_a_defined_alternative() {
        let cells = BTreeSet::from(["<x>".to_owned(), "<y>".to_owned()]);
        let rule = |cell, child: Term| InitializerRule {
            rule_right: incomplete_cell(cell, child),
            ensures: truth(),
        };
        let rules = BTreeMap::from([
            (
                "initXCell".to_owned(),
                vec![
                    rule("<x>", truth()),
                    rule("<x>", Term::apply("initYCell", vec![])),
                ],
            ),
            (
                "initYCell".to_owned(),
                vec![rule("<y>", Term::apply("initXCell", vec![]))],
            ),
        ]);
        assert!(proven_initializers(&rules, &cells, &cells, None).is_empty());
    }
}
