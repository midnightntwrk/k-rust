//! Initializer and covering-lambda totality is decided after written equations and macro expansions are available.
//! For I initializer and deferred lambda labels, T RHS nodes and U child-unit obligations, the least fixed point takes at most I changing rounds, O(I x (I + T + U) x log P) plus the main-module EquationTotality judgement and resolution.
//! RHS preparation allocates O(T + U) once.
#![deny(clippy::wildcard_enum_match_arm)]

use crate::definition::head_totality::{EquationTotality, is_true, term_is_defined};
use crate::definition::totality::TotalityWitness;
use crate::definition::{
    AttributeKey, Definition, ProductionItem, ResolveError, Sentence, match_rule_label,
};
use crate::kast::{InternalLabel, Label, Sort, Term};
use crate::provenance::GeneratingPass;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn declare_initializer_totality_pass(
    input: &super::super::pipeline::PassInput<'_>,
    state: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    let main = resolved.main_module_id();
    let productions = resolved.production_catalog(main);
    let rules = resolved.rule_catalog(main);
    let totality = resolved
        .overloads(main)
        .ok()
        .map(|overloads| EquationTotality::judge(&productions, &rules, &overloads));
    let lambdas = state
        .covering_lambdas
        .iter()
        .map(|lambda| (lambda.label().to_owned(), lambda))
        .collect::<BTreeMap<_, _>>();
    let mut headed = BTreeSet::new();
    for (_, rule) in rules.rules() {
        if !rule.attributes().has(AttributeKey::Simplification) {
            headed.insert(match_rule_label(rule).name);
        }
    }
    let mut deferred_rules = BTreeMap::<String, Vec<DeferredRule>>::new();
    let mut cells = BTreeSet::new();
    let mut defined = BTreeSet::new();
    let mut units = BTreeMap::<Sort, BTreeSet<String>>::new();
    for (_, production) in productions.productions() {
        if let Sentence::Production {
            sort, attributes, ..
        } = production
            && (attributes.has(AttributeKey::Cell) || attributes.has(AttributeKey::CellCollection))
            && let Some(unit) = attributes.string(AttributeKey::Unit)
        {
            units
                .entry(sort.clone())
                .or_default()
                .insert(unit.to_owned());
        }
    }
    let mut child_units = BTreeMap::<String, BTreeSet<String>>::new();
    // Generation receipts separate configuration products from source-written markers.
    // Signatures separate nullary initializers from configuration-map readers.
    // Collect cell boundaries and evidently defined hooked units before deferred dependencies.
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
        if production
            .attributes()
            .origin_record()
            .is_some_and(|origin| origin.pass == GeneratingPass::ResolveFun)
            && attributes.has(AttributeKey::Function)
            && !attributes.has(AttributeKey::Total)
            && lambdas.contains_key(&label.name)
        {
            deferred_rules.entry(label.name.clone()).or_default();
        }
        if !configuration_generated(production) {
            continue;
        }
        if attributes.has(AttributeKey::Cell) {
            cells.insert(label.name.clone());
            let required = child_units.entry(label.name.clone()).or_default();
            for item in items {
                if let ProductionItem::NonTerminal { sort, .. } = item
                    && let Some(units) = units.get(sort)
                {
                    required.extend(units.iter().cloned());
                }
            }
        }
        // Ordinary cell constructors and optional units use EquationTotality below: source
        // equations or a merged function property can make a generated label partial.
        // Hooked collection units build the empty collection despite lacking a total marker,
        // but any non-simplification rule headed by the unit can change that meaning.
        // The unit's own receipt supplies its origin; a cell's source-written unit property
        // cannot supply evidence.
        if matches!(items.as_slice(), [ProductionItem::Terminal(_)])
            && attributes.has(AttributeKey::Function)
            && matches!(
                attributes.string(AttributeKey::Hook),
                Some("BAG.unit" | "SET.unit" | "MAP.unit" | "LIST.unit")
            )
            && !headed.contains(&label.name)
        {
            defined.insert(label.name.clone());
        }
        if attributes.has(AttributeKey::Initializer)
            && attributes.has(AttributeKey::Function)
            && matches!(items.as_slice(), [ProductionItem::Terminal(_)])
        {
            deferred_rules.entry(label.name.clone()).or_default();
        }
    }
    for (_, rule) in rules.rules() {
        let Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        } = rule
        else {
            unreachable!("rule catalogs contain rules")
        };
        let label = match_rule_label(rule);
        if let Some(equations) = deferred_rules.get_mut(&label.name) {
            let rule_right = match body.unannotated() {
                Term::Rewrite { right, .. } => &**right,
                Term::As { .. }
                | Term::Apply { .. }
                | Term::Sequence(_)
                | Term::Variable { .. }
                | Term::Token { .. }
                | Term::InjectedLabel(_) => body,
                Term::Annotated { .. } => unreachable!("unannotated terms carry no annotation"),
            };
            equations.push(DeferredRule {
                // Boundary syntax is independent of the proven-label set; erase it once.
                rule_right: without_initializer_frames(rule_right, &cells),
                requires: requires.clone(),
                ensures: ensures.clone(),
                // Cell closing fills absent optional/collection slots with these units.
                // Check all possible insertions rather than duplicating its placement analysis.
                // This may withhold evidence when a partial unit's slot is already populated.
                child_units: initializer_child_units(rule_right, &child_units),
            });
        }
    }
    let proven = proven_deferred_labels(&deferred_rules, &lambdas, &defined, totality.as_ref());
    let mut changed = false;
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
            let initializer = configuration_generated(sentence)
                && attributes.has(AttributeKey::Initializer)
                && matches!(items.as_slice(), [ProductionItem::Terminal(_)]);
            let lambda = lambdas.get(&label.name).filter(|_| {
                attributes
                    .origin_record()
                    .is_some_and(|origin| origin.pass == GeneratingPass::ResolveFun)
            });
            if (!initializer && lambda.is_none())
                || attributes.has(AttributeKey::Total)
                || productions.find_equivalent(sentence).is_none()
                || !attributes.has(AttributeKey::Function)
                || !proven.contains(&label.name)
            {
                continue;
            }
            // Only the complete all-equations judgement can mint evidence, after its fixed point.
            let equations = &deferred_rules[&label.name];
            let mut label_is_defined = |label: &Label| {
                deferred_label_is_defined(
                    label,
                    &deferred_rules,
                    &proven,
                    &defined,
                    totality.as_ref(),
                )
            };
            let witness = if let Some(lambda) = lambda {
                TotalityWitness::defined_body(
                    defined_lambda(lambda, equations, &mut label_is_defined)
                        .expect("the fixed point established every lambda equation"),
                )
            } else {
                TotalityWitness::nullary_initializer(
                    defined_initializer(equations, &mut label_is_defined)
                        .expect("the fixed point established every initializer equation"),
                )
            };
            crate::definition::sentence_mut(sentence)
                .attributes_mut()
                .declare_total(witness);
            changed = true;
        }
    }
    state.record_initializer_totality_change(changed);
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

/// Evidence that an unconditional equation covers the nullary initializer's only argument tuple
/// and every equation builds a defined value with a trivial postcondition.
pub(crate) struct DefinedInitializer(());

struct DeferredRule {
    // Collected with generated-cell boundary frames already removed.
    rule_right: Term,
    requires: Term,
    ensures: Term,
    child_units: BTreeSet<String>,
}

fn initializer_child_units(
    term: &Term,
    child_units: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    let mut required = BTreeSet::new();
    term.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } = term.unannotated()
            && let Some(units) = child_units.get(&label.name)
        {
            required.extend(units.iter().cloned());
        }
    });
    required
}

fn initializer_rules_are_defined(
    rules: &[DeferredRule],
    defined: &mut dyn FnMut(&Label) -> bool,
) -> bool {
    // A partial function needs an applicable equation, not only defined possible results.
    // Nullary signatures have one argument tuple, covered by any unconditional equation.
    rules.iter().any(|rule| is_true(&rule.requires))
        && rules.iter().all(|rule| {
            is_true(&rule.ensures)
                && term_is_defined(&rule.rule_right, defined)
                && rule
                    .child_units
                    .iter()
                    .all(|unit| defined(&Label::new(unit)))
        })
}

fn defined_lambda(
    lambda: &super::resolve_fun::CoveringLambda,
    rules: &[DeferredRule],
    defined: &mut dyn FnMut(&Label) -> bool,
) -> Option<super::resolve_fun::DefinedBody> {
    if !rules.iter().all(|rule| {
        rule.child_units
            .iter()
            .all(|unit| defined(&Label::new(unit)))
    }) {
        return None;
    }
    lambda.defined_body(
        rules
            .iter()
            .map(|rule| (&rule.rule_right, &rule.requires, &rule.ensures)),
        defined,
    )
}

fn deferred_rules_are_defined(
    label: &str,
    rules: &[DeferredRule],
    lambdas: &BTreeMap<String, &super::resolve_fun::CoveringLambda>,
    defined: &mut dyn FnMut(&Label) -> bool,
) -> bool {
    if let Some(lambda) = lambdas.get(label) {
        defined_lambda(lambda, rules, defined).is_some()
    } else {
        initializer_rules_are_defined(rules, defined)
    }
}

fn defined_initializer(
    rules: &[DeferredRule],
    defined: &mut dyn FnMut(&Label) -> bool,
) -> Option<DefinedInitializer> {
    if initializer_rules_are_defined(rules, defined) {
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

fn proven_deferred_labels(
    rules: &BTreeMap<String, Vec<DeferredRule>>,
    lambdas: &BTreeMap<String, &super::resolve_fun::CoveringLambda>,
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
                && deferred_rules_are_defined(label, equations, lambdas, &mut |label| {
                    deferred_label_is_defined(
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

fn deferred_label_is_defined(
    label: &Label,
    rules: &BTreeMap<String, Vec<DeferredRule>>,
    proven: &BTreeSet<String>,
    generated_defined_labels: &BTreeSet<String>,
    totality: Option<&EquationTotality>,
) -> bool {
    // Collected equations decide deferred generated labels, even if a source declaration
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
            let rule = DeferredRule {
                rule_right: without_initializer_frames(term, &cells),
                requires: truth(),
                ensures: truth(),
                child_units: BTreeSet::new(),
            };
            defined_initializer(&[rule], &mut |label| {
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
        let rule = |cell, child: Term| DeferredRule {
            rule_right: without_initializer_frames(&incomplete_cell(cell, child), &cells),
            requires: truth(),
            ensures: truth(),
            child_units: BTreeSet::new(),
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
        assert!(proven_deferred_labels(&rules, &BTreeMap::new(), &cells, None).is_empty());
    }

    #[test]
    fn nullary_initializer_needs_unconditional_coverage_and_every_result_defined() {
        let conditional = || DeferredRule {
            rule_right: truth(),
            requires: Term::variable("Condition"),
            ensures: truth(),
            child_units: BTreeSet::new(),
        };
        let unconditional = || DeferredRule {
            requires: truth(),
            ..conditional()
        };
        let judge = |rules: &[DeferredRule]| defined_initializer(rules, &mut |_| false).is_some();
        assert!(!judge(&[]));
        assert!(!judge(&[conditional()]));
        assert!(judge(&[unconditional()]));
        assert!(judge(&[conditional(), unconditional()]));
        assert!(judge(&[unconditional(), conditional()]));
        assert!(!judge(&[
            unconditional(),
            DeferredRule {
                rule_right: Term::apply("partial", vec![]),
                ..conditional()
            },
        ]));
        assert!(!judge(&[
            unconditional(),
            DeferredRule {
                ensures: Term::variable("Postcondition"),
                ..conditional()
            },
        ]));
    }
}
