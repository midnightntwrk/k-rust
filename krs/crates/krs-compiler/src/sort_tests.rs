//! Warnings for `k::is!` and `k::project!` terms that test nothing (KF-013).
//!
//! A projection to a supersort of its operand's sort is the identity, and
//! `k::is!(K, ..)` is always true. Both are legal K, so they warn. The check
//! runs on Definition IR, where every operand has its inferred sort.

use std::collections::{BTreeMap, BTreeSet};

use krs_diagnostic::{Diagnostic, Location, Severity, codes};
use krs_ir::{ApplicationRef, BuiltinSort, GeneratedOperation};
use krs_ir_levels::{
    DefinitionIr, DefinitionSentence, DefinitionSortRef, DefinitionTerm, DefinitionTermKind,
};

use crate::capability::sentence_terms;

/// The `warning[krs::analysis::trivial-sort-test]` diagnostics of a
/// definition, in sentence order.
#[must_use]
pub fn sort_test_warnings(definition: &DefinitionIr) -> Vec<Diagnostic> {
    let mut parents = BTreeMap::<DefinitionSortRef, BTreeSet<DefinitionSortRef>>::new();
    let mut names = BTreeMap::new();
    for module in definition.modules() {
        for sentence in module.sentences() {
            match sentence {
                DefinitionSentence::Subsort(subsort) => {
                    parents
                        .entry(subsort.subsort().clone())
                        .or_default()
                        .insert(subsort.supersort().clone());
                }
                DefinitionSentence::SyntaxSort(sort) => {
                    names.insert(
                        DefinitionSortRef::Declared(sort.symbol().id().clone()),
                        sort.symbol().emitted_name().to_owned(),
                    );
                }
                _ => {}
            }
        }
    }
    let mut warnings = Vec::new();
    for module in definition.modules() {
        for sentence in module.sentences() {
            let DefinitionSentence::Rule(rule) = sentence else {
                continue;
            };
            for term in sentence_terms(rule) {
                collect(term, &parents, &names, &mut warnings);
            }
        }
    }
    warnings
}

fn collect(
    term: &DefinitionTerm,
    parents: &BTreeMap<DefinitionSortRef, BTreeSet<DefinitionSortRef>>,
    names: &BTreeMap<DefinitionSortRef, String>,
    warnings: &mut Vec<Diagnostic>,
) {
    let children: Vec<&DefinitionTerm> = match term.kind() {
        DefinitionTermKind::Variable { .. } | DefinitionTermKind::Token { .. } => Vec::new(),
        DefinitionTermKind::Application {
            application,
            arguments,
            ..
        } => {
            if let ApplicationRef::Generated(operation) = application
                && let [operand] = arguments.as_slice()
                && let Some(message) = trivial(operation, operand, parents, names)
            {
                let mut warning = Diagnostic::error(
                    codes::analysis::TRIVIAL_SORT_TEST,
                    message,
                    term.origin()
                        .origin()
                        .exact_authored_range()
                        .map_or(Location::None, Location::Source),
                );
                warning.severity = Severity::Warning;
                warnings.push(warning);
            }
            arguments.iter().collect()
        }
        DefinitionTermKind::KSequence { items, .. } => items.iter().collect(),
        DefinitionTermKind::Map(operands) => operands.operands().collect(),
        DefinitionTermKind::List(operands) => operands.operands().collect(),
        DefinitionTermKind::Set(operands) => operands.operands().collect(),
        DefinitionTermKind::Cell { children, .. } => children.iter().collect(),
        DefinitionTermKind::Rewrite { from, to } => vec![from.as_ref(), to.as_ref()],
        DefinitionTermKind::As { pattern, .. } => vec![pattern.as_ref()],
        DefinitionTermKind::Or { alternatives } => alternatives.iter().collect(),
        DefinitionTermKind::Matches {
            subject, pattern, ..
        } => vec![subject.as_ref(), pattern.as_ref()],
        DefinitionTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => vec![pattern.as_ref(), value.as_ref(), body.as_ref()],
    };
    for child in children {
        collect(child, parents, names, warnings);
    }
}

fn trivial(
    operation: &GeneratedOperation<DefinitionSortRef>,
    operand: &DefinitionTerm,
    parents: &BTreeMap<DefinitionSortRef, BTreeSet<DefinitionSortRef>>,
    names: &BTreeMap<DefinitionSortRef, String>,
) -> Option<String> {
    match operation {
        GeneratedOperation::SortPredicate(DefinitionSortRef::Builtin(BuiltinSort::KSequence)) => {
            Some("`k::is!(K, ..)` is always true: every term has sort `K`".to_owned())
        }
        GeneratedOperation::SortPredicate(_) => None,
        GeneratedOperation::SortProjection(target) => {
            is_subsort(operand.sort(), target, parents).then(|| {
                format!(
                    "projection is the identity: the operand already has sort `{}`, a subsort of `{}`; remove `k::project!`",
                    name(operand.sort(), names),
                    name(target, names),
                )
            })
        }
    }
}

fn is_subsort(
    candidate: &DefinitionSortRef,
    expected: &DefinitionSortRef,
    parents: &BTreeMap<DefinitionSortRef, BTreeSet<DefinitionSortRef>>,
) -> bool {
    let mut pending = vec![candidate];
    let mut visited = BTreeSet::new();
    while let Some(sort) = pending.pop() {
        if sort == expected {
            return true;
        }
        if visited.insert(sort) {
            pending.extend(parents.get(sort).into_iter().flatten());
        }
    }
    false
}

fn name(sort: &DefinitionSortRef, names: &BTreeMap<DefinitionSortRef, String>) -> String {
    match sort {
        DefinitionSortRef::Builtin(builtin) => builtin.k_name().to_owned(),
        _ => names.get(sort).cloned().unwrap_or_else(|| sort.to_string()),
    }
}
