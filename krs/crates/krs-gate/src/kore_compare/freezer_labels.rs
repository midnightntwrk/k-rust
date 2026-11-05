//! Freezer symbols paired by the heating and cooling rules that use them.
//!
//! A context (K's `context`, a context alias, or a strict production) lowers to a heating rule
//! labelled `<label>-heat`, a cooling rule labelled `<label>-cool`, and a fresh freezer symbol
//! `#freezer<hint>_<n>` that holds the rest of the term while the hole is evaluated.
//! The two frontends choose the hint and the number differently: Java K names a context's freezer
//! after the production that holds the hole, and k-rust may give it an empty hint and a number in
//! the order it meets the contexts. Both name the heating and cooling rules after the context.
//! A freezer is bound by the definition that generates it, so renaming it bijectively is
//! alpha-equivalence: the comparator names each native freezer after the reference freezer that
//! the rules with the same labels use. Everything else about the freezer, its declaration, its
//! constructor axioms and the rules themselves, is still compared.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::kore::ast::{Module, Pattern, Sentence};

use super::{CompareError, ComparePolicy, lambda_labels::rename_symbols, visit_sentence_symbols};

const FREEZER_PREFIX: &str = "Lbl'Hash'freezer";

/// The label of a heating or cooling rule without its `-heat` or `-cool` suffix, with a native
/// label first mapped as `policy` maps it.
fn context_label(sentence: &Sentence, policy: Option<&ComparePolicy>) -> Option<String> {
    let Sentence::Axiom { attributes, .. } = sentence else {
        return None;
    };
    attributes.0.iter().find_map(|attribute| {
        let Pattern::Application { symbol, arguments } = attribute else {
            return None;
        };
        let [Pattern::String(label)] = arguments.as_slice() else {
            return None;
        };
        if symbol.name != "label" {
            return None;
        }
        let label = label.as_utf8().ok()?;
        let label = policy
            .and_then(|policy| policy.label_map.get(label))
            .map_or(label, String::as_str);
        label
            .strip_suffix("-heat")
            .or_else(|| label.strip_suffix("-cool"))
            .map(str::to_owned)
    })
}

/// The freezer each context label's rules use, for every label whose heating and cooling rules
/// use exactly one freezer that no rule of another label uses.
fn freezers_by_label(module: &Module, policy: Option<&ComparePolicy>) -> BTreeMap<String, String> {
    let mut used = BTreeMap::<String, BTreeSet<String>>::new();
    let mut labels_of = BTreeMap::<String, BTreeSet<String>>::new();
    for sentence in &module.sentences {
        let Some(label) = context_label(sentence, policy) else {
            continue;
        };
        let freezers = used.entry(label.clone()).or_default();
        visit_sentence_symbols(sentence, &mut |name| {
            if name.starts_with(FREEZER_PREFIX) {
                freezers.insert(name.to_owned());
            }
        });
        for freezer in freezers.iter() {
            labels_of
                .entry(freezer.clone())
                .or_default()
                .insert(label.clone());
        }
    }
    used.into_iter()
        .filter_map(|(label, freezers)| {
            let [freezer] = Vec::from_iter(freezers).try_into().ok()?;
            (labels_of[&freezer].len() == 1).then_some((label, freezer))
        })
        .collect()
}

/// Rename each native freezer to the reference freezer of the context with the same label, where
/// the two names differ.
///
/// Returns the number of native freezer symbols renamed.
///
/// # Errors
///
/// Fails when a new name is already a native symbol, so the renaming would not be a bijection.
pub(super) fn pair_freezer_labels(
    reference: &Module,
    actual: &mut Module,
    policy: &ComparePolicy,
) -> Result<usize, CompareError> {
    let reference_freezers = freezers_by_label(reference, None);
    let actual_freezers = freezers_by_label(actual, Some(policy));
    let renamed = actual_freezers
        .iter()
        .filter_map(|(label, native)| {
            let reference = reference_freezers.get(label)?;
            (reference != native).then(|| (native.clone(), reference.clone()))
        })
        .collect::<BTreeMap<_, _>>();
    if renamed.is_empty() {
        return Ok(0);
    }
    let mut declared = BTreeSet::new();
    for sentence in &actual.sentences {
        if let Sentence::SymbolDeclaration { symbol, .. } = sentence {
            declared.insert(symbol.name.clone());
        }
        visit_sentence_symbols(sentence, &mut |name| {
            declared.insert(name.to_owned());
        });
    }
    for (native, reference) in &renamed {
        if declared.contains(reference) && !renamed.contains_key(reference) {
            return Err(CompareError::new(format!(
                "native KORE freezer {native} pairs with the reference freezer {reference} by its \
                 heating and cooling labels, and the native definition already has a symbol {reference}"
            )));
        }
    }
    for sentence in &mut actual.sentences {
        rename_symbols(sentence, &|name| renamed.get(name).cloned());
    }
    Ok(renamed.len())
}
