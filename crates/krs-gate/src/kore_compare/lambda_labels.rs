//! Content-based names for the generated lambda symbols of `#fun`, `#let`, and `:=K`.
//!
//! K's `ResolveFun` and k-rust's `resolve_fun` lift each occurrence into a fresh function symbol `#lambda<hint1>_<hint2>_<n>`, numbering the occurrences that share both hints in the order the pass meets them.
//! The two frontends meet the sentences of a module in different orders, so one lambda can carry a different `<n>`, or different hints, on each route.
//! A generated lambda symbol is bound by the definition that generates it, so renaming it bijectively is alpha-equivalence.
//! The comparator names each one after its definition and its uses instead, by refining a partition of the lambda symbols until it is stable.
//! Lambdas that the refinement cannot tell apart are named in either order only when exchanging them leaves the module's sentences unchanged; otherwise the comparison fails closed.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::kore::ast::{Module, Pattern, Sentence};

use super::{CompareError, sentence_attributes_mut, sentence_patterns_mut, visit_sentence_symbols};

const LAMBDA_PREFIX: &str = "Lbl'Hash'lambda";

/// Whether `name` is the KORE symbol of a generated `#lambda<hint1>_<hint2>_<n>` label.
///
/// The label always ends in `_` and an optional decimal suffix, so its KORE name ends in `Unds'` and those digits.
fn is_generated_lambda(name: &str) -> bool {
    name.strip_prefix(LAMBDA_PREFIX).is_some_and(|rest| {
        rest.trim_end_matches(|character: char| character.is_ascii_digit())
            .ends_with("Unds'")
    })
}

/// Rename every generated lambda symbol of `module` to `#lambda<class>`, its class in the stable content partition.
///
/// Returns the number of generated lambda symbols renamed.
///
/// # Errors
///
/// Fails when two lambda symbols cannot be told apart by content and exchanging them changes the module.
pub(super) fn canonicalize_lambda_labels(
    module: &mut Module,
    route: &str,
) -> Result<usize, CompareError> {
    let renamed = lambda_classes(module, route)?
        .into_iter()
        .map(|(name, class)| (name, format!("#lambda{class}")))
        .collect::<BTreeMap<_, _>>();
    rename_module(module, &renamed);
    Ok(renamed.len())
}

/// Renumber the generated lambda symbols of `module` within each family of shared hints.
///
/// `module` is one module of a definition as a K tool wrote it, and `normalized` the same module after the comparator's per-sentence normalization, sentence for sentence.
/// The members of a family `#lambda<hint1>_<hint2>_` take the empty suffix, then `2`, `3`, ... in the order of their content classes in `normalized`, so the renumbered module does not depend on the order in which the frontend met its sentences.
/// A sentence that mentions a lambda loses its `UNIQUE'Unds'ID` attribute, a digest of its text under the old name, which the comparator ignores (k-rust N23 drops it for the same sentences).
///
/// # Errors
///
/// Fails as [`canonicalize_lambda_labels`] does.
pub(super) fn renumber_lambda_families(
    module: &mut Module,
    normalized: &Module,
) -> Result<usize, CompareError> {
    let classes = lambda_classes(normalized, &module.name)?;
    let mut families = BTreeMap::<&str, Vec<(usize, &str)>>::new();
    for (name, class) in &classes {
        let family = name.trim_end_matches(|character: char| character.is_ascii_digit());
        families.entry(family).or_default().push((*class, name));
    }
    let mut renamed = BTreeMap::new();
    for (family, mut members) in families {
        members.sort_unstable();
        for (position, (_, name)) in members.into_iter().enumerate() {
            let suffix = if position == 0 {
                String::new()
            } else {
                (position + 1).to_string()
            };
            renamed.insert(name.to_owned(), format!("{family}{suffix}"));
        }
    }
    rename_module(module, &renamed);
    for sentence in &mut module.sentences {
        if !sentence_lambdas(sentence).is_empty() {
            sentence_attributes_mut(sentence).0.retain(|attribute| {
                !matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == "UNIQUE'Unds'ID")
            });
        }
    }
    Ok(renamed.len())
}

/// The class of each generated lambda symbol of `module` in the stable content partition.
///
/// Classes are numbered from 0 in an order that does not depend on the lambda names.
fn lambda_classes(module: &Module, route: &str) -> Result<BTreeMap<String, usize>, CompareError> {
    let mut mentions = BTreeMap::<String, BTreeSet<usize>>::new();
    for (index, sentence) in module.sentences.iter().enumerate() {
        for name in sentence_lambdas(sentence) {
            mentions.entry(name).or_default().insert(index);
        }
    }
    if mentions.is_empty() {
        return Ok(BTreeMap::new());
    }
    let mut classes = refine(&module.sentences, &mentions, initial_classes(&mentions));
    // Invariant: `classes` is stable under refinement, and each lambda individualized so far was checked to be interchangeable with every other member of its class; each iteration moves one lambda into a new singleton class, so the loop runs fewer times than there are lambdas.
    while let Some((first, rest)) = first_tied_class(&classes) {
        for other in &rest {
            if !exchange_is_automorphism(&module.sentences, &mentions, &first, other) {
                return Err(CompareError::new(format!(
                    "{route} KORE generated lambda symbols {first} and {other} have the same definition and uses \
                     under refinement but are not interchangeable; the comparator cannot pair them by content"
                )));
            }
        }
        let individual = classes.values().max().map_or(0, |maximum| maximum + 1);
        classes.insert(first, individual);
        classes = refine(&module.sentences, &mentions, classes);
    }
    Ok(classes)
}

fn rename_module(module: &mut Module, renamed: &BTreeMap<String, String>) {
    if renamed.is_empty() {
        return;
    }
    for sentence in &mut module.sentences {
        rename_symbols(sentence, &|name| renamed.get(name).cloned());
    }
}

fn initial_classes(mentions: &BTreeMap<String, BTreeSet<usize>>) -> BTreeMap<String, usize> {
    mentions.keys().map(|name| (name.clone(), 0)).collect()
}

/// Refine `classes` until the number of classes stops growing.
///
/// A lambda's fingerprint is its current class and the sorted texts of the sentences that mention it, with itself written `#self` and every other lambda written by its current class.
/// Classes are numbered in the order of their fingerprints, which do not depend on the lambda names.
fn refine(
    sentences: &[Sentence],
    mentions: &BTreeMap<String, BTreeSet<usize>>,
    mut classes: BTreeMap<String, usize>,
) -> BTreeMap<String, usize> {
    let mut count = classes.values().collect::<BTreeSet<_>>().len();
    // Invariant: each round's partition refines the previous one (a fingerprint includes the current class), so `count` never decreases and is bounded by the number of lambdas; the loop stops on the first round that does not split a class.
    loop {
        let fingerprints = mentions
            .iter()
            .map(|(lambda, indices)| {
                let mut texts = indices
                    .iter()
                    .map(|&index| {
                        let mut sentence = sentences[index].clone();
                        rename_symbols(&mut sentence, &|name| {
                            if name == lambda {
                                Some("#self".to_owned())
                            } else {
                                classes.get(name).map(|class| format!("#lambda{class}"))
                            }
                        });
                        format!("{sentence:?}")
                    })
                    .collect::<Vec<_>>();
                texts.sort();
                (lambda.clone(), (classes[lambda], texts))
            })
            .collect::<BTreeMap<_, _>>();
        let ranks = fingerprints
            .values()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .enumerate()
            .map(|(rank, fingerprint)| (fingerprint.clone(), rank))
            .collect::<BTreeMap<_, _>>();
        classes = fingerprints
            .iter()
            .map(|(lambda, fingerprint)| (lambda.clone(), ranks[fingerprint]))
            .collect();
        if ranks.len() == count {
            return classes;
        }
        count = ranks.len();
    }
}

/// The first member, in name order, of the lowest-numbered class with two or more members, and its other members.
fn first_tied_class(classes: &BTreeMap<String, usize>) -> Option<(String, Vec<String>)> {
    let mut members = BTreeMap::<usize, Vec<String>>::new();
    for (name, class) in classes {
        members.entry(*class).or_default().push(name.clone());
    }
    members.into_values().find_map(|mut names| {
        (names.len() > 1).then(|| {
            let first = names.remove(0);
            (first, names)
        })
    })
}

/// Whether exchanging the names `left` and `right` maps the sentences that mention lambdas onto themselves as a multiset.
fn exchange_is_automorphism(
    sentences: &[Sentence],
    mentions: &BTreeMap<String, BTreeSet<usize>>,
    left: &str,
    right: &str,
) -> bool {
    let indices = mentions
        .values()
        .flatten()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut before = indices
        .iter()
        .map(|&index| format!("{:?}", sentences[index]))
        .collect::<Vec<_>>();
    let mut after = indices
        .iter()
        .map(|&index| {
            let mut sentence = sentences[index].clone();
            rename_symbols(&mut sentence, &|name| {
                if name == left {
                    Some(right.to_owned())
                } else if name == right {
                    Some(left.to_owned())
                } else {
                    None
                }
            });
            format!("{sentence:?}")
        })
        .collect::<Vec<_>>();
    before.sort();
    after.sort();
    before == after
}

/// The generated lambda symbols `sentence` declares or applies.
fn sentence_lambdas(sentence: &Sentence) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    if let Sentence::SymbolDeclaration { symbol, .. } = sentence
        && is_generated_lambda(&symbol.name)
    {
        names.insert(symbol.name.clone());
    }
    visit_sentence_symbols(sentence, &mut |name| {
        if is_generated_lambda(name) {
            names.insert(name.to_owned());
        }
    });
    names
}

/// Rename the declared and applied symbols of `sentence` for which `rename` returns a name.
fn rename_symbols(sentence: &mut Sentence, rename: &impl Fn(&str) -> Option<String>) {
    if let Sentence::SymbolDeclaration { symbol, .. } = sentence
        && let Some(name) = rename(&symbol.name)
    {
        symbol.name = name;
    }
    for pattern in sentence_patterns_mut(sentence) {
        rename_pattern_symbols(pattern, rename);
    }
}

fn rename_pattern_symbols(pattern: &mut Pattern, rename: &impl Fn(&str) -> Option<String>) {
    match pattern {
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            if let Some(name) = rename(&symbol.name) {
                symbol.name = name;
            }
            for argument in arguments {
                rename_pattern_symbols(argument, rename);
            }
        }
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            for argument in arguments {
                rename_pattern_symbols(argument, rename);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. }
        | Pattern::Exists { body: argument, .. }
        | Pattern::Forall { body: argument, .. }
        | Pattern::Mu { body: argument, .. }
        | Pattern::Nu { body: argument, .. } => rename_pattern_symbols(argument, rename),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            rename_pattern_symbols(left, rename);
            rename_pattern_symbols(right, rename);
        }
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recognizes_only_generated_lambda_names() {
        assert!(is_generated_lambda("Lbl'Hash'lambdaE'Unds'pair'Unds'"));
        assert!(is_generated_lambda("Lbl'Hash'lambdaE'Unds'pair'Unds'12"));
        assert!(is_generated_lambda("Lbl'Hash'lambda'UndsUnds'2"));
        assert!(!is_generated_lambda("Lbl'Hash'lambdaE"));
        assert!(!is_generated_lambda("Lbllambda'Unds'"));
        assert!(!is_generated_lambda("Lbl'Hash'lambdaE'Unds'pair'Unds'x"));
    }
}
