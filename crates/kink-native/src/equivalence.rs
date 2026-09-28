//! A conservative compiled-output equivalence check for mutant classification.

use std::collections::BTreeMap;

use k_rust::{
    kore::{
        ast::{Attributes, Definition, Pattern, Sentence, Variable},
        parser::{ParseError, parse_definition},
    },
    names::KoreAttribute,
};

use crate::ValidatedDefinition;

/// Whether two sides have identical executable compiler output.
///
/// The comparison retains every distinct emitted sentence, its first occurrence order, its `UNIQUE_ID`,
/// and every attribute except KORE `Source`, `Location`, and rule `label`.
/// Those attributes identify written origins for diagnostics and observation
/// attribution; they do not change backend execution. Identical `UNIQUE_ID`
/// axioms are counted once, as the backend collapses equal executable copies.
/// The check also retains syntax and macro KORE, configuration variable sorts,
/// the source rewrite order, and compile options.
/// Diagnostic messages and the input-address relation describe compilation
/// provenance and do not enter execution. This is intentionally stricter than
/// semantic equivalence: equal output proves equivalence, but differing output
/// can still have equal behavior.
///
/// A parse error fails closed; callers must not classify that side as equivalent.
pub fn equivalent_compilation(
    baseline: &ValidatedDefinition,
    mutant: &ValidatedDefinition,
) -> Result<bool, ParseError> {
    let left = baseline.artifacts();
    let right = mutant.artifacts();
    if baseline.compile_options() != mutant.compile_options()
        || left.configuration_variables != right.configuration_variables
        || left.execution_rewrite_order != right.execution_rewrite_order
    {
        return Ok(false);
    }

    for (left, right) in [
        (&left.definition_kore, &right.definition_kore),
        (&left.syntax_definition_kore, &right.syntax_definition_kore),
        (&left.macros_kore, &right.macros_kore),
    ] {
        if left.trim().is_empty() || right.trim().is_empty() {
            if left.trim() != right.trim() {
                return Ok(false);
            }
            continue;
        }
        if normalized_kore(left)? != normalized_kore(right)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn normalized_kore(source: &str) -> Result<Definition, ParseError> {
    let mut definition = parse_definition(source)?;
    strip_origin_attributes(&mut definition.attributes);
    for module in &mut definition.modules {
        strip_origin_attributes(&mut module.attributes);
        for sentence in &mut module.sentences {
            let attributes = match sentence {
                Sentence::Import { attributes, .. }
                | Sentence::SortDeclaration { attributes, .. }
                | Sentence::SymbolDeclaration { attributes, .. }
                | Sentence::AliasDeclaration { attributes, .. }
                | Sentence::Axiom { attributes, .. }
                | Sentence::Claim { attributes, .. } => attributes,
            };
            strip_origin_attributes(attributes);
            if let Sentence::Axiom { attributes, .. } = sentence
                && rule_identity(attributes).is_some()
            {
                attributes.0.retain(|attribute| {
                    !matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == KoreAttribute::Label.as_str())
                });
            }
        }
        let mut seen = BTreeMap::<Vec<u8>, Vec<Sentence>>::new();
        module.sentences.retain(|sentence| {
            let Sentence::Axiom { attributes, .. } = sentence else {
                return true;
            };
            let Some(id) = rule_identity(attributes) else {
                return true;
            };
            let prior = seen.entry(id).or_default();
            if prior.contains(sentence) {
                false
            } else {
                prior.push(sentence.clone());
                true
            }
        });
    }
    Ok(definition)
}

/// The distinct axioms carrying each `UNIQUE_ID` of `source`, normalized as
/// [`equivalent_compilation`] normalizes them: `Source`, `Location` and a rule's `label`
/// stripped, identical copies collapsed (across modules too). An identity with more than one
/// distinct axiom has several executable meanings.
pub(crate) fn axioms_by_identity(
    source: &str,
) -> Result<BTreeMap<String, Vec<Sentence>>, ParseError> {
    let mut axioms = BTreeMap::<String, Vec<Sentence>>::new();
    for module in normalized_kore(source)?.modules {
        for sentence in module.sentences {
            let Sentence::Axiom { attributes, .. } = &sentence else {
                continue;
            };
            let Some(id) = rule_identity(attributes).and_then(|id| String::from_utf8(id).ok())
            else {
                continue;
            };
            let distinct = axioms.entry(id).or_default();
            if !distinct.contains(&sentence) {
                distinct.push(sentence);
            }
        }
    }
    Ok(axioms)
}

/// `axiom` with every pattern variable, free or bound, renamed to `Var'Canon'N`, where `N` is
/// the rank of the variable's name at its first occurrence in a pre-order walk of the axiom
/// (its pattern, then its attributes). Sorts, variable kinds and sort parameters are kept.
///
/// The renaming is injective on variable names, so two axioms with equal canonical forms
/// differ only by a consistent renaming of their variables: they are alpha-equivalent and
/// have the same rewrite relation. Sentences other than axioms are returned unchanged.
pub(crate) fn alpha_canonical(axiom: &Sentence) -> Sentence {
    let mut canonical = axiom.clone();
    if let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = &mut canonical
    {
        let mut names = BTreeMap::<String, String>::new();
        let mut rename = |variable: &mut Variable| {
            let next = names.len();
            variable.name = names
                .entry(variable.name.clone())
                .or_insert_with(|| format!("Var'Canon'{next}"))
                .clone();
        };
        let mut work = vec![&mut **pattern];
        work.extend(attributes.0.iter_mut().rev());
        // Invariant: `work` holds, in reverse pre-order, the roots of the subpatterns not yet
        // visited; each node is popped once, and its binder variable and its own variable are
        // renamed before any node below it.
        while let Some(node) = work.pop() {
            let children: Vec<&mut Pattern> = match node {
                Pattern::Variable(variable) => {
                    rename(variable);
                    Vec::new()
                }
                Pattern::Exists { variable, body, .. }
                | Pattern::Forall { variable, body, .. }
                | Pattern::Mu { variable, body }
                | Pattern::Nu { variable, body } => {
                    rename(variable);
                    vec![&mut **body]
                }
                Pattern::Application { arguments, .. }
                | Pattern::And { arguments, .. }
                | Pattern::Or { arguments, .. }
                | Pattern::AssociativeApplication { arguments, .. } => {
                    arguments.iter_mut().collect()
                }
                Pattern::Not { argument, .. }
                | Pattern::Next { argument, .. }
                | Pattern::Ceil { argument, .. }
                | Pattern::Floor { argument, .. } => vec![&mut **argument],
                Pattern::Implies { left, right, .. }
                | Pattern::Iff { left, right, .. }
                | Pattern::Rewrites { left, right, .. }
                | Pattern::Equals { left, right, .. }
                | Pattern::In { left, right, .. } => vec![&mut **left, &mut **right],
                Pattern::String(_)
                | Pattern::Top { .. }
                | Pattern::Bottom { .. }
                | Pattern::DomainValue { .. } => Vec::new(),
            };
            work.extend(children.into_iter().rev());
        }
    }
    canonical
}

fn rule_identity(attributes: &Attributes) -> Option<Vec<u8>> {
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments }
            if symbol.name == KoreAttribute::UniqueId.as_str() =>
        {
            let [Pattern::String(id)] = arguments.as_slice() else {
                return None;
            };
            Some(id.as_bytes().to_vec())
        }
        _ => None,
    })
}

fn strip_origin_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. }
                if symbol.name == KoreAttribute::Source.as_str()
                    || symbol.name == KoreAttribute::Location.as_str()
        )
    });
}

#[cfg(test)]
mod tests {
    use k_rust::kore::parser::parse_pattern;

    use super::*;

    fn axiom(pattern: &str) -> Sentence {
        Sentence::Axiom {
            parameters: Vec::new(),
            pattern: Box::new(parse_pattern(pattern).expect("pattern")),
            attributes: Attributes(Vec::new()),
        }
    }

    #[test]
    fn alpha_canonical_identifies_exactly_the_consistent_renamings() {
        let canonical = |pattern| alpha_canonical(&axiom(pattern));
        let pair =
            r"\rewrites{S{}}(Lblf{}(A:S{}, V:S{}), \exists{S{}}(B:S{}, Lblg{}(V:S{}, B:S{})))";
        // A consistent renaming, including the bound variable, and a swap of two names.
        let renamed =
            r"\rewrites{S{}}(Lblf{}(X:S{}, Y:S{}), \exists{S{}}(Z:S{}, Lblg{}(Y:S{}, Z:S{})))";
        let swapped =
            r"\rewrites{S{}}(Lblf{}(V:S{}, A:S{}), \exists{S{}}(B:S{}, Lblg{}(A:S{}, B:S{})))";
        assert_eq!(canonical(pair), canonical(renamed));
        assert_eq!(canonical(pair), canonical(swapped));
        // Merging two variables, or moving an occurrence, is not a renaming.
        let merged =
            r"\rewrites{S{}}(Lblf{}(A:S{}, A:S{}), \exists{S{}}(B:S{}, Lblg{}(A:S{}, B:S{})))";
        let moved =
            r"\rewrites{S{}}(Lblf{}(A:S{}, V:S{}), \exists{S{}}(B:S{}, Lblg{}(A:S{}, B:S{})))";
        assert_ne!(canonical(pair), canonical(merged));
        assert_ne!(canonical(pair), canonical(moved));
        // Sorts are kept.
        let resorted =
            r"\rewrites{S{}}(Lblf{}(A:T{}, V:S{}), \exists{S{}}(B:S{}, Lblg{}(V:S{}, B:S{})))";
        assert_ne!(canonical(pair), canonical(resorted));
    }
}
