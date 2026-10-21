//! A conservative compiled-output equivalence check for mutant classification.

use std::collections::BTreeMap;

use k_rust::{
    backend::{ExecutionRole, execution_role},
    kore::{
        ast::{Attributes, Definition, Pattern, Sentence},
        parser::{ParseError, parse_definition},
    },
    names::KoreAttribute,
};

use crate::ValidatedDefinition;

/// Whether two sides have identical executable compiler output.
///
/// The comparison retains every distinct emitted sentence, its first occurrence order, its `UNIQUE_ID`,
/// and every attribute except the origin attributes (k-rust `execution_role(..) ==
/// ExecutionRole::Origin`: `Source` and `Location` at the pinned revision; re-pin L2-1, finding
/// C-06) and the `label` of an axiom with a `UNIQUE_ID`.
/// Those attributes identify written origins for diagnostics; they do not change backend execution
/// (k-rust's `ExecutionRole` contract, which also lets a rule's label go where a `UNIQUE_ID` is its
/// id). Identical `UNIQUE_ID` axioms are counted once, as the backend collapses equal executable
/// copies; this dedup is narrower than the contract's, which drops any exact duplicate axiom.
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

/// Removes every attribute whose execution role is [`ExecutionRole::Origin`].
fn strip_origin_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. }
                if KoreAttribute::ALL.iter().any(|origin| {
                    execution_role(*origin) == ExecutionRole::Origin
                        && symbol.name == origin.as_str()
                })
        )
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kore(body: &str) -> String {
        format!("[]\nmodule M\n{body}\nendmodule []")
    }

    /// Re-pin L2-1 (finding C-06): the stripped set is k-rust's Origin role, which is exactly
    /// `Source` and `Location` at the pinned revision; two definitions that differ only there are
    /// equal, two whose axiom without a `UNIQUE_ID` differs in its label are not, and a label on
    /// an axiom with one is stripped.
    #[test]
    fn origin_attributes_are_the_execution_role_origin_and_only_they_and_ided_labels_go() {
        let origins = KoreAttribute::ALL
            .into_iter()
            .filter(|attribute| execution_role(*attribute) == ExecutionRole::Origin)
            .collect::<Vec<_>>();
        assert_eq!(origins, [KoreAttribute::Source, KoreAttribute::Location]);
        let source = KoreAttribute::Source.as_str();
        let location = KoreAttribute::Location.as_str();
        let label = KoreAttribute::Label.as_str();
        let id = KoreAttribute::UniqueId.as_str();
        let axiom = |attributes: &str| {
            kore(&format!(
                r#"axiom{{}} \rewrites{{S{{}}}}(a{{}}(), b{{}}()) [{attributes}]"#
            ))
        };
        let normal = |text: &str| normalized_kore(text).expect("KORE parses");
        let at = |file: &str, line: u32| {
            format!(r#"{source}{{}}("{file}"), {location}{{}}("({line},1,{line},9)")"#)
        };
        assert_eq!(
            normal(&axiom(&format!(r#"{id}{{}}("r"), {}"#, at("a.k", 1)))),
            normal(&axiom(&format!(r#"{id}{{}}("r"), {}"#, at("b.k", 7))))
        );
        assert_eq!(
            normal(&axiom(&format!(r#"{id}{{}}("r"), {label}{{}}("one")"#))),
            normal(&axiom(&format!(r#"{id}{{}}("r"), {label}{{}}("two")"#)))
        );
        assert_ne!(
            normal(&axiom(&format!(r#"{label}{{}}("one"), {}"#, at("a.k", 1)))),
            normal(&axiom(&format!(r#"{label}{{}}("two"), {}"#, at("a.k", 1))))
        );
    }
}
