//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Remove unit applications from associative collection terms before KORE emission.
#![deny(clippy::wildcard_enum_match_arm)]

use std::fmt;

use crate::definition::AttributeKey;
use crate::{
    definition::{Definition, LabelHead, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Term, TermMetadata},
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RemoveUnitError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for RemoveUnitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "unit removal produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for RemoveUnitError {}

/// Remove unit applications from the associative collection terms of rules before KORE emission.
pub fn remove_unit(definition: &Definition) -> Result<Definition, RemoveUnitError> {
    super::super::pipeline::run_standalone(
        definition,
        remove_unit_pass,
        Some(GeneratingPass::RemoveUnit),
    )
}

pub(crate) fn remove_unit_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, RemoveUnitError> {
    let resolved = input.resolved_raw().map_err(|error| RemoveUnitError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        for sentence in &mut module.local_sentences {
            // Only rules change. The kind is decided before taking a mutable sentence, which
            // copies a shared one, so every other kind stays shared.
            match &**sentence {
                Sentence::Rule { .. } => {}
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => continue,
            }
            let Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } = &**sentence
            else {
                unreachable!("the kind is decided above");
            };
            let error = |diagnostic| RemoveUnitError {
                diagnostics: vec![diagnostic],
            };
            // The terms are transformed on the shared sentence, in the order they were before;
            // a rule none of whose terms changes is left shared, uncopied.
            let transformed = [
                transform(body, productions).map_err(error)?,
                transform(requires, productions).map_err(error)?,
                transform(ensures, productions).map_err(error)?,
            ];
            if transformed.iter().all(Option::is_none) {
                continue;
            }
            let Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } = crate::definition::sentence_mut(sentence)
            else {
                unreachable!("copy-on-write keeps the kind decided above");
            };
            for (term, transformed) in [body, requires, ensures].into_iter().zip(transformed) {
                if let Some(transformed) = transformed {
                    *term = transformed;
                }
            }
        }
    }
    Ok(output)
}

// Invariant: each call rebuilds an application of a label with a `unit` attribute as a left-nested binary chain of its flattened non-unit operands (the unit itself when none remain), and otherwise recurses into the immediate subterms of `term`; the finite `term` bounds the recursion.
/// The term `term` becomes, or `None` when that is `term` itself, identical in every stored part:
/// the term is then kept as it is rather than rebuilt node by node.
fn transform(
    term: &Term,
    productions: &crate::definition::ProductionCatalog<'_>,
) -> Result<Option<Term>, Diagnostic> {
    // `None`: the node rebuilt without its annotation is `term.unannotated()` itself.
    let transformed = match term.unannotated() {
        Term::Apply { label, arguments } => {
            let ids = productions.productions_for(&LabelHead::from(label));
            let attributes = match ids {
                [id] => match productions.production(*id) {
                    Sentence::Production { attributes, .. } => Some(attributes),
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
                    | Sentence::Bubble { .. } => unreachable!(),
                },
                _ => None,
            };
            let optional_cell = attributes.is_some_and(|attributes| {
                attributes.has(AttributeKey::Cell)
                    && attributes.string(AttributeKey::Multiplicity) == Some("?")
            });
            if !optional_cell
                && let Some(unit) =
                    attributes.and_then(|attributes| attributes.string(AttributeKey::Unit))
            {
                if attributes.is_none_or(|attributes| !attributes.has(AttributeKey::Assoc)) {
                    return Err(Diagnostic::error_at(
                        DiagnosticCode::InvalidUnitAttribute,
                        format!(
                            "production for {} has a unit attribute but is not associative",
                            label.name
                        ),
                        attributes.expect("unit attribute must be present"),
                    ));
                }
                if is_rebuilt_chain(label, unit, arguments) {
                    None
                } else {
                    let mut items = Vec::new();
                    flatten(label, unit, arguments, &mut items);
                    let Some(transformed) = items.into_iter().reduce(|left, right| Term::Apply {
                        label: label.clone(),
                        arguments: vec![left, right],
                    }) else {
                        return Ok(Some(Term::apply(unit, vec![])));
                    };
                    Some(transformed)
                }
            } else {
                transform_all(arguments, productions)?.map(|arguments| Term::Apply {
                    label: label.clone(),
                    arguments,
                })
            }
        }
        Term::Rewrite { left, right } => {
            match (
                transform(left, productions)?,
                transform(right, productions)?,
            ) {
                (None, None) => None,
                (new_left, new_right) => Some(Term::Rewrite {
                    left: Box::new(new_left.unwrap_or_else(|| (**left).clone())),
                    right: Box::new(new_right.unwrap_or_else(|| (**right).clone())),
                }),
            }
        }
        Term::As { pattern, alias } => {
            match (
                transform(pattern, productions)?,
                transform(alias, productions)?,
            ) {
                (None, None) => None,
                (new_pattern, new_alias) => Some(Term::As {
                    pattern: Box::new(new_pattern.unwrap_or_else(|| (**pattern).clone())),
                    alias: Box::new(new_alias.unwrap_or_else(|| (**alias).clone())),
                }),
            }
        }
        Term::Sequence(items) => transform_all(items, productions)?.map(Term::Sequence),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => None,
        Term::Annotated { .. } => unreachable!(),
    };
    if transformed.is_none() && reannotation_keeps(term) {
        return Ok(None);
    }
    let transformed = transformed.unwrap_or_else(|| term.unannotated().clone());
    Ok(Some(match term.metadata() {
        Some(metadata) => transformed.with_metadata(metadata.clone()),
        None => transformed,
    }))
}

/// The transformed `terms`, in order, or `None` when every one of them is unchanged.
fn transform_all(
    terms: &[Term],
    productions: &crate::definition::ProductionCatalog<'_>,
) -> Result<Option<Vec<Term>>, Diagnostic> {
    let transformed = terms
        .iter()
        .map(|term| transform(term, productions))
        .collect::<Result<Vec<_>, _>>()?;
    if transformed.iter().all(Option::is_none) {
        return Ok(None);
    }
    Ok(Some(
        terms
            .iter()
            .zip(transformed)
            .map(|(term, transformed)| transformed.unwrap_or_else(|| term.clone()))
            .collect(),
    ))
}

/// Whether `term`, its node rebuilt identical without annotations and then given its outer
/// metadata by [`Term::with_metadata`] (as the transformations of this pass and of term
/// minimization reannotate a node), is `term` again. `with_metadata` gives a bare node one
/// annotation, and none for the default metadata, so this holds exactly for a bare term and for a
/// single annotation with metadata other than the default; under nested annotations, which the
/// rebuild collapses to the outer one, or a default annotation, which it drops, it does not.
pub(super) fn reannotation_keeps(term: &Term) -> bool {
    if let Term::Annotated {
        term: inner,
        metadata,
    } = term
    {
        !matches!(**inner, Term::Annotated { .. }) && *metadata != TermMetadata::default()
    } else {
        true
    }
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidUnitAttribute,
        message: message.into(),
        source: None,
        location: None,
        input_addresses: Vec::new(),
    }
}

/// How [`flatten`] reads one operand of an application of `label`.
enum Operand<'term> {
    /// A nested application of `label`, whose arguments are flattened in its place.
    Nested(&'term [Term]),
    /// The unit, dropped.
    Unit,
    /// Any other term, kept as it is.
    Item,
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn operand<'term>(label: &crate::kast::Label, unit: &str, term: &'term Term) -> Operand<'term> {
    match term.unannotated() {
        Term::Apply {
            label: nested,
            arguments,
        } if nested == label => Operand::Nested(arguments),
        Term::Apply {
            label: nested,
            arguments,
        } if nested.name == unit && arguments.is_empty() => Operand::Unit,
        _ => Operand::Item,
    }
}

// Invariant: `output` holds, in order, every non-unit operand reached so far from `terms` through nested applications of `label`; each iteration consumes one element of `terms`, and each recursive call descends into the `arguments` of one nested `label` application.
fn flatten(label: &crate::kast::Label, unit: &str, terms: &[Term], output: &mut Vec<Term>) {
    for term in terms {
        match operand(label, unit, term) {
            Operand::Nested(arguments) => flatten(label, unit, arguments, output),
            Operand::Unit => {}
            Operand::Item => output.push(term.clone()),
        }
    }
}

/// Whether the application of `label` to `arguments` is the chain [`transform`] rebuilds it as,
/// node for node: the left-nested fold of its [`flatten`]ed operands, whose inner applications
/// are bare. The fold of two or more operands is an application to exactly two arguments, the
/// last operand on the right and the fold of the others on the left; one operand, or none, is
/// not an application of `label` at all. So the application is its own rebuild exactly when it
/// has two arguments, the right one an operand kept as it is, and the left one either such an
/// operand or a bare nested application of `label` that is its own rebuild. A unit anywhere is
/// dropped, and an annotated nested application loses its annotation, so neither is.
// Invariant: each call descends into one bare nested application, so the finite term bounds it.
fn is_rebuilt_chain(label: &crate::kast::Label, unit: &str, arguments: &[Term]) -> bool {
    let [left, right] = arguments else {
        return false;
    };
    matches!(operand(label, unit, right), Operand::Item)
        && match operand(label, unit, left) {
            Operand::Item => true,
            Operand::Nested(nested) => {
                !matches!(left, Term::Annotated { .. }) && is_rebuilt_chain(label, unit, nested)
            }
            Operand::Unit => false,
        }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, sync::Arc};

    use serde_json::json;

    use super::remove_unit;
    use crate::{
        definition::{Attributes, Definition, FlatModule, Sentence},
        kast::{Label, Sort, Term},
    };

    fn apply(label: &str, arguments: Vec<Term>) -> Term {
        Term::Apply {
            label: Label::new(label),
            arguments,
        }
    }

    fn concat(left: Term, right: Term) -> Term {
        apply("_Items_", vec![left, right])
    }

    fn production(label: &str, attributes: Attributes) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new("Items"),
            items: Vec::new(),
            attributes,
        }
    }

    fn rule(term: Term) -> Sentence {
        let truth = Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(term.clone()),
                right: Box::new(term),
            },
            requires: truth.clone(),
            ensures: truth,
            attributes: Attributes::default(),
        }
    }

    /// A rule the pass would rebuild into itself is returned as the input sentence, shared, while
    /// a rule it changes is a new sentence: a unit-free left-nested chain is its own rebuild, and
    /// a right-nested chain or a chain holding the unit is not.
    #[test]
    fn a_rule_the_pass_does_not_change_stays_shared() {
        let (a, b, c) = (apply("a", vec![]), apply("b", vec![]), apply("c", vec![]));
        let collection = Attributes::new(BTreeMap::from([
            ("assoc".to_owned(), json!("")),
            ("unit".to_owned(), json!(".Items")),
        ]));
        let rules = [
            (rule(a.clone()), true),
            (rule(concat(concat(a.clone(), b.clone()), c.clone())), true),
            (rule(concat(a.clone(), concat(b.clone(), c.clone()))), false),
            (rule(concat(a.clone(), apply(".Items", vec![]))), false),
        ];
        let mut sentences = vec![
            production("_Items_", collection),
            production(".Items", Attributes::default()),
            production("a", Attributes::default()),
            production("b", Attributes::default()),
            production("c", Attributes::default()),
        ];
        sentences.extend(rules.iter().map(|(sentence, _)| sentence.clone()));
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: sentences.into_iter().map(Arc::new).collect(),
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        };
        let output = remove_unit(&definition).unwrap();
        let (before, after) = (
            &definition.modules[0].local_sentences,
            &output.modules[0].local_sentences,
        );
        for (index, (_, shared)) in rules.iter().enumerate() {
            let index = index + 5;
            assert_eq!(
                Arc::ptr_eq(&before[index], &after[index]),
                *shared,
                "{:?}",
                after[index]
            );
        }
    }
}
