//! The private transport of a normalized K payload through the hooked map's KItem value slot.

use std::sync::Arc;

use serde_json::json;

use super::{
    AttributeKey, Attributes, ConfigurationError, Definition, FlatModule, ProductionItem, Sentence,
    sentence_equivalent,
};
use crate::kast::{Label, Sort, Term};
use crate::names::BuiltinSort;
use crate::provenance::GeneratingPass;

pub(crate) const MODULE_NAME: &str = "K-RUST-CONFIGURATION-VALUES";
pub(crate) const BOX_LABEL: &str = "#KConfigValue";
pub(crate) const UNBOX_LABEL: &str = "#unboxKConfigValue";

/// The decoder is partial: only boxes, rather than every KItem, have a K payload.
pub(crate) fn module() -> FlatModule {
    let k = Sort::builtin(BuiltinSort::K);
    let item = Sort::builtin(BuiltinSort::KItem);
    let payload = Term::Variable {
        name: "KS".into(),
        sort: Some(k.clone()),
    };
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::builtin(BuiltinSort::Bool),
    };
    FlatModule {
        name: MODULE_NAME.into(),
        imports: vec![],
        local_sentences: vec![
            Arc::new(production(BOX_LABEL, item.clone(), k.clone(), false)),
            Arc::new(production(UNBOX_LABEL, k, item, true)),
            Arc::new(Sentence::Rule {
                body: Term::Rewrite {
                    left: Box::new(Term::apply(
                        UNBOX_LABEL,
                        vec![Term::apply(BOX_LABEL, vec![payload.clone()])],
                    )),
                    right: Box::new(payload),
                },
                requires: truth.clone(),
                ensures: truth,
                attributes: Attributes::default(),
            }),
        ],
        attributes: Attributes::default(),
    }
}

fn production(label: &str, result: Sort, argument: Sort, function: bool) -> Sentence {
    let mut attributes = Attributes::from_pairs([(AttributeKey::Symbol, json!(label))]);
    if function {
        attributes.mark(AttributeKey::Function);
    }
    Sentence::Production {
        label: Some(Label::new(label)),
        parameters: vec![],
        sort: result,
        items: vec![
            ProductionItem::Terminal(label.into()),
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: argument,
                name: None,
            },
            ProductionItem::Terminal(")".into()),
        ],
        attributes,
    }
}

/// Reuse requires the generated protocol and its compiler-written origin receipts.
/// A source declaration cannot replace this protocol's constructor or inverse equation.
pub(crate) fn reject_source_collisions(definition: &Definition) -> Result<(), ConfigurationError> {
    let expected = module();
    for module in &definition.modules {
        if module.name == MODULE_NAME {
            let generated = module.imports.is_empty()
                && module.attributes == expected.attributes
                && module.local_sentences.len() >= expected.local_sentences.len()
                && module
                    .local_sentences
                    .iter()
                    .zip(&expected.local_sentences)
                    .all(|(actual, expected)| {
                        protocol_sentence_equivalent(actual, expected)
                            && actual.attributes().origin_record().is_some_and(|record| {
                                record.pass == GeneratingPass::ConfigurationExpansion
                            })
                    })
                && module.local_sentences[expected.local_sentences.len()..]
                    .iter()
                    .all(|sentence| {
                        sentence.attributes().origin_record().is_some()
                            && !matches!(&**sentence, Sentence::Production { label: Some(label), .. }
                                if matches!(label.name.as_str(), BOX_LABEL | UNBOX_LABEL))
                    });
            if !generated {
                return Err(collision(
                    module,
                    &module.attributes,
                    format!("module `{MODULE_NAME}`"),
                ));
            }
            continue;
        }
        for sentence in &module.local_sentences {
            if let Sentence::Production {
                label: Some(label), ..
            } = &**sentence
                && matches!(label.name.as_str(), BOX_LABEL | UNBOX_LABEL)
            {
                return Err(collision(
                    module,
                    sentence.attributes(),
                    format!("label `{}`", label.name),
                ));
            }
        }
    }
    Ok(())
}

fn protocol_sentence_equivalent(actual: &Sentence, expected: &Sentence) -> bool {
    // Sentence numbering adds an identity to the equation before fresh-cell expansion reuses
    // this module. The identity names the equation; it does not change the decoder's domain.
    let mut actual = actual.clone();
    if let Sentence::Rule { attributes, .. } = &mut actual {
        attributes.remove(AttributeKey::UniqueId.as_str());
    }
    sentence_equivalent(&actual, expected) && actual.attributes() == expected.attributes()
}

fn collision(module: &FlatModule, attributes: &Attributes, name: String) -> ConfigurationError {
    ConfigurationError::Invalid {
        module: module.name.clone(),
        source: attributes.source().map(str::to_owned),
        location: attributes.location(),
        message: format!("{name} is reserved for configuration-value transport"),
    }
}
