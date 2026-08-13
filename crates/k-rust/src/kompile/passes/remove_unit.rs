//! Remove unit applications from associative collection terms before KORE emission.

use crate::{
    definition::{Definition, LabelHead, ResolvedDefinition, Sentence},
    kast::Term,
};

/// Apply Java's final `RemoveUnit` transformation to rules.
pub fn remove_unit(definition: &Definition) -> Result<Definition, String> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| error.to_string())?;
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        for sentence in &mut module.local_sentences {
            let Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } = sentence
            else {
                continue;
            };
            *body = transform(body, &productions)?;
            *requires = transform(requires, &productions)?;
            *ensures = transform(ensures, &productions)?;
        }
    }
    Ok(output)
}

fn transform(
    term: &Term,
    productions: &crate::definition::ProductionCatalog<'_>,
) -> Result<Term, String> {
    let metadata = term.metadata().cloned();
    let transformed = match term.unannotated() {
        Term::Apply { label, arguments } => {
            let ids = productions.productions_for(&LabelHead::from(label));
            let attributes = match ids {
                [id] => match productions.production(*id) {
                    Sentence::Production { attributes, .. } => Some(attributes),
                    _ => unreachable!(),
                },
                _ => None,
            };
            let optional_cell = attributes.is_some_and(|attributes| {
                attributes.get("cell").is_some() && attributes.get_str("multiplicity") == Some("?")
            });
            if !optional_cell
                && let Some(unit) = attributes.and_then(|attributes| attributes.get_str("unit"))
            {
                if attributes.is_none_or(|attributes| attributes.get("assoc").is_none()) {
                    return Err(format!(
                        "production for {} has a unit attribute but is not associative",
                        label.name
                    ));
                }
                let mut items = Vec::new();
                flatten(label, unit, arguments, &mut items);
                items
                    .into_iter()
                    .reduce(|left, right| Term::Apply {
                        label: label.clone(),
                        arguments: vec![left, right],
                    })
                    .unwrap_or_else(|| Term::apply(unit, vec![]))
            } else {
                Term::Apply {
                    label: label.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| transform(argument, productions))
                        .collect::<Result<Vec<_>, _>>()?,
                }
            }
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform(left, productions)?),
            right: Box::new(transform(right, productions)?),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(transform(pattern, productions)?),
            alias: Box::new(transform(alias, productions)?),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| transform(item, productions))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
            leaf.clone()
        }
        Term::Annotated { .. } => unreachable!(),
    };
    Ok(metadata.map_or(transformed.clone(), |metadata| {
        transformed.with_metadata(metadata)
    }))
}

fn flatten(label: &crate::kast::Label, unit: &str, terms: &[Term], output: &mut Vec<Term>) {
    for term in terms {
        match term.unannotated() {
            Term::Apply {
                label: nested,
                arguments,
            } if nested == label => flatten(label, unit, arguments, output),
            Term::Apply {
                label: nested,
                arguments,
            } if nested.name == unit && arguments.is_empty() => {}
            _ => output.push(term.clone()),
        }
    }
}
