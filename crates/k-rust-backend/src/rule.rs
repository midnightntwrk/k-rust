//! Recognition of the axiom shapes emitted by the K frontend.

use std::collections::{BTreeMap, BTreeSet};

use k_rust_kore::kore::ast as kore;

use crate::term::Name;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstraintKind {
    Concrete,
    Symbolic,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Concreteness {
    Unconstrained,
    All(ConstraintKind),
    Some(BTreeMap<(Name, Name), ConstraintKind>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleAttributes {
    pub priority: u8,
    pub label: Option<String>,
    pub unique_id: String,
    pub simplification: bool,
    pub preserves_definedness: bool,
    pub concreteness: Concreteness,
    pub smt_lemma: bool,
    pub executable: bool,
    pub source: Option<String>,
    pub location: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArgumentBinder {
    pub variable: kore::Variable,
    pub pattern: kore::Pattern,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClassifiedAxiom {
    Rewrite {
        module: Name,
        sort_parameters: Vec<Name>,
        lhs: kore::Pattern,
        rhs: kore::Pattern,
        existentials: Vec<kore::Variable>,
        attributes: RuleAttributes,
    },
    Function {
        module: Name,
        sort_parameters: Vec<Name>,
        requires: kore::Pattern,
        binders: Vec<ArgumentBinder>,
        lhs: kore::Pattern,
        rhs: kore::Pattern,
        attributes: RuleAttributes,
    },
    Simplification {
        module: Name,
        sort_parameters: Vec<Name>,
        requires: kore::Pattern,
        lhs: kore::Pattern,
        rhs: kore::Pattern,
        attributes: RuleAttributes,
    },
    Ceil {
        module: Name,
        sort_parameters: Vec<Name>,
        lhs: kore::Pattern,
        rhs: kore::Pattern,
        attributes: RuleAttributes,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AxiomError {
    MalformedRewrite,
    UnsupportedAliasRewrite(String),
    MalformedEquation,
    MalformedArgumentBinder,
    Unexpected,
    ConflictingPriorities(Vec<&'static str>),
    InvalidPriority(String),
    InvalidConcreteness(String),
    ConcretenessOverlap(String),
    MalformedAttribute(String),
}

pub fn classify_axiom(
    module: Name,
    sort_parameters: Vec<Name>,
    pattern: &kore::Pattern,
    syntax_attributes: &kore::Attributes,
) -> Result<Option<ClassifiedAxiom>, AxiomError> {
    let attributes = RuleAttributes::parse(syntax_attributes)?;
    match pattern {
        kore::Pattern::Rewrites { left, right, .. } => {
            if !matches!(left.as_ref(), kore::Pattern::And { .. }) {
                if let kore::Pattern::Application { symbol, .. } = left.as_ref() {
                    return Err(AxiomError::UnsupportedAliasRewrite(symbol.name.clone()));
                }
                return Err(AxiomError::MalformedRewrite);
            }
            let (rhs, existentials) = extract_existentials((**right).clone());
            Ok(Some(ClassifiedAxiom::Rewrite {
                module,
                sort_parameters,
                lhs: (**left).clone(),
                rhs,
                existentials,
                attributes,
            }))
        }
        kore::Pattern::Implies { left, right, .. } => {
            let kore::Pattern::Equals {
                left: equation_left,
                right: equation_right,
                ..
            } = right.as_ref()
            else {
                return if is_ignored_constructor_axiom(pattern, syntax_attributes) {
                    Ok(None)
                } else {
                    Err(AxiomError::Unexpected)
                };
            };
            if let kore::Pattern::Ceil { argument, .. } = equation_left.as_ref() {
                return Ok(Some(ClassifiedAxiom::Ceil {
                    module,
                    sort_parameters,
                    lhs: (**argument).clone(),
                    rhs: (**equation_right).clone(),
                    attributes,
                }));
            }
            if !matches!(equation_right.as_ref(), kore::Pattern::And { .. }) {
                return Err(AxiomError::MalformedEquation);
            }
            if attributes.simplification {
                return match equation_left.as_ref() {
                    kore::Pattern::Application { .. } => {
                        Ok(Some(ClassifiedAxiom::Simplification {
                            module,
                            sort_parameters,
                            requires: (**left).clone(),
                            lhs: (**equation_left).clone(),
                            rhs: (**equation_right).clone(),
                            attributes,
                        }))
                    }
                    _ => Ok(None),
                };
            }
            let kore::Pattern::Application { arguments, .. } = equation_left.as_ref() else {
                return Err(AxiomError::MalformedEquation);
            };
            if !arguments
                .iter()
                .all(|argument| matches!(argument, kore::Pattern::Variable(_)))
            {
                return Err(AxiomError::MalformedEquation);
            }
            let (requires, binders) = function_conditions(left, arguments.is_empty())?;
            Ok(Some(ClassifiedAxiom::Function {
                module,
                sort_parameters,
                requires,
                binders,
                lhs: (**equation_left).clone(),
                rhs: (**equation_right).clone(),
                attributes,
            }))
        }
        kore::Pattern::Exists { variable, body, .. }
            if matches!(body.as_ref(), kore::Pattern::Equals { left, .. }
                if matches!(left.as_ref(), kore::Pattern::Variable(found) if found == variable))
                && (has_attribute(syntax_attributes, "functional")
                    || has_attribute(syntax_attributes, "total")) =>
        {
            Ok(None)
        }
        kore::Pattern::Exists { .. } if has_attribute(syntax_attributes, "subsort") => Ok(None),
        kore::Pattern::Or { .. } | kore::Pattern::Bottom { .. }
            if has_attribute(syntax_attributes, "constructor") =>
        {
            Ok(None)
        }
        kore::Pattern::Not { .. } if has_attribute(syntax_attributes, "constructor") => Ok(None),
        kore::Pattern::Equals { left, right, .. }
            if [
                "assoc",
                "comm",
                "idem",
                "unit",
                "symbol-overload",
                "overload",
            ]
            .iter()
            .any(|name| has_attribute(syntax_attributes, name))
                || (has_attribute(syntax_attributes, "simplification")
                    && is_injection(left)
                    && is_injection(right)) =>
        {
            Ok(None)
        }
        _ => Err(AxiomError::Unexpected),
    }
}

impl RuleAttributes {
    pub fn parse(attributes: &kore::Attributes) -> Result<Self, AxiomError> {
        let priority = attribute_string(attributes, "priority")?;
        let simplification_priority = attribute_string_or_empty(attributes, "simplification")?;
        let owise = has_attribute(attributes, "owise");
        let present = [
            priority.as_ref().map(|_| "priority"),
            simplification_priority.as_ref().map(|_| "simplification"),
            owise.then_some("owise"),
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
        if present.len() > 1 {
            return Err(AxiomError::ConflictingPriorities(present));
        }
        let priority = if owise {
            u8::MAX
        } else {
            priority
                .or(simplification_priority)
                .map(|value| {
                    if value.is_empty() {
                        Ok(50)
                    } else {
                        value
                            .parse::<u8>()
                            .map_err(|_| AxiomError::InvalidPriority(value))
                    }
                })
                .transpose()?
                .unwrap_or(50)
        };
        let label = attribute_string(attributes, "label")?;
        let unique_id = attribute_string(attributes, "UNIQUE'Unds'ID")?
            .or_else(|| label.clone())
            .unwrap_or_else(|| "UNKNOWN".into());
        Ok(Self {
            priority,
            label,
            unique_id,
            simplification: has_attribute(attributes, "simplification"),
            preserves_definedness: has_attribute(attributes, "preserves-definedness"),
            concreteness: parse_concreteness(attributes)?,
            smt_lemma: has_attribute(attributes, "smt-lemma"),
            executable: !has_attribute(attributes, "non-executable"),
            source: attribute_string(
                attributes,
                "org'Stop'kframework'Stop'attributes'Stop'Source",
            )?,
            location: attribute_string(
                attributes,
                "org'Stop'kframework'Stop'attributes'Stop'Location",
            )?,
        })
    }
}

fn function_conditions(
    condition: &kore::Pattern,
    nullary: bool,
) -> Result<(kore::Pattern, Vec<ArgumentBinder>), AxiomError> {
    let kore::Pattern::And { arguments, .. } = condition else {
        return Err(AxiomError::MalformedEquation);
    };
    let [first, second] = arguments.as_slice() else {
        return Err(AxiomError::MalformedEquation);
    };
    if nullary && matches!(second, kore::Pattern::Top { .. }) {
        return Ok((first.clone(), Vec::new()));
    }
    if let kore::Pattern::And { arguments, .. } = second
        && arguments
            .first()
            .is_some_and(|pattern| matches!(pattern, kore::Pattern::In { .. }))
    {
        return Ok((first.clone(), extract_binders(second)?));
    }
    if let kore::Pattern::And { arguments, .. } = second
        && let [requires, binders] = arguments.as_slice()
    {
        return Ok((requires.clone(), extract_binders(binders)?));
    }
    Err(AxiomError::MalformedEquation)
}

fn extract_binders(pattern: &kore::Pattern) -> Result<Vec<ArgumentBinder>, AxiomError> {
    match pattern {
        kore::Pattern::Top { .. } => Ok(Vec::new()),
        kore::Pattern::In { left, right, .. } => {
            let kore::Pattern::Variable(variable) = left.as_ref() else {
                return Err(AxiomError::MalformedArgumentBinder);
            };
            Ok(vec![ArgumentBinder {
                variable: variable.clone(),
                pattern: (**right).clone(),
            }])
        }
        kore::Pattern::And { arguments, .. } => {
            let [first, rest] = arguments.as_slice() else {
                return Err(AxiomError::MalformedArgumentBinder);
            };
            let kore::Pattern::In { left, right, .. } = first else {
                return Err(AxiomError::MalformedArgumentBinder);
            };
            let kore::Pattern::Variable(variable) = left.as_ref() else {
                return Err(AxiomError::MalformedArgumentBinder);
            };
            let mut result = vec![ArgumentBinder {
                variable: variable.clone(),
                pattern: (**right).clone(),
            }];
            result.extend(extract_binders(rest)?);
            Ok(result)
        }
        _ => Err(AxiomError::MalformedArgumentBinder),
    }
}

fn extract_existentials(mut pattern: kore::Pattern) -> (kore::Pattern, Vec<kore::Variable>) {
    let mut variables = Vec::new();
    while let kore::Pattern::Exists { variable, body, .. } = pattern {
        variables.push(variable);
        pattern = *body;
    }
    (pattern, variables)
}

fn parse_concreteness(attributes: &kore::Attributes) -> Result<Concreteness, AxiomError> {
    let concrete = attribute_strings(attributes, "concrete")?;
    let symbolic = attribute_strings(attributes, "symbolic")?;
    match (concrete, symbolic) {
        (None, None) => Ok(Concreteness::Unconstrained),
        (Some(concrete), Some(_)) if concrete.is_empty() => {
            Err(AxiomError::ConcretenessOverlap("all concrete".into()))
        }
        (Some(_), Some(symbolic)) if symbolic.is_empty() => {
            Err(AxiomError::ConcretenessOverlap("all symbolic".into()))
        }
        (Some(concrete), None) if concrete.is_empty() => {
            Ok(Concreteness::All(ConstraintKind::Concrete))
        }
        (None, Some(symbolic)) if symbolic.is_empty() => {
            Ok(Concreteness::All(ConstraintKind::Symbolic))
        }
        (concrete, symbolic) => {
            let concrete = concrete.unwrap_or_default();
            let symbolic = symbolic.unwrap_or_default();
            let concrete = parse_constrained_variables(concrete, ConstraintKind::Concrete)?;
            let symbolic = parse_constrained_variables(symbolic, ConstraintKind::Symbolic)?;
            let overlap = concrete
                .keys()
                .collect::<BTreeSet<_>>()
                .intersection(&symbolic.keys().collect())
                .next()
                .cloned();
            if let Some((name, sort)) = overlap {
                return Err(AxiomError::ConcretenessOverlap(format!("{name}:{sort}")));
            }
            Ok(Concreteness::Some(
                concrete.into_iter().chain(symbolic).collect(),
            ))
        }
    }
}

fn parse_constrained_variables(
    variables: Vec<String>,
    kind: ConstraintKind,
) -> Result<BTreeMap<(Name, Name), ConstraintKind>, AxiomError> {
    variables
        .into_iter()
        .map(|variable| {
            let Some((name, sort)) = variable.split_once(':') else {
                return Err(AxiomError::InvalidConcreteness(variable));
            };
            Ok(((Name::from(name), Name::from(sort)), kind))
        })
        .collect()
}

fn is_ignored_constructor_axiom(pattern: &kore::Pattern, attributes: &kore::Attributes) -> bool {
    has_attribute(attributes, "constructor") && matches!(pattern, kore::Pattern::Implies { .. })
}

fn is_injection(pattern: &kore::Pattern) -> bool {
    matches!(pattern, kore::Pattern::Application { symbol, .. } if symbol.name == "inj")
}

fn has_attribute(attributes: &kore::Attributes, name: &str) -> bool {
    attribute_application(attributes, name).is_some()
}

fn attribute_application<'a>(
    attributes: &'a kore::Attributes,
    name: &str,
) -> Option<&'a Vec<kore::Pattern>> {
    attributes.0.iter().find_map(|attribute| match attribute {
        kore::Pattern::Application { symbol, arguments } if symbol.name == name => Some(arguments),
        _ => None,
    })
}

fn attribute_string(
    attributes: &kore::Attributes,
    name: &str,
) -> Result<Option<String>, AxiomError> {
    let Some(arguments) = attribute_application(attributes, name) else {
        return Ok(None);
    };
    match arguments.as_slice() {
        [kore::Pattern::String(value)] => Ok(Some(value.clone())),
        _ => Err(AxiomError::MalformedAttribute(name.into())),
    }
}

fn attribute_string_or_empty(
    attributes: &kore::Attributes,
    name: &str,
) -> Result<Option<String>, AxiomError> {
    let Some(arguments) = attribute_application(attributes, name) else {
        return Ok(None);
    };
    match arguments.as_slice() {
        [] => Ok(Some(String::new())),
        [kore::Pattern::String(value)] => Ok(Some(value.clone())),
        _ => Err(AxiomError::MalformedAttribute(name.into())),
    }
}

fn attribute_strings(
    attributes: &kore::Attributes,
    name: &str,
) -> Result<Option<Vec<String>>, AxiomError> {
    let Some(arguments) = attribute_application(attributes, name) else {
        return Ok(None);
    };
    arguments
        .iter()
        .map(|argument| match argument {
            kore::Pattern::String(value) => Ok(value.clone()),
            _ => Err(AxiomError::MalformedAttribute(name.into())),
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Some)
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::parse_sentence;

    use super::*;

    fn classify(source: &str) -> Result<Option<ClassifiedAxiom>, AxiomError> {
        let sentence = parse_sentence(source).expect("axiom should parse");
        let kore::Sentence::Axiom {
            parameters,
            pattern,
            attributes,
        } = sentence
        else {
            panic!("expected axiom");
        };
        classify_axiom(
            "MAIN".into(),
            parameters.into_iter().map(Into::into).collect(),
            &pattern,
            &attributes,
        )
    }

    #[test]
    fn classifies_rewrites_and_extracts_rhs_existentials() {
        let classified = classify(
            r#"axiom{} \rewrites{S{}}(
                \and{S{}}(lhs{}(X:S{}), \top{S{}}()),
                \exists{S{}}(Y:S{}, rhs{}(Y:S{}))
            ) [label{}("step"), priority{}("42")]"#,
        )
        .expect("axiom should classify")
        .expect("axiom should be executable");

        let ClassifiedAxiom::Rewrite {
            existentials,
            attributes,
            ..
        } = classified
        else {
            panic!("expected rewrite");
        };
        assert_eq!(existentials.len(), 1);
        assert_eq!(existentials[0].name, "Y");
        assert_eq!(attributes.priority, 42);
        assert_eq!(attributes.label.as_deref(), Some("step"));
        assert_eq!(attributes.unique_id, "step");
    }

    #[test]
    fn classifies_function_argument_binders() {
        let classified = classify(
            r#"axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(
                        \in{S{}, R}(X:S{}, arg{}()),
                        \top{R}()
                    )
                ),
                \equals{S{}, R}(
                    f{}(X:S{}),
                    \and{S{}}(result{}(), \top{S{}}())
                )
            ) [concrete{}("X:S")]"#,
        )
        .expect("axiom should classify")
        .expect("axiom should be executable");

        let ClassifiedAxiom::Function {
            binders,
            attributes,
            ..
        } = classified
        else {
            panic!("expected function equation");
        };
        assert_eq!(binders.len(), 1);
        assert_eq!(binders[0].variable.name, "X");
        assert_eq!(
            attributes.concreteness,
            Concreteness::Some(BTreeMap::from([(
                (Name::from("X"), Name::from("S")),
                ConstraintKind::Concrete,
            )]))
        );
    }

    #[test]
    fn classifies_simplifications_with_the_reference_default_priority() {
        let classified = classify(
            r#"axiom{R} \implies{R}(
                \top{R}(),
                \equals{S{}, R}(f{}(X:S{}), \and{S{}}(X:S{}, \top{S{}}()))
            ) [simplification{}()]"#,
        )
        .expect("axiom should classify")
        .expect("axiom should be executable");

        let ClassifiedAxiom::Simplification { attributes, .. } = classified else {
            panic!("expected simplification");
        };
        assert!(attributes.simplification);
        assert_eq!(attributes.priority, 50);
    }

    #[test]
    fn ignores_generated_constructor_axioms() {
        assert_eq!(
            classify(r#"axiom{} \or{S{}}(constructor{}(), \bottom{S{}}()) [constructor{}()]"#),
            Ok(None)
        );
    }

    #[test]
    fn rejects_conflicting_priority_attributes() {
        assert_eq!(
            classify(
                r#"axiom{} \rewrites{S{}}(
                    \and{S{}}(lhs{}(), \top{S{}}()), rhs{}()
                ) [priority{}("10"), owise{}()]"#
            ),
            Err(AxiomError::ConflictingPriorities(vec!["priority", "owise"]))
        );
    }
}
