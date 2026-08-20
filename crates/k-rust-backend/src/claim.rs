//! Internalization of modal reachability claims.

use std::collections::BTreeSet;

use k_rust_kore::kore::ast as kore;

use crate::{
    definition::{BackendDefinition, DefinitionError, PendingAxiom},
    rewrite::Pattern,
    rule::{RuleAttributes, internalize_rule_pattern},
    term::Variable,
};

const ONE_PATH_MODALITY: &str = "weakExistsFinally";
const ALL_PATH_MODALITY: &str = "weakAlwaysFinally";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReachabilityMode {
    OnePath,
    AllPath,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClaimAttributes {
    pub label: Option<String>,
    pub unique_id: String,
    pub trusted: bool,
    pub source: Option<String>,
    pub location: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReachabilityClaim {
    pub lhs: Pattern,
    pub rhs: Vec<Pattern>,
    pub existentials: BTreeSet<Variable>,
    pub mode: ReachabilityMode,
    pub attributes: ClaimAttributes,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClaimError {
    MalformedModality {
        modality: String,
        argument_count: usize,
    },
    MissingRightHandSide,
}

pub(crate) fn internalize_reachability_claim(
    definition: &BackendDefinition,
    claim: &PendingAxiom,
) -> Result<Option<ReachabilityClaim>, DefinitionError> {
    let kore::Pattern::Implies { left, right, .. } = &claim.pattern else {
        return Ok(None);
    };
    let kore::Pattern::Application { symbol, arguments } = right.as_ref() else {
        return Ok(None);
    };
    let mode = match symbol.name.as_str() {
        ONE_PATH_MODALITY => ReachabilityMode::OnePath,
        ALL_PATH_MODALITY => ReachabilityMode::AllPath,
        _ => return Ok(None),
    };
    let [right] = arguments.as_slice() else {
        return Err(DefinitionError::Claim(ClaimError::MalformedModality {
            modality: symbol.name.clone(),
            argument_count: arguments.len(),
        }));
    };

    let (right, existential_syntax) = extract_existentials(right);
    let existentials = existential_syntax
        .into_iter()
        .map(|variable| {
            Ok(Variable::new(
                variable.name.as_str(),
                definition.internalize_syntax_sort(&variable.sort, &claim.parameters)?,
            ))
        })
        .collect::<Result<BTreeSet<_>, DefinitionError>>()?;
    let rhs = distribute_term_or(right)
        .into_iter()
        .map(|branch| {
            let (term, constraints) =
                internalize_rule_pattern(definition, &branch, &claim.parameters)?;
            Ok(Pattern { term, constraints })
        })
        .collect::<Result<Vec<_>, DefinitionError>>()?;
    if rhs.is_empty() {
        return Err(DefinitionError::Claim(ClaimError::MissingRightHandSide));
    }
    let (lhs, constraints) = internalize_rule_pattern(definition, left, &claim.parameters)?;
    let parsed_attributes =
        RuleAttributes::parse(&claim.attributes).map_err(DefinitionError::Axiom)?;

    Ok(Some(ReachabilityClaim {
        lhs: Pattern {
            term: lhs,
            constraints,
        },
        rhs,
        existentials,
        mode,
        attributes: ClaimAttributes {
            label: parsed_attributes.label,
            unique_id: parsed_attributes.unique_id,
            trusted: has_attribute(&claim.attributes, "trusted"),
            source: parsed_attributes.source,
            location: parsed_attributes.location,
        },
    }))
}

fn extract_existentials(mut pattern: &kore::Pattern) -> (&kore::Pattern, Vec<&kore::Variable>) {
    let mut variables = Vec::new();
    while let kore::Pattern::Exists { variable, body, .. } = pattern {
        variables.push(variable);
        pattern = body;
    }
    (pattern, variables)
}

/// Distribute term-level disjunction through term constructors and conjunction while leaving
/// predicate-only disjunctions intact as constraints.
fn distribute_term_or(pattern: &kore::Pattern) -> Vec<kore::Pattern> {
    distribute_term_or_with_context(pattern, false)
}

fn distribute_term_or_with_context(
    pattern: &kore::Pattern,
    inside_term: bool,
) -> Vec<kore::Pattern> {
    match pattern {
        kore::Pattern::Or { arguments, .. }
            if inside_term || arguments.iter().any(contains_term_component) =>
        {
            arguments
                .iter()
                .flat_map(|argument| distribute_term_or_with_context(argument, true))
                .collect()
        }
        kore::Pattern::And { sort, arguments } => distribute_arguments(arguments, inside_term)
            .into_iter()
            .map(|arguments| kore::Pattern::And {
                sort: sort.clone(),
                arguments,
            })
            .collect(),
        kore::Pattern::Application { symbol, arguments } => distribute_arguments(arguments, true)
            .into_iter()
            .map(|arguments| kore::Pattern::Application {
                symbol: symbol.clone(),
                arguments,
            })
            .collect(),
        kore::Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => distribute_arguments(arguments, true)
            .into_iter()
            .map(|arguments| kore::Pattern::AssociativeApplication {
                associativity: *associativity,
                symbol: symbol.clone(),
                arguments,
            })
            .collect(),
        _ => vec![pattern.clone()],
    }
}

fn distribute_arguments(arguments: &[kore::Pattern], inside_term: bool) -> Vec<Vec<kore::Pattern>> {
    let mut combinations = vec![Vec::new()];
    for argument in arguments {
        let alternatives = distribute_term_or_with_context(argument, inside_term);
        combinations = combinations
            .into_iter()
            .flat_map(|prefix| {
                alternatives.iter().cloned().map(move |alternative| {
                    let mut combined = prefix.clone();
                    combined.push(alternative);
                    combined
                })
            })
            .collect();
    }
    combinations
}

fn contains_term_component(pattern: &kore::Pattern) -> bool {
    match pattern {
        kore::Pattern::String(_)
        | kore::Pattern::Variable(_)
        | kore::Pattern::Application { .. }
        | kore::Pattern::DomainValue { .. }
        | kore::Pattern::AssociativeApplication { .. } => true,
        kore::Pattern::And { arguments, .. } => arguments.iter().any(contains_term_component),
        kore::Pattern::Exists { body, .. } | kore::Pattern::Forall { body, .. } => {
            contains_term_component(body)
        }
        kore::Pattern::Top { .. }
        | kore::Pattern::Bottom { .. }
        | kore::Pattern::Or { .. }
        | kore::Pattern::Not { .. }
        | kore::Pattern::Next { .. }
        | kore::Pattern::Implies { .. }
        | kore::Pattern::Iff { .. }
        | kore::Pattern::Rewrites { .. }
        | kore::Pattern::Mu { .. }
        | kore::Pattern::Nu { .. }
        | kore::Pattern::Ceil { .. }
        | kore::Pattern::Floor { .. }
        | kore::Pattern::Equals { .. }
        | kore::Pattern::In { .. } => false,
    }
}

fn has_attribute(attributes: &kore::Attributes, name: &str) -> bool {
    attributes.0.iter().any(|attribute| {
        matches!(attribute, kore::Pattern::Application { symbol, .. } if symbol.name == name)
    })
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::parse_definition;

    use super::*;

    fn definition(claims: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                symbol c{{}}(SortS{{}}) : SortS{{}} [constructor{{}}()]
                {claims}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    #[test]
    fn internalizes_one_and_all_path_claims_but_not_equation_claims() {
        let definition = definition(
            r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(\top{SortS{}}(), c{}(X:SortS{})),
                weakExistsFinally{SortS{}}(
                    \exists{SortS{}}(
                        Y:SortS{},
                        \and{SortS{}}(c{}(Y:SortS{}), \top{SortS{}}())
                    )
                )
            ) [label{}("one"), one-path{}(), trusted{}()]
            claim{} \implies{SortS{}}(
                \and{SortS{}}(\top{SortS{}}(), c{}(X:SortS{})),
                weakAlwaysFinally{SortS{}}(
                    \and{SortS{}}(c{}(X:SortS{}), \top{SortS{}}())
                )
            ) [label{}("all"), all-path{}()]
            claim{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(c{}(X:SortS{}), c{}(X:SortS{}))
            ) [label{}("equation")]
            "#,
        );

        assert_eq!(definition.claims.len(), 3);
        assert_eq!(definition.reachability_claims.len(), 2);
        assert_eq!(
            definition.reachability_claims[0].mode,
            ReachabilityMode::OnePath
        );
        assert_eq!(
            definition.reachability_claims[1].mode,
            ReachabilityMode::AllPath
        );
        assert!(definition.reachability_claims[0].attributes.trusted);
        assert_eq!(
            definition.reachability_claims[0]
                .existentials
                .iter()
                .map(|variable| variable.name.as_ref())
                .collect::<Vec<_>>(),
            vec!["Y"]
        );
    }

    #[test]
    fn distributes_term_disjunctions_into_rhs_branches() {
        let definition = definition(
            r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(\top{SortS{}}(), c{}(X:SortS{})),
                weakExistsFinally{SortS{}}(
                    \or{SortS{}}(
                        c{}(X:SortS{}),
                        c{}(\dv{SortS{}}("other"))
                    )
                )
            ) []
            "#,
        );

        assert_eq!(definition.reachability_claims[0].rhs.len(), 2);
    }

    #[test]
    fn distributes_disjunctions_nested_inside_term_contexts() {
        let definition = definition(
            r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(\top{SortS{}}(), c{}(X:SortS{})),
                weakExistsFinally{SortS{}}(
                    c{}(
                        \or{SortS{}}(
                            X:SortS{},
                            \dv{SortS{}}("other")
                        )
                    )
                )
            ) []
            "#,
        );

        let claim = &definition.reachability_claims[0];
        assert_eq!(claim.rhs.len(), 2);
        assert_ne!(claim.rhs[0].term, claim.rhs[1].term);
    }

    #[test]
    fn retains_predicate_disjunction_as_one_constraint() {
        let definition = definition(
            r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(\top{SortS{}}(), c{}(X:SortS{})),
                weakExistsFinally{SortS{}}(
                    \and{SortS{}}(
                        c{}(X:SortS{}),
                        \or{SortS{}}(
                            \equals{SortS{}, SortS{}}(X:SortS{}, X:SortS{}),
                            \bottom{SortS{}}()
                        )
                    )
                )
            ) []
            "#,
        );

        let claim = &definition.reachability_claims[0];
        assert_eq!(claim.rhs.len(), 1);
        assert!(matches!(
            claim.rhs[0].constraints.as_slice(),
            [crate::rule::Predicate::Or(_)]
        ));
    }
}
