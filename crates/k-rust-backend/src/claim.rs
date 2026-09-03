//! Internalization of modal reachability claims.

use std::collections::BTreeSet;

use k_rust_kore::kore::ast as kore;

use crate::{
    definition::{BackendDefinition, DefinitionError, PendingAxiom, SubsortValidation},
    rewrite::Pattern,
    rule::{RuleAttributes, internalize_rule_pattern, term_disjuncts},
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
) -> Result<Vec<ReachabilityClaim>, DefinitionError> {
    let kore::Pattern::Implies { left, right, .. } = &claim.pattern else {
        return Ok(Vec::new());
    };
    let kore::Pattern::Application { symbol, arguments } = right.as_ref() else {
        return Ok(Vec::new());
    };
    let mode = match symbol.name.as_str() {
        ONE_PATH_MODALITY => ReachabilityMode::OnePath,
        ALL_PATH_MODALITY => ReachabilityMode::AllPath,
        _ => return Ok(Vec::new()),
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
        .map(|variable| definition.internalize_variable(variable, &claim.parameters))
        .collect::<Result<BTreeSet<_>, DefinitionError>>()?;
    let rhs = term_disjuncts(right)
        .into_iter()
        .map(|branch| {
            let (term, constraints) = internalize_rule_pattern(
                definition,
                &branch,
                &claim.parameters,
                SubsortValidation::Ignore,
            )?;
            Ok(Pattern { term, constraints })
        })
        .collect::<Result<Vec<_>, DefinitionError>>()?;
    if rhs.is_empty() {
        return Err(DefinitionError::Claim(ClaimError::MissingRightHandSide));
    }
    let parsed_attributes =
        RuleAttributes::parse(&claim.attributes).map_err(DefinitionError::Axiom)?;
    let attributes = ClaimAttributes {
        label: parsed_attributes.label,
        unique_id: parsed_attributes.unique_id,
        trusted: has_attribute(&claim.attributes, "trusted"),
        source: parsed_attributes.source,
        location: parsed_attributes.location,
    };
    term_disjuncts(left)
        .into_iter()
        .map(|left| {
            let (term, constraints) = internalize_rule_pattern(
                definition,
                &left,
                &claim.parameters,
                SubsortValidation::Ignore,
            )?;
            Ok(ReachabilityClaim {
                lhs: Pattern { term, constraints },
                rhs: rhs.clone(),
                existentials: existentials.clone(),
                mode,
                attributes: attributes.clone(),
            })
        })
        .collect()
}

fn extract_existentials(mut pattern: &kore::Pattern) -> (&kore::Pattern, Vec<&kore::Variable>) {
    let mut variables = Vec::new();
    while let kore::Pattern::Exists { variable, body, .. } = pattern {
        variables.push(variable);
        pattern = body;
    }
    (pattern, variables)
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
                symbol c{{}}(SortS{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), injective{{}}(), no-evaluators{{}}()]
                alias weakExistsFinally{{S}}(S) : S
                    where weakExistsFinally{{S}}(@X:S) := @X:S []
                alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
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
