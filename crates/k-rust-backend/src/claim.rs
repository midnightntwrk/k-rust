//! Internalization of modal reachability claims.

use std::collections::BTreeSet;

use k_rust_kore::kore::ast as kore;
use k_rust_kore::names::KoreAttribute;

use crate::{
    definition::{
        BackendDefinition, DefinitionError, PendingAxiom, UnlicensedInjectionSite,
        UnstatedDefinedness,
    },
    rewrite::Pattern,
    rule::{
        ConditionSlot, PredicateReading, RuleAttributes, RulePatternError, internalize_side,
        term_disjuncts,
    },
    term::Variable,
};

const ONE_PATH_MODALITY: &str = "weakExistsFinally";
const ALL_PATH_MODALITY: &str = "weakAlwaysFinally";

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
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
    /// The position of the claim sentence among the definition's claims. A sentence whose
    /// left-hand side is a disjunction is one claim per disjunct, all with its position; no two
    /// sentences share one, whatever their attributes say (a claim written in KORE may carry no
    /// unique id, no origin, or another claim's label).
    pub sentence: usize,
}

/// A modal reachability claim `lhs => rhs`, one per disjunct of its sentence's left-hand side.
///
/// The constraints of `lhs` and of every pattern of `rhs` are the claim author's statement about
/// the claim's instances, read with their matching-logic meaning: a Boolean atom `b` means
/// `\equals(b, true)`, which is `\bottom` wherever a term of `b` is undefined, and an equality of
/// two terms holds where both denote the same element or both denote nothing. They are stored in
/// definedness-explicit form (`with_explicit_definedness`), an equivalent list in which a
/// solver that reads a partial operation as total answers as that meaning does, so the claim
/// keeps one meaning as the initial state of its own proof, as a destination, and as an applied
/// circularity or trusted lemma. A claim whose constraints have no such form keeps them as
/// written and carries the reason in `unstated`; it is not proven ([`crate::proof::ProofError`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReachabilityClaim {
    pub lhs: Pattern,
    pub rhs: Vec<Pattern>,
    pub existentials: BTreeSet<Variable>,
    pub mode: ReachabilityMode,
    pub attributes: ClaimAttributes,
    /// Why the claim's constraints have no definedness-explicit form, when they have none.
    pub unstated: Option<UnstatedDefinedness>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClaimError {
    MalformedModality {
        modality: String,
        argument_count: usize,
    },
    MissingRightHandSide,
}

/// What is wrong with a reachability claim, in terms of what the claim states.
impl std::fmt::Display for ClaimError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedModality {
                modality,
                argument_count,
            } => write!(
                formatter,
                "the modality {modality} is applied to {argument_count} arguments, and it takes \
                 one, the claim's right-hand side"
            ),
            Self::MissingRightHandSide => formatter.write_str(
                "the claim's right-hand side has no disjunct, so it states no configuration to reach",
            ),
        }
    }
}

pub(crate) fn internalize_reachability_claim(
    definition: &BackendDefinition,
    sentence: usize,
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
    // A claim's predicates are read as an axiom's are: as written, but for the frontend's
    // condition slots, the `requires` before the left-hand side's configuration and the
    // `ensures` after the right-hand side's. A claim with a predicate that reading refuses has
    // no faithful reading, so it is refused alone, as unstated, and keeps its sides as the
    // reading without refusals gives them; the definition and its other claims load.
    let (unstated, lhs, rhs) = match claim_sides(
        definition,
        &claim.parameters,
        left,
        right,
        PredicateReading::Written,
    ) {
        Ok((lhs, rhs)) => (None, lhs, rhs),
        Err(error) => {
            let Some(refusal) = refused_reading(&error) else {
                return Err(error);
            };
            let (lhs, rhs) = claim_sides(
                definition,
                &claim.parameters,
                left,
                right,
                PredicateReading::Unchecked,
            )?;
            (Some(refusal), lhs, rhs)
        }
    };
    if rhs.is_empty() {
        return Err(DefinitionError::Claim(ClaimError::MissingRightHandSide));
    }
    let parsed_attributes =
        RuleAttributes::parse(&claim.attributes).map_err(DefinitionError::Axiom)?;
    let origin = parsed_attributes
        .origins
        .into_iter()
        .next()
        .expect("a parsed sentence has exactly one origin");
    let attributes = ClaimAttributes {
        label: parsed_attributes.label,
        unique_id: parsed_attributes.unique_id,
        trusted: claim.attributes.has(KoreAttribute::Trusted),
        source: origin.source,
        location: origin.location,
        sentence,
    };
    Ok(lhs
        .into_iter()
        .map(|lhs| ReachabilityClaim {
            lhs,
            rhs: rhs.clone(),
            existentials: existentials.clone(),
            mode,
            attributes: attributes.clone(),
            unstated: unstated.clone(),
        })
        .collect())
}

/// The left-hand disjuncts and the right-hand disjuncts of a claim `left => right` (`right`
/// under its modality and existentials), their predicates read with `reading` outside the
/// frontend's condition slots.
fn claim_sides(
    definition: &BackendDefinition,
    parameters: &[crate::term::Name],
    left: &kore::Pattern,
    right: &kore::Pattern,
    reading: PredicateReading,
) -> Result<(Vec<Pattern>, Vec<Pattern>), DefinitionError> {
    let sides = |side: &kore::Pattern, slot: ConditionSlot| {
        // The split into disjuncts keeps a root `\and` and its arity, so each keeps the slot.
        let slot = if matches!(side, kore::Pattern::And { arguments, .. } if arguments.len() == 2) {
            slot
        } else {
            ConditionSlot::None
        };
        term_disjuncts(side)
            .into_iter()
            .map(|branch| {
                let (term, constraints) = internalize_side(
                    definition,
                    &branch,
                    parameters,
                    UnlicensedInjectionSite::Refuse,
                    slot,
                    reading,
                )?;
                Ok(Pattern { term, constraints })
            })
            .collect::<Result<Vec<_>, DefinitionError>>()
    };
    let rhs = sides(right, ConditionSlot::Last)?;
    let lhs = sides(left, ConditionSlot::First)?;
    Ok((lhs, rhs))
}

/// Why the predicate reading refused a claim's side, when `error` is such a refusal: an
/// `\equals` that would read a term as a predicate, a connective over terms conjoined to a term,
/// or a term of another sort than Bool read as a predicate.
fn refused_reading(error: &DefinitionError) -> Option<UnstatedDefinedness> {
    match error {
        DefinitionError::UnstatedDefinedness(UnstatedDefinedness::TermReadAsPredicate) => {
            Some(UnstatedDefinedness::TermReadAsPredicate)
        }
        DefinitionError::RulePattern(
            error @ (RulePatternError::TermConnectiveInConjunction { .. }
            | RulePatternError::NonBoolTermAsPredicate { .. }),
        ) => Some(UnstatedDefinedness::RefusedReading(Box::new(error.clone()))),
        _ => None,
    }
}

/// `claim` with the constraints of its left-hand side and of every right-hand disjunct in
/// definedness-explicit form, as a request's are (`definedness::request_definedness`).
///
/// A claim's constraints select the instances the claim speaks about, and their meaning is the
/// pattern's alone: an atom over a term implies that term's definedness in every context, and an
/// equality of two possibly undefined terms holds where both denote nothing. Each rewrite of the
/// helper is an equivalence, so the claim denotes the same configurations after it, and the
/// statement is a fixed point. It reads the definition's ceil equations and value claims, so it
/// runs once the definition is complete. A side with no such form (an impure application whose
/// definedness a conditional would decide, an atom over a term-level `\and`) leaves the claim as
/// written, with the reason in `unstated`, so that the definition still loads and its other
/// claims and its execution are unaffected; so does a claim with a predicate that the backend's
/// reading refuses (`internalize_reachability_claim`: an `\equals` that would read a term as a
/// predicate, a connective over terms conjoined to a term, a term of another sort than Bool
/// read as a predicate), which keeps its reason.
///
/// The reading this gives a claim's KORE is the one `k_rust::backend::proving::CLAIM_READING`
/// names in saved-proof digests: a change to it changes what a saved proof certifies, and must
/// name a new reading there.
pub(crate) fn with_explicit_definedness(
    definition: &BackendDefinition,
    mut claim: ReachabilityClaim,
) -> ReachabilityClaim {
    if claim.unstated.is_some() {
        return claim;
    }
    let stated = |constraints: &[crate::rule::Predicate]| {
        crate::definedness::request_definedness(definition, constraints.to_vec())
            .map_err(UnstatedDefinedness::from)
    };
    let sides = std::iter::once(&claim.lhs)
        .chain(&claim.rhs)
        .map(|side| stated(&side.constraints))
        .collect::<Result<Vec<_>, _>>();
    match sides {
        Ok(sides) => {
            let mut sides = sides.into_iter();
            claim.lhs.constraints = sides.next().expect("the left-hand side is stated");
            for (side, constraints) in claim.rhs.iter_mut().zip(sides) {
                side.constraints = constraints;
            }
        }
        Err(refusal) => claim.unstated = Some(refusal),
    }
    claim
}

fn extract_existentials(mut pattern: &kore::Pattern) -> (&kore::Pattern, Vec<&kore::Variable>) {
    let mut variables = Vec::new();
    while let kore::Pattern::Exists { variable, body, .. } = pattern {
        variables.push(variable.as_ref());
        pattern = body;
    }
    (pattern, variables)
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

    /// A claim's constraints are its author's statement about its instances. `\not(true = p(X))`
    /// of a partial `p` holds where `p(X)` is undefined, so the stored form states `p(X)`'s
    /// definedness beside the atom, under the negation, and is a fixed point of the statement.
    #[test]
    fn stores_a_claims_constraints_with_their_definedness_stated_where_they_stand() {
        let source = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                sort SortT{} []
                sort SortBool{} [hasDomainValues{}()]
                symbol c{}(SortS{}) : SortT{} [constructor{}()]
                symbol p{}(SortS{}) : SortBool{} [function{}(), no-evaluators{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                claim{} \implies{SortT{}}(
                    \and{SortT{}}(
                        c{}(X:SortS{}),
                        \not{SortT{}}(\equals{SortBool{}, SortT{}}(
                            \dv{SortBool{}}("true"),
                            p{}(X:SortS{})
                        ))
                    ),
                    weakAlwaysFinally{SortT{}}(\and{SortT{}}(c{}(X:SortS{}), \top{SortT{}}()))
                ) [label{}("negated")]
            endmodule []"#;
        let syntax = parse_definition(source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let [claim] = definition.reachability_claims() else {
            panic!("one claim: {:?}", definition.reachability_claims());
        };
        assert_eq!(claim.unstated, None);
        let [stored] = claim.lhs.constraints.as_slice() else {
            panic!("one constraint: {:?}", claim.lhs.constraints);
        };
        let crate::rule::Predicate::Not(negated) = stored else {
            panic!("the negation stays the constraint: {stored:?}");
        };
        let rendered = format!("{negated:?}");
        assert!(
            rendered.contains("Defined") || rendered.contains("Ceil"),
            "the atom's definedness is stated under the negation: {negated:?}"
        );
        assert_eq!(
            crate::definedness::request_definedness(&definition, claim.lhs.constraints.clone())
                .expect("a stated form is stated again"),
            claim.lhs.constraints,
            "the stored form is a fixed point"
        );
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

        assert_eq!(definition.claims().len(), 3);
        assert_eq!(definition.reachability_claims().len(), 2);
        assert_eq!(
            definition.reachability_claims()[0].mode,
            ReachabilityMode::OnePath
        );
        assert_eq!(
            definition.reachability_claims()[1].mode,
            ReachabilityMode::AllPath
        );
        assert!(definition.reachability_claims()[0].attributes.trusted);
        assert_eq!(
            definition.reachability_claims()[0]
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

        assert_eq!(definition.reachability_claims()[0].rhs.len(), 2);
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

        let claim = &definition.reachability_claims()[0];
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

        let claim = &definition.reachability_claims()[0];
        assert_eq!(claim.rhs.len(), 1);
        assert!(matches!(
            claim.rhs[0].constraints.as_slice(),
            [crate::rule::Predicate::Or(_)]
        ));
    }
}
