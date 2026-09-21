//! Production metadata rebasing preserves parser identities across transformed catalogs.
//! Exact lookup costs O(P log P) to build and O(log P + b * eq) per uncached source production;
//! `KompileSentenceEquivalenceChecks` measures the bucket confirmations.
//! Strict rebases fail on missing metadata; executable tokens and sort-injection localization use
//! their explicitly narrower discard policies.

use std::collections::BTreeMap;

use k_rust_kore::measure::{self, Counter};

use crate::definition::{
    Definition, DefinitionViews, ProductionCatalog, ResolvedDefinition, Sentence,
};
use crate::kast::{ProductionIdentity, Term};

/// One exact source-to-target rebase with a target index and source-ID memo.
pub(crate) struct ExactRebaser<'source_catalog, 'source, 'target_catalog, 'target> {
    source: &'source_catalog ProductionCatalog<'source>,
    target: &'target_catalog ProductionCatalog<'target>,
    memo: BTreeMap<ProductionIdentity, Option<ProductionIdentity>>,
}

impl<'source_catalog, 'source, 'target_catalog, 'target>
    ExactRebaser<'source_catalog, 'source, 'target_catalog, 'target>
{
    pub(crate) fn new(
        source: &'source_catalog ProductionCatalog<'source>,
        target: &'target_catalog ProductionCatalog<'target>,
    ) -> Self {
        Self {
            source,
            target,
            memo: BTreeMap::new(),
        }
    }

    pub(crate) fn rebase_sentence(&mut self, sentence: &mut Sentence) -> Result<(), String> {
        rebase_sentence_terms(sentence, |term| {
            self.rebase_term(term, MissingProductionMetadata::Error)
        })
    }

    pub(crate) fn rebase_term_discarding_tokens(&mut self, term: Term) -> Result<Term, String> {
        self.rebase_term(term, MissingProductionMetadata::DiscardToken)
    }

    pub(crate) fn rebase_term_lossy(&mut self, term: Term) -> Term {
        self.rebase_term(term, MissingProductionMetadata::DiscardAny)
            .expect("lossy production metadata rebasing cannot fail")
    }

    fn equivalent(&mut self, source: ProductionIdentity) -> Option<ProductionIdentity> {
        if let Some(cached) = self.memo.get(&source) {
            return *cached;
        }
        let equivalent = self
            .source
            .lookup(&source)
            .and_then(|source| self.target.find_equivalent(self.source.production(source)))
            .map(|target| self.target.identity(target));
        self.memo.insert(source, equivalent);
        equivalent
    }

    // Invariant: each recursive call consumes one child of the current term, so the finite term
    // tree strictly bounds the remaining calls.
    fn rebase_term(
        &mut self,
        term: Term,
        missing: MissingProductionMetadata,
    ) -> Result<Term, String> {
        let token = matches!(term.unannotated(), Term::Token { .. });
        let mut metadata = term.metadata().cloned().unwrap_or_default();
        if let Some(identity) = metadata.production {
            if self.source.lookup(&identity).is_none() {
                if matches!(missing, MissingProductionMetadata::DiscardAny) {
                    metadata.production = None;
                } else {
                    return Err(format!(
                        "production metadata #{identity} is absent from the source catalog"
                    ));
                }
            } else {
                let rebased = self.equivalent(identity);
                metadata.production = match (rebased, missing) {
                    (Some(rebased), _) => Some(rebased),
                    (None, MissingProductionMetadata::DiscardToken) if token => None,
                    (None, MissingProductionMetadata::DiscardAny) => None,
                    (None, MissingProductionMetadata::Error) => {
                        return Err(format!(
                            "source production metadata #{identity} has no equivalent in the transformed catalog"
                        ));
                    }
                    (None, MissingProductionMetadata::DiscardToken) => {
                        return Err(format!(
                            "source production metadata #{identity} on an application has no equivalent in the target catalog"
                        ));
                    }
                };
            }
        }
        let rebuilt = match term.into_unannotated() {
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.rebase_term(*left, missing)?),
                right: Box::new(self.rebase_term(*right, missing)?),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.rebase_term(*pattern, missing)?),
                alias: Box::new(self.rebase_term(*alias, missing)?),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.rebase_term(item, missing))
                    .collect::<Result<_, _>>()?,
            ),
            Term::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.rebase_term(argument, missing))
                    .collect::<Result<_, _>>()?,
            },
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
            Term::Annotated { .. } => unreachable!(),
        };
        Ok(rebuilt.with_metadata(metadata))
    }
}

/// Rebase parser production indexes after a pass adds or removes productions.
///
/// Parsed terms intentionally store compact catalog indexes. Compilation passes preserve those
/// terms while changing the catalog around them, so every production-changing pass must translate
/// surviving indexes before the next resolved-definition boundary.
pub(crate) fn rebase_local_metadata(
    before: &DefinitionViews<'_>,
    mut after: Definition,
) -> Result<Definition, String> {
    measure::bump(Counter::KompileRebaseCalls);
    let after_resolved = ResolvedDefinition::resolve(&after).map_err(|error| error.to_string())?;
    for module in &mut after.modules {
        let Some(before_module) = before.definition().module_id(&module.name) else {
            continue;
        };
        let Some(after_module) = after_resolved.module_id(&module.name) else {
            continue;
        };
        let source = before.production_catalog(before_module);
        let target = after_resolved.production_catalog(after_module);
        let mut rebaser = ExactRebaser::new(&source, &target);
        for sentence in &mut module.local_sentences {
            rebaser.rebase_sentence(sentence)?;
        }
    }
    Ok(after)
}

/// Predicate-based rebase for transformations whose matching relation is wider than exact
/// sentence equivalence. These deliberately retain the linear target scan.
pub(crate) fn rebase_local_metadata_by(
    before: &DefinitionViews<'_>,
    mut after: Definition,
    production_matches: impl Fn(&Sentence, &Sentence) -> bool,
) -> Result<Definition, String> {
    measure::bump(Counter::KompileRebaseCalls);
    let after_resolved = ResolvedDefinition::resolve(&after).map_err(|error| error.to_string())?;
    for module in &mut after.modules {
        let Some(before_module) = before.definition().module_id(&module.name) else {
            continue;
        };
        let Some(after_module) = after_resolved.module_id(&module.name) else {
            continue;
        };
        let source = before.production_catalog(before_module);
        let target = after_resolved.production_catalog(after_module);
        for sentence in &mut module.local_sentences {
            rebase_sentence_by(sentence, &source, &target, &production_matches)?;
        }
    }
    Ok(after)
}

pub(crate) fn rebase_sentence(
    sentence: &mut Sentence,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
) -> Result<(), String> {
    ExactRebaser::new(source, target).rebase_sentence(sentence)
}

/// Rebase a standalone term into another visible production catalog.
///
/// Tokens describe their executable KORE value with their sort and may therefore discard an
/// absent lexical production index. Applications require an equivalent visible production so
/// sort injection and KORE conversion never interpret an index from another catalog.
pub(crate) fn rebase_term_to_visible_catalog(
    term: Term,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
) -> Result<Term, String> {
    ExactRebaser::new(source, target).rebase_term_discarding_tokens(term)
}

#[derive(Clone, Copy)]
enum MissingProductionMetadata {
    Error,
    DiscardToken,
    DiscardAny,
}

fn rebase_sentence_terms(
    sentence: &mut Sentence,
    mut rebase: impl FnMut(Term) -> Result<Term, String>,
) -> Result<(), String> {
    let mut rebase_in_place = |term: &mut Term| {
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = rebase(taken)?;
        Ok::<_, String>(())
    };
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => {
            rebase_in_place(body)?;
            rebase_in_place(requires)?;
            rebase_in_place(ensures)?;
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            rebase_in_place(body)?;
            rebase_in_place(requires)?;
        }
        Sentence::Configuration { body, ensures, .. } => {
            rebase_in_place(body)?;
            rebase_in_place(ensures)?;
        }
        _ => {}
    }
    Ok(())
}

fn rebase_sentence_by(
    sentence: &mut Sentence,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
    production_matches: &impl Fn(&Sentence, &Sentence) -> bool,
) -> Result<(), String> {
    rebase_sentence_terms(sentence, |term| {
        rebase_term_by(
            term,
            source,
            target,
            production_matches,
            MissingProductionMetadata::Error,
        )
    })
}

// Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
fn rebase_term_by(
    term: Term,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
    production_matches: &impl Fn(&Sentence, &Sentence) -> bool,
    missing: MissingProductionMetadata,
) -> Result<Term, String> {
    let token = matches!(term.unannotated(), Term::Token { .. });
    let mut metadata = term.metadata().cloned().unwrap_or_default();
    if let Some(identity) = metadata.production {
        if source.lookup(&identity).is_none() {
            return Err(format!(
                "production metadata #{identity} is absent from the source catalog"
            ));
        }
        let production = source.production(source.lookup(&identity).expect("checked above"));
        let rebased = target
            .productions()
            .find_map(|(id, candidate)| production_matches(production, candidate).then_some(id));
        metadata.production = match (rebased, missing) {
            (Some(rebased), _) => Some(target.identity(rebased)),
            (None, MissingProductionMetadata::DiscardToken) if token => None,
            (None, MissingProductionMetadata::DiscardAny) => None,
            (None, MissingProductionMetadata::Error) => {
                return Err(format!(
                    "source production metadata #{identity} has no equivalent in the transformed catalog"
                ));
            }
            (None, MissingProductionMetadata::DiscardToken) => {
                return Err(format!(
                    "source production metadata #{identity} on an application has no equivalent in the target catalog"
                ));
            }
        };
    }
    let rebuilt = match term.into_unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(rebase_term_by(
                *left,
                source,
                target,
                production_matches,
                missing,
            )?),
            right: Box::new(rebase_term_by(
                *right,
                source,
                target,
                production_matches,
                missing,
            )?),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rebase_term_by(
                *pattern,
                source,
                target,
                production_matches,
                missing,
            )?),
            alias: Box::new(rebase_term_by(
                *alias,
                source,
                target,
                production_matches,
                missing,
            )?),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| rebase_term_by(item, source, target, production_matches, missing))
                .collect::<Result<_, _>>()?,
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| {
                    rebase_term_by(argument, source, target, production_matches, missing)
                })
                .collect::<Result<_, _>>()?,
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!(),
    };
    Ok(rebuilt.with_metadata(metadata))
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use serde_json::json;

    use super::*;
    use crate::definition::resolve::SentenceKey;
    use crate::definition::{Attributes, ProductionItem, sentence_equivalent};
    use crate::kast::{Label, Sort};

    type ProductionSpec = (u8, u8, u8, u8);

    fn production((label, sort, first, second): ProductionSpec) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(format!("label{label}"))),
            parameters: Vec::new(),
            sort: Sort::new(format!("Sort{sort}")),
            items: vec![
                ProductionItem::Terminal(first.to_string()),
                ProductionItem::Terminal(second.to_string()),
            ],
            attributes: Attributes::default(),
        }
    }

    proptest! {
        #[test]
        fn sentence_key_contains_every_equivalence_class(
            spec in (any::<u8>(), any::<u8>(), any::<u8>(), any::<u8>()),
            left_location in any::<u8>(),
            right_location in any::<u8>(),
        ) {
            let mut left = production(spec);
            let mut right = left.clone();
            left.attributes_mut().insert(
                "org.kframework.attributes.Location",
                json!([left_location, 1, left_location, 2]),
            );
            right.attributes_mut().insert(
                "org.kframework.attributes.Location",
                json!([right_location, 1, right_location, 2]),
            );

            prop_assert!(sentence_equivalent(&left, &right));
            prop_assert!(SentenceKey::of(&left) == SentenceKey::of(&right));
        }

        #[test]
        fn indexed_lookup_matches_the_ascending_linear_oracle(
            target_specs in prop::collection::vec(
                (any::<u8>(), any::<u8>(), any::<u8>(), any::<u8>()),
                0..40,
            ),
            source_spec in (any::<u8>(), any::<u8>(), any::<u8>(), any::<u8>()),
        ) {
            let targets = target_specs.into_iter().map(production).collect::<Vec<_>>();
            let target = ProductionCatalog::from_visible(targets.iter());
            let source = production(source_spec);
            let expected = target
                .productions()
                .find_map(|(id, candidate)| sentence_equivalent(&source, candidate).then_some(id));
            let actual = target.find_equivalent(&source);

            prop_assert_eq!(actual, expected);
        }
    }
}
