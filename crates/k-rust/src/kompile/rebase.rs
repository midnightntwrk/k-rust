//! Production metadata rebasing preserves parser identities across transformed catalogs.
//! Strict rebases fail on missing metadata; executable tokens and sort-injection localization use
//! their explicitly narrower discard policies.

use k_rust_kore::measure::{self, Counter};

use crate::definition::{
    Definition, ProductionCatalog, ProductionId, ResolvedDefinition, Sentence, sentence_equivalent,
};
use crate::kast::{ResolvedProductionId, Term};

/// Find the first target production structurally equivalent to `source`.
pub(crate) fn find_equivalent(
    source: &Sentence,
    target: &ProductionCatalog<'_>,
) -> Option<ProductionId> {
    // Invariant: every smaller target ID has been checked and rejected; the remaining catalog
    // iterator shrinks by one until the first equivalent production is found.
    target
        .productions()
        .find_map(|(id, candidate)| sentence_equivalent(source, candidate).then_some(id))
}

/// Rebase parser production indexes after a pass adds or removes productions.
///
/// Parsed terms intentionally store compact catalog indexes. Compilation passes preserve those
/// terms while changing the catalog around them, so every production-changing pass must translate
/// surviving indexes before the next resolved-definition boundary.
pub(crate) fn rebase_local_metadata(
    before: &Definition,
    after: Definition,
) -> Result<Definition, String> {
    rebase_local_metadata_by(before, after, sentence_equivalent)
}

pub(crate) fn rebase_local_metadata_by(
    before: &Definition,
    mut after: Definition,
    production_matches: impl Fn(&Sentence, &Sentence) -> bool,
) -> Result<Definition, String> {
    measure::bump(Counter::KompileRebaseCalls);
    let before = ResolvedDefinition::resolve(before).map_err(|error| error.to_string())?;
    let after_resolved = ResolvedDefinition::resolve(&after).map_err(|error| error.to_string())?;
    for module in &mut after.modules {
        let Some(before_module) = before.module_id(&module.name) else {
            continue;
        };
        let Some(after_module) = after_resolved.module_id(&module.name) else {
            continue;
        };
        let source = before.production_catalog(before_module);
        let target = after_resolved.production_catalog(after_module);
        for sentence in &mut module.local_sentences {
            rebase_sentence(sentence, &source, &target, &production_matches)?;
        }
    }
    Ok(after)
}

pub(crate) fn rebase_sentence(
    sentence: &mut Sentence,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
    production_matches: &impl Fn(&Sentence, &Sentence) -> bool,
) -> Result<(), String> {
    rebase_sentence_with_policy(
        sentence,
        source,
        target,
        production_matches,
        MissingProductionMetadata::Error,
    )
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
    production_matches: &impl Fn(&Sentence, &Sentence) -> bool,
) -> Result<Term, String> {
    rebase_term(
        term,
        source,
        target,
        production_matches,
        MissingProductionMetadata::DiscardToken,
    )
}

/// Localize sort-injection metadata, discarding absent and out-of-range source indexes.
// Invariant: each recursive call consumes one child of the current term, so the finite term tree
// strictly bounds the remaining calls.
pub(crate) fn rebase_term_lossy(
    term: Term,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
) -> Term {
    let mut metadata = term.metadata().cloned().unwrap_or_default();
    if let Some(ResolvedProductionId(index)) = metadata.production {
        metadata.production = (index < source.len())
            .then(|| find_equivalent(source.production(ProductionId(index)), target))
            .flatten()
            .map(|id| ResolvedProductionId(id.0));
    }
    let rebuilt = match term.into_unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(rebase_term_lossy(*left, source, target)),
            right: Box::new(rebase_term_lossy(*right, source, target)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rebase_term_lossy(*pattern, source, target)),
            alias: Box::new(rebase_term_lossy(*alias, source, target)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| rebase_term_lossy(item, source, target))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| rebase_term_lossy(argument, source, target))
                .collect(),
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!(),
    };
    rebuilt.with_metadata(metadata)
}

#[derive(Clone, Copy)]
enum MissingProductionMetadata {
    Error,
    DiscardToken,
}

fn rebase_sentence_with_policy(
    sentence: &mut Sentence,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
    production_matches: &impl Fn(&Sentence, &Sentence) -> bool,
    missing: MissingProductionMetadata,
) -> Result<(), String> {
    let rebase = |term: &mut Term| {
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = rebase_term(taken, source, target, production_matches, missing)?;
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
            rebase(body)?;
            rebase(requires)?;
            rebase(ensures)?;
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            rebase(body)?;
            rebase(requires)?;
        }
        Sentence::Configuration { body, ensures, .. } => {
            rebase(body)?;
            rebase(ensures)?;
        }
        _ => {}
    }
    Ok(())
}

// Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
fn rebase_term(
    term: Term,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
    production_matches: &impl Fn(&Sentence, &Sentence) -> bool,
    missing: MissingProductionMetadata,
) -> Result<Term, String> {
    let token = matches!(term.unannotated(), Term::Token { .. });
    let mut metadata = term.metadata().cloned().unwrap_or_default();
    if let Some(ResolvedProductionId(index)) = metadata.production {
        if index >= source.len() {
            return Err(format!(
                "production metadata #{index} exceeds source catalog length {}",
                source.len()
            ));
        }
        let production = source.production(ProductionId(index));
        // Invariant: prior outer items and prior candidates for this item have been examined in order; the remaining inner iterator shrinks, giving O(n^2) over the two scanned collections.
        let rebased = target
            .productions()
            .find_map(|(id, candidate)| production_matches(production, candidate).then_some(id));
        metadata.production = match (rebased, missing) {
            (Some(rebased), _) => Some(ResolvedProductionId(rebased.0)),
            (None, MissingProductionMetadata::DiscardToken) if token => None,
            (None, MissingProductionMetadata::Error) => {
                return Err(format!(
                    "source production metadata #{index} has no equivalent in the transformed catalog"
                ));
            }
            (None, MissingProductionMetadata::DiscardToken) => {
                return Err(format!(
                    "source production metadata #{index} on an application has no equivalent in the target catalog"
                ));
            }
        };
    }
    let rebuilt = match term.into_unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(rebase_term(
                *left,
                source,
                target,
                production_matches,
                missing,
            )?),
            right: Box::new(rebase_term(
                *right,
                source,
                target,
                production_matches,
                missing,
            )?),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rebase_term(
                *pattern,
                source,
                target,
                production_matches,
                missing,
            )?),
            alias: Box::new(rebase_term(
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
                .map(|item| rebase_term(item, source, target, production_matches, missing))
                .collect::<Result<_, _>>()?,
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| rebase_term(argument, source, target, production_matches, missing))
                .collect::<Result<_, _>>()?,
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!(),
    };
    Ok(rebuilt.with_metadata(metadata))
}
