//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Name each matching-logic disjunction at a shared position of a rule or context with a fresh
//! alias, so that the built side reuses the term the disjunction matched.
//!
//! A term of a rule's body outside every rewrite is on both sides of the rule: it is matched, and
//! the same term is part of the result. There `A #Or B` must stand for the term it matched, not for
//! the disjunction of its alternatives, so the pass writes it as `(A #Or B) #as _GenN`. The walk
//! stops at every rewrite, inside which a term is on one side only, and at every `#as`, whose alias
//! already names the matched term; in practice the pass therefore names the disjunctions at shared
//! positions only.
//!
//! Conditions are not roots. A `requires` or `ensures` is matched against nothing and is part of
//! no right side, so an alias there would name no matched term: in an `ensures` it would be a free
//! variable of the result, in a `requires` a variable that no match binds. A disjunction in a
//! condition is the predicate disjunction its text states and stays as written. Claims are not
//! transformed.
//!
//! In the compile pipeline the stage `resolve contexts` runs before this one, so a context has
//! already become the heating and cooling rules that this pass transforms as rules; the context
//! arm serves a definition given to [`guard_or_patterns`] directly.
#![deny(clippy::wildcard_enum_match_arm)]

use std::fmt;

use crate::{
    definition::{Definition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{InternalLabel, Term, TermMetadata},
    kompile::{SortInjector, fresh_names::FreshNames},
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GuardOrPatternsError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for GuardOrPatternsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "or-pattern guarding produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for GuardOrPatternsError {}

/// Alias every `#Or` pattern of a rule's or context's body that lies outside its rewrites and
/// aliases with a fresh variable, so that the right-hand side reuses the term the disjunction
/// matched. Conditions and claims are left as written (see the module documentation).
pub fn guard_or_patterns(definition: &Definition) -> Result<Definition, GuardOrPatternsError> {
    super::super::pipeline::run_standalone(
        definition,
        guard_or_patterns_pass,
        Some(GeneratingPass::GuardOrPatterns),
    )
}

pub(crate) fn guard_or_patterns_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, GuardOrPatternsError> {
    let resolved = input.resolved_raw().map_err(|error| GuardOrPatternsError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let injector =
            SortInjector::with_views(&views, module_id).map_err(|error| GuardOrPatternsError {
                diagnostics: vec![plain_error(error.to_string())],
            })?;
        for sentence in &mut module.local_sentences {
            // A condition is matched against nothing, so only the body has positions to name.
            let body = match &**sentence {
                Sentence::Rule { body, .. } | Sentence::Context { body, .. } => body,
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => continue,
            };
            let mut fresh = FreshNames::for_sentence(sentence);
            let transformed =
                transform(body, &injector, &mut fresh).map_err(|error| GuardOrPatternsError {
                    diagnostics: vec![Diagnostic::error_at(
                        DiagnosticCode::InvalidOrPattern,
                        error.to_string(),
                        sentence.attributes(),
                    )],
                })?;
            // A body the walk leaves as it is keeps the sentence the shared input allocation.
            let Some(transformed) = transformed else {
                continue;
            };
            match crate::definition::sentence_mut(sentence) {
                Sentence::Rule { body, .. } | Sentence::Context { body, .. } => *body = transformed,
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => unreachable!("only a rule or a context has a body"),
            }
        }
    }
    Ok(output)
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidOrPattern,
        message: message.into(),
        source: None,
        location: None,
        input_addresses: Vec::new(),
    }
}

// Invariant: each call rewrites an internal `Or` application into an `As` pattern with a fresh `_Gen` alias, leaves `As` and `Rewrite` terms as they are, and otherwise recurses into `Apply` arguments and `Sequence` items, left to right; the finite depth of `term` bounds the recursion.
/// `term` with its guarded disjunctions named, or `None` when that is `term` itself.
///
/// A node is rebuilt from its unannotated form under its outermost annotation, so a node whose
/// annotation is not in the form `with_metadata` builds (one layer, not the default) is rebuilt
/// even when nothing below it changes: `None` is returned exactly when the rebuilt term would be
/// identical to `term`, and the caller then keeps `term`, its allocation included.
fn transform(
    term: &Term,
    injector: &SortInjector<'_, '_>,
    fresh: &mut FreshNames,
) -> Result<Option<Term>, crate::kompile::SortInjectionError> {
    let metadata = term.metadata();
    let unannotated = term.unannotated();
    let rebuilt = match unannotated {
        Term::Apply { label, .. } if label.is(InternalLabel::Or) => {
            let application = annotate(unannotated.clone(), metadata);
            let sort = injector.term_sort_before_shape_normalization(&application, None)?;
            Some(Term::As {
                pattern: Box::new(application),
                alias: Box::new(Term::Variable {
                    name: fresh.mint("_Gen"),
                    sort: Some(sort),
                }),
            })
        }
        // A term outside every rewrite is on both sides of the rule, and on the right-hand side
        // an `#Or` would denote the disjunction of its alternatives rather than the term it
        // matched. Inside a rewrite a term is on one side only, and under an `#as` the alias
        // already names the matched term, so the walk stops at both.
        Term::As { .. }
        | Term::Rewrite { .. }
        | Term::InjectedLabel(_)
        | Term::Variable { .. }
        | Term::Token { .. } => None,
        Term::Apply { label, arguments } => {
            transform_items(arguments, injector, fresh)?.map(|arguments| Term::Apply {
                label: label.clone(),
                arguments,
            })
        }
        Term::Sequence(items) => transform_items(items, injector, fresh)?.map(Term::Sequence),
        Term::Annotated { .. } => unreachable!("unannotated strips metadata"),
    };
    Ok(match rebuilt {
        Some(rebuilt) => Some(annotate(rebuilt, metadata)),
        None if annotation_is_rebuilt_form(term) => None,
        None => Some(annotate(unannotated.clone(), metadata)),
    })
}

/// `items` with each item transformed, or `None` when every item is kept as it is.
fn transform_items(
    items: &[Term],
    injector: &SortInjector<'_, '_>,
    fresh: &mut FreshNames,
) -> Result<Option<Vec<Term>>, crate::kompile::SortInjectionError> {
    let mut rebuilt: Option<Vec<Term>> = None;
    for (index, item) in items.iter().enumerate() {
        let transformed = transform(item, injector, fresh)?;
        match (&mut rebuilt, transformed) {
            (Some(rebuilt), transformed) => {
                rebuilt.push(transformed.unwrap_or_else(|| item.clone()));
            }
            (None, Some(transformed)) => {
                let mut items_so_far = Vec::with_capacity(items.len());
                items_so_far.extend_from_slice(&items[..index]);
                items_so_far.push(transformed);
                rebuilt = Some(items_so_far);
            }
            (None, None) => {}
        }
    }
    Ok(rebuilt)
}

fn annotate(term: Term, metadata: Option<&TermMetadata>) -> Term {
    match metadata {
        Some(metadata) => term.with_metadata(metadata.clone()),
        None => term,
    }
}

/// Whether `annotate(term.unannotated().clone(), term.metadata())` is `term`: `term` has no
/// annotation, or one layer whose metadata is not the default (`with_metadata` drops a default
/// annotation and merges into an existing layer, so it never builds the other shapes).
fn annotation_is_rebuilt_form(term: &Term) -> bool {
    match term {
        Term::Annotated {
            term: inner,
            metadata,
        } => !matches!(**inner, Term::Annotated { .. }) && *metadata != TermMetadata::default(),
        Term::InjectedLabel(_)
        | Term::Rewrite { .. }
        | Term::As { .. }
        | Term::Variable { .. }
        | Term::Sequence(_)
        | Term::Apply { .. }
        | Term::Token { .. } => true,
    }
}
