//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Give every anonymous variable occurrence a collision-free sentence-local name.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{collections::BTreeSet, convert::Infallible, sync::Arc};

use crate::{
    definition::{Definition, Sentence},
    kast::{Term, TermMetadata},
    kompile::fresh_names::{FreshNames, GeneratedVariableIdentity},
    provenance::GeneratingPass,
};

/// Give every anonymous variable occurrence of rules, claims and contexts a collision-free
/// sentence-local name.
pub fn resolve_anon_vars(definition: &Definition) -> Definition {
    super::super::pipeline::run_standalone(
        definition,
        resolve_anon_vars_pass,
        Some(GeneratingPass::ResolveAnonymousVariables),
    )
    .unwrap_or_else(|error| match error {})
}

pub(crate) fn resolve_anon_vars_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, Infallible> {
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            // A sentence the resolution leaves identical stays the input's allocation.
            if let Some(resolved) = resolve_anon_vars_in(sentence, &mut BTreeSet::new()) {
                *sentence = Arc::new(resolved);
            }
        }
    }
    Ok(output)
}

/// Resolve anonymous variables in one sentence and return exactly the identities minted.
pub fn resolve_anon_vars_in_sentence(
    sentence: Sentence,
) -> (Sentence, BTreeSet<GeneratedVariableIdentity>) {
    let mut generated = BTreeSet::new();
    let resolved = resolve_anon_vars_in(&sentence, &mut generated).unwrap_or(sentence);
    (resolved, generated)
}

/// `sentence` with every anonymous variable of its body and conditions given a fresh name, each
/// identity minted added to `generated`; `None` when that is `sentence` itself, identical in
/// every stored part.
fn resolve_anon_vars_in(
    sentence: &Sentence,
    generated: &mut BTreeSet<GeneratedVariableIdentity>,
) -> Option<Sentence> {
    let mut names = SentenceNames {
        sentence,
        fresh: None,
    };
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } => {
            let [body, requires, ensures] =
                transform_roots([body, requires, ensures], &mut names, generated)?;
            Some(Sentence::Rule {
                body,
                requires,
                ensures,
                attributes: attributes.clone(),
            })
        }
        Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } => {
            let [body, requires, ensures] =
                transform_roots([body, requires, ensures], &mut names, generated)?;
            Some(Sentence::Claim {
                body,
                requires,
                ensures,
                attributes: attributes.clone(),
            })
        }
        Sentence::Context {
            body,
            requires,
            attributes,
        } => {
            let [body, requires] = transform_roots([body, requires], &mut names, generated)?;
            Some(Sentence::Context {
                body,
                requires,
                attributes: attributes.clone(),
            })
        }
        Sentence::ContextAlias {
            body,
            requires,
            attributes,
        } => {
            let [body, requires] = transform_roots([body, requires], &mut names, generated)?;
            Some(Sentence::ContextAlias {
                body,
                requires,
                attributes: attributes.clone(),
            })
        }
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => None,
    }
}

/// The names of one sentence the minted names avoid. They are those of the sentence as received,
/// which no root has been rewritten in yet whenever the first name is minted, so they are read
/// then, and not at all for a sentence without an anonymous variable.
struct SentenceNames<'s> {
    sentence: &'s Sentence,
    fresh: Option<FreshNames>,
}

impl SentenceNames<'_> {
    fn mint(&mut self, sigil: &str) -> GeneratedVariableIdentity {
        let sentence = self.sentence;
        self.fresh
            .get_or_insert_with(|| FreshNames::for_sentence(sentence))
            .mint_generated(sigil)
    }
}

/// [`transform`] of each root in order, `None` when every root is left as it is.
fn transform_roots<const N: usize>(
    roots: [&Term; N],
    names: &mut SentenceNames<'_>,
    generated: &mut BTreeSet<GeneratedVariableIdentity>,
) -> Option<[Term; N]> {
    let transformed = roots.map(|root| transform(root, names, generated));
    if transformed.iter().all(Option::is_none) {
        return None;
    }
    let mut index = 0;
    Some(transformed.map(|root| {
        let root = root.unwrap_or_else(|| roots[index].clone());
        index += 1;
        root
    }))
}

/// `term` with every anonymous variable (`_`, `?_`, `!_`, `@_`) renamed to a fresh `_Gen` name
/// recorded in `generated`, in preorder; `None` when the result is `term` itself.
///
/// Every node is rebuilt as it is except an annotation, which is put back with
/// [`Term::with_metadata`]: that drops an empty annotation and merges an annotation into an
/// annotated child, so an annotation node is kept as it is only when its metadata is not empty,
/// its child is not annotated, and its child is kept.
// Invariant: each call recurses into the immediate subterms of `term`, so the finite `term`
// bounds the recursion.
fn transform(
    term: &Term,
    names: &mut SentenceNames<'_>,
    generated: &mut BTreeSet<GeneratedVariableIdentity>,
) -> Option<Term> {
    match term {
        Term::Annotated {
            term: inner,
            metadata,
        } => match transform(inner, names, generated) {
            None if *metadata != TermMetadata::default()
                && !matches!(**inner, Term::Annotated { .. }) =>
            {
                None
            }
            transformed => Some(
                transformed
                    .unwrap_or_else(|| (**inner).clone())
                    .with_metadata(metadata.clone()),
            ),
        },
        Term::Variable { name, sort } => {
            let prefix = anonymous_prefix(name)?;
            let identity = names.mint(prefix);
            let name = identity.name.clone();
            generated.insert(identity);
            Some(Term::Variable {
                name,
                sort: sort.clone(),
            })
        }
        Term::Rewrite { left, right } => {
            let new_left = transform(left, names, generated);
            let new_right = transform(right, names, generated);
            if new_left.is_none() && new_right.is_none() {
                return None;
            }
            Some(Term::Rewrite {
                left: Box::new(new_left.unwrap_or_else(|| (**left).clone())),
                right: Box::new(new_right.unwrap_or_else(|| (**right).clone())),
            })
        }
        Term::As { pattern, alias } => {
            let new_pattern = transform(pattern, names, generated);
            let new_alias = transform(alias, names, generated);
            if new_pattern.is_none() && new_alias.is_none() {
                return None;
            }
            Some(Term::As {
                pattern: Box::new(new_pattern.unwrap_or_else(|| (**pattern).clone())),
                alias: Box::new(new_alias.unwrap_or_else(|| (**alias).clone())),
            })
        }
        Term::Sequence(items) => transform_all(items, names, generated).map(Term::Sequence),
        Term::Apply { label, arguments } => {
            transform_all(arguments, names, generated).map(|arguments| Term::Apply {
                label: label.clone(),
                arguments,
            })
        }
        Term::InjectedLabel(_) | Term::Token { .. } => None,
    }
}

/// [`transform`] of each of `terms` in order, `None` when every one is `None`; the items before
/// the first change are copied only once one changes.
fn transform_all(
    terms: &[Term],
    names: &mut SentenceNames<'_>,
    generated: &mut BTreeSet<GeneratedVariableIdentity>,
) -> Option<Vec<Term>> {
    let mut transformed: Option<Vec<Term>> = None;
    for (index, term) in terms.iter().enumerate() {
        let new = transform(term, names, generated);
        match (&mut transformed, new) {
            (Some(items), new) => items.push(new.unwrap_or_else(|| term.clone())),
            (None, Some(new)) => {
                let mut items = Vec::with_capacity(terms.len());
                items.extend_from_slice(&terms[..index]);
                items.push(new);
                transformed = Some(items);
            }
            (None, None) => {}
        }
    }
    transformed
}

fn anonymous_prefix(name: &str) -> Option<&'static str> {
    match name {
        "_" => Some(""),
        "?_" => Some("?"),
        "!_" => Some("!"),
        "@_" => Some("@"),
        _ => None,
    }
}
