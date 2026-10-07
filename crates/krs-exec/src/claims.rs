//! The claim catalog and kprove's claim-label resolution.

use std::collections::BTreeSet;

use k_rust::kore::{
    ast::{Attributes, Pattern, Sentence},
    parser::parse_definition,
};
use krs_k_rust::{Author, SentenceProvenance};

use crate::{
    ExecError,
    origin::Origins,
    report::{ClaimInfo, Modality},
};

/// The generated spec module that holds a definition's loose claims in emitted `spec.k`.
pub(crate) fn spec_module(main_module: &str) -> String {
    format!("{main_module}-SPEC")
}

/// Every labelled claim of the compiled definition, spelled as `kprove --claims` spells it.
///
/// The native definition keeps semantics and claims in the main module, so a backend label is
/// `<MAIN>.label`; emitted `spec.k` holds the same claim as `<MAIN>-SPEC.label`.
pub(crate) fn catalog(
    definition_kore: &str,
    main_module: &str,
    provenance: &SentenceProvenance,
    origins: &mut Origins,
) -> Result<Vec<ClaimInfo>, ExecError> {
    let definition = parse_definition(definition_kore)
        .map_err(|error| ExecError::Result(format!("compiled KORE does not parse: {error}")))?;
    let spec = spec_module(main_module);
    let native_prefix = format!("{main_module}.");
    let mut claims = Vec::new();
    for module in &definition.modules {
        for sentence in &module.sentences {
            let Sentence::Claim {
                attributes,
                pattern,
                ..
            } = sentence
            else {
                continue;
            };
            let Some(backend_label) = string_attribute(attributes, "label") else {
                continue;
            };
            let local = backend_label
                .strip_prefix(&native_prefix)
                .unwrap_or(backend_label);
            let origin = string_attribute(attributes, "UNIQUE'Unds'ID")
                .and_then(|id| provenance.get(id))
                .and_then(|provenance| {
                    provenance.authors().iter().find_map(|author| match author {
                        Author::Krs { origin, .. } => Some(origin),
                        Author::Builtin { .. } => None,
                    })
                })
                .and_then(|origin| origins.span(origin));
            claims.push(ClaimInfo {
                label: format!("{spec}.{local}"),
                module: spec.clone(),
                modality: modality(pattern),
                origin,
                backend_label: backend_label.to_owned(),
            });
        }
    }
    claims.sort_by(|left, right| left.label.cmp(&right.label));
    claims.dedup_by(|left, right| left.label == right.label);
    Ok(claims)
}

fn string_attribute<'a>(attributes: &'a Attributes, name: &str) -> Option<&'a str> {
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == name => {
            match arguments.as_slice() {
                [Pattern::String(value)] => value.as_utf8().ok(),
                _ => None,
            }
        }
        _ => None,
    })
}

fn modality(pattern: &Pattern) -> Modality {
    let mut stack = vec![pattern];
    while let Some(pattern) = stack.pop() {
        match pattern {
            Pattern::Application { symbol, arguments } => {
                if symbol.name == "weakExistsFinally" {
                    return Modality::OnePath;
                }
                if symbol.name == "weakAlwaysFinally" {
                    return Modality::AllPath;
                }
                stack.extend(arguments);
            }
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. } => {
                stack.push(left);
                stack.push(right);
            }
            Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
                stack.extend(arguments);
            }
            Pattern::Not { argument, .. } | Pattern::Next { argument, .. } => stack.push(argument),
            Pattern::Exists { body, .. }
            | Pattern::Forall { body, .. }
            | Pattern::Mu { body, .. }
            | Pattern::Nu { body, .. } => stack.push(body),
            _ => {}
        }
    }
    Modality::AllPath
}

/// Resolve requested labels by exact match or unique `.`-suffix, as kprove's `--claims` does.
///
/// No request selects every claim. The result lists claim indices in request order without duplicates.
pub(crate) fn select(claims: &[ClaimInfo], requested: &[String]) -> Result<Vec<usize>, ExecError> {
    if requested.is_empty() {
        return Ok((0..claims.len()).collect());
    }
    let mut selected = Vec::new();
    let mut seen = BTreeSet::new();
    for request in requested {
        let index = resolve(claims, request)?;
        if seen.insert(index) {
            selected.push(index);
        }
    }
    Ok(selected)
}

fn resolve(claims: &[ClaimInfo], requested: &str) -> Result<usize, ExecError> {
    if let Some(index) = claims
        .iter()
        .position(|claim| claim.label == requested || claim.backend_label == requested)
    {
        return Ok(index);
    }
    let matches = suffix_matches(claims, requested);
    match matches.as_slice() {
        [index] => Ok(*index),
        [] => Err(ExecError::UnknownClaim {
            requested: requested.to_owned(),
            suggestion: suggestion(claims, requested),
        }),
        several => Err(ExecError::AmbiguousClaim {
            requested: requested.to_owned(),
            matches: several
                .iter()
                .map(|index| claims[*index].label.clone())
                .collect(),
        }),
    }
}

fn suffix_matches(claims: &[ClaimInfo], requested: &str) -> Vec<usize> {
    let suffix = format!(".{requested}");
    claims
        .iter()
        .enumerate()
        .filter(|(_, claim)| claim.label.ends_with(&suffix))
        .map(|(index, _)| index)
        .collect()
}

/// A did-you-mean for a label written as a Rust identifier (`eval_add` for `eval-add`) or in another case.
fn suggestion(claims: &[ClaimInfo], requested: &str) -> Option<String> {
    let kebab = requested.replace('_', "-");
    if let [index] = suffix_matches(claims, &kebab).as_slice() {
        return Some(claims[*index].label.clone());
    }
    let lowered = kebab.to_ascii_lowercase();
    let matches = claims
        .iter()
        .filter(|claim| {
            claim
                .label
                .rsplit_once('.')
                .is_some_and(|(_, local)| local.to_ascii_lowercase() == lowered)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [claim] => Some(claim.label.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{select, suggestion};
    use crate::{ExecError, report::ClaimInfo, report::Modality};

    fn claims() -> Vec<ClaimInfo> {
        ["eval-add", "foo-reaches-bar", "branching"]
            .into_iter()
            .map(|local| ClaimInfo {
                label: format!("MAIN-SPEC.{local}"),
                module: "MAIN-SPEC".to_owned(),
                modality: Modality::AllPath,
                origin: None,
                backend_label: format!("MAIN.{local}"),
            })
            .collect()
    }

    #[test]
    fn resolves_exact_suffix_and_backend_labels_in_request_order() {
        let claims = claims();
        let requested = ["branching", "MAIN-SPEC.eval-add", "MAIN.branching"]
            .map(str::to_owned)
            .to_vec();
        assert_eq!(select(&claims, &requested).unwrap(), vec![2, 0]);
        assert_eq!(select(&claims, &[]).unwrap(), vec![0, 1, 2]);
    }

    #[test]
    fn unknown_labels_suggest_the_kebab_label() {
        let claims = claims();
        let error = select(&claims, &["eval_add".to_owned()]).unwrap_err();
        assert!(
            matches!(&error, ExecError::UnknownClaim { suggestion: Some(label), .. } if label == "MAIN-SPEC.eval-add"),
            "{error:?}"
        );
        assert_eq!(
            error.to_string(),
            "no claim has label `eval_add`; did you mean `MAIN-SPEC.eval-add`?"
        );
        assert_eq!(suggestion(&claims, "missing"), None);
    }

    #[test]
    fn ambiguous_suffixes_list_every_match() {
        let mut claims = claims();
        claims.push(ClaimInfo {
            label: "OTHER-SPEC.branching".to_owned(),
            module: "OTHER-SPEC".to_owned(),
            modality: Modality::OnePath,
            origin: None,
            backend_label: "OTHER.branching".to_owned(),
        });
        let error = select(&claims, &["branching".to_owned()]).unwrap_err();
        assert_eq!(
            error.to_string(),
            "claim label `branching` is ambiguous; matches `MAIN-SPEC.branching`, `OTHER-SPEC.branching`"
        );
    }
}
