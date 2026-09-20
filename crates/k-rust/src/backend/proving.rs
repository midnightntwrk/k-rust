//! Claim selection, saved-proof bookkeeping, and proof orchestration (S16 and S17).

use std::{
    collections::BTreeSet,
    error::Error,
    fs, io,
    path::{Path, PathBuf},
};

use k_rust_backend::{
    claim::ReachabilityClaim,
    definition::BackendDefinition,
    proof::{ProofError, ProofOptions, ProofResult, prove_claim},
    smt::SmtSolver,
};
use k_rust_kore::{
    kore::{
        ast::{Attributes, Definition, Module, Sentence},
        parser::parse_definition,
        printer::Printer,
    },
    names::KoreAttribute,
};

use super::BackendError;

#[doc(hidden)]
pub const SAVED_PROOFS_MODULE: &str =
    "haskell-backend-saved-claims-43943e50-f723-47cd-99fd-07104d664c6d";

/// K's proof-module filter, with the CLI's exact-or-unique-suffix label resolution.
#[derive(Debug, Default)]
pub struct ClaimFilter {
    pub selected: Vec<String>,
    pub excluded: Vec<String>,
    pub trusted: Vec<String>,
}

pub fn filter_claims(
    claims: &[ReachabilityClaim],
    filter: &ClaimFilter,
) -> Result<Vec<ReachabilityClaim>, Box<dyn Error>> {
    let labels = claims
        .iter()
        .filter_map(|claim| claim.attributes.label.clone())
        .collect::<Vec<_>>();
    let selected = resolve_claim_labels(&labels, &filter.selected)?;
    let excluded = resolve_claim_labels(&labels, &filter.excluded)?;
    let trusted = resolve_claim_labels(&labels, &filter.trusted)?;
    if let Some(label) = selected.intersection(&excluded).next() {
        return Err(format!("label `{label}` used for both --claim and --exclude").into());
    }

    Ok(claims
        .iter()
        .filter_map(|claim| {
            let Some(label) = &claim.attributes.label else {
                return Some(claim.clone());
            };
            if excluded.contains(label) || (!selected.is_empty() && !selected.contains(label)) {
                return None;
            }
            let mut claim = claim.clone();
            if trusted.contains(label) {
                claim.attributes.trusted = true;
            }
            Some(claim)
        })
        .collect())
}

pub fn resolve_claim_labels(
    labels: &[String],
    requested: &[String],
) -> Result<BTreeSet<String>, Box<dyn Error>> {
    let mut selected = BTreeSet::new();
    // Invariant: selected contains the exact resolved label for every preceding request.
    for requested in requested {
        if labels.iter().any(|label| label == requested) {
            selected.insert(requested.clone());
            continue;
        }
        let suffix = format!(".{requested}");
        let matches = labels
            .iter()
            .filter(|label| label.ends_with(&suffix))
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [] => {
                return Err(format!("no modal reachability claim has label `{requested}`").into());
            }
            [label] => {
                selected.insert((**label).clone());
            }
            _ => {
                return Err(format!(
                    "claim label `{requested}` is ambiguous; matches {}",
                    matches
                        .iter()
                        .map(|label| format!("`{label}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
                .into());
            }
        }
    }
    Ok(selected)
}

/// The optional saved-proof ledger and its fixed wire-format module.
pub struct SavedProofs {
    path: Option<PathBuf>,
    claims: Vec<Sentence>,
}

impl SavedProofs {
    pub fn load(path: Option<&Path>) -> Result<Self, Box<dyn Error>> {
        let Some(path) = path else {
            return Ok(Self {
                path: None,
                claims: Vec::new(),
            });
        };
        if !path.exists() {
            return Ok(Self {
                path: Some(path.to_owned()),
                claims: Vec::new(),
            });
        }
        let definition = parse_definition(&fs::read_to_string(path)?)?;
        let module = definition
            .modules
            .iter()
            .find(|module| module.name == SAVED_PROOFS_MODULE)
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("saved proof file has no `{SAVED_PROOFS_MODULE}` module"),
                )
            })?;
        Ok(Self {
            path: Some(path.to_owned()),
            claims: module
                .sentences
                .iter()
                .filter(|sentence| matches!(sentence, Sentence::Claim { .. }))
                .cloned()
                .collect(),
        })
    }

    pub fn proven_ids(&self, spec_module: &Module) -> BTreeSet<String> {
        spec_module
            .sentences
            .iter()
            .filter_map(|sentence| {
                let id = claim_unique_id(sentence)?;
                self.claims
                    .iter()
                    .any(|saved| same_claim(sentence, saved))
                    .then_some(id)
            })
            .collect()
    }

    pub fn save(
        &self,
        spec_module: &Module,
        proven_ids: &BTreeSet<String>,
    ) -> Result<(), Box<dyn Error>> {
        let Some(path) = &self.path else {
            return Ok(());
        };
        let definition = saved_proof_definition(spec_module, proven_ids);
        fs::write(path, Printer::pretty(100).print_definition(&definition))?;
        Ok(())
    }
}

#[doc(hidden)]
pub fn saved_proof_definition(spec_module: &Module, proven_ids: &BTreeSet<String>) -> Definition {
    let declarations = spec_module
        .sentences
        .iter()
        .filter(|sentence| !matches!(sentence, Sentence::Axiom { .. } | Sentence::Claim { .. }))
        .cloned();
    let claims = spec_module
        .sentences
        .iter()
        .filter(|sentence| claim_unique_id(sentence).is_some_and(|id| proven_ids.contains(&id)))
        .cloned();
    Definition {
        attributes: Attributes::default(),
        modules: vec![Module {
            name: SAVED_PROOFS_MODULE.into(),
            sentences: declarations.chain(claims).collect(),
            attributes: Attributes::default(),
        }],
    }
}

#[doc(hidden)]
pub fn claim_unique_id(sentence: &Sentence) -> Option<String> {
    let Sentence::Claim { attributes, .. } = sentence else {
        return None;
    };
    attributes
        .string(KoreAttribute::UniqueId)
        .ok()
        .flatten()
        .or_else(|| attributes.string(KoreAttribute::Label).ok().flatten())
        .map(str::to_owned)
}

fn same_claim(left: &Sentence, right: &Sentence) -> bool {
    let (
        Sentence::Claim {
            parameters: left_parameters,
            pattern: left_pattern,
            ..
        },
        Sentence::Claim {
            parameters: right_parameters,
            pattern: right_pattern,
            ..
        },
    ) = (left, right)
    else {
        return false;
    };
    left_parameters == right_parameters && left_pattern == right_pattern
}

pub(super) fn select_claim<'a>(
    definition: &'a BackendDefinition,
    selector: Option<&str>,
) -> Result<(usize, &'a ReachabilityClaim), BackendError> {
    if let Some(selector) = selector {
        if let Some(index) = selector
            .strip_prefix('#')
            .and_then(|value| value.parse().ok())
        {
            return definition
                .reachability_claims
                .get(index)
                .map(|claim| (index, claim))
                .ok_or_else(|| BackendError(format!("no reachability claim at index {index}")));
        }
        return definition
            .reachability_claims
            .iter()
            .enumerate()
            .find(|(_, claim)| {
                claim.attributes.label.as_deref() == Some(selector)
                    || claim.attributes.unique_id == selector
            })
            .ok_or_else(|| BackendError(format!("no reachability claim named {selector:?}")));
    }
    match definition.reachability_claims.as_slice() {
        [claim] => Ok((0, claim)),
        [] => Err(BackendError(
            "the selected module contains no reachability claims".into(),
        )),
        claims => Err(BackendError(format!(
            "the selected module contains {} reachability claims; select one by label or #index",
            claims.len()
        ))),
    }
}

/// Run the backend proof algorithm; selection and presentation remain caller contracts.
pub fn run_claim(
    definition: &BackendDefinition,
    claim: &ReachabilityClaim,
    circularities: &[&ReachabilityClaim],
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> Result<ProofResult, ProofError> {
    prove_claim(definition, claim, circularities, options, solver)
}
