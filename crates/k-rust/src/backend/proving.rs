//! Claim selection, saved-proof bookkeeping, and proof orchestration.

use std::{
    collections::BTreeSet,
    error::Error,
    fs, io,
    path::{Path, PathBuf},
};

use k_rust_backend::{
    claim::{ReachabilityClaim, ReachabilityMode},
    definition::BackendDefinition,
    proof::{ProofError, ProofOptions, ProofResult, prove_claim},
    smt::SmtSolver,
};
use k_rust_kore::{
    kore::{
        ast::{Attributes, Definition, Module, Pattern, Sentence, Sort, Symbol},
        parser::parse_definition,
        printer::Printer,
    },
    names::KoreAttribute,
};

use super::BackendError;

#[doc(hidden)]
pub const SAVED_PROOFS_MODULE: &str =
    "haskell-backend-saved-claims-43943e50-f723-47cd-99fd-07104d664c6d";
const MODALITY_SAFE_PROOFS: &str = "kRustModalitySafeProofsV1";

fn modality_safe_proofs_attribute() -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: MODALITY_SAFE_PROOFS.into(),
            sort_parameters: Vec::new(),
        },
        arguments: Vec::new(),
    }
}

/// A proof identity is the emitted claim ID together with its reachability modality.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ProvenClaim {
    pub id: String,
    pub mode: ReachabilityMode,
}

impl ProvenClaim {
    pub fn from_claim(claim: &ReachabilityClaim) -> Self {
        Self {
            id: claim.attributes.unique_id.clone(),
            mode: claim.mode,
        }
    }

    pub fn supports(&self, claim: &Self) -> bool {
        self.id == claim.id
            && (self.mode == ReachabilityMode::AllPath || claim.mode == ReachabilityMode::OnePath)
    }
}

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
        if !module
            .attributes
            .0
            .contains(&modality_safe_proofs_attribute())
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "saved proof file predates modality-aware proof identities; remove it and rerun kprove",
            )
            .into());
        }
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

    pub fn proven_ids(&self, spec_module: &Module) -> BTreeSet<ProvenClaim> {
        spec_module
            .sentences
            .iter()
            .filter_map(|sentence| {
                let id = claim_proof_key(sentence)?;
                self.claims
                    .iter()
                    .any(|saved| saved_claim_supports(saved, sentence))
                    .then_some(id)
            })
            .collect()
    }

    pub fn save(
        &self,
        spec_module: &Module,
        proven_ids: &BTreeSet<ProvenClaim>,
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
pub fn saved_proof_definition(
    spec_module: &Module,
    proven_ids: &BTreeSet<ProvenClaim>,
) -> Definition {
    let declarations = spec_module
        .sentences
        .iter()
        .filter(|sentence| !matches!(sentence, Sentence::Axiom { .. } | Sentence::Claim { .. }))
        .cloned();
    let claims = spec_module
        .sentences
        .iter()
        .filter(|sentence| claim_proof_key(sentence).is_some_and(|id| proven_ids.contains(&id)))
        .cloned();
    Definition {
        attributes: Attributes::default(),
        modules: vec![Module {
            name: SAVED_PROOFS_MODULE.into(),
            sentences: declarations.chain(claims).collect(),
            attributes: Attributes(vec![modality_safe_proofs_attribute()]),
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

fn claim_proof_key(sentence: &Sentence) -> Option<ProvenClaim> {
    let (_, _, mode, _, _, _) = claim_body(sentence)?;
    Some(ProvenClaim {
        id: claim_unique_id(sentence)?,
        mode,
    })
}

type ClaimBody<'a> = (
    &'a [String],
    &'a Sort,
    ReachabilityMode,
    &'a [Sort],
    &'a Pattern,
    &'a Pattern,
);

fn claim_body(sentence: &Sentence) -> Option<ClaimBody<'_>> {
    let Sentence::Claim {
        parameters,
        pattern,
        ..
    } = sentence
    else {
        return None;
    };
    let Pattern::Implies { sort, left, right } = pattern.as_ref() else {
        return None;
    };
    let Pattern::Application { symbol, arguments } = right.as_ref() else {
        return None;
    };
    let mode = match symbol.name.as_str() {
        "weakExistsFinally" => ReachabilityMode::OnePath,
        "weakAlwaysFinally" => ReachabilityMode::AllPath,
        _ => return None,
    };
    let [right] = arguments.as_slice() else {
        return None;
    };
    Some((parameters, sort, mode, &symbol.sort_parameters, left, right))
}

fn saved_claim_supports(saved: &Sentence, target: &Sentence) -> bool {
    let (
        Some((saved_parameters, saved_sort, saved_mode, saved_mode_sorts, saved_left, saved_right)),
        Some((
            target_parameters,
            target_sort,
            target_mode,
            target_mode_sorts,
            target_left,
            target_right,
        )),
    ) = (claim_body(saved), claim_body(target))
    else {
        return false;
    };
    saved_parameters == target_parameters
        && saved_sort == target_sort
        && saved_mode_sorts == target_mode_sorts
        && saved_left == target_left
        && saved_right == target_right
        && (saved_mode == ReachabilityMode::AllPath || target_mode == ReachabilityMode::OnePath)
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
