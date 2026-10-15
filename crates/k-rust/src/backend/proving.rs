//! Claim selection, saved-proof bookkeeping, and proof orchestration.

use std::{
    collections::BTreeSet,
    error::Error,
    fs, io,
    path::{Path, PathBuf},
};

use k_rust_backend::evaluation::{EvaluationMode, with_evaluation};
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
/// The version of the saved-proof format, which a saved-proof file carries as an attribute of its
/// module and must carry to be read.
///
/// `kRustModalitySafeProofsV1` keyed a proof by its claim's unique id and modality, but recorded a
/// claim with a left-hand disjunction, one claim per disjunct under one id, as soon as its first
/// disjunct was proven, so a V1 file may record a claim that is not proven and is rejected. `V2`
/// records a claim only once every disjunct is proven. A later change of what a saved proof
/// certifies defines `V3` and rejects `V2` files the same way.
const SAVED_PROOFS_FORMAT: &str = "kRustSavedProofsV2";

fn saved_proofs_format_attribute() -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: SAVED_PROOFS_FORMAT.into(),
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
        // The disjuncts of one claim share its label, so a label counts once: only distinct
        // claims make a request ambiguous.
        let matches = labels
            .iter()
            .filter(|label| label.ends_with(&suffix))
            .collect::<BTreeSet<_>>()
            .into_iter()
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
            .contains(&saved_proofs_format_attribute())
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "saved proof file predates the saved-proof format {SAVED_PROOFS_FORMAT}, which \
                     records a claim with a left-hand disjunction only once every disjunct is \
                     proven; remove it and rerun kprove"
                ),
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
            attributes: Attributes(vec![saved_proofs_format_attribute()]),
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

/// Whether `left` and `right` are disjuncts of one claim sentence: a sentence with a left-hand
/// disjunction is internalized as one claim per disjunct, each with the sentence's attributes
/// (label, unique id, origin) and modality. The unique id alone does not tell sentences apart: two
/// claims with one body, one all-path and one one-path, share it.
fn same_sentence(left: &ReachabilityClaim, right: &ReachabilityClaim) -> bool {
    left.attributes == right.attributes && left.mode == right.mode
}

/// The position of each claim among the disjuncts of its claim sentence, as (1-based index,
/// count): the disjuncts of a sentence are internalized in order and consecutively.
pub fn disjunct_positions(claims: &[ReachabilityClaim]) -> Vec<(usize, usize)> {
    let mut positions = Vec::with_capacity(claims.len());
    let mut start = 0;
    while start < claims.len() {
        let count = claims[start..]
            .iter()
            .take_while(|claim| same_sentence(claim, &claims[start]))
            .count();
        positions.extend((1..=count).map(|index| (index, count)));
        start += count;
    }
    positions
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
                .reachability_claims()
                .get(index)
                .map(|claim| (index, claim))
                .ok_or_else(|| {
                    BackendError::new(format!("no reachability claim at index {index}"))
                });
        }
        // A claim with a left-hand disjunction is one claim per disjunct under one label and
        // unique id, and it holds only if every disjunct does; a request proves one claim, so a
        // name that selects several disjuncts is refused with their `#index` selectors.
        let named = select_claims(definition, selector)?;
        return match named.as_slice() {
            [claim] => Ok(*claim),
            disjuncts => Err(BackendError::new(format!(
                "claim {selector:?} has {} left-hand disjuncts, which a proof request proves one \
                 at a time; select each by its index: {}",
                disjuncts.len(),
                disjuncts
                    .iter()
                    .map(|(index, _)| format!("#{index}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))),
        };
    }
    match definition.reachability_claims() {
        [claim] => Ok((0, claim)),
        [] => Err(BackendError::new(
            "the selected module contains no reachability claims",
        )),
        claims => Err(BackendError::new(format!(
            "the selected module contains {} reachability claims; select one by label or #index",
            claims.len()
        ))),
    }
}

/// Every claim `selector` names: the claim at `#index`, or each disjunct of the first claim
/// sentence with that label or unique id.
pub(super) fn select_claims<'a>(
    definition: &'a BackendDefinition,
    selector: &str,
) -> Result<Vec<(usize, &'a ReachabilityClaim)>, BackendError> {
    if let Some(index) = selector
        .strip_prefix('#')
        .and_then(|value| value.parse().ok())
    {
        return definition
            .reachability_claims()
            .get(index)
            .map(|claim| vec![(index, claim)])
            .ok_or_else(|| BackendError::new(format!("no reachability claim at index {index}")));
    }
    let claims = definition.reachability_claims();
    let Some(first) = claims.iter().find(|claim| {
        claim.attributes.label.as_deref() == Some(selector)
            || claim.attributes.unique_id == selector
    }) else {
        return Err(BackendError::new(format!(
            "no reachability claim named {selector:?}"
        )));
    };
    Ok(claims
        .iter()
        .enumerate()
        .filter(|(_, claim)| same_sentence(claim, first))
        .collect())
}

/// Run the backend proof algorithm; selection and presentation remain caller contracts.
pub fn run_claim(
    definition: &BackendDefinition,
    claim: &ReachabilityClaim,
    circularities: &[&ReachabilityClaim],
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> Result<ProofResult, ProofError> {
    // A proof route: it evaluates only consequences of the definition, whatever scope the
    // caller runs it in (`k_rust_backend::evaluation`).
    with_evaluation(EvaluationMode::Proof, || {
        prove_claim(definition, claim, circularities, options, solver)
    })
}
