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
        ast::{Attributes, Definition, KoreString, Module, Pattern, Sentence, Sort, Symbol},
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
/// disjunct was proven, recorded a claim under an id that also named another claim, and recorded
/// proofs that assumed unproven claims as circularities, so a V1 file may record a claim that is
/// not proven and is rejected. `V2` records a claim only once every disjunct is proven, never
/// under an id two different claims carry, only from a run whose every claim is proven, saved or
/// trusted, and together with the digest of the definition the proofs were made under
/// ([`SAVED_PROOFS_DEFINITION`]). A later change of what a saved proof certifies defines `V3`
/// and rejects `V2` files the same way.
const SAVED_PROOFS_FORMAT: &str = "kRustSavedProofsV2";

/// The prefix every k-rust saved-proof format marker from V2 on shares.
const SAVED_PROOFS_FORMAT_PREFIX: &str = "kRustSavedProofsV";

/// The saved-proof format markers k-rust wrote before [`SAVED_PROOFS_FORMAT`].
const EARLIER_SAVED_PROOFS_FORMATS: &[&str] = &["kRustModalitySafeProofsV1"];

/// The attribute of a V2 saved-proof module that holds the SHA-256 digest, in lowercase hex, of
/// the compiled definition the proofs were made under, without its claims
/// ([`definition_digest`]). Proofs are reused only under the same digest.
pub const SAVED_PROOFS_DEFINITION: &str = "kRustSavedProofsDefinition";

/// The unique id `k-rust-backend` gives a claim with neither a unique id nor a label, which every
/// such claim shares: it names no claim.
const UNKNOWN_UNIQUE_ID: &str = "UNKNOWN";

/// The digest saved proofs are bound to: the SHA-256 of the compiled definition's sentences
/// other than claims, as the compact printer prints each, module by module.
///
/// It covers every declaration and axiom of every module, the specification module's lemmas
/// included, with their attributes, and the module attributes, so a change to the semantics or
/// to a lemma gives another digest. It leaves out what does not change what a proof shows: the
/// claims, which the file records claim by claim; the order of modules and of sentences within
/// a module, which compilation does not fix; the specification module's name and attributes,
/// and the definition's attributes (the path it was compiled from). So a claim proven under one
/// specification module is reused under another over the same semantics.
pub fn definition_digest(definition: &Definition, spec_module: &str) -> String {
    use sha2::{Digest, Sha256};
    let printer = Printer::compact();
    let mut modules = definition
        .modules
        .iter()
        .map(|module| {
            let (name, attributes) = if module.name == spec_module {
                ("SPECIFICATION".to_owned(), String::new())
            } else {
                (
                    module.name.clone(),
                    module
                        .attributes
                        .0
                        .iter()
                        .map(|attribute| printer.print_pattern(attribute))
                        .collect::<Vec<_>>()
                        .join(","),
                )
            };
            let mut sentences = module
                .sentences
                .iter()
                .filter(|sentence| !matches!(sentence, Sentence::Claim { .. }))
                .map(|sentence| printer.print_sentence(sentence))
                .collect::<Vec<_>>();
            sentences.sort_unstable();
            (name, attributes, sentences)
        })
        .collect::<Vec<_>>();
    modules.sort_unstable();
    let mut hasher = Sha256::new();
    for (name, attributes, sentences) in modules {
        for part in std::iter::once(name)
            .chain(std::iter::once(attributes))
            .chain(sentences)
        {
            hasher.update((part.len() as u64).to_le_bytes());
            hasher.update(part.as_bytes());
        }
    }
    hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

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
    /// The saved proofs at `path`, for the definition whose [`definition_digest`] is
    /// `definition`.
    ///
    /// A missing file holds none. A file not in format [`SAVED_PROOFS_FORMAT`] is an error, which
    /// names the format it is in, so nothing is overwritten that a user did not remove. A file
    /// made under another definition holds proofs of that definition, which certify nothing here:
    /// they are ignored, with a warning, and the file is rewritten for this definition.
    pub fn load(path: Option<&Path>, definition: &str) -> Result<Self, Box<dyn Error>> {
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
        let file = parse_definition(&fs::read_to_string(path)?)?;
        let module = file
            .modules
            .iter()
            .find(|module| module.name == SAVED_PROOFS_MODULE)
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "saved proof file `{}` has no `{SAVED_PROOFS_MODULE}` module",
                        path.display()
                    ),
                )
            })?;
        let markers = module
            .attributes
            .0
            .iter()
            .filter_map(|attribute| match attribute {
                Pattern::Application { symbol, arguments } if arguments.is_empty() => {
                    Some(symbol.name.as_str())
                }
                _ => None,
            })
            .filter(|name| {
                name.starts_with(SAVED_PROOFS_FORMAT_PREFIX)
                    || EARLIER_SAVED_PROOFS_FORMATS.contains(name)
            })
            .collect::<Vec<_>>();
        if !markers.contains(&SAVED_PROOFS_FORMAT) {
            let found = match markers.first() {
                Some(marker) if EARLIER_SAVED_PROOFS_FORMATS.contains(marker) => {
                    format!("is in the earlier saved-proof format {marker}")
                }
                Some(marker) => format!(
                    "is in saved-proof format {marker}, which this kprove does not read (a later \
                     k-rust may have written it)"
                ),
                None => "carries no saved-proof format marker (it predates \
                         modality-aware proof identities, or is not a k-rust file)"
                    .to_owned(),
            };
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "saved proof file `{}` {found}; this kprove reads and writes \
                     {SAVED_PROOFS_FORMAT}; remove the file and rerun kprove",
                    path.display()
                ),
            )
            .into());
        }
        let digest = module
            .attributes
            .0
            .iter()
            .find_map(|attribute| match attribute {
                Pattern::Application { symbol, arguments }
                    if symbol.name == SAVED_PROOFS_DEFINITION =>
                {
                    match arguments.as_slice() {
                        [Pattern::String(digest)] => digest.as_utf8().ok(),
                        _ => None,
                    }
                }
                _ => None,
            });
        if digest != Some(definition) {
            eprintln!(
                "warning: saved proof file `{}` was written for another compiled definition \
                 (digest {}, this one {definition}); its proofs are not reused, and the file is \
                 rewritten with this run's",
                path.display(),
                digest.unwrap_or("missing"),
            );
            return Ok(Self {
                path: Some(path.to_owned()),
                claims: Vec::new(),
            });
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

    /// The proof identities of the claims of `spec_module` a saved proof supports, among those
    /// whose id is in `reusable` ([`reusable_proof_ids`]).
    pub fn proven_ids(
        &self,
        spec_module: &Module,
        reusable: &BTreeSet<String>,
    ) -> BTreeSet<ProvenClaim> {
        spec_module
            .sentences
            .iter()
            .filter_map(|sentence| {
                let id = claim_proof_key(sentence)?;
                (reusable.contains(&id.id)
                    && self
                        .claims
                        .iter()
                        .any(|saved| saved_claim_supports(saved, sentence)))
                .then_some(id)
            })
            .collect()
    }

    /// Write the claims of `spec_module` whose identity is in `proven_ids`, under the definition
    /// digest `definition`.
    pub fn save(
        &self,
        spec_module: &Module,
        proven_ids: &BTreeSet<ProvenClaim>,
        definition: &str,
    ) -> Result<(), Box<dyn Error>> {
        let Some(path) = &self.path else {
            return Ok(());
        };
        let file = saved_proof_definition(spec_module, proven_ids, definition);
        fs::write(path, Printer::pretty(100).print_definition(&file))?;
        Ok(())
    }
}

#[doc(hidden)]
pub fn saved_proof_definition(
    spec_module: &Module,
    proven_ids: &BTreeSet<ProvenClaim>,
    definition: &str,
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
            attributes: Attributes(vec![
                saved_proofs_format_attribute(),
                Pattern::Application {
                    symbol: Symbol {
                        name: SAVED_PROOFS_DEFINITION.into(),
                        sort_parameters: Vec::new(),
                    },
                    arguments: vec![Pattern::String(KoreString::from_bytes(
                        definition.as_bytes(),
                    ))],
                },
            ]),
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
    left.attributes.sentence == right.attributes.sentence
}

/// The unique ids a proof may be recorded, reused and saved under: those that name one claim
/// body. An id is the claim's `UNIQUE'Unds'ID`, else its label, else `UNKNOWN`; K source gives
/// each claim text its own, but a claim written in KORE may carry none (`UNKNOWN`, shared by
/// every such claim) or another claim's label. An id whose claim sentences do not all have one
/// body (the same disjuncts, each with the same left-hand side, right-hand sides and
/// existentials; the modality may differ, as `ProvenClaim::supports` reads it) names no claim,
/// and neither does `UNKNOWN`.
pub fn reusable_proof_ids(claims: &[ReachabilityClaim]) -> BTreeSet<String> {
    type Body<'a> = Vec<(
        &'a k_rust_backend::rewrite::Pattern,
        &'a [k_rust_backend::rewrite::Pattern],
        &'a BTreeSet<k_rust_backend::term::Variable>,
    )>;
    let mut sentences = std::collections::BTreeMap::<usize, (&str, Body<'_>)>::new();
    for claim in claims {
        sentences
            .entry(claim.attributes.sentence)
            .or_insert_with(|| (claim.attributes.unique_id.as_str(), Vec::new()))
            .1
            .push((&claim.lhs, claim.rhs.as_slice(), &claim.existentials));
    }
    let mut bodies = std::collections::BTreeMap::<&str, Vec<&Body<'_>>>::new();
    for (id, body) in sentences.values() {
        bodies.entry(id).or_default().push(body);
    }
    bodies
        .into_iter()
        .filter(|(id, bodies)| {
            *id != UNKNOWN_UNIQUE_ID && bodies.windows(2).all(|pair| pair[0] == pair[1])
        })
        .map(|(id, _)| id.to_owned())
        .collect()
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
        claims if claims.iter().all(|claim| same_sentence(claim, &claims[0])) => {
            Err(BackendError::new(format!(
                "the selected module's one claim has {} left-hand disjuncts, which a proof \
                 request proves one at a time; select each by its index: {}",
                claims.len(),
                (0..claims.len())
                    .map(|index| format!("#{index}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )))
        }
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
