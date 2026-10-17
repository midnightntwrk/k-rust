//! Per-definition corpus admission, campaign execution and atomic publication.
//!
//! A store is honoured without re-deriving its verdicts (resume, summary), so every record that
//! decides what it reports is bound to the build that wrote it (packet CACHE-ID-fix-1; kink-campaign
//! `identity`): each index entry and admission record carries its writer's `kink_build`, outside
//! the campaign report's bytes, and each index entry the [`RunOptions`] its campaign ran with
//! (`run_options`). Resume refuses an entry of another build, of other run options or under
//! another semantics identity; summary does the same, and reads an admission record of another
//! build as missing. Campaign reports, artifacts and inputs stay build-independent.

use crate::{
    admission::{AdmissionRecord, AdmissionRefusal, admit_definition},
    manifest::CorpusManifest,
    store::{Store, StoreError, time_bound_fired},
};
use k_rust::{kompile::CompileOptions, kore::ast::Pattern};
use kink_campaign::{
    Campaign, CampaignFailureKind, CampaignOptions, ManifestOperator, MultiManifestInput,
    RunOptions, campaign_manifest_multi_with_budget, campaign_report_multi, run_campaign_multi,
};
use kink_native::{NativeValidator, execution::SolverProfile};
use kink_patch::{
    CAMPAIGN_MANIFEST_DOMAIN, OperatorSpec, Sha256Digest, canonical_json, payload_digest,
    resolve_universe, sha256,
};
use kink_pattern::ExecutionTerminalKind;
use serde_json::{Value, json};
use std::{fs, path::Path};

pub const CLASSIFIER: &str = "kink-corpus/all-normal/v1";

/// The run options of every campaign kink-corpus runs and stores (packet CACHE-ID-fix-1, CACHE-ID
/// review minor 4): each index entry records them ([`run_options_value`]), and resume and summary
/// refuse an entry made with others. The definition campaign, the admission's baseline-only run
/// and `replay-check` all run with these (re-pin L1-2-land; CACHE-ID review 2 minor 1). They are
/// the defaults: state sets, no work budget, no one-sided kill (kink-corpus sets no work budget,
/// so the rule could not fire).
#[must_use]
pub fn corpus_run_options() -> RunOptions {
    RunOptions::default()
}

/// The `run_options` member of an index entry: every run option, kink-campaign
/// [`RunOptions::value`] (`{result_modality, work, one_sided}`, `work` null without a work
/// budget, else `{factor, floor}`), which destructures every field, so a new option is recorded
/// or does not compile. An entry written before re-pin L1-2-land lacks `one_sided` and is refused.
#[must_use]
pub fn run_options_value(options: &RunOptions) -> Value {
    options.value()
}

/// kink's build identity, without which kink-corpus neither resumes nor writes a store: a store
/// is honoured only by the build that wrote it.
///
/// # Errors
/// When the running executable cannot be read.
pub fn corpus_build() -> Result<Sha256Digest, StoreError> {
    kink_campaign::kink_build().map_err(|e| {
        StoreError::Invalid(format!(
            "kink's build identity is unknown ({e}): kink-corpus neither resumes nor writes a \
             store without it"
        ))
    })
}

/// An admission record as the store holds it: the record and its writer's build (`kink_build`).
#[must_use]
pub fn stored_admission(record: &AdmissionRecord, build: Sha256Digest) -> Value {
    let mut value = record.value();
    value["kink_build"] = json!(build.to_string());
    value
}
pub fn all_normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

#[derive(Clone, Debug)]
pub struct DefinitionOutcome {
    pub admission: Value,
    pub campaign: Option<Value>,
    pub resumed: bool,
}

pub fn run_definition(
    workspace: &Path,
    manifest: &CorpusManifest,
    id: &str,
    store: &Store,
) -> Result<DefinitionOutcome, StoreError> {
    let build = corpus_build()?;
    // The shared declaration is the first file of every call, including resumptions.
    store.ensure_manifest(manifest)?;
    let digest = manifest.digest();
    let profile = SolverProfile::BUILD.name();
    let admission_path = store.admission_path(digest, profile, id)?;
    if !manifest.definitions().iter().any(|d| d.id == id) {
        return Err(StoreError::Invalid("definition is not listed".into()));
    }
    if let Some(outcome) = resume(store, digest, profile, id, &admission_path, build)? {
        return Ok(outcome);
    }
    let mut admission = admit_definition(manifest, id, workspace);
    let Some(admitted) = admission.admitted else {
        return store_refusal(store, &admission_path, &admission.record, build);
    };
    let d = manifest
        .definitions()
        .iter()
        .find(|d| d.id == id)
        .expect("listed definition");
    store.ensure_inputs(digest, d, &admitted.loaded.root)?;
    let rebuilt = store.rebuild_tests(digest, id, &admitted.loaded.baseline)?;
    if rebuilt != admitted.tests {
        return Err(StoreError::Invalid(
            "stored tests differ from admission".into(),
        ));
    }
    let config = manifest.campaign();
    let validator = NativeValidator::bind(admitted.loaded.baseline, CompileOptions::default());
    let universe = resolve_universe(validator.baseline(), manifest.universe());
    let cap = usize::try_from(config.max_candidates_per_spec)
        .map_err(|_| StoreError::Invalid("candidate maximum does not fit usize".into()))?;
    let specs = manifest
        .operators()
        .iter()
        .map(|spec| (spec, cap))
        .collect::<Vec<_>>();
    let budget_mutants = config.budget_mutants.as_ref();
    let generations = OperatorSpec::generate_all(
        validator.baseline(),
        &universe,
        &specs,
        budget_mutants.map(|b| (b.per_spec_max, b.total_max, b.seed.as_slice())),
    )
    .map_err(|e| StoreError::Invalid(e.to_string()))?;
    let mut budget = config.budget;
    if let Some(depth) = d.max_depth {
        budget.max_depth = Some(depth);
    }
    let module = k_rust::kast::identifier::encode(&d.main_module);
    let campaign = Campaign {
        validator: &validator,
        module: &module,
        observation: &d.observation,
        classify: &all_normal,
        tests: &admitted.tests,
        budget,
    };
    let operators = manifest
        .operators()
        .iter()
        .map(ManifestOperator::Spec)
        .collect::<Vec<_>>();
    let declaration = campaign_manifest_multi_with_budget(
        &MultiManifestInput {
            campaign: &campaign,
            generations: &generations,
            schedule: config.schedule,
            selection: config.selection,
            operators: &operators,
            classifier: CLASSIFIER,
            universe: Some(&universe),
        },
        budget_mutants,
    )
    .map_err(|e| StoreError::Invalid(e.to_string()))?;
    let options = corpus_run_options();
    let run = match run_campaign_multi(
        &campaign,
        &generations,
        &CampaignOptions {
            schedule: config.schedule,
            selection: config.selection,
            share_evidence: true,
            run: options,
        },
    ) {
        Ok(run) => run,
        Err(e) => {
            admission.record.refusal = Some(AdmissionRefusal {
                stage: "baseline".into(),
                reason: failure_kind(e.kind()).into(),
                detail: e.to_string(),
            });
            return store_refusal(store, &admission_path, &admission.record, build);
        }
    };
    let report = campaign_report_multi(&declaration, &campaign, &generations, &run)
        .map_err(|e| StoreError::Invalid(e.to_string()))?;
    let text = report.text();
    // The writer's build and run options sit in the index entry, outside the report's bytes, so
    // the report stays build-independent (packet CACHE-ID-fix-1).
    let entry = json!({"manifest_sha256":declaration.digest().to_string(),
        "report_sha256":sha256(text.as_bytes()).to_string(),"time_bound_fired":time_bound_fired(report.value()),
        "kink_build":build.to_string(),"run_options":run_options_value(&options)});
    let root = store.profile_path(digest, profile);
    let admission = stored_admission(&admission.record, build);
    store.write_json(&admission_path, &admission)?;
    // Use the very artifact named by the campaign declaration.
    store.write_text(
        &root.join(format!(
            "semantic-input/{}.json",
            declaration.baseline_input().digest()
        )),
        declaration.baseline_input().text(),
    )?;
    store.write_text(
        &root.join(format!("campaigns/{}.json", declaration.digest())),
        &text,
    )?;
    let mut index = store.read_index(digest, profile)?;
    index[id] = entry.clone();
    store.write_json(&root.join("index.json"), &index)?;
    Ok(DefinitionOutcome {
        admission,
        campaign: Some(entry),
        resumed: false,
    })
}
fn store_refusal(
    store: &Store,
    path: &Path,
    record: &AdmissionRecord,
    build: Sha256Digest,
) -> Result<DefinitionOutcome, StoreError> {
    let admission = stored_admission(record, build);
    store.write_json(path, &admission)?;
    Ok(DefinitionOutcome {
        admission,
        campaign: None,
        resumed: false,
    })
}
fn failure_kind(kind: CampaignFailureKind) -> &'static str {
    match kind {
        CampaignFailureKind::InvalidManifest => "invalid-manifest",
        CampaignFailureKind::InvalidDeclaration => "invalid-declaration",
        CampaignFailureKind::ForeignGeneration => "foreign-generation",
        CampaignFailureKind::FabricatedSkip => "fabricated-skip",
        CampaignFailureKind::BaselineInvalid => "baseline-invalid",
        CampaignFailureKind::BaselineOracleFailed => "baseline-oracle-failed",
        CampaignFailureKind::BaselineError => "baseline-error",
    }
}
fn resume(
    store: &Store,
    digest: Sha256Digest,
    profile: &str,
    id: &str,
    admission_path: &Path,
    build: Sha256Digest,
) -> Result<Option<DefinitionOutcome>, StoreError> {
    let index = store.read_index(digest, profile)?;
    let Some(entry) = index.get(id) else {
        return Ok(None);
    };
    let manifest_digest = entry["manifest_sha256"]
        .as_str()
        .ok_or_else(|| StoreError::Invalid("index manifest digest".into()))?;
    let parsed: Sha256Digest = Sha256Digest::parse(manifest_digest)
        .ok_or_else(|| StoreError::Invalid("index manifest digest".into()))?;
    let report_path = store
        .profile_path(digest, profile)
        .join(format!("campaigns/{parsed}.json"));
    if !admission_path.exists() || !report_path.exists() {
        return Ok(None);
    }
    let admission = store.read_json(admission_path)?;
    let report = store.read_json(&report_path)?;
    if admission["definition"] != id
        || admission["outcome"] != "admitted"
        || report["manifest_sha256"] != manifest_digest
        || report["manifest"]["profile"] != profile
        || payload_digest(
            CAMPAIGN_MANIFEST_DOMAIN,
            canonical_json(&report["manifest"]).as_bytes(),
        )
        .to_string()
            != manifest_digest
        || sha256(canonical_json(&report).as_bytes()).to_string() != entry["report_sha256"]
        || entry["time_bound_fired"] != time_bound_fired(&report)
    {
        return Err(StoreError::Invalid("indexed report differs".into()));
    }
    // A store is resumed only by the build that wrote it (packet CACHE-ID-fix-1): the semantics
    // identity below names only kink's versioned algorithms, and most verdict code (the
    // comparison, the status fold, pattern matching, adaptation, step events, feasibility, the
    // census) has no version constant, so only the build identity can tell that it changed.
    if let Some(reason) = kink_campaign::writer_difference(
        &entry["kink_build"],
        &report["manifest"]["kink"],
        &Ok(build),
    ) {
        return Err(StoreError::Invalid(format!(
            "the indexed report is not resumed: {reason}; delete the store to rerun it with this \
             build"
        )));
    }
    if admission["kink_build"] != build.to_string() {
        return Err(StoreError::Invalid(
            "the indexed definition's admission record was written by another kink build".into(),
        ));
    }
    if entry["run_options"] != run_options_value(&corpus_run_options()) {
        return Err(StoreError::Invalid(format!(
            "the indexed report was made with run options {}, not {}",
            entry["run_options"],
            run_options_value(&corpus_run_options())
        )));
    }
    // A report written under another kink semantics identity at the same k-rust pin (other
    // mutant admission algorithms, definition exclusions, execution requests, result schema or
    // coverage reading; kink-campaign `identity`) is not resumed: its statuses may rest on
    // mutants this build refuses (re-pin R0c-fix-4), on comparisons it excludes (re-pin R0-tail)
    // or on runs it no longer makes (packet CACHE-ID). Nor is a report of another format.
    if let Some(key) = kink_campaign::identity_difference(&report["manifest"]["kink"]) {
        return Err(StoreError::Invalid(format!(
            "the indexed report was written under another kink identity (`{key}` is missing \
             or differs): other mutant admission algorithms, exclusions or execution requests"
        )));
    }
    if report["version"] != kink_campaign::CAMPAIGN_REPORT_VERSION {
        return Err(StoreError::Invalid(
            "the indexed report has another campaign report version".into(),
        ));
    }
    let artifact_digest = report["manifest"]["baseline"]["semantic_input_sha256"]
        .as_str()
        .ok_or_else(|| StoreError::Invalid("artifact digest".into()))?;
    let parsed: Sha256Digest = Sha256Digest::parse(artifact_digest)
        .ok_or_else(|| StoreError::Invalid("artifact digest".into()))?;
    if report["manifest"]["baseline"]["artifact"] != format!("semantic-input/{parsed}.json") {
        return Err(StoreError::Invalid("indexed artifact path differs".into()));
    }
    let path = store
        .profile_path(digest, profile)
        .join(format!("semantic-input/{parsed}.json"));
    if !path.exists() {
        return Ok(None);
    }
    let artifact = fs::read_to_string(path)?;
    if sha256(artifact.as_bytes()).to_string() != artifact_digest {
        return Err(StoreError::Invalid("indexed artifact differs".into()));
    }
    let (_, baseline) = kink_patch::SemanticInput::read(&artifact)
        .map_err(|e| StoreError::Invalid(e.to_string()))?;
    store.rebuild_tests(digest, id, &baseline)?;
    Ok(Some(DefinitionOutcome {
        admission,
        campaign: Some(entry.clone()),
        resumed: true,
    }))
}
