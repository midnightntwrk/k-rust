//! Per-definition corpus admission, campaign execution and atomic publication.

use crate::{
    admission::{AdmissionRecord, AdmissionRefusal, admit_definition},
    manifest::CorpusManifest,
    store::{Store, StoreError, time_bound_fired},
};
use k_rust::{kompile::CompileOptions, kore::ast::Pattern};
use kink_campaign::{
    Campaign, CampaignFailureKind, CampaignOptions, ManifestOperator, MultiManifestInput,
    campaign_manifest_multi_with_budget, campaign_report_multi, run_campaign_multi,
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
    // The shared declaration is the first file of every call, including resumptions.
    store.ensure_manifest(manifest)?;
    let digest = manifest.digest();
    let profile = SolverProfile::BUILD.name();
    let admission_path = store.admission_path(digest, profile, id)?;
    if !manifest.definitions().iter().any(|d| d.id == id) {
        return Err(StoreError::Invalid("definition is not listed".into()));
    }
    if let Some(outcome) = resume(store, digest, profile, id, &admission_path)? {
        return Ok(outcome);
    }
    let mut admission = admit_definition(manifest, id, workspace);
    let Some(admitted) = admission.admitted else {
        store.write_text(&admission_path, &admission.record.text())?;
        return Ok(DefinitionOutcome {
            admission: admission.record.value(),
            campaign: None,
            resumed: false,
        });
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
    let run = match run_campaign_multi(
        &campaign,
        &generations,
        &CampaignOptions {
            schedule: config.schedule,
            selection: config.selection,
            share_evidence: true,
        },
    ) {
        Ok(run) => run,
        Err(e) => {
            admission.record.refusal = Some(AdmissionRefusal {
                stage: "baseline".into(),
                reason: failure_kind(e.kind()).into(),
                detail: e.to_string(),
            });
            return store_refusal(store, &admission_path, &admission.record);
        }
    };
    let report = campaign_report_multi(&declaration, &campaign, &generations, &run)
        .map_err(|e| StoreError::Invalid(e.to_string()))?;
    let text = report.text();
    let entry = json!({"manifest_sha256":declaration.digest().to_string(),
        "report_sha256":sha256(text.as_bytes()).to_string(),"time_bound_fired":time_bound_fired(report.value())});
    let root = store.profile_path(digest, profile);
    store.write_text(&admission_path, &admission.record.text())?;
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
        admission: admission.record.value(),
        campaign: Some(entry),
        resumed: false,
    })
}
fn store_refusal(
    store: &Store,
    path: &Path,
    record: &AdmissionRecord,
) -> Result<DefinitionOutcome, StoreError> {
    store.write_text(path, &record.text())?;
    Ok(DefinitionOutcome {
        admission: record.value(),
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
