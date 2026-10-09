//! Strict replay checks artifact identity, rebuilds each patch, and regenerates the report.
//!
//! Reproduction assumes the same kink build and operator code, no fired wall-clock
//! or SMT time bound, and k-rust provenance round-trip and compilation determinism.
//! Route A checks structure and compiled KORE, not metadata-sensitive mutant
//! provenance bytes. Route B is the authority: only byte-identical regeneration
//! gives `Reproduced`. Refusals and divergences never return or alter a verdict.

use crate::{
    CAMPAIGN_REPORT_VERSION, Campaign, CampaignOptions, ManifestInput, MutantId, OperatorId,
    ScheduleMode, SelectionPolicy, TestCase, campaign_manifest, campaign_report, run_campaign_with,
};
use k_rust::{definition::json, kompile::CompileOptions, kore::ast::Pattern};
use kink_native::{
    K_RUST_REVISION, MutantRejection, NativeValidator,
    execution::{ExecutionBudget, SolverProfile},
    step_events::StepEventSpec,
};
use kink_patch::{
    Baseline, CAMPAIGN_MANIFEST_DOMAIN, CANONICAL_PATCH_DOMAIN, COMPILED_KORE_DOMAIN,
    CandidateFailure, CandidateGeneration, FINGERPRINT_DOMAIN, Patch, PatchFailureKind,
    SemanticInput, apply, canonical_json, payload_digest, sha256, structure_sha256,
};
use kink_pattern::ExecutionTerminalKind;
use serde_json::{Value, json};
use std::collections::BTreeSet;

pub struct ReplayDeclaration<'a> {
    pub module: &'a str,
    pub observation: &'a [StepEventSpec],
    pub classify: &'a dyn Fn(&Pattern) -> ExecutionTerminalKind,
    pub classifier: &'a str,
    pub tests: &'a [TestCase],
    pub budget: ExecutionBudget,
    pub schedule: ScheduleMode,
    pub selection: SelectionPolicy,
    pub operator: OperatorId<'a>,
    pub select:
        &'a dyn for<'b> Fn(&'b Baseline) -> Result<CandidateGeneration<'b>, CandidateFailure>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReplayOutcome {
    Reproduced,
    Refused(ReplayRefusal),
    Diverged {
        pointer: String,
        mutants: Vec<MutantId>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReplayRefusal {
    Schema,
    ManifestDigest,
    Environment(String),
    BaselineDigest,
    Artifact(String),
    PatchDecode(MutantId),
    PatchDigest(MutantId),
    Stale(MutantId),
    Rebuild(MutantId),
    MutantDigest(MutantId),
    Declaration,
    Selection(String),
    Campaign(String),
    Report(String),
}

pub fn replay(
    report: &str,
    baseline_artifact: &str,
    declaration: &ReplayDeclaration<'_>,
) -> ReplayOutcome {
    replay_checked(report, baseline_artifact, declaration).unwrap_or_else(ReplayOutcome::Refused)
}

fn replay_checked(
    report: &str,
    baseline_artifact: &str,
    declaration: &ReplayDeclaration<'_>,
) -> Result<ReplayOutcome, ReplayRefusal> {
    let value: Value = serde_json::from_str(report).map_err(|_| ReplayRefusal::Schema)?;
    if value["schema"] != "kink-campaign-report" || value["version"] != CAMPAIGN_REPORT_VERSION {
        return Err(ReplayRefusal::Schema);
    }
    let manifest = &value["manifest"];
    let manifest_text = canonical_json(manifest);
    if value["manifest_sha256"]
        != payload_digest(CAMPAIGN_MANIFEST_DOMAIN, manifest_text.as_bytes()).to_string()
    {
        return Err(ReplayRefusal::ManifestDigest);
    }
    check_environment(manifest)?;
    if manifest["baseline"]["semantic_input_sha256"]
        != sha256(baseline_artifact.as_bytes()).to_string()
    {
        return Err(ReplayRefusal::BaselineDigest);
    }
    let (_, baseline) = SemanticInput::read(baseline_artifact)
        .map_err(|e| ReplayRefusal::Artifact(e.to_string()))?;
    let validator = NativeValidator::bind(baseline, CompileOptions::default());
    rebuild(&value, &validator)?;
    let campaign = Campaign {
        validator: &validator,
        module: declaration.module,
        observation: declaration.observation,
        classify: declaration.classify,
        tests: declaration.tests,
        budget: declaration.budget,
    };
    let generation = (declaration.select)(validator.baseline())
        .map_err(|e| ReplayRefusal::Selection(e.to_string()))?;
    let regenerated_manifest = campaign_manifest(&ManifestInput {
        campaign: &campaign,
        generation: &generation,
        schedule: declaration.schedule,
        selection: declaration.selection,
        operator: OperatorId {
            id: declaration.operator.id,
            version: declaration.operator.version,
            policy: declaration.operator.policy,
        },
        classifier: declaration.classifier,
    })
    .map_err(|_| ReplayRefusal::Declaration)?;
    if regenerated_manifest.text() != manifest_text {
        return Err(ReplayRefusal::Declaration);
    }
    let run = run_campaign_with(
        &campaign,
        &generation,
        &CampaignOptions {
            schedule: declaration.schedule,
            selection: declaration.selection,
        },
    )
    .map_err(|e| ReplayRefusal::Campaign(e.to_string()))?;
    let regenerated = campaign_report(&regenerated_manifest, &campaign, &generation, &run)
        .map_err(|e| ReplayRefusal::Report(e.to_string()))?;
    if regenerated.text() == report {
        return Ok(ReplayOutcome::Reproduced);
    }
    Ok(ReplayOutcome::Diverged {
        // A byte-only noncanonical difference points to the document root.
        pointer: first_difference(&value, regenerated.value(), "").unwrap_or_default(),
        mutants: differing_mutants(&value, regenerated.value()),
    })
}

fn check_environment(manifest: &Value) -> Result<(), ReplayRefusal> {
    for (pointer, expected) in [
        ("/k_rust/revision", json!(K_RUST_REVISION)),
        ("/k_rust/provenance_format", json!(json::PROVENANCE_FORMAT)),
        (
            "/k_rust/provenance_version",
            json!(json::PROVENANCE_VERSION),
        ),
        ("/kink/fingerprint", json!(FINGERPRINT_DOMAIN)),
        ("/kink/canonical_patch", json!(CANONICAL_PATCH_DOMAIN)),
        ("/kink/compiled_kore", json!(COMPILED_KORE_DOMAIN)),
        ("/profile", json!(SolverProfile::BUILD.name())),
    ] {
        if manifest.pointer(pointer) != Some(&expected) {
            return Err(ReplayRefusal::Environment(pointer[1..].replace('/', ".")));
        }
    }
    Ok(())
}

fn mutant_id(value: &Value) -> Option<MutantId> {
    value["mutant_id"]
        .as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .map(MutantId)
}

fn rebuild(report: &Value, validator: &NativeValidator) -> Result<(), ReplayRefusal> {
    let mutants = report["mutants"].as_array().ok_or(ReplayRefusal::Schema)?;
    let entries = report["manifest"]["mutants"]
        .as_array()
        .ok_or(ReplayRefusal::Schema)?;
    if mutants.len() != entries.len() {
        return Err(ReplayRefusal::Schema);
    }
    for (index, (mutant, entry)) in mutants.iter().zip(entries).enumerate() {
        let id = mutant_id(mutant).ok_or(ReplayRefusal::Schema)?;
        if id != MutantId(index) || mutant_id(entry) != Some(id) {
            return Err(ReplayRefusal::Schema);
        }
        let patch = Patch::from_canonical_json(&canonical_json(&mutant["canonical_patch"]))
            .map_err(|_| ReplayRefusal::PatchDecode(id))?;
        let digest = patch
            .digest()
            .map_err(|_| ReplayRefusal::PatchDigest(id))?
            .to_string();
        if mutant["patch_sha256"] != digest || entry["patch_sha256"] != digest {
            return Err(ReplayRefusal::PatchDigest(id));
        }
        let rebuilt = apply(validator.baseline(), &patch).map_err(|e| {
            if e.kind() == PatchFailureKind::StalePrecondition {
                ReplayRefusal::Stale(id)
            } else {
                ReplayRefusal::Rebuild(id)
            }
        })?;
        if structure_sha256(rebuilt.definition())
            .map_err(|_| ReplayRefusal::MutantDigest(id))?
            .to_string()
            != entry["structure_sha256"]
        {
            return Err(ReplayRefusal::MutantDigest(id));
        }
        let (kore, validation) = match validator.validate(&patch) {
            Ok(compiled) => (
                Some(compiled.kore_sha256().to_string()),
                json!({"outcome":"compiled","stage":null,"detail":null}),
            ),
            Err(MutantRejection::Patch(f)) => (
                None,
                json!({"outcome":"rejected","stage":"patch","detail":f.kind().as_str()}),
            ),
            Err(MutantRejection::Relink(_)) => (
                None,
                json!({"outcome":"rejected","stage":"relink","detail":null}),
            ),
            Err(MutantRejection::Compilation(e)) => (
                None,
                json!({"outcome":"rejected","stage":"compilation","detail":e.stage}),
            ),
        };
        if entry["kore_sha256"] != json!(kore) || entry["validation"] != validation {
            return Err(ReplayRefusal::MutantDigest(id));
        }
    }
    Ok(())
}

fn first_difference(left: &Value, right: &Value, pointer: &str) -> Option<String> {
    if left == right {
        return None;
    }
    match (left, right) {
        (Value::Object(a), Value::Object(b)) => {
            let keys = a.keys().chain(b.keys()).collect::<BTreeSet<_>>();
            for key in keys {
                let next = format!("{pointer}/{}", key.replace('~', "~0").replace('/', "~1"));
                match (a.get(key), b.get(key)) {
                    (Some(x), Some(y)) => {
                        if let Some(found) = first_difference(x, y, &next) {
                            return Some(found);
                        }
                    }
                    _ => return Some(next),
                }
            }
        }
        (Value::Array(a), Value::Array(b)) => {
            for index in 0..a.len().max(b.len()) {
                let next = format!("{pointer}/{index}");
                match (a.get(index), b.get(index)) {
                    (Some(x), Some(y)) => {
                        if let Some(found) = first_difference(x, y, &next) {
                            return Some(found);
                        }
                    }
                    _ => return Some(next),
                }
            }
        }
        _ => return Some(pointer.to_owned()),
    }
    None
}

fn differing_mutants(left: &Value, right: &Value) -> Vec<MutantId> {
    let a = left["mutants"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default();
    let b = right["mutants"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default();
    let ids = a
        .iter()
        .chain(b)
        .filter_map(mutant_id)
        .collect::<BTreeSet<_>>();
    ids.into_iter()
        .filter(|id| {
            let x = a.iter().find(|m| mutant_id(m) == Some(*id));
            let y = b.iter().find(|m| mutant_id(m) == Some(*id));
            match (x, y) {
                (Some(x), Some(y)) => ["status", "killing_test_ids", "tests"]
                    .iter()
                    .any(|key| x.get(key) != y.get(key)),
                _ => true,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn differences_use_sorted_keys_array_indices_and_rfc6901_escaping() {
        let cases = [
            (
                json!({"z":0,"a~/":[1,2]}),
                json!({"z":1,"a~/":[1,3]}),
                "/a~0~1/1",
            ),
            (json!({"a":null}), json!({}), "/a"),
            (json!([0]), json!([0, 1]), "/1"),
            (json!(true), json!([]), ""),
        ];
        for (a, b, expected) in cases {
            assert_eq!(first_difference(&a, &b, "").as_deref(), Some(expected));
        }
        assert_eq!(first_difference(&json!({}), &json!({}), ""), None);
    }

    #[test]
    fn divergence_names_every_changed_verdict_or_test() {
        let left = json!({"mutants":[
            {"mutant_id":0,"status":"killed","killing_test_ids":["a"],"tests":[]},
            {"mutant_id":1,"status":"survived","killing_test_ids":[],"tests":[1]},
            {"mutant_id":2,"status":"equivalent","killing_test_ids":[],"tests":[]},
            {"mutant_id":3,"status":"killed","killing_test_ids":["a"],"tests":[]},
        ]});
        let mut right = left.clone();
        right["mutants"][0]["status"] = json!("survived");
        right["mutants"][1]["tests"] = json!([2]);
        right["mutants"][2]["operator"] = json!("other");
        right["mutants"][3]["killing_test_ids"] = json!(["b"]);
        assert_eq!(
            differing_mutants(&left, &right),
            vec![MutantId(0), MutantId(1), MutantId(3)]
        );
    }
}
