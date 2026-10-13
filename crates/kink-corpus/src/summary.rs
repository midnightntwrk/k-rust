//! Deterministic aggregation of the digest-checked corpus results store.
//!
//! Campaign evidence supplies every tally and score. This module only reads it;
//! it does not execute a definition or produce a campaign verdict.

use crate::{
    manifest::DefinitionSpec,
    store::{Store, StoreError},
};
use kink_campaign::{CAMPAIGN_REPORT_VERSION, Projection};
use kink_native::execution::SolverProfile;
use kink_patch::{CAMPAIGN_MANIFEST_DOMAIN, SemanticInput, canonical_json, payload_digest, sha256};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

const TALLY_KEYS: [&str; 8] = [
    "killed",
    "survived",
    "equivalent",
    "invalid",
    "timeout",
    "unknown",
    "error",
    "rejected_origins",
];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorpusSummary {
    value: Value,
}
impl CorpusSummary {
    pub const fn value(&self) -> &Value {
        &self.value
    }
    pub fn text(&self) -> String {
        canonical_json(&self.value)
    }
}

/// Summarize only the declarations and evidence stored under this corpus digest.
/// A missing campaign has unknown baseline pattern results and no score.
pub fn summarize(
    store: &Store,
    corpus_manifest_sha256: &str,
    profile: &str,
) -> Result<CorpusSummary, StoreError> {
    let digest = kink_patch::Sha256Digest::parse(corpus_manifest_sha256)
        .ok_or_else(|| invalid("corpus manifest digest"))?;
    let manifest = store.read_manifest(digest)?;
    let solver_profile = match profile {
        "no-z3" => SolverProfile::NoZ3,
        "z3" => SolverProfile::Z3,
        _ => return Err(invalid("summary profile")),
    };
    manifest
        .check_profile(solver_profile)
        .map_err(|e| invalid(e.to_string()))?;
    let base = store.profile_path(digest, profile);
    let index = store.read_index(digest, profile)?;
    let entries = index
        .as_object()
        .ok_or_else(|| invalid("store index object"))?;
    if entries
        .keys()
        .any(|id| !manifest.definitions().iter().any(|d| &d.id == id))
    {
        return Err(invalid("unlisted index definition"));
    }
    let mut definitions = Vec::new();
    let mut admitted = 0_u64;
    let mut errors = 0_u64;
    let mut refused = BTreeMap::<String, u64>::new();
    let mut total_tally = [0_u64; 8];
    let mut total_causes = BTreeMap::<String, u64>::new();
    let mut all_scored = true;
    let mut pattern_counts = [0_u64; 3];
    for definition in manifest.definitions() {
        let admission_path = store.admission_path(digest, profile, &definition.id)?;
        let record = match fs::read_to_string(&admission_path) {
            Ok(_) => store.read_json(&admission_path)?,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => json!({
                "definition":definition.id,"outcome":"error","stage":"process",
                "reason":"process","census":null
            }),
            Err(e) => return Err(e.into()),
        };
        if record["definition"] != definition.id {
            return Err(invalid("admission definition differs"));
        }
        let mut outcome = string(&record["outcome"], "admission outcome")?.to_owned();
        if !matches!(outcome.as_str(), "admitted" | "refused" | "error") {
            return Err(invalid(
                "admission outcome (Q1 refuses exposed definitions)",
            ));
        }
        let mut stage = record["stage"].clone();
        let mut reason = record["reason"].clone();
        let census = summarize_census(&record["census"])?;
        // Q1=a is checked here too, so edited admission bytes cannot count a
        // flagged census as an admitted definition.
        if outcome == "admitted" && record["census"]["verdict"] == "flagged" {
            outcome = "refused".into();
            stage = json!("declaration-census");
            reason = json!("vi-t13");
        }
        let report = entries
            .get(&definition.id)
            .map(|entry| read_report(store, &base, entry, profile, digest, &definition.id))
            .transpose()?;
        if report
            .as_ref()
            .is_some_and(|report| report["manifest"]["admission"]["verdict"] == "flagged")
        {
            outcome = "refused".into();
            stage = json!("declaration-census");
            reason = json!("vi-t13-mutant");
        }
        if outcome == "admitted" && record["census"]["verdict"] != "natural" {
            return Err(invalid("admitted definition lacks a natural census"));
        }
        let patterns = patterns(definition, report.as_ref())?;
        let campaign = match (entries.get(&definition.id), report.as_ref()) {
            (Some(entry), Some(report)) => {
                let tally = read_tally(&report["summary"]["tally"])?;
                let causes = unknown_causes(report)?;
                let score = &report["summary"]["score"];
                validate_score(score, &tally)?;
                let per_operator = report["summary"]["per_operator"]
                    .as_array()
                    .ok_or_else(|| invalid("per_operator array"))?;
                let mut operator_rows = Vec::new();
                for row in per_operator {
                    let operator_tally = read_tally(&row["tally"])?;
                    validate_score(&row["score"], &operator_tally)?;
                    let operator = number(&row["operator"], "operator index")?;
                    operator_rows.push(
                        json!({"operator":operator,"tally":row["tally"],"score":row["score"]}),
                    );
                }
                if outcome == "admitted" {
                    add_tally(&mut total_tally, &tally)?;
                    add_causes(&mut total_causes, &causes)?;
                    all_scored &= !score.is_null();
                }
                json!({"manifest_sha256":entry["manifest_sha256"],"report_sha256":entry["report_sha256"],
                    "time_bound_fired":entry["time_bound_fired"],"tally":report["summary"]["tally"],
                    "unknown_causes":causes,"per_operator":operator_rows,"score":score})
            }
            _ => {
                if outcome == "admitted" {
                    all_scored = false;
                }
                Value::Null
            }
        };
        match outcome.as_str() {
            "admitted" => {
                admitted += 1;
                add_patterns(&mut pattern_counts, &patterns)?;
            }
            "refused" => {
                let stage_name = string(&stage, "refusal stage")?.to_owned();
                *refused.entry(stage_name).or_default() += 1;
            }
            "error" => errors += 1,
            _ => unreachable!("checked admission outcome"),
        }
        definitions.push(
            json!({"id":definition.id,"admission":{"outcome":outcome,"stage":stage,"reason":reason},
            "census":census,"campaign":campaign,"patterns":patterns}),
        );
    }
    let any_match = if pattern_counts[0] > 0 {
        "yes"
    } else if pattern_counts[2] > 0 {
        "unknown"
    } else {
        "no"
    };
    Ok(CorpusSummary {
        value: json!({"schema":"kink-corpus-summary","version":1,
        "corpus_manifest_sha256":corpus_manifest_sha256,"profile":profile,"definitions":definitions,
        "totals":{"definitions":{"listed":manifest.definitions().len(),"admitted":admitted,"exposed":0,
            "refused":refused,"error":errors},"tally":tally_value(&total_tally),"unknown_causes":total_causes,
            "score":if all_scored { score_value(&total_tally)? } else { Value::Null },
            "patterns":{"tests_with_match":pattern_counts[0],"tests_no_match":pattern_counts[1],
                "tests_unknown":pattern_counts[2],"any_match":any_match}},"exposed":[]}),
    })
}

fn invalid(detail: impl Into<String>) -> StoreError {
    StoreError::Invalid(detail.into())
}
fn string<'a>(value: &'a Value, name: &str) -> Result<&'a str, StoreError> {
    value
        .as_str()
        .ok_or_else(|| invalid(format!("{name}: expected string")))
}
fn number(value: &Value, name: &str) -> Result<u64, StoreError> {
    value
        .as_u64()
        .ok_or_else(|| invalid(format!("{name}: expected u64")))
}
fn read_report(
    store: &Store,
    base: &Path,
    entry: &Value,
    profile: &str,
    corpus: kink_patch::Sha256Digest,
    id: &str,
) -> Result<Value, StoreError> {
    let digest = string(&entry["manifest_sha256"], "campaign digest")?;
    if kink_patch::Sha256Digest::parse(digest).is_none() {
        return Err(invalid("campaign digest"));
    }
    entry["time_bound_fired"]
        .as_bool()
        .ok_or_else(|| invalid("time_bound_fired boolean"))?;
    let path = base.join("campaigns").join(format!("{digest}.json"));
    let text = fs::read_to_string(&path)?;
    if entry["report_sha256"] != sha256(text.as_bytes()).to_string() {
        return Err(invalid("campaign report digest"));
    }
    let report = store.read_json(&path)?;
    let campaign = &report["manifest"];
    if report["schema"] != "kink-campaign-report"
        || report["version"] != CAMPAIGN_REPORT_VERSION
        || report["manifest_sha256"] != digest
        || payload_digest(
            CAMPAIGN_MANIFEST_DOMAIN,
            canonical_json(campaign).as_bytes(),
        )
        .to_string()
            != digest
        || campaign["schema"] != "kink-campaign-manifest"
        || campaign["version"] != 5
        || campaign["profile"] != profile
    {
        return Err(invalid("campaign manifest or report identity"));
    }
    if campaign["admission"]["verdict"] != "natural"
        && campaign["admission"]["verdict"] != "flagged"
    {
        return Err(invalid("campaign census verdict"));
    }
    let artifact_digest = string(
        &campaign["baseline"]["semantic_input_sha256"],
        "baseline digest",
    )?;
    if kink_patch::Sha256Digest::parse(artifact_digest).is_none()
        || campaign["baseline"]["artifact"] != format!("semantic-input/{artifact_digest}.json")
    {
        return Err(invalid("baseline artifact identity"));
    }
    let artifact_text = fs::read_to_string(
        base.join("semantic-input")
            .join(format!("{artifact_digest}.json")),
    )?;
    if sha256(artifact_text.as_bytes()).to_string() != artifact_digest {
        return Err(invalid("baseline artifact digest"));
    }
    let (_, baseline) = SemanticInput::read(&artifact_text)
        .map_err(|e| invalid(format!("baseline artifact: {e}")))?;
    store.rebuild_tests(corpus, id, &baseline)?;
    Ok(report)
}
fn summarize_census(census: &Value) -> Result<Value, StoreError> {
    if census.is_null() {
        return Ok(Value::Null);
    }
    let verdict = string(&census["verdict"], "census verdict")?;
    if !matches!(verdict, "natural" | "flagged") {
        return Err(invalid("census verdict"));
    }
    let findings = census["findings"]
        .as_array()
        .ok_or_else(|| invalid("census findings"))?
        .len();
    let inert = census["inert"]
        .as_array()
        .ok_or_else(|| invalid("census inert"))?
        .len();
    Ok(json!({"verdict":verdict,"findings":findings,"inert":inert}))
}
fn read_tally(value: &Value) -> Result<[u64; 8], StoreError> {
    let object = value.as_object().ok_or_else(|| invalid("tally object"))?;
    if object.len() != TALLY_KEYS.len() {
        return Err(invalid("tally keys"));
    }
    let mut tally = [0; 8];
    for (count, name) in tally.iter_mut().zip(TALLY_KEYS) {
        *count = number(&value[name], name)?;
    }
    Ok(tally)
}
fn tally_value(tally: &[u64; 8]) -> Value {
    Value::Object(
        TALLY_KEYS
            .into_iter()
            .zip(tally.iter())
            .map(|(key, count)| (key.into(), json!(count)))
            .collect(),
    )
}
fn add_tally(total: &mut [u64; 8], tally: &[u64; 8]) -> Result<(), StoreError> {
    for (total, count) in total.iter_mut().zip(tally) {
        *total = total
            .checked_add(*count)
            .ok_or_else(|| invalid("tally overflow"))?;
    }
    Ok(())
}
fn score_value(tally: &[u64; 8]) -> Result<Value, StoreError> {
    let denominator = tally[0]
        .checked_add(tally[1])
        .ok_or_else(|| invalid("score overflow"))?;
    let ratio = if denominator == 0 {
        Value::Null
    } else {
        let (mut a, mut b) = (tally[0], denominator);
        while b != 0 {
            (a, b) = (b, a % b);
        }
        json!({"numerator":tally[0]/a,"denominator":denominator/a})
    };
    Ok(json!({"killed":tally[0],"survived":tally[1],"denominator":denominator,"ratio":ratio}))
}
fn validate_score(score: &Value, tally: &[u64; 8]) -> Result<(), StoreError> {
    if !score.is_null() && *score != score_value(tally)? {
        return Err(invalid("score differs from tally"));
    }
    Ok(())
}
fn unknown_causes(report: &Value) -> Result<BTreeMap<String, u64>, StoreError> {
    let mutants = report["mutants"]
        .as_array()
        .ok_or_else(|| invalid("mutants array"))?;
    let entries = report["manifest"]["mutants"]
        .as_array()
        .ok_or_else(|| invalid("manifest mutants array"))?;
    if mutants.len() != entries.len() {
        return Err(invalid("mutant count"));
    }
    let mut counts = BTreeMap::new();
    for (index, (mutant, entry)) in mutants.iter().zip(entries).enumerate() {
        if !entry["same_as"].is_null() {
            let earlier = number(&entry["same_as"], "same_as index")?;
            if earlier >= index as u64 {
                return Err(invalid("same_as must precede mutant"));
            }
            continue;
        }
        if mutant["status"] != "unknown" {
            continue;
        }
        let mut causes = BTreeSet::new();
        if let Some(cause) = mutant["mutant_failure"].as_str() {
            causes.insert(cause.to_owned());
        } else {
            let tests = mutant["tests"]
                .as_array()
                .ok_or_else(|| invalid("mutant tests array"))?;
            for test in tests {
                if let Some(cause) = test["run"]["failed"].as_str() {
                    causes.insert(cause.to_owned());
                }
                if test["run"]["compared"]
                    .as_array()
                    .is_some_and(|outcomes| outcomes.iter().any(|o| o == "unknown"))
                {
                    causes.insert("oracle-unknown".into());
                }
            }
        }
        if causes.is_empty() {
            causes.insert("oracle-unknown".into());
        }
        for cause in causes {
            *counts.entry(cause).or_insert(0) += 1;
        }
    }
    Ok(counts)
}
fn add_causes(
    total: &mut BTreeMap<String, u64>,
    causes: &BTreeMap<String, u64>,
) -> Result<(), StoreError> {
    for (cause, count) in causes {
        let total = total.entry(cause.clone()).or_default();
        *total = total
            .checked_add(*count)
            .ok_or_else(|| invalid("unknown causes overflow"))?;
    }
    Ok(())
}
fn patterns(definition: &DefinitionSpec, report: Option<&Value>) -> Result<Value, StoreError> {
    let mut rows = BTreeMap::new();
    if let Some(report) = report {
        for row in report["baseline"]
            .as_array()
            .ok_or_else(|| invalid("baseline rows"))?
        {
            let id = string(&row["test_id"], "baseline test id")?;
            let test = definition
                .tests
                .iter()
                .find(|test| test.id == id)
                .ok_or_else(|| invalid("unlisted baseline test"))?;
            if rows.insert(id, &row["run"]).is_some() {
                return Err(invalid("duplicate baseline test id"));
            }
            if let Some(sides) = row["run"]["sides"].as_array()
                && sides.len() != test.oracles.len()
            {
                return Err(invalid("baseline oracle count"));
            }
        }
    }
    let mut patterns = Vec::new();
    for test in &definition.tests {
        for (oracle, declaration) in test.oracles.iter().enumerate() {
            if !matches!(declaration.projection(), Projection::Pattern { .. }) {
                continue;
            }
            let side = rows
                .get(test.id.as_str())
                .and_then(|run| run["sides"].as_array())
                .and_then(|sides| sides.get(oracle));
            let baseline = match side {
                Some(side)
                    if side["normal"]["pattern"]
                        .as_object()
                        .is_some_and(|p| p.contains_key("match")) =>
                {
                    "match"
                }
                Some(side) if side["normal"]["pattern"] == "no-match" => "no-match",
                _ => "unknown",
            };
            patterns.push(json!({"test_id":test.id,"oracle":oracle,"baseline":baseline}));
        }
    }
    Ok(if patterns.is_empty() {
        Value::Null
    } else {
        json!(patterns)
    })
}
fn add_patterns(counts: &mut [u64; 3], patterns: &Value) -> Result<(), StoreError> {
    let Some(patterns) = patterns.as_array() else {
        return Ok(());
    };
    let mut tests = BTreeMap::<&str, Vec<&str>>::new();
    for row in patterns {
        tests
            .entry(string(&row["test_id"], "pattern test id")?)
            .or_default()
            .push(string(&row["baseline"], "pattern baseline")?);
    }
    for sides in tests.values() {
        let index = if sides.contains(&"match") {
            0
        } else if sides.iter().all(|side| *side == "no-match") {
            1
        } else {
            2
        };
        counts[index] += 1;
    }
    Ok(())
}
