use kink_campaign::{
    CacheRecord, PortableBranchCollection, PortableCampaignReport, PortableClosureRoot,
    PortableOracleComparison, PortableOracleEvidence, PortableProductionWitness,
    PortablePublishedReport, ReplayVersionRegistry,
};
use kink_portable::{SemanticJson, parse_json};
use std::fs;
use std::path::{Path, PathBuf};

fn package_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("investigations/backend-agnostic-goal-closure")
}

fn load(relative: &str) -> SemanticJson {
    parse_json(&fs::read(package_root().join(relative)).expect("fixture is readable"))
        .expect("fixture is restricted JSON")
}

#[test]
fn all_bag16_collection_positives_rederive_and_identity_drift_rejects() {
    let fixtures = package_root().join("fixtures");
    let mut checked = 0;
    for entry in fs::read_dir(fixtures).expect("fixture directory") {
        let path = entry.expect("entry").path();
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !name.starts_with("bag16-collection-")
            || path.extension().and_then(|value| value.to_str()) != Some("json")
        {
            continue;
        }
        let value = parse_json(&fs::read(&path).expect("fixture")).expect("JSON");
        PortableBranchCollection::from_json(&value)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        checked += 1;
    }
    assert!(checked >= 8);
    let mut drift = load("fixtures/bag16-collection-empty.json");
    let SemanticJson::Object(fields) = &mut drift else {
        unreachable!()
    };
    fields.insert("collectionId".into(), SemanticJson::String("f".repeat(64)));
    assert!(PortableBranchCollection::from_json(&drift).is_err());

    let mut refreshed = load("fixtures/bag16-collection-two-branch.json");
    let SemanticJson::Object(fields) = &mut refreshed else {
        unreachable!()
    };
    let SemanticJson::Array(visits) = fields.get_mut("visited").expect("visited") else {
        unreachable!()
    };
    let SemanticJson::Object(first) = &mut visits[0] else {
        unreachable!()
    };
    first.insert("visitOrdinal".into(), SemanticJson::Integer(7));
    let SemanticJson::Object(fields) = &mut refreshed else {
        unreachable!()
    };
    refresh_self_id(fields, "collectionId", "k-in-k/branch-trace-collection/v1");
    assert!(PortableBranchCollection::from_json(&refreshed).is_err());
}

#[test]
fn v1_and_v2_recursive_registry_identities_are_closed() {
    for relative in [
        "fixtures/bag15-replay-version-registry.json",
        "fixtures/bag16-replay-version-registry.json",
        "fixtures/bag16-replay-version-registry-empty.json",
        "fixtures/bag16-replay-version-registry-oracle-pattern.json",
    ] {
        ReplayVersionRegistry::from_json(&load(relative))
            .unwrap_or_else(|error| panic!("{relative}: {error}"));
    }
    let mut drift = load("fixtures/bag16-replay-version-registry.json");
    let SemanticJson::Object(fields) = &mut drift else {
        unreachable!()
    };
    fields.insert("registryId".into(), SemanticJson::String("e".repeat(64)));
    assert!(ReplayVersionRegistry::from_json(&drift).is_err());
}

#[test]
fn every_bag16_closure_root_binds_exact_catalog_registry_and_finite_identity() {
    let fixtures = package_root().join("fixtures");
    let mut checked = 0;
    for entry in fs::read_dir(fixtures).expect("fixture directory") {
        let path = entry.expect("entry").path();
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !name.starts_with("bag16-closure-")
            || path.extension().and_then(|value| value.to_str()) != Some("json")
        {
            continue;
        }
        let value = parse_json(&fs::read(&path).expect("fixture")).expect("JSON");
        PortableClosureRoot::from_json(&value)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        checked += 1;
    }
    assert_eq!(checked, 15);

    let mut drift = load("fixtures/bag16-closure-empty-execution.json");
    let SemanticJson::Object(fields) = &mut drift else {
        unreachable!()
    };
    let SemanticJson::Object(catalog) = fields.get_mut("artifactCatalog").expect("catalog") else {
        unreachable!()
    };
    let SemanticJson::Array(entries) = catalog.get_mut("entries").expect("entries") else {
        unreachable!()
    };
    let SemanticJson::Object(entry) = &mut entries[0] else {
        unreachable!()
    };
    entry.insert("contentSha256".into(), SemanticJson::String("f".repeat(64)));
    refresh_self_id(catalog, "catalogId", "k-in-k/artifact-catalog/v2");
    let SemanticJson::Object(fields) = &mut drift else {
        unreachable!()
    };
    refresh_self_id(fields, "closureId", "k-in-k/portable-closure-root/v1");
    assert!(PortableClosureRoot::from_json(&drift).is_err());
}

#[test]
fn bag14_first_kill_report_closes_exact_selected_record_prefix() {
    let invocation = load("fixtures/bag14-campaign-invocation-first-kill.json");
    let report = load("fixtures/bag14-mutation-report-first-kill.json");
    let records = records_for_report(&report);
    PortableCampaignReport::from_json(&invocation, &report, &records)
        .expect("report closure validates");
    let mut omitted = records.clone();
    omitted.pop();
    assert!(PortableCampaignReport::from_json(&invocation, &report, &omitted).is_err());
}

#[test]
fn bag14_full_report_derives_statuses_score_and_complete_suffix() {
    let invocation = load("fixtures/bag14-campaign-invocation-full.json");
    let report = load("fixtures/bag14-mutation-report-full.json");
    let records = records_for_report(&report);
    assert_eq!(records.len(), 10);
    PortableCampaignReport::from_json(&invocation, &report, &records)
        .expect("full report closure validates");

    let mut drift = report.clone();
    let SemanticJson::Object(fields) = &mut drift else {
        unreachable!()
    };
    let SemanticJson::Array(statuses) = fields.get_mut("testStatuses").expect("statuses") else {
        unreachable!()
    };
    let SemanticJson::Object(first) = &mut statuses[0] else {
        unreachable!()
    };
    first.insert("status".into(), SemanticJson::String("error".into()));
    let refreshed = kink_portable::digest_without_field(
        &kink_portable::DigestDomain::new("k-in-k/mutation-report/v1").expect("domain"),
        &drift,
        "reportId",
    )
    .expect("refreshed report");
    let SemanticJson::Object(fields) = &mut drift else {
        unreachable!()
    };
    fields.insert(
        "reportId".into(),
        SemanticJson::String(refreshed.to_string()),
    );
    assert!(PortableCampaignReport::from_json(&invocation, &drift, &records).is_err());
}

#[test]
fn bag15_derivation_and_publication_receipts_close_selected_record_dag() {
    for mode in ["first-kill", "full"] {
        let report = load(&format!("fixtures/bag15-provenance-report-{mode}.json"));
        let records = bag15_records_for_report(&report);
        let derivation_result = load(&format!("fixtures/bag15-derivation-result-{mode}.json"));
        let derivation_receipt = load(&format!("fixtures/bag15-receipt-derivation-{mode}.json"));
        let publication_result = load(&format!("fixtures/bag15-publication-result-{mode}.json"));
        let publication_receipt = load(&format!("fixtures/bag15-receipt-publication-{mode}.json"));
        let registry = load("fixtures/bag15-replay-version-registry.json");
        PortablePublishedReport::from_json(
            &report,
            &derivation_result,
            &derivation_receipt,
            &publication_result,
            &publication_receipt,
            &registry,
            &records,
        )
        .unwrap_or_else(|error| panic!("{mode}: {error}"));
        let mut omitted = records.clone();
        omitted.pop();
        assert!(
            PortablePublishedReport::from_json(
                &report,
                &derivation_result,
                &derivation_receipt,
                &publication_result,
                &publication_receipt,
                &registry,
                &omitted,
            )
            .is_err()
        );
    }
}

fn bag15_records_for_report(report: &SemanticJson) -> Vec<CacheRecord> {
    report
        .as_object()
        .and_then(|fields| fields.get("outcome"))
        .and_then(SemanticJson::as_object)
        .and_then(|outcome| outcome.get("selectedRecords"))
        .and_then(SemanticJson::as_array)
        .expect("selected records")
        .iter()
        .map(|selected| {
            let record_id = selected
                .as_object()
                .and_then(|fields| fields.get("recordId"))
                .and_then(SemanticJson::as_str)
                .expect("record ID");
            let record = fixture_by_self_id("recordId", record_id);
            let production = record
                .as_object()
                .and_then(|fields| fields.get("productionEvidence"))
                .and_then(SemanticJson::as_object)
                .expect("production evidence");
            let receipt_id = key_id(production.get("receipt")).expect("receipt ID");
            let result_id = key_id(production.get("result")).expect("result ID");
            let receipt = fixture_by_self_id("receiptId", receipt_id);
            let result = fixture_by_self_id("resultId", result_id);
            CacheRecord::from_portable_json(
                &record,
                PortableProductionWitness::BundledOperationReceipt {
                    receipt: &receipt,
                    result: &result,
                },
            )
            .expect("receipt-backed record")
        })
        .collect()
}

fn fixture_by_self_id(field: &str, expected: &str) -> SemanticJson {
    for entry in fs::read_dir(package_root().join("fixtures")).expect("fixtures") {
        let path = entry.expect("entry").path();
        if path.extension().and_then(|value| value.to_str()) != Some("json") {
            continue;
        }
        let Ok(value) = parse_json(&fs::read(&path).expect("fixture")) else {
            continue;
        };
        if value
            .as_object()
            .and_then(|fields| fields.get(field))
            .and_then(SemanticJson::as_str)
            == Some(expected)
        {
            return value;
        }
    }
    panic!("fixture with {field}={expected}")
}

fn key_id(value: Option<&SemanticJson>) -> Option<&str> {
    value
        .and_then(SemanticJson::as_object)
        .and_then(|key| key.get("digest"))
        .and_then(SemanticJson::as_str)
}

fn records_for_report(report: &SemanticJson) -> Vec<CacheRecord> {
    let selected = match report
        .as_object()
        .and_then(|fields| fields.get("selectedRecords"))
    {
        Some(SemanticJson::Array(items)) => items,
        _ => panic!("selected records"),
    };
    let mut records = Vec::new();
    for selected_item in selected {
        let id = selected_item
            .as_object()
            .and_then(|fields| fields.get("recordId"))
            .and_then(SemanticJson::as_str)
            .expect("record id");
        let mut found = None;
        for directory in ["fixtures", "material"] {
            for entry in fs::read_dir(package_root().join(directory)).expect("directory") {
                let path = entry.expect("entry").path();
                if path.extension().and_then(|value| value.to_str()) != Some("json") {
                    continue;
                }
                let Ok(bytes) = fs::read(&path) else { continue };
                let Ok(value) = parse_json(&bytes) else {
                    continue;
                };
                if value
                    .as_object()
                    .and_then(|fields| fields.get("recordId"))
                    .and_then(SemanticJson::as_str)
                    == Some(id)
                {
                    found = Some(value);
                    break;
                }
            }
            if found.is_some() {
                break;
            }
        }
        records.push(
            CacheRecord::from_portable_json(
                &found.expect("selected cache record exists"),
                PortableProductionWitness::BundledFiniteVector,
            )
            .expect("record validates"),
        );
    }
    records
}

#[test]
fn all_six_bag12_builtin_families_rederive_normal_comparisons() {
    for stem in [
        "exit-stop-terminal-class-and-declared-exit-agree",
        "final-result-whole-portable-term-agree",
        "concrete-output-ordered-output-bytes-agree",
        "reachability-reachability-truth-agree",
        "execution-pattern-pattern-outcome-agree",
        "structured-predicate-predicate-bool-agree",
    ] {
        PortableOracleComparison::from_json(
            &load(&format!("fixtures/oracle-declaration-{stem}.json")),
            &load(&format!("fixtures/oracle-operand-{stem}-baseline.json")),
            &load(&format!("fixtures/oracle-operand-{stem}-mutant.json")),
            &load(&format!("fixtures/oracle-comparison-{stem}.json")),
        )
        .unwrap_or_else(|error| panic!("{stem}: {error}"));
    }
}

#[test]
fn complete_bag12_finite_graph_closes_all_outcomes_and_outer_absence_rules() {
    let vectors = load("vectors/oracle-semantics-vectors.json");
    let cases = vectors
        .as_object()
        .and_then(|fields| fields.get("evidenceCases"))
        .and_then(SemanticJson::as_array)
        .expect("evidence cases");
    assert_eq!(cases.len(), 22);
    for case in cases {
        let fields = case.as_object().expect("case");
        let id = fields.get("id").and_then(SemanticJson::as_str).expect("id");
        let baseline_operand = artifact_for_case(fields, "baselineOperand", id, "baseline");
        let mutant_operand = artifact_for_case(fields, "mutantOperand", id, "mutant");
        let comparison = optional_case_artifact(fields, "comparison", || {
            load(&format!("fixtures/oracle-comparison-{id}.json"))
        });
        let baseline_crash = outer_crash(fields, "baselineSide")
            .map(|_| load("fixtures/semantic-crash-baseline-live.json"));
        let mutant_crash = outer_crash(fields, "mutantSide")
            .map(|_| load("fixtures/semantic-crash-mutant-live.json"));
        PortableOracleEvidence::from_frozen_vector(
            &load(&format!("fixtures/oracle-declaration-{id}.json")),
            &load(&format!("fixtures/baseline-oracle-gate-{id}.json")),
            baseline_operand.as_ref(),
            baseline_crash.as_ref(),
            mutant_operand.as_ref(),
            mutant_crash.as_ref(),
            comparison.as_ref(),
            fields.get("outerResult").expect("outer result"),
        )
        .unwrap_or_else(|error| panic!("{id}: {error}"));
    }
}

#[test]
fn refreshed_outer_oracle_graph_cannot_authorize_unregistered_semantics() {
    let vectors = load("vectors/oracle-semantics-vectors.json");
    let case = vectors
        .as_object()
        .and_then(|fields| fields.get("evidenceCases"))
        .and_then(SemanticJson::as_array)
        .and_then(|cases| cases.first())
        .and_then(SemanticJson::as_object)
        .expect("first evidence case");
    let id = case.get("id").and_then(SemanticJson::as_str).expect("id");
    let declaration = load(&format!("fixtures/oracle-declaration-{id}.json"));
    let gate = load(&format!("fixtures/baseline-oracle-gate-{id}.json"));
    let mut baseline = load(&format!("fixtures/oracle-operand-{id}-baseline.json"));
    let mutant = load(&format!("fixtures/oracle-operand-{id}-mutant.json"));
    let comparison = load(&format!("fixtures/oracle-comparison-{id}.json"));
    let outer = case.get("outerResult").expect("outer");
    let SemanticJson::Object(fields) = &mut baseline else {
        unreachable!()
    };
    let SemanticJson::Object(value) = fields.get_mut("normalizedValue").expect("value") else {
        unreachable!()
    };
    value.insert("exitCode".into(), SemanticJson::Integer(0));
    let refreshed = kink_portable::digest_without_field(
        &kink_portable::DigestDomain::new("k-in-k/oracle-operand/v1").expect("domain"),
        &baseline,
        "operandId",
    )
    .expect("refreshed operand");
    let SemanticJson::Object(fields) = &mut baseline else {
        unreachable!()
    };
    fields.insert(
        "operandId".into(),
        SemanticJson::String(refreshed.to_string()),
    );
    assert!(
        PortableOracleEvidence::from_frozen_vector(
            &declaration,
            &gate,
            Some(&baseline),
            None,
            Some(&mutant),
            None,
            Some(&comparison),
            outer,
        )
        .is_err()
    );
}

fn optional_case_artifact(
    fields: &std::collections::BTreeMap<String, SemanticJson>,
    name: &str,
    load_value: impl FnOnce() -> SemanticJson,
) -> Option<SemanticJson> {
    (!matches!(fields.get(name), None | Some(SemanticJson::Null))).then(load_value)
}

fn artifact_for_case(
    fields: &std::collections::BTreeMap<String, SemanticJson>,
    name: &str,
    id: &str,
    side: &str,
) -> Option<SemanticJson> {
    optional_case_artifact(fields, name, || {
        load(&format!("fixtures/oracle-operand-{id}-{side}.json"))
    })
}

fn outer_crash<'a>(
    fields: &'a std::collections::BTreeMap<String, SemanticJson>,
    side: &str,
) -> Option<&'a SemanticJson> {
    fields
        .get("outerResult")
        .and_then(SemanticJson::as_object)
        .and_then(|outer| outer.get(side))
        .and_then(SemanticJson::as_object)
        .and_then(|side| side.get("semanticCrash"))
        .filter(|value| !matches!(value, SemanticJson::Null))
}

fn refresh_self_id(
    fields: &mut std::collections::BTreeMap<String, SemanticJson>,
    name: &str,
    domain: &str,
) {
    let value = SemanticJson::Object(fields.clone());
    let digest = kink_portable::digest_without_field(
        &kink_portable::DigestDomain::new(domain).expect("domain"),
        &value,
        name,
    )
    .expect("refreshed self ID");
    fields.insert(name.into(), SemanticJson::String(digest.to_string()));
}
