use kink_campaign::{
    CheckedCompilerReceiptCandidate, CheckedEvaluatorConformanceCandidate, EvaluatorAuthority,
    InvocationFailureKind, OracleFailureKind, Producer,
};
use kink_contracts::NativeConformance;
use kink_portable::{
    ArtifactCatalogEntry, Digest, DigestDomain, IngressedArtifact, RepositoryResolver,
    RoleSpecRegistry, SemanticJson, canonical_json_bytes, digest, digest_without_field,
    ingest_artifact, parse_json, sha256_bytes,
};
use std::fs;
use std::path::{Path, PathBuf};

const PATTERN_SOURCE: &str = "ed9ae3907d39b5d29809163ea7d272745a559504a408083b9edab6a9b5d267da";
const PATTERN_PLAN: &str = "3a9db24b23b99a7a5a57e10fd4ef4591d553bc6bd1e6dc15fcceac9588b90dbd";
const PATTERN_QUERY: &str = "078960b20beff8c8d087be6163897925d85fe257c808ffdbac80662fc32ff88e";
const COMPILER_PROFILE: &str = "8ca3331eaace7b1153a7a2530b921c23335a6624493d4b9da91e7447c64588dd";

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn package_root() -> PathBuf {
    workspace_root().join("investigations/backend-agnostic-goal-closure")
}

fn catalog_entries() -> SemanticJson {
    parse_json(
        &fs::read(package_root().join("fixtures/artifact-catalog.json"))
            .expect("catalog fixture is readable"),
    )
    .expect("catalog fixture is restricted JSON")
}

fn ingressed(role: &str, digest: &str) -> IngressedArtifact {
    let catalog = catalog_entries();
    let row = catalog
        .as_object()
        .and_then(|fields| fields.get("entries"))
        .and_then(SemanticJson::as_array)
        .expect("catalog entries")
        .iter()
        .find(|value| {
            let fields = value.as_object().expect("catalog row");
            fields.get("role").and_then(SemanticJson::as_str) == Some(role)
                && fields.get("digest").and_then(SemanticJson::as_str) == Some(digest)
        })
        .unwrap_or_else(|| panic!("catalog contains {role}:{digest}"));
    let entry = ArtifactCatalogEntry::from_json(row).expect("catalog row validates");
    let bytes = RepositoryResolver::new(&workspace_root())
        .and_then(|resolver| resolver.fetch(&entry.locator))
        .expect("bundled artifact resolves");
    let registry = RoleSpecRegistry::from_repository_root(&workspace_root())
        .expect("frozen role registry loads");
    ingest_artifact(&registry, &entry, bytes).expect("frozen artifact ingresses")
}

fn synthetic_compatibility_profile() -> IngressedArtifact {
    let catalog = catalog_entries();
    let row = catalog
        .as_object()
        .and_then(|fields| fields.get("entries"))
        .and_then(SemanticJson::as_array)
        .expect("catalog entries")
        .iter()
        .find(|value| {
            value
                .as_object()
                .and_then(|fields| fields.get("role"))
                .and_then(SemanticJson::as_str)
                == Some("compatibility-profile")
        })
        .expect("compatibility profile catalog row");
    let mut entry = ArtifactCatalogEntry::from_json(row).expect("catalog row validates");
    let value = SemanticJson::Object(
        [(
            "profile".to_owned(),
            SemanticJson::String("nr03-candidate".to_owned()),
        )]
        .into_iter()
        .collect(),
    );
    let bytes = canonical_json_bytes(&value).expect("canonical profile");
    entry.digest = digest(
        &DigestDomain::new("k-in-k/compatibility-profile/v1").expect("static domain"),
        &value,
    )
    .expect("profile identity derives");
    entry.content_sha256 = sha256_bytes(&bytes);
    IngressedArtifact {
        entry,
        bytes,
        semantic_json: Some(value),
    }
}

fn set_string(value: &mut SemanticJson, field: &str, replacement: &str) {
    let SemanticJson::Object(fields) = value else {
        panic!("object")
    };
    fields.insert(
        field.to_owned(),
        SemanticJson::String(replacement.to_owned()),
    );
}

fn refresh_id(value: &mut SemanticJson, field: &str, domain: &str) -> Digest {
    let derived = digest_without_field(
        &DigestDomain::new(domain).expect("static digest domain"),
        value,
        field,
    )
    .expect("self-ID projection derives");
    set_string(value, field, derived.as_str());
    derived
}

fn replace_nested_digest(value: &mut SemanticJson, field: &str, digest: &str) {
    let SemanticJson::Object(fields) = value else {
        panic!("object")
    };
    let Some(SemanticJson::Object(nested)) = fields.get_mut(field) else {
        panic!("nested artifact key")
    };
    nested.insert("digest".to_owned(), SemanticJson::String(digest.to_owned()));
}

fn refresh_structured_artifact(
    artifact: &mut IngressedArtifact,
    value: SemanticJson,
    digest: Digest,
) {
    let bytes = canonical_json_bytes(&value).expect("canonical JSON encodes");
    artifact.entry.digest = digest;
    artifact.entry.content_sha256 = sha256_bytes(&bytes);
    artifact.bytes = bytes;
    artifact.semantic_json = Some(value);
}

#[test]
fn compiler_candidate_rederives_registered_tuple_but_never_becomes_a_receipt() {
    let source = ingressed("pattern-source", PATTERN_SOURCE);
    let plan = ingressed("pattern-plan", PATTERN_PLAN);
    let query = ingressed("pattern-query", PATTERN_QUERY);
    let compiler_profile = ingressed("pattern-compiler-profile", COMPILER_PROFILE);
    let checked = CheckedCompilerReceiptCandidate::validate_frozen_inputs(
        &source,
        &plan,
        &query,
        &compiler_profile,
    )
    .expect("complete frozen compiler-input tuple validates");
    assert_eq!(checked.source().digest.as_str(), PATTERN_SOURCE);
    assert_eq!(checked.plan().digest.as_str(), PATTERN_PLAN);
    assert_eq!(checked.query().digest.as_str(), PATTERN_QUERY);
    assert_eq!(checked.compiler_profile().digest.as_str(), COMPILER_PROFILE);
    assert_eq!(checked.entry_module(), "PATTERN-QUERIES");
    assert_eq!(checked.exported_name(), "single-write");

    assert_eq!(
        Producer::scripted("candidate-only", 1).native_conformance(),
        NativeConformance::NotProven
    );
    assert!(
        EvaluatorAuthority::finite_vector()
            .validate_k_authored()
            .is_err()
    );
}

#[test]
fn refreshed_query_identity_cannot_hide_nested_compiler_source_drift() {
    let source = ingressed("pattern-source", PATTERN_SOURCE);
    let plan = ingressed("pattern-plan", PATTERN_PLAN);
    let mut query = ingressed("pattern-query", PATTERN_QUERY);
    let compiler_profile = ingressed("pattern-compiler-profile", COMPILER_PROFILE);
    let mut value = query.semantic_json.clone().expect("structured query");
    replace_nested_digest(&mut value, "patternSource", &"a".repeat(64));
    let query_id = refresh_id(&mut value, "queryId", "k-in-k/pattern-query/v1");
    refresh_structured_artifact(&mut query, value, query_id);

    assert_eq!(
        CheckedCompilerReceiptCandidate::validate_frozen_inputs(
            &source,
            &plan,
            &query,
            &compiler_profile,
        )
        .expect_err("refreshed outer query ID must not hide nested drift")
        .kind(),
        InvocationFailureKind::CompilerInputMismatch
    );
}

#[test]
fn compiler_entry_export_drift_without_a_matching_query_identity_rejects() {
    let source = ingressed("pattern-source", PATTERN_SOURCE);
    let plan = ingressed("pattern-plan", PATTERN_PLAN);
    let mut query = ingressed("pattern-query", PATTERN_QUERY);
    let compiler_profile = ingressed("pattern-compiler-profile", COMPILER_PROFILE);
    let mut value = query.semantic_json.clone().expect("structured query");
    set_string(&mut value, "entryModule", "DRIFTED-MODULE");
    let bytes = canonical_json_bytes(&value).expect("canonical JSON encodes");
    query.entry.content_sha256 = sha256_bytes(&bytes);
    query.bytes = bytes;
    query.semantic_json = Some(value);

    assert_eq!(
        CheckedCompilerReceiptCandidate::validate_frozen_inputs(
            &source,
            &plan,
            &query,
            &compiler_profile,
        )
        .expect_err("entry/export drift must be covered by query identity")
        .kind(),
        InvocationFailureKind::DigestMismatch
    );
}

fn conformance_fixture() -> SemanticJson {
    parse_json(
        &fs::read(package_root().join("material/oracle-evaluator-conformance-nonconformant.json"))
            .expect("conformance fixture is readable"),
    )
    .expect("conformance fixture is restricted JSON")
}

fn conformance_artifacts(value: &SemanticJson) -> Vec<IngressedArtifact> {
    let fields = value.as_object().expect("conformance object");
    let mut keys = ["source", "plan", "query", "comparisonArtifact"]
        .into_iter()
        .filter_map(|name| fields.get(name))
        .map(|key| {
            let fields = key.as_object().expect("artifact key");
            (
                fields.get("role").and_then(SemanticJson::as_str).unwrap(),
                fields.get("digest").and_then(SemanticJson::as_str).unwrap(),
            )
        })
        .map(|(role, digest)| ingressed(role, digest))
        .collect::<Vec<_>>();
    for (field, role) in [
        ("compatibilityProfileDigest", "compatibility-profile"),
        ("executionProfileDigest", "execution-profile"),
        ("solverProfileDigest", "solver-profile"),
    ] {
        keys.push(if role == "compatibility-profile" {
            synthetic_compatibility_profile()
        } else {
            ingressed(
                role,
                fields.get(field).and_then(SemanticJson::as_str).unwrap(),
            )
        });
    }
    let suite = fields
        .get("conformanceSuite")
        .and_then(SemanticJson::as_object)
        .expect("suite key");
    keys.push(ingressed(
        suite.get("role").and_then(SemanticJson::as_str).unwrap(),
        suite.get("digest").and_then(SemanticJson::as_str).unwrap(),
    ));
    keys
}

fn structurally_conformant_fixture() -> SemanticJson {
    let mut value = conformance_fixture();
    set_string(
        &mut value,
        "compatibilityProfileDigest",
        synthetic_compatibility_profile().entry.digest.as_str(),
    );
    set_string(&mut value, "result", "conformant");
    set_string(&mut value, "compilerVersion", "candidate-1");
    set_string(&mut value, "evaluatorVersion", "candidate-1");
    refresh_id(
        &mut value,
        "conformanceId",
        "k-in-k/oracle-evaluator-conformance/v1",
    );
    value
}

#[test]
fn bundled_nonconformant_evaluator_record_is_always_negative_evidence() {
    let value = conformance_fixture();
    assert_eq!(
        CheckedEvaluatorConformanceCandidate::validate_frozen_candidate(&value, &[])
            .expect_err("bundled nonconformant fixture must reject")
            .kind(),
        OracleFailureKind::EvaluatorNonconformant
    );
}

#[test]
fn evaluator_candidate_rederives_every_registered_root_without_granting_authority() {
    let value = structurally_conformant_fixture();
    let artifacts = conformance_artifacts(&value);
    let checked =
        CheckedEvaluatorConformanceCandidate::validate_frozen_candidate(&value, &artifacts)
            .expect("structurally conformant candidate validates");
    assert_eq!(checked.roots().len(), 7);
    assert_eq!(checked.compiler().1, "candidate-1");
    assert_eq!(checked.evaluator().1, "candidate-1");
    assert!(
        EvaluatorAuthority::finite_vector()
            .validate_k_authored()
            .is_err()
    );
}

#[test]
fn refreshed_conformance_and_query_ids_cannot_hide_nested_source_drift() {
    let mut value = structurally_conformant_fixture();
    let mut artifacts = conformance_artifacts(&value);
    let query_index = artifacts
        .iter()
        .position(|artifact| artifact.entry.role == "predicate-query")
        .expect("query artifact");
    let mut query = artifacts[query_index]
        .semantic_json
        .clone()
        .expect("structured query");
    replace_nested_digest(&mut query, "source", &"a".repeat(64));
    let query_id = refresh_id(&mut query, "queryId", "k-in-k/predicate-query/v1");
    refresh_structured_artifact(&mut artifacts[query_index], query, query_id.clone());
    replace_nested_digest(&mut value, "query", query_id.as_str());
    refresh_id(
        &mut value,
        "conformanceId",
        "k-in-k/oracle-evaluator-conformance/v1",
    );

    assert_eq!(
        CheckedEvaluatorConformanceCandidate::validate_frozen_candidate(&value, &artifacts)
            .expect_err("refreshed enclosing IDs must not hide nested source drift")
            .kind(),
        OracleFailureKind::ConformanceRootMismatch
    );
}

#[test]
fn evaluator_profile_and_version_drift_reject_fail_closed() {
    let mut profile_drift = structurally_conformant_fixture();
    let artifacts = conformance_artifacts(&profile_drift);
    set_string(
        &mut profile_drift,
        "compatibilityProfileDigest",
        &"a".repeat(64),
    );
    refresh_id(
        &mut profile_drift,
        "conformanceId",
        "k-in-k/oracle-evaluator-conformance/v1",
    );
    assert_eq!(
        CheckedEvaluatorConformanceCandidate::validate_frozen_candidate(
            &profile_drift,
            &artifacts,
        )
        .expect_err("refreshed profile drift must reject")
        .kind(),
        OracleFailureKind::ConformanceRootMismatch
    );

    let mut pending = structurally_conformant_fixture();
    set_string(&mut pending, "compilerVersion", "pending");
    refresh_id(
        &mut pending,
        "conformanceId",
        "k-in-k/oracle-evaluator-conformance/v1",
    );
    assert_eq!(
        CheckedEvaluatorConformanceCandidate::validate_frozen_candidate(&pending, &[])
            .expect_err("placeholder version must reject before authority")
            .kind(),
        OracleFailureKind::PlaceholderVersion
    );

    let mut suite_drift = structurally_conformant_fixture();
    let artifacts = conformance_artifacts(&suite_drift);
    replace_nested_digest(&mut suite_drift, "conformanceSuite", &"b".repeat(64));
    refresh_id(
        &mut suite_drift,
        "conformanceId",
        "k-in-k/oracle-evaluator-conformance/v1",
    );
    assert_eq!(
        CheckedEvaluatorConformanceCandidate::validate_frozen_candidate(&suite_drift, &artifacts)
            .expect_err("refreshed differential-suite drift must reject")
            .kind(),
        OracleFailureKind::ConformanceRootMismatch
    );
}
