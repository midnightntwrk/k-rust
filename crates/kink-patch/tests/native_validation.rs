use kink_patch::{
    AppliedPatch, NativeIrValidation, NativeTransactionFailure, NativeValidationRejectionKind,
    Patch, PatchFailureKind, StagedNativeInput, apply_patch, apply_patch_with_native_validation,
};
use kink_portable::{
    Digest, DigestDomain, SemanticJson, canonical_json as checked_canonical_json,
    digest as checked_digest, parse_json,
};
use std::cell::Cell;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

#[derive(Debug, Eq, PartialEq)]
struct TestNativeOutput {
    output_definition_digest: Digest,
    lowered_node_count: usize,
}

#[derive(Debug)]
struct LeakingNativeFailure {
    staged: AppliedPatch,
    staged_identity: Digest,
    dropped: Rc<Cell<bool>>,
}

impl Drop for LeakingNativeFailure {
    fn drop(&mut self) {
        assert_eq!(self.staged.output_definition_digest, self.staged_identity);
        self.dropped.set(true);
    }
}

fn package_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("workspace layout")
        .join("investigations/backend-agnostic-goal-closure")
}

fn load(path: impl AsRef<Path>) -> SemanticJson {
    parse_json(&fs::read(path).expect("frozen input is present"))
        .expect("frozen input is restricted JSON")
}

fn object(value: &SemanticJson) -> &BTreeMap<String, SemanticJson> {
    value.as_object().expect("frozen object")
}

fn domain(value: &str) -> DigestDomain {
    DigestDomain::new(value).expect("static domain")
}

fn digest(domain: &DigestDomain, value: &SemanticJson) -> Digest {
    checked_digest(domain, value).expect("test value is valid semantic JSON")
}

fn canonical_json(value: &SemanticJson) -> String {
    checked_canonical_json(value).expect("test value is valid semantic JSON")
}

fn edit_key(edit: &SemanticJson) -> (String, String, String, String) {
    let fields = object(edit);
    (
        match fields.get("targetLineage") {
            Some(SemanticJson::String(value)) => value.clone(),
            _ => String::new(),
        },
        canonical_json(fields.get("targetPath").expect("targetPath")),
        fields
            .get("operation")
            .and_then(SemanticJson::as_str)
            .expect("operation")
            .to_owned(),
        fields
            .get("editId")
            .and_then(SemanticJson::as_str)
            .expect("editId")
            .to_owned(),
    )
}

fn materialize_patch(vectors: &SemanticJson, case: &SemanticJson) -> Patch {
    let vectors = object(vectors);
    let case = object(case);
    let pool = object(vectors.get("valuePool").expect("value pool"));
    let mut edits = case
        .get("edits")
        .and_then(SemanticJson::as_array)
        .expect("edit templates")
        .to_vec();
    for edit in &mut edits {
        let SemanticJson::Object(fields) = edit else {
            panic!("edit template object")
        };
        let value_ref = fields
            .remove("valueRef")
            .and_then(|value| match value {
                SemanticJson::String(value) => Some(value),
                _ => None,
            })
            .expect("valueRef");
        fields.insert(
            "value".to_owned(),
            pool.get(&value_ref).expect("known pool value").clone(),
        );
        fields.remove("editId");
        let edit_id = digest(
            &domain("k-in-k/edit/v1"),
            &SemanticJson::Object(fields.clone()),
        );
        fields.insert(
            "editId".to_owned(),
            SemanticJson::String(edit_id.to_string()),
        );
    }
    edits.sort_by_key(edit_key);
    let payload = SemanticJson::Object(BTreeMap::from([
        ("schemaVersion".to_owned(), SemanticJson::Integer(1)),
        ("edits".to_owned(), SemanticJson::Array(edits.clone())),
    ]));
    let patch_id = digest(&domain("k-in-k/patch/v1"), &payload);
    let patch = SemanticJson::Object(BTreeMap::from([
        ("schemaVersion".to_owned(), SemanticJson::Integer(1)),
        (
            "patchId".to_owned(),
            SemanticJson::String(patch_id.to_string()),
        ),
        (
            "operatorId".to_owned(),
            case.get("operatorId").expect("operatorId").clone(),
        ),
        (
            "operatorVersion".to_owned(),
            case.get("operatorVersion")
                .expect("operatorVersion")
                .clone(),
        ),
        ("edits".to_owned(), SemanticJson::Array(edits)),
    ]));
    Patch::from_json(&patch).expect("materialized vector patch is canonical")
}

fn fixture_case<'a>(vectors: &'a SemanticJson, id: &str) -> &'a SemanticJson {
    object(vectors)
        .get("cases")
        .and_then(SemanticJson::as_array)
        .expect("cases")
        .iter()
        .find(|case| object(case).get("id").and_then(SemanticJson::as_str) == Some(id))
        .expect("known frozen case")
}

fn validate_test_native_input(input: StagedNativeInput<'_>) -> TestNativeOutput {
    assert_eq!(input.portable().applied_edit_count, 2);
    assert_eq!(input.patch().edits().len(), 2);
    assert_eq!(
        input.portable().native_ir_validation,
        NativeIrValidation::RustProofPending
    );
    TestNativeOutput {
        output_definition_digest: input.portable().output_definition_digest.clone(),
        lowered_node_count: 17,
    }
}

#[test]
fn publishes_portable_and_opaque_native_outputs_only_after_validation_success() {
    let root = package_root();
    let vectors = load(root.join("vectors/patch-application-vectors.json"));
    let baseline = load(root.join("fixtures/semantic-definition-memory.json"));
    let patch = materialize_patch(
        &vectors,
        fixture_case(&vectors, "atomic-distinct-sentence-replacements"),
    );
    let ordinary = apply_patch(&baseline, &patch).expect("ordinary portable application succeeds");
    assert_eq!(
        ordinary.native_ir_validation,
        NativeIrValidation::RustProofPending
    );

    let committed = apply_patch_with_native_validation(&baseline, &patch, |input| {
        assert_eq!(input.baseline(), &baseline);
        assert_eq!(input.patch(), &patch);
        assert_eq!(
            input.portable().output_definition_digest,
            ordinary.output_definition_digest
        );
        Ok::<_, ()>(validate_test_native_input(input))
    })
    .expect("native validation commits both outputs");

    assert_eq!(committed.portable(), &ordinary);
    assert_eq!(committed.native_output().lowered_node_count, 17);
    let (portable, native_output) = committed.into_parts();
    assert_eq!(
        native_output.output_definition_digest,
        portable.output_definition_digest
    );
    assert_eq!(
        portable.native_ir_validation,
        NativeIrValidation::RustProofPending
    );
}

#[test]
fn validator_owned_error_cannot_escape_with_cloned_staged_output_or_identity() {
    let root = package_root();
    let vectors = load(root.join("vectors/patch-application-vectors.json"));
    let baseline = load(root.join("fixtures/semantic-definition-memory.json"));
    let patch = materialize_patch(
        &vectors,
        fixture_case(&vectors, "atomic-distinct-sentence-replacements"),
    );
    let mut validator_called = false;
    let validator_error_dropped = Rc::new(Cell::new(false));
    let dropped = Rc::clone(&validator_error_dropped);

    let failure = apply_patch_with_native_validation(&baseline, &patch, |input| {
        validator_called = true;
        let staged = input.portable().clone();
        let staged_identity = input.portable().output_definition_digest.clone();
        Err::<TestNativeOutput, _>(Box::new(LeakingNativeFailure {
            staged,
            staged_identity,
            dropped,
        }))
    })
    .expect_err("native rejection must not publish staged output");

    assert!(validator_called);
    assert!(validator_error_dropped.get());
    assert_eq!(failure.committed_edit_count(), 0);
    match failure {
        NativeTransactionFailure::Native(rejection) => {
            assert_eq!(
                rejection.kind(),
                NativeValidationRejectionKind::ValidatorRejected
            );
            assert_eq!(rejection.kind().as_str(), "validator-rejected");
            assert_eq!(
                rejection.diagnostic(),
                "the native validator rejected the privately staged portable result"
            );
        }
        NativeTransactionFailure::Portable(_) => panic!("portable staging succeeded"),
    }
}

#[test]
fn portable_failure_skips_native_validation_and_commits_nothing() {
    let root = package_root();
    let vectors = load(root.join("vectors/patch-application-vectors.json"));
    let baseline = load(root.join("fixtures/semantic-definition-memory.json"));
    let patch = materialize_patch(
        &vectors,
        fixture_case(&vectors, "stale-precondition-is-atomic"),
    );
    let mut validator_called = false;

    let failure = apply_patch_with_native_validation(&baseline, &patch, |_| {
        validator_called = true;
        Ok::<_, ()>(TestNativeOutput {
            output_definition_digest: patch.patch_id().clone(),
            lowered_node_count: 0,
        })
    })
    .expect_err("portable failure must prevent native validation");

    assert!(!validator_called);
    assert_eq!(failure.committed_edit_count(), 0);
    match failure {
        NativeTransactionFailure::Portable(failure) => {
            assert_eq!(failure.kind(), PatchFailureKind::StalePrecondition);
            assert_eq!(failure.applied_edit_count(), 0);
        }
        NativeTransactionFailure::Native(_) => panic!("validator must not run"),
    }
}
