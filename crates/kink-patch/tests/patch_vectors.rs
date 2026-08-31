use kink_patch::{
    NativeIrValidation, Patch, PatchModelErrorKind, PortableApplication, apply_patch,
};
use kink_portable::{
    Digest, DigestDomain, PortableDefinition, SemanticJson,
    canonical_json as checked_canonical_json, canonical_json_bytes as checked_canonical_json_bytes,
    digest as checked_digest, parse_json,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

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

fn domain(value: &str) -> DigestDomain {
    DigestDomain::new(value).expect("static domain")
}

fn digest(domain: &DigestDomain, value: &SemanticJson) -> Digest {
    checked_digest(domain, value).expect("test value is valid semantic JSON")
}

fn canonical_json(value: &SemanticJson) -> String {
    checked_canonical_json(value).expect("test value is valid semantic JSON")
}

fn canonical_json_bytes(value: &SemanticJson) -> Vec<u8> {
    checked_canonical_json_bytes(value).expect("test value is valid semantic JSON")
}

fn object(value: &SemanticJson) -> &BTreeMap<String, SemanticJson> {
    value.as_object().expect("frozen object")
}

fn materialize_patch(
    vectors: &SemanticJson,
    case: &SemanticJson,
    reverse_templates: bool,
) -> Patch {
    let vectors = object(vectors);
    let case = object(case);
    let pool = object(vectors.get("valuePool").expect("value pool"));
    let mut templates = case
        .get("edits")
        .and_then(SemanticJson::as_array)
        .expect("edit templates")
        .to_vec();
    if reverse_templates {
        templates.reverse();
    }
    let mut edits = Vec::new();
    for template in templates {
        let SemanticJson::Object(mut fields) = template else {
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
        edits.push(SemanticJson::Object(fields));
    }
    canonical_patch(
        case.get("operatorId")
            .and_then(SemanticJson::as_str)
            .expect("operatorId"),
        u64::try_from(
            case.get("operatorVersion")
                .and_then(SemanticJson::as_i64)
                .expect("operatorVersion"),
        )
        .expect("positive operatorVersion"),
        edits,
    )
}

fn canonical_patch(
    operator_id: &str,
    operator_version: u64,
    mut edits: Vec<SemanticJson>,
) -> Patch {
    for edit in &mut edits {
        let SemanticJson::Object(fields) = edit else {
            panic!("edit object")
        };
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
            SemanticJson::String(operator_id.to_owned()),
        ),
        (
            "operatorVersion".to_owned(),
            SemanticJson::Integer(i64::try_from(operator_version).expect("v1 version fits i64")),
        ),
        ("edits".to_owned(), SemanticJson::Array(edits)),
    ]));
    Patch::from_json(&patch).expect("materialized vector patch is canonical")
}

fn rematerialize_patch(value: &mut SemanticJson) -> Patch {
    let SemanticJson::Object(patch) = value else {
        panic!("patch object")
    };
    let operator_id = patch
        .get("operatorId")
        .and_then(SemanticJson::as_str)
        .expect("operatorId")
        .to_owned();
    let operator_version = u64::try_from(
        patch
            .get("operatorVersion")
            .and_then(SemanticJson::as_i64)
            .expect("operatorVersion"),
    )
    .expect("positive version");
    let SemanticJson::Array(edits) = patch.remove("edits").expect("edits") else {
        panic!("edits array")
    };
    canonical_patch(&operator_id, operator_version, edits)
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

#[test]
fn all_frozen_patch_application_vectors_pass_unchanged() {
    let root = package_root();
    let vectors = load(root.join("vectors/patch-application-vectors.json"));
    let cases = object(&vectors)
        .get("cases")
        .and_then(SemanticJson::as_array)
        .expect("cases");
    assert_eq!(cases.len(), 22);
    for case in cases {
        let fields = object(case);
        let id = fields
            .get("id")
            .and_then(SemanticJson::as_str)
            .expect("case id");
        let fixture = fields
            .get("definitionFixture")
            .and_then(SemanticJson::as_str)
            .expect("definition fixture");
        let baseline = load(root.join("fixtures").join(fixture));
        let patch = materialize_patch(&vectors, case, false);
        let expected = object(fields.get("expected").expect("expected"));
        if expected
            .get("valid")
            .and_then(SemanticJson::as_bool)
            .expect("valid")
        {
            let applied = apply_patch(&baseline, &patch)
                .unwrap_or_else(|failure| panic!("{id}: unexpected {failure}"));
            assert_eq!(
                applied.applied_edit_count,
                usize::try_from(
                    expected
                        .get("appliedEditCount")
                        .and_then(SemanticJson::as_i64)
                        .expect("applied count")
                )
                .expect("nonnegative"),
                "{id}: applied count"
            );
            assert_eq!(
                applied.output_definition_digest.as_str(),
                expected
                    .get("outputDefinitionDigest")
                    .and_then(SemanticJson::as_str)
                    .expect("output digest"),
                "{id}: output definition digest"
            );
            assert_eq!(
                applied.diff_id.as_str(),
                expected
                    .get("diffId")
                    .and_then(SemanticJson::as_str)
                    .expect("diff ID"),
                "{id}: structural diff identity"
            );
            assert_eq!(
                applied.portable_application,
                PortableApplication::AppliedAndLocallyWellFormed
            );
            assert_eq!(
                applied.native_ir_validation,
                NativeIrValidation::RustProofPending
            );
            let repeated = apply_patch(&baseline, &patch).expect("repeat succeeds");
            assert_eq!(
                canonical_json_bytes(&applied.output_definition),
                canonical_json_bytes(&repeated.output_definition),
                "{id}: repeated output bytes"
            );
            assert_eq!(
                applied.structural_diff, repeated.structural_diff,
                "{id}: repeat diff"
            );

            let permuted = materialize_patch(&vectors, case, true);
            let permuted_result =
                apply_patch(&baseline, &permuted).expect("permuted input succeeds");
            assert_eq!(
                patch.to_json(),
                permuted.to_json(),
                "{id}: canonical edit input"
            );
            assert_eq!(applied, permuted_result, "{id}: input permutation result");
        } else {
            let failure =
                apply_patch(&baseline, &patch).expect_err("invalid patch must not publish output");
            assert_eq!(
                failure.kind().as_str(),
                expected
                    .get("failure")
                    .and_then(SemanticJson::as_str)
                    .expect("failure"),
                "{id}: failure classification"
            );
            assert_eq!(failure.applied_edit_count(), 0, "{id}: atomic failure");
        }
    }
}

#[test]
fn rejects_sort_condition_signature_and_replacement_anchor_adversaries_atomically() {
    let root = package_root();
    let vectors = load(root.join("vectors/patch-application-vectors.json"));
    let cases = object(&vectors)
        .get("cases")
        .and_then(SemanticJson::as_array)
        .expect("cases");
    let atomic_case = cases
        .iter()
        .find(|case| {
            object(case).get("id").and_then(SemanticJson::as_str)
                == Some("atomic-distinct-sentence-replacements")
        })
        .expect("atomic case");
    let baseline = load(root.join("fixtures/semantic-definition-memory.json"));

    let mut outer_drift = materialize_patch(&vectors, atomic_case, false).to_json();
    let edits = patch_edits_mut(&mut outer_drift);
    edits.truncate(1);
    object_mut(&mut edits[0]).insert(
        "value".to_owned(),
        object(&vectors)
            .get("valuePool")
            .and_then(SemanticJson::as_object)
            .expect("value pool")
            .get("zero-int")
            .expect("zero-int")
            .clone(),
    );
    let failure = apply_patch(&baseline, &rematerialize_patch(&mut outer_drift))
        .expect_err("outer-sort drift must reject");
    assert_eq!(failure.kind().as_str(), "locally-ill-formed");
    assert_eq!(failure.applied_edit_count(), 0);

    let condition_case = cases
        .iter()
        .find(|case| {
            object(case).get("id").and_then(SemanticJson::as_str)
                == Some("replace-condition-second-family")
        })
        .expect("condition case");
    let counter = load(root.join("fixtures/semantic-definition-counter.json"));
    let mut non_bool = materialize_patch(&vectors, condition_case, false).to_json();
    object_mut(&mut patch_edits_mut(&mut non_bool)[0]).insert(
        "value".to_owned(),
        object(&vectors)
            .get("valuePool")
            .and_then(SemanticJson::as_object)
            .expect("value pool")
            .get("zero-int")
            .expect("zero-int")
            .clone(),
    );
    assert_eq!(
        apply_patch(&counter, &rematerialize_patch(&mut non_bool))
            .expect_err("non-Bool condition must reject")
            .kind()
            .as_str(),
        "locally-ill-formed"
    );

    let mut signature_drift = materialize_patch(&vectors, atomic_case, false).to_json();
    let edits = patch_edits_mut(&mut signature_drift);
    edits.truncate(1);
    let baseline_term = object(&baseline)
        .get("modules")
        .and_then(SemanticJson::as_array)
        .and_then(|modules| object(&modules[0]).get("sentences"))
        .and_then(SemanticJson::as_array)
        .and_then(|sentences| object(&sentences[0]).get("value"))
        .and_then(SemanticJson::as_object)
        .and_then(|value| value.get("body"))
        .and_then(SemanticJson::as_object)
        .and_then(|term| term.get("node"))
        .and_then(SemanticJson::as_object)
        .and_then(|node| node.get("left"))
        .and_then(SemanticJson::as_object)
        .and_then(|term| term.get("node"))
        .and_then(SemanticJson::as_object)
        .expect("known application");
    let conflicting = SemanticJson::Object(BTreeMap::from([
        (
            "encoding".to_owned(),
            SemanticJson::String("portable-term-v1".to_owned()),
        ),
        (
            "sort".to_owned(),
            SemanticJson::String("Address".to_owned()),
        ),
        (
            "node".to_owned(),
            SemanticJson::Object(BTreeMap::from([
                (
                    "kind".to_owned(),
                    SemanticJson::String("application".to_owned()),
                ),
                (
                    "symbolId".to_owned(),
                    baseline_term.get("symbolId").expect("symbolId").clone(),
                ),
                (
                    "label".to_owned(),
                    baseline_term.get("label").expect("label").clone(),
                ),
                (
                    "args".to_owned(),
                    baseline_term.get("args").expect("args").clone(),
                ),
            ])),
        ),
    ]));
    object_mut(&mut edits[0]).insert(
        "value".to_owned(),
        SemanticJson::Object(BTreeMap::from([
            ("kind".to_owned(), SemanticJson::String("term".to_owned())),
            ("term".to_owned(), conflicting),
        ])),
    );
    assert_eq!(
        apply_patch(&baseline, &rematerialize_patch(&mut signature_drift))
            .expect_err("baseline signature drift must reject")
            .kind()
            .as_str(),
        "locally-ill-formed"
    );

    let sentence_case = cases
        .iter()
        .find(|case| {
            object(case).get("id").and_then(SemanticJson::as_str)
                == Some("replace-sentence-second-family")
        })
        .expect("sentence case");
    let mut contradiction = materialize_patch(&vectors, sentence_case, false).to_json();
    let edit = object_mut(&mut patch_edits_mut(&mut contradiction)[0]);
    let value = edit.get_mut("value").expect("value");
    let sentence = object_mut(value).get_mut("sentence").expect("sentence");
    object_mut(sentence).insert(
        "source".to_owned(),
        SemanticJson::String("repo://wrong/source.k".to_owned()),
    );
    assert_eq!(
        apply_patch(&counter, &rematerialize_patch(&mut contradiction))
            .expect_err("replacement anchor drift must reject")
            .kind()
            .as_str(),
        "locally-ill-formed"
    );
}

#[test]
fn injection_descendant_path_is_typed_and_sort_preserving() {
    let root = package_root();
    let vectors = load(root.join("vectors/patch-application-vectors.json"));
    let cases = object(&vectors)
        .get("cases")
        .and_then(SemanticJson::as_array)
        .expect("cases");
    let atomic_case = cases
        .iter()
        .find(|case| {
            object(case).get("id").and_then(SemanticJson::as_str)
                == Some("atomic-distinct-sentence-replacements")
        })
        .expect("atomic case");
    let mut baseline = load(root.join("fixtures/semantic-definition-memory.json"));
    let sentence = first_sentence_value_mut(&mut baseline);
    let body = object_mut(sentence).get_mut("body").expect("body");
    let left = object_mut(object_mut(body).get_mut("node").expect("node"))
        .get_mut("left")
        .expect("left");
    let argument = object_mut(object_mut(left).get_mut("node").expect("node"))
        .get_mut("args")
        .and_then(|args| match args {
            SemanticJson::Array(args) => args.get_mut(0),
            _ => None,
        })
        .expect("first argument");
    *argument = parse_json(
        br#"{"encoding":"portable-term-v1","sort":"Address","node":{"kind":"injection","fromSort":"Int","toSort":"Address","term":{"encoding":"portable-term-v1","sort":"Int","node":{"kind":"token","text":"1"}}}}"#,
    )
    .expect("injection term");
    refresh_test_definition(&mut baseline);

    let mut patch = materialize_patch(&vectors, atomic_case, false).to_json();
    let target_lineage = first_sentence_provenance(&baseline)
        .get("lineageId")
        .expect("lineageId")
        .clone();
    let edits = patch_edits_mut(&mut patch);
    edits.retain(|edit| object(edit).get("targetLineage") == Some(&target_lineage));
    assert_eq!(edits.len(), 1);
    let edit = object_mut(&mut edits[0]);
    edit.insert(
        "expectedContent".to_owned(),
        first_sentence_provenance(&baseline)
            .get("contentFingerprint")
            .expect("content fingerprint")
            .clone(),
    );
    edit.insert(
        "targetPath".to_owned(),
        parse_json(
            br#"[{"kind":"field","name":"body"},{"kind":"field","name":"lhs"},{"kind":"argument","index":0},{"kind":"injection-term"}]"#,
        )
        .expect("typed path"),
    );
    edit.insert(
        "value".to_owned(),
        parse_json(
            br#"{"kind":"term","term":{"encoding":"portable-term-v1","sort":"Int","node":{"kind":"token","text":"2"}}}"#,
        )
        .expect("replacement"),
    );
    let applied = apply_patch(&baseline, &rematerialize_patch(&mut patch))
        .expect("typed injection descendant applies");
    assert_eq!(applied.applied_edit_count, 1);
}

#[test]
fn patch_model_rejects_identity_order_shape_and_operation_drift() {
    let root = package_root();
    let vectors = load(root.join("vectors/patch-application-vectors.json"));
    let case = object(&vectors)
        .get("cases")
        .and_then(SemanticJson::as_array)
        .expect("cases")
        .iter()
        .find(|case| {
            object(case).get("id").and_then(SemanticJson::as_str)
                == Some("atomic-distinct-sentence-replacements")
        })
        .expect("two-edit case");
    let valid = materialize_patch(&vectors, case, false).to_json();

    let mut wrong_id = valid.clone();
    object_mut(&mut wrong_id).insert("patchId".to_owned(), SemanticJson::String("f".repeat(64)));
    assert_eq!(
        Patch::from_json(&wrong_id)
            .expect_err("wrong patch ID")
            .kind(),
        PatchModelErrorKind::DigestMismatch
    );

    let mut reversed = valid.clone();
    patch_edits_mut(&mut reversed).reverse();
    assert_eq!(
        Patch::from_json(&reversed)
            .expect_err("noncanonical edit order")
            .kind(),
        PatchModelErrorKind::NonCanonicalOrder
    );

    let mut unsupported = valid.clone();
    object_mut(&mut patch_edits_mut(&mut unsupported)[0]).insert(
        "operation".to_owned(),
        SemanticJson::String("rewrite-host-node".to_owned()),
    );
    assert_eq!(
        Patch::from_json(&unsupported)
            .expect_err("unsupported operation")
            .kind(),
        PatchModelErrorKind::UnsupportedOperation
    );

    let mut extra_field = valid;
    object_mut(&mut extra_field).insert("diagnostic".to_owned(), SemanticJson::Null);
    assert_eq!(
        Patch::from_json(&extra_field)
            .expect_err("open patch shape")
            .kind(),
        PatchModelErrorKind::MalformedPatch
    );
}

#[test]
fn equal_slot_cross_module_insertions_have_distinct_destination_anchored_lineages() {
    let root = package_root();
    let vectors = load(root.join("vectors/patch-application-vectors.json"));
    let mut combined = load(root.join("fixtures/semantic-definition-memory.json"));
    let counter = load(root.join("fixtures/semantic-definition-counter.json"));
    let counter_module = object(&counter)
        .get("modules")
        .and_then(SemanticJson::as_array)
        .expect("counter modules")[0]
        .clone();
    let combined_root = object_mut(&mut combined);
    let SemanticJson::Array(modules) = combined_root.get_mut("modules").expect("modules") else {
        panic!("modules array")
    };
    let mut counter_module = counter_module;
    object_mut(&mut counter_module).insert("ordinal".to_owned(), SemanticJson::Integer(1));
    modules.push(counter_module);
    let family = SemanticJson::Object(BTreeMap::from([
        (
            "familyName".to_owned(),
            SemanticJson::String("cross-module-portable-slice".to_owned()),
        ),
        (
            "entryModules".to_owned(),
            SemanticJson::Array(vec![
                SemanticJson::String("MEMORY".to_owned()),
                SemanticJson::String("COUNTER".to_owned()),
            ]),
        ),
        (
            "compatibilityProfile".to_owned(),
            object(combined_root.get("family").expect("family"))
                .get("compatibilityProfile")
                .expect("compatibilityProfile")
                .clone(),
        ),
    ]));
    let family_payload = SemanticJson::Object(BTreeMap::from([
        (
            "familyName".to_owned(),
            SemanticJson::String("cross-module-portable-slice".to_owned()),
        ),
        (
            "entryModules".to_owned(),
            SemanticJson::Array(vec![
                SemanticJson::String("COUNTER".to_owned()),
                SemanticJson::String("MEMORY".to_owned()),
            ]),
        ),
        (
            "compatibilityProfile".to_owned(),
            object(&family)
                .get("compatibilityProfile")
                .expect("compatibilityProfile")
                .clone(),
        ),
    ]));
    let family_id = digest(&domain("k-in-k/baseline-family/v1"), &family_payload);
    combined_root.insert("family".to_owned(), family);
    combined_root.insert(
        "baselineFamilyId".to_owned(),
        SemanticJson::String(family_id.to_string()),
    );
    let SemanticJson::Array(modules) = combined_root.get_mut("modules").expect("modules") else {
        panic!("modules array")
    };
    for module in modules {
        let module_name = object(module)
            .get("name")
            .and_then(SemanticJson::as_str)
            .expect("module name")
            .to_owned();
        let SemanticJson::Array(sentences) =
            object_mut(module).get_mut("sentences").expect("sentences")
        else {
            panic!("sentences array")
        };
        for sentence in sentences {
            let sentence_fields = object_mut(sentence);
            let ordinal = sentence_fields
                .get("sourceOccurrenceOrdinal")
                .expect("source occurrence")
                .clone();
            let value = sentence_fields.get("value").expect("value").clone();
            let value_fields = object(&value);
            let lineage_payload = SemanticJson::Object(BTreeMap::from([
                (
                    "baselineFamilyId".to_owned(),
                    SemanticJson::String(family_id.to_string()),
                ),
                (
                    "module".to_owned(),
                    SemanticJson::String(module_name.clone()),
                ),
                (
                    "source".to_owned(),
                    value_fields.get("source").expect("source").clone(),
                ),
                (
                    "location".to_owned(),
                    value_fields.get("location").expect("location").clone(),
                ),
                (
                    "kind".to_owned(),
                    value_fields.get("kind").expect("kind").clone(),
                ),
                ("sourceOccurrenceOrdinal".to_owned(), ordinal),
            ]));
            let lineage = digest(&domain("k-in-k/input-lineage/v1"), &lineage_payload);
            object_mut(sentence_fields.get_mut("provenance").expect("provenance")).insert(
                "lineageId".to_owned(),
                SemanticJson::String(lineage.to_string()),
            );
        }
    }
    refresh_test_definition(&mut combined);
    PortableDefinition::from_json(&combined).expect("combined baseline is valid");

    let sentence_template = object(&vectors)
        .get("valuePool")
        .and_then(SemanticJson::as_object)
        .expect("value pool")
        .get("inserted-memory-sentence")
        .expect("inserted sentence");
    let mut edits = Vec::new();
    let mut baseline_module_fingerprints = BTreeSet::new();
    for module in object(&combined)
        .get("modules")
        .and_then(SemanticJson::as_array)
        .expect("modules")
    {
        let module_fields = object(module);
        let module_name = module_fields
            .get("name")
            .and_then(SemanticJson::as_str)
            .expect("module name");
        let fingerprint = module_fields
            .get("fingerprint")
            .and_then(SemanticJson::as_str)
            .expect("module fingerprint");
        baseline_module_fingerprints.insert(fingerprint.to_owned());
        let mut value = sentence_template.clone();
        let sentence = object_mut(&mut value)
            .get_mut("sentence")
            .expect("sentence");
        let sentence = object_mut(sentence);
        sentence.insert(
            "module".to_owned(),
            SemanticJson::String(module_name.to_owned()),
        );
        sentence.insert(
            "source".to_owned(),
            SemanticJson::String(format!("generated://{}/audit", module_name.to_lowercase())),
        );
        edits.push(SemanticJson::Object(BTreeMap::from([
            (
                "operation".to_owned(),
                SemanticJson::String("insert-sentence".to_owned()),
            ),
            ("targetLineage".to_owned(), SemanticJson::Null),
            ("expectedContent".to_owned(), SemanticJson::Null),
            (
                "expectedModuleFingerprint".to_owned(),
                SemanticJson::String(fingerprint.to_owned()),
            ),
            ("targetPath".to_owned(), SemanticJson::Array(Vec::new())),
            (
                "position".to_owned(),
                SemanticJson::Object(BTreeMap::from([
                    (
                        "kind".to_owned(),
                        SemanticJson::String("module-start".to_owned()),
                    ),
                    (
                        "module".to_owned(),
                        SemanticJson::String(module_name.to_owned()),
                    ),
                    ("ordinal".to_owned(), SemanticJson::Integer(0)),
                ])),
            ),
            ("value".to_owned(), value),
        ])));
    }
    let patch = canonical_patch("cross-module-insertion", 1, edits);
    let applied = apply_patch(&combined, &patch).expect("cross-module insertion applies");
    let mut lineages = BTreeSet::new();
    let mut anchors = BTreeSet::new();
    let mut transformations = BTreeSet::new();
    for module in object(&applied.output_definition)
        .get("modules")
        .and_then(SemanticJson::as_array)
        .expect("output modules")
    {
        for sentence in object(module)
            .get("sentences")
            .and_then(SemanticJson::as_array)
            .expect("sentences")
        {
            let provenance = object(object(sentence).get("provenance").expect("provenance"));
            if provenance.get("generated").and_then(SemanticJson::as_bool) == Some(true) {
                lineages.insert(
                    provenance
                        .get("lineageId")
                        .and_then(SemanticJson::as_str)
                        .expect("lineage")
                        .to_owned(),
                );
                let identity = object(
                    object(sentence)
                        .get("generatedIdentity")
                        .expect("generated identity"),
                );
                anchors.insert(
                    identity
                        .get("anchorIdentity")
                        .and_then(SemanticJson::as_str)
                        .expect("anchor")
                        .to_owned(),
                );
                transformations.insert(
                    identity
                        .get("transformationId")
                        .and_then(SemanticJson::as_str)
                        .expect("transformation")
                        .to_owned(),
                );
            }
        }
    }
    assert_eq!(lineages.len(), 2);
    assert_eq!(anchors, baseline_module_fingerprints);
    assert_eq!(
        transformations,
        BTreeSet::from([applied.transformation_id.to_string()])
    );
}

fn patch_edits_mut(patch: &mut SemanticJson) -> &mut Vec<SemanticJson> {
    let fields = object_mut(patch);
    match fields.get_mut("edits").expect("edits") {
        SemanticJson::Array(edits) => edits,
        _ => panic!("edits array"),
    }
}

fn object_mut(value: &mut SemanticJson) -> &mut BTreeMap<String, SemanticJson> {
    match value {
        SemanticJson::Object(fields) => fields,
        _ => panic!("object"),
    }
}

fn first_sentence_value_mut(definition: &mut SemanticJson) -> &mut SemanticJson {
    let modules = object_mut(definition).get_mut("modules").expect("modules");
    let SemanticJson::Array(modules) = modules else {
        panic!("modules array")
    };
    let sentences = object_mut(&mut modules[0])
        .get_mut("sentences")
        .expect("sentences");
    let SemanticJson::Array(sentences) = sentences else {
        panic!("sentences array")
    };
    object_mut(&mut sentences[0])
        .get_mut("value")
        .expect("value")
}

fn first_sentence_provenance(definition: &SemanticJson) -> &BTreeMap<String, SemanticJson> {
    object(definition)
        .get("modules")
        .and_then(SemanticJson::as_array)
        .and_then(|modules| object(&modules[0]).get("sentences"))
        .and_then(SemanticJson::as_array)
        .and_then(|sentences| object(&sentences[0]).get("provenance"))
        .and_then(SemanticJson::as_object)
        .expect("provenance")
}

fn refresh_test_definition(definition: &mut SemanticJson) {
    let root = object_mut(definition);
    let schema = root.get("schemaVersion").expect("schema").clone();
    let representation = root.get("representation").expect("representation").clone();
    let family = root
        .get("baselineFamilyId")
        .expect("baselineFamilyId")
        .clone();
    let SemanticJson::Array(modules) = root.get_mut("modules").expect("modules") else {
        panic!("modules array")
    };
    let mut module_payloads = Vec::new();
    for module in modules {
        let fields = object_mut(module);
        let name = fields.get("name").expect("name").clone();
        let ordinal = fields.get("ordinal").expect("ordinal").clone();
        let imports = fields.get("imports").expect("imports").clone();
        let SemanticJson::Array(sentences) = fields.get_mut("sentences").expect("sentences") else {
            panic!("sentences array")
        };
        let mut contents = Vec::new();
        for sentence in sentences {
            let fields = object_mut(sentence);
            let value = fields.get("value").expect("value").clone();
            let value = object(&value);
            let provenance = object_mut(fields.get_mut("provenance").expect("provenance"));
            for key in ["module", "label", "kind", "source", "location"] {
                provenance.insert(key.to_owned(), value.get(key).expect(key).clone());
            }
            let body_payload = SemanticJson::Object(BTreeMap::from([
                ("body".to_owned(), value.get("body").expect("body").clone()),
                (
                    "requires".to_owned(),
                    value.get("requires").expect("requires").clone(),
                ),
                (
                    "ensures".to_owned(),
                    value.get("ensures").expect("ensures").clone(),
                ),
            ]));
            let body = digest(&domain("k-in-k/sentence-body/v1"), &body_payload);
            provenance.insert(
                "bodyFingerprint".to_owned(),
                SemanticJson::String(body.to_string()),
            );
            let content_payload = SemanticJson::Object(BTreeMap::from([
                (
                    "lineageId".to_owned(),
                    provenance.get("lineageId").expect("lineageId").clone(),
                ),
                (
                    "module".to_owned(),
                    value.get("module").expect("module").clone(),
                ),
                (
                    "label".to_owned(),
                    value.get("label").expect("label").clone(),
                ),
                ("kind".to_owned(), value.get("kind").expect("kind").clone()),
                (
                    "source".to_owned(),
                    value.get("source").expect("source").clone(),
                ),
                (
                    "location".to_owned(),
                    value.get("location").expect("location").clone(),
                ),
                (
                    "generated".to_owned(),
                    provenance.get("generated").expect("generated").clone(),
                ),
                (
                    "bodyFingerprint".to_owned(),
                    SemanticJson::String(body.to_string()),
                ),
                (
                    "attributes".to_owned(),
                    value.get("attributes").expect("attributes").clone(),
                ),
                (
                    "transformationChain".to_owned(),
                    provenance
                        .get("transformationChain")
                        .expect("transformationChain")
                        .clone(),
                ),
            ]));
            let content = digest(&domain("k-in-k/sentence-content/v1"), &content_payload);
            provenance.insert(
                "contentFingerprint".to_owned(),
                SemanticJson::String(content.to_string()),
            );
            contents.push(SemanticJson::String(content.to_string()));
        }
        let module_payload = SemanticJson::Object(BTreeMap::from([
            ("name".to_owned(), name),
            ("ordinal".to_owned(), ordinal),
            ("imports".to_owned(), imports),
            (
                "sentenceContentFingerprints".to_owned(),
                SemanticJson::Array(contents),
            ),
        ]));
        let fingerprint = digest(&domain("k-in-k/module/v1"), &module_payload);
        fields.insert(
            "fingerprint".to_owned(),
            SemanticJson::String(fingerprint.to_string()),
        );
        module_payloads.push(module_payload);
    }
    let definition_payload = SemanticJson::Object(BTreeMap::from([
        ("schemaVersion".to_owned(), schema),
        ("representation".to_owned(), representation),
        ("baselineFamilyId".to_owned(), family),
        ("modules".to_owned(), SemanticJson::Array(module_payloads)),
    ]));
    root.insert(
        "definitionDigest".to_owned(),
        SemanticJson::String(
            digest(&domain("k-in-k/definition/v1"), &definition_payload).to_string(),
        ),
    );
}
