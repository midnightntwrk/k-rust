#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::{
    definition::{AttributeKey, Attributes, Sentence},
    kast::{Sort, Term},
};
use kink_patch::{
    Baseline, CodecError, Edit, InsertPosition, Patch, TermRef, apply, canonical_json,
    structure_sha256,
};
use serde_json::{Value, json};

fn boolean(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Bool"),
    }
}
fn patches(b: &Baseline) -> Vec<Patch> {
    let at = support::rule(b, "COUNTER.increment");
    let target = TermRef::new(at.clone(), [1]);
    let sentence = b.sentence(&at).unwrap().clone();
    let mut inserted = sentence.clone();
    for key in kink_patch::POSITION_KEYS
        .into_iter()
        .chain([AttributeKey::Label, AttributeKey::UniqueId])
    {
        inserted.attributes_mut().unset(key);
    }
    let edits = vec![
        Edit::ReplaceTerm {
            at: target.clone(),
            expected: b.term(&target).unwrap().clone(),
            replacement: boolean(false),
        },
        Edit::ReplaceSentence {
            at: at.clone(),
            replacement: sentence.clone(),
        },
        Edit::DeleteSentence { at: at.clone() },
        Edit::AddAttribute {
            at: at.clone(),
            key: "owise".into(),
            value: json!(""),
        },
        Edit::RemoveAttribute {
            at: at.clone(),
            key: AttributeKey::Label.as_str().into(),
            expected: json!("COUNTER.increment"),
        },
        Edit::ReplaceAttribute {
            at: at.clone(),
            key: AttributeKey::Label.as_str().into(),
            expected: json!("COUNTER.increment"),
            replacement: json!("COUNTER.changed"),
        },
    ];
    let mut patches = edits
        .into_iter()
        .map(|edit| Patch::new(vec![edit]).unwrap().pinned(b).unwrap())
        .collect::<Vec<_>>();
    for position in [
        InsertPosition::Before(at.clone()),
        InsertPosition::After(at),
        InsertPosition::ModuleStart("COUNTER".into()),
        InsertPosition::ModuleEnd("COUNTER".into()),
    ] {
        patches.push(
            Patch::new(vec![Edit::InsertSentence {
                position,
                ordinal: 0,
                sentence: inserted.clone(),
            }])
            .unwrap()
            .pinned(b)
            .unwrap(),
        );
    }
    patches
}
fn keys(value: &Value, expected: &[&str]) {
    let actual = value
        .as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect::<Vec<_>>();
    let mut expected = expected.to_vec();
    expected.sort();
    assert_eq!(actual, expected);
}
fn round_trip(patch: &Patch) {
    let text = patch.canonical_json().unwrap();
    let read = Patch::from_canonical_json(&text).unwrap();
    assert_eq!(&read, patch);
    assert_eq!(read.canonical_json().unwrap(), text);
    assert_eq!(read.digest().unwrap(), patch.digest().unwrap());
    assert_eq!(patch.digest().unwrap(), patch.digest().unwrap());
    let value = patch.canonical_value().unwrap();
    keys(&value, &["version", "edits", "pins"]);
    for pin in value["pins"].as_array().unwrap() {
        keys(pin, &["module", "index", "fingerprint"]);
    }
    for edit in value["edits"].as_array().unwrap() {
        let expected: &[&str] = match edit["op"].as_str().unwrap() {
            "replace-term" => &["op", "sentence", "path", "expected", "replacement"],
            "replace-sentence" => &["op", "sentence", "replacement"],
            "delete-sentence" => &["op", "sentence"],
            "insert-sentence" => &["op", "position", "ordinal", "sentence"],
            "add-attribute" => &["op", "sentence", "key", "value"],
            "remove-attribute" => &["op", "sentence", "key", "expected"],
            "replace-attribute" => &["op", "sentence", "key", "expected", "replacement"],
            op => panic!("{op}"),
        };
        keys(edit, expected);
        if edit["op"] != "insert-sentence" {
            keys(&edit["sentence"], &["module", "index"]);
        } else {
            let pos = edit["position"].as_object().unwrap();
            assert_eq!(pos.len(), 1);
            for (kind, at) in pos {
                if matches!(kind.as_str(), "before" | "after") {
                    keys(at, &["module", "index"]);
                } else {
                    assert!(matches!(kind.as_str(), "module-start" | "module-end"));
                    assert!(at.is_string());
                }
            }
        }
    }
}

#[test]
fn all_edit_variants_round_trip_with_exact_keys_and_stable_digests() {
    let first = support::load("counter.k");
    let second = support::load("counter.k");
    for (p, q) in patches(&first).iter().zip(patches(&second)) {
        round_trip(p);
        assert_eq!(p.canonical_json().unwrap(), q.canonical_json().unwrap());
        assert_eq!(p.digest().unwrap(), q.digest().unwrap());
    }
}
fn coupled(b: &Baseline) -> Patch {
    Patch::new(
        ["SYMMEM.write", "SYMMEM.load"]
            .into_iter()
            .map(|label| {
                let at = TermRef::new(support::rule(b, label), [0, 1]);
                let expected = b.term(&at).unwrap().clone();
                let address = b
                    .term(&TermRef::new(support::rule(b, label), [0, 0, 0, 0]))
                    .unwrap()
                    .clone();
                Edit::ReplaceTerm {
                    at,
                    expected: expected.clone(),
                    replacement: Term::apply(
                        "seq",
                        vec![Term::apply("free", vec![address]), expected],
                    ),
                }
            })
            .collect(),
    )
    .unwrap()
    .pinned(b)
    .unwrap()
}
#[test]
fn coupled_patch_round_trip_and_noncanonical_refusals() {
    let first = support::load("symmem.k");
    let second = support::load("symmem.k");
    let p = coupled(&first);
    let q = coupled(&second);
    round_trip(&p);
    assert_eq!(p.digest().unwrap(), q.digest().unwrap());
    let read = Patch::from_canonical_json(&p.canonical_json().unwrap()).unwrap();
    let original_mutant = apply(&first, &p).unwrap();
    let rebuilt = apply(&first, &read).unwrap();
    assert_eq!(original_mutant.definition(), rebuilt.definition());
    assert_eq!(
        structure_sha256(original_mutant.definition()),
        structure_sha256(rebuilt.definition())
    );
    assert_eq!(
        support::compile(&original_mutant.to_loaded(&first).unwrap()).unwrap(),
        support::compile(&rebuilt.to_loaded(&first).unwrap()).unwrap()
    );
    let value = p.canonical_value().unwrap();
    assert!(matches!(
        Patch::from_canonical_json(&serde_json::to_string_pretty(&value).unwrap()),
        Err(CodecError::NonCanonical)
    ));
    let mut reversed = value.clone();
    reversed["edits"].as_array_mut().unwrap().reverse();
    assert!(matches!(
        Patch::from_canonical_json(&canonical_json(&reversed)),
        Err(CodecError::NonCanonical)
    ));
    let mut extra = value.clone();
    extra["extra"] = json!(0);
    assert!(matches!(
        Patch::from_canonical_json(&canonical_json(&extra)),
        Err(CodecError::Decode(_))
    ));
    let mut mistyped = value;
    mistyped["edits"][0]["path"] = json!([1.5]);
    assert!(matches!(
        Patch::from_canonical_json(&canonical_json(&mistyped)),
        Err(CodecError::Decode(_))
    ));
}
#[test]
fn unpinned_and_context_alias_are_refused() {
    let baseline = support::load("counter.k");
    let at = support::rule(&baseline, "COUNTER.increment");
    let patch = Patch::new(vec![Edit::DeleteSentence { at: at.clone() }]).unwrap();
    assert_eq!(patch.canonical_json(), Err(CodecError::Unpinned));
    let replacement = Sentence::ContextAlias {
        body: Term::apply("z", vec![]),
        requires: boolean(true),
        attributes: Attributes::default(),
    };
    let patch = Patch::new(vec![Edit::ReplaceSentence {
        at,
        replacement: replacement.clone(),
    }])
    .unwrap()
    .pinned(&baseline)
    .unwrap();
    assert_eq!(patch.canonical_json(), Err(CodecError::ContextAlias));
    let patch = Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::ModuleEnd("COUNTER".into()),
        ordinal: 0,
        sentence: replacement,
    }])
    .unwrap()
    .pinned(&baseline)
    .unwrap();
    assert_eq!(patch.canonical_json(), Err(CodecError::ContextAlias));
}
