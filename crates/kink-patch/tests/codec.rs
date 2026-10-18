#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::{
    definition::{AttributeKey, Attributes, Sentence},
    kast::{Sort, Term},
};
use kink_patch::{
    Baseline, CodecError, Edit, InsertPosition, JsonError, MAX_JSON_DEPTH, Patch, TermRef, apply,
    canonical_json, json_depth, parse_json, structure_sha256, value_depth,
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
    // Re-pin L1-3-tail: the depth the codec sizes its stack from is the document's exactly.
    assert_eq!(patch.document_depth().unwrap(), value_depth(&value));
    assert_eq!(json_depth(&text), value_depth(&value));
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

/// Re-pin L1-3-fix-1: a patch whose terms are 60, 200 or 1500 levels deep encodes, decodes and
/// re-encodes byte-equally, as a shallow one does. serde_json's recursion limit of 128 nested
/// values used to refuse every term more than about 55 levels deep (KAST JSON takes two levels
/// per term level), so kink-flow reported a valid mutation of a deep rule as invalid-mutation
/// (review L1-3-1). On a 256 MiB thread, as kink's commands run.
#[test]
fn deep_terms_round_trip_past_serde_jsons_recursion_limit() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let baseline = support::load("counter.k");
            let at = support::rule(&baseline, "COUNTER.increment");
            let target = TermRef::new(at.clone(), [1]);
            for depth in [60, 200, 1500] {
                let mut deep = Term::apply("z", vec![]);
                for _ in 0..depth {
                    deep = Term::apply("s", vec![deep]);
                }
                let mut sentence = baseline.sentence(&at).unwrap().clone();
                let Sentence::Rule { requires, .. } = &mut sentence else {
                    panic!("a rule");
                };
                *requires = deep.clone();
                for edit in [
                    Edit::ReplaceTerm {
                        at: target.clone(),
                        expected: baseline.term(&target).unwrap().clone(),
                        replacement: deep.clone(),
                    },
                    Edit::ReplaceSentence {
                        at: at.clone(),
                        replacement: sentence.clone(),
                    },
                ] {
                    let patch = Patch::new(vec![edit]).unwrap().pinned(&baseline).unwrap();
                    round_trip(&patch);
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Re-pin L1-3-tail (review L1-3-fix-2-1 D1): `Patch::document_depth`, which the codec sizes its
/// stack from and refuses past the limit by, is the depth of the patch's canonical document, for
/// every edit kind and for terms, sentences and attribute values of any depth, pinned or not. At
/// L1-3-fix-2 the codec took a segment sized for `MAX_JSON_DEPTH` (768 MB in release) for every
/// patch more than 48 term levels deep, which an address-space limit refused; a patch 60 term
/// levels deep now needs a document of about 130 levels.
#[test]
fn the_document_depth_is_the_canonical_documents_depth() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let baseline = support::load("counter.k");
            let at = support::rule(&baseline, "COUNTER.increment");
            let target = TermRef::new(at.clone(), [1]);
            let mut attribute = json!("deep");
            for _ in 0..300 {
                attribute = json!([attribute]);
            }
            let mut edits = vec![
                Edit::AddAttribute {
                    at: at.clone(),
                    key: "deep".into(),
                    value: attribute.clone(),
                },
                Edit::ReplaceAttribute {
                    at: at.clone(),
                    key: AttributeKey::Label.as_str().into(),
                    expected: json!("COUNTER.increment"),
                    replacement: attribute,
                },
            ];
            for depth in [1, 60, 200] {
                let mut sentence = baseline.sentence(&at).unwrap().clone();
                let Sentence::Rule { requires, .. } = &mut sentence else {
                    panic!("a rule");
                };
                *requires = numeral(depth);
                edits.push(Edit::ReplaceTerm {
                    at: target.clone(),
                    expected: baseline.term(&target).unwrap().clone(),
                    replacement: numeral(depth),
                });
                edits.push(Edit::ReplaceSentence {
                    at: at.clone(),
                    replacement: sentence,
                });
            }
            let mut checked = 0;
            for patch in patches(&baseline).into_iter().chain(
                edits
                    .into_iter()
                    .map(|edit| Patch::new(vec![edit]).unwrap().pinned(&baseline).unwrap()),
            ) {
                let value = patch.canonical_value().unwrap();
                let depth = patch.document_depth().unwrap();
                assert_eq!(depth, value_depth(&value), "{value}");
                assert_eq!(json_depth(&patch.canonical_json().unwrap()), depth);
                let unpinned = Patch::new(patch.edits().to_vec()).unwrap();
                assert_eq!(unpinned.document_depth().unwrap(), depth);
                checked += 1;
            }
            assert_eq!(checked, 18);
            // The review's 60-deep mutation: a document of 2 x 60 levels and a constant, not
            // MAX_JSON_DEPTH.
            let mut sentence = baseline.sentence(&at).unwrap().clone();
            let Sentence::Rule { requires, .. } = &mut sentence else {
                panic!("a rule");
            };
            *requires = numeral(60);
            let depth = Patch::new(vec![Edit::ReplaceSentence {
                at,
                replacement: sentence,
            }])
            .unwrap()
            .document_depth()
            .unwrap();
            assert!((120..160).contains(&depth), "{depth}");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A Peano numeral `depth` levels above `z`.
fn numeral(depth: usize) -> Term {
    let mut deep = Term::apply("z", vec![]);
    for _ in 0..depth {
        deep = Term::apply("s", vec![deep]);
    }
    deep
}

/// Re-pin L1-3-fix-2 (review L1-3-2 D3): a patch is encoded and decoded on a stack sized from its
/// depth, so a thread whose stack the depth exceeds gives the text, decoding and digest a 256 MiB
/// thread gives. A term 20,000 levels deep took about 78 MB of stack to encode unoptimized, and
/// on this 4 MiB thread the fix-1 codec aborted the process.
#[test]
fn a_deep_patch_encodes_and_decodes_alike_on_a_thread_too_small_for_it() {
    const DEPTH: usize = 20_000;
    let (patches, texts) = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let baseline = support::load("counter.k");
            let at = support::rule(&baseline, "COUNTER.increment");
            let target = TermRef::new(at.clone(), [1]);
            let mut sentence = baseline.sentence(&at).unwrap().clone();
            let Sentence::Rule { requires, .. } = &mut sentence else {
                panic!("a rule");
            };
            *requires = numeral(DEPTH);
            let patches = [
                Edit::ReplaceTerm {
                    at: target.clone(),
                    expected: baseline.term(&target).unwrap().clone(),
                    replacement: numeral(DEPTH),
                },
                Edit::ReplaceSentence {
                    at,
                    replacement: sentence,
                },
            ]
            .map(|edit| Patch::new(vec![edit]).unwrap().pinned(&baseline).unwrap());
            let texts = patches
                .iter()
                .map(|patch| patch.canonical_json().unwrap())
                .collect::<Vec<_>>();
            (patches, texts)
        })
        .unwrap()
        .join()
        .unwrap();
    for (patch, text) in patches.into_iter().zip(texts) {
        assert!(json_depth(&text) > 2 * DEPTH, "{}", json_depth(&text));
        let expected_digest =
            kink_patch::payload_digest(kink_patch::CANONICAL_PATCH_DOMAIN, text.as_bytes());
        std::thread::Builder::new()
            .stack_size(4 << 20)
            .spawn(move || {
                assert_eq!(patch.canonical_json().unwrap(), text);
                assert_eq!(patch.digest().unwrap(), expected_digest);
                let read = Patch::from_canonical_json(&text).unwrap();
                assert!(read == patch);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

/// Re-pin L1-3-fix-2 (review L1-3-2 D3): `parse_json` parses a document exactly
/// `MAX_JSON_DEPTH` levels deep and refuses one level more as `TooDeep`, before parsing any of
/// it, where the fix-1 parser had no bound and aborted the process on a deep enough document.
/// The patch codec refuses such a document by the same limit. Brackets inside strings are not
/// nesting. On a 256 MiB thread, as kink's commands run (the parsed document is dropped there).
#[test]
fn parse_json_refuses_one_level_past_its_limit() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let nested = |depth: usize| format!("{}{}", "[".repeat(depth), "]".repeat(depth));
            let at_limit = nested(MAX_JSON_DEPTH);
            let value = parse_json(&at_limit).unwrap();
            assert_eq!(value_depth(&value), MAX_JSON_DEPTH);
            assert_eq!(canonical_json(&value), at_limit);
            drop(value);
            let past = nested(MAX_JSON_DEPTH + 1);
            let refused = parse_json(&past).unwrap_err();
            assert!(
                matches!(refused, JsonError::TooDeep { depth, limit }
                    if depth == MAX_JSON_DEPTH + 1 && limit == MAX_JSON_DEPTH),
                "{refused:?}"
            );
            assert!(refused.to_string().contains("MAX_JSON_DEPTH"), "{refused}");
            assert_eq!(
                Patch::from_canonical_json(&past),
                Err(CodecError::TooDeep {
                    depth: MAX_JSON_DEPTH + 1,
                    limit: MAX_JSON_DEPTH
                })
            );
            assert_eq!(json_depth(r#"["[[[\"", {"a":"]]{"}, [[]]]"#), 3);
            assert!(matches!(parse_json("[[1]"), Err(JsonError::Syntax(_))));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Re-pin L1-3-fix-2: a patch whose document would nest past `MAX_JSON_DEPTH` (a term half as
/// deep: KAST JSON takes two levels per term level) has no encoding, and the refusal names kink's
/// limit (`TooDeep`), not a malformed patch.
#[test]
fn a_patch_past_the_document_limit_is_refused_as_too_deep() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let baseline = support::load("counter.k");
            let at = support::rule(&baseline, "COUNTER.increment");
            let target = TermRef::new(at, [1]);
            let patch = Patch::new(vec![Edit::ReplaceTerm {
                at: target.clone(),
                expected: baseline.term(&target).unwrap().clone(),
                replacement: numeral(MAX_JSON_DEPTH / 2),
            }])
            .unwrap()
            .pinned(&baseline)
            .unwrap();
            for refused in [
                patch.canonical_json().map(|_| ()),
                patch.digest().map(|_| ()),
            ] {
                assert!(
                    matches!(refused, Err(CodecError::TooDeep { depth, limit })
                        if depth > MAX_JSON_DEPTH && limit == MAX_JSON_DEPTH),
                    "{refused:?}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
