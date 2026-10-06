//! Sentence versions and original-relative patch pins.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::definition::{AttributeKey, Attributes, Sentence};
use k_rust::kast::{Sort, Term};
use kink_patch::{
    Baseline, Edit, FingerprintError, InsertPosition, POSITION_KEYS, Patch, PatchFailureKind,
    PatchModelError, SelectionPolicy, SentenceFingerprint, SentenceOrigin, SentenceRef,
    Sha256Digest, SiteSelector, TermRef, apply, derive_sites, fingerprint_payload, select, sha256,
};
use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

fn boolean(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Bool"),
    }
}

fn requires_edit(baseline: &Baseline, at: SentenceRef) -> Edit {
    let at = TermRef::new(at, [1]);
    let expected = baseline.term(&at).expect("requires").clone();
    let replacement = boolean(expected != boolean(true));
    Edit::ReplaceTerm {
        at,
        expected,
        replacement,
    }
}

fn variant(directory: &str, contents: &str) -> Baseline {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(directory);
    fs::create_dir_all(&dir).expect("directory");
    let path = dir.join("counter.k");
    fs::write(&path, contents).expect("variant");
    support::load_path(&path, "COUNTER")
}

fn table(baseline: &Baseline) -> Vec<(SentenceRef, SentenceFingerprint)> {
    baseline
        .definition()
        .modules
        .iter()
        .flat_map(|module| {
            module
                .local_sentences
                .iter()
                .enumerate()
                .map(|(index, sentence)| {
                    (
                        SentenceRef::new(&module.name, u32::try_from(index).expect("index")),
                        SentenceFingerprint::of(sentence).expect("fingerprint"),
                    )
                })
        })
        .collect()
}

#[test]
fn digest_known_answers() {
    for (bytes, expected) in [
        (
            &b""[..],
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        ),
        (
            &b"abc"[..],
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        ),
        (
            &[0xef, 0xbb, 0xbf, 0x61, 0x0d, 0x0a, 0x62, 0x00, 0xff][..],
            "190cea37c95f6ef0e8c57ea9bb936eba699b3feae844706288b397ac4f8b313b",
        ),
    ] {
        let digest = sha256(bytes);
        assert_eq!(digest.to_string(), expected);
        assert_eq!(Sha256Digest::parse(expected), Some(digest));
        assert_eq!(digest.as_bytes().len(), 32);
        assert_eq!(Sha256Digest::parse(&expected.to_uppercase()), None);
        assert_eq!(Sha256Digest::parse(&expected[..63]), None);
    }
    assert_eq!(Sha256Digest::parse(&"g".repeat(64)), None);
}

#[test]
fn fingerprint_literals() {
    for (file, label, expected) in [
        (
            "counter.k",
            "COUNTER.increment",
            "54fe0f8ab4a2960043bf920269631e53512f3777f1a35c10da9db9a0812cc935",
        ),
        (
            "counter.k",
            "COUNTER.branch",
            "7454c0491e2f2b3304b29466287c5a38accc466dfe7367fc406e6164316a057e",
        ),
        (
            "counter.k",
            "COUNTER.fallback",
            "eacff122ceaec16b124f4e3f6cff9cdf6e84c10092dc55548b83e1c8f9399480",
        ),
        (
            "symmem.k",
            "SYMMEM.write",
            "66212f2ac7ed0cdc6554f02845d8435217715a7a495ec0e1d38d46ad5aa5d753",
        ),
        (
            "symmem.k",
            "SYMMEM.load",
            "6fb6e1b1cfefdc0c4244e2f13bf9655c272b2ba5602cf2940fc86e9eb098ac83",
        ),
        (
            "guardedmem.k",
            "GUARDEDMEM.load",
            "16ad805e89809abe110e642c93022e808c5c20cfab12fce5b2ca115422032f45",
        ),
    ] {
        let baseline = support::load(file);
        let fingerprint = baseline
            .fingerprint(&support::rule(&baseline, label))
            .expect("fingerprint");
        assert_eq!(fingerprint.to_string(), expected, "{label}");
        assert_eq!(SentenceFingerprint::parse(expected), Some(fingerprint));
    }
    let baseline = support::load("duplicate_unlabelled.k");
    for index in [0, 1] {
        assert_eq!(
            baseline
                .fingerprint(&SentenceRef::new("DUPLICATE_UNLABELLED", index))
                .expect("fingerprint")
                .to_string(),
            "c50da9161073410bd52e410ec7e01c2c28efe4afb0792055bc48d5ede0407850"
        );
    }
}

#[test]
fn fingerprint_payload_is_position_free() {
    let baseline = support::load("counter.k");
    let payload = fingerprint_payload(
        baseline
            .sentence(&support::rule(&baseline, "COUNTER.increment"))
            .expect("sentence"),
    )
    .expect("payload");
    let json: serde_json::Value = serde_json::from_str(&payload).expect("JSON");
    assert_eq!(json["format"], "KAST");
    assert_eq!(json["version"], 4);
    assert!(payload.contains("COUNTER.increment"));
    for key in POSITION_KEYS {
        assert!(!payload.contains(key.as_str()), "{}", key.as_str());
    }
}

#[test]
fn fingerprints_are_stable_across_loads_and_reformatting() {
    let start = Instant::now();
    let mut paths: Vec<PathBuf> = fs::read_dir(support::DIR)
        .expect("fixtures")
        .map(|entry| entry.expect("entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
        .collect();
    paths.sort();
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("fingerprint-reformat");
    fs::create_dir_all(&dir).expect("directory");
    for path in &paths {
        let text = fs::read_to_string(path).expect("fixture");
        let main_module = text
            .lines()
            .filter_map(|line| line.trim().strip_prefix("module "))
            .next_back()
            .expect("main module")
            .split_whitespace()
            .next()
            .expect("name");
        let first = table(&support::load_path(path, main_module));
        assert_eq!(
            first,
            table(&support::load_path(path, main_module)),
            "{}",
            path.display()
        );
        let reformatted = dir.join(path.file_name().expect("name"));
        fs::write(
            &reformatted,
            format!("// fingerprint reformat probe\n\n\n{text}"),
        )
        .expect("reformatted");
        assert_eq!(
            first,
            table(&support::load_path(&reformatted, main_module)),
            "{}",
            path.display()
        );
    }
    eprintln!(
        "fingerprint stability: {} definitions in {:?}",
        paths.len(),
        start.elapsed()
    );
}

fn assert_changes(baseline: &Baseline, patch: Patch) {
    let patch = patch.pinned(baseline).expect("pins");
    let mutant = apply(baseline, &patch).expect("applies");
    let written = patch.written_sentences();
    let mut changed = Vec::new();
    for (output, origin) in mutant.origins() {
        let SentenceOrigin::Baseline(at) = origin else {
            panic!("no insertions")
        };
        let sentence = mutant
            .definition()
            .modules
            .iter()
            .find(|module| module.name == output.module)
            .expect("module")
            .local_sentences
            .get(usize::try_from(output.index).expect("index"))
            .expect("sentence");
        let differs = SentenceFingerprint::of(sentence).expect("new")
            != baseline.fingerprint(at).expect("old");
        assert_eq!(differs, written.contains(at), "{at:?}");
        if differs {
            changed.push(at.clone());
        }
    }
    changed.sort();
    assert_eq!(changed, written);
}

#[test]
fn only_written_sentences_change_fingerprint() {
    for file in ["counter.k", "symmem.k"] {
        let baseline = support::load(file);
        for (at, _) in baseline
            .authored_sentences()
            .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
        {
            assert_changes(
                &baseline,
                Patch::new(vec![requires_edit(&baseline, at)]).expect("patch"),
            );
        }
        if file == "symmem.k" {
            assert_changes(
                &baseline,
                Patch::new(
                    ["SYMMEM.write", "SYMMEM.load"]
                        .map(|label| requires_edit(&baseline, support::rule(&baseline, label)))
                        .to_vec(),
                )
                .expect("patch"),
            );
        }
    }
}

#[test]
fn fold_pins_every_candidate() {
    let baseline = support::load("counter.k");
    let discovery =
        derive_sites(&baseline, "condition", &[SiteSelector::Path(vec![1])]).expect("sites");
    let generation = select(&discovery, SelectionPolicy::Each, 100)
        .expect("selection")
        .fold("toggle-requires", |origin| {
            Patch::new(
                origin
                    .site_tuple
                    .iter()
                    .map(|site| requires_edit(&baseline, site.sentence.clone()))
                    .collect(),
            )
            .expect("patch")
        })
        .expect("fold");
    assert!(!generation.candidates().is_empty());
    for candidate in generation.candidates() {
        assert!(candidate.patch.is_pinned());
        assert_eq!(
            candidate.patch.pins().keys().cloned().collect::<Vec<_>>(),
            candidate.patch.addressed_sentences()
        );
        for (at, pin) in candidate.patch.pins() {
            assert_eq!(*pin, baseline.fingerprint(at).expect("fingerprint"));
        }
    }
}

#[test]
fn stale_fingerprints_are_refused() {
    let baseline = support::load("counter.k");
    let text = fs::read_to_string(Path::new(support::DIR).join("counter.k")).expect("source");
    let changed = variant(
        "fingerprint-stale",
        &text.replace("counter(s(N), L)", "counter(s(s(N)), L)"),
    );
    let reformatted = variant(
        "fingerprint-stale-reformat",
        &format!("// fingerprint reformat probe\n\n\n{text}"),
    );
    let increment = support::rule(&baseline, "COUNTER.increment");
    assert_eq!(increment, SentenceRef::new("COUNTER", 0));
    let mut anonymous = baseline
        .sentence(&support::rule(&baseline, "COUNTER.fallback"))
        .expect("fallback")
        .clone();
    for key in POSITION_KEYS
        .into_iter()
        .chain([AttributeKey::Label, AttributeKey::UniqueId])
    {
        anonymous.attributes_mut().remove(key.as_str());
    }
    let edits = [
        requires_edit(&baseline, increment.clone()),
        Edit::DeleteSentence {
            at: increment.clone(),
        },
        Edit::InsertSentence {
            position: InsertPosition::Before(increment.clone()),
            ordinal: 0,
            sentence: anonymous,
        },
        Edit::AddAttribute {
            at: increment,
            key: "owise".to_owned(),
            value: serde_json::Value::String(String::new()),
        },
    ];
    for (index, edit) in edits.into_iter().enumerate() {
        let unpinned = Patch::new(vec![edit]).expect("patch");
        let pinned = unpinned.clone().pinned(&baseline).expect("pins");
        assert!(apply(&baseline, &pinned).is_ok());
        assert!(apply(&reformatted, &pinned).is_ok());
        assert_eq!(
            apply(&changed, &pinned)
                .expect_err("stale publishes nothing")
                .kind(),
            PatchFailureKind::StalePrecondition
        );
        assert_eq!(
            pinned
                .pinned(&changed)
                .expect_err("repinning refuses stale")
                .kind(),
            PatchFailureKind::StalePrecondition
        );
        let result = apply(&changed, &unpinned);
        if index < 3 {
            assert!(result.is_ok(), "unpinned {index}: {result:?}");
        } else {
            eprintln!(
                "unpinned AddAttribute on B: {}",
                result
                    .as_ref()
                    .map(|_| "applied".to_owned())
                    .unwrap_or_else(|error| error.to_string())
            );
        }
    }
}

#[test]
fn context_alias_has_no_fingerprint() {
    let sentence = Sentence::ContextAlias {
        body: Term::apply("z", vec![]),
        requires: boolean(true),
        attributes: Attributes::default(),
    };
    assert_eq!(
        SentenceFingerprint::of(&sentence),
        Err(FingerprintError::ContextAlias)
    );
}

#[test]
fn with_pins_requires_exact_coverage() {
    let baseline = support::load("counter.k");
    let at = support::rule(&baseline, "COUNTER.increment");
    let edits = vec![requires_edit(&baseline, at.clone())];
    let pin = baseline.fingerprint(&at).expect("fingerprint");
    assert_eq!(
        Patch::with_pins(edits.clone(), vec![]),
        Err(PatchModelError::PinMismatch)
    );
    let extra = support::rule(&baseline, "COUNTER.branch");
    assert_eq!(
        Patch::with_pins(
            edits.clone(),
            vec![
                (at.clone(), pin),
                (extra.clone(), baseline.fingerprint(&extra).expect("extra"))
            ]
        ),
        Err(PatchModelError::PinMismatch)
    );
    assert_eq!(
        Patch::with_pins(edits.clone(), vec![(at.clone(), pin), (at.clone(), pin)]),
        Err(PatchModelError::PinMismatch)
    );
    assert_eq!(
        Patch::with_pins(edits.clone(), vec![(at, pin)]).expect("exact"),
        Patch::new(edits)
            .expect("patch")
            .pinned(&baseline)
            .expect("pins")
    );
}
