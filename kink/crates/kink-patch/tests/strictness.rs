//! Claim removal for strictness edits (PJ-35, U35b) over `testdata/k/strictness.k` and
//! `testdata/k/strictunary.k`: a production edit that changes only its `strict` or `seqstrict`
//! positions redefines nothing where both definitions keep a strict production with two or more
//! nonterminals ([`ClaimSupport`]'s `strictness_only` and `open_freezers`); `hybrid`, an edit of a
//! production-level `result`, a context alias and a definition whose freezers have no argument
//! fail closed (every symbol counts as redefined, so INT's hooked equations refuse the mutant).

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::definition::{AttributeKey, Sentence};
use kink_patch::{Baseline, ClaimSupport, Edit, Patch, SentenceRef};
use serde_json::Value;
use std::collections::BTreeSet;

/// A production's replacement, built from it.
type Rewrite = Box<dyn Fn(&Sentence) -> Sentence>;

fn production(baseline: &Baseline, label: &str) -> (SentenceRef, Sentence) {
    let mut found = baseline.authored_sentences().filter(
        |(_, sentence)| matches!(sentence, Sentence::Production { label: Some(l), .. } if l.name == label),
    );
    let (at, sentence) = found.next().expect("a matching production");
    assert!(found.next().is_none(), "one matching production");
    (at, sentence.clone())
}

/// The production labelled `label` with `key` set to `value`, or removed when `value` is `None`.
fn with(sentence: &Sentence, key: AttributeKey, value: Option<&str>) -> Sentence {
    let mut sentence = sentence.clone();
    if let Some(value) = value {
        sentence
            .attributes_mut()
            .set(key, Value::String(value.to_owned()));
    } else {
        sentence.attributes_mut().remove(key.as_str());
    }
    sentence
}

fn replace(baseline: &Baseline, label: &str, edit: impl Fn(&Sentence) -> Sentence) -> Patch {
    let (at, sentence) = production(baseline, label);
    Patch::new(vec![Edit::ReplaceSentence {
        at,
        replacement: edit(&sentence),
    }])
    .expect("patch")
}

#[track_caller]
fn redefines_nothing(baseline: &Baseline, support: &ClaimSupport, patch: &Patch, what: &str) {
    let withdrawal = support.withdraw(baseline, patch).expect("applies");
    assert!(
        withdrawal.trusted() && withdrawal.withdrawn.is_empty(),
        "{what}: {withdrawal:?}"
    );
    let effect = support.effect(baseline, patch).expect("applies");
    assert_eq!(effect.redefined, Some(BTreeSet::new()), "{what}");
}

#[track_caller]
fn fails_closed(baseline: &Baseline, support: &ClaimSupport, patch: &Patch, what: &str) {
    let effect = support.effect(baseline, patch).expect("applies");
    assert_eq!(effect.redefined, None, "{what}");
    let withdrawal = support.withdraw(baseline, patch).expect("applies");
    assert!(!withdrawal.trusted(), "{what}: {withdrawal:?}");
}

/// A strictness edit lowers to other evaluation contexts, so to other heating and cooling rewrite
/// rules and other freezer constructors of `KItem`, which no sentence names: it redefines no
/// symbol, withdraws no claim and is trusted, though the main module imports INT. Positions are
/// added (`strict(1)` to `strict`, to `strict(1, 2)`), removed (`strict` to `strict(1)`, `strict`
/// removed) or reordered (`strict` to `seqstrict` and back), by a replacement or by an attribute
/// edit; a production that carries a `result` keeps it.
#[test]
fn a_strictness_edit_redefines_nothing() {
    let baseline = support::load("strictness.k");
    let support = ClaimSupport::new(&baseline);
    let strict = AttributeKey::Strict;
    let seqstrict = AttributeKey::Seqstrict;
    for (label, what, edit) in [
        (
            "and",
            "strict(1) to strict",
            Box::new(move |s: &Sentence| with(s, strict, Some(""))) as Rewrite,
        ),
        (
            "and",
            "strict(1) to strict(1, 2)",
            Box::new(move |s: &Sentence| with(s, strict, Some("1, 2"))),
        ),
        (
            "plus",
            "strict to strict(1)",
            Box::new(move |s: &Sentence| with(s, strict, Some("1"))),
        ),
        (
            "plus",
            "strict removed",
            Box::new(move |s: &Sentence| with(s, strict, None)),
        ),
        (
            "neg",
            "strict removed from a unary production",
            Box::new(move |s: &Sentence| with(s, strict, None)),
        ),
        (
            "plus",
            "strict to seqstrict",
            Box::new(move |s: &Sentence| with(&with(s, strict, None), seqstrict, Some(""))),
        ),
        (
            "minus",
            "seqstrict to strict",
            Box::new(move |s: &Sentence| with(&with(s, seqstrict, None), strict, Some(""))),
        ),
        (
            "times",
            "strict to strict(2) beside result(Int)",
            Box::new(move |s: &Sentence| with(s, strict, Some("2"))),
        ),
    ] {
        let patch = replace(&baseline, label, edit);
        redefines_nothing(&baseline, &support, &patch, &format!("{label}: {what}"));
    }
    let (at, _) = production(&baseline, "and");
    let attribute = Patch::new(vec![Edit::ReplaceAttribute {
        at,
        key: "strict".to_owned(),
        expected: Value::String("1".to_owned()),
        replacement: Value::String(String::new()),
    }])
    .expect("patch");
    redefines_nothing(
        &baseline,
        &support,
        &attribute,
        "and: strict(1) to strict, attribute edit",
    );
}

/// Strictness edits not read as redefining nothing: the strictness of a `hybrid` production
/// (its generated `isKResult` equations read the strict positions), an edit of a production's
/// `result`, strictness through a context alias (`strict(c)`, on either side of the edit), a
/// strictness edit beside another attribute edit, and any strictness edit over a definition
/// whose strict productions all have one nonterminal (its freezers have no argument, so finitely
/// many values, whose number a claim could state).
#[test]
fn a_strictness_edit_fails_closed_where_its_effect_is_not_contexts_alone() {
    let baseline = support::load("strictness.k");
    let support = ClaimSupport::new(&baseline);
    let strict = AttributeKey::Strict;
    let cases: [(&str, &str, Rewrite); 5] = [
        (
            "pair",
            "hybrid, strict to strict(1)",
            Box::new(move |s| with(s, strict, Some("1"))),
        ),
        (
            "times",
            "result(Int) removed",
            Box::new(move |s| with(s, AttributeKey::Result, None)),
        ),
        (
            "div",
            "strict(c) to strict",
            Box::new(move |s| with(s, strict, Some(""))),
        ),
        (
            "plus",
            "strict to strict(c)",
            Box::new(move |s| with(s, strict, Some("c"))),
        ),
        (
            "plus",
            "strict to strict(1) beside left",
            Box::new(move |s| with(&with(s, strict, Some("1")), AttributeKey::Left, Some(""))),
        ),
    ];
    for (label, what, edit) in cases {
        let patch = replace(&baseline, label, edit);
        fails_closed(&baseline, &support, &patch, &format!("{label}: {what}"));
    }

    let unary = support::load("strictunary.k");
    let support = ClaimSupport::new(&unary);
    for (label, what, edit) in [
        (
            "neg",
            "strict removed",
            Box::new(move |s: &Sentence| with(s, strict, None)) as Rewrite,
        ),
        (
            "not",
            "strict added",
            Box::new(move |s: &Sentence| with(s, strict, Some(""))),
        ),
    ] {
        let patch = replace(&unary, label, edit);
        fails_closed(&unary, &support, &patch, &format!("{label}: {what}"));
    }
}
