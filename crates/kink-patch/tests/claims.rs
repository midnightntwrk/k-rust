//! The support relation of trusted claims over `testdata/k/claims.k`.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::{Sort, Term};
use kink_patch::{
    Baseline, ClaimSupport, Edit, InsertPosition, Patch, SentenceOrigin, SentenceRef, TermRef,
    Withdrawal, apply,
};
use serde_json::Value;
use std::collections::BTreeSet;

const TOTAL: &str = "total";
const DEFINED: &str = "preserves-definedness";
const SIMPLIFICATION: &str = "simplification";

fn baseline() -> Baseline {
    support::load("claims.k")
}

fn int(value: &str) -> Term {
    Term::Token {
        token: value.to_owned(),
        sort: Sort::new("Int"),
    }
}

fn bool_true() -> Term {
    Term::Token {
        token: "true".to_owned(),
        sort: Sort::new("Bool"),
    }
}

fn rule(baseline: &Baseline, label: &str) -> SentenceRef {
    support::rule(baseline, &format!("CLAIMS.{label}"))
}

fn production(baseline: &Baseline, name: &str) -> SentenceRef {
    baseline
        .authored_sentences()
        .find(|(_, sentence)| {
            matches!(sentence, Sentence::Production { label: Some(label), .. } if label.name == name)
        })
        .map(|(at, _)| at)
        .unwrap_or_else(|| panic!("a production of {name}"))
}

fn replace(baseline: &Baseline, label: &str, path: &[u32], replacement: Term) -> Edit {
    let at = TermRef::new(rule(baseline, label), path);
    Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("baseline term").clone(),
        at,
        replacement,
    }
}

/// A sentence's name: its production's symbol or its rule's label, without the module.
fn name(baseline: &Baseline, at: &SentenceRef) -> String {
    match baseline.sentence(at).expect("a baseline sentence") {
        Sentence::Production {
            label: Some(label), ..
        } => label.name.clone(),
        sentence => sentence
            .attributes()
            .string(AttributeKey::Label)
            .and_then(|label| label.strip_prefix("CLAIMS."))
            .expect("a labelled rule")
            .to_owned(),
    }
}

/// The user-written claims of a list, by (sentence name, key); prelude claims are left out.
fn named(baseline: &Baseline, claims: &[kink_patch::Claim]) -> BTreeSet<(String, String)> {
    claims
        .iter()
        .filter_map(|claim| match &claim.origin {
            SentenceOrigin::Baseline(at) if at.module == "CLAIMS" => {
                Some((name(baseline, at), claim.key.clone()))
            }
            SentenceOrigin::Baseline(_) => None,
            SentenceOrigin::Inserted { edit } => {
                Some((format!("inserted {edit}"), claim.key.clone()))
            }
        })
        .collect()
}

fn set(items: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    items
        .iter()
        .map(|(name, key)| ((*name).to_owned(), (*key).to_owned()))
        .collect()
}

fn withdraw(baseline: &Baseline, edits: Vec<Edit>) -> Withdrawal {
    ClaimSupport::new(baseline)
        .withdraw(baseline, &Patch::new(edits).expect("patch"))
        .expect("the patch applies")
}

/// The withdrawn patch applies, compiles, and no longer carries the withdrawn attributes.
fn assert_withdrawn_patch(baseline: &Baseline, withdrawal: &Withdrawal) {
    let patch = withdrawal.patch().expect("something is withdrawn");
    let mutant = apply(baseline, patch).expect("the withdrawn patch applies");
    support::compile(&mutant.to_loaded(baseline)).expect("the withdrawn mutant compiles");
    for claim in &withdrawal.withdrawn {
        let SentenceOrigin::Baseline(at) = &claim.origin else {
            panic!("a withdrawn claim of a baseline sentence");
        };
        let output = mutant
            .origins()
            .iter()
            .find(|(_, origin)| **origin == claim.origin)
            .map(|(output, _)| output)
            .expect("the sentence survives");
        let sentence = mutant
            .definition()
            .modules
            .iter()
            .find(|module| module.name == output.module)
            .and_then(|module| module.local_sentences.get(output.index as usize))
            .expect("output sentence");
        assert!(
            sentence.attributes().get(&claim.key).is_none(),
            "{at:?} still has {}",
            claim.key
        );
    }
}

/// Probe 3's literal mutant `d() => 0`: f's equations divide by d(), so f's `total`, d's
/// `total`, `step`'s `preserves-definedness` (it mentions f) and the lemma about f all rest
/// on the changed equation; g, `go` and the lemma about g do not.
#[test]
fn a_changed_equation_withdraws_every_claim_resting_on_it() {
    let baseline = baseline();
    let edit = replace(&baseline, "d", &[0, 1], int("0"));
    let withdrawal = withdraw(&baseline, vec![edit.clone()]);
    assert_eq!(
        named(&baseline, &withdrawal.withdrawn),
        set(&[("f", TOTAL), ("d", TOTAL), ("step", DEFINED)])
    );
    assert_eq!(
        named(&baseline, &withdrawal.unsupported),
        set(&[("lemma", SIMPLIFICATION)])
    );
    assert!(!withdrawal.trusted());
    let patch = withdrawal.patch().expect("a withdrawing patch");
    assert!(patch.edits().contains(&edit));
    assert_eq!(patch.edits().len(), 4);
    assert!(patch.edits().contains(&Edit::RemoveAttribute {
        at: production(&baseline, "f"),
        key: TOTAL.to_owned(),
        expected: Value::String(String::new()),
    }));
    assert_withdrawn_patch(&baseline, &withdrawal);
}

/// Support runs from a claim to the equations it rests on, not back: an edit of f's equation
/// withdraws f's claims and those of rules mentioning f, but not d's.
#[test]
fn support_follows_what_equations_mention_not_who_mentions_them() {
    let baseline = baseline();
    let withdrawal = withdraw(
        &baseline,
        vec![replace(&baseline, "f-z", &[0, 1, 0], int("11"))],
    );
    assert_eq!(
        named(&baseline, &withdrawal.withdrawn),
        set(&[("f", TOTAL), ("step", DEFINED)])
    );
    assert_eq!(
        named(&baseline, &withdrawal.unsupported),
        set(&[("lemma", SIMPLIFICATION)])
    );
    assert_withdrawn_patch(&baseline, &withdrawal);
}

/// A rewrite rule is a transition: editing one withdraws only its own claim. An equation no
/// claim rests on withdraws nothing, and its mutant is its own withdrawn definition.
#[test]
fn edits_outside_a_claims_support_withdraw_nothing_of_it() {
    let baseline = baseline();
    let withdrawal = withdraw(&baseline, vec![replace(&baseline, "go", &[1], bool_true())]);
    assert_eq!(
        named(&baseline, &withdrawal.withdrawn),
        set(&[("go", DEFINED)])
    );
    assert!(withdrawal.trusted());
    assert_withdrawn_patch(&baseline, &withdrawal);

    let withdrawal = withdraw(
        &baseline,
        vec![replace(&baseline, "inc", &[0, 1, 1], int("2"))],
    );
    assert_eq!(withdrawal, Withdrawal::default());
    assert!(withdrawal.trusted());
    assert_eq!(withdrawal.patch(), None);
}

/// A claim the patch adds is a hypothesis: withdrawing it would undo the mutant, so it stays
/// and is unsupported. Removing a claim touches every claim that rests on it.
#[test]
fn claims_the_patch_writes_are_unsupported_and_removals_propagate() {
    let baseline = baseline();
    let withdrawal = withdraw(
        &baseline,
        vec![Edit::AddAttribute {
            at: production(&baseline, "inc"),
            key: TOTAL.to_owned(),
            value: Value::String(String::new()),
        }],
    );
    assert_eq!(
        named(&baseline, &withdrawal.unsupported),
        set(&[("inc", TOTAL)])
    );
    assert!(withdrawal.withdrawn.is_empty());
    assert!(!withdrawal.trusted());
    assert_eq!(withdrawal.patch(), None);

    let withdrawal = withdraw(
        &baseline,
        vec![Edit::AddAttribute {
            at: rule(&baseline, "inc"),
            key: DEFINED.to_owned(),
            value: Value::String(String::new()),
        }],
    );
    assert_eq!(
        named(&baseline, &withdrawal.unsupported),
        set(&[("inc", DEFINED)])
    );

    let withdrawal = withdraw(
        &baseline,
        vec![Edit::RemoveAttribute {
            at: production(&baseline, "d"),
            key: TOTAL.to_owned(),
            expected: Value::String(String::new()),
        }],
    );
    assert_eq!(
        named(&baseline, &withdrawal.withdrawn),
        set(&[("f", TOTAL), ("step", DEFINED)])
    );
    assert_eq!(
        named(&baseline, &withdrawal.unsupported),
        set(&[("lemma", SIMPLIFICATION)])
    );
    assert_withdrawn_patch(&baseline, &withdrawal);
}

/// An inserted equation redefines its head. A replacing sentence that carries its
/// original's claim over has the claim dropped from the replacement instead of removed.
#[test]
fn inserted_and_replaced_sentences() {
    let baseline = baseline();
    let mut inserted = baseline
        .sentence(&rule(&baseline, "d"))
        .expect("d's equation")
        .clone();
    for key in [
        AttributeKey::Label,
        AttributeKey::Location,
        AttributeKey::Source,
        AttributeKey::SourceId,
        AttributeKey::SentenceStartOffset,
        AttributeKey::SentenceEndOffset,
        AttributeKey::ContentStartLine,
        AttributeKey::ContentStartColumn,
        AttributeKey::ContentStartOffset,
    ] {
        inserted.attributes_mut().unset(key);
    }
    let withdrawal = withdraw(
        &baseline,
        vec![Edit::InsertSentence {
            position: InsertPosition::ModuleEnd("CLAIMS".to_owned()),
            ordinal: 0,
            sentence: inserted,
        }],
    );
    assert_eq!(
        named(&baseline, &withdrawal.withdrawn),
        set(&[("f", TOTAL), ("d", TOTAL), ("step", DEFINED)])
    );

    let step = rule(&baseline, "step");
    let mut replacement = baseline.sentence(&step).expect("step").clone();
    let Sentence::Rule { requires, .. } = &mut replacement else {
        panic!("a rule");
    };
    *requires = bool_true();
    let withdrawal = withdraw(
        &baseline,
        vec![Edit::ReplaceSentence {
            at: step.clone(),
            replacement,
        }],
    );
    assert_eq!(
        named(&baseline, &withdrawal.withdrawn),
        set(&[("step", DEFINED)])
    );
    assert!(withdrawal.trusted());
    let [Edit::ReplaceSentence { replacement, .. }] =
        withdrawal.patch().expect("a withdrawing patch").edits()
    else {
        panic!("the replacement alone");
    };
    assert!(replacement.attributes().get(DEFINED).is_none());
    assert_withdrawn_patch(&baseline, &withdrawal);
}

/// An edit whose effect on what terms denote is not known symbol by symbol, here deleting a
/// production (which changes its sort's values), withdraws every claim and leaves every
/// lemma unsupported.
#[test]
fn an_unknown_effect_withdraws_every_claim() {
    let baseline = baseline();
    let withdrawal = withdraw(
        &baseline,
        vec![Edit::DeleteSentence {
            at: production(&baseline, "halt"),
        }],
    );
    assert_eq!(
        named(&baseline, &withdrawal.withdrawn),
        set(&[
            ("f", TOTAL),
            ("d", TOTAL),
            ("g", TOTAL),
            ("step", DEFINED),
            ("go", DEFINED),
            ("initKCell", TOTAL),
        ])
    );
    assert_eq!(
        named(&baseline, &withdrawal.unsupported),
        set(&[("lemma", SIMPLIFICATION), ("glemma", SIMPLIFICATION)])
    );
    assert!(
        withdrawal.withdrawn.iter().any(
            |claim| matches!(&claim.origin, SentenceOrigin::Baseline(at) if at.module != "CLAIMS")
        ),
        "prelude claims are withdrawn too"
    );
    assert_withdrawn_patch(&baseline, &withdrawal);
}

/// A function equation's result assertion depends on its own sentence and on equations
/// reached through every function it mentions. A rewrite rule's `ensures` is a result
/// condition, not a trusted claim.
#[test]
fn equation_ensures_follows_its_sentence_and_reachable_equations() {
    let baseline = support::load_path(
        &std::path::Path::new(support::DIR).join("equation-ensures-support.k"),
        "EQSUPPORT",
    );
    let rule = |label: &str| support::rule(&baseline, &format!("EQSUPPORT.{label}"));
    let replacement = |label: &str, path: &[u32], term: Term| {
        let at = TermRef::new(rule(label), path);
        Edit::ReplaceTerm {
            expected: baseline.term(&at).expect("existing term").clone(),
            at,
            replacement: term,
        }
    };
    let unsupported = |edit| {
        let withdrawal = withdraw_for(&baseline, vec![edit]);
        assert!(withdrawal.withdrawn.is_empty());
        assert_eq!(withdrawal.unsupported.len(), 1);
        let claim = &withdrawal.unsupported[0];
        assert_eq!(claim.origin, SentenceOrigin::Baseline(rule("f")));
        assert_eq!(claim.key, "ensures");
        assert!(!withdrawal.trusted());
    };
    unsupported(replacement("f", &[0, 1], int("2")));
    unsupported(replacement("d", &[0, 1], int("0")));

    assert_eq!(
        withdraw_for(&baseline, vec![replacement("g", &[0, 1], int("2"))]),
        Withdrawal::default()
    );
    assert_eq!(
        withdraw_for(&baseline, vec![replacement("step", &[2], bool_true())]),
        Withdrawal::default()
    );
}

fn withdraw_for(baseline: &Baseline, edits: Vec<Edit>) -> Withdrawal {
    ClaimSupport::new(baseline)
        .withdraw(baseline, &Patch::new(edits).expect("patch"))
        .expect("the patch applies")
}
