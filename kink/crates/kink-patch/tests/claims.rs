//! The support relation of trusted claims over `testdata/k/claims.k`.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::{Sort, Term};
use kink_patch::{
    Baseline, CONCRETENESS, ClaimRemoval, ClaimSupport, ENSURES_CLAIM, Edit, HOOKED_EQUATION_CLAIM,
    InsertPosition, LEMMA, Patch, RULE_CLAIMS, SYMBOL_CLAIMS, SentenceOrigin, SentenceRef,
    TRUSTED_CLAIMS, TermRef, Withdrawal, apply,
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
    support::compile(&mutant.to_loaded(baseline).expect("the mutant relinks"))
        .expect("the withdrawn mutant compiles");
    for claim in &withdrawal.withdrawn {
        let SentenceOrigin::Baseline(at) = &claim.origin else {
            panic!("a withdrawn claim of a baseline sentence");
        };
        let output = mutant
            .origins()
            .iter()
            .find(|(_, origin)| **origin == claim.origin)
            .map(|(output, _)| output);
        // A withdrawn lemma is deleted as a whole (re-pin R0c-fix-2).
        if claim.key == SIMPLIFICATION {
            assert!(output.is_none(), "{at:?} is a deleted lemma");
            continue;
        }
        let output = output.expect("the sentence survives");
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
///
/// Re-pin R0c-fix-2: the lemma about f is removed with the rest, by deleting it (a lemma is a
/// claim as a whole). Before: it was unsupported, and the mutant's symbolic tests did not run.
#[test]
fn a_changed_equation_withdraws_every_claim_resting_on_it() {
    let baseline = baseline();
    let edit = replace(&baseline, "d", &[0, 1], int("0"));
    let withdrawal = withdraw(&baseline, vec![edit.clone()]);
    assert_eq!(
        named(&baseline, &withdrawal.withdrawn),
        set(&[
            ("f", TOTAL),
            ("d", TOTAL),
            ("step", DEFINED),
            ("lemma", SIMPLIFICATION)
        ])
    );
    assert!(withdrawal.unsupported.is_empty());
    assert!(withdrawal.trusted());
    let patch = withdrawal.patch().expect("a withdrawing patch");
    assert!(patch.edits().contains(&edit));
    assert_eq!(patch.edits().len(), 5);
    assert!(patch.edits().contains(&Edit::DeleteSentence {
        at: rule(&baseline, "lemma"),
    }));
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
        set(&[("f", TOTAL), ("step", DEFINED), ("lemma", SIMPLIFICATION)])
    );
    assert!(withdrawal.unsupported.is_empty());
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
        set(&[("f", TOTAL), ("step", DEFINED), ("lemma", SIMPLIFICATION)])
    );
    assert!(withdrawal.unsupported.is_empty());
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
        set(&[
            ("f", TOTAL),
            ("d", TOTAL),
            ("step", DEFINED),
            ("lemma", SIMPLIFICATION)
        ])
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
/// production (which changes its sort's values), withdraws every claim. Load-stage change
/// (VI-03F, k-rust 378a97ca): initKCell totality is derived during compilation per side, so it
/// is not a trusted loaded-stage claim.
///
/// Re-pin R0c-fix-2: every lemma is now withdrawn by deletion, and every equation of a hooked
/// prelude symbol (its agreement with the hook) and every `concrete` prelude equation are
/// unsupported, since they rest on everything, so no claim-free mutant exists and the mutant is
/// refused. Before: the lemmas were unsupported.
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
            ("lemma", SIMPLIFICATION),
            ("glemma", SIMPLIFICATION),
        ])
    );
    assert!(named(&baseline, &withdrawal.unsupported).is_empty());
    assert!(!withdrawal.unsupported.is_empty());
    assert!(
        withdrawal
            .unsupported
            .iter()
            .all(|claim| ["hooked-equation", "concrete"].contains(&claim.key.as_str())),
        "{:?}",
        withdrawal.unsupported
    );
    assert!(!withdrawal.trusted());
    assert!(
        withdrawal.withdrawn.iter().any(
            |claim| matches!(&claim.origin, SentenceOrigin::Baseline(at) if at.module != "CLAIMS")
        ),
        "prelude claims are withdrawn too"
    );
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

/// Re-pin R0c-fix-2 deliverable 1: the claims k-rust 501f18b9 trusts, each with how kink removes
/// it from a mutant (`kink_patch::TRUSTED_CLAIMS` cites k-rust's docs and code for each). A change
/// of the set needs the k-rust contract read again.
#[test]
fn trusted_claims_are_pinned() {
    let pinned = TRUSTED_CLAIMS
        .iter()
        .map(|claim| (claim.claim, claim.removal))
        .collect::<Vec<_>>();
    assert_eq!(
        pinned,
        [
            ("total", ClaimRemoval::Attribute),
            ("functional", ClaimRemoval::Attribute),
            ("injective", ClaimRemoval::Attribute),
            ("smt-hook", ClaimRemoval::Attribute),
            ("smtlib", ClaimRemoval::Attribute),
            ("preserves-definedness", ClaimRemoval::Attribute),
            ("smt-lemma", ClaimRemoval::Attribute),
            ("simplification", ClaimRemoval::Sentence),
            ("ensures", ClaimRemoval::Refused),
            ("concrete-equation", ClaimRemoval::Refused),
            ("hooked-equation", ClaimRemoval::Refused),
        ]
    );
    assert!(
        TRUSTED_CLAIMS
            .iter()
            .all(|claim| !claim.citation.is_empty())
    );
    assert!(
        !TRUSTED_CLAIMS
            .iter()
            .any(|claim| claim.claim == "constructor")
    );

    // Re-pin R0c-fix-3 (R0c-fix-2 review minor 1): the rows are the constants the removal
    // algorithm reads, so dropping a key from one of them, or adding a row without it, fails.
    let rows = |removal: ClaimRemoval| {
        TRUSTED_CLAIMS
            .iter()
            .filter(|claim| claim.removal == removal)
            .map(|claim| claim.claim)
            .collect::<Vec<_>>()
    };
    let attributes = SYMBOL_CLAIMS
        .iter()
        .chain(&RULE_CLAIMS)
        .map(|key| key.as_str())
        .collect::<Vec<_>>();
    assert_eq!(rows(ClaimRemoval::Attribute), attributes);
    assert_eq!(rows(ClaimRemoval::Sentence), [LEMMA.as_str()]);
    assert_eq!(
        rows(ClaimRemoval::Refused),
        [ENSURES_CLAIM, "concrete-equation", HOOKED_EQUATION_CLAIM]
    );
    assert_eq!(
        CONCRETENESS.map(|key| key.as_str()),
        ["concrete", "symbolic"]
    );

    // The k-rust passages the rows cite (and the "not claims" of the TRUSTED_CLAIMS docs), by
    // digest at the pin: a re-pin that changes one needs the contract read again.
    let k_rust = k_rust_tree();
    for (file, first, last, digest) in TRUSTED_CLAIM_PASSAGES {
        let text = std::fs::read_to_string(k_rust.join(file)).expect("a k-rust file");
        let lines = text.split('\n').collect::<Vec<_>>();
        let passage = lines[first - 1..last].join("\n");
        assert_eq!(
            kink_patch::sha256(passage.as_bytes()).to_string(),
            digest,
            "{file} {first}-{last} changed: read the k-rust contract again"
        );
    }
}

/// Each passage `TRUSTED_CLAIMS` cites (file relative to the k-rust tree, first and last line,
/// sha256 of the lines joined by newlines) at k-rust 501f18b9.
///
/// Re-pin probe P-1 (k-rust 58720d2e5): sixteen passages are byte-identical and only moved (the
/// docs grew by k-rust's KINK-17..KINK-22 and MLP sections), so only their lines are re-pinned.
/// The `total` passage (501f18b9 lines 1376-1384, now 1477-1487) changed (KINK-18/2, head
/// 16e88a6d4, merge 7d4c588f9; KINK-18/3, head a009ea6fc, merge 4561f7820; k-rust's draft
/// answers-add3 section 2.1 "Contradicted claims" and "Contradicted `preserves-definedness`"):
/// krun's warning names the observing rule and says when a record is not ground, and a
/// contradiction is also found where an equation's result is `\bottom` with no undefined builtin
/// (a `#Bottom` right-hand side, a refuted `ensures`). The attribute is still the author's
/// claim, trusted and named when evaluation observes it contradicted, which is what the `total`
/// row cites; the new route only reports more contradictions, which kink reads as no evidence.
/// `TRUSTED_CLAIMS`' citation strings gave the 501f18b9 lines until re-pin L-1, which moved them
/// to the 8f8ad57c5 lines below.
///
/// Re-pin P-2 (k-rust 8f8ad57c5): all seventeen passages are byte-identical to 58720d2e5's, and
/// twelve only moved. compatibility.md grew by rounds 26-28 (the BIND/A5 "Frontend policy"
/// binder paragraphs, A6, A3, MLP/4b and MLP/9 text; k-rust ORCHESTRATION.md 10.4), so its ten
/// passages moved down 17 to 31 lines; module_to_kore.rs moved its two passages down 3 lines
/// (MLP/4b, MLP/9). backend-port.md and k-rust-backend smt.rs did not change. Only the line
/// numbers are re-pinned.
///
/// Re-pin P-1 (`draft/tasks/repin-0068938b`, k-rust 0068938b1): sixteen passages are
/// byte-identical to 8f8ad57c5's and only moved. compatibility.md grew by round D's text and the
/// correctness sweep's (UNDEF/1-2, MLP/10, FU-27; k-rust draft/k-in-k/answers-2026-10b.md), so
/// its passages moved down 8 to 124 lines; smt.rs's second passage moved down 90 lines (the
/// sweep's 7a9558e96, cbbc530ac and 0bfac13fa, and 4a34be746), and module_to_kore.rs's two up 27
/// (the sweep's 27e0f03ae and 7355b8699, FU-27's 2f841146a, ks3's d0a7c8daf); backend-port.md
/// and smt.rs 207 did not move. The `total` passage changed in one sentence (8f8ad57c5 line
/// 1517, now 1638): a successor whose equation's own result is `#Bottom` or whose `ensures` is
/// refuted was "a vacuous state rather than an undefined result", and is now a successor that
/// "denotes no state, as an undefined result does, so the step is undefined there alike", whose
/// halt still has no `contradictedTotal`, so only the record names the contradiction. Cause:
/// UNDEF/1 (k-rust e3d260c4c, merge dec70ffd1; worker report
/// draft/kink-handoff-2026-10-15/workers/UNDEF-1-report.md; result changes RC-73 to RC-76 of
/// draft/k-in-k/answers-2026-10b.toml), reading R of FU-42: a `\bottom` successor is no
/// successor on every route. The `total` attribute is still the author's claim, trusted and
/// named by a record when evaluation observes it contradicted, which is all the `total` row
/// cites; such a run carries the record on its `contradictedClaims` list, which excludes it
/// since re-pin adoption A-1, whatever leaf it ends on, so the change moves no verdict.
///
/// Re-pin FZ-15 (fz26/solve): the `smt-lemma` passage of compatibility.md is byte-identical and
/// moved down 2 lines, by the "Clock-free solver mode" paragraph of "Determinism and
/// concurrency", which precedes it. Only its lines are re-pinned.
///
/// Re-pin of smt.rs's second passage (`smt_lemmas`): byte-identical, moved down 78 lines by the
/// translation of `bitRangeInt`, `>>Int` and low-bit masks of `&Int` by literal amounts, which
/// precedes it in the file. Only its lines are re-pinned.
///
/// Re-pin FZ-DATAEND (fz26/dataend): compatibility.md's passages after "Anywhere rules"' value
/// claims are byte-identical and moved down 6 lines, by the data-term paragraph
/// (`k_rust_backend::data_term`) inserted before "When a definition is loaded the backend checks
/// its critical pairs once". Only their lines, and `TRUSTED_CLAIMS`' citations of them, are
/// re-pinned.
///
/// Re-pin FZ-CONFLUENCE (fz26/confluence): compatibility.md 1142 no longer lists "a hooked
/// symbol's equations agree with its hook" among the unchecked premises; the check now pairs
/// each such equation with the builtin's written meaning, which names only builtins the
/// evaluator applies (1144, pinned here, which `hooked-equation` cites, and the three lines after
/// it, which also state that domains.md's `replaceAll` equation is reported). Those five
/// inserted lines move every later passage down 5, byte-identical: only their lines, and
/// `TRUSTED_CLAIMS`' citations of them, are re-pinned.
///
/// Re-pin fz26 phase-6 integration (INT8): FZ-EMPTYSORT's sentence that no overlap is set aside
/// for a sort with no normal form ("Anywhere rules", after "Each overlap is then refuted") adds
/// one line above every compatibility.md passage after 1100, which moves those ten passages down
/// 1, byte-identical (found by their text in the merged file): only their lines, and
/// `TRUSTED_CLAIMS`' citations of them, are re-pinned.
///
/// Re-pin fz26 INT9-FIX-DOCS (review CHKB-2): compatibility.md 1143, the list of premises the
/// contract states and does not check, now also names A1+ (the executable and adopted witness
/// equations terminate innermost over the signature with the added constants). The clauses the
/// `total`, `concrete`/`symbolic` and lemma rows cite (a `total` symbol is defined on defined
/// arguments, an author axiom; lemmas and `concrete` or `symbolic` equations are theorems of the
/// executable equations) are byte-identical and still unchecked; no line moved. Only 1143's
/// digest is re-pinned.
///
/// Re-pin FZ-STATESET-MATCH (fz26/stateset-match): the "Committed transitions" subsection of
/// "Run coverage" and the "State matches" section after "Work budget" add 42 lines between 2279
/// and 2833, which move the definedness-faithful passage down 42 to 2875-2876, byte-identical:
/// only its lines, and `TRUSTED_CLAIMS`' citations of them, are re-pinned.
///
/// Re-pin fz26 FZ-FRESH: the fresh-constants section (8 lines) and the implementation-chosen
/// section (4 lines) grow above the eleven compatibility.md passages, which move down 8 to 12
/// lines with the lines they name; no pinned line changes and no digest is touched, and
/// `TRUSTED_CLAIMS`' citations move alike. At the branch base `16014aab4` the ranges already did
/// not hold their pinned text, the test being red there (moved by later k-rust documentation),
/// so this moves no verdict.
///
/// Re-pin fz26 KINK-REPINS (before the kink hand-over, main `602746a9d`): the fourteen
/// compatibility.md, smt.rs and module_to_kore.rs passages that moved byte-identical are
/// re-pinned at the lines their digests now hold, and `TRUSTED_CLAIMS`' citations name the
/// passages the pins locate (several had drifted from their pins before: `total`'s 1649-1659 and
/// `functional`'s 1651 named the contradicted-`total` passage, the docs' 2291 and 1183-1186 the
/// refused-claim and derived-`functional` passages). compatibility.md 2954-2956 is not re-pinned:
/// 6058eb6bb rewrote its abstraction sentence ("pure total contexts" became "pure functional
/// contexts ... with separate source-aware partial domains"), which the WORD-03 review below rests
/// on, so the contract must be read again by that change's owner; the test stays red there.
///
/// Re-pin kink27 R1-TRUST (main `d3e259fe1`): the definedness-faithful passage is read again and
/// re-pinned at 2974-2976 (moved down 20 lines by later documentation). Its first two lines are
/// byte-identical: the SMT reading trusts exactly that each `smt-hook` is exact where its symbol
/// is defined, each `smt-lemma` axiom and the user's SMT prelude, which the `smt-hook` and
/// `smt-lemma` rows and the prelude premise cover. Only the third line changed: congruence UFs
/// now also cover pure partial functions, each with a value UF and a separate Boolean domain UF
/// (the paragraph 6058eb6bb rewrote, 2947-2957). What kink concludes from the passage is that the
/// abstraction trusts no author assertion beyond those rows, and that still holds from the
/// semantics. Take a K valuation `v` that satisfies the predicate. A pure function's application
/// (no effect, binder, macro or alias) denotes at most one element and depends on its arguments
/// only, so reading its value UF as the K value where the application is defined (any value
/// elsewhere) and its domain UF as the application's definedness interprets both as functions of
/// the arguments: forward congruence on defined arguments and domain congruence hold, and the
/// interpretation extends `v`. The domain UF stands for the application's `\ceil`, read as the
/// definedness walk reads it (`apply_ceil_equation`'s condition and the arguments' strict
/// domains, k-rust-backend `smt/functional.rs` `domain_plan`), so it states what the definition
/// already states: a ceil equation, compiler-derived from the mutant's own sorts (a sort
/// projection's exact image, as freeness is) or an author's ceil lemma, which the
/// `simplification` row withdraws when its support is touched; a sort projection's `\bottom` on
/// an input off its image, from that compiler-derived image equation and the matcher's
/// constructor clash; a hook's builtin domain (a map lookup's key membership, a list access's
/// length bound), a hooked symbol's own equations being refused (`hooked-equation`); a field of a
/// sole-constructor sort, from the compiler's no-junk axiom and the field's one equation, a
/// function rule or a lemma the `simplification` row withdraws; and nothing owed for an
/// irreducible application of a `value-production` symbol (`value_production_ceil_equations`),
/// a marker the compiler derives for a production that is not a function (an `anywhere` or
/// macro-like head). Each is compiler-derived, a builtin's own domain or a withdrawn lemma, none an author
/// assertion outside the rows. Whether a head is partial is the `total` and `functional`
/// rows' attribute, withdrawn alike, and withdrawing one only adds a domain UF to the head, which
/// weakens the query. So every author assertion the new reading consumes is already a row. A
/// satisfying interpretation is still no K model ("Automatic congruence is an approximation",
/// 2959), and kink reads no solver model as evidence. Whether 6058eb6bb's code meets this
/// passage (a domain condition stronger than the definition's, an unknown decided wrongly) is
/// k-rust's soundness, not a claim a mutant can lose: kink27 R1-SOUND judges it for 6058eb6bb,
/// kink27 R2-DOMAIN-ROUTES for the four observation routes read as domain conditions, and a
/// restriction of the commit that rewrites this passage again needs it read again.
// WORD-03 also reviews the SMT-03 congruence paragraph: a K valuation extends to the
// query-local UF interpretation of a pure functional context (re-read at R1-TRUST above: value
// and domain UFs). No constructor injectivity, map law or model exactness follows. The trusted
// hook/lemma/prelude sentence is unchanged. Pin that reviewed three-line passage.
// The total and coverage passages are byte-identical and moved by the added scalar/map docs.
// WORD-03: both SMT passages remain byte-identical after domains/literal/helper/word
// emission changes; their SHA-256 pins are unchanged. Source-derived functions are readings
// of admitted source equations, not new user smt-lemma assumptions. Re-pin only their lines.
const TRUSTED_CLAIM_PASSAGES: [(&str, usize, usize, &str); 18] = [
    (
        "docs/compatibility.md",
        1078,
        1078,
        "bcee9ac9986b1b5c90868e046c36afc8da3dc45638790a4926d7ef624b18e8b7",
    ),
    (
        "docs/compatibility.md",
        1156,
        1156,
        "9fa7fb1ee4fde986bdc71fd04e907f47fe0d37e800774563526ce8a8bfaaeef3",
    ),
    (
        "docs/compatibility.md",
        1158,
        1158,
        "6ac61e27f16d7f63164621e446aa193f3d769bd4ce09ba332bf23b95c7c6fd13",
    ),
    (
        "docs/compatibility.md",
        1188,
        1193,
        "0f233fef017749e7d8e86379281d8286817adc73b4cf10fc9330213551261915",
    ),
    (
        "docs/compatibility.md",
        1206,
        1206,
        "674db170e02676b6eeeb961e20bf1ab36874f7b9e9c9615bdd12b603a17277e1",
    ),
    (
        "docs/compatibility.md",
        1412,
        1412,
        "fd173e7f850dec9744c13cfce3954d1e2f5521b7259f29f78e60235cc70f325d",
    ),
    (
        "docs/compatibility.md",
        1566,
        1566,
        "ceadc9f94bdf864bcf369b5fc107b27a3bf10026e71c05c5a54d547610075107",
    ),
    (
        "docs/compatibility.md",
        1591,
        1591,
        "cb62c2f07d19806a29e137c7821fdc2113eabdb6404dfd53215e3d51fb0b9bcb",
    ),
    (
        "docs/compatibility.md",
        1671,
        1681,
        "1c61218ca52c52d4e182fd7c3b475ebd3129ff57d44c41bb280f022eff21fb32",
    ),
    (
        "docs/compatibility.md",
        2313,
        2313,
        "1af53c1bf1af7a9f17e6a3fec30797cc00225b31ea36dbd3e7b68304ffa3481a",
    ),
    (
        "docs/compatibility.md",
        2974,
        2976,
        "06f1bdd33226940c3a77f600bf937ac94fe8601e4099065edee67ce69d9a612a",
    ),
    (
        "docs/backend-port.md",
        316,
        316,
        "3cb01101c1550a2cde4fb062444584d6a81cddbb1191285a8e4a30d2f9404a83",
    ),
    (
        "docs/backend-port.md",
        323,
        323,
        "6b6bfb6c4e2d37a4467c7b236e637cfe25cb60ba07e253a7eede5a48398e5178",
    ),
    (
        "docs/backend-port.md",
        342,
        342,
        "7cbfd603d6854b8c5f39175bfa1cf41c1a6a0a8d9712ea5e8811693e724b1e30",
    ),
    (
        "crates/k-rust-backend/src/smt.rs",
        230,
        230,
        "1caeb7f3044a3c36838e03391db8bd8d4a3d57a57c386b6479dd73af441d909c",
    ),
    (
        "crates/k-rust-backend/src/smt.rs",
        1852,
        1863,
        "a93c2de2f4221dc5c729b3e23a7426ee612300dfbddc13ff04275418b7291974",
    ),
    (
        "crates/k-rust/src/kompile/module_to_kore.rs",
        1520,
        1531,
        "57fb9f4beb1240e4987bfa6175dbfcc3b4ce218b3b8cd24147c85628b3ec740d",
    ),
    (
        "crates/k-rust/src/kompile/module_to_kore.rs",
        1547,
        1553,
        "f8374d89dd45e5237e10cba035a7513c592452cb734a31bac411d7fe4a1dda08",
    ),
];

/// The k-rust tree the workspace builds against: the parent of the `k-rust-backend` path
/// dependency's `crates/` directory, read from k-rust's root manifest (kink is a part of k-rust's
/// workspace since merge packet M-1).
fn k_rust_tree() -> std::path::PathBuf {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let manifest =
        std::fs::read_to_string(root.join("Cargo.toml")).expect("the workspace manifest");
    let line = manifest
        .lines()
        .find(|line| line.trim_start().starts_with("k-rust-backend"))
        .expect("a k-rust-backend dependency");
    let path = line
        .split("path = \"")
        .nth(1)
        .and_then(|rest| rest.split('"').next())
        .expect("k-rust-backend is a path dependency");
    root.join(path).join("../..")
}

fn reach() -> Baseline {
    support::load_path(
        &std::path::Path::new(support::DIR).join("r0c/claimreach.k"),
        "CLAIMREACH",
    )
}

/// The user-written claims of `testdata/k/r0c/claimreach.k`, by (sentence name, key).
fn reach_named(baseline: &Baseline, claims: &[kink_patch::Claim]) -> BTreeSet<(String, String)> {
    claims
        .iter()
        .filter_map(|claim| match &claim.origin {
            SentenceOrigin::Baseline(at) if at.module.starts_with("CLAIMREACH") => {
                let name = match baseline.sentence(at).expect("a baseline sentence") {
                    Sentence::Production {
                        label: Some(label), ..
                    } => label.name.clone(),
                    sentence => sentence
                        .attributes()
                        .string(AttributeKey::Label)
                        .and_then(|label| label.strip_prefix("CLAIMREACH."))
                        .expect("a labelled rule")
                        .to_owned(),
                };
                Some((name, claim.key.clone()))
            }
            _ => None,
        })
        .collect()
}

fn reach_literal(baseline: &Baseline, label: &str, path: &[u32], to: &str) -> Edit {
    let at = TermRef::new(
        support::rule(baseline, &format!("CLAIMREACH.{label}")),
        path,
    );
    Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("baseline term").clone(),
        at,
        replacement: int(to),
    }
}

/// Re-pin R0c-fix-2 deliverables 1 and 5: the reach of an edit is the reverse call-graph closure
/// over equations (left side, right side and condition). An edit of f's equation (`I +Int 1` to
/// `I +Int 0`, which makes f partial at 0) removes f's `total` and `smtlib`, the `total` of g
/// (whose equation applies f) and of h (whose condition applies g: transitive), the lemma about f
/// (deleted), and the `preserves-definedness` of `use`, whose condition applies g. k, its lemma
/// and `other` rest on nothing the edit touches and keep their claims. The claim-free mutant
/// compiles.
#[test]
fn an_edit_removes_the_claims_of_every_symbol_that_reaches_it() {
    let baseline = reach();
    let withdrawal = ClaimSupport::new(&baseline)
        .withdraw(
            &baseline,
            &Patch::new(vec![reach_literal(&baseline, "f", &[0, 1, 1, 1], "0")]).expect("patch"),
        )
        .expect("the patch applies");
    assert_eq!(
        reach_named(&baseline, &withdrawal.withdrawn),
        set(&[
            ("f", TOTAL),
            ("f", "smtlib"),
            ("g", TOTAL),
            ("h", TOTAL),
            ("flemma", SIMPLIFICATION),
            ("use", DEFINED),
        ])
    );
    assert!(withdrawal.unsupported.is_empty());
    assert_withdrawn_patch(&baseline, &withdrawal);
}

/// Re-pin R0c-fix-2 deliverable 5: an edit of a rewrite rule only redefines no symbol, so it
/// removes that rule's own claim and nothing from any function; one of a rule that carries no
/// claim removes nothing.
#[test]
fn a_rewrite_rule_edit_removes_nothing_from_functions() {
    let baseline = reach();
    let support = ClaimSupport::new(&baseline);
    let withdraw = |edit| {
        support
            .withdraw(&baseline, &Patch::new(vec![edit]).expect("patch"))
            .expect("the patch applies")
    };
    let withdrawal = withdraw(reach_literal(&baseline, "use", &[1, 1], "1"));
    assert_eq!(
        reach_named(&baseline, &withdrawal.withdrawn),
        set(&[("use", DEFINED)])
    );
    assert!(withdrawal.unsupported.is_empty());
    assert_withdrawn_patch(&baseline, &withdrawal);
    // k's equation: k, its lemma and `other` (whose condition applies k), nothing of f, g or h.
    let withdrawal = withdraw(reach_literal(&baseline, "k", &[0, 1, 1], "3"));
    assert_eq!(
        reach_named(&baseline, &withdrawal.withdrawn),
        set(&[("k", TOTAL), ("klemma", SIMPLIFICATION), ("other", DEFINED)])
    );
}

/// Re-pin R0c-fix-2: a lemma the patch edits is the patch's own claim. Deleting it would undo the
/// mutant, so it is unsupported and the mutant is refused.
#[test]
fn an_edited_lemma_is_unsupported() {
    let baseline = reach();
    let withdrawal = ClaimSupport::new(&baseline)
        .withdraw(
            &baseline,
            &Patch::new(vec![reach_literal(&baseline, "klemma", &[0, 0, 1], "1")]).expect("patch"),
        )
        .expect("the patch applies");
    assert_eq!(
        reach_named(&baseline, &withdrawal.unsupported),
        set(&[("klemma", SIMPLIFICATION)])
    );
    assert!(!withdrawal.trusted());
}

/// Re-pin R0c-fix-3 deliverable 3 (R0c-fix-2 review major 2, `testdata/k/r0c/ovl.k`): kompile
/// generates the overload axiom `fnum(inj(X)) = inj(fint(X))`, an equation of the greater `fnum`
/// that no source sentence carries and that mentions the lesser `fint`. An edit of `fint` reaches
/// `fnum` through it, so `fnum`'s `total` is removed with `fint`'s, and both are symbols the
/// mutant consistency check reads (`ClaimSupport::affected`). At R0c-fix-2 only `fint`'s was
/// removed.
#[test]
fn an_edit_of_a_lesser_overload_reaches_the_greater() {
    let baseline = support::load_path(&std::path::Path::new(support::DIR).join("r0c/ovl.k"), "OVL");
    // `f(I:Int) => 10 /Int (I +Int 1)`: the right side's second argument's second argument.
    let at = TermRef::new(support::rule(&baseline, "OVL.fint"), [0, 1, 1, 1]);
    let expected = baseline.term(&at).expect("the literal 1").clone();
    assert_eq!(expected, int("1"));
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        at,
        expected,
        replacement: int("0"),
    }])
    .unwrap();
    let support = ClaimSupport::new(&baseline);
    let withdrawal = support.withdraw(&baseline, &patch).unwrap();
    let mut removed = withdrawal
        .withdrawn
        .iter()
        .filter_map(|claim| match &claim.origin {
            SentenceOrigin::Baseline(at) => match baseline.sentence(at) {
                Some(Sentence::Production {
                    label: Some(label), ..
                }) => Some((label.name.clone(), claim.key.clone())),
                _ => None,
            },
            SentenceOrigin::Inserted { .. } => None,
        })
        .collect::<Vec<_>>();
    removed.sort();
    assert_eq!(
        removed,
        [
            ("fint".to_owned(), "total".to_owned()),
            ("fnum".to_owned(), "total".to_owned())
        ]
    );
    assert_eq!(
        support.affected(&baseline, &patch).unwrap(),
        Some(BTreeSet::from(["fint".to_owned(), "fnum".to_owned()]))
    );
}

/// Re-pin R0c-fix-4 (R0c-fix-3 review critical 2, `r0c/cfgf.k`): a function rule written with
/// configuration context, `rule [fpos]: [[ f(I) => 1 ]] <k> _ </k> requires I >=Int 0`, is read
/// as an equation of `f` (k-rust loads it as `#withConfig(F, C)` and compiles it to an equation of
/// `F`'s head, `rule_catalog::match_rule_label`). An edit of its guard redefines `f`, so `f`'s
/// `total` is removed and `f` is a head the consistency check reads; `go`, whose rule applies
/// `f`, is a rewrite rule and is not affected. At 25e229e the rule read as a rewrite rule and
/// nothing was redefined or removed.
#[test]
fn a_rule_with_configuration_context_is_an_equation_of_its_head() {
    let baseline = support::load_path(
        &std::path::Path::new(support::DIR).join("r0c/cfgf.k"),
        "CFGF",
    );
    // `requires I >=Int 0`: the condition's second argument.
    let at = TermRef::new(support::rule(&baseline, "CFGF.fpos"), [1, 1]);
    let expected = baseline.term(&at).expect("the guard literal").clone();
    assert_eq!(expected, int("0"));
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        at,
        expected,
        replacement: int("5"),
    }])
    .unwrap();
    let support = ClaimSupport::new(&baseline);
    let effect = support.effect(&baseline, &patch).unwrap();
    assert_eq!(effect.redefined, Some(BTreeSet::from(["f".to_owned()])));
    assert_eq!(effect.affected, Some(BTreeSet::from(["f".to_owned()])));
    assert_eq!(
        effect.touched,
        BTreeSet::from([support::rule(&baseline, "CFGF.fpos")])
    );
    let withdrawal = support.withdraw(&baseline, &patch).unwrap();
    let removed = withdrawal
        .withdrawn
        .iter()
        .map(|claim| claim.key.clone())
        .collect::<Vec<_>>();
    assert_eq!(removed, [TOTAL.to_owned()]);
    assert!(withdrawal.trusted());
}
