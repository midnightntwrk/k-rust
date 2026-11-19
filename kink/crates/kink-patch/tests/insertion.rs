//! Claim removal of an inserted constructor over a definition that imports the prelude (PJ-34,
//! U34f), over `testdata/k/insertion/insertion.k`: the claims of the symbols that take a value of
//! a grown sort, and of those that reach one, are withdrawn; the rest stay; and an insertion whose
//! effect is not known symbol by symbol is refused.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::definition::{AttributeKey, ProductionItem, Sentence};
use k_rust::kast::{Label, Sort};
use kink_patch::{
    Baseline, ClaimSupport, Edit, InsertPosition, Patch, SentenceOrigin, SentenceRef, Withdrawal,
    apply,
};
use serde_json::Value;
use std::collections::BTreeSet;
use std::path::Path;

const MAIN: &str = "INSERTION";
const SYNTAX: &str = "INSERTION-SYNTAX";

fn baseline() -> Baseline {
    support::load_path(&Path::new(support::DIR).join("insertion/insertion.k"), MAIN)
}

/// A fresh constructor `name` of `sort`, written `name` or `name(arguments)`.
fn constructor(name: &str, sort: &str, arguments: &[&str]) -> Sentence {
    let mut items = vec![ProductionItem::Terminal(name.to_owned())];
    if !arguments.is_empty() {
        items.push(ProductionItem::Terminal("(".to_owned()));
        for (index, argument) in arguments.iter().enumerate() {
            if index > 0 {
                items.push(ProductionItem::Terminal(",".to_owned()));
            }
            items.push(ProductionItem::NonTerminal {
                sort: Sort::new(*argument),
                name: None,
            });
        }
        items.push(ProductionItem::Terminal(")".to_owned()));
    }
    Sentence::Production {
        label: Some(Label::new(name)),
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items,
        attributes: k_rust::definition::Attributes::default(),
    }
}

fn insert(module: &str, sentence: Sentence) -> Patch {
    Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::ModuleEnd(module.to_owned()),
        ordinal: 0,
        sentence,
    }])
    .expect("patch")
}

/// A user claim's name: its production's symbol or its rule's label, without the module.
fn name(baseline: &Baseline, at: &SentenceRef) -> String {
    match baseline.sentence(at).expect("a baseline sentence") {
        Sentence::Production {
            label: Some(label), ..
        } => label.name.clone(),
        sentence => sentence
            .attributes()
            .string(AttributeKey::Label)
            .and_then(|label| {
                label
                    .strip_prefix("INSERTION.")
                    .or_else(|| label.strip_prefix("OPEN."))
            })
            .expect("a labelled rule")
            .to_owned(),
    }
}

/// The claims of the fixture's own modules, by (sentence name, key).
fn user(baseline: &Baseline, claims: &[kink_patch::Claim]) -> BTreeSet<(String, String)> {
    claims
        .iter()
        .filter_map(|claim| match &claim.origin {
            SentenceOrigin::Baseline(at)
                if at.module == MAIN || at.module == SYNTAX || at.module == "OPEN" =>
            {
                Some((name(baseline, at), claim.key.clone()))
            }
            _ => None,
        })
        .collect()
}

fn set(items: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    items
        .iter()
        .map(|(name, key)| ((*name).to_owned(), (*key).to_owned()))
        .collect()
}

fn withdraw(baseline: &Baseline, patch: &Patch) -> Withdrawal {
    ClaimSupport::new(baseline)
        .withdraw(baseline, patch)
        .expect("the patch applies")
}

/// Every claim of a user symbol that takes a value of a grown sort, or reaches one, is withdrawn,
/// and every other claim stays. Inserting `w(Val)` at Val grows Val, Top above it, Wrap and Prog
/// (whose constructors hold a Val), `KItem` and `K`, and the collections. `depth` (over Val),
/// `topSize` (over Top), `unwrap` (over Wrap) and `count` (over List) take a grown sort,
/// `viaDepth` reaches `depth`, `depth-lemma` mentions `depth`, and the `run` and `go` rules
/// quantify over Prog (and `run` mentions `depth`). `nat`, into Val, is a function whose value may
/// be a new one, and its own recursive equation names it, so its `total` goes too (conservative:
/// its equations decide every value). `twice` (over Int) keeps its `total`, `twice-lemma` stays,
/// and `note-lemma`, over Note, which does not grow, stays. No claim is unsupported: the prelude's hooked and `concrete` equations rest on the parametric
/// premise (kink `trust.md`), so the mutant is built with the withdrawn claims removed.
#[test]
fn an_inserted_constructor_withdraws_what_takes_its_sort() {
    let baseline = baseline();
    let patch = insert(SYNTAX, constructor("w", "Val", &["Val"]));
    let withdrawal = withdraw(&baseline, &patch);
    assert!(withdrawal.trusted(), "{:?}", withdrawal.unsupported);
    assert_eq!(
        user(&baseline, &withdrawal.withdrawn),
        set(&[
            ("depth", "total"),
            ("topSize", "total"),
            ("unwrap", "total"),
            ("count", "total"),
            ("viaDepth", "total"),
            ("nat", "total"),
            ("depth-lemma", "simplification"),
            ("run", "preserves-definedness"),
            ("go", "preserves-definedness"),
        ])
    );
    let support = ClaimSupport::new(&baseline);
    let affected = support
        .affected(&baseline, &patch)
        .unwrap()
        .expect("known symbol by symbol");
    for kept in ["twice", "s", "wrap", "w"] {
        assert!(!affected.contains(kept), "{kept} in {affected:?}");
    }
    for redefined in ["depth", "topSize", "unwrap", "count", "viaDepth", "nat"] {
        assert!(
            affected.contains(redefined),
            "{redefined} not in {affected:?}"
        );
    }
    // The withdrawn mutant applies and compiles.
    let mutant = apply(&baseline, withdrawal.patch().expect("a withdrawing patch"))
        .expect("the withdrawn patch applies");
    support::compile(&mutant.to_loaded(&baseline).expect("the mutant relinks"))
        .expect("the withdrawn mutant compiles");
}

/// A sentence that quantifies over a grown sort sees the new values whatever symbols it names:
/// `note-lemma` (`{_X:Note #Equals _Y:Note} => #Top`) names only the prelude's generic `#Equals`,
/// and was true while Note had no value; with a constructor of Note it says that Note has one
/// value at most, which a constructor with an argument falsifies. It is withdrawn, and the claims
/// over Val stay; `count` (over List, which holds K items) and the rules over Prog (K items too,
/// Prog being below `KItem`, but not grown: no constructor of Prog takes a Note) are as the growth
/// of `KItem` gives them.
#[test]
fn a_sentence_over_a_grown_sort_is_withdrawn_whatever_it_names() {
    let baseline = baseline();
    let withdrawal = withdraw(
        &baseline,
        &insert(SYNTAX, constructor("n", "Note", &["Int"])),
    );
    assert!(withdrawal.trusted(), "{:?}", withdrawal.unsupported);
    assert_eq!(
        user(&baseline, &withdrawal.withdrawn),
        set(&[("count", "total"), ("note-lemma", "simplification")])
    );
}

/// An insertion whose effect the growth does not know symbol by symbol counts every symbol as
/// redefined, so the prelude's hooked and `concrete` equations are unsupported and the mutant is
/// refused: a constructor of a prelude sort (Int), a constructor of Flag, whose values the
/// definition puts into the prelude's `IOError` (`syntax IOError ::= Flag`), a production that
/// redeclares a baseline symbol (`depth`), and one that is no constructor (a `function`).
#[test]
fn an_insertion_the_growth_does_not_read_is_refused() {
    let baseline = baseline();
    let mut function = constructor("fresh", "Val", &["Int"]);
    function
        .attributes_mut()
        .set(AttributeKey::Function, Value::String(String::new()));
    for (what, sentence) in [
        ("a constructor of Int", constructor("seven", "Int", &[])),
        ("a constructor of Flag", constructor("off", "Flag", &[])),
        ("a redeclared symbol", constructor("depth", "Val", &[])),
        ("a function", function),
    ] {
        let withdrawal = withdraw(&baseline, &insert(SYNTAX, sentence));
        assert!(!withdrawal.trusted(), "{what}");
        assert!(
            withdrawal
                .unsupported
                .iter()
                .any(|claim| claim.key == kink_patch::HOOKED_EQUATION_CLAIM),
            "{what}: {:?}",
            withdrawal.unsupported
        );
    }
}

/// An application of an equationally defined symbol into a grown sort may denote a new value: in
/// `open.k`, `p(Int)` into Val is `total` with no equation, so `p(0)` is a value of Val no
/// equation fixes, `a` or `b` in the baseline and possibly `c` in the mutant that inserts the
/// constructor `c`. `q`'s equation and the lemma `ab`, which name `p` but bind no variable of
/// Val, rest on `p(N)` being `a` or `b`: `q`'s `total` and `ab` are withdrawn. So is `t`'s, whose
/// condition names the sort predicate `isVal` that compilation generates. `p` keeps its own
/// `total` (its domain and its equations, none, are the baseline's), and `r` keeps its.
#[test]
fn a_sentence_over_an_open_value_is_withdrawn() {
    let baseline = support::load_path(&Path::new(support::DIR).join("insertion/open.k"), "OPEN");
    let withdrawal = withdraw(&baseline, &insert("OPEN", constructor("c", "Val", &[])));
    assert!(withdrawal.trusted(), "{:?}", withdrawal.unsupported);
    assert_eq!(
        user(&baseline, &withdrawal.withdrawn),
        set(&[("q", "total"), ("ab", "simplification"), ("t", "total"),])
    );
}

/// An inserted label must be new to every sentence, the prelude's included, not only to the
/// productions: `_==K_` names the prelude's `==K` and `isVal` a sort predicate, so neither is a
/// fresh constructor, and the insertion counts every symbol as redefined.
#[test]
fn an_inserted_label_must_be_new_to_every_sentence() {
    let baseline = baseline();
    for label in ["_==K_", "isVal", "depth"] {
        let withdrawal = withdraw(&baseline, &insert(SYNTAX, constructor(label, "Val", &[])));
        assert!(!withdrawal.trusted(), "{label}");
    }
}
