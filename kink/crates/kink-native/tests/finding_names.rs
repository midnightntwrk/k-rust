//! KINK-FINDING-NAMES: a `[spec] assume_joined` premise names a finding of the full critical-pair
//! check by its kind, its sentences and a digest of the compiled sentences (k-rust-backend
//! `data_term::names`), so it survives every edit of the K that leaves those sentences alone and
//! is refused, never silently re-matched, once they change.
//!
//! The definition is r4-empty's (`f(_) => a` beside `f(_) => bb` over a sort with no element, an
//! undecided root pair), its rules labelled as KRS labels every sentence; each test compiles an
//! edit of its text as kink loads a specification.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Arc;

use k_rust::builtin;
use k_rust::kompile::CompileOptions;
use k_rust::outer::ResolvedSource;
use k_rust_backend::definition::BackendDefinition;
use kink_native::NativeValidator;
use kink_native::consistency::loaded_definition;
use kink_native::data::{DataEnds, DataFacts, FindingVerdict, SentenceNames, data_ends};
use kink_patch::Baseline;

const R4: &str = "module R4
  imports INT
  imports BOOL
  syntax A  ::= \"a\"
  syntax B  ::= \"bb\"
  syntax AB ::= A | B
  syntax S
  syntax AB ::= f(S) [function, total]
  rule [fa]: f(_) => a
  rule [fb]: f(_) => bb
  syntax Pgm ::= go(Int)
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => a </s>
endmodule
";

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// `text`, a specification `spec.k`, loaded as kink runs it.
fn definition(text: &str) -> Arc<BackendDefinition> {
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
    };
    let baseline = Baseline::load(
        ResolvedSource::new("spec.k", text.to_owned()),
        "R4",
        None,
        &mut resolver,
        &support::options(),
    )
    .unwrap();
    let compiled = NativeValidator::bind(baseline, CompileOptions::default())
        .compile_baseline()
        .unwrap();
    loaded_definition(&compiled).unwrap()
}

fn facts(text: &str, names: &[String]) -> DataFacts {
    DataFacts::of(&definition(text), names)
}

/// The one finding's name of `text`.
fn name(text: &str) -> String {
    let facts = facts(text, &[]);
    let [finding] = facts.unnamed().try_into().unwrap();
    assert_eq!(finding.verdict, FindingVerdict::Undecided);
    finding.name.expect("named")
}

/// The one refusal of `premise` on `text`: its code and detail.
fn refused(text: &str, premise: &str) -> (String, String) {
    let facts = facts(text, &[premise.to_owned()]);
    let [refusal] = facts.refused_names().try_into().unwrap();
    assert_eq!(data_ends(&facts), DataEnds::None);
    (refusal.reason, refusal.detail)
}

fn assumed(text: &str, premise: &str) {
    let facts = facts(text, &[premise.to_owned()]);
    assert!(
        facts.refused_names().is_empty(),
        "{:?}",
        facts.refused_names()
    );
    assert!(matches!(data_ends(&facts), DataEnds::Admitted(_)));
}

/// Tests 1, 2, 11 and 12: lines inserted above both sentences, a reformatting, and a renaming of
/// their variables leave the name, so the premise still applies; the facts of such an edit (a
/// mutant whose patch only moves lines) do not differ from the baseline's, so the comparison
/// gives no `mutant-findings`, and the identity the execution digest records is the same.
#[test]
fn an_edit_that_leaves_the_sentences_alone_leaves_the_name() {
    on_a_big_stack(|| {
        let premise = name(R4);
        eprintln!("K: {premise}");
        assert!(premise.starts_with("root:R4.fa,R4.fb#"), "{premise}");
        let shifted = R4.replace(
            "  rule [fa]:",
            "  // a comment\n\n  syntax Unused ::= \"unused\"\n\n  rule [fa]:",
        );
        let reformatted = R4.replace(
            "rule [fb]: f(_) => bb",
            "rule [fb]:\n      f ( _X:S )\n        =>\n      bb",
        );
        for edited in [&shifted, &reformatted] {
            assert_eq!(&name(edited), &premise);
            assumed(edited, &premise);
        }
        let baseline = facts(R4, std::slice::from_ref(&premise));
        let moved = facts(&shifted, std::slice::from_ref(&premise));
        assert!(!moved.differs(&baseline));
        assert!(!moved.differs_outside(&baseline, Some(&BTreeSet::new())));
        assert_eq!(
            moved
                .findings()
                .into_iter()
                .map(|finding| finding.identity)
                .collect::<Vec<_>>(),
            baseline
                .findings()
                .into_iter()
                .map(|finding| finding.identity)
                .collect::<Vec<_>>()
        );
        // The sentences' positions are shown, as information only.
        let [finding] = baseline.findings().try_into().unwrap();
        assert_eq!(finding.sentences.len(), 2);
        assert!(
            finding.sentences.iter().all(|sentence| sentence
                .at
                .as_deref()
                .is_some_and(|at| at.contains("spec.k:"))),
            "{finding:?}"
        );
        let [moved_finding] = moved.findings().try_into().unwrap();
        assert_ne!(finding.sentences, moved_finding.sentences);
    });
}

/// Tests 3, 4, 5 and 11: an edit of a premised sentence refuses the premise (`changed`, with the
/// new name), a label swapped between the two equations is no re-match, and a branch inserted
/// before a positionally named one (KRS names a function's branches `f_1`, `f_2`, ...) refuses
/// the old premise rather than assuming the pair now at its names; the mutant's facts then
/// differ from the baseline's.
#[test]
fn an_edit_of_a_premised_sentence_refuses_the_premise() {
    on_a_big_stack(|| {
        let premise = name(R4);
        let rhs = R4
            .replace(
                "rule [fb]: f(_) => bb",
                "rule [fb]: f(_) => bb [priority(40)]",
            )
            .replace(
                "rule [fa]: f(_) => a",
                "rule [fa]: f(_) => a [priority(40)]",
            );
        let total = R4.replace("[function, total]", "[function]");
        for edited in [&rhs, &total] {
            let now = name(edited);
            assert_ne!(now, premise);
            let (reason, detail) = refused(edited, &premise);
            assert_eq!(reason, "changed", "{detail}");
            assert!(detail.contains(&now), "{detail}");
            assert!(facts(edited, &[]).differs(&facts(R4, &[])));
        }
        let swapped = R4
            .replace("rule [fa]: f(_) => a", "rule [fb]: f(_) => a")
            .replace("rule [fb]: f(_) => bb", "rule [fa]: f(_) => bb");
        assert_eq!(refused(&swapped, &premise).0, "changed");
        let branches = |rules: &[&str]| {
            let written = rules
                .iter()
                .enumerate()
                .map(|(i, rhs)| format!("  rule f(_) => {rhs} [label(r4--f_{})]\n", i + 1))
                .collect::<String>();
            R4.replace(
                "  rule [fa]: f(_) => a\n  rule [fb]: f(_) => bb\n",
                &written,
            )
            .replace(
                "syntax AB ::= A | B",
                "syntax C ::= \"c\"\n  syntax AB ::= A | B | C",
            )
        };
        let before = branches(&["a", "bb"]);
        let old = name(&before);
        let after = branches(&["c", "a", "bb"]);
        let after_facts = facts(&after, std::slice::from_ref(&old));
        let [refusal] = after_facts.refused_names().try_into().unwrap();
        assert!(
            ["changed", "no-finding"].contains(&refusal.reason.as_str()),
            "{refusal:?}"
        );
        assert!(after_facts.heads().assumed().is_empty());
    });
}

/// Test 6 (K level): a former position name is refused with the names at that position now, a
/// name without its digest with the full names it reads as, and a text of neither grammar as
/// `malformed`.
#[test]
fn former_and_partial_names_are_refused_with_what_to_write() {
    on_a_big_stack(|| {
        let premise = name(R4);
        let (reason, detail) = refused(R4, "spec.k:9:3,spec.k:10:3@root");
        assert_eq!(reason, "position-name", "{detail}");
        assert!(detail.contains(&premise), "{detail}");
        let readable = premise.rsplit_once('#').unwrap().0;
        let (reason, detail) = refused(R4, readable);
        assert_eq!(reason, "no-digest", "{detail}");
        assert!(detail.contains(&premise), "{detail}");
        assert_eq!(refused(R4, "R4.fa").0, "malformed");
    });
}

/// Test 9 (the spelling): a front end that spells sentences by the item that wrote them prints
/// names in its spelling, reads a premise in it once mapped to the K spelling, and refuses in
/// it.
#[test]
fn a_front_ends_spelling_is_read_and_printed() {
    on_a_big_stack(|| {
        let spelling = SentenceNames::new([
            ("R4.fa".to_owned(), "crate::fa".to_owned()),
            ("R4.fb".to_owned(), "crate::fb".to_owned()),
        ]);
        let definition = definition(R4);
        let strict = DataFacts::spelled(&definition, &[], spelling.clone());
        let [finding] = strict.unnamed().try_into().unwrap();
        let premise = finding.name.clone().expect("named");
        eprintln!("KRS: {premise}");
        assert!(
            premise.starts_with("root:crate::fa,crate::fb#"),
            "{premise}"
        );
        assert_eq!(
            finding
                .sentences
                .iter()
                .map(|sentence| sentence.part.as_str())
                .collect::<Vec<_>>(),
            ["crate::fa", "crate::fb"]
        );
        let k = spelling.to_k(&premise);
        assert_eq!(k, name(R4));
        assert_eq!(spelling.spelled(&k), premise);
        let named = DataFacts::spelled(&definition, std::slice::from_ref(&k), spelling.clone());
        assert!(named.refused_names().is_empty());
        assert_eq!(named.value()["assume_joined"], serde_json::json!([premise]));
        // A refusal names the premise and the findings in the front end's spelling.
        let changed = R4
            .replace(
                "rule [fb]: f(_) => bb",
                "rule [fb]: f(_) => bb [priority(40)]",
            )
            .replace(
                "rule [fa]: f(_) => a",
                "rule [fa]: f(_) => a [priority(40)]",
            );
        let refusing = DataFacts::spelled(
            &self::definition(&changed),
            std::slice::from_ref(&k),
            spelling.clone(),
        );
        let [refusal] = refusing.refused_names().try_into().unwrap();
        assert_eq!(refusal.name, premise);
        assert_eq!(refusal.reason, "changed");
        assert!(
            refusal.detail.contains("`root:crate::fa,crate::fb#"),
            "{refusal:?}"
        );
        // A spelling of two labels is dropped for both: each keeps its K label.
        let shared = SentenceNames::new([
            ("R4.fa".to_owned(), "crate::f".to_owned()),
            ("R4.fb".to_owned(), "crate::f".to_owned()),
        ]);
        assert!(shared.is_empty());
    });
}

/// Test 7, the cheaper uniqueness check (the WASM and KEVM baselines take minutes and gigabytes
/// to check, so the flow fixtures stand in): over every finding of every `testdata/flow/findings`
/// fixture, one name is one proposition (several findings share a name only as the hook pairs of
/// one equation do: the same sentences, kind and position), and no two findings of different
/// sentences share a name.
#[test]
fn a_name_is_one_proposition_on_every_fixture() {
    on_a_big_stack(|| {
        let root = Path::new(support::DIR).join("../flow/findings");
        let mut fixtures = std::fs::read_dir(&root)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect::<Vec<_>>();
        fixtures.sort();
        let mut named = 0;
        for fixture in fixtures {
            let spec = fixture.join("spec.k");
            let text = std::fs::read_to_string(&spec).unwrap();
            let module = text
                .lines()
                .filter_map(|line| line.strip_prefix("module "))
                .next_back()
                .unwrap()
                .trim()
                .to_owned();
            let compiled = NativeValidator::bind(
                support::load_path(&spec, &module),
                CompileOptions::default(),
            )
            .compile_baseline()
            .unwrap();
            let definition = loaded_definition(&compiled).unwrap();
            let heads = definition.data_heads();
            let mut subjects = BTreeMap::<String, BTreeSet<String>>::new();
            for (_, name, _) in heads.named() {
                let name = name.expect("every fixture sentence is named");
                subjects
                    .entry(
                        k_rust_backend::data_term::names::Spelling::k(&kink_native::data::label)
                            .text(name),
                    )
                    .or_default()
                    .insert(name.subjects());
                named += 1;
            }
            for (name, keys) in &subjects {
                assert_eq!(keys.len(), 1, "{}: {name}: {keys:?}", fixture.display());
            }
        }
        assert!(named >= 10, "{named}");
    });
}
