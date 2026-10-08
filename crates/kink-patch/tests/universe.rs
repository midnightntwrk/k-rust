//! The declared written-rule universe and its exhaustive selector predicates.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::builtin;
use k_rust::definition::sentence_mut;
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::{Sort, Term};
use k_rust::outer::ResolvedSource;
use kink_patch::{
    Baseline, Discovery, Edit, ExclusionReason, Patch, SelectionPolicy, SiteSelector, Universe,
    canonical_json, derive_sites, derive_sites_in, payload_digest, resolve_universe, select,
};
use serde_json::json;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

fn load_text(text: &str) -> Baseline {
    let mut resolver = |_: &str, name: &str| {
        builtin::embedded(name).ok_or_else(|| format!("{name} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new("cells.k", text),
        "CELLS",
        None,
        &mut resolver,
        &support::options(),
    )
    .expect("inline cell fixture loads")
}

fn cells() -> Baseline {
    load_text(
        r#"
module CELLS
 imports INT
 imports BASIC-K
 syntax KItem ::= go() [symbol(go)] | done() [symbol(done)]
 configuration <top> <k> .K </k> <n> 0 </n> </top>
 rule [go]: <k> go() => done() ... </k> <n> N => N +Int 1 </n>
endmodule
"#,
    )
}

fn all_rules() -> Universe {
    Universe {
        authored: true,
        typed: false,
        exclude_attributes: vec![],
        exclude_macro_rules: false,
    }
}

fn paths(discovery: &Discovery<'_>) -> Vec<Vec<u32>> {
    discovery
        .tuples()
        .iter()
        .map(|tuple| tuple.sites[0].at.path.0.clone())
        .collect()
}

#[test]
fn each_new_clause_has_positive_and_negative_exhaustive_rows() {
    let baseline = support::load("counter.k");
    let universe = resolve_universe(&baseline, &Universe::v1());
    let rule = SiteSelector::RuleLabel("COUNTER.increment".to_owned());
    let rows = [
        (
            vec![
                SiteSelector::Path(vec![0, 1, 0]),
                SiteSelector::NotHead {
                    label: "z".to_owned(),
                },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![0, 1, 0]),
                SiteSelector::NotHead {
                    label: "s".to_owned(),
                },
            ],
            false,
        ),
        (
            vec![
                SiteSelector::Path(vec![1]),
                SiteSelector::NotToken {
                    token: "false".to_owned(),
                    sort: Sort::new("Bool"),
                },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![1]),
                SiteSelector::NotToken {
                    token: "true".to_owned(),
                    sort: Sort::new("Bool"),
                },
            ],
            false,
        ),
        (
            vec![
                SiteSelector::Path(vec![1]),
                SiteSelector::TokenOfSort {
                    sort: Sort::new("Bool"),
                },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![1]),
                SiteSelector::TokenOfSort {
                    sort: Sort::new("Int"),
                },
            ],
            false,
        ),
        (
            vec![
                SiteSelector::Path(vec![0]),
                SiteSelector::RuleAttribute {
                    key: "label".to_owned(),
                    present: true,
                },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![0]),
                SiteSelector::RuleAttribute {
                    key: "label".to_owned(),
                    present: false,
                },
            ],
            false,
        ),
        (
            vec![
                SiteSelector::Path(vec![0, 1, 0]),
                SiteSelector::ArgumentCount { count: 1 },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![0, 1, 0]),
                SiteSelector::ArgumentCount { count: 2 },
            ],
            false,
        ),
    ];
    for (mut clauses, present) in rows {
        clauses.push(rule.clone());
        let derived = derive_sites_in(&baseline, &universe, &clauses).expect("valid clauses");
        assert!(derived.exhaustive(), "{clauses:?}");
        assert_eq!(derived.tuples().len(), usize::from(present), "{clauses:?}");
        assert_eq!(
            derived.tuples(),
            derive_sites(&baseline, "site", &clauses)
                .expect("legacy clauses")
                .tuples()
        );
    }
    for present in [false, true] {
        let derived = derive_sites_in(
            &baseline,
            &universe,
            &[
                rule.clone(),
                SiteSelector::Path(vec![0]),
                SiteSelector::RuleAttribute {
                    key: "owise".to_owned(),
                    present,
                },
            ],
        )
        .expect("attribute absence");
        assert!(derived.exhaustive());
        assert_eq!(derived.tuples().len(), usize::from(!present));
    }
}

#[test]
fn cell_syntax_is_a_sort_non_site_only_in_the_declared_universe() {
    let baseline = cells();
    let universe = resolve_universe(&baseline, &Universe::v1());
    assert!(universe.excluded().is_empty());
    for label in ["#cells", "#dots", "#noDots"] {
        let head = SiteSelector::Head {
            label: label.to_owned(),
        };
        let syntax = derive_sites(&baseline, "site", std::slice::from_ref(&head)).expect("head");
        assert!(!syntax.tuples().is_empty(), "fixture has {label}");
        let clauses = [head, SiteSelector::Sort(Sort::new("Int"))];
        let old = derive_sites(&baseline, "site", &clauses).expect("legacy sort");
        let new = derive_sites_in(&baseline, &universe, &clauses).expect("universe sort");
        assert!(!old.exhaustive(), "legacy {label}");
        assert!(new.exhaustive(), "universe {label}");
        assert!(new.tuples().is_empty());
        assert_eq!(paths(&new), paths(&old));
    }
}

fn load_definition(path: &Path) -> Option<Baseline> {
    let text = fs::read_to_string(path).expect("fixture readable");
    let module = text
        .lines()
        .filter_map(|line| line.trim().strip_prefix("module "))
        .next_back()
        .expect("a main module")
        .split_whitespace()
        .next()
        .expect("module name");
    let mut resolver = |_: &str, name: &str| {
        builtin::embedded(name).ok_or_else(|| format!("{name} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new(
            path.file_name().expect("name").to_str().expect("UTF-8"),
            text.clone(),
        ),
        module,
        None,
        &mut resolver,
        &support::options(),
    )
    .ok()
}

fn selection_clauses() -> Vec<Vec<SiteSelector>> {
    let path = |p: &[u32]| SiteSelector::Path(p.to_vec());
    let sort = |s: &str| SiteSelector::Sort(Sort::new(s));
    let head = |s: &str| SiteSelector::Head {
        label: s.to_owned(),
    };
    let bind = |s: &str| SiteSelector::Bind(s.to_owned());
    vec![
        vec![],
        vec![path(&[0])],
        vec![path(&[0, 1])],
        vec![path(&[1])],
        vec![path(&[2])],
        vec![head("s")],
        vec![sort("Nat")],
        vec![path(&[1]), sort("Bool")],
        vec![path(&[2]), sort("Bool")],
        vec![path(&[0, 1, 0]), sort("Nat"), head("s"), bind("E")],
        vec![path(&[0, 0, 1]), sort("Nat"), bind("V")],
        vec![path(&[0, 0, 0]), bind("A")],
        vec![path(&[0, 0, 0, 0]), bind("A")],
        vec![sort("Nat"), bind("A")],
        vec![path(&[0, 0]), bind("X")],
        vec![path(&[0]), bind("X")],
        vec![path(&[0]), bind("V"), bind("T")],
    ]
}

#[test]
fn top_level_definitions_keep_legacy_tuples_and_have_deterministic_universes() {
    let mut files = fs::read_dir(support::DIR)
        .expect("testdata")
        .map(|entry| entry.expect("entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
        .collect::<Vec<_>>();
    files.sort();
    let mut loaded = 0;
    for file in files {
        let Some(baseline) = load_definition(&file) else {
            continue;
        };
        loaded += 1;
        let legacy = resolve_universe(&baseline, &all_rules());
        let clauses = selection_clauses();
        for clauses in &clauses {
            let old = derive_sites(&baseline, "site", clauses).expect("valid clauses");
            let new = derive_sites_in(&baseline, &legacy, clauses).expect("valid universe");
            let sort_cells = clauses
                .iter()
                .any(|clause| matches!(clause, SiteSelector::Sort(_)))
                && ["#cells", "#dots", "#noDots"].iter().any(|label| {
                    let mut clauses = clauses
                        .iter()
                        .filter(|clause| !matches!(clause, SiteSelector::Sort(_)))
                        .cloned()
                        .collect::<Vec<_>>();
                    clauses.push(SiteSelector::Head {
                        label: (*label).to_owned(),
                    });
                    !derive_sites(&baseline, "site", &clauses)
                        .expect("cell scan")
                        .tuples()
                        .is_empty()
                });
            if !sort_cells {
                assert_eq!(old.tuples(), new.tuples(), "{} {clauses:?}", file.display());
                assert_eq!(
                    old.exhaustive(),
                    new.exhaustive(),
                    "{} {clauses:?}",
                    file.display()
                );
            }
        }
        for (at, sentence) in baseline
            .authored_sentences()
            .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
        {
            if let Some(label) = sentence.attributes().string(AttributeKey::Label) {
                for path in [vec![0], vec![0, 1]] {
                    let clauses = [
                        SiteSelector::RuleLabel(label.to_owned()),
                        SiteSelector::Path(path),
                    ];
                    let old = derive_sites(&baseline, "site", &clauses);
                    let new = derive_sites_in(&baseline, &legacy, &clauses);
                    match (old, new) {
                        (Ok(old), Ok(new)) => assert_eq!(old.tuples(), new.tuples(), "{at:?}"),
                        (Err(old), Err(new)) => assert_eq!(old, new),
                        other => panic!("{at:?}: {other:?}"),
                    }
                }
            }
        }
        let resolved = resolve_universe(&baseline, &Universe::v1());
        let mut partition = resolved.included().to_vec();
        partition.extend(resolved.excluded().iter().map(|(at, _)| at.clone()));
        partition.sort();
        let mut written = baseline
            .authored_sentences()
            .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
            .map(|(at, _)| at)
            .collect::<Vec<_>>();
        written.sort();
        assert_eq!(
            partition,
            written,
            "{}: no silent exclusions",
            file.display()
        );
        let again = load_definition(&file).expect("second load");
        let repeated = resolve_universe(&again, &Universe::v1());
        assert_eq!(resolved.excluded(), repeated.excluded());
        assert_eq!(resolved.excluded_digest(), repeated.excluded_digest());
        assert_eq!(
            canonical_json(&resolved.value()),
            canonical_json(&repeated.value())
        );
        let mut counts = BTreeMap::<String, usize>::new();
        for (_, reason) in resolved.excluded() {
            let key = match reason {
                ExclusionReason::Untyped => "untyped".to_owned(),
                ExclusionReason::Attribute(key) => format!("attribute:{key}"),
                ExclusionReason::MacroRule => "macro-rule".to_owned(),
            };
            *counts.entry(key).or_default() += 1;
        }
        println!(
            "universe-count {} included={} excluded={}",
            file.file_name().expect("name").to_string_lossy(),
            resolved.included().len(),
            canonical_json(&json!(counts))
        );
    }
    assert!(loaded > 0);
}

#[test]
fn universe_value_has_exact_keys_and_the_excluded_payload_digest() {
    let baseline = support::load("claims.k");
    let resolved = resolve_universe(&baseline, &Universe::v1());
    let value = resolved.value();
    let keys = value
        .as_object()
        .expect("object")
        .keys()
        .map(String::as_str)
        .collect::<Vec<_>>();
    assert_eq!(
        keys,
        [
            "authored",
            "exclude_attributes",
            "exclude_macro_rules",
            "excluded",
            "excluded_sha256",
            "kinds",
            "typed"
        ]
    );
    assert_eq!(value["kinds"], json!(["rule"]));
    assert_eq!(value["authored"], true);
    assert_eq!(value["typed"], true);
    assert_eq!(
        value["exclude_attributes"],
        json!(["simplification", "smt-lemma"])
    );
    assert_eq!(value["exclude_macro_rules"], true);
    assert_eq!(
        value["excluded_sha256"],
        payload_digest(
            "kink/universe-excluded/v1",
            canonical_json(&value["excluded"]).as_bytes()
        )
        .to_string()
    );
    for entry in value["excluded"].as_array().expect("exclusions") {
        assert_eq!(
            entry
                .as_object()
                .expect("entry")
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            ["index", "module", "reason"]
        );
    }
    assert!(resolved.included().windows(2).all(|pair| pair[0] < pair[1]));
    assert!(
        resolved
            .excluded()
            .windows(2)
            .all(|pair| pair[0].0 < pair[1].0)
    );
}

#[test]
fn expected_rule_exclusions() {
    let partial = support::load("sympartial.k");
    let resolved = resolve_universe(&partial, &Universe::v1());
    assert_eq!(
        resolved.excluded(),
        &[(
            support::rule(&partial, "SYMPARTIAL.halflet"),
            ExclusionReason::Untyped
        )]
    );
    let macros = support::load("t12macro.k");
    let resolved = resolve_universe(&macros, &Universe::v1());
    assert_eq!(resolved.excluded().len(), 1);
    assert_eq!(resolved.excluded()[0].1, ExclusionReason::MacroRule);
    let claims = support::load("claims.k");
    let resolved = resolve_universe(&claims, &Universe::v1());
    assert!(resolved.excluded().contains(&(
        support::rule(&claims, "CLAIMS.lemma"),
        ExclusionReason::Attribute("simplification".to_owned())
    )));
}

#[test]
fn every_other_missing_sort_keeps_the_discovery_incomplete() {
    let baseline = support::load("counter.k");
    let at = support::rule(&baseline, "COUNTER.increment");
    let mut definition = baseline.definition().clone();
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == at.module)
        .expect("module");
    let Sentence::Rule { requires, .. } =
        sentence_mut(&mut module.local_sentences[at.index as usize])
    else {
        panic!("rule");
    };
    *requires = Term::Variable {
        name: "B".to_owned(),
        sort: None,
    };
    let baseline = Baseline::new(
        baseline
            .loaded()
            .with_definition(definition)
            .expect("relinks"),
    );
    let universe = resolve_universe(&baseline, &all_rules());
    let clauses = [
        SiteSelector::Path(vec![1]),
        SiteSelector::Sort(Sort::new("Bool")),
    ];
    let old = derive_sites(&baseline, "site", &clauses).expect("legacy");
    let new = derive_sites_in(&baseline, &universe, &clauses).expect("universe");
    assert!(!old.exhaustive() && !new.exhaustive());
    assert_eq!(old.tuples(), new.tuples());
}

#[test]
fn a_foreign_universe_cannot_silently_skip_rules() {
    let counter = support::load("counter.k");
    let memory = support::load("memory.k");
    let universe = resolve_universe(&memory, &all_rules());
    assert!(derive_sites_in(&counter, &universe, &[]).is_err());
}

#[test]
fn exclusion_priority_is_untyped_then_attribute_then_macro_rule() {
    let partial = support::load("sympartial.k");
    let universe = Universe {
        exclude_attributes: vec!["label".to_owned()],
        ..Universe::v1()
    };
    let resolved = resolve_universe(&partial, &universe);
    assert!(resolved.excluded().contains(&(
        support::rule(&partial, "SYMPARTIAL.halflet"),
        ExclusionReason::Untyped
    )));
    assert!(resolved.excluded().contains(&(
        support::rule(&partial, "SYMPARTIAL.half"),
        ExclusionReason::Attribute("label".to_owned())
    )));
    let macros = support::load("t12macro.k");
    let default = resolve_universe(&macros, &Universe::v1());
    let macro_at = &default.excluded()[0].0;
    let universe = Universe {
        exclude_attributes: vec![AttributeKey::Source.as_str().to_owned()],
        ..Universe::v1()
    };
    let resolved = resolve_universe(&macros, &universe);
    assert!(resolved.excluded().contains(&(
        macro_at.clone(),
        ExclusionReason::Attribute(AttributeKey::Source.as_str().to_owned())
    )));
}

#[test]
fn recorded_exclusions_alone_do_not_make_a_generation_incomplete() {
    let baseline = support::load("sympartial.k");
    let universe = resolve_universe(&baseline, &Universe::v1());
    assert_eq!(universe.excluded().len(), 1);
    let discovery = derive_sites_in(
        &baseline,
        &universe,
        &[
            SiteSelector::Path(vec![1]),
            SiteSelector::Sort(Sort::new("Bool")),
        ],
    )
    .expect("declared requires sites");
    assert!(discovery.exhaustive());
    assert_eq!(discovery.tuples().len(), 3);
    let generation = select(&discovery, SelectionPolicy::Each, 16)
        .expect("finite selection")
        .fold("requires-false", |origin| {
            let at = origin.site_tuple[0].clone();
            Patch::new(vec![Edit::ReplaceTerm {
                expected: baseline.term(&at).expect("term").clone(),
                at,
                replacement: Term::Token {
                    token: "false".to_owned(),
                    sort: Sort::new("Bool"),
                },
            }])
            .expect("one edit")
        })
        .expect("each edit stays in its origin");
    assert!(generation.scored());
    assert_eq!(generation.candidates().len(), 3);
}

#[test]
fn v1_discovery_refuses_an_un_authored_declaration() {
    let baseline = support::load("counter.k");
    let universe = resolve_universe(
        &baseline,
        &Universe {
            authored: false,
            ..all_rules()
        },
    );
    assert!(derive_sites_in(&baseline, &universe, &[]).is_err());
}
