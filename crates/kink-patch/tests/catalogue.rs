//! Catalogue order, codec pins, fixture labels and deterministic candidate sweeps.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::builtin;
use k_rust::definition::Sentence;
use k_rust::kast::Term;
use k_rust::outer::ResolvedSource;
use kink_patch::{
    Action, Baseline, CandidateDisposition, CandidateFailureKind, CandidateGeneration, Clause,
    OperatorSpec, Universe, apply, canonical_json, catalogue_v1, generate, resolve_universe,
    sha256,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

fn names() -> Vec<String> {
    let mut names = fs::read_dir(support::DIR)
        .expect("fixture directory")
        .map(|entry| {
            entry
                .expect("fixture entry")
                .file_name()
                .into_string()
                .expect("UTF-8 fixture name")
        })
        .filter(|name| name.ends_with(".k"))
        .collect::<Vec<_>>();
    names.sort();
    names
}

fn try_load(name: &str) -> Result<Baseline, String> {
    let text = fs::read_to_string(Path::new(support::DIR).join(name)).expect("fixture text");
    let module = text
        .lines()
        .filter_map(|line| line.trim().strip_prefix("module "))
        .next_back()
        .expect("a main module")
        .split_whitespace()
        .next()
        .expect("module name");
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new(name, text.clone()),
        module,
        None,
        &mut resolver,
        &support::options(),
    )
    .map_err(|error| error.to_string())
}

#[test]
fn catalogue_order_and_all_codecs_are_pinned() {
    let specs = catalogue_v1();
    assert_eq!(specs.len(), 63);
    let groups = [
        ("cond-true", 1),
        ("cond-false", 1),
        ("cond-negate", 1),
        ("not-unwrap", 1),
        ("ror", 30),
        ("aor", 20),
        ("lcr", 2),
        ("eqk", 2),
        ("int-literal", 2),
        ("drop-owise", 1),
        ("drop-priority", 1),
        ("delete-rule", 1),
    ];
    let expected_ids = groups
        .into_iter()
        .flat_map(|(id, count)| std::iter::repeat_n(id, count))
        .collect::<Vec<_>>();
    assert_eq!(
        specs.iter().map(OperatorSpec::id).collect::<Vec<_>>(),
        expected_ids
    );
    assert_eq!(
        specs
            .iter()
            .map(OperatorSpec::name)
            .collect::<BTreeSet<_>>()
            .len(),
        63
    );
    for spec in &specs {
        assert_eq!(spec.version(), 1);
        let text = spec.canonical_json();
        let decoded = OperatorSpec::from_canonical_json(&text).expect("catalogue decodes");
        assert_eq!(&decoded, spec);
        assert_eq!(decoded.canonical_json(), text);
        assert_eq!(decoded.digest(), spec.digest());
    }
    for (id, labels) in [
        (
            "ror",
            [
                "_<Int_", "_<=Int_", "_>Int_", "_>=Int_", "_==Int_", "_=/=Int_",
            ]
            .as_slice(),
        ),
        (
            "aor",
            ["_+Int_", "_-Int_", "_*Int_", "_/Int_", "_%Int_"].as_slice(),
        ),
        ("lcr", ["_andBool_", "_orBool_"].as_slice()),
        ("eqk", ["_==K_", "_=/=K_"].as_slice()),
    ] {
        let expected = labels
            .iter()
            .flat_map(|from| {
                labels
                    .iter()
                    .filter(move |to| from != *to)
                    .map(move |to| (*from, *to))
            })
            .collect::<Vec<_>>();
        let actual = specs
            .iter()
            .filter(|spec| spec.id() == id)
            .map(|spec| {
                let [Clause::Head { label }] = spec.selector() else {
                    panic!("pair head selector")
                };
                let Action::ReplaceHead { to } = spec.action() else {
                    panic!("pair replacement")
                };
                assert_eq!(spec.variant(), format!("{label}->{to}"));
                (label.as_str(), to.as_str())
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }
    assert_eq!(specs[58].variant(), "+1");
    assert_eq!(specs[59].variant(), "-1");
}

fn heads(term: &Term, labels: &mut BTreeSet<String>) {
    match term.unannotated() {
        Term::Apply { label, arguments } => {
            labels.insert(label.name.clone());
            for argument in arguments {
                heads(argument, labels);
            }
        }
        Term::Rewrite { left, right } => {
            heads(left, labels);
            heads(right, labels);
        }
        Term::As { pattern, alias } => {
            heads(pattern, labels);
            heads(alias, labels);
        }
        Term::Sequence(items) => {
            for item in items {
                heads(item, labels);
            }
        }
        _ => {}
    }
}

#[test]
fn catalogue_label_spellings_are_pinned_on_authored_fixture_rules() {
    let pins = [
        ("_<Int_", Some("guardedeq.k")),
        ("_<=Int_", Some("guardedeq.k")),
        ("_>Int_", Some("guardedeq.k")),
        ("_>=Int_", Some("guardedeq.k")),
        ("_==Int_", Some("guardedeq.k")),
        ("_=/=Int_", Some("guardeddiv.k")),
        ("_+Int_", Some("claims.k")),
        ("_-Int_", Some("t12hook.k")),
        ("_*Int_", Some("t12hook.k")),
        ("_/Int_", Some("guardeddiv.k")),
        ("_%Int_", Some("partialreq.k")),
        ("_andBool_", Some("guardedeq.k")),
        ("_orBool_", Some("guardedeq.k")),
        ("_==K_", Some("symensures.k")),
        ("_=/=K_", None),
        ("notBool_", None),
    ];
    let mut by_fixture = BTreeMap::new();
    for name in names() {
        let Ok(baseline) = try_load(&name) else {
            continue;
        };
        let mut labels = BTreeSet::new();
        for (_, sentence) in baseline.authored_sentences() {
            if let Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } = sentence
            {
                for term in [body, requires, ensures] {
                    heads(term, &mut labels);
                }
            }
        }
        by_fixture.insert(name, labels);
    }
    for (label, fixture) in pins {
        if let Some(fixture) = fixture {
            assert!(
                by_fixture
                    .get(fixture)
                    .expect("pinned fixture loads")
                    .contains(label),
                "{fixture} lacks KAST head {label}"
            );
        } else {
            assert!(
                !by_fixture.values().any(|labels| labels.contains(label)),
                "previously absent catalogue label {label} gained a fixture"
            );
        }
        println!("CS08_LABEL {}", json!({"label":label,"fixture":fixture}));
    }
}

fn summary(generation: &CandidateGeneration<'_>) -> Value {
    let candidates = generation.candidates().iter().map(|candidate| {
        assert!(candidate.patch.is_pinned());
        apply(generation.baseline(), &candidate.patch).expect("every published candidate applies");
        json!({
            "operator":candidate.operator,
            "origins":candidate.origins.iter().map(|origin| format!("{origin:?}")).collect::<Vec<_>>(),
            "patch_sha256":candidate.patch.digest().expect("patch digest").to_string(),
        })
    }).collect::<Vec<_>>();
    json!({
        "origins":generation.selected_origins().iter().map(|origin| format!("{origin:?}")).collect::<Vec<_>>(),
        "dispositions":generation.dispositions().iter().map(|disposition| format!("{disposition:?}")).collect::<Vec<_>>(),
        "candidates":candidates,
        "completeness":format!("{:?}",generation.completeness()),
        "failure":format!("{:?}",generation.failure()),
        "scored":generation.scored(),
    })
}

#[test]
fn every_loading_top_level_definition_has_a_deterministic_pinned_sweep() {
    let specs = catalogue_v1();
    let mut loaded = 0;
    for name in names() {
        let first = try_load(&name);
        let second = try_load(&name);
        let (baseline, reloaded) = match (first, second) {
            (Ok(first), Ok(second)) => (first, second),
            (Err(first), Err(second)) => {
                assert_eq!(first, second, "stable load refusal: {name}");
                println!(
                    "CS08_LOAD {}",
                    json!({"definition":name,"loaded":false,"reason":first})
                );
                continue;
            }
            _ => panic!("load changed across two loads for {name}"),
        };
        loaded += 1;
        let universe = resolve_universe(&baseline, &Universe::v1());
        let reloaded_universe = resolve_universe(&reloaded, &Universe::v1());
        for spec in &specs {
            let first = generate(&baseline, &universe, spec, usize::MAX).unwrap_or_else(|error| {
                assert_ne!(
                    error.kind(),
                    CandidateFailureKind::UnauthorizedEdit,
                    "STOP {name} {}",
                    spec.name()
                );
                panic!("generation {name} {}: {error}", spec.name());
            });
            let second = generate(&reloaded, &reloaded_universe, spec, usize::MAX)
                .expect("reloaded generation");
            assert_ne!(
                first.failure(),
                Some(CandidateFailureKind::UnauthorizedEdit)
            );
            let bytes = canonical_json(&summary(&first));
            assert_eq!(
                bytes,
                canonical_json(&summary(&second)),
                "{name} {}",
                spec.name()
            );
            assert!(
                first
                    .candidates()
                    .iter()
                    .all(|candidate| candidate.operator == spec.name())
            );
            let rejected = first
                .dispositions()
                .iter()
                .filter(|disposition| matches!(disposition, CandidateDisposition::Rejected(_)))
                .count();
            println!(
                "CS08_SWEEP {}",
                json!({
                    "definition":name,"spec":spec.name(),"origins":first.selected_origins().len(),
                    "rejected":rejected,"candidates":first.candidates().len(),
                    "completeness":format!("{:?}",first.completeness()),"failure":format!("{:?}",first.failure()),
                    "summary_sha256":sha256(bytes.as_bytes()).to_string(),
                })
            );
        }
    }
    assert_eq!(loaded, 64, "CS-05 top-level load census");
}

#[test]
fn cond_true_v1_has_an_independent_known_answer() {
    // Independently computed with Python hashlib: domain UTF-8, NUL, canonical bytes.
    const BYTES: &str = r#"{"action":{"replace-with-token":{"sort":"Bool","token":"true"}},"id":"cond-true","policy":"each","selector":[{"path":[1]},{"not-token":{"sort":"Bool","token":"true"}}],"variant":"1","version":1}"#;
    const DIGEST: &str = "576790b100cbd01d3b28759dd70e68e725716b6e6660c5869108c7c2be02799c";
    let spec = &catalogue_v1()[0];
    assert_eq!(spec.canonical_json(), BYTES);
    assert_eq!(spec.digest().to_string(), DIGEST);
    assert_eq!(
        OperatorSpec::from_canonical_json(BYTES).expect("known answer decodes"),
        *spec
    );
}
