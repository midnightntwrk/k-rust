//! One sweep over the top-level definitions of `testdata/k` (packet test-gate TG-P): each
//! definition is loaded once as written and once reformatted (three lines prepended, so every
//! source position moves), and the two loads give the catalogue's deterministic pinned candidate
//! sweep, equal sentence fingerprints, the legacy tuples and a deterministic universe, while the
//! first load's semantic input round-trips canonically. The light tier sweeps the protected
//! fixtures and checks the catalogue label pins on the fixtures that pin them; the heavy tier
//! sweeps every definition, with the load census and the label absent from every fixture.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::builtin;
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::{Sort, Term};
use k_rust::outer::ResolvedSource;
use kink_patch::{
    Baseline, CandidateDisposition, CandidateFailureKind, CandidateGeneration, ExclusionReason,
    SemanticInput, SentenceFingerprint, SentenceRef, SiteSelector, Universe, apply, canonical_json,
    catalogue_v1, derive_sites, derive_sites_in, generate, resolve_universe, sha256,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

/// The fixtures every protected kill and the declaration census's protected set rest on
/// (kink-native tests/census.rs `PROTECTED`).
const PROTECTED: &[&str] = &[
    "counter.k",
    "symmem.k",
    "symmem_release.k",
    "guardedmem.k",
    "guardedeq.k",
    "guardeddiv.k",
    "effectmem.k",
    "memory.k",
];

/// The catalogue's labels and the authored fixture rule that writes each, or `None` for a label
/// no fixture writes.
const LABEL_PINS: [(&str, Option<&str>); 16] = [
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
    ("notBool_", Some("collimp.k")),
];

/// The `.k` files of the fixture directory, sorted.
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

/// Loads `text` as the file `name`, its main module the last `module NAME` of the text.
fn try_load(name: &str, text: &str) -> Result<Baseline, String> {
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
        ResolvedSource::new(name, text.to_owned()),
        module,
        None,
        &mut resolver,
        &support::options(),
    )
    .map_err(|error| error.to_string())
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

/// The KAST heads of the authored rules of `baseline`.
fn rule_heads(baseline: &Baseline) -> BTreeSet<String> {
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
    labels
}

/// A generation's published content; every published candidate applies.
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

/// Every local sentence of every module with its fingerprint.
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

fn all_rules() -> Universe {
    Universe {
        authored: true,
        typed: false,
        exclude_attributes: vec![],
        exclude_macro_rules: false,
    }
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

fn artifact_has_no_paths_or_measurements(value: &Value, key: &str) {
    match value {
        Value::Object(object) => {
            for (key, value) in object {
                assert!(!key.ends_with("_ms"));
                artifact_has_no_paths_or_measurements(value, key);
            }
        }
        Value::Array(array) => {
            for value in array {
                artifact_has_no_paths_or_measurements(value, key);
            }
        }
        Value::String(text) if matches!(key, "logical" | "org.kframework.attributes.Source") => {
            assert!(
                !Path::new(text).is_absolute(),
                "absolute source path: {text}"
            );
        }
        _ => {}
    }
}

/// The catalogue sweep (formerly catalogue.rs
/// `every_loading_top_level_definition_has_a_deterministic_pinned_sweep`): every catalogue
/// operator generates on both loads without an unauthorized edit, publishes only its own
/// candidates, each of which applies, and publishes the same bytes from both loads.
fn catalogue_sweep(name: &str, baseline: &Baseline, reloaded: &Baseline) {
    let universe = resolve_universe(baseline, &Universe::v1());
    let reloaded_universe = resolve_universe(reloaded, &Universe::v1());
    for spec in &catalogue_v1() {
        let first = generate(baseline, &universe, spec, usize::MAX).unwrap_or_else(|error| {
            assert_ne!(
                error.kind(),
                CandidateFailureKind::UnauthorizedEdit,
                "STOP {name} {}",
                spec.name()
            );
            panic!("generation {name} {}: {error}", spec.name());
        });
        let second =
            generate(reloaded, &reloaded_universe, spec, usize::MAX).expect("reloaded generation");
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

/// The universe sweep (formerly universe.rs
/// `top_level_definitions_keep_legacy_tuples_and_have_deterministic_universes`): the legacy
/// discovery and the all-rules universe find the same tuples, the v1 universe partitions the
/// authored rules without a silent exclusion, and both loads resolve the same universe.
fn universe_sweep(name: &str, baseline: &Baseline, reloaded: &Baseline) {
    let legacy = resolve_universe(baseline, &all_rules());
    let clauses = selection_clauses();
    for clauses in &clauses {
        let old = derive_sites(baseline, "site", clauses).expect("valid clauses");
        let new = derive_sites_in(baseline, &legacy, clauses).expect("valid universe");
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
                !derive_sites(baseline, "site", &clauses)
                    .expect("cell scan")
                    .tuples()
                    .is_empty()
            });
        if !sort_cells {
            assert_eq!(old.tuples(), new.tuples(), "{name} {clauses:?}");
            assert_eq!(old.exhaustive(), new.exhaustive(), "{name} {clauses:?}");
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
                let old = derive_sites(baseline, "site", &clauses);
                let new = derive_sites_in(baseline, &legacy, &clauses);
                match (old, new) {
                    (Ok(old), Ok(new)) => assert_eq!(old.tuples(), new.tuples(), "{at:?}"),
                    (Err(old), Err(new)) => assert_eq!(old, new),
                    other => panic!("{at:?}: {other:?}"),
                }
            }
        }
    }
    let resolved = resolve_universe(baseline, &Universe::v1());
    let mut partition = resolved.included().to_vec();
    partition.extend(resolved.excluded().iter().map(|(at, _)| at.clone()));
    partition.sort();
    let mut written = baseline
        .authored_sentences()
        .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
        .map(|(at, _)| at)
        .collect::<Vec<_>>();
    written.sort();
    assert_eq!(partition, written, "{name}: no silent exclusions");
    let repeated = resolve_universe(reloaded, &Universe::v1());
    assert_eq!(resolved.excluded(), repeated.excluded());
    assert_eq!(resolved.excluded_digest(), repeated.excluded_digest());
    assert_eq!(
        canonical_json(&resolved.value()),
        canonical_json(&repeated.value())
    );
    let mut counts = BTreeMap::<String, usize>::new();
    for (_, reason) in resolved.excluded() {
        let key = match reason {
            ExclusionReason::Attribute(key) => format!("attribute:{key}"),
            ExclusionReason::MacroRule => "macro-rule".to_owned(),
        };
        *counts.entry(key).or_default() += 1;
    }
    println!(
        "universe-count {name} included={} excluded={}",
        resolved.included().len(),
        canonical_json(&json!(counts))
    );
}

/// The semantic-input round trip (formerly semantic_input.rs `corpus_round_trip_is_canonical`):
/// the artifact holds no absolute path or measurement and reads back to an equal input, an equal
/// definition, source table and fingerprints.
fn semantic_input_round_trip(original: &Baseline) {
    let input = SemanticInput::of(original).unwrap();
    assert!(!input.text().contains(env!("CARGO_MANIFEST_DIR")));
    artifact_has_no_paths_or_measurements(&serde_json::from_str(input.text()).unwrap(), "");
    let (read, baseline) = SemanticInput::read(input.text()).unwrap();
    assert_eq!(input, read);
    assert_eq!(input, SemanticInput::of(&baseline).unwrap());
    assert_eq!(original.definition(), baseline.definition());
    assert_eq!(
        original.loaded().source_table(),
        baseline.loaded().source_table()
    );
    let table = |b: &Baseline| {
        b.authored_sentences()
            .map(|(at, _)| {
                let fingerprint = b.fingerprint(&at).unwrap();
                (at, fingerprint)
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(table(original), table(&baseline));
}

/// Every sweep check on the fixture `name`; returns the KAST heads of its authored rules.
fn sweep(name: &str) -> BTreeSet<String> {
    let text = fs::read_to_string(Path::new(support::DIR).join(name)).expect("fixture text");
    let reformatted = format!("// fingerprint reformat probe\n\n\n{text}");
    let (baseline, reloaded) = match (try_load(name, &text), try_load(name, &reformatted)) {
        (Ok(first), Ok(second)) => (first, second),
        (Err(first), Err(_)) => {
            assert_eq!(
                Err(first.clone()),
                try_load(name, &text).map(|_| ()),
                "stable load refusal: {name}"
            );
            println!(
                "CS08_LOAD {}",
                json!({"definition":name,"loaded":false,"reason":first})
            );
            panic!("{name}: every top-level definition loads: {first}");
        }
        _ => panic!("load changed across two loads for {name}"),
    };
    catalogue_sweep(name, &baseline, &reloaded);
    assert_eq!(table(&baseline), table(&reloaded), "{name}");
    universe_sweep(name, &baseline, &reloaded);
    semantic_input_round_trip(&baseline);
    rule_heads(&baseline)
}

/// Sweeps `names` on up to eight threads; the KAST heads of each fixture's authored rules.
fn sweep_all(names: &[&str]) -> BTreeMap<String, BTreeSet<String>> {
    let next = AtomicUsize::new(0);
    let threads = names.len().min(8);
    let swept = std::thread::scope(|scope| {
        let workers = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    let mut swept = Vec::new();
                    loop {
                        let Some(name) = names.get(next.fetch_add(1, Ordering::Relaxed)) else {
                            return swept;
                        };
                        swept.push((name.to_string(), sweep(name)));
                    }
                })
            })
            .collect::<Vec<_>>();
        workers
            .into_iter()
            .flat_map(|worker| worker.join().expect("a fixture's sweep failed"))
            .collect::<BTreeMap<_, _>>()
    });
    assert_eq!(swept.len(), names.len(), "every fixture is swept");
    swept
}

/// The label pins whose fixture is in `by_fixture`; with `every` set, also that no fixture
/// writes a label pinned as absent.
fn assert_label_pins(by_fixture: &BTreeMap<String, BTreeSet<String>>, every: bool) {
    for (label, fixture) in LABEL_PINS {
        if let Some(fixture) = fixture {
            assert!(
                by_fixture
                    .get(fixture)
                    .expect("pinned fixture loads")
                    .contains(label),
                "{fixture} lacks KAST head {label}"
            );
        } else if every {
            assert!(
                !by_fixture.values().any(|labels| labels.contains(label)),
                "previously absent catalogue label {label} gained a fixture"
            );
        }
        println!("CS08_LABEL {}", json!({"label":label,"fixture":fixture}));
    }
}

/// The light subset of the sweep: every protected fixture.
#[test]
fn the_protected_fixtures_have_a_deterministic_sweep() {
    sweep_all(PROTECTED);
}

/// Each catalogue label is written by an authored rule of the fixture that pins it (formerly
/// catalogue.rs `catalogue_label_spellings_are_pinned_on_authored_fixture_rules`, whose absent
/// label the heavy sweep checks over every fixture).
#[test]
fn catalogue_label_spellings_are_pinned_on_their_fixtures() {
    let fixtures = LABEL_PINS
        .iter()
        .filter_map(|(_, fixture)| *fixture)
        .collect::<BTreeSet<_>>();
    let by_fixture = fixtures
        .into_iter()
        .map(|name| {
            let text =
                fs::read_to_string(Path::new(support::DIR).join(name)).expect("fixture text");
            let baseline = try_load(name, &text).expect("pinned fixture loads");
            (name.to_owned(), rule_heads(&baseline))
        })
        .collect();
    assert_label_pins(&by_fixture, false);
}

mod heavy {
    use super::*;

    /// The whole sweep: every top-level definition of the fixture directory (the CS-05 load
    /// census of 69), and the catalogue label pins over all of them.
    #[test]
    #[ignore = "heavy"]
    fn every_top_level_definition_has_a_deterministic_sweep() {
        let names = names();
        let by_fixture = sweep_all(&names.iter().map(String::as_str).collect::<Vec<_>>());
        assert_eq!(by_fixture.len(), 69, "CS-05 top-level load census");
        assert_label_pins(&by_fixture, true);
    }
}
