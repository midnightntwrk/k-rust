//! Rule coverage of baseline runs and the compiled rule id -> `SentenceRef` map (corpus-scale
//! CS-03, README section 4.5; semantic-input ticket SI-T04).

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::builtin;
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use k_rust::outer::ResolvedSource;
use kink_native::coverage::{
    Authorship, COVERAGE_DOMAIN, RuleAuthors, TestCoverage, UNMAPPED_INSERTED, coverage_digest,
    coverage_text,
};
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, SolverProfile};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{Baseline, Edit, InsertPosition, Patch, SentenceRef, TermRef};
use serde_json::json;

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: Some(1000),
    max_breadth: None,
};

/// Runs `body` with stack headroom for compilation and execution.
fn with_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(body)
        .expect("test thread")
        .join()
        .expect("test thread does not panic");
}

fn app(symbol: &str, arguments: Vec<Pattern>) -> Pattern {
    kore_application(symbol, Vec::new(), arguments)
}

fn bool_value(value: &str) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortBool"),
        value: value.into(),
    }
}

fn inj(from: &str, to: &str, pattern: Pattern) -> Pattern {
    kore_application("inj", vec![kore_sort(from), kore_sort(to)], vec![pattern])
}

fn counter_state() -> Pattern {
    let z = || app("Lblz", vec![]);
    let s = |p| app("Lbls", vec![p]);
    support::initial_state(app("Lblcounter", vec![z(), s(s(s(z())))]), "SortCounter")
}

fn choose_state(argument: Pattern) -> Pattern {
    support::initial_state(app("Lblchoose", vec![argument]), "SortControl")
}

fn divide_state() -> Pattern {
    support::initial_state(
        app("Lbldivide", vec![support::int(10), support::int(2)]),
        "SortProg",
    )
}

fn load_state() -> Pattern {
    support::initial_state(
        app(
            "Lblseq",
            vec![
                app(
                    "Lblload",
                    vec![app("Lbladdr", vec![support::int(1)]), support::int(0)],
                ),
                app("Lblhalt", vec![]),
            ],
        ),
        "SortProg",
    )
}

/// `add(inc(1), 2)` of strictheat.k.
fn strict_state() -> Pattern {
    support::initial_state(
        app(
            "Lbladd",
            vec![
                app("Lblinc", vec![inj("SortInt", "SortExp", support::int(1))]),
                inj("SortInt", "SortExp", support::int(2)),
            ],
        ),
        "SortExp",
    )
}

fn compile(name: &str) -> (NativeValidator, ValidatedDefinition) {
    let validator = NativeValidator::bind(support::load(name), CompileOptions::default());
    let side = validator.compile_baseline().expect("baseline compiles");
    (validator, side)
}

fn backend(side: &ValidatedDefinition, module: &str) -> Backend {
    Backend::from_definition(
        parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
        module,
        BackendOptions::default(),
    )
    .expect("backend")
}

/// The coverage of one state's observed, unobserved and (when the step run is observable)
/// stepped runs, each on a fresh backend.
struct Runs {
    observed: TestCoverage,
    unobserved: TestCoverage,
    stepped: Option<TestCoverage>,
}

fn runs(side: &ValidatedDefinition, module: &str, test_id: &str, state: &Pattern) -> Runs {
    let authors = RuleAuthors::of(side);
    let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
    let observed = adapter
        .execute(&mut backend(side, module), state, BUDGET)
        .expect("observed run");
    let unobserved = adapter
        .execute_unobserved(&mut backend(side, module), state, BUDGET)
        .expect("unobserved run");
    let stepped = adapter
        .execute_steps(&mut backend(side, module), state, BUDGET)
        .expect("stepped run")
        .ok();
    Runs {
        observed: TestCoverage::of_execution(test_id, &observed, &authors),
        unobserved: TestCoverage::of_unobserved(test_id, &unobserved, &authors),
        stepped: stepped
            .map(|stepped| TestCoverage::of_execution(test_id, &stepped.adapted, &authors)),
    }
}

fn refs(module: &str, indices: &[u32]) -> BTreeSet<SentenceRef> {
    indices
        .iter()
        .map(|index| SentenceRef::new(module, *index))
        .collect()
}

fn ids_of(authors: &RuleAuthors, at: &SentenceRef) -> BTreeSet<String> {
    authors.ids_of(at).map(str::to_owned).collect()
}

/// README section 9, CS-03 rows (scout-coverage M-C3), in both profiles; M-C4 for each run.
#[test]
fn coverage_pins() {
    with_stack(|| {
        let (validator, counter) = compile("counter.k");
        let baseline = validator.baseline();
        let authors = RuleAuthors::of(&counter);
        let increment = support::rule(baseline, "COUNTER.increment");
        let branch = support::rule(baseline, "COUNTER.branch");
        assert_eq!(increment, SentenceRef::new("COUNTER", 0));
        assert_eq!(branch, SentenceRef::new("COUNTER", 1));

        let t1 = runs(&counter, "COUNTER", "t1", &counter_state());
        assert!(t1.observed.complete);
        assert_eq!(t1.observed.sentences, refs("COUNTER", &[0]));
        assert_eq!(t1.observed.rule_ids, ids_of(&authors, &increment));
        assert!(t1.observed.unmapped.is_empty());

        let choose = runs(&counter, "COUNTER", "t2", &choose_state(bool_value("true")));
        assert!(choose.observed.complete);
        assert_eq!(choose.observed.sentences, refs("COUNTER", &[1]));
        assert_eq!(choose.observed.rule_ids, ids_of(&authors, &branch));

        let symbolic = runs(
            &counter,
            "COUNTER",
            "choose-B",
            &choose_state(support::var("B", "SortBool")),
        );
        eprintln!("COVERAGE_SYMBOLIC_CHOOSE {}", symbolic.observed.value());
        if cfg!(feature = "z3") {
            // Both rules fire: `branch` under B, and `fallback` on every instance.
            assert!(symbolic.observed.complete);
            assert_eq!(symbolic.observed.sentences, refs("COUNTER", &[1, 2]));
        } else {
            // Indeterminate at depth 0: nothing committed, incomplete.
            assert!(!symbolic.observed.complete);
            assert!(symbolic.observed.rule_ids.is_empty());
        }

        let (validator, guardeddiv) = compile("guardeddiv.k");
        let divide = runs(&guardeddiv, "GUARDEDDIV", "divide", &divide_state());
        assert!(divide.observed.complete);
        assert_eq!(divide.observed.sentences, refs("GUARDEDDIV", &[2, 3]));
        assert_eq!(
            divide.observed.sentences,
            [
                support::rule(validator.baseline(), "GUARDEDDIV.divide"),
                support::rule(validator.baseline(), "GUARDEDDIV.done"),
            ]
            .into_iter()
            .collect()
        );

        // The `norm` equation decides load's condition but is not traced (M-C3, CS-T09): a
        // known under-approximation of coverage.
        let (validator, guardedeq) = compile("guardedeq.k");
        let eq_authors = RuleAuthors::of(&guardedeq);
        let load = runs(&guardedeq, "GUARDEDEQ", "load", &load_state());
        assert!(load.observed.complete);
        assert_eq!(load.observed.sentences, refs("GUARDEDEQ", &[5]));
        assert_eq!(
            support::rule(validator.baseline(), "GUARDEDEQ.load"),
            SentenceRef::new("GUARDEDEQ", 5)
        );
        let norm = support::rule(validator.baseline(), "GUARDEDEQ.norm");
        let norm_ids = ids_of(&eq_authors, &norm);
        assert!(!norm_ids.is_empty(), "the norm equation has a compiled id");
        assert!(load.observed.rule_ids.is_disjoint(&norm_ids));
        assert!(!load.observed.sentences.contains(&norm));

        // M-C4: the observed, unobserved and stepped runs cover the same ids.
        for (name, run) in [
            ("t1", &t1),
            ("choose", &choose),
            ("choose-B", &symbolic),
            ("divide", &divide),
            ("load", &load),
        ] {
            assert_eq!(run.observed.rule_ids, run.unobserved.rule_ids, "{name}");
            assert_eq!(run.observed, run.unobserved, "{name}");
            let stepped = run.stepped.as_ref().expect("an observable step run");
            assert_eq!(&run.observed, stepped, "{name}");
        }
    });
}

/// The deliberate duplicate's one compiled id has both sentences as authors, and a run of it
/// covers both (scout-coverage M-C1).
#[test]
fn duplicate_unlabelled_id_maps_to_both_sentences() {
    with_stack(|| {
        let (validator, side) = compile("duplicate_unlabelled.k");
        let authors = RuleAuthors::of(&side);
        let written = validator
            .baseline()
            .authored_sentences()
            .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
            .map(|(at, _)| at)
            .collect::<BTreeSet<_>>();
        assert_eq!(written.len(), 2);
        let shared = authors
            .iter()
            .filter(|(_, authorship)| {
                matches!(authorship, Authorship::Sentences(sentences) if *sentences == written)
            })
            .map(|(id, _)| id.to_owned())
            .collect::<Vec<_>>();
        assert_eq!(shared.len(), 1, "one id for the two equal sentences");
        let state = support::initial_state(app("Lblx", vec![]), "SortS");
        let run = runs(&side, "DUPLICATE'Unds'UNLABELLED", "x", &state);
        assert!(run.observed.complete);
        assert_eq!(run.observed.rule_ids, shared.iter().cloned().collect());
        assert_eq!(run.observed.sentences, written);
        assert_eq!(run.observed, run.unobserved);
        // The two equal sentences compile to one axiom, so the step run observes it too.
        assert_eq!(Some(&run.observed), run.stepped.as_ref());
    });
}

/// Coverage bytes are a function of the definition, the state and the build: two loads,
/// compiles and runs agree byte for byte, and no host path enters them.
#[test]
fn coverage_text_is_deterministic() {
    with_stack(|| {
        let coverage = || {
            let (_, counter) = compile("counter.k");
            let (_, guardeddiv) = compile("guardeddiv.k");
            vec![
                runs(&counter, "COUNTER", "t1", &counter_state()).observed,
                runs(&counter, "COUNTER", "t2", &choose_state(bool_value("true"))).observed,
                runs(&guardeddiv, "GUARDEDDIV", "divide", &divide_state()).observed,
            ]
        };
        let (first, second) = (coverage(), coverage());
        assert_eq!(coverage_text(&first), coverage_text(&second));
        assert_eq!(coverage_digest(&first), coverage_digest(&second));
        assert_eq!(
            coverage_digest(&first),
            kink_patch::payload_digest(COVERAGE_DOMAIN, coverage_text(&first).as_bytes())
        );
        let text = coverage_text(&first);
        assert!(!text.contains(env!("CARGO_MANIFEST_DIR")));
        assert!(!text.contains("/home"));
        let value: serde_json::Value = serde_json::from_str(&text).expect("JSON");
        assert_eq!(value[0]["test_id"], "t1");
        assert_eq!(value[0]["complete"], true);
        assert_eq!(
            value[0]["sentences"],
            json!([{"module": "COUNTER", "index": 0}])
        );
        assert_eq!(value[0]["unmapped"], json!([]));
        eprintln!("COVERAGE_TEXT {text}");
        eprintln!("COVERAGE_DIGEST {}", coverage_digest(&first));
    });
}

/// Every Compile address of every top-level testdata definition names a sentence of the
/// definition it compiled (the packet's STOP condition), and every executable rewrite id has
/// provenance (M-C2). The per-definition table goes to the handoff.
#[test]
fn rule_authors_resolve_over_testdata() {
    with_stack(|| {
        let mut paths: Vec<_> = std::fs::read_dir(support::DIR)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
            .collect();
        paths.sort();
        let mut totals = BTreeMap::<String, u64>::new();
        for path in paths {
            let name = path.file_name().unwrap().to_str().unwrap().to_owned();
            let text = std::fs::read_to_string(&path).unwrap();
            let module = text
                .lines()
                .filter_map(|line| line.trim().strip_prefix("module "))
                .next_back()
                .unwrap()
                .split_whitespace()
                .next()
                .unwrap()
                .to_owned();
            let mut resolver = |_: &str, required: &str| {
                builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
            };
            let Ok(baseline) = Baseline::load(
                ResolvedSource::new(&name, text.clone()),
                &module,
                None,
                &mut resolver,
                &support::options(),
            ) else {
                eprintln!("COVERAGE_MAP_LOAD_REFUSED {name}");
                continue;
            };
            let compiled =
                NativeValidator::bind(baseline, CompileOptions::default()).compile_baseline();
            // Re-pin R0a (finding E-06; k-rust f07565265, 55a57846b, bc90d4226): b1coll.k and
            // t13role.k are refused by compilation at 501f18b9; the refusal is pinned, not skipped.
            let side = match (support::expected_compile_failure(&name), compiled) {
                (None, Ok(side)) => side,
                (None, Err(error)) => panic!("{name}: {error}"),
                (
                    Some((stage, detail)),
                    Err(kink_native::NativeFailure::Compilation {
                        stage: actual,
                        detail: text,
                    }),
                ) => {
                    assert_eq!(actual, stage, "{name}: {text}");
                    assert!(
                        detail.iter().all(|fragment| text.contains(fragment)),
                        "{name}: {text}"
                    );
                    eprintln!("COVERAGE_MAP_COMPILE_REFUSED {name}");
                    continue;
                }
                (Some(_), Ok(_)) => panic!("{name}: expected a compile refusal, compiled"),
            };
            let authors = RuleAuthors::of(&side);
            assert!(
                authors.unresolved().is_empty(),
                "{name}: {:?}",
                authors.unresolved()
            );
            for id in &side.artifacts().execution_rewrite_order {
                assert!(authors.get(id).is_some(), "{name}: {id} has no provenance");
            }
            let mut counts = BTreeMap::<String, u64>::new();
            for (_, authorship) in authors.iter() {
                let key = match authorship {
                    Authorship::Sentences(sentences) => {
                        let kinds = sentences
                            .iter()
                            .map(|at| {
                                let sentence = side
                                    .definition()
                                    .modules
                                    .iter()
                                    .find(|candidate| candidate.name == at.module)
                                    .and_then(|module| {
                                        module.local_sentences.get(at.index as usize)
                                    })
                                    .expect("a resolved address names a sentence");
                                match &**sentence {
                                    Sentence::Rule { .. } => "rule",
                                    Sentence::Production { .. } => "production",
                                    Sentence::Claim { .. } => "claim",
                                    _ => "other",
                                }
                            })
                            .collect::<BTreeSet<_>>();
                        format!(
                            "{}:{}",
                            if sentences.len() == 1 { "one" } else { "many" },
                            kinds.into_iter().collect::<Vec<_>>().join("+")
                        )
                    }
                    Authorship::Unmapped(reason) => format!("unmapped:{reason}"),
                };
                *counts.entry(key.clone()).or_default() += 1;
                *totals.entry(key).or_default() += 1;
            }
            eprintln!("COVERAGE_MAP {}", json!({"file": name, "ids": counts}));
        }
        eprintln!("COVERAGE_MAP_TOTALS {}", json!(totals));
    });
}

/// A user `strict` production's heating and cooling rules have no written rule: their ids map
/// to the production's Compile address. A run that heats and cools covers them.
#[test]
fn strict_heating_and_cooling_ids_map_to_the_production() {
    with_stack(|| {
        let (validator, side) = compile("strictheat.k");
        let baseline = validator.baseline();
        let authors = RuleAuthors::of(&side);
        let production = baseline
            .authored_sentences()
            .find(|(_, sentence)| {
                matches!(sentence, Sentence::Production { .. })
                    && sentence.attributes().has(AttributeKey::Strict)
            })
            .map(|(at, _)| at)
            .expect("the strict add production");
        let generated = ids_of(&authors, &production);
        let run = runs(&side, "STRICTHEAT", "add", &strict_state());
        eprintln!(
            "COVERAGE_STRICT {}",
            json!({"production": {"module": production.module, "index": production.index},
                   "production_ids": generated, "coverage": run.observed.value()})
        );
        assert!(run.observed.complete);
        // A heating and a cooling rule for each of the two strict arguments.
        assert_eq!(generated.len(), 4);
        // `2` is already a result, so only the first argument heats and cools.
        assert_eq!(
            generated.intersection(&run.observed.rule_ids).count(),
            2,
            "the first argument's heating and cooling ids"
        );
        let add = support::rule(baseline, "STRICTHEAT.add");
        let inc = support::rule(baseline, "STRICTHEAT.inc");
        assert_eq!(
            run.observed.sentences,
            [production, add, inc].into_iter().collect()
        );
        assert_eq!(run.observed, run.unobserved);
        assert_eq!(Some(&run.observed), run.stepped.as_ref());
    });
}

fn bool_token(value: &str) -> Term {
    Term::Token {
        token: value.to_owned(),
        sort: KastSort::new("Bool"),
    }
}

/// An inserted sentence carries no protected identity or position attribute.
fn anonymous(sentence: &Sentence) -> Sentence {
    let mut clone = sentence.clone();
    for key in [
        AttributeKey::Label,
        AttributeKey::UniqueId,
        AttributeKey::Origin,
        AttributeKey::Location,
        AttributeKey::Source,
        AttributeKey::SourceId,
        AttributeKey::SentenceStartOffset,
        AttributeKey::SentenceEndOffset,
        AttributeKey::ContentStartLine,
        AttributeKey::ContentStartColumn,
        AttributeKey::ContentStartOffset,
    ] {
        clone.attributes_mut().remove(key.as_str());
    }
    clone
}

/// The baseline ids none of whose authors the patch writes, and the generated ids (no
/// author), are ids of the mutant with the same authors once its addresses are mapped back
/// through its origins (README 4.5's removed(m) premise); the written sentences' own ids are
/// gone; an inserted sentence with new content is `inserted`, one equal to a baseline
/// sentence joins that sentence's id.
#[test]
fn mutant_authors_map_back_to_the_baseline() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let base = RuleAuthors::of(&validator.compile_baseline().expect("baseline"));
        let increment = support::rule(baseline, "COUNTER.increment");
        let branch = support::rule(baseline, "COUNTER.branch");
        let fallback = support::rule(baseline, "COUNTER.fallback");
        let requires_false = {
            let at = TermRef::new(branch.clone(), [1]);
            Patch::new(vec![Edit::ReplaceTerm {
                expected: baseline.term(&at).expect("condition").clone(),
                at,
                replacement: bool_token("false"),
            }])
            .expect("patch")
        };
        let delete_fallback = Patch::new(vec![Edit::DeleteSentence {
            at: fallback.clone(),
        }])
        .expect("patch");
        let clone_increment = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::Before(increment.clone()),
            ordinal: 0,
            sentence: anonymous(baseline.sentence(&increment).expect("rule")),
        }])
        .expect("patch");
        let new_rule = {
            let mut sentence = anonymous(baseline.sentence(&branch).expect("rule"));
            if let Sentence::Rule { requires, .. } = &mut sentence {
                *requires = bool_token("false");
            }
            Patch::new(vec![Edit::InsertSentence {
                position: InsertPosition::ModuleStart("COUNTER".into()),
                ordinal: 0,
                sentence,
            }])
            .expect("patch")
        };
        for (name, patch) in [
            ("requires-false", &requires_false),
            ("delete-fallback", &delete_fallback),
            ("clone-increment", &clone_increment),
            ("insert-new-rule", &new_rule),
        ] {
            let mutant = validator.validate(patch).expect("the mutant compiles");
            let authors = RuleAuthors::of(&mutant);
            assert!(authors.unresolved().is_empty(), "{name}");
            let written = patch
                .written_sentences()
                .into_iter()
                .collect::<BTreeSet<_>>();
            for (id, authorship) in base.iter() {
                let unwritten = match authorship {
                    Authorship::Sentences(sentences) => sentences.is_disjoint(&written),
                    Authorship::Unmapped(_) => true,
                };
                if unwritten {
                    assert_eq!(authors.get(id), Some(authorship), "{name}: {id}");
                } else {
                    assert_eq!(authors.get(id), None, "{name}: written {id} is removed");
                }
            }
            let added = authors
                .iter()
                .filter(|(id, _)| base.get(id).is_none())
                .map(|(id, authorship)| (id.to_owned(), authorship.clone()))
                .collect::<Vec<_>>();
            match name {
                "requires-false" => {
                    assert_eq!(added.len(), 1, "{name}: {added:?}");
                    assert_eq!(
                        added[0].1,
                        Authorship::Sentences([branch.clone()].into_iter().collect())
                    );
                }
                "delete-fallback" => assert!(added.is_empty(), "{name}: {added:?}"),
                "clone-increment" => {
                    // Equal content: the clone joins increment's id and adds no author.
                    assert!(added.is_empty(), "{name}: {added:?}");
                }
                "insert-new-rule" => {
                    assert_eq!(added.len(), 1, "{name}: {added:?}");
                    assert_eq!(added[0].1, Authorship::Unmapped(UNMAPPED_INSERTED.into()));
                }
                _ => unreachable!(),
            }
        }
    });
}
