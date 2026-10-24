//! fz26 KINK-BASELINE-FINDINGS (finding KINK-BASELINE-TRUST): kink counts no kill on a definition
//! whose full critical-pair check has a finding the author has not named as a premise.
//!
//! The fixtures `testdata/flow/findings/*` are the seven DATAEND-review repros that a kink mutation
//! can express (copied from `probe-kinkflow-review/flows` on fz26/kinkflow-review 790a695de, their
//! `run.json` left out). Each mutation edits only the rewrite rule `go`, writing one constant where
//! the baseline writes another, and in each the two constants are equal in every model of the
//! definition (r3-plainq: `q(_) => a` and `q(_) => bb`, so `a = bb`). Before this ticket kink-flow
//! killed all seven through the whole-term slot, with no diagnostic; the fuzz refused all seven as
//! not comparable (three genuine findings, four undecided).
//!
//! - Each is `unknown` with reason `baseline-findings`, its findings named with their verdicts,
//!   `results` marks the comparable program unable to kill, and a query `no` is `unknown` while
//!   a hit stays a hit.
//! - With every finding named in `[spec] assume_joined` (the names `results` prints, which are
//!   k-rust-fuzz's names byte for byte: `NAMES` is pinned here and in k-rust-fuzz's
//!   `tests/kink_names.rs`), each is `killed` again.
//! - A name that names no finding refuses the specification (stage `assume-joined`).
//! - A tier-1 store that says `killed` (as a run before this ticket wrote it) decides nothing.

mod flow_support;

use flow_support::{copy_dir, flow};
use kink_corpus::Store;
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_flow::{
    FlowManifest, MutationList,
    admit::admit,
    digest::{execution_digest, mutation_identity, outcome_context},
    outcomes::{CachedOutcome, OutcomeRecord, OutcomeStore},
    pattern::PatternList,
    query::{QueryOptions, query},
    resolve,
    results::{ResultsOptions, results},
    search::{ProgramOrder, RunOptions, run},
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

/// The seven repros, each with the names of its findings (k-rust-backend
/// `data_term::names::finding_name`) and their verdicts. k-rust-fuzz's `tests/kink_names.rs`
/// pins the same names from the fuzz's `definition-findings`.
const NAMES: [(&str, &[(&str, &str)]); 7] = [
    (
        "diamond",
        &[
            (
                r#"overload:".List{\"_,__DIA-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__DIA-SYNTAX_Ids_Id2_Ids\"}_Ids",overload:".List{\"_,__DIA-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__DIA-SYNTAX_Vals_Val_Vals\"}_Vals"@root"#,
                "genuine",
            ),
            (
                r#"overload:"_,__DIA-SYNTAX_Exps_Exp_Exps":"_,__DIA-SYNTAX_Ids_Id2_Ids",overload:"_,__DIA-SYNTAX_Exps_Exp_Exps":"_,__DIA-SYNTAX_Vals_Val_Vals"@root"#,
                "genuine",
            ),
        ],
    ),
    (
        "r3-modov",
        &[
            ("spec.k:16:3,spec.k:17:3@root", "undecided"),
            (
                r#"spec.k:17:3,overload:"_,__MO-SYNTAX_Exps_Exp_Exps":"_,__MO-SYNTAX_Ids_Id_Ids"@0"#,
                "undecided",
            ),
        ],
    ),
    ("r3-plainq", &[("spec.k:7:3,spec.k:8:3@root", "genuine")]),
    (
        "r3-propagate",
        &[
            (
                r#"overload:".List{\"_,__PR-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__PR-SYNTAX_Ids_Id2_Ids\"}_Ids",overload:".List{\"_,__PR-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__PR-SYNTAX_Vals_Val_Vals\"}_Vals"@root"#,
                "genuine",
            ),
            (
                r#"overload:"_,__PR-SYNTAX_Exps_Exp_Exps":"_,__PR-SYNTAX_Ids_Id2_Ids",overload:"_,__PR-SYNTAX_Exps_Exp_Exps":"_,__PR-SYNTAX_Vals_Val_Vals"@root"#,
                "genuine",
            ),
        ],
    ),
    ("r4-empty", &[("spec.k:9:3,spec.k:10:3@root", "undecided")]),
    ("r4-hookite", &[("hook:spec.k:8:3", "undecided")]),
    (
        "r4-partnorule",
        &[("spec.k:9:3,spec.k:10:3@root", "undecided")],
    ),
];

fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-findings-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// A private copy of `findings/<name>`, with `assume_joined` added to its `[spec]` when given.
fn repro(name: &str, test: &str, assume_joined: Option<&[&str]>) -> PathBuf {
    let dir = scratch(test).join(name);
    copy_dir(&flow(&format!("findings/{name}")), &dir);
    if let Some(names) = assume_joined {
        let manifest = dir.join("FLOW.toml");
        let text = fs::read_to_string(&manifest).unwrap();
        let list = names
            .iter()
            .map(|name| format!("{name:?}"))
            .collect::<Vec<_>>()
            .join(", ");
        let text = text.replacen(
            "[spec]\n",
            &format!("[spec]\nassume_joined = [{list}]\n"),
            1,
        );
        fs::write(&manifest, text).unwrap();
    }
    dir
}

fn search(dir: &Path) -> (Value, bool) {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
    run(
        &manifest,
        &list,
        &RunOptions {
            only: Vec::new(),
            cache: None,
            order: ProgramOrder::Corpus,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
        },
    )
}

fn row(document: &Value) -> &Value {
    let rows = document["mutations"].as_array().unwrap();
    assert_eq!(rows.len(), 1, "{document:#}");
    &rows[0]
}

/// `(name, verdict)` of each finding of a findings list, as written.
fn named(findings: &Value) -> Vec<(String, String)> {
    findings
        .as_array()
        .unwrap_or_else(|| panic!("{findings:#}"))
        .iter()
        .map(|finding| {
            (
                finding["name"].as_str().unwrap().to_owned(),
                finding["verdict"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn expected(names: &[(&str, &str)]) -> Vec<(String, String)> {
    names
        .iter()
        .map(|(name, verdict)| ((*name).to_owned(), (*verdict).to_owned()))
        .collect()
}

fn on_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(DEFINITION_STACK_BYTES)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

mod kink_tier {
    use super::*;

    /// Fail at base: all seven were `killed` by `one`.
    #[test]
    #[ignore = "kink"]
    fn the_seven_repros_are_unknown_until_their_findings_are_named() {
        on_stack(|| {
            for (name, names) in NAMES {
                let dir = repro(name, "gate", None);
                let (document, ok) = search(&dir);
                assert!(ok, "{name}: {document:#}");
                let mutation = row(&document);
                assert_eq!(mutation["status"], "unknown", "{name}: {mutation:#}");
                assert_eq!(mutation["reason"], "baseline-findings", "{name}");
                assert_eq!(mutation["killer"], Value::Null, "{name}");
                assert_eq!(mutation["calls"], json!([]), "{name}: no call is made");
                assert_eq!(named(&mutation["findings"]), expected(names), "{name}");
                assert!(
                    mutation["action"]
                        .as_str()
                        .unwrap()
                        .contains("assume_joined"),
                    "{name}"
                );
                assert_eq!(document["data"]["has_data"], false, "{name}");
                assert_eq!(document["data"]["assume_joined"], json!([]), "{name}");
                assert_eq!(named(&document["data"]["findings"]), expected(names));
                let program = &document["programs"][0];
                assert_eq!(program["class"], "comparable", "{name}: {program:#}");
                assert_eq!(program["unable_to_kill"], "baseline-findings", "{name}");

                // `results` lists the findings and marks the comparable row.
                let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
                let (listed, ok) = results(&manifest, &ResultsOptions::default());
                assert!(ok, "{name}: {listed:#}");
                assert_eq!(named(&listed["data"]["findings"]), expected(names));
                assert_eq!(listed["programs"][0]["unable_to_kill"], "baseline-findings");

                // The names `results` prints, given back as premises, kill again.
                let printed = named(&listed["data"]["findings"])
                    .into_iter()
                    .map(|(name, _)| name)
                    .collect::<Vec<_>>();
                let premises = printed.iter().map(String::as_str).collect::<Vec<_>>();
                let dir = repro(name, "named", Some(&premises));
                let (document, ok) = search(&dir);
                assert!(ok, "{name}: {document:#}");
                let mutation = row(&document);
                assert_eq!(mutation["status"], "killed", "{name}: {mutation:#}");
                assert_eq!(mutation["killer"], "one", "{name}");
                assert_eq!(document["data"]["has_data"], true, "{name}");
                assert_eq!(document["data"]["assume_joined"], json!(printed));
                assert!(
                    document["data"]["findings"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .all(|finding| finding["assumed"] == true),
                    "{name}"
                );
                assert_eq!(document["programs"][0].get("unable_to_kill"), None);
            }
        });
    }

    /// The runner's own gate (kink-campaign, for every caller: kink-corpus's campaigns as well as
    /// kink-flow, which decides before it calls): every mutant of a baseline with a finding left
    /// is `BaselineFindings`, unknown, before it compiles; with the finding named through the
    /// session, the same mutant is killed.
    #[test]
    #[ignore = "kink"]
    fn the_runner_refuses_every_mutant_of_a_baseline_with_findings() {
        use kink_campaign::{
            BaselineSession, Campaign, CampaignOptions, MutantScopeFailure, MutantStatus,
            RunOptions, ScheduleMode, SelectionPolicy, TestCase, run_campaign_multi_with,
        };
        on_stack(|| {
            let dir = repro("r3-plainq", "runner", None);
            let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
            let admission = admit(&manifest);
            let spec = admission.spec.as_ref().unwrap();
            let test = admission.programs[0].outcome.clone().unwrap();
            let tests = [TestCase {
                oracles: kink_flow::results::fixed_oracles(),
                ..test
            }];
            let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
            let campaign = Campaign {
                validator: &spec.validator,
                module: &module,
                observation: &[],
                classify: &kink_corpus::runner::all_normal,
                tests: &tests,
                budget: kink_flow::results::execution_budget(manifest.budget),
            };
            let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
            let resolved = resolve(&manifest, &spec.loaded, &list.mutations[0]).unwrap();
            let generation = resolved.generation(spec.validator.baseline()).unwrap();
            let options = CampaignOptions {
                schedule: ScheduleMode::FirstKill,
                selection: SelectionPolicy::None,
                share_evidence: false,
                run: RunOptions::default(),
                compile_workers: 1,
            };
            for (names, status, failure) in [
                (
                    Vec::new(),
                    MutantStatus::Unknown,
                    Some(MutantScopeFailure::BaselineFindings),
                ),
                (
                    vec!["spec.k:7:3,spec.k:8:3@root".to_owned()],
                    MutantStatus::Killed,
                    None,
                ),
            ] {
                let mut session = BaselineSession::new(&spec.validator).assuming(names);
                let run = run_campaign_multi_with(
                    &campaign,
                    std::slice::from_ref(&generation),
                    &options,
                    &mut session,
                )
                .unwrap();
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant");
                };
                assert_eq!(mutant.report.status, status);
                assert_eq!(mutant.plan.mutant_failure, failure);
                assert_eq!(
                    session.baseline_data().map(|data| data.has_data()),
                    Some(failure.is_none())
                );
            }
        });
    }

    /// A name that names no finding, or a side-prefixed name (kink's list is about both
    /// definitions), refuses the specification at stage `assume-joined`.
    #[test]
    #[ignore = "kink"]
    fn a_name_that_names_no_finding_refuses_the_specification() {
        on_stack(|| {
            for premise in [
                "spec.k:1:1,spec.k:2:1@root",
                "baseline:spec.k:7:3,spec.k:8:3@root",
            ] {
                let dir = repro("r3-plainq", "unmatched", Some(&[premise]));
                let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
                let (document, ok) = results(&manifest, &ResultsOptions::default());
                assert!(!ok);
                assert_eq!(document["spec"]["outcome"], "refused", "{document:#}");
                assert_eq!(document["spec"]["stage"], "assume-joined");
                assert_eq!(document["spec"]["reason"], "name-refused");
                assert!(
                    document["spec"]["detail"]
                        .as_str()
                        .unwrap()
                        .contains("names no finding"),
                    "{document:#}"
                );
            }
        });
    }

    /// R2-B1's warm cache: a tier-1 record that says `killed`, under exactly the current context
    /// (as a run before this ticket, with the same build, wrote it), decides nothing on a
    /// baseline with findings left. Fail at base: the record decided `killed` with no call.
    #[test]
    #[ignore = "kink"]
    fn a_cached_kill_decides_nothing_on_a_baseline_with_findings() {
        on_stack(|| {
            let dir = repro("r3-plainq", "warm", None);
            let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
            let (listed, ok) = results(&manifest, &ResultsOptions::default());
            assert!(ok, "{listed:#}");
            let program = &listed["programs"][0];
            let cache = dir.join(kink_flow::results::CACHE_DIRECTORY);
            let admission = admit(&manifest);
            let spec = admission.spec.unwrap();
            let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
            let resolved = resolve(&manifest, &spec.loaded, &list.mutations[0]).unwrap();
            let identity = mutation_identity(&spec.loaded.baseline, &resolved.patch).unwrap();
            let Ok(build) = kink_campaign::kink_build() else {
                return;
            };
            let store = OutcomeStore::new(
                &cache,
                outcome_context(
                    build,
                    execution_digest(&manifest, &spec.loaded),
                    manifest.budget,
                ),
            );
            let record = OutcomeRecord {
                program_id: "one".into(),
                baseline_run_sha256: program_run_sha256(&cache, program),
                outcome: CachedOutcome::Killed,
                slots: vec![
                    kink_campaign::OracleOutcome::Agree,
                    kink_campaign::OracleOutcome::Distinguish,
                ],
                mutant_run_sha256: "0".repeat(64),
                allowance_bytes: None,
            };
            store
                .write(
                    &Store::new(&cache),
                    identity,
                    "store-changed",
                    &Value::Null,
                    &[(program["digest"].as_str().unwrap().to_owned(), record)],
                )
                .unwrap();
            let (document, ok) = search(&dir);
            assert!(ok, "{document:#}");
            let mutation = row(&document);
            assert_eq!(mutation["status"], "unknown", "{mutation:#}");
            assert_eq!(mutation["reason"], "baseline-findings");
            assert_eq!(document["outcome_cache"]["mutations_from_cache"], 0);
        });
    }

    /// A query `no` is `unknown` while a finding is left (matching is syntactic, the theory
    /// identifies terms); a hit stays a hit. With the finding named, the `no` is given (outside
    /// the Z3 profile, where no `no` is ever given).
    #[test]
    #[ignore = "kink"]
    fn a_query_no_is_unknown_on_a_baseline_with_findings_and_a_hit_stands() {
        on_stack(|| {
            for (premises, no) in [
                (None, "unknown"),
                (
                    Some(&["spec.k:7:3,spec.k:8:3@root"][..]),
                    if cfg!(feature = "z3") {
                        "unknown"
                    } else {
                        "no"
                    },
                ),
            ] {
                let dir = repro("r3-plainq", "query", premises);
                fs::write(
                    dir.join("PATTERNS.toml"),
                    "[[pattern]]\nid = \"stores-a\"\npattern = \"<s> a </s>\"\n\n\
                     [[pattern]]\nid = \"stores-bb\"\npattern = \"<s> bb </s>\"\n",
                )
                .unwrap();
                let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
                let patterns = PatternList::read(&dir.join("PATTERNS.toml")).unwrap();
                let (document, ok) = query(&manifest, &patterns, &QueryOptions::default());
                assert!(ok, "{document:#}");
                let answer = |pattern: &str| {
                    document["rows"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .find(|row| row["pattern"] == pattern)
                        .unwrap()
                        .clone()
                };
                assert_eq!(answer("stores-a")["answer"], "hit", "{document:#}");
                let bb = answer("stores-bb");
                assert_eq!(bb["answer"], no, "{premises:?}: {bb:#}");
                if premises.is_none() {
                    assert!(
                        bb["cause"].as_str().unwrap().contains("baseline-findings"),
                        "{bb:#}"
                    );
                }
            }
        });
    }
}

/// The `run_sha256` of a program's result record (the document's row names its digest).
fn program_run_sha256(cache: &Path, program: &Value) -> String {
    let digest = program["digest"].as_str().unwrap();
    let results = cache.join("results");
    for spec in fs::read_dir(&results).unwrap() {
        let path = spec.unwrap().path().join(format!("{digest}.json"));
        if let Ok(text) = fs::read_to_string(&path) {
            let record: Value = serde_json::from_str(&text).unwrap();
            return record["run_sha256"].as_str().unwrap().to_owned();
        }
    }
    panic!("no result record for {digest}")
}
