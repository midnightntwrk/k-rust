//! Where `krust fuzz` (k-rust-fuzz) and kink agree, and where they knowingly do not (fz26
//! FZ-KINK-XTEST): each test runs both tools on one small definition and pins both answers, so a
//! change in either judgement fails here instead of drifting silently. Every test runs kink, so
//! all of them are in the kink tier.
//!
//! Agreement, which both tools derive from the same semantics:
//! - (a) an added end on a mutant whose run never completes: the fuzz kills by the added end (the
//!   baseline's complete set of ends lacks a clean end of the mutant), and kink kills the same
//!   program one-sidedly (a work-bound mutant run whose explored part holds a clean, ground, stuck
//!   end outside the baseline's complete set);
//! - (b) a fuzz pattern hit, at `final` and at `any-state`, is a `hit` of kink's query on the
//!   witness program: a hit is a decided match of a reached configuration, and the query asks
//!   whether some reached configuration matches;
//! - (c) on the programs of k-rust-fuzz's `COMPARABLE_ENDS` (`tests/support/mod.rs`), a run the
//!   fuzz judges comparable is `comparable` in kink's `results`; and on those programs kink-flow's
//!   witness filter accepts a reach candidate exactly when kink's own confirmation lists it;
//! - (d) an undefined step is no end (finding KINK-UNDEFINED-END; kink's `README.md`, "What a kill
//!   trusts"): its configuration is reached, but its outcome is undefinedness, which is no
//!   configuration, and neither tool takes a verdict from undefinedness itself. So two definitions
//!   that both end undefined at different pre-step configurations are killed by neither tool, an
//!   undefined path beside the same ends is no difference, and a side whose every path takes an
//!   undefined step has the empty set of ends, which a clean end of the other side distinguishes.
//!   kink completes an undefined step whose configuration exists without being a value (kink27
//!   R3-UNDEF-BRIDGE); the fuzz's comparable conditions do not yet (known divergence below).
//!
//! Known divergences, pinned for the final first-principles review, not desired behaviour:
//! - cond(0): the fuzz holds no end of a definition with an unnamed critical-pair finding to be
//!   data, while kink's `results` classifies the run by its own end check and lists its coverage;
//! - a non-ASCII String end: k-rust's data judgement accepts it and kink's end check does not; the
//!   witness filter closes the gap inside a kink-flow campaign, the library judgement keeps it;
//! - an undefined step taken from a configuration that exists but is not data (an irreducible
//!   application of a total function): kink's `results` judges the run `comparable` (kink27
//!   R3-UNDEF-BRIDGE), while the fuzz's comparable conditions (k-rust-fuzz `end_conditions`, P3)
//!   still require an undefined step's term to be data (`end-not-data`). The fuzz is the stricter,
//!   so (c)'s direction (fuzz comparable, then kink comparable) still holds.
//!
//! The kill job's agreement of the filter and kink's confirmation on a non-ASCII end is pinned in
//! `tests/fuzz.rs` (`a_witness_kink_refuses_is_unconfirmed_with_kinks_cause`, and `comparable_b`
//! for String holes); this file adds the reach job.
//!
//! Every flow is written under `CARGO_TARGET_TMPDIR`; the `COMPARABLE_ENDS` definitions are read
//! from `crates/k-rust-fuzz/tests/data`, so both tools judge the same sources.

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl, PathMode,
    ProgramInput, ProposerConfig, Target, TargetKind,
    spec::{DEFAULT_REJECTION_CAP, ProgramSource as FuzzProgram, ProgramText},
    target::{PatternAt, PatternTarget},
    values::GenerationBounds,
};
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_flow::{
    FlowManifest, MutationList, admit_spec,
    fuzz::{FuzzJob, FuzzOptions, TemplateList, compiled_side, fuzz_job},
    memo::MemoUse,
    pattern::PatternList,
    query::{QueryOptions, query},
    results::{ResultsOptions, results},
    search::{ProgramOrder, RunOptions, run},
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// A file of k-rust-fuzz's test data.
fn fuzz_data(file: &str) -> String {
    fs::read_to_string(
        repository()
            .join("../crates/k-rust-fuzz/tests/data")
            .join(file),
    )
    .unwrap()
}

fn on_stack<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(DEFINITION_STACK_BYTES)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap()
}

/// A fresh directory under the test target's scratch space.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-fuzz-parity-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// The `FLOW.toml` text of `entry` (main module `main`, syntax module `{main}-SYNTAX`) with the
/// `[budget]` lines `budget` (none when empty) and the programs `(id, text)`.
fn manifest_text(entry: &str, main: &str, budget: &str, programs: &[(&str, &str)]) -> String {
    let mut text = format!(
        "[spec]\nentry = \"{entry}\"\nmain_module = \"{main}\"\nsyntax_module = \
         \"{main}-SYNTAX\"\n"
    );
    if !budget.is_empty() {
        text.push_str(&format!("\n[budget]\n{budget}"));
    }
    for (id, program) in programs {
        text.push_str(&format!(
            "\n[[program]]\nid = \"{id}\"\ntext = '''{program}'''\n"
        ));
    }
    text
}

/// A flow in a scratch directory: `spec` as `entry`, its manifest and its mutation list.
fn flow(
    name: &str,
    entry: &str,
    spec: &str,
    main: &str,
    budget: &str,
    programs: &[(&str, &str)],
    mutations: &str,
) -> PathBuf {
    let dir = scratch(name);
    fs::write(dir.join(entry), spec).unwrap();
    fs::write(
        dir.join("FLOW.toml"),
        manifest_text(entry, main, budget, programs),
    )
    .unwrap();
    fs::write(dir.join("MUTATIONS.toml"), mutations).unwrap();
    dir
}

/// kink's `results` on the flow in `dir`, with a cache inside it.
fn kink_results(dir: &Path) -> Value {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let cache = dir.join("cache");
    let (document, ok) = on_stack(move || {
        results(
            &manifest,
            &ResultsOptions {
                cache: Some(cache),
                ..ResultsOptions::default()
            },
        )
    });
    assert!(ok, "{document:#}");
    document
}

/// The row of program `id` in a `results` document.
fn row<'a>(document: &'a Value, id: &str) -> &'a Value {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("{id}: {document:#}"))
}

/// kink's `run` of the mutation `only` on the flow in `dir`: the mutation's entry.
fn kink_run(dir: &Path, only: &str) -> Value {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
    let options = RunOptions {
        only: vec![only.to_owned()],
        cache: Some(dir.join("cache")),
        order: ProgramOrder::Corpus,
        compile_workers: None,
        memo: MemoUse::On,
    };
    let (document, ok) = on_stack(move || run(&manifest, &list, &options));
    assert!(ok, "{document:#}");
    document["mutations"][0].clone()
}

/// kink's `query` of `pattern`, claimed for the program `program` of the flow in `dir`: the
/// program's row.
fn kink_query(dir: &Path, pattern: &str, program: &str) -> Value {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let list = PatternList::decode(&format!(
        "[[pattern]]\nid = \"p\"\npattern = '''{pattern}'''\nprograms = [\"{program}\"]\n"
    ))
    .unwrap();
    let cache = dir.join("cache");
    let (document, _) = on_stack(move || {
        query(
            &manifest,
            &list,
            &QueryOptions {
                cache: Some(cache),
                ..QueryOptions::default()
            },
        )
    });
    document["rows"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["program"] == program)
        .unwrap_or_else(|| panic!("{program}: {document:#}"))
        .clone()
}

/// A `krust fuzz` campaign, the library alone (no kink judgement, no filter), on kink's compiled
/// baseline of the flow in `dir`, converted as kink-flow converts it: the program `text` named
/// `name` (start sort `Pgm`) with `holes`, a pattern target `at` with data ends and neither
/// option, all paths, the flow's `max_depth` and clock, `max_work` 20000. The report as JSON.
fn krust_fuzz(
    dir: &Path,
    name: &str,
    text: &str,
    holes: Vec<HoleDecl>,
    pattern: &str,
    at: PatternAt,
    cases: u64,
) -> Value {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let (name, text, pattern) = (name.to_owned(), text.to_owned(), pattern.to_owned());
    on_stack(move || {
        let (_, admitted) = admit_spec(&manifest);
        let (spec, _) = admitted.expect("kink admits the specification");
        let baseline = compiled_side(&manifest, &spec, &spec.compiled).unwrap();
        let campaign = CampaignSpec {
            definitions: Definitions {
                baseline: Arc::new(baseline),
                mutant: None,
            },
            program: ProgramInput::Source(FuzzProgram {
                program: Some(ProgramText {
                    name,
                    text,
                    start_sort: "Pgm".into(),
                }),
                config_vars: Vec::new(),
            }),
            holes,
            target: Target {
                kind: TargetKind::Pattern(PatternTarget { pattern, at }),
                run_to_completion: false,
                negated_property: false,
                data_end: true,
                comparable: false,
                query_confirmable: false,
            },
            options: CaseOptions {
                paths: PathMode::AllPaths,
                max_depth: Some(manifest.budget.max_depth),
                max_work: Some(20_000),
                safety_limit_ms: Some(manifest.budget.time_ms),
                ..CaseOptions::default()
            },
            proposers: ProposerConfig::default(),
            bounds: GenerationBounds::default(),
            rejection_cap: DEFAULT_REJECTION_CAP,
            seed: 0,
            identity: CallerIdentity {
                k_rust_revision: "fz26-kink-xtest".into(),
                thread_stack_size: None,
            },
        };
        let report = Campaign::new(campaign)
            .expect("the campaign is valid")
            .run(Budget::Cases(cases), None);
        assert!(
            report.engine_defects.is_empty(),
            "{:?}",
            report.engine_defects
        );
        serde_json::from_str(&report.to_canonical_json()).unwrap()
    })
}

/// The witness case of a report: the shrunk case, else the first.
fn witness(report: &Value) -> &Value {
    assert_eq!(report["outcome"]["status"], "witness-found", "{report:#}");
    let witness = &report["outcome"]["witness"];
    if witness["shrunk"].is_object() {
        &witness["shrunk"]
    } else {
        &witness["first"]
    }
}

/// A `kink-flow fuzz` job: the mutation, the rule, or the pattern's text.
#[derive(Clone, Copy)]
enum Job {
    Kill(&'static str),
    Reach(&'static str),
    Pattern(&'static str),
}

/// The `kink-flow fuzz` job on the flow in `dir` with `templates` (decoded in `dir`).
fn kink_flow_fuzz(
    dir: &Path,
    templates: &str,
    template: &str,
    job: Job,
    options: FuzzOptions,
) -> (Value, bool) {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let templates = TemplateList::decode(templates, dir).unwrap();
    let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
    let template = template.to_owned();
    on_stack(move || {
        let patterns;
        let job = match job {
            Job::Kill(mutation) => FuzzJob::Kill {
                list: &list,
                mutation,
            },
            Job::Reach(rule) => FuzzJob::Reach { rule, fired: false },
            Job::Pattern(pattern) => {
                patterns = PatternList::decode(&format!(
                    "[[pattern]]\nid = \"p\"\npattern = '''{pattern}'''\n"
                ))
                .unwrap();
                FuzzJob::Pattern {
                    list: &patterns,
                    id: "p",
                }
            }
        };
        fuzz_job(&manifest, &templates, &template, job, &options)
    })
}

fn options(cases: u64, confirm: bool, filter: bool) -> FuzzOptions {
    FuzzOptions {
        budget: Budget::Cases(cases),
        max_work: Some(20_000),
        confirm,
        filter,
        ..FuzzOptions::default()
    }
}

fn totals(document: &Value) -> &Value {
    &document["attempts"][0]["fuzz"]["totals"]
}

/// One `Int` hole `N` over 0 to 5 at the literal `1` of the flow's program `one`.
const HOLE_TEMPLATE: &str = "[[template]]\nid = \"h\"\nprogram = \"one\"\n[[template.hole]]\n\
                             name = \"N\"\nsort = \"Int\"\nfind = \"1\"\nliteral = \"1\"\n\
                             range = { min = 0, max = 5 }\n";

/// A template of the flow's program `id`, with no hole.
fn plain_template(id: &str) -> String {
    format!("[[template]]\nid = \"t\"\nprogram = \"{id}\"\n")
}

mod kink_tier {
    use super::*;

    // -----------------------------------------------------------------------------------------
    // (a) An added end of a mutant whose run never completes
    // -----------------------------------------------------------------------------------------

    /// `a(N)` reaches `done(N)` on two paths. `g` is unreachable in the baseline: `g(X)` ends in
    /// `done(X +Int 1)` or enters `spin`, which steps to itself forever.
    const ONE_SIDED_K: &str = "module OSA-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= a(Int) [symbol(a)]
endmodule

module OSA
  imports OSA-SYNTAX
  imports INT
  syntax KItem ::= e(Int) [symbol(e)] | f(Int) [symbol(f)] | g(Int) [symbol(g)]
                 | done(Int) [symbol(done)] | \"spin\" [symbol(spin)]
  configuration <k> $PGM:Pgm </k>
  rule [start]:  <k> a(N) => e(N) </k>
  rule [e-done]: <k> e(X) => done(X) </k>
  rule [e-f]:    <k> e(X) => f(X) </k>
  rule [f-done]: <k> f(X) => done(X) </k>
  rule [g-done]: <k> g(X) => done(X +Int 1) </k>
  rule [g-spin]: <k> g(_) => spin </k>
  rule [spin]:   <k> spin => spin </k>
endmodule
";

    /// `f(X)` steps to `g(X)`: the mutant adds the end `done(N +Int 1)`, and its run never
    /// completes (a state set merges the configurations reached at one depth, so `spin`'s cycle
    /// is not cut short).
    const ONE_SIDED_MUTATIONS: &str = "[[mutation]]\nid = \"f-to-g\"\n[[mutation.edit]]\nrule = \
                                       \"OSA.f-done\"\nfind = \"done(X)\"\nreplace = \"g(X)\"\n";

    /// (a) The fuzz kills by an added end, which needs the baseline's complete set of ends and a
    /// clean stuck mutant end outside it, not a complete mutant run: the mutant's run is cut by
    /// its work bound. kink kills the same program one-sidedly: the mutant's run ends at kink's
    /// work budget (`work_factor = 4`) and its explored part holds a clean, ground, stuck end the
    /// baseline's complete set lacks, so the whole-term slot distinguishes with no mutant value
    /// and the exit stop slot is unknown. T4's confirmation of the fuzz candidate is that kill.
    ///
    /// Fails if the fuzz requires a complete mutant run for an added end (no witness), or if
    /// kink-flow stops judging a work-bound mutant run one-sidedly (the confirmation is not
    /// `killed`, the slots are `unknown`).
    #[test]
    #[ignore = "kink"]
    fn an_added_end_of_a_mutant_that_never_completes_is_killed_by_both() {
        let dir = flow(
            "one-sided",
            "osa.k",
            ONE_SIDED_K,
            "OSA",
            "work_factor = 4\n",
            &[("one", "a(1)")],
            ONE_SIDED_MUTATIONS,
        );
        let (document, ok) = kink_flow_fuzz(
            &dir,
            HOLE_TEMPLATE,
            "h",
            Job::Kill("f-to-g"),
            options(20, true, true),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        let candidate = &document["attempts"][0]["candidate"];
        assert_eq!(candidate["kill"], "added-end", "{candidate:#}");
        let mutant = &candidate["sides"][1];
        assert_eq!(mutant["role"], "mutant");
        assert!(
            mutant["halts"]
                .as_array()
                .unwrap()
                .iter()
                .any(|halt| halt == "work-bound"),
            "the mutant's run is cut: {mutant:#}"
        );
        let confirmation = &document["attempts"][0]["confirmation"];
        assert_eq!(confirmation["status"], "killed", "{confirmation:#}");
        assert_eq!(confirmation["killer"], document["program"]["id"]);

        // kink's own run with the fragment as the only program: a one-sided kill.
        let id = document["program"]["id"].as_str().unwrap();
        let fragment = document["program"]["fragment"].as_str().unwrap();
        let mut manifest = manifest_text("osa.k", "OSA", "work_factor = 4\n", &[]);
        manifest.push('\n');
        manifest.push_str(fragment);
        fs::write(dir.join("FLOW.toml"), manifest).unwrap();
        let mutation = kink_run(&dir, "f-to-g");
        assert_eq!(mutation["status"], "killed", "{mutation:#}");
        assert_eq!(mutation["killer"], id);
        let executed = &mutation["executed"][0];
        assert_eq!(
            executed["slots"],
            json!({
                "exit-stop": {"outcome": "unknown"},
                "whole-term": {"outcome": "distinguish", "sides": null},
            }),
            "{executed:#}"
        );
    }

    // -----------------------------------------------------------------------------------------
    // (b) A fuzz pattern hit is a query hit
    // -----------------------------------------------------------------------------------------

    /// (b) A fuzz pattern hit is a decided, clean match of a configuration the program's run
    /// reaches (at `final`, a final one); kink's query asks whether some configuration reached
    /// from the program's input matches, so the witness program is a `hit`, never a `no`. Both
    /// targets run on COIN's `flip(N)` with `<out> 3 </out>` (two paths, which end with N and
    /// N + 1) and on IMP's `primes-holes` template (`testdata/flow/fuzz/imp`) with
    /// `<k> _:Int / 0 ~> _ </k>` (a division by zero is stuck). `final` is the library's target,
    /// since kink-flow's pattern job matches at any state; `any-state` is kink-flow's pattern job,
    /// run without confirmation, so the query here is the only confirmation.
    ///
    /// Fails if the fuzz accepts a match kink's query does not (an undecided or diagnosed match, a
    /// state kink does not hold defined), or if the query stops finding a match a run reaches.
    #[test]
    #[ignore = "kink"]
    fn a_fuzz_pattern_hit_is_a_kink_query_hit() {
        let coin = flow(
            "pattern-coin",
            "coin.k",
            &fuzz_data("coin/coin.k"),
            "COIN",
            "",
            &[("one", "flip(1)")],
            "",
        );
        let source = repository().join("testdata/flow/fuzz/imp");
        let primes = fs::read_to_string(source.join("programs/primes.imp")).unwrap();
        let imp = flow(
            "pattern-imp",
            "imp.k",
            &fs::read_to_string(source.join("imp.k")).unwrap(),
            "IMP",
            "time_ms = 10000\nmax_depth = 100000\nwork_factor = 4\n",
            &[("primes", &primes)],
            "",
        );
        let imp_templates = fs::read_to_string(source.join("TEMPLATES.toml")).unwrap();
        let holes = |dir: &Path, templates: &str, id: &str| {
            TemplateList::decode(templates, dir)
                .unwrap()
                .get(id)
                .unwrap()
                .holes
                .clone()
        };
        for (dir, templates, template, text, pattern) in [
            (&coin, HOLE_TEMPLATE, "h", "flip(1)", "<out> 3 </out>"),
            (
                &imp,
                imp_templates.as_str(),
                "primes-holes",
                primes.as_str(),
                "<k> _:Int / 0 ~> _ </k>",
            ),
        ] {
            // At `final`: the library.
            let report = krust_fuzz(
                dir,
                template,
                text,
                holes(dir, templates, template),
                pattern,
                PatternAt::Final,
                300,
            );
            let at_final = witness(&report)["program"].as_str().unwrap().to_owned();
            // At `any-state`: kink-flow's pattern job.
            let (document, ok) = kink_flow_fuzz(
                dir,
                templates,
                template,
                Job::Pattern(pattern),
                options(300, false, true),
            );
            assert!(ok, "{document:#}");
            assert_eq!(document["stopped"], Value::Null, "{document:#}");
            let at_any_state = document["attempts"][0]["candidate"]["program"]
                .as_str()
                .unwrap()
                .to_owned();
            let manifest = fs::read_to_string(dir.join("FLOW.toml")).unwrap();
            for (at, witness) in [("final", at_final), ("any-state", at_any_state)] {
                fs::write(
                    dir.join("FLOW.toml"),
                    format!("{manifest}\n[[program]]\nid = \"witness\"\ntext = '''{witness}'''\n"),
                )
                .unwrap();
                let answer = kink_query(dir, pattern, "witness");
                assert_eq!(
                    (&answer["answer"], &answer["claim"]),
                    (&json!("hit"), &json!("confirmed")),
                    "{pattern} at {at} on {witness}: {answer:#}"
                );
            }
        }
    }

    // -----------------------------------------------------------------------------------------
    // (c) Comparable runs
    // -----------------------------------------------------------------------------------------

    /// One program of k-rust-fuzz's `COMPARABLE_ENDS`, with both judgements of its all-paths run.
    struct End {
        /// The program's id in its fixture's flow.
        id: &'static str,
        text: &'static str,
        /// A pattern a clean end of one path matches (the `COMPARABLE_ENDS` entry's).
        pattern: &'static str,
        /// The fuzz's judgement: `comparable.reasons`, empty when it holds.
        fuzz: &'static [&'static str],
        /// kink's `results` class.
        kink: &'static str,
    }

    /// The `COMPARABLE_ENDS` fixtures: `(file, main module, programs)`.
    const ENDS: [(&str, &str, &[End]); 5] = [
        (
            "imp/imp.k",
            "IMP",
            &[End {
                id: "le",
                text: "int x, y, r;\nx = 3;\ny = 5;\nif (x <= y) { r = 1; } else { r = 0; }\n",
                pattern: "<k> .K </k>",
                fuzz: &[],
                kink: "comparable",
            }],
        ),
        (
            "coin/coin.k",
            "COIN",
            &[End {
                id: "flip",
                text: "flip(3)",
                pattern: "<out> 3 </out>",
                fuzz: &[],
                kink: "comparable",
            }],
        ),
        (
            "comparable/comparable.k",
            "COMPARABLE",
            &[
                End {
                    id: "stay-zero",
                    text: "stay(0)",
                    pattern: "<out> 1 </out>",
                    fuzz: &[],
                    kink: "comparable",
                },
                // The fuzz's run is cut by `max_work`, kink's (no work budget) by `max_depth`.
                End {
                    id: "start",
                    text: "start(5)",
                    pattern: "<out> 5 </out>",
                    fuzz: &["work-bound"],
                    kink: "unknown",
                },
                // `g(3)` is no data for the fuzz and no value for kink's end check.
                End {
                    id: "stay",
                    text: "stay(3)",
                    pattern: "<k> .K </k>",
                    fuzz: &["end-not-data"],
                    kink: "unknown",
                },
            ],
        ),
        (
            "comparable/cond.k",
            "COMPARABLE-COND",
            &[
                End {
                    id: "cond",
                    text: "cond(3)",
                    pattern: "<k> .K </k>",
                    fuzz: &["undecided-condition", "end-not-data"],
                    kink: "unknown",
                },
                End {
                    id: "both",
                    text: "both(3)",
                    pattern: "<out> 3 </out>",
                    fuzz: &["undecided-condition", "end-not-data"],
                    kink: "unknown",
                },
                // Known divergence (`known_divergence_kink_lists_cond_zero_which_the_fuzz_refuses`):
                // the fuzz holds no end of this definition to be data, kink compares the end `1`.
                End {
                    id: "cond-zero",
                    text: "cond(0)",
                    pattern: "<out> 1 </out>",
                    fuzz: &["end-not-data"],
                    kink: "comparable",
                },
            ],
        ),
        (
            "loadclaim/loadclaim.k",
            "LOADCLAIM",
            &[End {
                id: "go",
                text: "go(7)",
                pattern: "<out> 0 </out>",
                fuzz: &["contradicted-claim"],
                kink: "unknown",
            }],
        ),
    ];

    /// (c) On every program of `COMPARABLE_ENDS`, the fuzz's judgement of its all-paths run (the
    /// `comparable` of a pattern witness, by the library alone) and kink's `results` class, both
    /// on kink's compile of the same source. The fuzz reads the k-rust facts kink's comparability
    /// rests on (completeness, diagnostics, contradicted claims) and judges each end by k-rust's
    /// data judgement, so where it holds kink's class is `comparable`; the converse fails only at
    /// cond(0), a pinned divergence. This is R2-REFRESH's measurement M4, re-taken after round 3,
    /// with IMP's `le` added.
    ///
    /// Fails on any change of either column (a fuzz condition added, dropped or reordered, a kink
    /// class moved), and the implication fails first if the fuzz judges comparable a run kink does
    /// not (the fuzz would then offer reach witnesses kink does not list).
    #[test]
    #[ignore = "kink"]
    fn a_run_the_fuzz_judges_comparable_is_comparable_in_kinks_results() {
        let mut measured = Vec::new();
        for (file, main, ends) in ENDS {
            let entry = Path::new(file).file_name().unwrap().to_str().unwrap();
            let programs = ends
                .iter()
                .map(|end| (end.id, end.text))
                .collect::<Vec<_>>();
            let dir = flow(main, entry, &fuzz_data(file), main, "", &programs, "");
            let document = kink_results(&dir);
            for end in ends {
                let report = krust_fuzz(
                    &dir,
                    "t",
                    end.text,
                    Vec::new(),
                    end.pattern,
                    PatternAt::Final,
                    1,
                );
                let comparable = witness(&report)["comparable"].clone();
                let class = row(&document, end.id)["class"].clone();
                if comparable["holds"] == true {
                    assert_eq!(
                        class, "comparable",
                        "{}: the fuzz holds, kink does not",
                        end.id
                    );
                }
                measured.push((end.id, comparable, class));
            }
        }
        let expected = ENDS
            .iter()
            .flat_map(|(_, _, ends)| ends.iter())
            .map(|end| {
                (
                    end.id,
                    json!({"holds": end.fuzz.is_empty(), "reasons": end.fuzz}),
                    json!(end.kink),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(measured, expected);
    }

    /// (c) The witness filter agrees with kink's confirmation on the reach candidates of the
    /// comparable `COMPARABLE_ENDS` programs: the fuzz judges the run comparable, the filter
    /// accepts it, and kink's `results` (T4's confirmation) lists it, comparable, for the rule.
    /// The programs the fuzz judges not comparable give no candidate (the reach target requires a
    /// comparable run), so the filter never judges them, and `cond.k` is refused before any case
    /// (`known_divergence_kink_lists_cond_zero_which_the_fuzz_refuses`).
    ///
    /// Fails if the filter refuses a run kink compares (its end check or exclusion reading drifts
    /// from kink's runner), or if kink stops listing the run.
    #[test]
    #[ignore = "kink"]
    fn the_witness_filter_accepts_the_reach_candidates_kink_confirms() {
        for (file, main, id, rule) in [
            ("imp/imp.k", "IMP", "le", "IMP.if-true"),
            ("coin/coin.k", "COIN", "flip", "COIN.heads"),
            (
                "comparable/comparable.k",
                "COMPARABLE",
                "stay-zero",
                "COMPARABLE.stay",
            ),
        ] {
            let end = ENDS
                .iter()
                .flat_map(|(_, _, ends)| ends.iter())
                .find(|end| end.id == id)
                .unwrap();
            let entry = Path::new(file).file_name().unwrap().to_str().unwrap();
            let dir = flow(
                &format!("reach-{id}"),
                entry,
                &fuzz_data(file),
                main,
                "",
                &[(id, end.text)],
                "",
            );
            let (document, ok) = kink_flow_fuzz(
                &dir,
                &plain_template(id),
                "t",
                Job::Reach(rule),
                options(1, true, true),
            );
            assert!(ok, "{id}: {document:#}");
            assert_eq!(document["stopped"], Value::Null, "{id}: {document:#}");
            let attempt = &document["attempts"][0];
            assert_eq!(attempt["candidate"]["comparable"]["holds"], true, "{id}");
            assert_eq!(
                totals(&document)["filter"],
                Value::Null,
                "{id}: nothing refused"
            );
            let confirmation = &attempt["confirmation"];
            assert_eq!(
                (&confirmation["status"], &confirmation["class"]),
                (&json!("reached"), &json!("comparable")),
                "{id}: {confirmation:#}"
            );
        }
    }

    /// Known divergence (R2-REFRESH decision 4, kept strict by D33): `cond.k`'s equation `f-some`
    /// leaves its result variable unbound, a decided critical-pair finding, so the fuzz holds no
    /// end of the definition to be data and refuses every campaign that reads data ends before any
    /// case (`not-comparable`); a decided finding cannot be named. kink's `results` classifies
    /// `cond(0)` by its own end check, which accepts the end `1`, and lists it in the `cond`
    /// rule's `reached_by`, although a kill on the definition needs the finding named
    /// (`baseline-findings`). So the reach job refuses a program kink lists.
    ///
    /// Fails if kink's `results` starts reading the definition's data facts (cond(0) no longer
    /// comparable or listed), or if the fuzz judges ends of a definition with a decided finding.
    #[test]
    #[ignore = "kink"]
    fn known_divergence_kink_lists_cond_zero_which_the_fuzz_refuses() {
        let dir = flow(
            "cond-zero",
            "cond.k",
            &fuzz_data("comparable/cond.k"),
            "COMPARABLE-COND",
            "",
            &[("cond-zero", "cond(0)")],
            "",
        );
        let document = kink_results(&dir);
        // kink's own data facts say the definition has no data; its class does not read them.
        assert_eq!(
            document["data"]["has_data"], false,
            "{:#}",
            document["data"]
        );
        assert_eq!(row(&document, "cond-zero")["class"], "comparable");
        let cond = document["rules"]
            .as_array()
            .unwrap()
            .iter()
            .find(|rule| rule["label"] == "COMPARABLE-COND.cond")
            .unwrap_or_else(|| panic!("{document:#}"));
        assert_eq!(cond["reached_by"], json!(["cond-zero"]), "{cond:#}");
        let (reach, ok) = kink_flow_fuzz(
            &dir,
            &plain_template("cond-zero"),
            "t",
            Job::Reach("COMPARABLE-COND.cond"),
            options(1, true, true),
        );
        assert!(!ok);
        assert_eq!(reach["stopped"], "not-comparable", "{reach:#}");
        let findings = reach["findings"].as_array().unwrap();
        assert_eq!(findings.len(), 1, "{findings:#?}");
        assert_eq!(findings[0]["verdict"], "decided");
    }

    /// R2-REFRESH's probe M2: every end holds a non-ASCII string.
    const NON_ASCII_K: &str = "module NA-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module NA
  imports NA-SYNTAX
  imports INT
  imports STRING
  configuration <k> $PGM:Pgm </k> <out> \"\" </out>
  rule [go]: <k> go(I) => .K </k> <out> _ => \"\u{e9}\" +String Int2String(I) </out>
endmodule
";

    /// Known divergence, closed inside a kink-flow campaign since FZ-COMPARABLE-B: k-rust's data
    /// judgement accepts every String domain value, so the library judges the run comparable;
    /// kink's end check gives a String a value only when it is ASCII, so the class is `unknown`
    /// for the domain value. kink-flow's witness filter applies kink's end check to every
    /// candidate, so the reach job refuses each case inside the campaign
    /// (`domain-value-not-ascii`; the hole is an integer, so no repair applies) and stops
    /// `client-refused`; without the filter the candidate reaches kink's confirmation, which
    /// refuses it for the same domain value. The kill job's agreement is pinned in `tests/fuzz.rs`
    /// (`a_witness_kink_refuses_is_unconfirmed_with_kinks_cause`).
    ///
    /// Fails if the library's data judgement starts refusing non-ASCII strings (the fuzz column),
    /// if kink's end check accepts them (the class), or if the filter and kink's confirmation stop
    /// agreeing on the case.
    #[test]
    #[ignore = "kink"]
    fn known_divergence_a_non_ascii_end_is_data_for_the_fuzz_and_no_value_for_kink() {
        let dir = flow(
            "non-ascii",
            "na.k",
            NON_ASCII_K,
            "NA",
            "",
            &[("one", "go(1)")],
            "",
        );
        let report = krust_fuzz(
            &dir,
            "t",
            "go(1)",
            Vec::new(),
            "<k> .K </k>",
            PatternAt::Final,
            1,
        );
        assert_eq!(
            witness(&report)["comparable"],
            json!({"holds": true, "reasons": []})
        );
        let document = kink_results(&dir);
        let one = row(&document, "one");
        assert_eq!(one["class"], "unknown");
        assert!(
            one["cause"].as_str().unwrap().contains("a domain value"),
            "{one:#}"
        );

        let reach = |filter| {
            kink_flow_fuzz(
                &dir,
                HOLE_TEMPLATE,
                "h",
                Job::Reach("NA.go"),
                options(6, true, filter),
            )
        };
        let (filtered, ok) = reach(true);
        assert!(ok, "{filtered:#}");
        assert_eq!(filtered["stopped"], "client-refused", "{filtered:#}");
        assert_eq!(
            totals(&filtered)["filter"],
            json!({"refused": {"domain-value-not-ascii": 6}}),
            "{filtered:#}"
        );
        let (unfiltered, ok) = reach(false);
        assert!(ok, "{unfiltered:#}");
        assert_eq!(unfiltered["stopped"], "unconfirmed", "{unfiltered:#}");
        let attempt = &unfiltered["attempts"][0];
        assert_eq!(attempt["candidate"]["comparable"]["holds"], true);
        let confirmation = &attempt["confirmation"];
        assert_eq!(
            (&confirmation["status"], &confirmation["class"]),
            (&json!("unreached"), &json!("unknown")),
            "{confirmation:#}"
        );
        assert!(
            confirmation["cause"]
                .as_str()
                .unwrap()
                .contains("a domain value"),
            "{confirmation:#}"
        );
    }

    // -----------------------------------------------------------------------------------------
    // (d) An undefined step is no end
    // -----------------------------------------------------------------------------------------

    /// `go(N)` writes `0` to `<log>` and steps to `step(N)`, whose one rule writes `N /Int 0`: an
    /// undefined step from every input.
    const UNDEFINED_K: &str = "module UE-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module UE
  imports UE-SYNTAX
  imports INT
  syntax KItem ::= step(Int) [symbol(step)]
  configuration <k> $PGM:Pgm </k> <log> 0 </log> <out> 0 </out>
  rule [go]:   <k> go(N) => step(N) </k> <log> _ => 0 </log>
  rule [step]: <k> step(N) => .K </k> <out> _ => N /Int 0 </out>
endmodule
";

    /// `log-one` writes `1` to `<log>`: it ends undefined too, at another pre-step configuration.
    /// `out-defined` writes `N` to `<out>`: its step is defined, and every run ends cleanly.
    const UNDEFINED_MUTATIONS: &str = "[[mutation]]\nid = \"log-one\"\n[[mutation.edit]]\nrule = \
                                       \"UE.go\"\nfind = \"_ => 0\"\nreplace = \"_ => \
                                       1\"\n\n[[mutation]]\nid = \"out-defined\"\n\
                                       [[mutation.edit]]\nrule = \"UE.step\"\nfind = \"N /Int \
                                       0\"\nreplace = \"N\"\n";

    /// (d) An undefined step is no end, for both tools (finding KINK-UNDEFINED-END; kink's
    /// `README.md`, "What a kill trusts"): the configuration the step is taken from is reached,
    /// but the step's outcome is undefinedness, which is no configuration. The baseline ends every
    /// run in an undefined step, so its set of ends is empty, and both tools judge the run
    /// comparable (complete, every leaf a clean end or an undefined step).
    /// - `log-one` ends every run undefined too, at pre-step configurations that differ in
    ///   `<log>`: both sets of ends are empty, the fuzz finds no witness among the six inputs of the
    ///   hole's domain, and kink's slots agree (both exit stops and both whole terms are the empty
    ///   set), so the mutation survives.
    /// - `out-defined` gives every run a clean end: the fuzz kills by an added end, and kink kills
    ///   the corpus program by both slots, its baseline exit stop and whole term the empty set.
    ///
    /// Fails if either tool counts an undefined step's pre-step configuration as an end (a fuzz
    /// witness for `log-one`, or kink killing it), or if an empty set of ends stops being a value
    /// (`out-defined` is not killed by its whole term).
    #[test]
    #[ignore = "kink"]
    fn an_undefined_step_is_no_end_for_either_tool() {
        let dir = flow(
            "undefined-end",
            "ue.k",
            UNDEFINED_K,
            "UE",
            "",
            &[("one", "go(1)")],
            UNDEFINED_MUTATIONS,
        );
        let report = krust_fuzz(
            &dir,
            "t",
            "go(1)",
            Vec::new(),
            "<k> step(_) </k>",
            PatternAt::AnyState,
            1,
        );
        let case = witness(&report);
        assert_eq!(case["comparable"], json!({"holds": true, "reasons": []}));
        assert_eq!(case["sides"][0]["halts"], json!(["trivial"]), "{case:#}");
        assert_eq!(row(&kink_results(&dir), "one")["class"], "comparable");
        // The program's result record, the one record of the flow's result cache.
        let records = fs::read_dir(dir.join("cache/results"))
            .unwrap()
            .flat_map(|spec| fs::read_dir(spec.unwrap().path()).unwrap())
            .map(|record| record.unwrap().path())
            .collect::<Vec<_>>();
        let [record] = records.as_slice() else {
            panic!("one result record: {records:?}");
        };
        let record: Value = serde_json::from_str(&fs::read_to_string(record).unwrap()).unwrap();
        assert_eq!(
            record["final_configuration"],
            json!([]),
            "an undefined step's pre-step configuration is no final configuration: {record:#}"
        );

        // `log-one`, the fuzz: each of the six inputs ends undefined on both sides; no witness.
        // The six cases try every assignment of the hole's finite domain, so the campaign stops
        // on that.
        let (document, ok) = kink_flow_fuzz(
            &dir,
            HOLE_TEMPLATE,
            "h",
            Job::Kill("log-one"),
            options(6, true, true),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], "domain-exhausted", "{document:#}");
        assert_eq!(document["program"], Value::Null);
        assert_eq!(totals(&document)["classes"], json!({"undefined": 6}));

        // `log-one`, kink: the corpus program agrees on both slots; the mutation survives.
        let mutation = kink_run(&dir, "log-one");
        assert_eq!(mutation["status"], "survived", "{mutation:#}");
        assert_eq!(
            mutation["executed"][0]["slots"],
            json!({"exit-stop": {"outcome": "agree"}, "whole-term": {"outcome": "agree"}}),
            "{mutation:#}"
        );

        // `out-defined`, the fuzz: an added end.
        let (document, ok) = kink_flow_fuzz(
            &dir,
            HOLE_TEMPLATE,
            "h",
            Job::Kill("out-defined"),
            options(6, true, true),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        let candidate = &document["attempts"][0]["candidate"];
        assert_eq!(candidate["kill"], "added-end", "{candidate:#}");
        let confirmation = &document["attempts"][0]["confirmation"];
        assert_eq!(confirmation["status"], "killed", "{confirmation:#}");

        // `out-defined`, kink: the corpus program kills by both slots; the baseline's exit stop
        // and whole term are the empty set.
        let mutation = kink_run(&dir, "out-defined");
        assert_eq!(
            (&mutation["status"], &mutation["killer"]),
            (&json!("killed"), &json!("one")),
            "{mutation:#}"
        );
        let slots = &mutation["executed"][0]["slots"];
        assert_eq!(slots["exit-stop"]["outcome"], "distinguish", "{slots:#}");
        assert_eq!(
            slots["exit-stop"]["sides"]["baseline"],
            json!([]),
            "{slots:#}"
        );
        assert_eq!(slots["whole-term"]["outcome"], "distinguish", "{slots:#}");
        assert_eq!(
            slots["whole-term"]["sides"]["baseline"],
            json!({"final_configurations": 0}),
            "{slots:#}"
        );
        assert_eq!(
            slots["whole-term"]["sides"]["mutant"]["final_configurations"], 1,
            "{slots:#}"
        );
    }

    /// `go(N)` reaches `done(N)` through `pa(N)`, and through `pb(N)`, whose step writes
    /// `N /Int 0` to `<out>`: an undefined step beside an end. `split(N)` ends in `done(N)` or,
    /// through `edge(N)`, in `done(N +Int 1)`.
    const UNDEFINED_PATH_K: &str = "module UP-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | split(Int) [symbol(split)]
endmodule

module UP
  imports UP-SYNTAX
  imports INT
  syntax KItem ::= pa(Int) [symbol(pa)] | pb(Int) [symbol(pb)]
                 | edge(Int) [symbol(edge)] | done(Int) [symbol(done)]
  configuration <k> $PGM:Pgm </k> <out> 0 </out>
  rule [toa]:   <k> go(N) => pa(N) </k>
  rule [tob]:   <k> go(N) => pb(N) </k>
  rule [adone]: <k> pa(N) => done(N) </k>
  rule [bdone]: <k> pb(N) => done(N) </k> <out> _ => N /Int 0 </out>
  rule [sdone]: <k> split(N) => done(N) </k>
  rule [sedge]: <k> split(N) => edge(N) </k>
  rule [edge]:  <k> edge(N) => done(N +Int 1) </k>
endmodule
";

    /// `pb-defined` makes `pb(N)`'s step defined, ending in `go(N)`'s other end: the mutant
    /// differs from the baseline only by the undefined path it removes. `edge-undefined` makes
    /// `edge(N)`'s step undefined: `split(N)` loses the end `done(N +Int 1)` beside its end
    /// `done(N)`.
    const UNDEFINED_PATH_MUTATIONS: &str = "[[mutation]]\nid = \"pb-defined\"\n\
                                            [[mutation.edit]]\nrule = \"UP.bdone\"\nfind = \"N \
                                            /Int 0\"\nreplace = \"0\"\n\n[[mutation]]\nid = \
                                            \"edge-undefined\"\n[[mutation.edit]]\nrule = \
                                            \"UP.edge\"\nfind = \"N +Int 1\"\nreplace = \"N \
                                            /Int 0\"\n";

    /// (d) An undefined path beside an end is no difference, and an end it replaces is a removed
    /// end (kink27 R1-UNDEF fix round 1). An undefined step's outcome is undefinedness, which is
    /// no configuration and no end, and neither tool takes a verdict from undefinedness itself.
    /// - `pb-defined`: the baseline's `go(1)` has the ends `{done(1)}` and an undefined path, the
    ///   mutant's the same ends and no undefined path. The fuzz finds no witness among the six
    ///   inputs of the hole's domain; kink's slots agree on both programs (the exit stops are
    ///   `{normal}` on both sides), so the mutation survives.
    /// - `edge-undefined`: `split(1)` ends in `{done(1), done(2)}` in the baseline and in
    ///   `{done(1)}` and an undefined path in the mutant. kink kills by the whole term (a removed
    ///   end); the exit stops are `{normal}` on both sides and agree.
    ///
    /// Fails if a state slot tells the sides apart by an undefined path (before the fix round the
    /// exit stop held the class `undefined-step` and killed `pb-defined`), or if an end removed
    /// beside an undefined path stops distinguishing.
    #[test]
    #[ignore = "kink"]
    fn an_undefined_path_beside_an_unchanged_end_is_no_difference() {
        let dir = flow(
            "undefined-path",
            "up.k",
            UNDEFINED_PATH_K,
            "UP",
            "",
            &[("one", "go(1)"), ("split", "split(1)")],
            UNDEFINED_PATH_MUTATIONS,
        );

        // `pb-defined`, the fuzz: no input gives an added or a removed end.
        let (document, ok) = kink_flow_fuzz(
            &dir,
            HOLE_TEMPLATE,
            "h",
            Job::Kill("pb-defined"),
            options(6, true, true),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], "domain-exhausted", "{document:#}");
        assert_eq!(document["program"], Value::Null, "{document:#}");

        // `pb-defined`, kink: every slot of both programs agrees.
        let mutation = kink_run(&dir, "pb-defined");
        assert_eq!(mutation["status"], "survived", "{mutation:#}");
        let executed = mutation["executed"].as_array().unwrap();
        assert_eq!(executed.len(), 2, "{mutation:#}");
        for entry in executed {
            assert_eq!(
                entry["slots"],
                json!({"exit-stop": {"outcome": "agree"}, "whole-term": {"outcome": "agree"}}),
                "{mutation:#}"
            );
        }

        // `edge-undefined`, kink: `split` kills by the whole term alone.
        let mutation = kink_run(&dir, "edge-undefined");
        assert_eq!(
            (&mutation["status"], &mutation["killer"]),
            (&json!("killed"), &json!("split")),
            "{mutation:#}"
        );
        let slots = &mutation["executed"]
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["program"] == "split")
            .unwrap_or_else(|| panic!("{mutation:#}"))["slots"];
        assert_eq!(slots["exit-stop"], json!({"outcome": "agree"}), "{slots:#}");
        assert_eq!(slots["whole-term"]["outcome"], "distinguish", "{slots:#}");
        assert_eq!(
            slots["whole-term"]["sides"]["baseline"],
            json!({"final_configurations": 2}),
            "{slots:#}"
        );
        assert_eq!(
            slots["whole-term"]["sides"]["mutant"]["final_configurations"], 1,
            "{slots:#}"
        );
    }

    /// `go(N)` writes `g(N)` to `<log>` and `hgo(N)` writes `h(N)`, then `step(N)` writes
    /// `N /Int 0` to `<out>`: an undefined step from every input, taken from a configuration whose
    /// `<log>` holds an application no equation reduces. `g` is declared total, `h` is not.
    const UNDEFINED_EXISTS_K: &str = "module UX-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | hgo(Int) [symbol(hgo)]
endmodule

module UX
  imports UX-SYNTAX
  imports INT
  syntax Int   ::= g(Int) [function, total, symbol(g)]
                 | h(Int) [function, symbol(h)]
  syntax KItem ::= step(Int) [symbol(step)]
  configuration <k> $PGM:Pgm </k> <log> 0 </log> <out> 0 </out>
  rule [g-zero]: g(0) => 1
  rule [h-zero]: h(0) => 1
  rule [go]:   <k> go(N) => step(N) </k> <log> _ => g(N) </log>
  rule [hgo]:  <k> hgo(N) => step(N) </k> <log> _ => h(N) </log>
  rule [step]: <k> step(N) => .K </k> <log> _ => 0 </log> <out> _ => N /Int 0 </out>
endmodule
";

    /// `out-defined` writes `N` to `<out>`: the step is defined, and every run ends cleanly.
    const UNDEFINED_EXISTS_MUTATIONS: &str = "[[mutation]]\nid = \"out-defined\"\n\
                                              [[mutation.edit]]\nrule = \"UX.step\"\nfind = \
                                              \"N /Int 0\"\nreplace = \"N\"\n";

    /// (d) An undefined step needs its configuration to exist, not to be a value, for kink (kink27
    /// R3-UNDEF-BRIDGE). The configuration an undefined step is taken from is no end and is never
    /// compared, so a run whose every path ends in an undefined step has the empty set of ends;
    /// its path is real only if that configuration has an instance.
    /// - `go(1)` takes its undefined step from `<k> step(1) </k> <log> g(1) </log> <out> 0 </out>`:
    ///   ground, without a path condition, `g(1)` irreducible and so no value, but `g` is total, so
    ///   the configuration exists. kink's `results` judges the run comparable, with the empty set
    ///   of final configurations; `out-defined` gives the run a clean end, which kink's whole term
    ///   and exit stop tell from the baseline's empty sets. Known divergence (module
    ///   documentation): the fuzz's comparable conditions still read the undefined step's term as
    ///   an end that must be data, and refuse the run `end-not-data`.
    /// - `hgo(1)`'s configuration holds `h(1)`, which k-rust does not show defined: kink cannot
    ///   tell an instance-less run from the empty set of ends, so the row stays `unknown`.
    ///
    /// Fails if kink requires the pre-step configuration to be a terminal value (`one` is
    /// `unknown` and `out-defined` survives), or if it completes a leaf whose configuration is not
    /// shown to exist (`partial` is decided).
    #[test]
    #[ignore = "kink"]
    fn an_undefined_steps_configuration_need_only_exist() {
        let dir = flow(
            "undefined-exists",
            "ux.k",
            UNDEFINED_EXISTS_K,
            "UX",
            "",
            &[("one", "go(1)"), ("partial", "hgo(1)")],
            UNDEFINED_EXISTS_MUTATIONS,
        );
        let report = krust_fuzz(
            &dir,
            "t",
            "go(1)",
            Vec::new(),
            "<k> step(_) </k>",
            PatternAt::AnyState,
            1,
        );
        let case = witness(&report);
        assert_eq!(
            case["comparable"],
            json!({"holds": false, "reasons": ["end-not-data"]}),
            "{case:#}"
        );
        assert_eq!(case["sides"][0]["halts"], json!(["trivial"]), "{case:#}");

        let document = kink_results(&dir);
        assert_eq!(row(&document, "one")["class"], "comparable", "{document:#}");
        assert_eq!(
            row(&document, "partial")["class"],
            "unknown",
            "{document:#}"
        );
        // The result record of `one` in the flow's result cache.
        let record = fs::read_dir(dir.join("cache/results"))
            .unwrap()
            .flat_map(|spec| fs::read_dir(spec.unwrap().path()).unwrap())
            .map(|record| {
                let text = fs::read_to_string(record.unwrap().path()).unwrap();
                serde_json::from_str::<Value>(&text).unwrap()
            })
            .find(|record| record["program_id"] == "one")
            .expect("a result record of `one`");
        assert_eq!(
            record["final_configuration"],
            json!([]),
            "an undefined step's pre-step configuration is no final configuration: {record:#}"
        );

        // `out-defined`, kink: `one` kills by both slots; the baseline's whole term and exit stop
        // are the empty set.
        let mutation = kink_run(&dir, "out-defined");
        assert_eq!(
            (&mutation["status"], &mutation["killer"]),
            (&json!("killed"), &json!("one")),
            "{mutation:#}"
        );
        let slots = &mutation["executed"]
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["program"] == "one")
            .unwrap_or_else(|| panic!("{mutation:#}"))["slots"];
        assert_eq!(slots["whole-term"]["outcome"], "distinguish", "{slots:#}");
        assert_eq!(
            slots["whole-term"]["sides"]["baseline"],
            json!({"final_configurations": 0}),
            "{slots:#}"
        );
        assert_eq!(
            slots["whole-term"]["sides"]["mutant"]["final_configurations"], 1,
            "{slots:#}"
        );
        assert_eq!(slots["exit-stop"]["outcome"], "distinguish", "{slots:#}");
        assert_eq!(
            slots["exit-stop"]["sides"]["baseline"],
            json!([]),
            "{slots:#}"
        );
    }
}
