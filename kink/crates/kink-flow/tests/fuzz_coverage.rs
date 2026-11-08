//! `kink-flow fuzz` jobs for coverage gaps (CS-8): `--refuted RULE` and `--cover ITEM` look for
//! hole values whose program covers an open obligation of `coverage` (a requirement, a
//! production, a heating rule), read from the records `coverage` reads, and kink's own
//! `coverage` confirms the program covers it; every open obligation's target spells its job.
//!
//! The fixture is written here: every program ends by itself within a few steps, and the
//! manifest's `[budget] time_ms` is far above what such a run takes (R4-WALLCLOCK), so no result
//! depends on a clock. Each test compiles the definition and runs campaigns (kink tier).

use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_flow::{
    FlowManifest,
    coverage::CoverageOptions,
    fuzz::{FuzzJob, FuzzOptions, TemplateList, fuzz_job},
};
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

/// `run(X)` steps to `add(X, 1)` for `X <=Int 5` (`plain`) and to the nested `add(add(X, 1), 1)`
/// otherwise (`nested`), whose inner sum `add` heats out of its first position (it is
/// `strict`); `sum` adds two integers. The sum ends the run through `mark` (`0 <= N < 4`, noting
/// `low()`) or `other` (`N >= 4` or `N < 0`, noting `high()`). The corpus's one program `run(1)`
/// takes `plain`, `sum` and `mark`: `plain`'s condition is never refuted, `mark`'s second
/// conjunct never `false`, `high` is never built, and `add` never heats its first position.
const GAPS_K: &str = r#"module GAPS-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int | add(Exp, Exp) [strict, symbol(add)]
  syntax Note ::= low() [symbol(low)] | high() [symbol(high)]
  syntax Pgm ::= run(Int) [symbol(run)]
endmodule

module GAPS
  imports GAPS-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k> <note> .K </note>
  syntax KResult ::= Int
  rule [plain]: <k> run(X) => add(X, 1) </k> requires X <=Int 5
  rule [nested]: <k> run(X) => add(add(X, 1), 1) </k> requires X >Int 5
  rule [sum]: <k> add(A:Int, B:Int) => A +Int B ... </k>
  rule [mark]: <k> N:Int => .K </k> <note> _ => low() </note> requires N >=Int 0 andBool N <Int 4
  rule [other]: <k> N:Int => .K </k> <note> _ => high() </note> requires N >=Int 4 orBool N <Int 0
endmodule
"#;

/// One hole over `run(1)`'s integer.
const GAPS_TEMPLATES: &str = "[[template]]\nid = \"run-holes\"\nprogram = \"p\"\n\
                              [[template.hole]]\nname = \"X\"\nsort = \"Int\"\nfind = \"1\"\n\
                              literal = \"1\"\nrange = { min = 0, max = 20 }\n";

fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-fuzz-coverage-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// The GAPS flow in a scratch directory, with the program `p` (`run(1)`).
fn gaps_flow(name: &str) -> PathBuf {
    let dir = scratch(name);
    fs::write(dir.join("gaps.k"), GAPS_K).unwrap();
    // R4-WALLCLOCK: every run ends by itself within a few steps, far below this bound.
    fs::write(
        dir.join("FLOW.toml"),
        "[spec]\nentry = \"gaps.k\"\nmain_module = \"GAPS\"\nsyntax_module = \"GAPS-SYNTAX\"\n\n\
         [budget]\ntime_ms = 600000\n\n[[program]]\nid = \"p\"\ntext = \"run(1)\"\n",
    )
    .unwrap();
    dir
}

fn on_stack<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(DEFINITION_STACK_BYTES)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap()
}

/// The coverage document of the flow in `dir`, derived with kink-flow's spelling.
fn coverage(dir: &Path) -> Value {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let cache = dir.join("cache");
    on_stack(move || {
        let (mut document, ok) = kink_flow::coverage::coverage(
            &manifest,
            &CoverageOptions {
                cache: Some(cache),
                ..CoverageOptions::default()
            },
        );
        assert!(ok, "{document:#}");
        kink_flow::coverage::derive(&mut document, &kink_flow::cli::KinkFlowSpelling);
        document
    })
}

/// The open target whose item `select` accepts.
fn target(document: &Value, select: impl Fn(&str) -> bool) -> &Value {
    document["targets"]
        .as_array()
        .unwrap()
        .iter()
        .find(|target| target["item"].as_str().is_some_and(&select))
        .unwrap_or_else(|| panic!("no such target: {:#}", document["targets"]))
}

/// The obligation id a target's `fuzz --cover` hint names, unquoted.
fn cover_id(target: &Value) -> String {
    let hint = target["fuzz"]
        .as_str()
        .unwrap_or_else(|| panic!("{target:#}"));
    let (_, id) = hint
        .split_once(" --cover ")
        .unwrap_or_else(|| panic!("no --cover in {hint}"));
    assert!(
        hint.starts_with("kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID --cover "),
        "{hint}"
    );
    id.trim_matches('\'').to_owned()
}

/// What a job on the GAPS flow in `dir` names.
enum Job {
    Refuted(&'static str),
    Cover(String),
    Fired(&'static str),
}

fn run(dir: &Path, job: Job, cases: u64) -> Value {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let templates = TemplateList::decode(GAPS_TEMPLATES, dir).unwrap();
    let options = FuzzOptions {
        budget: k_rust_fuzz::Budget::Cases(cases),
        max_work: Some(20_000),
        confirm: true,
        cache: Some(dir.join("fuzz-cache")),
        ..FuzzOptions::default()
    };
    on_stack(move || {
        let job = match &job {
            Job::Refuted(rule) => FuzzJob::Refuted { rule },
            Job::Cover(item) => FuzzJob::Cover { item },
            Job::Fired(rule) => FuzzJob::Rule { rule, fired: true },
        };
        let (document, ok) = fuzz_job(&manifest, &templates, "run-holes", job, &options);
        assert!(ok, "{document:#}");
        document
    })
}

/// The found program's `X`.
fn hole(document: &Value) -> i64 {
    let candidate = &document["attempts"][0]["candidate"];
    candidate["holes"][0]["k-text"]
        .as_str()
        .and_then(|x| x.parse().ok())
        .unwrap_or_else(|| panic!("{candidate:#}"))
}

/// A witness kink's own `coverage` confirmed as covering `item`, and its document's job.
fn assert_covers(document: &Value, kind: &str, item: &str) {
    assert_eq!(document["stopped"], Value::Null, "{document:#}");
    assert_eq!(document["job"]["kind"], kind, "{document:#}");
    assert_eq!(document["job"]["item"]["id"], item, "{document:#}");
    let confirmation = &document["attempts"][0]["confirmation"];
    assert_eq!(confirmation["confirmed"], true, "{confirmation:#}");
    assert_eq!(confirmation["status"], "covered", "{confirmation:#}");
    assert_eq!(confirmation["class"], "comparable", "{confirmation:#}");
    assert_eq!(document["program"]["confirmed"], true, "{document:#}");
    // The goal's distance is followed by the climb, beside blind sampling.
    let weights = &document["attempts"][0]["fuzz"]["identity"]["proposers"]["weights"];
    assert_eq!(weights["climb"], 1, "{weights:#}");
}

mod kink_tier {
    use super::*;

    /// `plain`'s condition `X <=Int 5` no case refuted: its requirement `refuted` is open, and
    /// its target spells `--cover` with its id. `--refuted plain` finds `X > 5`, which `coverage`
    /// confirms; with the fragment appended, the requirement is covered. The same seed gives the
    /// same document.
    #[test]
    #[ignore = "kink"]
    fn a_refuted_job_finds_a_program_that_refutes_a_guard_no_case_refuted() {
        let dir = gaps_flow("refuted");
        let before = coverage(&dir);
        let item = "requirement:GAPS.plain:refuted";
        assert_eq!(cover_id(target(&before, |id| id == item)), item);
        let document = run(&dir, Job::Refuted("plain"), 60);
        assert_covers(&document, "refuted", item);
        assert_eq!(
            document["job"]["rule"]["label"], "GAPS.plain",
            "{document:#}"
        );
        assert_eq!(document["job"]["item"]["family"], "requirements");
        assert!(hole(&document) > 5, "{document:#}");
        assert_eq!(run(&dir, Job::Refuted("plain"), 60), document);
        // `--cover` of the same id is the same goal.
        let covered = run(&dir, Job::Cover(item.to_owned()), 60);
        assert_eq!(covered["job"]["item"], document["job"]["item"]);

        let path = dir.join("FLOW.toml");
        let mut flow = fs::read_to_string(&path).unwrap();
        flow.push('\n');
        flow.push_str(document["program"]["fragment"].as_str().unwrap());
        fs::write(&path, flow).unwrap();
        let after = coverage(&dir);
        let requirement = after["families"]["requirements"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|requirement| requirement["id"] == item)
            .unwrap();
        assert_eq!(requirement["covered"], true, "{requirement:#}");
    }

    /// `mark`'s second conjunct `N <Int 4` was reached only `true`: its `false` is open, and the
    /// job its target spells finds a program whose sum is at least 4 after a first conjunct
    /// `true`.
    #[test]
    #[ignore = "kink"]
    fn an_operand_truth_job_finds_the_valuation_that_reaches_the_node() {
        let dir = gaps_flow("operand");
        let before = coverage(&dir);
        let id = cover_id(target(&before, |id| {
            id.starts_with("requirement:GAPS.mark:")
                && id.contains("<Int 4")
                && id.ends_with(":false")
        }));
        let document = run(&dir, Job::Cover(id.clone()), 60);
        assert_covers(&document, "cover", &id);
        assert_eq!(document["job"]["item"]["kind"], "false");
        let x = hole(&document);
        assert!(x >= 3, "{document:#}");
    }

    /// `high` is built only by `other`, which no case fires: the production is unreached, and
    /// the job its target spells finds a program whose sum is at least 4.
    #[test]
    #[ignore = "kink"]
    fn a_syntax_item_job_finds_a_program_that_touches_the_production() {
        let dir = gaps_flow("syntax");
        let before = coverage(&dir);
        let id = cover_id(target(&before, |id| {
            id.starts_with("syntax:") && id.contains("high")
        }));
        let document = run(&dir, Job::Cover(id.clone()), 60);
        assert_covers(&document, "cover", &id);
        assert_eq!(document["job"]["item"]["family"], "syntax");
        assert!(hole(&document) >= 3, "{document:#}");
    }

    /// `add` is `strict`: its first position heats only on `nested`'s path, which no case takes;
    /// the heating item's target spells its job, which finds `X > 5`.
    #[test]
    #[ignore = "kink"]
    fn a_heating_job_finds_a_program_that_heats_the_position() {
        let dir = gaps_flow("heating");
        let before = coverage(&dir);
        let id = cover_id(target(&before, |id| {
            id.starts_with("rule:") && id.ends_with(":heat:1")
        }));
        let document = run(&dir, Job::Cover(id.clone()), 60);
        assert_covers(&document, "cover", &id);
        assert_eq!(document["job"]["item"]["kind"], "heating");
        assert!(hole(&document) > 5, "{document:#}");
    }

    /// The rule jobs are unchanged: `--fired` samples blind and its document has no `item`; an
    /// obligation no family lists, and a rule that states no requirement, are refused at stage
    /// `item` before any campaign.
    #[test]
    #[ignore = "kink"]
    fn the_rule_jobs_are_unchanged_and_an_unknown_obligation_is_refused() {
        let dir = gaps_flow("unchanged");
        let fired = run(&dir, Job::Fired("nested"), 40);
        assert_eq!(fired["job"]["kind"], "fired");
        assert!(fired["job"].get("item").is_none(), "{fired:#}");
        let weights = &fired["attempts"][0]["fuzz"]["identity"]["proposers"]["weights"];
        assert_eq!(weights, &serde_json::json!({"blind": 1}), "{weights:#}");
        assert!(hole(&fired) > 5, "{fired:#}");

        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let templates = TemplateList::decode(GAPS_TEMPLATES, &dir).unwrap();
        let (refused, ok) = on_stack(move || {
            fuzz_job(
                &manifest,
                &templates,
                "run-holes",
                FuzzJob::Cover {
                    item: "requirement:GAPS.plain:nothing",
                },
                &FuzzOptions::default(),
            )
        });
        assert!(!ok);
        assert_eq!(refused["stopped"], "refused", "{refused:#}");
        assert_eq!(refused["job"]["refusal"]["stage"], "item", "{refused:#}");
        assert_eq!(
            refused["job"]["refusal"]["reason"], "unknown-item",
            "{refused:#}"
        );
        let (no_requirement, _) = {
            let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
            let templates = TemplateList::decode(GAPS_TEMPLATES, &dir).unwrap();
            on_stack(move || {
                fuzz_job(
                    &manifest,
                    &templates,
                    "run-holes",
                    FuzzJob::Refuted { rule: "sum" },
                    &FuzzOptions::default(),
                )
            })
        };
        assert_eq!(
            no_requirement["job"]["refusal"]["reason"], "no-requirement",
            "{no_requirement:#}"
        );
    }
}
