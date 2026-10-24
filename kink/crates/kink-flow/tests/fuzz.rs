//! `kink-flow fuzz` (fz26 P7-KINKFLOW T3a): `TEMPLATES.toml` decoding, the command line, and the
//! kill job on kink's own sides.
//!
//! The kink-tier tests (`#[ignore = "kink"]`) compile definitions and run campaigns:
//! - every mutant kink builds for `examples/imp`, `testdata/flow/markdown` and
//!   `testdata/flow/overlap` converts into a k-rust-fuzz definition with the baseline's source
//!   table, and both provenance digests compute (design F4, the review's probe A);
//! - on TRIAL2's IMP thin corpus (`testdata/flow/fuzz/imp`) the survivors TRIAL2 killed are killed
//!   on their templates, and the equivalent `add-commuted` gives no witness in 300 cases;
//! - a mutation kink refuses ends the command with kink's status and reason;
//! - the seven DATAEND repros (`testdata/flow/findings`) are not comparable, with their findings
//!   named, and with their names assumed give a witness whose fragment lists the premises;
//! - the same seed gives the same document.

use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_USAGE, execute},
    fuzz::{FuzzOptions, TemplateList, TemplateSource, compiled_side, kill},
    resolve,
};
use serde_json::Value;
use std::{
    ffi::OsString,
    path::{Path, PathBuf},
};

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn flow(name: &str) -> PathBuf {
    repository().join("testdata/flow").join(name)
}

fn on_stack<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(DEFINITION_STACK_BYTES)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap()
}

fn decode_error(text: &str) -> String {
    TemplateList::decode(text, Path::new("."))
        .expect_err("the templates are refused")
        .to_string()
}

#[test]
fn templates_decode_with_krust_fuzz_hole_keys() {
    let list = TemplateList::read(&flow("fuzz/imp/TEMPLATES.toml")).unwrap();
    let ids = list
        .templates
        .iter()
        .map(|t| t.id.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        ids,
        [
            "primes-holes",
            "sum-holes",
            "straight-holes",
            "sum-redeclare"
        ]
    );
    let primes = list.get("primes-holes").unwrap();
    assert_eq!(primes.source, TemplateSource::Program("primes".into()));
    assert_eq!(primes.holes.len(), 4);
    let straight = list.get("straight-holes").unwrap();
    assert_eq!(
        straight.source,
        TemplateSource::File("templates/straight.imp".into())
    );
    // A span hole addresses the template's text, named by the template's id.
    let json = serde_json::to_value(&straight.holes).unwrap();
    assert_eq!(json[0]["location"]["program"], "straight-holes");
    assert!(
        TemplateList::read(&flow("fuzz/impu/TEMPLATES.toml"))
            .unwrap()
            .get("clamp-holes")
            .is_some()
    );
}

#[test]
fn templates_are_decoded_strictly_and_hole_errors_name_the_template_and_hole() {
    let one = |hole: &str| {
        format!("[[template]]\nid = \"t\"\ntext = \"x = 1;\"\n[[template.hole]]\n{hole}\n")
    };
    // An unknown key of a hole: serde's message, wrapped with the template and the hole index.
    let message = decode_error(&one("nmae = \"X\"\nsort = \"Int\"\nliteral = \"1\""));
    assert!(
        message.starts_with("template \"t\".hole[0]: unknown field `nmae`"),
        "{message}"
    );
    // A TOML date is refused on kink's route (`try_into` would read it as a string choice).
    let message = decode_error(&one(
        "name = \"X\"\nsort = \"Int\"\nliteral = \"1\"\nchoices = [1979-05-27]",
    ));
    assert!(
        message.starts_with("template \"t\".hole[0]: a TOML date or time is not a hole value"),
        "{message}"
    );
    // A non-value choice: the library's refusal, named.
    let message = decode_error(&one(
        "name = \"X\"\nsort = \"Int\"\nliteral = \"1\"\nchoices = [[1, 2]]",
    ));
    assert!(message.starts_with("template \"t\".hole[0]: "), "{message}");
    assert!(message.contains("write collections"), "{message}");
    // The library's own refusals, named.
    let message = decode_error(&one("name = \"X\"\nsort = \"Int\""));
    assert_eq!(
        message,
        "template \"t\".hole[0]: hole `X`: give its `literal` (and `find`), or a `config-var`"
    );
    // A hole may not address another program by name.
    let message = decode_error(&one(
        "name = \"X\"\nsort = \"Int\"\nliteral = \"1\"\nprogram = \"other\"",
    ));
    assert!(
        message.starts_with("template \"t\".hole[0].program: \"other\""),
        "{message}"
    );
    // Template-level keys.
    assert_eq!(
        decode_error("[[template]]\nid = \"t\"\ntext = \"x\"\nholes = []\n"),
        "template \"t\".holes: unknown key"
    );
    assert_eq!(
        decode_error("[[template]]\nid = \"t\"\ntext = \"x\"\nfile = \"a.imp\"\n"),
        "template \"t\": give exactly one of program, file and text"
    );
    assert_eq!(
        decode_error("[[template]]\nid = \"t\"\nprogram = \"p\"\nstart_sort = \"Pgm\"\n"),
        "template \"t\": a template of a corpus program takes that program's start_sort and \
         variables; give the text as file or text to set others"
    );
    assert_eq!(
        decode_error("[[template]]\nid = \"t\"\nfile = \"../a.imp\"\n"),
        "template \"t\".file: path \"../a.imp\" leaves the templates' directory"
    );
    assert_eq!(
        decode_error(
            "[[template]]\nid = \"t\"\ntext = \"x\"\n[[template]]\nid = \"t\"\ntext = \"y\"\n"
        ),
        "template \"t\": duplicate template id"
    );
    assert_eq!(
        decode_error("[[templates]]\nid = \"t\"\n"),
        "templates: unknown key"
    );
}

fn run_cli(args: &[&str]) -> u8 {
    execute(args.iter().map(OsString::from).collect())
}

#[test]
fn the_command_line_refuses_what_t3a_does_not_build() {
    let dir = flow("fuzz/imp");
    let manifest = dir.join("FLOW.toml");
    let templates = dir.join("TEMPLATES.toml");
    let mutations = dir.join("MUTATIONS.toml");
    let (manifest, templates, mutations) = (
        manifest.to_str().unwrap(),
        templates.to_str().unwrap(),
        mutations.to_str().unwrap(),
    );
    let base = [
        "fuzz",
        manifest,
        templates,
        "--template",
        "primes-holes",
        "--kill",
        "div-becomes-mul",
        "--mutations",
        mutations,
    ];
    // Confirmation is T4's: without --no-confirm the command refuses to run.
    assert_eq!(run_cli(&base), EXIT_USAGE);
    for extra in [
        &["--no-confirm", "--reach", "imp.k:47"][..],
        &["--no-confirm", "--attempts", "3"],
        &["--no-confirm", "--cases", "0"],
        &["--no-confirm", "--cases", "3", "--work", "9"],
    ] {
        let args = base.iter().chain(extra).copied().collect::<Vec<_>>();
        assert_eq!(run_cli(&args), EXIT_USAGE, "{extra:?}");
    }
    let mut unknown = base.to_vec();
    unknown[4] = "no-such-template";
    unknown.push("--no-confirm");
    assert_eq!(run_cli(&unknown), EXIT_USAGE);
    let mut unknown = base.to_vec();
    unknown[6] = "no-such-mutation";
    unknown.push("--no-confirm");
    assert_eq!(run_cli(&unknown), EXIT_USAGE);
}

/// The kill job on the flow in `dir` with `templates` (a `TEMPLATES.toml` text decoded in `dir`,
/// or `None` for the file beside the flow).
fn fuzz_kill(
    dir: &Path,
    mutations: &str,
    templates: Option<&str>,
    template: &str,
    mutation: &str,
    options: FuzzOptions,
) -> (Value, bool) {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let list = MutationList::read(&dir.join(mutations)).unwrap();
    let templates = match templates {
        Some(text) => TemplateList::decode(text, dir).unwrap(),
        None => TemplateList::read(&dir.join("TEMPLATES.toml")).unwrap(),
    };
    let (template, mutation) = (template.to_owned(), mutation.to_owned());
    on_stack(move || kill(&manifest, &templates, &template, &list, &mutation, &options))
}

fn imp_options(cases: u64) -> FuzzOptions {
    FuzzOptions {
        budget: k_rust_fuzz::Budget::Cases(cases),
        max_work: Some(20_000),
        ..FuzzOptions::default()
    }
}

fn totals(document: &Value) -> &Value {
    &document["attempts"][0]["fuzz"]["totals"]
}

/// Design F4 (the review's probe A, kept as a test): every mutant kink builds converts through
/// `from_artifacts` with the baseline's source table, and both provenance digests compute.
#[test]
#[ignore = "kink"]
fn kink_mutants_convert_with_the_baseline_source_table() {
    let converted = on_stack(|| {
        let mut counts = Vec::new();
        for name in ["../../examples/imp", "markdown", "overlap"] {
            let mut converted = 0;
            let dir = flow(name);
            let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
            let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
            let (_, admitted) = kink_flow::admit_spec(&manifest);
            let (spec, _) = admitted.expect("the specification is admitted");
            let baseline = compiled_side(&manifest, &spec, &spec.compiled).unwrap();
            baseline.frontend_digest().unwrap();
            baseline.execution_definition_digest().unwrap();
            for mutation in &list.mutations {
                let Ok(resolved) = resolve(&manifest, &spec.loaded, mutation) else {
                    continue;
                };
                let Ok(validated) = spec.validator.validate(&resolved.patch) else {
                    continue;
                };
                let mutant = compiled_side(&manifest, &spec, &validated)
                    .unwrap_or_else(|e| panic!("{name} {}: {e}", mutation.id));
                mutant
                    .frontend_digest()
                    .unwrap_or_else(|e| panic!("{name} {}: {e}", mutation.id));
                mutant
                    .execution_definition_digest()
                    .unwrap_or_else(|e| panic!("{name} {}: {e}", mutation.id));
                converted += 1;
            }
            counts.push(converted);
        }
        counts
    });
    // The review's probe A log (`probe-kinkflow-review/probe_f4.log`, `cf456b34f`) converts 21
    // IMP, 6 Markdown and 2 overlap mutants; the design's "30 (22 IMP)" counts IMP's baseline.
    assert_eq!(converted, [21, 6, 2]);
}

/// TRIAL2's kills on IMP's thin corpus: blind sampling over the template's holes finds a
/// killing assignment, and the fragment re-enters it as a program of the flow.
#[test]
#[ignore = "kink"]
fn imp_survivors_are_killed_on_their_templates() {
    let dir = flow("fuzz/imp");
    for (template, mutation) in [
        ("primes-holes", "div-becomes-mul"),
        ("primes-holes", "and-true-ignores-rhs"),
        ("primes-holes", "div-guard-dropped"),
        ("straight-holes", "add-becomes-sub"),
    ] {
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            template,
            mutation,
            imp_options(300),
        );
        assert!(ok, "{mutation}: {:#}", document["action"]);
        assert_eq!(document["stopped"], Value::Null, "{mutation}");
        assert_eq!(document["job"]["outcome"], "fuzzed");
        assert_eq!(document["job"]["path_mode"], "all-paths");
        let fragment = document["program"]["fragment"].as_str().unwrap();
        let id = document["program"]["id"].as_str().unwrap();
        assert!(id.starts_with(&format!("{template}-fz-")), "{id}");
        assert!(
            fragment.starts_with(&format!("[[program]]\nid = \"{id}\"\n")),
            "{fragment}"
        );
        // The fragment is a program kink's manifest decoder accepts.
        let mut text = std::fs::read_to_string(dir.join("FLOW.toml")).unwrap();
        text.push('\n');
        text.push_str(fragment);
        let decoded = FlowManifest::decode(&text, &dir).unwrap();
        assert_eq!(decoded.programs.last().unwrap().id, id);
        assert_eq!(document["program"]["premises"], serde_json::json!([]));
        assert!(document["attempts"][0]["candidate"]["kill"].is_string());
    }
    let (document, ok) = fuzz_kill(
        &dir,
        "MUTATIONS.toml",
        None,
        // primes rather than TRIAL2's sum: on sum a hole D = 0 makes both sides loop, and
        // each such case runs out its work bound (300 cases took 207 s on a loaded host,
        // against 16 s on primes).
        "primes-holes",
        "add-commuted",
        imp_options(300),
    );
    assert!(ok);
    assert_eq!(document["stopped"], "budget", "{:#}", document["action"]);
    assert_eq!(document["program"], Value::Null);
    assert_eq!(totals(&document)["cases"], 300);
}

/// A mutation kink refuses ends the command with kink's status and reason; nothing is fuzzed.
#[test]
#[ignore = "kink"]
fn kink_refusals_end_the_command_with_kinks_reason() {
    let calc = "[[template]]\nid = \"add\"\nprogram = \"add\"\n";
    for (mutation, status, reason) in [
        ("no-such-rule", "invalid-mutation", "unknown-label"),
        ("add-in-a-group", "equivalent", "equivalent-compilation"),
        ("add-unbound", "invalid", "rejected"),
    ] {
        let (document, ok) = fuzz_kill(
            &flow("calc"),
            "MUTATIONS-statuses.toml",
            Some(calc),
            "add",
            mutation,
            FuzzOptions::default(),
        );
        assert!(!ok, "{mutation}");
        assert_eq!(document["job"]["outcome"], "refused", "{mutation}");
        assert_eq!(
            document["job"]["status"], status,
            "{mutation}: {document:#}"
        );
        assert_eq!(
            document["job"]["reason"], reason,
            "{mutation}: {document:#}"
        );
        assert_eq!(document["stopped"], "refused");
        assert_eq!(document["attempts"], serde_json::json!([]));
    }
    let overlap = "[[template]]\nid = \"one\"\nprogram = \"minus-one\"\n";
    let (document, ok) = fuzz_kill(
        &flow("overlap"),
        "MUTATIONS.toml",
        Some(overlap),
        "one",
        "pos-widened",
        FuzzOptions::default(),
    );
    assert!(!ok);
    assert_eq!(document["job"]["status"], "invalid");
    assert_eq!(document["job"]["reason"], "inconsistent-mutant");
    assert!(
        !document["job"]["inconsistent_pairs"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{document:#}"
    );
}

const REPROS: [&str; 7] = [
    "diamond",
    "r3-modov",
    "r3-plainq",
    "r3-propagate",
    "r4-empty",
    "r4-hookite",
    "r4-partnorule",
];

/// One hole on the repros' program `go(1)`.
const REPRO_TEMPLATE: &str = r#"
[[template]]
id = "go"
program = "one"

  [[template.hole]]
  name = "N"
  sort = "Int"
  find = "go(1)"
  literal = "1"
  range = { min = 0, max = 3 }
"#;

/// The seven DATAEND repros: strict comparability makes each campaign `not-comparable`, naming
/// its findings with their verdicts; with every name assumed on the command line the campaign
/// finds a witness, and the fragment lists each premise, genuine ones flagged, with the
/// instruction to add it to the flow.
#[test]
#[ignore = "kink"]
fn the_findings_repros_are_not_comparable_until_their_findings_are_named() {
    for name in REPROS {
        let dir = flow(&format!("findings/{name}"));
        let (strict, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(REPRO_TEMPLATE),
            "go",
            "store-changed",
            FuzzOptions::default(),
        );
        assert!(!ok, "{name}");
        assert_eq!(strict["stopped"], "not-comparable", "{name}: {strict:#}");
        assert_eq!(strict["program"], Value::Null);
        let findings = strict["findings"].as_array().unwrap();
        assert!(!findings.is_empty(), "{name}");
        // kink's own facts agree: the baseline has no data while these are unnamed.
        assert_eq!(strict["spec"]["has_data"], false, "{name}");
        let mut names = findings
            .iter()
            .filter(|f| f["side"] == "baseline")
            .map(|f| f["name"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        names.sort();
        names.dedup();
        let genuine = findings.iter().any(|f| f["verdict"] == "genuine");
        let (assumed, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(REPRO_TEMPLATE),
            "go",
            "store-changed",
            FuzzOptions {
                assume_joined: names.clone(),
                ..FuzzOptions::default()
            },
        );
        assert!(ok, "{name}: {assumed:#}");
        assert_eq!(assumed["stopped"], Value::Null, "{name}");
        let premises = assumed["program"]["premises"].as_array().unwrap();
        assert_eq!(
            premises
                .iter()
                .map(|p| p["name"].as_str().unwrap())
                .collect::<Vec<_>>(),
            names,
            "{name}"
        );
        assert!(premises.iter().all(|p| p["in_flow"] == false));
        assert_eq!(
            premises.iter().any(|p| p["genuine"] == true),
            genuine,
            "{name}: {premises:#?}"
        );
        assert!(
            assumed["action"]
                .as_str()
                .unwrap()
                .contains("first add to [spec] assume_joined"),
            "{name}"
        );
    }
}

/// The same seed gives the same document; a time limit of 0 cancels the run before its first
/// case.
#[test]
#[ignore = "kink"]
fn the_same_seed_gives_the_same_document() {
    let dir = flow("fuzz/imp");
    let run = || {
        fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            "primes-holes",
            "div-becomes-mul",
            imp_options(300),
        )
    };
    let (first, ok) = run();
    assert!(ok);
    let (second, _) = run();
    assert_eq!(first, second);
    let (cancelled, ok) = fuzz_kill(
        &dir,
        "MUTATIONS.toml",
        None,
        "primes-holes",
        "div-becomes-mul",
        FuzzOptions {
            time_limit_ms: Some(0),
            ..imp_options(300)
        },
    );
    assert!(ok);
    assert_eq!(cancelled["stopped"], "time-limit", "{cancelled:#}");
}
