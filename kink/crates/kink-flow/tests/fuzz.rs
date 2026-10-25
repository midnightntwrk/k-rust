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
//!
//! T3b's guards (kink-tier unless noted):
//! - a hole may address a configuration variable's text (`program = "$NAME"`; light), and its
//!   witness re-enters with the instantiated binding;
//! - kink's definition exclusions on either side refuse the job with kink's own reason;
//! - a mutation of a `[macro]` rule that changes the template's parse is refused before any case;
//! - the per-candidate assembly check: a hand-altered initial configuration is an
//!   `assembly-mismatch`, and every witness above matches kink's assembly;
//! - a Markdown template without `start_sort` takes kink's default start sort and parses;
//! - the last `run` document gives the template's class, the mutation's reaching programs as
//!   suggested templates, and the warnings.

use kink_corpus::ProgramSource;
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_USAGE, execute},
    fuzz::{
        AssemblyCheck, FuzzJob, FuzzOptions, TemplateList, TemplateSource, check_assembly,
        compiled_side, fuzz_job, kill,
    },
    pattern::PatternList,
    query::{QueryOptions, query},
    resolve,
    results::{ResultsOptions, results},
    search::RunOptions,
};
use serde_json::Value;
use std::{
    collections::BTreeSet,
    ffi::OsString,
    fs,
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
        // One job per command.
        &["--no-confirm", "--reach", "imp.k:47"][..],
        &["--no-confirm", "--attempts", "3"],
        &["--no-confirm", "--cases", "0"],
        &["--no-confirm", "--cases", "3", "--work", "9"],
    ] {
        let args = base.iter().chain(extra).copied().collect::<Vec<_>>();
        assert_eq!(run_cli(&args), EXIT_USAGE, "{extra:?}");
    }
    // The reach and pattern jobs (T5) parse; a pattern job takes no assumed name.
    let patterns = scratch("cli-patterns").join("PATTERNS.toml");
    fs::write(
        &patterns,
        "[[pattern]]\nid = \"p\"\npattern = \"<k> 0 </k>\"\n",
    )
    .unwrap();
    let patterns = patterns.to_str().unwrap();
    let job = |extra: &[&str]| {
        let mut args = vec!["fuzz", manifest, templates, "--template", "primes-holes"];
        args.extend_from_slice(extra);
        args.push("--no-confirm");
        run_cli(&args)
    };
    assert_eq!(
        job(&[
            "--pattern",
            "p",
            "--patterns",
            patterns,
            "--assume-joined",
            "x"
        ]),
        EXIT_USAGE
    );
    assert_eq!(job(&["--pattern", "q", "--patterns", patterns]), EXIT_USAGE);
    assert_eq!(job(&["--pattern", "p"]), EXIT_USAGE);
    assert_eq!(
        job(&["--reach", "imp.k:47", "--fired", "--mutations", mutations]),
        EXIT_USAGE
    );
    assert_eq!(job(&["--fired"]), EXIT_USAGE);
    let mut unknown = base.to_vec();
    unknown[4] = "no-such-template";
    unknown.push("--no-confirm");
    assert_eq!(run_cli(&unknown), EXIT_USAGE);
    let mut unknown = base.to_vec();
    unknown[6] = "no-such-mutation";
    unknown.push("--no-confirm");
    assert_eq!(run_cli(&unknown), EXIT_USAGE);
}

/// A small definition for the reach and pattern jobs (T5): `run(X)` steps to `step(dbl(X))`,
/// which writes `X` to `<out>` above 10 (rule `big`) and `0` otherwise (`small`), ending
/// naturally; `dbl` is a function (an equation) and `seven` a macro.
const STEPS_K: &str = "module STEPS-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= run(Int)
endmodule

module STEPS
  imports STEPS-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k> <out> 0 </out>
  syntax KItem ::= step(Int)
  syntax Int ::= dbl(Int) [function, total]
  syntax Int ::= seven() [macro]
  rule seven() => 7
  rule dbl(X) => X *Int 2
  rule [go]: <k> run(X) => step(dbl(X)) </k>

  rule [big]: <k> step(X) => .K </k> <out> _ => X </out> requires X >Int 10
  rule [small]: <k> step(X) => .K </k> <out> _ => 0 </out> requires X <=Int 10
endmodule
";

const STEPS_TEMPLATES: &str = "[[template]]\nid = \"run-holes\"\nprogram = \"one\"\n\
                               [[template.hole]]\nname = \"X\"\nsort = \"Int\"\nfind = \"1\"\n\
                               literal = \"1\"\nrange = { min = 0, max = 9 }\n";

/// The 1-based line of `STEPS_K` that starts with `prefix` (after indentation).
fn steps_line(prefix: &str) -> usize {
    STEPS_K
        .lines()
        .position(|line| line.trim_start().starts_with(prefix))
        .unwrap()
        + 1
}

/// The STEPS flow in a scratch directory, with the program `one` (`run(1)`).
fn steps_flow(name: &str) -> PathBuf {
    let manifest = "[spec]\nentry = \"steps.k\"\nmain_module = \"STEPS\"\nsyntax_module = \
                    \"STEPS-SYNTAX\"\n\n[[program]]\nid = \"one\"\ntext = \"run(1)\"\n";
    scratch_flow(name, "steps.k", STEPS_K, manifest, "")
}

/// A job on the flow in `dir` with `templates` (decoded in `dir`), on the thread allowance.
fn run_job(
    dir: &Path,
    templates: &str,
    template: &str,
    job: Job,
    options: FuzzOptions,
) -> (Value, bool) {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let templates = TemplateList::decode(templates, dir).unwrap();
    let template = template.to_owned();
    on_stack(move || match &job {
        Job::Reach(rule, fired) => fuzz_job(
            &manifest,
            &templates,
            &template,
            FuzzJob::Reach {
                rule,
                fired: *fired,
            },
            &options,
        ),
        Job::Pattern(list, id) => fuzz_job(
            &manifest,
            &templates,
            &template,
            FuzzJob::Pattern { list, id },
            &options,
        ),
    })
}

/// [`run_job`]'s job.
enum Job {
    Reach(String, bool),
    Pattern(PatternList, String),
}

/// Append the witness's `[[program]]` fragment to the flow's `FLOW.toml`.
fn append_fragment(dir: &Path, document: &Value) {
    let path = dir.join("FLOW.toml");
    let mut text = fs::read_to_string(&path).unwrap();
    text.push('\n');
    text.push_str(document["program"]["fragment"].as_str().unwrap());
    fs::write(&path, text).unwrap();
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

// ---------------------------------------------------------------------------------------------
// T3b: the guards
// ---------------------------------------------------------------------------------------------

/// A fresh directory under the test target's scratch space.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-fuzz-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// A flow of one specification file in a scratch directory: `spec` as `{entry}`, the manifest
/// text, and the mutation list.
fn scratch_flow(name: &str, entry: &str, spec: &str, manifest: &str, mutations: &str) -> PathBuf {
    let dir = scratch(name);
    fs::write(dir.join(entry), spec).unwrap();
    fs::write(dir.join("FLOW.toml"), manifest).unwrap();
    fs::write(dir.join("MUTATIONS.toml"), mutations).unwrap();
    dir
}

/// A hole inside a configuration variable's text decodes (KF-T3a refused it): the span is
/// addressed in that binding, by `$NAME`.
#[test]
fn a_template_hole_may_address_a_binding() {
    let list = TemplateList::decode(
        "[[template]]\nid = \"t\"\ntext = \"settle\"\nvariables = { TX = \"transfer(30, 1)\" \
         }\n[[template.hole]]\nname = \"A\"\nsort = \"Int\"\nprogram = \"$TX\"\nfind = \
         \"transfer(30, 1)\"\nliteral = \"30\"\n",
        Path::new("."),
    )
    .expect("a binding's text may hold a hole");
    let json = serde_json::to_value(&list.get("t").unwrap().holes).unwrap();
    assert_eq!(json[0]["location"]["program"], "$TX");
}

const LEDGER_SPEC: &str = r#"
// A transfer bound to the configuration variable $TX, settled against an account of 100 with a
// fee (k-rust-fuzz's tests/data/ledger, cut down).
module LEDGER-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "settle" [symbol(settle)]
endmodule
module LEDGER
  imports LEDGER-SYNTAX
  imports INT
  imports BOOL
  syntax Tx ::= transfer(Int, Int) [symbol(transfer)]
  configuration <k> $PGM:Pgm </k>
                <tx> $TX:Tx </tx>
                <balance> 100 </balance>
  rule [settle]: <k> settle => .K ... </k>
                 <tx> transfer(Amount, Fee) </tx>
                 <balance> Balance => Balance -Int Amount -Int Fee </balance>
endmodule
"#;

/// decision 1's census: a rule lists a map's keys, an order the definition leaves open
/// (`testdata/k/r0b/implchosen.k`); `{START}` is the `start` rule's right-hand side.
const CHOSEN_SPEC: &str = r#"
module IMPLCHOSEN-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax Prog ::= start(Int) [symbol(start)]
                | keys(List) [symbol(keys)]
                | count(Int) [symbol(count)]
endmodule
module IMPLCHOSEN
  imports IMPLCHOSEN-SYNTAX
  imports INT
  imports MAP
  imports LIST
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start(I) => keys({START}) </k>
  rule [count]: <k> count(I) => keys(ListItem(I)) </k>
endmodule
"#;

const CHOSEN_MANIFEST: &str = "[spec]\nentry = \"chosen.k\"\nmain_module = \"IMPLCHOSEN\"\n\
                               syntax_module = \"IMPLCHOSEN-SYNTAX\"\n\n[[program]]\nid = \
                               \"count\"\ntext = \"count(1)\"\n";

const CHOSEN_TEMPLATE: &str = "[[template]]\nid = \"count\"\nprogram = \"count\"\n\
                               [[template.hole]]\nname = \"N\"\nsort = \"Int\"\nfind = \
                               \"count(1)\"\nliteral = \"1\"\n";

const MACRO_SPEC: &str = r#"
// A program-level macro: `ten` is expanded when a program is parsed.
module MAC-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | Exp "+" Exp [strict, symbol(plus)]
  syntax Int ::= "ten" [macro]
endmodule
module MAC
  imports MAC-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  syntax KResult ::= Int
  rule [ten]: ten => 10
  rule [plus]: I1:Int + I2:Int => I1 +Int I2
endmodule
"#;

fn warning_kinds(document: &Value) -> Vec<&str> {
    document["warnings"]
        .as_array()
        .unwrap()
        .iter()
        .map(|warning| warning["kind"].as_str().unwrap())
        .collect()
}

mod kink_tier {
    use super::*;

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

    /// A span hole inside `$TX`'s text: the witness re-enters with the binding as instantiated (the
    /// fuzz report's `config-vars`), and kink's assembly of the fragment is each side's input.
    #[test]
    #[ignore = "kink"]
    fn a_hole_inside_a_binding_reenters_with_its_instantiated_binding() {
        let dir = scratch_flow(
            "ledger",
            "ledger.k",
            LEDGER_SPEC,
            "[spec]\nentry = \"ledger.k\"\nmain_module = \"LEDGER\"\nsyntax_module = \
             \"LEDGER-SYNTAX\"\n\n[[program]]\nid = \"settle\"\ntext = \"settle\"\nvariables = { TX = \
             \"transfer(30, 1)\" }\n",
            "[[mutation]]\nid = \"fee-dropped\"\n  [[mutation.edit]]\n  rule = \"LEDGER.settle\"\n  \
             find = \"Balance -Int Amount -Int Fee\"\n  replace = \"Balance -Int Amount\"\n",
        );
        let templates = "[[template]]\nid = \"tx\"\nprogram = \"settle\"\n[[template.hole]]\nname = \
                         \"A\"\nsort = \"Int\"\nprogram = \"$TX\"\nfind = \"transfer(30, 1)\"\nliteral \
                         = \"30\"\nrange = { min = 0, max = 50 }\n";
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(templates),
            "tx",
            "fee-dropped",
            imp_options(20),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        let candidate = &document["attempts"][0]["candidate"];
        assert_eq!(candidate["assembly"]["status"], "match", "{candidate:#}");
        let value = candidate["holes"][0]["k-text"].as_str().unwrap();
        assert_eq!(
            candidate["config-vars"]["TX"],
            format!("transfer({value}, 1)")
        );
        let fragment = document["program"]["fragment"].as_str().unwrap();
        let mut text = fs::read_to_string(dir.join("FLOW.toml")).unwrap();
        text.push('\n');
        text.push_str(fragment);
        let decoded = FlowManifest::decode(&text, &dir).unwrap();
        assert_eq!(
            decoded.programs.last().unwrap().variables,
            [("TX".to_owned(), format!("transfer({value}, 1)"))]
        );
    }

    /// kink's definition exclusions (design 3.2.4): an implementation-chosen hook on the baseline
    /// excludes every baseline run, so kink's `run` finds no comparable program (`error`,
    /// `no-comparable-program`, the program's cause naming the exclusion); one the mutation brings
    /// in makes kink report that mutation `unknown` (`implementation-chosen-hook`). Either refuses
    /// the job before any case, with kink's status and reason.
    #[test]
    #[ignore = "kink"]
    fn a_definition_exclusion_refuses_the_job_with_kinks_reason() {
        let keys = "keys_list((1 |-> I) (2 |-> I))";
        let count_edit = "[[mutation]]\nid = \"count-plus-one\"\n  [[mutation.edit]]\n  rule = \
                          \"IMPLCHOSEN.count\"\n  find = \"ListItem(I)\"\n  replace = \"ListItem(I \
                          +Int 1)\"\n";
        let baseline = scratch_flow(
            "chosen-baseline",
            "chosen.k",
            &CHOSEN_SPEC.replace("{START}", keys),
            CHOSEN_MANIFEST,
            count_edit,
        );
        let start_edit = format!(
            "[[mutation]]\nid = \"start-lists-keys\"\n  [[mutation.edit]]\n  rule = \
             \"IMPLCHOSEN.start\"\n  find = \"ListItem(I) ListItem(I)\"\n  replace = \"{keys}\"\n"
        );
        let mutant = scratch_flow(
            "chosen-mutant",
            "chosen.k",
            &CHOSEN_SPEC.replace("{START}", "ListItem(I) ListItem(I)"),
            CHOSEN_MANIFEST,
            &start_edit,
        );
        for (dir, mutation, side, status, reason) in [
            (
                &baseline,
                "count-plus-one",
                "baseline",
                "error",
                "no-comparable-program",
            ),
            (
                &mutant,
                "start-lists-keys",
                "mutant",
                "unknown",
                "implementation-chosen-hook",
            ),
        ] {
            let (document, ok) = fuzz_kill(
                dir,
                "MUTATIONS.toml",
                Some(CHOSEN_TEMPLATE),
                "count",
                mutation,
                imp_options(20),
            );
            assert!(!ok, "{side}");
            assert_eq!(document["stopped"], "refused", "{side}: {document:#}");
            let refusal = &document["job"]["refusal"];
            assert_eq!(refusal["stage"], "exclusions", "{side}: {document:#}");
            assert_eq!(refusal["reason"], "implementation-chosen-hook");
            assert!(
                refusal["detail"]
                    .as_str()
                    .unwrap()
                    .contains("MAP.keys_list"),
                "{refusal:#}"
            );
            assert_eq!(document["job"]["status"], status, "{side}");
            assert_eq!(document["job"]["reason"], reason, "{side}");
            assert_eq!(
                document["job"]["exclusions"][side]["exclusion"],
                "implementation-chosen-hook"
            );
            assert_eq!(document["attempts"], serde_json::json!([]));
            // kink's own run gives the same status and reason.
            let (manifest, mutations) = (dir.join("FLOW.toml"), dir.join("MUTATIONS.toml"));
            let cache = scratch(&format!("chosen-{side}-cache"));
            let (run, _) = on_stack(move || {
                kink_flow::cli::run(
                    &manifest,
                    &mutations,
                    &RunOptions {
                        cache: Some(cache),
                        ..RunOptions::default()
                    },
                )
            });
            let row = &run["mutations"][0];
            assert_eq!(row["status"], status, "{side}: {run:#}");
            assert_eq!(row["reason"], reason, "{side}: {run:#}");
            if side == "baseline" {
                assert!(
                    run["programs"][0]["cause"]
                        .as_str()
                        .unwrap()
                        .contains("implementation-chosen-hook"),
                    "{run:#}"
                );
            }
        }
    }

    /// The up-front assembly check (design 3.2.5): kink assembles both sides' inputs from the
    /// baseline, so a mutation of a `[macro]` rule that changes how the template parses would be
    /// judged on an input kink never runs; it is refused before any case. A mutation of another
    /// rule on the same template gives a witness whose assembly matches kink's.
    #[test]
    #[ignore = "kink"]
    fn a_macro_edit_that_changes_the_templates_parse_is_refused_before_any_case() {
        let dir = scratch_flow(
            "macro",
            "mac.k",
            MACRO_SPEC,
            "[spec]\nentry = \"mac.k\"\nmain_module = \"MAC\"\nsyntax_module = \
             \"MAC-SYNTAX\"\n\n[[program]]\nid = \"ten\"\ntext = \"ten + 1\"\n",
            "[[mutation]]\nid = \"ten-is-eleven\"\n  [[mutation.edit]]\n  rule = \"MAC.ten\"\n  find \
             = \"10\"\n  replace = \"11\"\n\n[[mutation]]\nid = \"plus-becomes-minus\"\n  \
             [[mutation.edit]]\n  rule = \"MAC.plus\"\n  find = \"I1 +Int I2\"\n  replace = \"I1 -Int \
             I2\"\n",
        );
        let templates = "[[template]]\nid = \"ten\"\nprogram = \"ten\"\n[[template.hole]]\nname = \
                         \"N\"\nsort = \"Int\"\nfind = \"+ 1\"\nliteral = \"1\"\nrange = { min = 0, \
                         max = 9 }\n";
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(templates),
            "ten",
            "ten-is-eleven",
            imp_options(20),
        );
        assert!(!ok, "{document:#}");
        let refusal = &document["job"]["refusal"];
        assert_eq!(refusal["stage"], "assembly", "{document:#}");
        assert_eq!(refusal["reason"], "mutant-assembly-differs");
        assert!(
            refusal["detail"]
                .as_str()
                .unwrap()
                .contains("the mutant parses the template differently from kink's input")
        );
        let assembly = &document["assembly"];
        assert_ne!(assembly["baseline_anchor"], assembly["mutant_anchor"]);
        assert_eq!(
            assembly["baseline_anchor"],
            assembly["kink_template"]["sha256"]
        );
        assert_eq!(document["attempts"], serde_json::json!([]));
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(templates),
            "ten",
            "plus-becomes-minus",
            imp_options(20),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        assert_eq!(
            document["attempts"][0]["candidate"]["assembly"]["status"],
            "match"
        );
    }

    /// The per-candidate assembly check (design 3.2.5): a witness's sides start from kink's
    /// assembly of its program; a hand-altered initial configuration, one that is no KORE, and a
    /// program kink refuses are each caught.
    #[test]
    #[ignore = "kink"]
    fn a_hand_altered_initial_configuration_is_an_assembly_mismatch() {
        let dir = flow("fuzz/imp");
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            "straight-holes",
            "add-becomes-sub",
            imp_options(50),
        );
        assert!(ok, "{document:#}");
        let mut candidate = document["attempts"][0]["candidate"].clone();
        assert_eq!(candidate["assembly"]["status"], "match", "{candidate:#}");
        let object = candidate.as_object_mut().unwrap();
        object.remove("case");
        object.remove("assembly");
        let case: k_rust_fuzz::report::WitnessCase = serde_json::from_value(candidate).unwrap();
        let mut text = fs::read_to_string(dir.join("FLOW.toml")).unwrap();
        text.push('\n');
        text.push_str(document["program"]["fragment"].as_str().unwrap());
        let program = FlowManifest::decode(&text, &dir)
            .unwrap()
            .programs
            .pop()
            .unwrap();
        let ProgramSource::Text(program_text) = program.source.clone() else {
            panic!("the fragment's program is inline");
        };
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let checks = on_stack(move || {
            let (_, admitted) = kink_flow::admit_spec(&manifest);
            let (spec, mut inputs) = admitted.expect("the specification is admitted");
            let mut check = |case: &k_rust_fuzz::report::WitnessCase, text: &str| {
                check_assembly(&spec, &mut inputs, &program, text, case)
            };
            let unchanged = check(&case, &program_text);
            // The mutant's input with `x = 5` read as `x = 6`.
            let mut altered = case.clone();
            let five = r#"\dv{SortInt{}}("5")"#;
            assert!(altered.sides[1].initial_configuration.contains(five));
            altered.sides[1].initial_configuration = altered.sides[1]
                .initial_configuration
                .replacen(five, r#"\dv{SortInt{}}("6")"#, 1);
            let one_side = check(&altered, &program_text);
            let mut garbled = case.clone();
            garbled.sides[0].initial_configuration = "not KORE".into();
            let unparsed = check(&garbled, &program_text);
            let refused = check(&case, "int x; x = ;");
            (unchanged, one_side, unparsed, refused)
        });
        assert_eq!(checks.0, AssemblyCheck::Match);
        assert!(
            matches!(&checks.1, AssemblyCheck::Mismatch { sides, .. } if sides == &["mutant"]),
            "{:?}",
            checks.1
        );
        assert!(
            matches!(&checks.2, AssemblyCheck::Mismatch { sides, detail }
                if sides == &["baseline"] && detail.contains("does not parse as KORE")),
            "{:?}",
            checks.2
        );
        assert!(
            matches!(&checks.3, AssemblyCheck::Refused { reason, .. } if reason == "parse"),
            "{:?}",
            checks.3
        );
    }

    /// A Markdown template without `start_sort` takes kink's default (`program_start_position` of
    /// `$PGM`'s sort, design 3.1, review S4): it parses, and the witness's input is kink's.
    #[test]
    #[ignore = "kink"]
    fn a_markdown_template_without_start_sort_parses() {
        let templates = "[[template]]\nid = \"add\"\ntext = \"1 + 2\"\n[[template.hole]]\nname = \
                         \"B\"\nsort = \"Int\"\nfind = \"+ 2\"\nliteral = \"2\"\nrange = { min = 0, max \
                         = 9 }\n";
        let (document, ok) = fuzz_kill(
            &flow("markdown"),
            "MUTATIONS.toml",
            Some(templates),
            "add",
            "add-becomes-sub",
            imp_options(20),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["template"]["start_sort_source"], "default");
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        assert_eq!(
            document["attempts"][0]["candidate"]["assembly"]["status"],
            "match"
        );
        assert!(
            !document["program"]["fragment"]
                .as_str()
                .unwrap()
                .contains("start_sort")
        );
    }

    /// A template on a definition that reads standard input (stock SIMPLE) and binds no `$STDIN`
    /// assembles as kink's program does: the campaign binds `$STDIN` to empty input, as kink does,
    /// where k-rust-fuzz's own default is krun's buffered `"\n"`, which made every such job a
    /// `template-assembly-differs` refusal (INT9 review K2). The fragment does not print the
    /// binding, which kink's default gives the program anyway. A template that binds `$STDIN`
    /// itself keeps kink's order (its binding, then `$IO`'s default) and also assembles as kink's.
    #[test]
    #[ignore = "kink"]
    fn a_template_without_stdin_on_a_stream_definition_assembles_as_kinks() {
        let spec =
            fs::read_to_string(repository().join("testdata/k/runlist/simple-untyped.md")).unwrap();
        let manifest = "[spec]\nentry = \"simple-untyped.md\"\nmain_module = \"SIMPLE-UNTYPED\"\n\
                        syntax_module = \"SIMPLE-UNTYPED-SYNTAX\"\n\n[[program]]\nid = \"add\"\n\
                        text = 'function main() { var x; x = 1 + 2; }'\n\n[[program]]\nid = \
                        \"add-stdin\"\ntext = 'function main() { var x; x = 1 + 2; }'\nvariables = \
                        { STDIN = '\"\"' }\n";
        let mutations = "[[mutation]]\nid = \"add-becomes-sub\"\nnote = \"addition subtracts\"\n\
                         [[mutation.edit]]\nline = 603\nfind = \"I1 +Int I2\"\nreplace = \"I1 -Int \
                         I2\"\n";
        let hole = "[[template.hole]]\nname = \"A\"\nsort = \"Int\"\nfind = \"1 + 2\"\nliteral = \
                    \"1\"\nrange = { min = 0, max = 3 }\n";
        let templates = format!(
            "[[template]]\nid = \"add-holes\"\nprogram = \"add\"\n{hole}[[template]]\nid = \
             \"add-stdin-holes\"\nprogram = \"add-stdin\"\n{hole}"
        );
        let dir = scratch_flow("stdin", "simple-untyped.md", &spec, manifest, mutations);
        for (template, prints_stdin) in [("add-holes", false), ("add-stdin-holes", true)] {
            let (document, ok) = fuzz_kill(
                &dir,
                "MUTATIONS.toml",
                Some(&templates),
                template,
                "add-becomes-sub",
                imp_options(20),
            );
            assert!(ok, "{template}: {document:#}");
            assert_eq!(document["stopped"], Value::Null, "{template}: {document:#}");
            assert_eq!(
                document["attempts"][0]["candidate"]["assembly"]["status"], "match",
                "{template}: {document:#}"
            );
            assert_eq!(
                document["program"]["fragment"]
                    .as_str()
                    .unwrap()
                    .contains("STDIN"),
                prints_stdin,
                "{template}: {document:#}"
            );
        }
    }

    /// The reach job (T5) finds a program whose comparable all-paths run applies `big` (`--fired`:
    /// `dbl(X) > 10`, so `X >= 6`), and kink's own `results`, with the fragment appended, lists
    /// it in the rule's `fired_by`; without `--fired` any program reaches `big`'s condition. The
    /// same seed gives the same document.
    #[test]
    #[ignore = "kink"]
    fn reach_finds_a_program_kinks_results_confirm() {
        let dir = steps_flow("reach");
        let fired = || {
            run_job(
                &dir,
                STEPS_TEMPLATES,
                "run-holes",
                Job::Reach("big".into(), true),
                imp_options(40),
            )
        };
        let (document, ok) = fired();
        assert!(ok, "{document:#}");
        assert_eq!(
            document["stopped"],
            Value::Null,
            "{:#}\n{:#}",
            document["attempts"][0]["fuzz"]["totals"],
            document["attempts"][0]["fuzz"]["outcome"]
        );
        assert_eq!(document["job"]["kind"], "reach");
        assert_eq!(document["job"]["rule"]["mode"], "covered");
        assert_eq!(
            document["job"]["rule"]["label"], "STEPS.big",
            "{document:#}"
        );
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        let candidate = &document["attempts"][0]["candidate"];
        assert_eq!(candidate["assembly"]["status"], "match", "{candidate:#}");
        assert_eq!(candidate["comparable"]["holds"], true, "{candidate:#}");
        let x = candidate["holes"][0]["k-text"].as_str().unwrap_or_default();
        assert!(x.parse::<i64>().is_ok_and(|x| x >= 6), "{candidate:#}");
        assert_eq!(fired().0, document, "the same seed gives the same document");
        let by_line = run_job(
            &dir,
            STEPS_TEMPLATES,
            "run-holes",
            Job::Reach(format!("steps.k:{}", steps_line("rule [small]")), false),
            imp_options(5),
        );
        assert!(by_line.1, "{:#}", by_line.0);
        assert_eq!(by_line.0["job"]["rule"]["label"], "STEPS.small");
        assert_eq!(by_line.0["job"]["rule"]["mode"], "condition-reached");

        append_fragment(&dir, &document);
        let id = document["program"]["id"].as_str().unwrap().to_owned();
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let cache = dir.join("cache");
        let (results, ok) = on_stack(move || {
            results(
                &manifest,
                &ResultsOptions {
                    cache: Some(cache),
                    ..ResultsOptions::default()
                },
            )
        });
        assert!(ok, "{results:#}");
        let big = results["rules"]
            .as_array()
            .unwrap()
            .iter()
            .find(|rule| rule["label"] == "STEPS.big")
            .unwrap();
        assert!(
            big["fired_by"]
                .as_array()
                .unwrap()
                .iter()
                .any(|p| p == id.as_str()),
            "{big:#}"
        );
    }

    /// The reach job refuses a rule it cannot target before any campaign: a macro has no
    /// coverage signal, a function rule compiles to equations, a line between rules and an
    /// unknown label name no rule.
    #[test]
    #[ignore = "kink"]
    fn reach_refuses_what_kink_cannot_list() {
        let dir = steps_flow("reach-refusals");
        for (rule, reason) in [
            (
                format!("steps.k:{}", steps_line("rule seven()")),
                "no-coverage-signal",
            ),
            (
                format!("steps.k:{}", steps_line("rule dbl(")),
                "equation-target",
            ),
            (
                format!("steps.k:{}", steps_line("rule [go]") + 1),
                "no-rule-at-line",
            ),
            ("nope".to_owned(), "unknown-label"),
        ] {
            let (document, ok) = run_job(
                &dir,
                STEPS_TEMPLATES,
                "run-holes",
                Job::Reach(rule.clone(), false),
                imp_options(5),
            );
            assert!(!ok, "{rule}");
            assert_eq!(
                document["job"]["refusal"]["reason"], reason,
                "{rule}: {document:#}"
            );
            assert_eq!(
                document["attempts"],
                Value::Array(Vec::new()),
                "{rule}: no campaign ran"
            );
        }
    }

    /// A reach job on a definition with an unnamed finding is not comparable, as a kill is
    /// (Sebastien, D33); naming the findings gives a witness.
    #[test]
    #[ignore = "kink"]
    fn reach_on_a_findings_repro_needs_its_names() {
        let dir = flow("findings/r3-plainq");
        let rule = || Job::Reach("spec.k:11".into(), false);
        let (strict, ok) = run_job(&dir, REPRO_TEMPLATE, "go", rule(), FuzzOptions::default());
        assert!(!ok);
        assert_eq!(strict["stopped"], "not-comparable", "{strict:#}");
        let names = strict["findings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|f| f["name"].as_str().unwrap().to_owned())
            .collect::<BTreeSet<_>>();
        let (named, ok) = run_job(
            &dir,
            REPRO_TEMPLATE,
            "go",
            rule(),
            FuzzOptions {
                assume_joined: names.into_iter().collect(),
                ..FuzzOptions::default()
            },
        );
        assert!(ok, "{named:#}");
        assert_eq!(named["stopped"], Value::Null, "{named:#}");
        assert!(!named["program"]["premises"].as_array().unwrap().is_empty());
    }

    /// The pattern job (T5) finds a program reaching a configuration that matches (`step(V)`
    /// with `V > 14`, so `X >= 8`), at any state (the configuration is not the run's end), and kink's own `query`, with the fragment
    /// appended and claimed, confirms the claim; an invalid pattern is refused by kink's compiler
    /// before any campaign.
    #[test]
    #[ignore = "kink"]
    fn pattern_finds_a_program_kinks_query_confirms() {
        let dir = steps_flow("pattern");
        let patterns = "[[pattern]]\nid = \"big-step\"\npattern = \"<k> step(V) </k> requires V \
                        >Int 14\"\n\n[[pattern]]\nid = \"broken\"\npattern = \"<k> step( </k>\"\n";
        let list = PatternList::decode(patterns).unwrap();
        let (document, ok) = run_job(
            &dir,
            STEPS_TEMPLATES,
            "run-holes",
            Job::Pattern(list.clone(), "big-step".into()),
            imp_options(40),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["job"]["kind"], "pattern");
        assert_eq!(document["assumed"], Value::Array(Vec::new()));
        assert!(
            document["job"]["pattern"]["kore"].is_string(),
            "{document:#}"
        );
        let candidate = &document["attempts"][0]["candidate"];
        assert_eq!(candidate["assembly"]["status"], "match", "{candidate:#}");
        assert!(candidate["reaching"]["step"].is_u64(), "{candidate:#}");
        let (broken, ok) = run_job(
            &dir,
            STEPS_TEMPLATES,
            "run-holes",
            Job::Pattern(list, "broken".into()),
            imp_options(5),
        );
        assert!(!ok);
        assert_eq!(
            broken["job"]["refusal"]["reason"], "invalid-pattern",
            "{broken:#}"
        );
        assert_eq!(broken["attempts"], Value::Array(Vec::new()));

        append_fragment(&dir, &document);
        let id = document["program"]["id"].as_str().unwrap().to_owned();
        let claimed = format!(
            "[[pattern]]\nid = \"big-step\"\npattern = \"<k> step(V) </k> requires V >Int 14\"\n\
             programs = [\"{id}\"]\n"
        );
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let claimed = PatternList::decode(&claimed).unwrap();
        let cache = dir.join("cache");
        let (answers, _) = on_stack(move || {
            query(
                &manifest,
                &claimed,
                &QueryOptions {
                    cache: Some(cache),
                    ..QueryOptions::default()
                },
            )
        });
        let row = answers["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["program"] == id.as_str())
            .unwrap_or_else(|| panic!("{answers:#}"));
        assert_eq!(row["claim"], "confirmed", "{row:#}");
    }

    /// The last `run` document (read from `--cache`, never written by `fuzz`): no document, then
    /// the mutation's reaching programs suggested as templates with a warning for a template outside
    /// them, and a warning for a template whose program is not comparable; `--time-limit-ms` warns
    /// that it does not bound the campaign's setup.
    #[test]
    #[ignore = "kink"]
    fn the_last_run_suggests_reaching_templates_and_warns() {
        let dir = flow("fuzz/imp");
        let cache = scratch("imp-cache");
        let options = |cases| FuzzOptions {
            cache: Some(cache.clone()),
            ..imp_options(cases)
        };
        let (document, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            "straight-holes",
            "div-becomes-mul",
            options(1),
        );
        assert_eq!(document["template"]["last_run"]["found"], false);
        assert!(warning_kinds(&document).is_empty(), "{document:#}");
        let (manifest, mutations, run_cache) = (
            dir.join("FLOW.toml"),
            dir.join("MUTATIONS.toml"),
            cache.clone(),
        );
        let (run, _) = on_stack(move || {
            kink_flow::cli::run(
                &manifest,
                &mutations,
                &RunOptions {
                    only: vec!["div-becomes-mul".into()],
                    cache: Some(run_cache),
                    ..RunOptions::default()
                },
            )
        });
        let row = &run["mutations"][0];
        // primes's run on the mutant is not comparable (the `unknown` survivor TRIAL2 killed).
        assert_eq!(row["status"], "unknown", "{run:#}");
        let reaching = row["reaching"].clone();
        assert!(
            reaching.as_array().unwrap().iter().any(|id| id == "primes"),
            "{row:#}"
        );
        // straight.imp divides nothing: the reaching programs are suggested instead.
        let (document, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            "straight-holes",
            "div-becomes-mul",
            options(1),
        );
        let last_run = &document["template"]["last_run"];
        assert_eq!(last_run["current"], true, "{last_run:#}");
        assert_eq!(last_run["mutation"]["status"], "unknown");
        assert_eq!(last_run["mutation"]["reaching"], reaching);
        assert!(
            last_run["suggested_templates"][0]["template"]
                .as_str()
                .unwrap()
                .starts_with("[[template]]\n")
        );
        assert_eq!(warning_kinds(&document), ["template-not-reaching"]);
        // primes reaches the rule; read as a timeout, its template is warned as unusable.
        let path = cache.join("report.json");
        let mut stored: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        for program in stored["programs"].as_array_mut().unwrap() {
            if program["id"] == "primes" {
                program["class"] = "timeout".into();
                program["cause"] = "a doctored class".into();
            }
        }
        fs::write(&path, serde_json::to_string(&stored).unwrap()).unwrap();
        let (document, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            "primes-holes",
            "div-becomes-mul",
            FuzzOptions {
                time_limit_ms: Some(0),
                ..options(1)
            },
        );
        assert_eq!(
            document["template"]["last_run"]["template"]["class"],
            "timeout"
        );
        assert_eq!(
            warning_kinds(&document),
            ["time-limit-scope", "unusable-template"],
            "{document:#}"
        );
    }
}
