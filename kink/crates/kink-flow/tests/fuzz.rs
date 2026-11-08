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
//! - the campaign reads a configuration variable's text as kink does: on a `tokens.k`-shaped
//!   definition a template binding `$W` and the `K` variable `$V` to `word` (a `Word` only the
//!   syntax module's grammar reads) assembles as kink's before any case (light), and is fuzzed,
//!   its witness matching kink's assembly and confirmed;
//! - the last `run` document gives the template's class, the mutation's witnesses as
//!   suggested templates, and the warnings.

use kink_corpus::ProgramSource;
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, execute},
    coverage::CoverageOptions,
    fuzz::{
        AssemblyCheck, FuzzJob, FuzzOptions, TemplateList, TemplateSource, check_assembly,
        compiled_side, confirm_program, fuzz_job, kill,
    },
    pattern::PatternList,
    query::{QueryOptions, query},
    resolve,
    search::RunOptions,
};
use serde_json::Value;
use std::{
    collections::BTreeSet,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
};

mod flow_support;

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
    // Confirmation (KF-T4) is the default; --no-confirm turns it off, and there is no seed retry.
    for extra in [
        // One job per command.
        &["--no-confirm", "--matched", "imp.k:47"][..],
        &["--no-confirm", "--attempts", "3"],
        &["--no-confirm", "--cases", "0"],
        &["--no-confirm", "--cases", "3", "--work", "9"],
    ] {
        let args = base.iter().chain(extra).copied().collect::<Vec<_>>();
        assert_eq!(run_cli(&args), EXIT_UNASKED, "{extra:?}");
    }
    // The rule and pattern jobs (T5) parse; a pattern job takes no assumed name (front_end.rs
    // pins the rule job each flag parses to, and the usage errors of `--reach` and of two jobs).
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
        EXIT_UNASKED
    );
    assert_eq!(
        job(&["--pattern", "q", "--patterns", patterns]),
        EXIT_UNASKED
    );
    assert_eq!(job(&["--pattern", "p"]), EXIT_UNASKED);
    assert_eq!(
        job(&["--fired", "imp.k:47", "--mutations", mutations]),
        EXIT_UNASKED
    );
    assert_eq!(job(&["--fired"]), EXIT_UNASKED);
    let mut unknown = base.to_vec();
    unknown[4] = "no-such-template";
    unknown.push("--no-confirm");
    assert_eq!(run_cli(&unknown), EXIT_UNASKED);
    let mut unknown = base.to_vec();
    unknown[6] = "no-such-mutation";
    unknown.push("--no-confirm");
    assert_eq!(run_cli(&unknown), EXIT_UNASKED);
}

/// R2-REFRESH's M2 probe: every end holds a non-ASCII string, a domain value kink's end check
/// refuses and k-rust's data judgement accepts.
const NA_K: &str = "module NA-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int)
endmodule

module NA
  imports NA-SYNTAX
  imports INT
  imports STRING
  configuration <k> $PGM:Pgm </k> <out> \"\" </out>
  rule <k> go(I) => .K </k> <out> _ => \"\u{e9}\" +String Int2String(I) </out>
endmodule
";
const NA_FLOW: &str = "[spec]\nentry = \"na.k\"\nmain_module = \"NA\"\nsyntax_module = \
                       \"NA-SYNTAX\"\n\n[[program]]\nid = \"one\"\ntext = \"go(1)\"\n";
const NA_MUTATIONS: &str = "[[mutation]]\nid = \"plus-one\"\nmisunderstanding = \"a test mutation\"\n[[mutation.edit]]\nline = 11\nfind = \
                            \"Int2String(I)\"\nreplace = \"Int2String(I +Int 1)\"\n";
const NA_TEMPLATES: &str = "[[template]]\nid = \"one-holes\"\nprogram = \"one\"\n\
                            [[template.hole]]\nname = \"I\"\nsort = \"Int\"\nfind = \"go(1)\"\n\
                            literal = \"1\"\nrange = { min = 0, max = 3 }\n";

/// Every path under `dir` with its size, sorted.
fn listing(dir: &Path) -> Vec<(PathBuf, u64)> {
    let mut entries = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(next) = stack.pop() {
        for entry in fs::read_dir(&next).unwrap() {
            let entry = entry.unwrap();
            let metadata = entry.metadata().unwrap();
            if metadata.is_dir() {
                stack.push(entry.path());
            }
            entries.push((entry.path(), metadata.len()));
        }
    }
    entries.sort();
    entries
}

/// A small definition for the rule and pattern jobs (T5): `run(X)` steps to `step(dbl(X))`,
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
        Job::Rule(rule, fired) => fuzz_job(
            &manifest,
            &templates,
            &template,
            FuzzJob::Rule {
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
    Rule(String, bool),
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

/// A definition of the shape of `testdata/corpus/tokens.k`, written out here on its own (its
/// program takes an `Int`, it binds a `K` variable `$V` as well, and it has a rule): a token sort
/// of the syntax module (`Word`) and one of the main module (`Name`) whose regex the main
/// module's scanner prefers for `word`. `go` fires only when `$W` and `$V` hold the `Word` `word`
/// and the program's integer is above 5, so a witness exists only where the campaign reads the
/// text `word` of `$W` and of `$V` as kink does, as that `Word`: with the main module's grammar
/// alone `word` does not parse at `Word`, and at `K` it is a `Name`.
const TOKENS_K: &str = r#"
module TOKENS-SYNTAX
  imports INT-SYNTAX
  syntax Word ::= r"w[a-z]*" [token]
  syntax Pgm ::= run(Int) [symbol(run)]
endmodule

module TOKENS
  imports TOKENS-SYNTAX
  imports INT
  imports BOOL
  syntax Name ::= r"wor[a-z]*" [token, prec(2)]
  configuration <k> $PGM:Pgm </k> <w> $W:Word </w> <n> $N:Name </n> <v> $V:K </v>
  rule [go]: <k> run(I) => .K </k> <w> #token("word", "Word") </w>
             <v> #token("word", "Word") </v>
    requires I >Int 5
endmodule
"#;

const TOKENS_MANIFEST: &str = "[spec]\nentry = \"tokens.k\"\nmain_module = \"TOKENS\"\n\
                               syntax_module = \"TOKENS-SYNTAX\"\n\n[[program]]\nid = \
                               \"one\"\ntext = \"run(1)\"\nvariables = { W = \"word\", N = \
                               \"word\", V = \"word\" }\n";

/// The campaign reads a configuration variable's text as kink does (k-rust
/// `variable_reading_modules`, krun's `-c` reading too): on [`TOKENS_K`] the template binds `$W`
/// and the `K` variable `$V` to `word`, a `Word` only the syntax module's grammar reads there, so
/// a run of no case passes the up-front assembly checks: kink assembles the template, and the
/// campaign baseline's initial configuration at the holes' anchors is kink's assembly.
#[test]
fn a_template_whose_variables_only_the_syntax_module_reads_assembles_as_kinks() {
    let dir = scratch_flow("tokens-assembly", "tokens.k", TOKENS_K, TOKENS_MANIFEST, "");
    let (document, _) = run_job(
        &dir,
        TOKENS_TEMPLATES,
        "run-holes",
        Job::Rule("go".into(), true),
        FuzzOptions {
            filter: false,
            ..imp_options(0)
        },
    );
    assert_eq!(document["job"]["refusal"], Value::Null, "{document:#}");
    let assembly = &document["assembly"];
    let kink = &assembly["kink_template"]["sha256"];
    assert!(kink.is_string(), "{assembly:#}");
    assert_eq!(&assembly["baseline_anchor"], kink, "{assembly:#}");
}

/// CF-03: a definition whose short-circuit analysis flags a rule has no definition exclusion for
/// it, since kink's runner judges each of its runs by k-rust's list of that run's short-circuit
/// readings, so a fuzz job of it is no longer refused before any case (`job.exclusions` names none
/// on the baseline), with the witness filter and without it. `at` writes `andThenBool` over
/// `10 /Int I >Int 0` to its output cell, flagged; the template's input `at(1)` applies no
/// function, so the filter's static initial-state check passes it. A case whose step of `at`
/// reads the undefined skipped operand gives no witness; one whose run reads only defined
/// operands is confirmed.
#[test]
fn a_job_of_a_flagged_definition_is_not_refused_up_front() {
    let spec = r"module SCR-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= at(Int) [symbol(at)]
endmodule

module SCR
  imports SCR-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k> <out> true </out>
  rule [at]: <k> at(I) => .K </k> <out> _ => false andThenBool 10 /Int I >Int 0 </out>
endmodule
";
    let manifest = "[spec]\nentry = \"scr.k\"\nmain_module = \"SCR\"\nsyntax_module = \
                    \"SCR-SYNTAX\"\n\n[[program]]\nid = \"one\"\ntext = \"at(1)\"\n";
    let dir = scratch_flow("short-circuit-job", "scr.k", spec, manifest, "");
    let templates = "[[template]]\nid = \"at-holes\"\nprogram = \"one\"\n\
                     [[template.hole]]\nname = \"N\"\nsort = \"Int\"\nfind = \"at(1)\"\n\
                     literal = \"1\"\nrange = { min = 0, max = 3 }\n";
    for filter in [true, false] {
        let (document, _) = run_job(
            &dir,
            templates,
            "at-holes",
            Job::Rule("at".into(), true),
            FuzzOptions {
                filter,
                ..imp_options(0)
            },
        );
        assert_eq!(
            document["job"]["refusal"],
            Value::Null,
            "filter {filter}: {document:#}"
        );
        assert_eq!(
            document["job"]["exclusions"]["baseline"],
            Value::Null,
            "filter {filter}: {document:#}"
        );
    }
    // The job runs. On `at(0)` the step of `at` is undefined only through the operand
    // `andThenBool` skips, so no run of it reaches the rule as a comparable baseline and the
    // campaign exhausts that domain with no witness (the filter's leaf check of such a step,
    // `short-circuit-step`, is the unit test `fuzz_filter`
    // `an_undefined_step_of_a_short_circuit_rule_is_refused_under_its_sides_facts`). On `at(2)`
    // the run lists no short-circuit reading, and kink's confirmation confirms the witness.
    let only = |value: u32| {
        format!(
            "[[template]]\nid = \"at-holes\"\nprogram = \"one\"\n[[template.hole]]\nname = \
             \"N\"\nsort = \"Int\"\nfind = \"at(1)\"\nliteral = \"1\"\nrange = {{ min = \
             {value}, max = {value} }}\n"
        )
    };
    let rule_job = |templates: &str| {
        run_job(
            &dir,
            templates,
            "at-holes",
            Job::Rule("at".into(), false),
            FuzzOptions {
                confirm: true,
                ..imp_options(4)
            },
        )
        .0
    };
    let undefined = rule_job(&only(0));
    assert_eq!(undefined["stopped"], "domain-exhausted", "{undefined:#}");
    assert_eq!(undefined["program"], Value::Null, "{undefined:#}");
    let confirmed = rule_job(&only(2));
    assert_eq!(confirmed["stopped"], Value::Null, "{confirmed:#}");
    assert_eq!(confirmed["program"]["confirmed"], true, "{confirmed:#}");
}

const TOKENS_TEMPLATES: &str = "[[template]]\nid = \"run-holes\"\nprogram = \"one\"\n\
                                [[template.hole]]\nname = \"X\"\nsort = \"Int\"\nfind = \
                                \"run(1)\"\nliteral = \"1\"\nrange = { min = 0, max = 9 }\n";

/// A template of a corpus program with typed inputs (`inputs`) is refused before any case: a
/// fuzz campaign varies and replays K text only, so it could neither carry the typed inputs into
/// its input nor write them back into a witness's fragment.
#[test]
fn a_template_with_typed_inputs_is_refused() {
    let manifest = "[spec]\nentry = \"steps.k\"\nmain_module = \"STEPS\"\nsyntax_module = \
                    \"STEPS-SYNTAX\"\n\n[[program]]\nid = \"typed\"\ntext = \"run(1)\"\n\
                    inputs = { n = 1 }\n";
    let dir = scratch_flow("typed-template", "steps.k", STEPS_K, manifest, "");
    let (document, ok) = run_job(
        &dir,
        "[[template]]\nid = \"t\"\nprogram = \"typed\"\n",
        "t",
        Job::Rule("big".into(), true),
        FuzzOptions::default(),
    );
    assert!(!ok, "{document:#}");
    let refusal = &document["job"]["refusal"];
    assert_eq!(
        (&refusal["stage"], &refusal["reason"]),
        (&Value::from("template"), &Value::from("template-refused")),
        "{document:#}"
    );
    assert!(
        refusal["detail"]
            .as_str()
            .unwrap()
            .starts_with("program \"typed\" has typed inputs (`inputs`)"),
        "{document:#}"
    );
}

/// Under the Z3 profile the fuzz document names the Z3 build its confirmations are decided on
/// (`z3`), whatever the outcome: a job refused before any case and the document of an input that
/// does not decode; under the portable profile neither names a Z3 build.
#[test]
fn the_fuzz_document_names_the_z3_build_under_the_z3_profile() {
    let z3 = flow_support::z3_member();
    let manifest = "[spec]\nentry = \"steps.k\"\nmain_module = \"STEPS\"\nsyntax_module = \
                    \"STEPS-SYNTAX\"\n\n[[program]]\nid = \"typed\"\ntext = \"run(1)\"\n\
                    inputs = { n = 1 }\n";
    let dir = scratch_flow("z3-build", "steps.k", STEPS_K, manifest, "");
    let (document, ok) = run_job(
        &dir,
        "[[template]]\nid = \"t\"\nprogram = \"typed\"\n",
        "t",
        Job::Rule("big".into(), true),
        FuzzOptions::default(),
    );
    assert!(!ok, "{document:#}");
    assert_eq!(document.get("z3"), z3.as_ref(), "{document:#}");
    let refused = kink_flow::fuzz::input_refused("TEMPLATES.toml", &"invalid TOML");
    assert_eq!(refused.get("z3"), z3.as_ref(), "{refused:#}");
}

/// A template's own `file` or `text` is read as admission reads a program's, through the front
/// end's decoder (`InputDecoder::program`), so it binds what the same text as a `[[program]]`
/// binds: one the front end binds to another variable than `$PGM` is refused before any case,
/// since fuzz varies `$PGM` text only.
#[test]
fn a_template_the_front_end_binds_otherwise_is_refused() {
    struct EntryDecoder;
    impl kink_flow::InputDecoder for EntryDecoder {
        fn decode(
            &self,
            name: &str,
            _: &toml::Value,
            _: &mut dyn kink_flow::InputFiles,
        ) -> Result<(String, k_rust::kast::Term), String> {
            Err(format!("no typed input {name}"))
        }

        fn program(
            &self,
            _: Option<&str>,
            bytes: &[u8],
        ) -> Option<Result<kink_flow::ProgramBinding, String>> {
            Some(Ok(kink_flow::ProgramBinding::Text {
                variable: "ENTRY".into(),
                text: String::from_utf8(bytes.to_vec()).unwrap(),
            }))
        }
    }
    let manifest = "[spec]\nentry = \"steps.k\"\nmain_module = \"STEPS\"\nsyntax_module = \
                    \"STEPS-SYNTAX\"\n\n[[program]]\nid = \"one\"\ntext = \"run(1)\"\n";
    let dir = scratch_flow("entry-template", "steps.k", STEPS_K, manifest, "");
    fs::write(dir.join("t.txt"), "run(1)").unwrap();
    let templates = TemplateList::decode(
        "[[template]]\nid = \"text\"\ntext = \"run(1)\"\n\n[[template]]\nid = \"file\"\nfile = \
         \"t.txt\"\n",
        &dir,
    )
    .unwrap();
    let manifest = FlowManifest::read(&dir.join("FLOW.toml"))
        .unwrap()
        .with_input_decoder(std::sync::Arc::new(EntryDecoder));
    for (template, described) in [
        ("text", "the template's text"),
        ("file", "the template's file t.txt"),
    ] {
        let (document, ok) = {
            let manifest = manifest.clone();
            let templates = templates.clone();
            on_stack(move || {
                fuzz_job(
                    &manifest,
                    &templates,
                    template,
                    FuzzJob::Rule {
                        rule: "big",
                        fired: true,
                    },
                    &FuzzOptions::default(),
                )
            })
        };
        assert!(!ok, "{document:#}");
        let refusal = &document["job"]["refusal"];
        assert_eq!(
            (&refusal["stage"], &refusal["reason"]),
            (&Value::from("template"), &Value::from("template-refused")),
            "{document:#}"
        );
        assert_eq!(
            refusal["detail"],
            format!(
                "{described} binds $ENTRY as the front end reads its program, which fuzz does not \
                 carry yet: fuzz varies $PGM text, so use a template that binds every input as K \
                 text under `variables`"
            ),
            "{document:#}"
        );
    }
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
  imports BYTES
  imports STRING
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

/// The K that `krs emit-k` writes for the introduction's story (`docs-site/story/plus`), less its
/// header and `// KRS` comments: natural numbers whose programs are written in `Nat` itself, and
/// `plus`, declared `total`, defined by `plus_zero` and `plus_succ`.
const STORY_K: &str = r#"
module KRS-FRAMEWORK
  syntax KItem
  syntax KResult
  syntax KItem ::= KResult
endmodule
module NAT-SYNTAX
  imports KRS-FRAMEWORK
  syntax Nat
  syntax Nat ::= "s" "(" Nat ")" [symbol(natSyntaxSucc), group(krsgroup-ed0b6ff63cf0cba2ebb2a364), format(%1%2%3%4)]
  syntax Nat ::= "zero" [symbol(natSyntaxZero), group(krsgroup-ed0b6ff63cf0cba2ebb2a364), format(%1)]
  syntax Nat ::= "plus" "(" Nat "," Nat ")" [symbol(plus), function, total]
endmodule
module NAT
  imports KRS-FRAMEWORK
  imports NAT-SYNTAX
  syntax KItem ::= Nat
  configuration
    <k> $PGM:Nat </k>
  rule plus ( s ( M:Nat ) , N:Nat ) => s ( plus ( M:Nat , N:Nat ) ) [label(nat--plus_succ)]
  rule plus ( zero , N:Nat ) => N:Nat [label(nat--plus_zero)]
endmodule
"#;

/// The story's corpus: `t1` and `t2` apply only `plus_zero`, `t3` and `t4` `plus_succ` too.
const STORY_MANIFEST: &str = r#"[spec]
entry = "story.k"
main_module = "NAT"
syntax_module = "NAT-SYNTAX"

[[program]]
id = "t1"
text = "plus(zero, zero)"

[[program]]
id = "t2"
text = "plus(zero, s(zero))"

[[program]]
id = "t3"
text = "plus(s(zero), s(zero))"

[[program]]
id = "t4"
text = "plus(s(s(zero)), s(zero))"
"#;

/// The story guide's survivor `survivors/one`, an edit of `plus_succ` alone, which every case of
/// [`STORY_MANIFEST`] leaves alive: their recursive calls pass `s(zero)` already.
const STORY_MUTATIONS: &str = r#"[[mutation]]
id = "one"
note = "passes one instead of n to the recursive call"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "s ( plus ( M:Nat , N:Nat ) )"
  replace = "s ( plus ( M:Nat , s ( zero ) ) )"
"#;

/// A hole over the second argument of `t4` and one of `t2`, each a `Nat`: the sort programs are
/// written in, which only the override admits.
const STORY_TEMPLATES: &str = r#"[[template]]
id = "t4-second"
program = "t4"

  [[template.hole]]
  name = "B"
  sort = "Nat"
  find = ", s(zero))"
  literal = "s(zero)"
  allow-refused-sort = true

[[template]]
id = "t2-second"
program = "t2"

  [[template.hole]]
  name = "B"
  sort = "Nat"
  find = ", s(zero))"
  literal = "s(zero)"
  allow-refused-sort = true
"#;

mod kink_tier {
    use super::*;

    /// A mutant's `witnesses` are the programs whose coverage reaches a sentence the author's
    /// edit changes: kink withdraws `plus`'s `total` from the mutant of a `plus_succ` edit (the
    /// row's `removed_claims` still says so), and that withdrawal adds no witness through a
    /// program's coverage, so `t1` and `t2`, which apply only `plus_zero`, are not witnesses.
    /// `fuzz` warns from the same set. A hole of the program sort `Nat` with
    /// `allow-refused-sort = true` is then fuzzed, not refused again where its values are built,
    /// and the template on the witness `t4` kills the survivor.
    #[test]
    #[ignore = "kink"]
    fn a_story_survivor_is_witnessed_by_its_edit_and_fuzzed_through_a_nat_hole() {
        let dir = scratch_flow("story", "story.k", STORY_K, STORY_MANIFEST, STORY_MUTATIONS);
        let cache = scratch("story-cache");
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
                    schedule: kink_campaign::ScheduleMode::Full,
                    cache: Some(run_cache),
                    ..RunOptions::default()
                },
            )
        });
        let row = &run["mutations"][0];
        assert_eq!(row["status"], "survived", "{run:#}");
        assert_eq!(row["witnesses"], serde_json::json!(["t3", "t4"]), "{row:#}");
        let removed = row["removed_claims"].to_string();
        assert!(removed.contains("total"), "{row:#}");

        let options = || FuzzOptions {
            cache: Some(cache.clone()),
            ..imp_options(50)
        };
        let (document, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(STORY_TEMPLATES),
            "t2-second",
            "one",
            FuzzOptions {
                budget: k_rust_fuzz::Budget::Cases(1),
                ..options()
            },
        );
        assert_eq!(document["job"]["refusal"], Value::Null, "{document:#}");
        assert_eq!(
            document["template"]["last_run"]["mutation"]["witnesses"],
            serde_json::json!(["t3", "t4"]),
            "{document:#}"
        );
        let warning = document["warnings"]
            .as_array()
            .unwrap()
            .iter()
            .find(|warning| warning["kind"] == "template-not-a-witness")
            .unwrap_or_else(|| panic!("t2 is no witness: {document:#}"));
        assert!(
            warning["detail"].as_str().unwrap().contains("(t3, t4)"),
            "{warning:#}"
        );

        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(STORY_TEMPLATES),
            "t4-second",
            "one",
            FuzzOptions {
                confirm: true,
                ..options()
            },
        );
        assert!(ok, "{:#}", document["action"]);
        assert_eq!(document["job"]["refusal"], Value::Null, "{document:#}");
        assert!(warning_kinds(&document).is_empty(), "{document:#}");
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        assert_eq!(document["program"]["confirmed"], true, "{document:#}");
        assert_eq!(
            document["template"]["holes"][0]["allow-refused-sort"], true,
            "{document:#}"
        );
    }

    /// A program witnesses a mutation when its baseline run reaches a sentence the mutant
    /// changes, whatever the mutant then does. `no-decrease` edits only `plus_succ`'s result, into
    /// one that reuses its left-hand side's `s(M)` (an alias of the left-hand side in the compiled
    /// rule), and its mutant recurses without end: its witnesses are `t3` and `t4`, never `t1` or
    /// `t2`, which apply only `plus_zero`, and it stays `unknown` with the reason `stack-stop`.
    /// `shifted` edits `plus_succ`'s pattern, which can match terms no baseline run tried, so
    /// every program witnesses it (`witnesses_global`); its result is `plus`'s own value on the
    /// narrowed instances, but not the old result's instance, so it runs, and on `t4` the mutant
    /// ends on `plus(s(zero), zero)`, which none of its equations reduces: the reason is
    /// `open-application`. `fuzz --kill shifted` on a template of `t2` warns `global-witnesses`,
    /// not `template-not-a-witness`: `t2` is a witness by default, not by its coverage.
    #[test]
    #[ignore = "kink"]
    fn a_result_edit_is_witnessed_by_coverage_and_a_pattern_edit_by_every_program() {
        let mutations = r#"[[mutation]]
id = "no-decrease"
note = "recurses on s(M) instead of M"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "s ( plus ( M:Nat , N:Nat ) )"
  replace = "s ( plus ( s ( M:Nat ) , N:Nat ) )"

[[mutation]]
id = "shifted"
note = "narrows the pattern to a nonzero second argument"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "plus ( s ( M:Nat ) , N:Nat ) => s ( plus ( M:Nat , N:Nat ) )"
  replace = "plus ( s ( M:Nat ) , s ( N:Nat ) ) => s ( s ( plus ( M:Nat , N:Nat ) ) )"
"#;
        // `no-decrease` stops at the native stack's bound, a bound on work: the clock never
        // decides a run of the tests (R4-WALLCLOCK), so the budget's time is far above it.
        let manifest = format!(
            "{STORY_MANIFEST}\n[budget]\n# the clock never decides a run of the tests (R4-WALLCLOCK)\ntime_ms = 600000\n"
        );
        let dir = scratch_flow("story-witnesses", "story.k", STORY_K, &manifest, mutations);
        let cache = scratch("story-witnesses-cache");
        let (manifest, list, run_cache) = (
            dir.join("FLOW.toml"),
            dir.join("MUTATIONS.toml"),
            cache.clone(),
        );
        let (run, _) = on_stack(move || {
            kink_flow::cli::run(
                &manifest,
                &list,
                &RunOptions {
                    cache: Some(run_cache),
                    ..RunOptions::default()
                },
            )
        });
        let row = |id: &str| {
            run["mutations"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["id"] == id)
                .unwrap_or_else(|| panic!("no row {id}: {run:#}"))
                .clone()
        };
        let no_decrease = row("no-decrease");
        assert_eq!(no_decrease["status"], "unknown", "{no_decrease:#}");
        assert_eq!(no_decrease["reason"], "stack-stop", "{no_decrease:#}");
        assert_eq!(
            no_decrease["witnesses"],
            serde_json::json!(["t3", "t4"]),
            "{no_decrease:#}"
        );
        assert_eq!(no_decrease["witnesses_global"], false, "{no_decrease:#}");
        let shifted = row("shifted");
        assert_eq!(shifted["status"], "unknown", "{shifted:#}");
        assert_eq!(
            shifted["witnesses"],
            serde_json::json!(["t1", "t2", "t3", "t4"]),
            "{shifted:#}"
        );
        assert_eq!(shifted["witnesses_global"], true, "{shifted:#}");
        assert_eq!(shifted["reason"], "open-application", "{shifted:#}");

        let (document, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(STORY_TEMPLATES),
            "t2-second",
            "shifted",
            FuzzOptions {
                cache: Some(cache.clone()),
                ..imp_options(1)
            },
        );
        let last = &document["template"]["last_run"]["mutation"];
        assert_eq!(last["witnesses_global"], true, "{document:#}");
        let kinds = warning_kinds(&document);
        assert!(kinds.contains(&"global-witnesses"), "{document:#}");
        assert!(!kinds.contains(&"template-not-a-witness"), "{document:#}");
        // The last run left `shifted` unknown with reason open-application: `fuzz` says so before
        // any case.
        assert!(kinds.contains(&"open-application"), "{document:#}");

        // `t4`'s comparable baseline run matches `plus_succ`, so a template of `t4` already is
        // what `global-witnesses` advises: it is not warned, though the witnesses stay global.
        let (document, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(STORY_TEMPLATES),
            "t4-second",
            "shifted",
            FuzzOptions {
                cache: Some(cache.clone()),
                ..imp_options(1)
            },
        );
        let last = &document["template"]["last_run"]["mutation"];
        assert_eq!(last["witnesses_global"], true, "{document:#}");
        let kinds = warning_kinds(&document);
        assert!(!kinds.contains(&"global-witnesses"), "{document:#}");
        assert!(!kinds.contains(&"template-not-a-witness"), "{document:#}");
        assert!(kinds.contains(&"open-application"), "{document:#}");

        // A mutation the last run did not judge (another list): its status and witnesses are
        // unknown here, which `fuzz` says instead of checking them.
        std::fs::write(dir.join("OTHER.toml"), STORY_MUTATIONS).unwrap();
        let (document, _) = fuzz_kill(
            &dir,
            "OTHER.toml",
            Some(STORY_TEMPLATES),
            "t4-second",
            "one",
            FuzzOptions {
                cache: Some(cache.clone()),
                ..imp_options(1)
            },
        );
        assert_eq!(
            document["template"]["last_run"]["mutation"],
            Value::Null,
            "{document:#}"
        );
        let kinds = warning_kinds(&document);
        assert!(kinds.contains(&"last-run-without-mutation"), "{document:#}");
        assert!(!kinds.contains(&"global-witnesses"), "{document:#}");
    }

    /// What kink decides from a mutation's edit, no case can change, so `fuzz --kill` refuses it
    /// before any campaign, exit 2, with the status and reason `run` gives the row and its
    /// action: `requires false` and a narrower pattern are `unkillable` (reason `weakening`), and
    /// `requires isNat ( N:Nat )`, which holds of every `Nat`, keeps `plus_succ`'s axiom, so the
    /// mutant is the specification: `equivalent`, reason `valid-condition`, kind
    /// `valid-condition`. `run --verify` gives each row the reason `run` gives it, the
    /// `stack-stop` of `no-decrease` and the `open-application` of `shifted` included.
    /// `no-decrease` recurses without end on every case that reaches `plus_succ`: `fuzz` warns
    /// `stack-stop` before any case, and ends the search after `--stack-stops` such cases in a
    /// row (`stopped: stack-stops`, exit 3) with the advice of the reason, never a larger budget.
    /// `shifted`'s cases whose second argument is `zero` end on an application of `plus` its
    /// equations leave open, which the campaign cannot judge (`not-ceil-free`): the document
    /// names `plus` in a `not-ceil-free` warning, as its action says; on a template every case of
    /// which ends so, the search ends after `--open-stops` such cases in a row
    /// (`stopped: open-stops`).
    #[test]
    #[ignore = "kink"]
    fn a_decided_mutation_is_refused_and_a_recursion_without_end_ends_the_search() {
        let mutations = r#"[[mutation]]
id = "false"
note = "never applies plus_succ"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "s ( plus ( M:Nat , N:Nat ) )"
  replace = "s ( plus ( M:Nat , N:Nat ) ) requires false"

[[mutation]]
id = "guide-pattern"
note = "plus_succ only for a nonzero second argument"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "plus ( s ( M:Nat ) , N:Nat ) => s ( plus ( M:Nat , N:Nat ) )"
  replace = "plus ( s ( M:Nat ) , s ( N:Nat ) ) => s ( plus ( M:Nat , s ( N:Nat ) ) )"

[[mutation]]
id = "isnat"
note = "a condition every Nat meets"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "s ( plus ( M:Nat , N:Nat ) )"
  replace = "s ( plus ( M:Nat , N:Nat ) ) requires isNat ( N:Nat )"

[[mutation]]
id = "no-decrease"
note = "recurses on s(M) instead of M"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "s ( plus ( M:Nat , N:Nat ) )"
  replace = "s ( plus ( s ( M:Nat ) , N:Nat ) )"

[[mutation]]
id = "shifted"
note = "narrows the pattern to a nonzero second argument"

  [[mutation.edit]]
  rule = "plus_succ"
  find = "plus ( s ( M:Nat ) , N:Nat ) => s ( plus ( M:Nat , N:Nat ) )"
  replace = "plus ( s ( M:Nat ) , s ( N:Nat ) ) => s ( s ( plus ( M:Nat , N:Nat ) ) )"
"#;
        // `no-decrease` stops at the native stack's bound, a bound on work: the clock never
        // decides a run of the tests (R4-WALLCLOCK), so the budget's time is far above it.
        // `t5`'s first argument is nonzero and its second `zero`: every `plus(s(A), zero)` its
        // template makes ends, on `shifted`'s mutant, on an application of `plus` that no
        // equation reduces.
        let manifest = format!(
            "{STORY_MANIFEST}\n[[program]]\nid = \"t5\"\ntext = \"plus(s(s(zero)), zero)\"\n\n[budget]\n# the clock never decides a run of the tests (R4-WALLCLOCK)\ntime_ms = 600000\n"
        );
        let dir = scratch_flow("story-decided", "story.k", STORY_K, &manifest, mutations);
        let cache = scratch("story-decided-cache");
        let (flow, list, run_cache) = (
            dir.join("FLOW.toml"),
            dir.join("MUTATIONS.toml"),
            cache.clone(),
        );
        let ((run, _), (verified, _)) = on_stack(move || {
            let options = RunOptions {
                cache: Some(run_cache),
                ..RunOptions::default()
            };
            (
                kink_flow::cli::run(&flow, &list, &options),
                kink_flow::cli::run_mode(
                    &flow,
                    &list,
                    &options,
                    kink_flow::search::RunMode::Verify,
                ),
            )
        });
        let row = |document: &Value, id: &str| {
            document["mutations"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["id"] == id)
                .unwrap_or_else(|| panic!("no row {id}: {document:#}"))
                .clone()
        };
        for (id, status, reason) in [
            ("false", "unkillable", "weakening"),
            ("guide-pattern", "unkillable", "weakening"),
            ("isnat", "equivalent", "valid-condition"),
            ("no-decrease", "unknown", "stack-stop"),
            ("shifted", "unknown", "open-application"),
        ] {
            for document in [&run, &verified] {
                let row = row(document, id);
                assert_eq!(row["status"], status, "{row:#}");
                assert_eq!(row["reason"], reason, "{row:#}");
            }
        }
        assert_eq!(
            verified["mismatches"],
            serde_json::json!([]),
            "{verified:#}"
        );
        let isnat = row(&run, "isnat");
        assert_eq!(
            isnat["weakening"][0]["kind"], "valid-condition",
            "{isnat:#}"
        );
        // The mutant is the specification's theory: it withdraws not even `plus`'s `total`.
        assert_eq!(
            isnat["removed_claims"],
            serde_json::json!({"removed": [], "unsupported": []}),
            "{isnat:#}"
        );
        assert!(
            isnat["action"]
                .as_str()
                .unwrap()
                .contains("hold of every value"),
            "{isnat:#}"
        );

        let options = || FuzzOptions {
            cache: Some(cache.clone()),
            ..imp_options(50)
        };
        for (id, status, reason) in [
            ("false", "unkillable", "weakening"),
            ("guide-pattern", "unkillable", "weakening"),
            ("isnat", "equivalent", "valid-condition"),
        ] {
            let (document, ok) = fuzz_kill(
                &dir,
                "MUTATIONS.toml",
                Some(STORY_TEMPLATES),
                "t4-second",
                id,
                options(),
            );
            assert!(!ok, "{document:#}");
            assert_eq!(document["stopped"], "refused", "{document:#}");
            assert_eq!(
                kink_flow::cli::fuzz_status(&document),
                EXIT_UNASKED,
                "{document:#}"
            );
            let refusal = &document["job"]["refusal"];
            assert_eq!(refusal["stage"], "mutation", "{document:#}");
            assert_eq!(refusal["reason"], status, "{document:#}");
            assert_eq!(document["job"]["status"], status, "{document:#}");
            assert_eq!(document["job"]["reason"], reason, "{document:#}");
            assert!(!document["job"]["weakening"].is_null(), "{document:#}");
            assert_eq!(document["attempts"], serde_json::json!([]), "{document:#}");
            let action = document["action"].as_str().unwrap();
            assert!(
                action.contains(row(&run, id)["action"].as_str().unwrap()),
                "{action}"
            );
        }

        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(STORY_TEMPLATES),
            "t4-second",
            "no-decrease",
            FuzzOptions {
                stack_stops: 2,
                ..options()
            },
        );
        assert!(ok, "{document:#}");
        assert!(
            warning_kinds(&document).contains(&"stack-stop"),
            "{document:#}"
        );
        assert_eq!(document["stopped"], "stack-stops", "{document:#}");
        assert_eq!(
            kink_flow::cli::fuzz_status(&document),
            kink_flow::cli::EXIT_UNANSWERED
        );
        assert_eq!(totals(&document)["cases"], 2, "{document:#}");
        let action = document["action"].as_str().unwrap();
        assert!(action.contains("a mutant that ends"), "{action}");
        assert!(!action.contains("--cases"), "{action}");
        assert!(!action.contains("raise"), "{action}");
        // k-rust-fuzz words the observer's stop as its caller's cancellation; the action names
        // the count that ended the search instead.
        assert!(
            action.contains("The search ended at its --stack-stops count."),
            "{action}"
        );
        assert!(!action.contains("cancelled"), "{action}");

        // Every case of `t5-first` ends, on `shifted`'s mutant, holding an application its
        // equations leave open: the search ends after `--open-stops` of them in a row, a count
        // and never a clock, with the advice of the reason open-application.
        let templates = format!(
            "{STORY_TEMPLATES}\n[[template]]\nid = \"t5-first\"\nprogram = \"t5\"\n\n  [[template.hole]]\n  name = \"A\"\n  sort = \"Nat\"\n  find = \"plus(s(s(zero))\"\n  literal = \"s(zero)\"\n  allow-refused-sort = true\n"
        );
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(&templates),
            "t5-first",
            "shifted",
            FuzzOptions {
                open_stops: 2,
                ..options()
            },
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], "open-stops", "{document:#}");
        assert_eq!(
            kink_flow::cli::fuzz_status(&document),
            kink_flow::cli::EXIT_UNANSWERED
        );
        assert_eq!(totals(&document)["cases"], 2, "{document:#}");
        let action = document["action"].as_str().unwrap();
        assert!(action.contains("(--open-stops)"), "{action}");
        assert!(
            action.contains("The search ended at its --open-stops count."),
            "{action}"
        );
        assert!(!action.contains("cancelled"), "{action}");

        let (document, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(STORY_TEMPLATES),
            "t4-second",
            "shifted",
            options(),
        );
        assert_eq!(document["stopped"], "budget", "{document:#}");
        let named = document["warnings"]
            .as_array()
            .unwrap()
            .iter()
            .find(|warning| warning["kind"] == "not-ceil-free")
            .unwrap_or_else(|| panic!("no not-ceil-free warning: {document:#}"));
        assert!(
            named["detail"].as_str().unwrap().contains("`plus`"),
            "{named:#}"
        );
        assert!(
            document["action"]
                .as_str()
                .unwrap()
                .contains("a warning names the function"),
            "{document:#}"
        );
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
                FuzzOptions {
                    confirm: true,
                    ..imp_options(300)
                },
            );
            assert!(ok, "{mutation}: {:#}", document["action"]);
            assert_eq!(document["stopped"], Value::Null, "{mutation}");
            // kink's own run (KF-T4), on the flow with the fragment alone, kills with it.
            let confirmation = &document["attempts"][0]["confirmation"];
            assert_eq!(
                confirmation["confirmed"], true,
                "{mutation}: {confirmation:#}"
            );
            assert_eq!(confirmation["status"], "killed", "{mutation}");
            assert_eq!(
                confirmation["killer"], document["program"]["id"],
                "{mutation}"
            );
            assert_eq!(document["program"]["confirmed"], true, "{mutation}");
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

    /// fz26 KINK-PATHSET-FALLBACK, S9 (`testdata/flow/diamonds`): the removed-end job of
    /// `end-guard-dropped` on `go(14, $D)` finds `D = 0`, whose mutant state set ends in one
    /// undefined step after 14 converging diamonds; the witness filter accepts it (the mutant's
    /// work is within `4 * W + 10000`), and kink's confirmation, which runs the same state set,
    /// kills with the fragment. Before the ticket kink ran that side as a path set, about 49 000
    /// states, which the work budget cut, and the job stopped `unconfirmed`.
    #[test]
    #[ignore = "kink"]
    fn a_kill_through_an_undefined_step_after_converging_paths_is_confirmed() {
        let (document, ok) = fuzz_kill(
            &flow("diamonds"),
            "MUTATIONS.toml",
            None,
            "divisor",
            "end-guard-dropped",
            FuzzOptions {
                confirm: true,
                ..imp_options(100)
            },
        );
        assert!(ok, "{:#}", document["action"]);
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        let confirmation = &document["attempts"][0]["confirmation"];
        assert_eq!(confirmation["confirmed"], true, "{confirmation:#}");
        assert_eq!(confirmation["status"], "killed");
        assert_eq!(confirmation["killer"], document["program"]["id"]);
        let fragment = document["program"]["fragment"].as_str().unwrap();
        assert!(fragment.contains("go(14, 0)"), "{fragment}");
    }

    /// A kill job of a mutation expected to survive is not refused: the search is an attempt to
    /// refute the expectation, it says so up front, and the witness it finds is a finding (exit
    /// status 1) whose action says what it shows. The job is the one above, whose witness kink
    /// confirms, on a copy of the list in which the mutation expects to survive.
    #[test]
    #[ignore = "kink"]
    fn a_witness_of_a_mutation_expected_to_survive_is_a_finding() {
        let dir = scratch("expected-to-survive");
        flow_support::copy_dir(&flow("diamonds"), &dir);
        let list = dir.join("MUTATIONS.toml");
        let text = fs::read_to_string(&list).unwrap().replacen(
            "id = \"end-guard-dropped\"\n",
            "id = \"end-guard-dropped\"\nexpect = \"survive\"\n",
            1,
        );
        assert!(text.contains("expect = \"survive\""), "{text}");
        fs::write(&list, text).unwrap();
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            "divisor",
            "end-guard-dropped",
            FuzzOptions {
                confirm: true,
                ..imp_options(100)
            },
        );
        assert!(ok, "{:#}", document["action"]);
        assert_eq!(
            document["job"]["expect"], "survive",
            "{:#}",
            document["job"]
        );
        assert!(
            warning_kinds(&document).contains(&"expected-to-survive"),
            "{:#}",
            document["warnings"]
        );
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        assert_eq!(document["attempts"][0]["confirmation"]["status"], "killed");
        assert_eq!(kink_flow::cli::fuzz_status(&document), EXIT_NO);
        let action = document["action"].as_str().unwrap();
        assert!(
            action.starts_with("the mutation expects to survive, and this program distinguishes"),
            "{action}"
        );
        // The same witness unconfirmed (`--no-confirm`) is a candidate: nothing shows the corpus
        // kills, so the claim is neither refuted nor confirmed.
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            "divisor",
            "end-guard-dropped",
            imp_options(100),
        );
        assert!(ok, "{:#}", document["action"]);
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        assert_eq!(document["program"]["confirmed"], false, "{document:#}");
        assert_eq!(kink_flow::cli::fuzz_status(&document), EXIT_UNANSWERED);
        let action = document["action"].as_str().unwrap();
        assert!(
            action.starts_with(
                "the mutation expects to survive, and this program may distinguish its mutant \
                 from the specification, but it does not refute the expectation yet: kink's own \
                 run did not confirm the kill (--no-confirm)"
            ),
            "{action}"
        );
    }

    /// A witness of a mutation expected to survive whose kill kink confirms only under premises
    /// `FLOW.toml` lacks (given with `--assume-joined`) does not refute the expectation: on the
    /// flow as it stands kink counts no kill, so the job is unanswered (exit status 3), and the
    /// action names the premises. The job is the one of
    /// `a_premise_given_on_the_command_line_confirms_under_the_overlay`, on a copy of its list in
    /// which the mutation expects to survive.
    #[test]
    #[ignore = "kink"]
    fn a_witness_of_a_mutation_expected_to_survive_under_a_missing_premise_is_no_finding() {
        let dir = scratch("expected-to-survive-premise");
        flow_support::copy_dir(&flow("findings/r3-plainq"), &dir);
        let list = dir.join("MUTATIONS.toml");
        let text = fs::read_to_string(&list).unwrap().replacen(
            "id = \"store-changed\"\n",
            "id = \"store-changed\"\nexpect = \"survive\"\n",
            1,
        );
        assert!(text.contains("expect = \"survive\""), "{text}");
        fs::write(&list, text).unwrap();
        let (strict, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(REPRO_TEMPLATE),
            "go",
            "store-changed",
            FuzzOptions::default(),
        );
        let names = strict["findings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|f| f["name"].as_str().unwrap().to_owned())
            .collect::<BTreeSet<_>>();
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(REPRO_TEMPLATE),
            "go",
            "store-changed",
            FuzzOptions {
                assume_joined: names.into_iter().collect(),
                confirm: true,
                ..FuzzOptions::default()
            },
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["job"]["expect"], "survive");
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        assert_eq!(document["program"]["confirmed"], true, "{document:#}");
        let premises = document["program"]["premises"].as_array().unwrap();
        assert!(!premises.is_empty() && premises.iter().all(|p| p["in_flow"] == false));
        assert_eq!(kink_flow::cli::fuzz_status(&document), EXIT_UNANSWERED);
        let action = document["action"].as_str().unwrap();
        assert!(
            action.starts_with(
                "the mutation expects to survive, and this program may distinguish its mutant \
                 from the specification, but it does not refute the expectation yet: the kill \
                 rests on premises FLOW.toml's [spec] assume_joined lacks ("
            ),
            "{action}"
        );
    }

    /// A mutation kink refuses ends the command with kink's status and reason; nothing is fuzzed.
    #[test]
    #[ignore = "kink"]
    fn kink_refusals_end_the_command_with_kinks_reason() {
        let calc = "[[template]]\nid = \"add\"\nprogram = \"add\"\n";
        for (mutation, status, reason) in [
            ("no-such-rule", "invalid-mutation", "unknown-label"),
            ("add-in-a-group", "equivalent", "equivalent-compilation"),
            ("add-unbound", "not-admitted", "rejected"),
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
        assert_eq!(document["job"]["status"], "not-admitted");
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
            "[[mutation]]\nid = \"fee-dropped\"\nmisunderstanding = \"a test mutation\"\n  [[mutation.edit]]\n  rule = \"LEDGER.settle\"\n  \
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
    ///
    /// Re-pin kink27 R3-CENSUS-RUNLEVEL: `keys_list` is a k-rust class, judged per run, and left
    /// the census, so the hook is `String2Bytes` (its encoding left open, evaluated by k-rust with
    /// no run-level record), which the census keeps; it is applied to `Int2String(I)` so that the
    /// constant fold cannot remove it from the rule.
    #[test]
    #[ignore = "kink"]
    fn a_definition_exclusion_refuses_the_job_with_kinks_reason() {
        let keys = "ListItem(lengthBytes(String2Bytes(Int2String(I))))";
        let count_edit = "[[mutation]]\nid = \"count-plus-one\"\nmisunderstanding = \"a test mutation\"\n  [[mutation.edit]]\n  rule = \
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
            "[[mutation]]\nid = \"start-lists-keys\"\nmisunderstanding = \"a test mutation\"\n  [[mutation.edit]]\n  rule = \
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
                    .contains("BYTES.string2bytes"),
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
            "[[mutation]]\nid = \"ten-is-eleven\"\nmisunderstanding = \"a test mutation\"\n  [[mutation.edit]]\n  rule = \"MAC.ten\"\n  find \
             = \"10\"\n  replace = \"11\"\n\n[[mutation]]\nid = \"plus-becomes-minus\"\nmisunderstanding = \"a test mutation\"\n  \
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
        let Some(ProgramSource::Text(program_text)) = program.source.clone() else {
            panic!("the fragment's program is inline");
        };
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let checks = on_stack(move || {
            let (_, admitted) = kink_flow::admit_spec(&manifest);
            let (spec, mut inputs) = admitted.expect("the specification is admitted");
            let mut inputs = inputs.session(&spec);
            let mut check = |case: &k_rust_fuzz::report::WitnessCase, text: &str| {
                check_assembly(&mut inputs, &program, &text.into(), case)
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

    /// A witness kink's own run refuses is not offered (KF-T4): on NA every end holds a non-ASCII
    /// string, which the fuzz's data judgement accepts and kink's end check does not, so without
    /// the witness filter the confirmation is refused with kink's cause, the job stops
    /// `unconfirmed` and prints no program. The confirmation writes nothing under the flow's
    /// directory. With the filter (the default, FZ-COMPARABLE-B) the fuzz agrees with kink inside
    /// the campaign: every hit is refused for its non-ASCII end, nothing reaches kink's run, and the
    /// job stops `client-refused`.
    #[test]
    #[ignore = "kink"]
    fn a_witness_kink_refuses_is_unconfirmed_with_kinks_cause() {
        let dir = scratch_flow("nonascii", "na.k", NA_K, NA_FLOW, NA_MUTATIONS);
        let before = listing(&dir);
        let (filtered, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(NA_TEMPLATES),
            "one-holes",
            "plus-one",
            FuzzOptions {
                confirm: true,
                ..imp_options(20)
            },
        );
        assert!(ok, "{filtered:#}");
        assert_eq!(filtered["stopped"], "client-refused", "{filtered:#}");
        let attempt = filtered["attempts"]
            .as_array()
            .and_then(|attempts| attempts.first())
            .expect("one attempt");
        assert_eq!(
            attempt.get("confirmation"),
            Some(&Value::Null),
            "{attempt:#}"
        );
        assert_eq!(
            totals(&filtered)["filter"]["refused"]["domain-value-not-ascii"],
            totals(&filtered)["unsupported-reasons"]["client-refused"],
            "{:#}",
            totals(&filtered)
        );
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(NA_TEMPLATES),
            "one-holes",
            "plus-one",
            FuzzOptions {
                confirm: true,
                filter: false,
                ..imp_options(20)
            },
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], "unconfirmed", "{document:#}");
        assert_eq!(document["program"], Value::Null);
        let confirmation = &document["attempts"][0]["confirmation"];
        assert_eq!(confirmation["confirmed"], false, "{confirmation:#}");
        assert_ne!(confirmation["status"], "killed", "{confirmation:#}");
        assert!(!confirmation["cause"].is_null(), "{confirmation:#}");
        assert_eq!(listing(&dir), before, "nothing is written under the flow");
        // Without confirmation the same candidate is offered, unconfirmed.
        let (unconfirmed, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(NA_TEMPLATES),
            "one-holes",
            "plus-one",
            FuzzOptions {
                filter: false,
                ..imp_options(20)
            },
        );
        assert!(ok);
        assert_eq!(
            unconfirmed["program"]["confirmed"], false,
            "{unconfirmed:#}"
        );
        assert_eq!(unconfirmed["attempts"][0]["confirmation"], Value::Null);
    }

    /// When kink refuses the shrunk witness, the unshrunk one is confirmed (KF-T4): only `go(0)`
    /// writes the non-ASCII string, so without the witness filter the shrunk case is `I = 0`, and
    /// the first case (the template's own `go(2)`) kills under kink's run. With the filter (the
    /// default, FZ-COMPARABLE-B) shrinking never keeps `I = 0`, so the shrunk case is the one kink
    /// confirms.
    #[test]
    #[ignore = "kink"]
    fn the_unshrunk_witness_is_confirmed_when_the_shrunk_one_is_refused() {
        let spec = "module NA-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int)
endmodule

module NA
  imports NA-SYNTAX
  imports INT
  imports STRING
  configuration <k> $PGM:Pgm </k> <out> \"\" </out>
  rule <k> go(0) => .K </k> <out> _ => \"\u{e9}\" </out>
  rule <k> go(I) => .K </k> <out> _ => Int2String(I) </out> requires I =/=Int 0
endmodule
";
        let mutations = "[[mutation]]\nid = \"both\"\nmisunderstanding = \"a test mutation\"\n[[mutation.edit]]\nline = 11\nfind = \
                         \"\\\"\u{e9}\\\"\"\nreplace = \"\\\"\u{e8}\\\"\"\n[[mutation.edit]]\nline = \
                         12\nfind = \"Int2String(I)\"\nreplace = \"Int2String(I +Int 1)\"\n";
        let flow_toml = NA_FLOW.replace("go(1)", "go(2)");
        let templates = NA_TEMPLATES
            .replace("go(1)", "go(2)")
            .replace("\"1\"", "\"2\"");
        let dir = scratch_flow("unshrunk", "na.k", spec, &flow_toml, mutations);
        let (filtered, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(&templates),
            "one-holes",
            "both",
            FuzzOptions {
                confirm: true,
                ..imp_options(20)
            },
        );
        assert!(ok, "{filtered:#}");
        assert_eq!(filtered["stopped"], Value::Null, "{filtered:#}");
        let attempt = &filtered["attempts"][0];
        assert_eq!(attempt["candidate"]["case"], "shrunk", "{attempt:#}");
        assert_eq!(
            attempt["candidate"]["holes"][0]["value"]["int"], "1",
            "{attempt:#}"
        );
        assert_eq!(attempt["confirmation"]["confirmed"], true, "{attempt:#}");
        assert_eq!(attempt.get("refused_confirmations"), None, "{attempt:#}");
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(&templates),
            "one-holes",
            "both",
            FuzzOptions {
                confirm: true,
                filter: false,
                ..imp_options(20)
            },
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        let attempt = &document["attempts"][0];
        assert_eq!(attempt["candidate"]["case"], "first", "{attempt:#}");
        assert_eq!(attempt["confirmation"]["confirmed"], true, "{attempt:#}");
        let refused = attempt["refused_confirmations"].as_array().unwrap();
        assert_eq!(refused.len(), 1, "{attempt:#}");
        assert_eq!(refused[0]["case"], "shrunk");
        assert_eq!(document["program"]["confirmed"], true);
    }

    /// GUIDE-USABILITY nit: when kink refuses both the shrunk and the first case, `confirmation`
    /// holds the last refused verdict (the first case's) and `refused_confirmations` lists only
    /// the others (the shrunk case's), not the first again. Every end here holds a non-ASCII
    /// String, which kink's end check refuses, so without the witness filter every kill is
    /// refused at confirmation.
    #[test]
    #[ignore = "kink"]
    fn refused_confirmations_does_not_repeat_the_confirmation() {
        let spec = "module NA-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int)
endmodule

module NA
  imports NA-SYNTAX
  imports INT
  imports STRING
  configuration <k> $PGM:Pgm </k> <out> \"\" </out>
  rule <k> go(I) => .K </k> <out> _ => \"\u{e9}\" +String Int2String(I) </out>
endmodule
";
        let mutations = "[[mutation]]\nid = \"accent\"\nmisunderstanding = \"a test mutation\"\n[[mutation.edit]]\nline = 11\nfind = \
                         \"\\\"\u{e9}\\\"\"\nreplace = \"\\\"\u{e8}\\\"\"\n";
        let flow_toml = NA_FLOW.replace("go(1)", "go(2)");
        let templates = NA_TEMPLATES
            .replace("go(1)", "go(2)")
            .replace("\"1\"", "\"2\"");
        let dir = scratch_flow("both-refused", "na.k", spec, &flow_toml, mutations);
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(&templates),
            "one-holes",
            "accent",
            FuzzOptions {
                confirm: true,
                filter: false,
                ..imp_options(20)
            },
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], "unconfirmed", "{document:#}");
        let attempt = &document["attempts"][0];
        assert_eq!(attempt["confirmation"]["case"], "first", "{attempt:#}");
        assert_eq!(attempt["confirmation"]["confirmed"], false, "{attempt:#}");
        let refused = attempt["refused_confirmations"].as_array().unwrap();
        assert_eq!(refused.len(), 1, "{attempt:#}");
        assert_eq!(refused[0]["case"], "shrunk", "{attempt:#}");
    }

    /// A premise given on the command line only confirms under the overlay (KF-T4): r3-plainq's
    /// finding, named with `--assume-joined` and absent from `FLOW.toml`, lets kink's run kill;
    /// the premise is printed as not in the flow.
    #[test]
    #[ignore = "kink"]
    fn a_premise_given_on_the_command_line_confirms_under_the_overlay() {
        let dir = flow("findings/r3-plainq");
        let (strict, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(REPRO_TEMPLATE),
            "go",
            "store-changed",
            FuzzOptions::default(),
        );
        let names = strict["findings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|f| f["name"].as_str().unwrap().to_owned())
            .collect::<BTreeSet<_>>();
        let (document, ok) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            Some(REPRO_TEMPLATE),
            "go",
            "store-changed",
            FuzzOptions {
                assume_joined: names.into_iter().collect(),
                confirm: true,
                ..FuzzOptions::default()
            },
        );
        assert!(ok, "{document:#}");
        assert_eq!(
            document["attempts"][0]["confirmation"]["status"], "killed",
            "{document:#}"
        );
        assert_eq!(document["program"]["confirmed"], true);
        let premises = document["program"]["premises"].as_array().unwrap();
        assert!(!premises.is_empty() && premises.iter().all(|p| p["in_flow"] == false));
    }

    /// The campaign reads a configuration variable's text as kink does (k-rust
    /// `variable_reading_modules`, krun's `-c` reading too): on the `tokens.k`-shaped
    /// [`TOKENS_K`] the template binds `$W` and `$V` to `word`, which is the `Word` `word` in
    /// both, so the job runs (no assembly refusal), the rule job finds a program that fires `go`
    /// (`X >= 6`), its initial configuration is kink's assembly on both counts, and kink confirms
    /// it.
    #[test]
    #[ignore = "kink"]
    fn a_template_whose_variable_only_the_syntax_module_reads_is_fuzzed_as_kink_reads_it() {
        let dir = scratch_flow("tokens", "tokens.k", TOKENS_K, TOKENS_MANIFEST, "");
        let (document, ok) = run_job(
            &dir,
            TOKENS_TEMPLATES,
            "run-holes",
            Job::Rule("go".into(), true),
            FuzzOptions {
                confirm: true,
                ..imp_options(40)
            },
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["job"]["refusal"], Value::Null, "{document:#}");
        assert_eq!(
            document["job"]["rule"]["label"], "TOKENS.go",
            "{document:#}"
        );
        assert_eq!(document["stopped"], Value::Null, "{document:#}");
        let attempt = &document["attempts"][0];
        let candidate = &attempt["candidate"];
        assert_eq!(candidate["assembly"]["status"], "match", "{candidate:#}");
        assert_eq!(candidate["comparable"]["holds"], true, "{candidate:#}");
        let x = candidate["holes"][0]["k-text"].as_str().unwrap_or_default();
        assert!(x.parse::<i64>().is_ok_and(|x| x >= 6), "{candidate:#}");
        let confirmation = &attempt["confirmation"];
        assert_eq!(confirmation["confirmed"], true, "{confirmation:#}");
        assert_eq!(confirmation["status"], "fired", "{confirmation:#}");
    }

    /// The rule job (T5) finds a program whose comparable all-paths run applies `big` (`--fired`:
    /// `dbl(X) > 10`, so `X >= 6`), and kink's own `results`, with the fragment appended, lists
    /// it in the rule's `fired_by`; without `--fired` any program reaches `big`'s condition. The
    /// same seed gives the same document.
    #[test]
    #[ignore = "kink"]
    fn a_rule_job_finds_a_program_kinks_results_confirm() {
        let dir = steps_flow("rule-job");
        let fired = || {
            run_job(
                &dir,
                STEPS_TEMPLATES,
                "run-holes",
                Job::Rule("big".into(), true),
                imp_options(40),
            )
        };
        let (document, ok) = fired();
        assert!(ok, "{document:#}");
        let (confirmed, _) = run_job(
            &dir,
            STEPS_TEMPLATES,
            "run-holes",
            Job::Rule("big".into(), true),
            FuzzOptions {
                confirm: true,
                ..imp_options(40)
            },
        );
        let confirmation = &confirmed["attempts"][0]["confirmation"];
        assert_eq!(confirmation["confirmed"], true, "{confirmation:#}");
        assert_eq!(confirmation["status"], "fired");
        assert_eq!(confirmation["class"], "comparable");
        assert_eq!(
            document["stopped"],
            Value::Null,
            "{:#}\n{:#}",
            document["attempts"][0]["fuzz"]["totals"],
            document["attempts"][0]["fuzz"]["outcome"]
        );
        assert_eq!(document["job"]["kind"], "fired");
        assert!(
            document["job"]["rule"].get("mode").is_none(),
            "{document:#}"
        );
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
            Job::Rule(format!("steps.k:{}", steps_line("rule [small]")), false),
            imp_options(5),
        );
        assert!(by_line.1, "{:#}", by_line.0);
        assert_eq!(by_line.0["job"]["rule"]["label"], "STEPS.small");
        assert_eq!(by_line.0["job"]["kind"], "matched");

        append_fragment(&dir, &document);
        let id = document["program"]["id"].as_str().unwrap().to_owned();
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let cache = dir.join("cache");
        let (results, ok) = on_stack(move || {
            kink_flow::coverage::coverage(
                &manifest,
                &CoverageOptions {
                    cache: Some(cache),
                    ..CoverageOptions::default()
                },
            )
        });
        assert!(ok, "{results:#}");
        let big = results["families"]["rules"]["items"]
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

    /// Final review S1: a rule job's confirmation reads the targeted rule's own `coverage` item.
    /// `run(1)` steps to `step(2)`, so `small` fires and `big` never does; the program is
    /// comparable and listed under `go`, `small` and others, yet `big --fired` must not confirm
    /// it. Before the fix a listing under any rule confirmed it (`listed`).
    #[test]
    #[ignore = "kink"]
    fn a_rule_jobs_confirmation_reads_the_targeted_rules_entry_only() {
        let dir = steps_flow("rule-target");
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        // A `[coverage]` section (a depth above 1, which `coverage` refuses, and an `mcdc`
        // selection) does not stop a confirmation, which reads only the rule's own lists.
        let mut sectioned = manifest.clone();
        sectioned.coverage.depth = std::num::NonZeroU64::new(2).unwrap();
        sectioned.coverage.mcdc = kink_flow::manifest::Mcdc::Rules(vec!["STEPS.big".to_owned()]);
        sectioned.coverage.declared = true;
        let confirm_on = |manifest: &FlowManifest, rule: &'static str, fired: bool| {
            let manifest = manifest.clone();
            on_stack(move || {
                let program = kink_flow::Program {
                    id: "probe".to_owned(),
                    source: Some(ProgramSource::Text("run(1)".to_owned())),
                    start_sort: None,
                    variables: Vec::new(),
                    inputs: toml::Table::new(),
                    case: None,
                    case_file: None,
                    expect: None,
                    stop_count: None,
                };
                confirm_program(
                    &manifest,
                    &FuzzOptions::default(),
                    FuzzJob::Rule { rule, fired },
                    &program,
                )
            })
        };
        let confirm = |rule: &'static str, fired: bool| confirm_on(&manifest, rule, fired);
        let big = confirm("big", true);
        assert_eq!(big["confirmed"], false, "{big:#}");
        assert_eq!(big["status"], "not-fired", "{big:#}");
        assert_eq!(big["reason"], "not-listed", "{big:#}");
        assert_eq!(big["class"], "comparable", "{big:#}");
        let small = confirm("small", true);
        assert_eq!(small["confirmed"], true, "{small:#}");
        assert_eq!(small["reason"], "listed", "{small:#}");
        assert_eq!(confirm_on(&sectioned, "small", true), small);
        // With --matched the target is `big`'s condition, which `step(2)` matches.
        let matched = confirm("big", false);
        assert_eq!(matched["confirmed"], true, "{matched:#}");
        assert_eq!(matched["status"], "matched", "{matched:#}");
        let unknown = confirm("nothing", false);
        assert_eq!(unknown["status"], "refused", "{unknown:#}");
        assert_eq!(unknown["reason"], "unknown-label", "{unknown:#}");
    }

    /// The rule job refuses a rule it cannot target before any campaign: a macro has no
    /// coverage signal, a function rule compiles to equations, a line between rules and an
    /// unknown label name no rule.
    #[test]
    #[ignore = "kink"]
    fn a_rule_job_refuses_what_kink_cannot_list() {
        let dir = steps_flow("rule-refusals");
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
                Job::Rule(rule.clone(), false),
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
        // Final review ux S9: a refusal lists the rules nearest the reference with the ids a
        // rule job can target, so the action's "its 64-hex id" can be followed; before, it
        // pointed at "listed" ids and listed none.
        let (found, _) = run_job(
            &dir,
            STEPS_TEMPLATES,
            "run-holes",
            Job::Rule("big".into(), false),
            imp_options(1),
        );
        let big = found["job"]["rule"]["id"].as_str().unwrap().to_owned();
        for (rule, listed) in [
            (
                format!("steps.k:{}", steps_line("rule [go]") + 1),
                "nearest are",
            ),
            ("bi".to_owned(), "the labels that contain it"),
        ] {
            let (document, _) = run_job(
                &dir,
                STEPS_TEMPLATES,
                "run-holes",
                Job::Rule(rule.clone(), false),
                imp_options(1),
            );
            let detail = document["job"]["refusal"]["detail"].as_str().unwrap();
            assert!(detail.contains(listed), "{rule}: {detail}");
            assert!(
                detail.contains(&format!("label STEPS.big) id {big}")),
                "{rule}: {detail}"
            );
            let action = document["action"].as_str().unwrap();
            assert!(!action.contains("listed 64-hex"), "{action}");
        }
    }

    /// A rule job on a definition with an unnamed finding is not comparable, as a kill is
    /// (Sebastien, D33); naming the findings gives a witness.
    #[test]
    #[ignore = "kink"]
    fn a_rule_job_on_a_findings_repro_needs_its_names() {
        let dir = flow("findings/r3-plainq");
        let rule = || Job::Rule("spec.k:11".into(), false);
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
        let (confirmed, _) = run_job(
            &dir,
            STEPS_TEMPLATES,
            "run-holes",
            Job::Pattern(list.clone(), "big-step".into()),
            FuzzOptions {
                confirm: true,
                ..imp_options(40)
            },
        );
        let confirmation = &confirmed["attempts"][0]["confirmation"];
        assert_eq!(confirmation["confirmed"], true, "{confirmation:#}");
        assert_eq!(confirmation["status"], "confirmed");
        assert_eq!(confirmation["answer"], "hit");
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

    /// Final review ux S6 (FZ-ENGINE-R4): `run-holes` has 10 assignments (X in 0..=9), none of
    /// which reaches `step(V)` with `V > 18` (V = 2X), so the campaign ends after them with no
    /// budget spent: `stopped: domain-exhausted`, from the embedded report's `totals.domain`,
    /// and the action does not suggest more cases.
    #[test]
    #[ignore = "kink"]
    fn an_exhausted_domain_stops_domain_exhausted() {
        let dir = steps_flow("exhausted");
        let list = PatternList::decode(
            "[[pattern]]\nid = \"huge-step\"\npattern = \"<k> step(V) </k> requires V >Int 18\"\n",
        )
        .unwrap();
        let (document, ok) = run_job(
            &dir,
            STEPS_TEMPLATES,
            "run-holes",
            Job::Pattern(list, "huge-step".into()),
            imp_options(40),
        );
        assert!(ok, "{document:#}");
        assert_eq!(
            document["stopped"], "domain-exhausted",
            "{:#}",
            document["action"]
        );
        assert_eq!(
            totals(&document)["domain"],
            serde_json::json!({"assignments": 10, "tried": 10, "exhausted": true})
        );
        assert_eq!(totals(&document)["cases"], 10);
        let action = document["action"].as_str().unwrap();
        assert!(
            action.contains("so this campaign has no other case to run"),
            "{action}"
        );
        assert!(!action.contains("Raise --cases"), "{action}");
    }

    /// Final review ux S5: the action after a `budget` stop advises more cases only when the
    /// statement does not say they would not help. `big --fired` on `run(X)` with `X <= 5` never
    /// fires (`dbl(5) = 10`), and every case reaches the same rules from the first on: after 10
    /// cases more cases are advised, after 40 (39 cases with no new rule) the statement says
    /// coverage stopped growing and the action no longer advises raising --cases. Before the fix
    /// it always did.
    #[test]
    #[ignore = "kink"]
    fn the_budget_action_advises_more_cases_only_while_coverage_grows() {
        let dir = steps_flow("stalled");
        let templates = "[[template]]\nid = \"wide\"\nprogram = \"one\"\n[[template.hole]]\n\
                         name = \"X\"\nsort = \"Int\"\nfind = \"1\"\nliteral = \"1\"\n\
                         range = { min = -100000, max = 5 }\n";
        let job = |cases| {
            run_job(
                &dir,
                templates,
                "wide",
                Job::Rule("big".into(), true),
                imp_options(cases),
            )
        };
        let (early, ok) = job(10);
        assert!(ok, "{early:#}");
        assert_eq!(early["stopped"], "budget", "{early:#}");
        let action = early["action"].as_str().unwrap();
        assert!(action.contains("Raise --cases or --work"), "{action}");
        let (stalled, ok) = job(40);
        assert!(ok, "{stalled:#}");
        assert_eq!(stalled["stopped"], "budget", "{stalled:#}");
        assert_eq!(totals(&stalled)["coverage-last-grew"], 0, "{stalled:#}");
        let action = stalled["action"].as_str().unwrap();
        assert!(action.contains("unlikely to reach a new rule"), "{action}");
        assert!(!action.contains("Raise --cases"), "{action}");
        assert!(
            action.contains("Rather than raising --cases or --work"),
            "{action}"
        );
        // GUIDE-USABILITY 5: the document names k-rust's build as the embedded report does.
        assert_eq!(stalled["k_rust_revision"], k_rust::build_identity());
        assert_eq!(
            stalled["k_rust_revision"],
            stalled["attempts"][0]["fuzz"]["identity"]["k-rust-revision"]
        );
    }

    /// Final review ux S5 on the guide's `sum` example: the mutant `add-becomes-sub` runs out of
    /// work where the definition ends, so the statement says it may not terminate on this
    /// program, and the action does not advise raising --cases or --work after it.
    #[test]
    #[ignore = "kink"]
    fn the_budget_action_advises_no_bound_after_a_diverging_mutant() {
        let (document, ok) = fuzz_kill(
            &flow("fuzz/imp"),
            "MUTATIONS.toml",
            None,
            "sum-holes",
            "add-becomes-sub",
            FuzzOptions {
                budget: k_rust_fuzz::Budget::Cases(20),
                max_work: Some(2000),
                ..FuzzOptions::default()
            },
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], "budget", "{document:#}");
        assert!(totals(&document)["diverging"].is_object(), "{document:#}");
        let action = document["action"].as_str().unwrap();
        assert!(
            action.contains("may not terminate on this program"),
            "{action}"
        );
        assert!(!action.contains("Raise --cases"), "{action}");
    }

    /// Final review ux S8 (FZ-ENGINE-R4): on `run(0)` the program reaches `spin(0)`, which
    /// rewrites to itself forever, so the pattern witness is a hit whose run of every path
    /// stops at the work bound: kink-flow warns `witness-not-terminating`. A witness whose run
    /// ends carries no such warning.
    #[test]
    #[ignore = "kink"]
    fn a_pattern_witness_that_does_not_terminate_is_warned() {
        const SPIN_K: &str = "module SPIN-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= run(Int)
endmodule

module SPIN
  imports SPIN-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= spin(Int)
  rule <k> run(X) => spin(X) </k>
  rule <k> spin(X) => spin(X) </k> requires X ==Int 0
endmodule
";
        let manifest = "[spec]\nentry = \"spin.k\"\nmain_module = \"SPIN\"\nsyntax_module = \
                        \"SPIN-SYNTAX\"\n\n[[program]]\nid = \"one\"\ntext = \"run(1)\"\n";
        let dir = scratch_flow("spin", "spin.k", SPIN_K, manifest, "");
        let list = PatternList::decode(
            "[[pattern]]\nid = \"spins\"\npattern = \"<k> spin(0) </k>\"\n\n[[pattern]]\nid = \
             \"stops\"\npattern = \"<k> spin(3) </k>\"\n",
        )
        .unwrap();
        let templates = "[[template]]\nid = \"run-holes\"\nprogram = \"one\"\n\
                         [[template.hole]]\nname = \"X\"\nsort = \"Int\"\nfind = \"1\"\n\
                         literal = \"1\"\nrange = { min = 0, max = 3 }\n";
        let options = || FuzzOptions {
            max_work: Some(2_000),
            ..imp_options(20)
        };
        let (document, ok) = run_job(
            &dir,
            templates,
            "run-holes",
            Job::Pattern(list.clone(), "spins".into()),
            options(),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], Value::Null, "{:#}", document["action"]);
        assert!(
            warning_kinds(&document).contains(&"witness-not-terminating"),
            "{:#}",
            document["warnings"]
        );
        let (document, ok) = run_job(
            &dir,
            templates,
            "run-holes",
            Job::Pattern(list, "stops".into()),
            options(),
        );
        assert!(ok, "{document:#}");
        assert_eq!(document["stopped"], Value::Null, "{:#}", document["action"]);
        assert!(
            !warning_kinds(&document).contains(&"witness-not-terminating"),
            "{:#}",
            document["warnings"]
        );
    }

    /// The last `run` document (read from `--cache`, never written by `fuzz`): no document, then
    /// the mutation's witnesses suggested as templates with a warning for a template outside
    /// them, and a warning for a template whose program is not comparable; `--time-limit-ms` warns
    /// that it does not bound the campaign's setup.
    #[test]
    #[ignore = "kink"]
    fn the_last_run_suggests_witness_templates_and_warns() {
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
        let witnesses = row["witnesses"].clone();
        assert!(
            witnesses
                .as_array()
                .unwrap()
                .iter()
                .any(|id| id == "primes"),
            "{row:#}"
        );
        // straight.imp divides nothing: the witnesses are suggested instead.
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
        assert_eq!(last_run["mutation"]["witnesses"], witnesses);
        assert!(
            last_run["suggested_templates"][0]["template"]
                .as_str()
                .unwrap()
                .starts_with("[[template]]\n")
        );
        assert_eq!(warning_kinds(&document), ["template-not-a-witness"]);
        let path = cache.join("report.json");
        let mut stored: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        // A run of other programs than the corpus's says nothing about the mutation, whose
        // status and witnesses are facts about the programs judged: the corpus has gained a
        // program since (its row removed here) or changed one (its digest doctored), and the
        // document is stale, as one of another specification is.
        let programs = stored["programs"].as_array().unwrap();
        let (gained, changed) = (
            programs[0]["id"].as_str().unwrap().to_owned(),
            programs[1]["id"].as_str().unwrap().to_owned(),
        );
        let mut other = stored.clone();
        other["programs"].as_array_mut().unwrap().remove(0);
        other["programs"][0]["digest"] = "0".repeat(64).into();
        fs::write(&path, serde_json::to_string(&other).unwrap()).unwrap();
        let (document, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            "straight-holes",
            "div-becomes-mul",
            options(1),
        );
        assert_eq!(
            document["template"]["last_run"],
            serde_json::json!({"found": true, "current": false}),
            "{document:#}"
        );
        assert_eq!(warning_kinds(&document), ["stale-run-document"]);
        let detail = document["warnings"][0]["detail"].as_str().unwrap();
        assert!(
            detail.contains(&format!("added {gained}; changed {changed}")),
            "{detail}"
        );
        // primes reaches the rule; read as a timeout, its template is warned as unusable.
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
        // A row for which the last run had no compiled edit (it compiled no mutant for the row and
        // the outcome file kept no `witness`, as for a `baseline-findings` row; a row tier 1
        // decided keeps the outcome file's) has no `witnesses`, doctored here: nothing is
        // suggested, and the warning says why, with the row's reason.
        for row in stored["mutations"].as_array_mut().unwrap() {
            row["witnesses"] = Value::Null;
        }
        fs::write(&path, serde_json::to_string(&stored).unwrap()).unwrap();
        let (document, _) = fuzz_kill(
            &dir,
            "MUTATIONS.toml",
            None,
            "straight-holes",
            "div-becomes-mul",
            options(1),
        );
        let last_run = &document["template"]["last_run"];
        assert_eq!(
            last_run["mutation"]["witnesses"],
            Value::Null,
            "{last_run:#}"
        );
        assert_eq!(
            last_run["suggested_templates"],
            serde_json::json!([]),
            "{last_run:#}"
        );
        assert_eq!(
            warning_kinds(&document),
            ["witnesses-not-computed"],
            "{document:#}"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// FZ-COMPARABLE-B: the in-campaign witness filter
// ---------------------------------------------------------------------------------------------

/// Three programs whose ends hold strings. kink's end check (TV-01) gives a `String` domain value
/// a terminal value only when its bytes are ASCII, so whether kink can compare a run's ends
/// depends on the input: `cat` writes its two holes, `tag` always writes a non-ASCII string, and
/// `pick` writes one below 10 and an ASCII numeral from 10 on.
const STR_K: &str = r#"
module STR-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax Pgm ::= cat(String, String) [symbol(cat)]
               | tag(Int) [symbol(tag)]
               | pick(Int) [symbol(pick)]
endmodule

module STR
  imports STR-SYNTAX
  imports INT
  imports STRING
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Pgm </k> <out> "" </out>
  rule [cat]: <k> cat(S1, S2) => .K ... </k> <out> _ => S1 +String S2 </out>
  rule [tag]: <k> tag(N) => .K ... </k> <out> _ => "é" +String Int2String(N) </out>
  rule [pick]: <k> pick(N) => .K ... </k> <out> _ => #if N <Int 10 #then "é" #else Int2String(N) #fi </out>
endmodule
"#;

const STR_FLOW: &str = "[spec]\nentry = \"str.k\"\nmain_module = \"STR\"\nsyntax_module = \
                        \"STR-SYNTAX\"\n\n[[program]]\nid = \"cat\"\ntext = 'cat(\"ab\", \"cd\")'\n\n\
                        [[program]]\nid = \"tag\"\ntext = \"tag(1)\"\n\n[[program]]\nid = \
                        \"pick\"\ntext = \"pick(2)\"\n";

/// TRIAL3's `concat-drops-long-left` (a left operand longer than 3 characters is dropped), and two
/// mutations whose kills hold a non-ASCII end: always (`tag-shifts`), or below 10 (`pick-shifts`).
const STR_MUTATIONS: &str = r##"
[[mutation]]
id = "concat-drops-long-left"
misunderstanding = "a test mutation"
  [[mutation.edit]]
  rule = "STR.cat"
  find = "S1 +String S2"
  replace = "#if lengthString(S1) >Int 3 #then S2 #else S1 +String S2 #fi"

[[mutation]]
id = "tag-shifts"
misunderstanding = "a test mutation"
  [[mutation.edit]]
  rule = "STR.tag"
  find = "Int2String(N)"
  replace = "Int2String(N +Int 1)"

[[mutation]]
id = "pick-shifts"
misunderstanding = "a test mutation"
  [[mutation.edit]]
  rule = "STR.pick"
  find = "#then \"é\" #else Int2String(N)"
  replace = "#then \"è\" #else Int2String(N +Int 1)"
"##;

const STR_TEMPLATES: &str = r#"
[[template]]
id = "cat-holes"
program = "cat"
  [[template.hole]]
  name = "S"
  sort = "String"
  find = 'cat("ab"'
  literal = '"ab"'
  [[template.hole]]
  name = "T"
  sort = "String"
  find = '"cd")'
  literal = '"cd"'

[[template]]
id = "tag-holes"
program = "tag"
  [[template.hole]]
  name = "N"
  sort = "Int"
  find = "tag(1)"
  literal = "1"
  range = { min = 0, max = 1000 }

[[template]]
id = "pick-holes"
program = "pick"
  [[template.hole]]
  name = "N"
  sort = "Int"
  find = "pick(2)"
  literal = "2"
  range = { min = 0, max = 1000 }
"#;

fn str_flow(name: &str) -> PathBuf {
    scratch_flow(name, "str.k", STR_K, STR_FLOW, STR_MUTATIONS)
}

/// The hole values of a candidate witness case, by hole name.
fn candidate_strings(document: &Value) -> Vec<String> {
    document["attempts"][0]["candidate"]["holes"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|hole| hole["value"]["string"].as_str().map(str::to_owned))
        .collect()
}

/// TRIAL3's SIMPLE flow for its String job (`$T3/simple`): the specification
/// `testdata/k/overload/simple.md` (TRIAL3's `simple.md`, byte-identical), TRIAL3's budget, and its
/// `strings` program.
fn simple_strings_flow(name: &str) -> PathBuf {
    let spec = fs::read_to_string(repository().join("testdata/k/overload/simple.md")).unwrap();
    let manifest = r#"[spec]
entry = "simple.md"
main_module = "SIMPLE-UNTYPED"
syntax_module = "SIMPLE-UNTYPED-SYNTAX"

[budget]
# the clock never decides a run of the tests (R4-WALLCLOCK)
time_ms = 600000
max_depth = 100000
work_factor = 4

[[program]]
id = "strings"
file = "strings.simple"
"#;
    let dir = scratch_flow(name, "simple.md", &spec, manifest, SIMPLE_STRINGS_MUTATIONS);
    fs::write(
        dir.join("strings.simple"),
        r#"// String concatenation and equality.
function main() {
  var s = "ab", t = "cd";
  print(s + t, " ", s == "ab", "\n");
}
"#,
    )
    .unwrap();
    dir
}

/// TRIAL3's `MUTATIONS-t3.toml`: a left operand longer than 3 characters is dropped.
const SIMPLE_STRINGS_MUTATIONS: &str = r#"
[[mutation]]
id = "concat-drops-long-left"
note = "a left operand longer than 3 characters is dropped"

  [[mutation.edit]]
  line = 604
  find = 'Str1 +String Str2'
  replace = '#if lengthString(Str1) >Int 3 #then Str2 #else Str1 +String Str2 #fi'
"#;

/// TRIAL3's `strings-holes` template.
const SIMPLE_STRINGS_TEMPLATES: &str = r#"
[[template]]
id = "strings-holes"
program = "strings"
  [[template.hole]]
  name = "S"
  sort = "String"
  find = 'var s = "ab"'
  literal = '"ab"'
  [[template.hole]]
  name = "T"
  sort = "String"
  find = 't = "cd";'
  literal = '"cd"'
"#;

mod comparable_b {
    use super::*;

    // Each test runs kink, so they belong to the kink tier.
    mod kink_tier {
        use super::*;

        /// ASCII-STRINGS (TRIAL3 item 6, D34), the headline, on TRIAL3's own job: SIMPLE
        /// (`testdata/k/overload/simple.md`, byte-identical to TRIAL3's), its `strings` program with
        /// the `strings-holes` template, and `concat-drops-long-left`. Generated strings are almost
        /// never ASCII. Without the filter the campaign's witness ends on non-ASCII strings, which
        /// kink's end check refuses, so kink confirms no kill (TRIAL3's seeds 0 and 2). With it, the
        /// filter refuses each such hit inside the campaign, its repair replaces the non-ASCII
        /// characters of the String holes (lengths kept), the repaired case is a witness, and kink's
        /// own run kills the mutation with it.
        #[test]
        #[ignore = "kink"]
        fn a_string_hole_kill_is_repaired_into_one_kink_confirms() {
            let dir = simple_strings_flow("simple-strings");
            let kill = |seed, confirm, filter| {
                fuzz_kill(
                    &dir,
                    "MUTATIONS.toml",
                    Some(SIMPLE_STRINGS_TEMPLATES),
                    "strings-holes",
                    "concat-drops-long-left",
                    FuzzOptions {
                        seed,
                        confirm,
                        filter,
                        ..imp_options(300)
                    },
                )
            };
            for seed in [0, 2] {
                let (document, ok) = kill(seed, true, true);
                assert!(ok, "seed {seed}: {:#}", document["action"]);
                assert_eq!(
                    document["stopped"],
                    Value::Null,
                    "seed {seed}: {:#}",
                    document["action"]
                );
                let confirmation = &document["attempts"][0]["confirmation"];
                assert_eq!(
                    confirmation["confirmed"], true,
                    "seed {seed}: {confirmation:#}"
                );
                assert_eq!(confirmation["status"], "killed");
                let strings = candidate_strings(&document);
                assert_eq!(strings.len(), 2, "seed {seed}: {document:#}");
                for text in strings {
                    assert!(text.is_ascii(), "seed {seed}: {text:?}");
                }
                let fuzz = &document["attempts"][0]["fuzz"];
                let refusals = fuzz["client-refusals"].as_array().expect("refusals");
                let refusal = refusals
                    .iter()
                    .find(|refusal| refusal["cause"] == "domain-value-not-ascii")
                    .unwrap_or_else(|| panic!("seed {seed}: {refusals:#?}"));
                let witness = &fuzz["outcome"]["witness"];
                assert_eq!(witness["repaired-from"]["cause"], "domain-value-not-ascii");
                // The entry marks its own case as repaired exactly when `repaired-from` names it.
                assert_eq!(
                    refusal["repaired"],
                    refusal["case"] == witness["repaired-from"]["case"],
                    "seed {seed}: {refusal:#}"
                );
                assert!(
                    fuzz["identity"]["filter"]
                        .as_str()
                        .unwrap()
                        .starts_with("kink-flow/witness-filter/"),
                    "{:#}",
                    fuzz["identity"]
                );
                assert_eq!(document["job"]["filter"]["on"], true);
                // Without the filter, the campaign's witness is one kink refuses (TRIAL3's result).
                let (unfiltered, _) = kill(seed, true, false);
                assert_eq!(
                    unfiltered["stopped"], "unconfirmed",
                    "seed {seed}: {:#}",
                    unfiltered["action"]
                );
                assert_eq!(unfiltered["job"]["filter"]["on"], false);
            }
            // The filter and its repair are functions of the case: the same seed gives the same
            // document (no confirmation, which reads nothing back into the campaign).
            let (first, _) = kill(0, false, true);
            assert!(
                first["attempts"][0]["fuzz"]["outcome"]["witness"]["repaired-from"].is_object()
            );
            assert_eq!(first, kill(0, false, true).0);
        }

        /// A template whose own input the witness filter excludes is refused before any case
        /// (`initial-state-excluded`): `g` is a total function whose value depends on whether
        /// `orBool` skips an operand that may be undefined, which no rule applies (so the definition
        /// has no exclusion of its own), but the template's input `run(g(1))` applies it, and the
        /// filter, which reads a case's initial state without the run's list, refuses every
        /// candidate that keeps it. With `--no-filter` the check is not made, and kink's
        /// confirmation judges each witness by its runs' lists.
        #[test]
        #[ignore = "kink"]
        fn a_template_whose_input_kink_excludes_is_refused_before_any_case() {
            let spec = "module SC-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= run(Bool) [symbol(run)]
  syntax Bool ::= g(Int) [function, total, symbol(g)]
endmodule

module SC
  imports SC-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k> <out> false </out>
  rule g(X) => true orBool (X /Int 0 ==Int 1)
  rule [run]: <k> run(B) => .K </k> <out> _ => B </out>
endmodule
";
            let manifest = "[spec]\nentry = \"sc.k\"\nmain_module = \"SC\"\nsyntax_module = \
                        \"SC-SYNTAX\"\n\n[[program]]\nid = \"one\"\ntext = \"run(g(1))\"\n";
            let dir = scratch_flow("short-circuit-input", "sc.k", spec, manifest, "");
            let templates = "[[template]]\nid = \"one-holes\"\nprogram = \"one\"\n\
                         [[template.hole]]\nname = \"N\"\nsort = \"Int\"\nfind = \"g(1)\"\n\
                         literal = \"1\"\nrange = { min = 0, max = 3 }\n";
            let rule_job = |filter| {
                run_job(
                    &dir,
                    templates,
                    "one-holes",
                    Job::Rule("SC.run".into(), false),
                    FuzzOptions {
                        filter,
                        ..imp_options(5)
                    },
                )
            };
            let (document, ok) = rule_job(true);
            assert!(!ok, "{document:#}");
            assert_eq!(document["job"]["outcome"], "refused", "{document:#}");
            assert_eq!(
                document["job"]["refusal"]["reason"], "initial-state-excluded",
                "{document:#}"
            );
            assert!(
                document["job"]["refusal"]["detail"]
                    .as_str()
                    .unwrap()
                    .contains("short-circuit-reading"),
                "{document:#}"
            );
            let (unfiltered, _) = rule_job(false);
            assert_eq!(unfiltered["job"]["outcome"], "fuzzed", "{unfiltered:#}");
        }

        /// A refusal for every input of the template (`tag` always ends on a non-ASCII string) spends
        /// the budget without a kink run: every hit is refused in the campaign (no repair applies, the
        /// holes are integers), and the campaign stops `client-refused` with a warning, never `budget`
        /// (review M5). Without the filter the first hit is the witness, and kink refuses it; that half
        /// is pinned by `a_witness_kink_refuses_is_unconfirmed_with_kinks_cause`, not here.
        #[test]
        #[ignore = "kink"]
        fn a_systematic_refusal_stops_client_refused_without_kink_runs() {
            let dir = str_flow("str-tag");
            let (document, ok) = fuzz_kill(
                &dir,
                "MUTATIONS.toml",
                Some(STR_TEMPLATES),
                "tag-holes",
                "tag-shifts",
                FuzzOptions {
                    confirm: true,
                    ..imp_options(20)
                },
            );
            assert!(ok, "{:#}", document["action"]);
            assert_eq!(
                document["stopped"], "client-refused",
                "{:#}",
                document["action"]
            );
            let attempt = document["attempts"]
                .as_array()
                .and_then(|attempts| attempts.first())
                .expect("one attempt");
            assert_eq!(
                attempt.get("confirmation"),
                Some(&Value::Null),
                "{attempt:#}"
            );
            assert_eq!(document["program"], Value::Null);
            let reasons = &totals(&document)["unsupported-reasons"];
            assert_eq!(reasons["client-refused"], 20, "{reasons:#}");
            assert_eq!(
                totals(&document)["filter"]["refused"]["domain-value-not-ascii"],
                20,
                "{:#}",
                totals(&document)
            );
            // No repair applies: the holes are integers.
            assert_eq!(totals(&document)["filter"].get("repairs"), None);
            assert!(
                warning_kinds(&document).contains(&"client-refused"),
                "{document:#}"
            );
            let action = document["action"].as_str().unwrap();
            assert!(action.contains("ASCII"), "{action}");
        }

        /// An input-dependent refusal the repair cannot fix (the non-ASCII string comes from the
        /// definition, below 10) does not end the search: the anchor `pick(2)` is refused, a later hit
        /// from 10 on is the witness, and shrinking stops at 10, since the filter refuses every
        /// smaller candidate inside the shrink screen. Without the filter the anchor is the witness,
        /// it shrinks to 0, and kink refuses both.
        #[test]
        #[ignore = "kink"]
        fn an_input_dependent_refusal_is_skipped_and_shrinking_respects_it() {
            let dir = str_flow("str-pick");
            let (document, ok) = fuzz_kill(
                &dir,
                "MUTATIONS.toml",
                Some(STR_TEMPLATES),
                "pick-holes",
                "pick-shifts",
                FuzzOptions {
                    confirm: true,
                    ..imp_options(300)
                },
            );
            assert!(ok, "{:#}", document["action"]);
            assert_eq!(document["stopped"], Value::Null, "{:#}", document["action"]);
            assert_eq!(document["attempts"][0]["confirmation"]["confirmed"], true);
            let fuzz = &document["attempts"][0]["fuzz"];
            let shrunk = &fuzz["outcome"]["witness"]["shrunk"];
            assert_eq!(shrunk["holes"][0]["value"]["int"], "10", "{shrunk:#}");
            assert!(
                fuzz["totals"]["unsupported-reasons"]["client-refused"]
                    .as_u64()
                    .is_some_and(|count| count >= 1),
                "{:#}",
                fuzz["totals"]
            );
            assert!(
                fuzz["totals"]["filter"]["refused-shrink-candidates"]
                    .as_u64()
                    .is_some_and(|count| count >= 1),
                "{:#}",
                fuzz["totals"]
            );
        }
    }
}
