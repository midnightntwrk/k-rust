//! The command layer as a library for a front end (CF-40): parsing and dispatching a command,
//! mutations a front end refuses, the annotation of every rule a document names, next steps in
//! the front end's spelling, and the deterministic verdicts rendering. Every run is of the calc
//! fixture, in corpus order unless a test says otherwise.

mod flow_support;

use flow_support::{copy_dir, flow};
use kink_corpus::load_source;
use kink_flow::{
    CommandFiles, CommandSpelling, FlowCommand, FlowManifest, FrontEnd, InvalidMutation,
    InvalidReason, KinkFlowSpelling, MutationList, OutputFormat, RuleRef, Verb,
    admit::corpus_source,
    cli::{EXIT_CORPUS, EXIT_OK, FuzzJobRequest},
    dispatch,
    hints::Hints,
    memo::resolution_path,
    outcomes::OUTCOMES_DIRECTORY,
    report::{action, action_spelled},
    verdicts::{refusal_details, verdicts},
    visit_rules,
};
use kink_patch::Sha256Digest;
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command,
};

/// A private copy of the calc fixture for one test.
fn calc(test: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-front-end-{}", std::process::id()))
        .join(test)
        .join("calc");
    let _ = fs::remove_dir_all(&dir);
    copy_dir(&flow("calc"), &dir);
    dir
}

fn strings(options: &[&str]) -> Vec<String> {
    options.iter().map(|option| (*option).to_owned()).collect()
}

/// Parse `verb` with `files` and `options` and dispatch it on `dir`'s FLOW.toml for `front`.
fn command(
    dir: &Path,
    verb: &str,
    files: CommandFiles,
    options: &[&str],
    front: FrontEnd<'_>,
) -> (Value, u8) {
    let command = FlowCommand::parse(verb, files, &strings(options)).expect("the command parses");
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    dispatch(manifest, command, front).expect("the command's thread does not panic")
}

fn mutations(dir: &Path) -> CommandFiles {
    CommandFiles {
        mutations: Some(dir.join("MUTATIONS.toml")),
        ..CommandFiles::default()
    }
}

/// A refusal by a front end's own check.
fn refusal() -> InvalidMutation {
    InvalidMutation {
        edit: Some(0),
        reason: InvalidReason::External {
            name: "generated-only",
            next: "edit the authored node instead",
        },
        detail: "the edit changes only a node the front end generated".into(),
    }
}

fn refusing(id: &str) -> FrontEnd<'static> {
    FrontEnd {
        refused: BTreeMap::from([(id.to_owned(), refusal())]),
        ..FrontEnd::default()
    }
}

fn row<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no row {id}: {document:#}"))
}

/// Every file under `dir`, relative to it.
fn files(dir: &Path) -> BTreeSet<PathBuf> {
    let mut found = BTreeSet::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(next) = stack.pop() {
        let Ok(entries) = fs::read_dir(&next) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else {
                found.insert(path.strip_prefix(dir).unwrap().to_path_buf());
            }
        }
    }
    found
}

#[test]
fn kink_flow_options_parse_with_the_front_end_files() {
    let dir = flow("calc");
    // run takes its list from the files, and checks `--only` against it.
    let parsed = FlowCommand::parse(
        "run",
        mutations(&dir),
        &strings(&[
            "--only", "no-mul", "--order", "corpus", "--output", "verdicts",
        ]),
    )
    .unwrap();
    assert_eq!(parsed.verb(), Verb::Run);
    assert_eq!(parsed.output(), OutputFormat::Verdicts);
    let FlowCommand::Run { options, .. } = &parsed else {
        panic!("{parsed:?}");
    };
    assert_eq!(options.only, ["no-mul"]);
    assert_eq!(
        FlowCommand::parse("run", mutations(&dir), &strings(&["--only", "nope"])).unwrap_err(),
        "--only nope: no mutation has this id"
    );
    assert!(FlowCommand::parse("run", CommandFiles::default(), &[]).is_err());
    assert_eq!(
        FlowCommand::parse("run", mutations(&dir), &strings(&["--output", "text"])).unwrap_err(),
        "--output \"text\": expected json or verdicts"
    );
    // check and results take the front end's list unless `--mutations` names one.
    let FlowCommand::Check(options) = FlowCommand::parse("check", mutations(&dir), &[]).unwrap()
    else {
        panic!("check");
    };
    assert_eq!(options.mutations, Some(dir.join("MUTATIONS.toml")));
    let statuses = dir.join("MUTATIONS-statuses.toml");
    let FlowCommand::Results { options, output } = FlowCommand::parse(
        "results",
        mutations(&dir),
        &strings(&["--mutations", statuses.to_str().unwrap()]),
    )
    .unwrap() else {
        panic!("results");
    };
    assert_eq!(options.mutations, Some(statuses));
    assert_eq!(output, OutputFormat::Json);
    // A fuzz kill job takes the front end's list when `--mutations` is not given (FLOW.toml
    // stands for the template list: one that does not decode is the command's refusal, so the
    // template id is not checked here).
    let templates = CommandFiles {
        templates: Some(dir.join("FLOW.toml")),
        ..mutations(&dir)
    };
    let FlowCommand::Fuzz { request, .. } = FlowCommand::parse(
        "fuzz",
        templates,
        &strings(&["--template", "t", "--kill", "no-mul"]),
    )
    .unwrap() else {
        panic!("fuzz");
    };
    assert!(matches!(
        request.job,
        FuzzJobRequest::Kill { ref mutations, .. } if *mutations == dir.join("MUTATIONS.toml")
    ));
    assert_eq!(
        FlowCommand::parse("nope", CommandFiles::default(), &[]).unwrap_err(),
        "unknown command \"nope\""
    );
}

#[test]
fn a_refused_mutation_runs_nothing_and_writes_nothing() {
    let dir = calc("refused-alone");
    let (document, status) = command(
        &dir,
        "run",
        mutations(&dir),
        &["--only", "sub-off-by-one", "--order", "corpus"],
        refusing("sub-off-by-one"),
    );
    assert_eq!(status, EXIT_CORPUS, "{document:#}");
    let refused = row(&document, "sub-off-by-one");
    assert_eq!(refused["status"], "invalid-mutation", "{refused:#}");
    assert_eq!(refused["reason"], "generated-only");
    assert_eq!(refused["edit"], 0);
    assert_eq!(
        refused["detail"],
        "the edit changes only a node the front end generated"
    );
    assert_eq!(
        refused["action"],
        "fix the mutation: edit the authored node instead (reason, edit, detail)"
    );
    assert_eq!(refused["executed"], json!([]));
    assert_eq!(refused["calls"], json!([]));
    assert_eq!(refused["killer"], Value::Null);
    assert_eq!(refused["rules"], Value::Null);
    assert_eq!(document["counts"]["invalid-mutation"], 1, "{document:#}");
    // No outcome record or hint: the only mutation selected was refused. Every other mutation of
    // the list is resolved (for `untargeted_rules`), so its resolution memo is written; the
    // refused one's is not.
    let cache = dir.join(".kink-flow");
    let written = files(&cache);
    assert!(
        !written
            .iter()
            .any(|path| path.starts_with(OUTCOMES_DIRECTORY)),
        "{written:?}"
    );
    let spec = Sha256Digest::parse(document["spec"]["digest"].as_str().unwrap()).unwrap();
    let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
    for mutation in &list.mutations {
        let memo = resolution_path(&cache, spec, mutation);
        assert_eq!(
            memo.is_file(),
            mutation.id != "sub-off-by-one",
            "{}: {written:?}",
            mutation.id
        );
    }
    assert!(Hints::read(&cache).is_empty());
}

/// A fuzz kill job of a mutation the front end refused is refused before anything runs, with the
/// front end's next step.
#[test]
fn a_fuzz_kill_job_of_a_refused_mutation_is_refused() {
    let dir = calc("refused-fuzz");
    let templates = dir.join("TEMPLATES.toml");
    fs::write(
        &templates,
        "[[template]]\nid = \"inline-holes\"\nprogram = \"inline\"\n\n  [[template.hole]]\n  \
         name = \"A\"\n  sort = \"Int\"\n  find = \"2 *\"\n  literal = \"2\"\n  range = { \
         min = 0, max = 3 }\n",
    )
    .unwrap();
    let files = CommandFiles {
        templates: Some(templates),
        ..mutations(&dir)
    };
    let (document, status) = command(
        &dir,
        "fuzz",
        files,
        &[
            "--template",
            "inline-holes",
            "--kill",
            "sub-off-by-one",
            "--no-confirm",
        ],
        refusing("sub-off-by-one"),
    );
    assert_eq!(status, EXIT_CORPUS, "{document:#}");
    assert_eq!(document["job"]["outcome"], "refused", "{document:#}");
    assert_eq!(document["job"]["reason"], "generated-only", "{document:#}");
    assert_eq!(
        document["action"],
        "fix the mutation: edit the authored node instead (kink-flow run gives the same status)"
    );
}

#[test]
fn a_refused_mutation_leaves_the_other_rows_as_without_it() {
    let refused_dir = calc("refused-list");
    let plain_dir = calc("plain-list");
    let options = ["--order", "corpus"];
    let (with, status) = command(
        &refused_dir,
        "run",
        mutations(&refused_dir),
        &options,
        refusing("sub-off-by-one"),
    );
    assert_eq!(status, EXIT_CORPUS, "{with:#}");
    let (without, status) = command(
        &plain_dir,
        "run",
        mutations(&plain_dir),
        &options,
        FrontEnd::default(),
    );
    assert_eq!(status, EXIT_OK, "{without:#}");
    let key = |row: &Value| {
        (
            row["status"].clone(),
            row["reason"].clone(),
            row["killer"].clone(),
            row["executed"].as_array().map(|executed| {
                executed
                    .iter()
                    .map(|e| e["program"].clone())
                    .collect::<Vec<_>>()
            }),
        )
    };
    for plain in without["mutations"].as_array().unwrap() {
        let id = plain["id"].as_str().unwrap();
        if id == "sub-off-by-one" {
            assert_eq!(plain["status"], "killed");
            assert_eq!(row(&with, id)["status"], "invalid-mutation");
            continue;
        }
        assert_eq!(key(row(&with, id)), key(plain), "{id}");
    }
    // `check --mutations` refuses it too, with the front end's reason and next step.
    let (checked, status) = command(
        &refused_dir,
        "check",
        mutations(&refused_dir),
        &[],
        refusing("sub-off-by-one"),
    );
    assert_eq!(status, EXIT_CORPUS, "{checked:#}");
    let checked_row = row(&checked, "sub-off-by-one");
    assert_eq!(checked_row["outcome"], "refused", "{checked_row:#}");
    assert_eq!(checked_row["refusals"][0]["reason"], "generated-only");
    assert_eq!(
        checked_row["refusals"][0]["next"],
        "edit the authored node instead"
    );
    assert_eq!(row(&checked, "add-becomes-sub")["outcome"], "ok");
    let (_, status) = command(
        &refused_dir,
        "check",
        mutations(&refused_dir),
        &[],
        FrontEnd::default(),
    );
    assert_eq!(status, EXIT_OK);
}

/// Every object of `document` with a string `module` and an unsigned `index`, by its JSON
/// pointer.
fn rule_objects(value: &Value, pointer: &str, into: &mut BTreeSet<String>) {
    match value {
        Value::Object(object) => {
            if object.get("module").is_some_and(Value::is_string)
                && object.get("index").is_some_and(Value::is_u64)
            {
                into.insert(pointer.to_owned());
            }
            for (key, value) in object {
                rule_objects(value, &format!("{pointer}/{key}"), into);
            }
        }
        Value::Array(values) => {
            for (index, value) in values.iter().enumerate() {
                rule_objects(value, &format!("{pointer}/{index}"), into);
            }
        }
        _ => {}
    }
}

/// Mark every visited object with a unique `visit` number and return the visits.
fn visited(document: &mut Value) -> Vec<RuleRef> {
    let mut visits = Vec::new();
    visit_rules(document, &mut |rule, object: &mut Map<String, Value>| {
        assert!(!object.contains_key("visit"), "visited twice: {object:?}");
        object.insert("visit".into(), json!(visits.len()));
        visits.push(rule.clone());
    });
    visits
}

const SCFETCH_K: &str = include_str!("../../../testdata/k/r0c/scfetch.k");

/// A private flow over kink-native's fixture `r0c/scfetch.k`, whose definition kink excludes
/// (`short-circuit-reading`): every document's `spec.exclusion` names the rules `fetch` and
/// `fetch-halt-bug` and the equation of `decode` through which each depends on the reading.
fn scfetch(test: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-front-end-{}", std::process::id()))
        .join(test)
        .join("scfetch");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("scfetch.k"), SCFETCH_K).unwrap();
    fs::write(
        dir.join("FLOW.toml"),
        "[spec]\nentry = \"scfetch.k\"\nmain_module = \"SCFETCH\"\nsyntax_module = \
         \"SCFETCH-SYNTAX\"\n\n[[program]]\nid = \"fetch\"\ntext = \"# fetch\"\n",
    )
    .unwrap();
    dir
}

/// Every object of `documents` with a string `module` and an unsigned `index` is visited once,
/// and names a baseline sentence of `loaded` with that sentence's label.
fn assert_every_rule_visited_once(
    loaded: &kink_corpus::LoadedSource,
    documents: Vec<(&str, Value)>,
) -> Vec<(String, Value)> {
    let mut marked_documents = Vec::new();
    for (name, mut document) in documents {
        let mut expected = BTreeSet::new();
        rule_objects(&document, "", &mut expected);
        assert!(!expected.is_empty(), "{name}: no rule objects");
        let visits = visited(&mut document);
        let mut marked = BTreeSet::new();
        rule_objects(&document, "", &mut marked);
        assert_eq!(marked, expected, "{name}");
        assert_eq!(visits.len(), expected.len(), "{name}");
        for rule in &visits {
            // Each names a sentence of the baseline, with that sentence's label when it has one.
            let sentence = loaded
                .baseline
                .sentence(&rule.at)
                .unwrap_or_else(|| panic!("{name}: {:?} is no baseline sentence", rule.at));
            let label = sentence
                .attributes()
                .string(k_rust::definition::AttributeKey::Label);
            if let Some(given) = &rule.label {
                assert_eq!(Some(given.as_str()), label, "{name}: {:?}", rule.at);
            }
        }
        marked_documents.push((name.to_owned(), document));
    }
    marked_documents
}

/// The rules of every document visited; in an excluded definition's documents, every compiled
/// sentence an exclusion cause names (the rule, each function link's equation) carries the
/// baseline sentences it was compiled from, and each of them is visited.
#[test]
fn every_rule_a_document_names_is_visited_once() {
    let dir = calc("names");
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let loaded = load_source(&corpus_source(&manifest)).unwrap();
    let (results, _) = command(&dir, "results", mutations(&dir), &[], FrontEnd::default());
    let (run, _) = command(
        &dir,
        "run",
        mutations(&dir),
        &["--order", "corpus"],
        FrontEnd::default(),
    );
    let (check, _) = command(&dir, "check", mutations(&dir), &[], FrontEnd::default());
    assert_every_rule_visited_once(
        &loaded,
        vec![("results", results), ("run", run), ("check", check)],
    );

    let dir = scfetch("names-exclusion");
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let loaded = load_source(&corpus_source(&manifest)).unwrap();
    let (check, status) = command(
        &dir,
        "check",
        CommandFiles::default(),
        &[],
        FrontEnd::default(),
    );
    assert_eq!(status, EXIT_CORPUS, "{check:#}");
    let (results, _) = command(
        &dir,
        "results",
        CommandFiles::default(),
        &[],
        FrontEnd::default(),
    );
    for (name, document) in
        assert_every_rule_visited_once(&loaded, vec![("check", check), ("results", results)])
    {
        let exclusion = &document["spec"]["exclusion"];
        assert_eq!(exclusion["exclusion"], "short-circuit-reading", "{name}");
        let causes = exclusion["causes"].as_array().unwrap();
        assert_eq!(causes.len(), 2, "{name}: {exclusion:#}");
        for cause in causes {
            let equations = cause["links"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|link| link["link"] == "function")
                .map(|link| &link["equation"]);
            for sentence in std::iter::once(&cause["rule"]).chain(equations) {
                let authors = sentence["authors"].as_array().unwrap();
                assert_eq!(authors.len(), 1, "{name}: {sentence:#}");
                let author = &authors[0];
                assert!(
                    author["visit"].is_u64(),
                    "{name}: not visited: {sentence:#}"
                );
                // The baseline sentence is the one the compiled sentence's position names.
                assert_eq!(author["module"], sentence["module"], "{name}: {sentence:#}");
                assert_eq!(
                    author["start_line"], sentence["location"]["start_line"],
                    "{name}: {sentence:#}"
                );
            }
        }
    }
}

/// An annotation as a front end writes it: the sentence's name in the front end's terms.
fn annotate(document: &mut Value) {
    visit_rules(document, &mut |rule, object| {
        object.insert(
            "krs".into(),
            json!({"item": format!("item-{}-{}", rule.at.module, rule.at.index)}),
        );
    });
}

#[test]
fn the_annotation_reaches_the_printed_and_the_stored_run_document() {
    let dir = calc("annotate");
    let front = || FrontEnd {
        annotate: Some(&annotate),
        ..FrontEnd::default()
    };
    let (run, status) = command(
        &dir,
        "run",
        mutations(&dir),
        &["--order", "corpus"],
        front(),
    );
    assert_eq!(status, EXIT_OK, "{run:#}");
    let mut objects = BTreeSet::new();
    rule_objects(&run, "", &mut objects);
    let mut annotated = 0;
    visit_rules(&mut run.clone(), &mut |_, object| {
        assert!(object.contains_key("krs"), "{object:?}");
        annotated += 1;
    });
    assert_eq!(annotated, objects.len());
    // `report` prints what `run` printed.
    let (report, status) = command(&dir, "report", CommandFiles::default(), &[], front());
    assert_eq!(status, EXIT_OK);
    assert_eq!(report, run);
    // The results rendering names each rule by its front-end item.
    let (results, _) = command(&dir, "results", CommandFiles::default(), &[], front());
    let rendered = verdicts(&results).unwrap();
    assert!(rendered.contains("fired = [\"item-"), "{rendered}");
}

/// A front end's spelling: its program, then its selection of the corpus.
struct Krs;

impl CommandSpelling for Krs {
    fn command(&self, verb: Verb) -> String {
        format!("krs kink {} --definition main", verb.as_str())
    }
}

#[test]
fn next_steps_name_the_front_end_command() {
    let krs = Krs;
    assert_eq!(krs.command(Verb::Run), "krs kink run --definition main");
    assert_eq!(krs.verb(Verb::Run), "krs kink run --definition main");
    assert_eq!(
        KinkFlowSpelling.command(Verb::Run),
        "kink-flow run FLOW.toml MUTATIONS.toml"
    );
    assert_eq!(KinkFlowSpelling.verb(Verb::Results), "kink-flow results");
    let conflict = action_spelled("error", Some("outcome-conflict"), &krs).unwrap();
    assert!(
        conflict.ends_with("run `krs kink run --definition main --verify`"),
        "{conflict}"
    );
    let corpus = action_spelled("error", Some("baseline-mismatch:add"), &krs).unwrap();
    assert!(
        corpus.ends_with("run `krs kink results --definition main --verify`"),
        "{corpus}"
    );
    // Under kink-flow's own spelling every action is the one `action` gives.
    let reasons = [
        None,
        Some("baseline-findings"),
        Some("mutant-findings"),
        Some("inconsistent-mutant"),
        Some("host-stack-refused"),
        Some("outcome-conflict"),
        Some("baseline-mismatch:add"),
        Some("program-refused:add"),
        Some("no-comparable-program"),
        Some("resolution-mismatch"),
        Some("outcome-mismatch:add"),
        Some("campaign-refused"),
    ];
    for status in kink_flow::search::STATUSES {
        for reason in reasons {
            assert_eq!(
                action_spelled(status, reason, &KinkFlowSpelling).as_deref(),
                action(status, reason),
                "{status} {reason:?}"
            );
        }
    }
    // The missing report's next step, through `dispatch`.
    let dir = calc("spelling");
    let front = FrontEnd {
        spelling: &krs,
        ..FrontEnd::default()
    };
    let (missing, status) = command(&dir, "report", CommandFiles::default(), &[], front);
    assert_eq!(status, EXIT_CORPUS);
    let detail = missing["detail"].as_str().unwrap();
    assert!(
        detail.ends_with("run `krs kink run --definition main` first"),
        "{detail}"
    );
    // The check document's coverage detail, with no result records yet.
    let front = FrontEnd {
        spelling: &krs,
        ..FrontEnd::default()
    };
    let (checked, _) = command(&dir, "check", mutations(&dir), &[], front);
    let detail = checked["coverage"]["detail"].as_str().unwrap();
    assert!(
        detail.contains("(run `krs kink results --definition main`)"),
        "{detail}"
    );
}

/// Rewrite every result record's `wall_ms` in `dir`'s cache so that cost order is the reverse
/// of corpus order; `wall_ms` is outside the key, so every record stays in use.
fn reverse_costs(dir: &Path, results: &Value) {
    let programs = results["programs"].as_array().unwrap();
    let records = dir.join(".kink-flow").join("results").join(
        results["spec"]["execution_digest"]["digest"]
            .as_str()
            .unwrap(),
    );
    let mut rewritten = 0;
    for (index, program) in programs.iter().enumerate() {
        let path = records.join(format!("{}.json", program["digest"].as_str().unwrap()));
        let mut record: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        record["wall_ms"] = json!((programs.len() - index) * 1000);
        fs::write(&path, record.to_string()).unwrap();
        rewritten += 1;
    }
    assert_eq!(rewritten, programs.len());
}

#[test]
fn verdicts_do_not_depend_on_the_cache_or_the_order() {
    let corpus = calc("verdicts-corpus");
    let cost = calc("verdicts-cost");
    let document = |dir: &Path, verb: &str, options: &[&str]| {
        let files = if verb == "run" {
            mutations(dir)
        } else {
            CommandFiles::default()
        };
        command(dir, verb, files, options, FrontEnd::default()).0
    };
    let render =
        |dir: &Path, verb: &str, options: &[&str]| verdicts(&document(dir, verb, options)).unwrap();
    let cold_results = render(&corpus, "results", &[]);
    let cold_document = document(&corpus, "run", &["--order", "corpus"]);
    let cold = verdicts(&cold_document).unwrap();
    let warm = render(&corpus, "run", &["--order", "corpus"]);
    let warm_results = render(&corpus, "results", &[]);
    // Cost order, made the reverse of corpus order, on a cache with result records and no
    // outcome record or hint.
    let cost_results = document(&cost, "results", &[]);
    reverse_costs(&cost, &cost_results);
    let cost_document = document(&cost, "run", &["--order", "cost"]);
    let executed = |document: &Value| {
        document["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| {
                row["executed"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|entry| entry["program"].clone())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    };
    assert_ne!(
        executed(&cold_document),
        executed(&cost_document),
        "the cost order ran the programs in another order"
    );
    let other_order = verdicts(&cost_document).unwrap();
    assert_eq!(cold, warm);
    assert_eq!(cold, other_order);
    assert_eq!(cold_results, warm_results);
    assert!(cold.starts_with(
        "schema = \"kink-flow-verdicts\"\nversion = 1\ndocument = \"run\"\n\n[spec]\noutcome = \
         \"admitted\"\n"
    ));
    assert!(
        cold.contains("\n[[mutation]]\nid = \"add-swaps-operands\"\nstatus = \"survived\"\n"),
        "{cold}"
    );
    assert!(
        cold.contains("\n[[mutation]]\nid = \"add-becomes-sub\"\nstatus = \"killed\"\n"),
        "{cold}"
    );
    assert!(
        cold_results.contains("\n[[case]]\nid = \"add\"\nclass = \"comparable\"\n"),
        "{cold_results}"
    );
    // A document that is neither is refused, naming what it is.
    assert!(
        verdicts(&json!({"schema": "kink-flow-check"}))
            .unwrap_err()
            .contains("kink-flow-check")
    );
}

#[test]
fn the_command_line_prints_verdicts() {
    let dir = calc("command-line");
    let output = Command::new(env!("CARGO_BIN_EXE_kink-flow"))
        .args(["results"])
        .arg(dir.join("FLOW.toml"))
        .args(["--output", "verdicts"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_OK)));
    let printed = String::from_utf8(output.stdout).unwrap();
    let (document, _) = command(
        &dir,
        "results",
        CommandFiles::default(),
        &[],
        FrontEnd::default(),
    );
    assert_eq!(printed, verdicts(&document).unwrap());
    // A mutation list that does not decode: the run document has no specification, and the
    // rendering says that the list was refused; its text goes to stderr.
    let bad = dir.join("bad.toml");
    fs::write(&bad, "this is not TOML [").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kink-flow"))
        .arg("run")
        .arg(dir.join("FLOW.toml"))
        .arg(&bad)
        .args(["--output", "verdicts"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_CORPUS)));
    let printed = String::from_utf8(output.stdout).unwrap();
    assert_eq!(
        printed,
        "schema = \"kink-flow-verdicts\"\nversion = 1\ndocument = \"run\"\n\n\
         [mutation_list]\noutcome = \"refused\"\n"
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.starts_with("kink-flow: mutation_list: refused: "),
        "{stderr}"
    );
    // A manifest that does not decode: the stage and the reason, and the key on stderr.
    let bad_flow = dir.join("BAD-FLOW.toml");
    fs::write(&bad_flow, "[spec]\nentry = 3\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kink-flow"))
        .arg("results")
        .arg(&bad_flow)
        .args(["--output", "verdicts"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_CORPUS)));
    let printed = String::from_utf8(output.stdout).unwrap();
    assert!(
        printed.ends_with(
            "[spec]\noutcome = \"refused\"\nstage = \"manifest\"\nreason = \"invalid-manifest\"\n"
        ),
        "{printed}"
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.starts_with("kink-flow: spec: manifest invalid-manifest: ")
            && stderr.contains("spec.entry"),
        "{stderr}"
    );
    // A stopped run renders where it stopped; the details name the stop and its text.
    let stopped = json!({
        "schema": "kink-flow-run",
        "spec": {"outcome": "admitted"},
        "mutations": [
            {"id": "a", "status": "killed"},
            {"id": "b", "status": "error", "reason": "baseline-mismatch:add", "detail": "drift"},
        ],
        "stopped": {"mutation": "b", "reason": "baseline-mismatch:add"},
    });
    assert!(
        verdicts(&stopped)
            .unwrap()
            .ends_with("\n[stopped]\nmutation = \"b\"\nreason = \"baseline-mismatch:add\"\n")
    );
    assert_eq!(
        refusal_details(&stopped),
        ["stopped at b: baseline-mismatch:add: drift"]
    );
    // A KRS corpus is refused by kink-flow, naming the command to use.
    fs::write(
        dir.join("FLOW.toml"),
        "[spec]\nkrs = { definition = \"main\" }\n",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kink-flow"))
        .arg("check")
        .arg(dir.join("FLOW.toml"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_CORPUS)));
    let document: Value = serde_json::from_slice(&output.stdout).unwrap();
    let detail = document["spec"]["detail"].as_str().unwrap();
    assert!(
        detail.starts_with("spec.krs: a KRS corpus: run `krs kink"),
        "{detail}"
    );
}
