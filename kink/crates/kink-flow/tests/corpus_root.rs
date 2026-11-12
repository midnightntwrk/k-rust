//! `[corpus] root` (CORPUS-ROOT): a flow reads its cases from a corpus root it names, and two
//! flows that name one root give each case the same id.
//!
//! A case's inputs are values of a machine's inputs, which several definitions of one interface
//! take alike; every other file of a flow is a function of one definition. The workspace of
//! these tests has one corpus root, `corpus/`, with calc's programs, and two flows beside two
//! definitions of calc's language: `spec/` (the calc fixture) and `variant/` (the same language
//! whose addition adds its operands in the other order). Each flow keeps its definition, its
//! mutations, its record and its cache in its own directory, and reads `../corpus`.

mod flow_support;

use flow_support::flow;
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_flow::{
    FlowManifest, FrontEnd, ManifestError,
    cli::{CommandFiles, EXIT_YES, FlowCommand},
    dispatch,
    fuzz::{FuzzJob, FuzzOptions, TemplateList, fuzz_job},
    lock::LOCK_FILE,
    results::CACHE_DIRECTORY,
};
use serde_json::{Value, json};
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
};

/// How a message names the root the flows name.
const ROOT_NAME: &str = "the corpus root `../corpus`";

const PROGRAMS: [(&str, &str); 3] = [("a1", "1 + 2"), ("m1", "2 * 3"), ("s1", "5 - 1")];

/// The ids the programs have in every flow that names the root: their paths relative to it.
const IDS: [&str; 3] = ["programs/a1.calc", "programs/m1.calc", "programs/s1.calc"];

/// A flow of calc's language that reads the corpus root.
const FLOW: &str = "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \
                    \"CALC-SYNTAX\"\n\n[corpus]\nroot = \"../corpus\"\n\n";

const GLOB: &str = "[[program]]\nfiles = \"programs/*.calc\"\n";

/// One mutation of each flow's addition, written against that flow's definition.
fn mutations(sum: &str, wrong: &str) -> String {
    format!(
        "[[mutation]]\nid = \"add-becomes-sub\"\nmisunderstanding = \"addition evaluates as \
         subtraction\"\n  [[mutation.edit]]\n  rule = \"add\"\n  find = \"{sum}\"\n  replace = \
         \"{wrong}\"\n\n[[mutation]]\nid = \"mul-becomes-add\"\nmisunderstanding = \
         \"multiplication evaluates as addition\"\n  [[mutation.edit]]\n  rule = \"mul\"\n  find \
         = \"I1 *Int I2\"\n  replace = \"I1 +Int I2\"\n"
    )
}

/// A fresh workspace for one test: the corpus root and the two flows, each with `programs` as
/// its `[[program]]` entries.
fn workspace(name: &str, programs: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-corpus-root-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("corpus/programs")).unwrap();
    for (id, text) in PROGRAMS {
        fs::write(dir.join(format!("corpus/programs/{id}.calc")), text).unwrap();
    }
    let calc = fs::read_to_string(flow("calc").join("calc.k")).unwrap();
    let variant = calc.replace("=> I1 +Int I2", "=> I2 +Int I1");
    assert_ne!(calc, variant);
    for (flow, definition, mutations) in [
        ("spec", calc, mutations("I1 +Int I2", "I1 -Int I2")),
        ("variant", variant, mutations("I2 +Int I1", "I2 -Int I1")),
    ] {
        let flow = dir.join(flow);
        fs::create_dir_all(&flow).unwrap();
        fs::write(flow.join("calc.k"), definition).unwrap();
        fs::write(flow.join("FLOW.toml"), format!("{FLOW}{programs}")).unwrap();
        fs::write(flow.join("MUTATIONS.toml"), mutations).unwrap();
    }
    dir
}

fn read(flow: &Path) -> Result<FlowManifest, ManifestError> {
    FlowManifest::read(&flow.join("FLOW.toml"))
}

fn ids(manifest: &FlowManifest) -> Vec<&str> {
    manifest
        .programs
        .iter()
        .map(|program| program.id.as_str())
        .collect()
}

/// `kink-flow VERB` on the flow in `flow`, with its own mutation list and `patterns`.
fn command(flow: &Path, verb: &str, patterns: Option<&Path>, options: &[&str]) -> (Value, u8) {
    let files = CommandFiles {
        mutations: matches!(verb, "run" | "prune").then(|| flow.join("MUTATIONS.toml")),
        patterns: patterns.map(Path::to_path_buf),
        templates: None,
    };
    let options = options.iter().map(|o| (*o).to_owned()).collect::<Vec<_>>();
    let command = FlowCommand::parse(verb, files, &options).unwrap();
    dispatch(read(flow).unwrap(), command, FrontEnd::default()).unwrap()
}

/// Every file under `dir`, sorted.
fn listing(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(next) = stack.pop() {
        for entry in fs::read_dir(&next).unwrap() {
            let entry = entry.unwrap();
            if entry.file_type().unwrap().is_dir() {
                stack.push(entry.path());
            } else {
                files.push(entry.path());
            }
        }
    }
    files.sort();
    files
}

/// The program ids a corpus record names: its killers.
fn recorded_programs(lock: &str) -> BTreeSet<String> {
    let record: toml::Table = lock.parse().unwrap();
    let mut programs = BTreeSet::new();
    let mut stack = vec![toml::Value::Table(record)];
    while let Some(value) = stack.pop() {
        match value {
            toml::Value::Table(table) => {
                for (key, value) in table {
                    match (&*key, value) {
                        ("killer" | "witness" | "program", toml::Value::String(id)) => {
                            programs.insert(id);
                        }
                        (_, value) => stack.push(value),
                    }
                }
            }
            toml::Value::Array(values) => stack.extend(values),
            _ => {}
        }
    }
    programs
}

/// Two flows of two definitions over one corpus root: each decodes the same program ids (the
/// paths relative to the root), `coverage` and `run` pass in both, and both records name their
/// killers by those ids. Each flow's record and cache are beside the flow, and nothing is
/// written under the root.
#[test]
fn two_flows_of_one_corpus_root_give_each_case_one_id() {
    let dir = workspace("two-flows", GLOB);
    let root_files = listing(&dir.join("corpus"));
    let mut records = Vec::new();
    for flow in ["spec", "variant"] {
        let flow = dir.join(flow);
        let manifest = read(&flow).unwrap();
        assert_eq!(ids(&manifest), IDS);
        assert_eq!(manifest.corpus.as_ref().unwrap().root, "../corpus");
        let lock = flow.join(LOCK_FILE);
        let lock_option = lock.to_str().unwrap();

        let (coverage, status) = command(&flow, "coverage", None, &["--lock", lock_option]);
        assert_eq!(status, EXIT_YES, "{coverage:#}");
        let rows = coverage["programs"].as_array().unwrap();
        let covered = rows
            .iter()
            .map(|row| (row["id"].as_str().unwrap(), row["class"].as_str().unwrap()))
            .collect::<Vec<_>>();
        assert_eq!(covered, IDS.map(|id| (id, "comparable")), "{coverage:#}");

        let (run, status) = command(&flow, "run", None, &["--lock", lock_option]);
        assert_eq!(status, EXIT_YES, "{run:#}");
        let killers = run["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| (row["id"].as_str().unwrap(), row["killer"].as_str()))
            .collect::<Vec<_>>();
        assert_eq!(
            killers,
            [
                ("add-becomes-sub", Some("programs/a1.calc")),
                ("mul-becomes-add", Some("programs/m1.calc"))
            ],
            "{run:#}"
        );
        // The flow's own files are beside it.
        assert!(flow.join(CACHE_DIRECTORY).is_dir());
        records.push(fs::read_to_string(&lock).unwrap());
    }
    let programs = recorded_programs(&records[0]);
    assert_eq!(
        programs,
        BTreeSet::from(["programs/a1.calc".to_owned(), "programs/m1.calc".to_owned()]),
        "{}",
        records[0]
    );
    assert_eq!(programs, recorded_programs(&records[1]), "{}", records[1]);
    assert_eq!(listing(&dir.join("corpus")), root_files);
}

/// The root as written is in no key: a flow at another depth, which names the same root by
/// another path, reads the first flow's cache and runs no baseline again.
#[test]
fn where_the_root_is_relative_to_the_flow_is_in_no_key() {
    let dir = workspace("no-key", GLOB);
    let spec = dir.join("spec");
    let (cold, status) = command(&spec, "coverage", None, &[]);
    assert_eq!(status, EXIT_YES, "{cold:#}");
    assert_eq!(
        cold["baseline_runs"],
        json!({"diagnostic": 0, "live": 3, "reused": 0}),
        "{cold:#}"
    );

    let deeper = dir.join("flows/deeper/spec");
    flow_support::copy_all(&spec, &deeper);
    fs::write(
        deeper.join("FLOW.toml"),
        format!("{FLOW}{GLOB}").replace("../corpus", "../../../corpus"),
    )
    .unwrap();
    let (warm, status) = command(&deeper, "coverage", None, &[]);
    assert_eq!(status, EXIT_YES, "{warm:#}");
    assert_eq!(
        warm["baseline_runs"],
        json!({"diagnostic": 0, "live": 0, "reused": 0}),
        "{warm:#}"
    );
    for (cold, warm) in cold["programs"]
        .as_array()
        .unwrap()
        .iter()
        .zip(warm["programs"].as_array().unwrap())
    {
        assert_eq!(cold["id"], warm["id"]);
        assert_eq!(
            (&cold["cached"], &warm["cached"]),
            (&json!(false), &json!(true))
        );
        assert_eq!(cold["digest"], warm["digest"]);
    }
    assert_eq!(cold["spec"]["digest"], warm["spec"]["digest"]);
}

#[track_caller]
fn assert_error(flow: &Path, key: &str, message: &str) {
    let error = read(flow).unwrap_err();
    assert_eq!(error.key, key, "{error}");
    assert!(error.message.contains(message), "{error}");
}

/// `[corpus]` is decoded strictly: `root` is a relative path to a directory, and the paths of
/// the cases are relative to it, while a pattern list stays relative to the flow's directory.
#[test]
fn the_corpus_section_is_decoded_strictly() {
    let dir = workspace("decode", GLOB);
    let spec = dir.join("spec");
    let write = |corpus: &str, programs: &str| {
        let text = format!("{FLOW}{programs}").replace("[corpus]\nroot = \"../corpus\"\n", corpus);
        fs::write(spec.join("FLOW.toml"), text).unwrap();
    };
    write("[corpus]\nroot = \"../corpus\"\nrot = 1\n", GLOB);
    assert_error(&spec, "corpus.rot", "unknown key");
    write("[corpus]\n", GLOB);
    assert_error(&spec, "corpus.root", "missing");
    write("[corpus]\nroot = \"/corpus\"\n", GLOB);
    assert_error(&spec, "corpus.root", "is absolute");
    write("[corpus]\nroot = \"../gone\"\n", GLOB);
    assert_error(&spec, "corpus.root", "is no directory");

    // A pattern is matched under the root: the flow's own directory has no `programs/`.
    write("", GLOB);
    assert_error(
        &spec,
        "program[0].files",
        "matches no file in the manifest's directory",
    );
    write(
        "[corpus]\nroot = \"../corpus\"\n",
        "[[program]]\nfiles = \"gone/*.calc\"\n",
    );
    assert_error(
        &spec,
        "program[0].files",
        &format!("matches no file in {ROOT_NAME}"),
    );
    // A listed program's file is a path under the root, which it may not leave.
    write(
        "[corpus]\nroot = \"../corpus\"\n",
        "[[program]]\nid = \"calc\"\nfile = \"../spec/calc.k\"\n",
    );
    assert_error(
        &spec,
        "program \"calc\".file",
        &format!("leaves {ROOT_NAME}"),
    );
    // A pattern list is beside the flow, not under the root.
    fs::write(dir.join("corpus/PATTERNS.toml"), "").unwrap();
    write(
        "[corpus]\nroot = \"../corpus\"\n",
        &format!("{GLOB}\n[[patterns]]\nfiles = \"PATTERNS.toml\"\n"),
    );
    assert_error(
        &spec,
        "patterns[0].files",
        "matches no file in the manifest's directory",
    );
    fs::write(
        spec.join("PATTERNS.toml"),
        "[[pattern]]\nid = \"three\"\npattern = \"<k> 3 </k>\"\n",
    )
    .unwrap();
    assert_eq!(ids(&read(&spec).unwrap()), IDS);
}

/// The containment rule has the root as its boundary: a case document, a file it includes and a
/// program file that a link leads out of the root are refused, naming the root as the manifest
/// writes it. The flow's own directory is outside the root too.
#[cfg(unix)]
#[test]
fn a_link_out_of_the_root_is_refused_naming_the_root() {
    use std::os::unix::fs::symlink;
    let cases = "[[program]]\ncases = \"cases/*.toml\"\n";
    let dir = workspace("escape", cases);
    let (spec, corpus) = (dir.join("spec"), dir.join("corpus"));
    fs::create_dir_all(corpus.join("cases")).unwrap();

    // A case document reached through a link that leaves the root.
    let outside = dir.join("outside.toml");
    fs::write(&outside, "[inputs]\nn = 1\n").unwrap();
    symlink(&outside, corpus.join("cases/out.toml")).unwrap();
    assert_error(
        &spec,
        "program \"cases/out.toml\"",
        &format!("the case document escapes {ROOT_NAME}"),
    );
    fs::remove_file(corpus.join("cases/out.toml")).unwrap();

    // A file a case document includes, by a path that climbs out of the root.
    fs::write(dir.join("list.toml"), "[[case]]\nname = \"one\"\n").unwrap();
    fs::write(
        corpus.join("cases/in.toml"),
        "case = { \"$data-file\" = \"../../list.toml\" }\n",
    )
    .unwrap();
    assert_error(
        &spec,
        "program \"cases/in.toml\".case",
        &format!("cases/../../list.toml escapes {ROOT_NAME}"),
    );

    // A program file: the link is followed when the program is read, at admission. One link
    // leads above the root, one into the flow's own directory.
    symlink(dir.join("outside.calc"), corpus.join("programs/out.calc")).unwrap();
    fs::write(dir.join("outside.calc"), "1 + 1").unwrap();
    symlink(spec.join("own.calc"), corpus.join("programs/own.calc")).unwrap();
    fs::write(spec.join("own.calc"), "1 + 1").unwrap();
    fs::write(spec.join("FLOW.toml"), format!("{FLOW}{GLOB}")).unwrap();
    let (coverage, _) = command(&spec, "coverage", None, &[]);
    let rows = coverage["programs"].as_array().unwrap();
    let refused = rows
        .iter()
        .filter(|row| row["class"] == "refused")
        .map(|row| (row["id"].as_str().unwrap(), row["cause"].as_str().unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(
        refused,
        [
            (
                "programs/out.calc",
                "load/load-error: programs/out.calc escapes the corpus root `../corpus`"
            ),
            (
                "programs/own.calc",
                "load/load-error: programs/own.calc escapes the corpus root `../corpus`"
            ),
        ],
        "{coverage:#}"
    );
}

/// `query` reads the cases under the root: a pattern's witness is a case named by its path
/// relative to the root, and a claim names a case by that id.
#[test]
fn query_names_a_case_by_its_path_under_the_root() {
    let dir = workspace("query", GLOB);
    let spec = dir.join("spec");
    let patterns = spec.join("PATTERNS.toml");
    fs::write(
        &patterns,
        "[[pattern]]\nid = \"three\"\npattern = \"<k> 3 </k>\"\nprograms = \
         [\"programs/a1.calc\"]\n\n[[pattern]]\nid = \"six\"\npattern = \"<k> 6 </k>\"\n",
    )
    .unwrap();
    let (document, status) = command(&spec, "query", Some(&patterns), &[]);
    assert_eq!(status, EXIT_YES, "{document:#}");
    let hits = document["rows"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row["answer"] == "hit")
        .map(|row| {
            (
                row["pattern"].as_str().unwrap(),
                row["program"].as_str().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        hits,
        [("three", "programs/a1.calc"), ("six", "programs/m1.calc")],
        "{document:#}"
    );
}

/// A `fuzz` template that names a `[[program]]` takes the program's text from its file under
/// the root: the campaign starts from that text, and a program whose file a link leads out of
/// the root is refused as a template, naming the root. A template's own `file` stays relative to
/// the templates' directory. (calc's runs end with a value left in `<k>`, which fuzz does not
/// count as a natural end, so the campaign confirms no witness here; what the test pins is which
/// text it instantiates.)
#[cfg(unix)]
#[test]
fn a_fuzz_template_reads_its_program_under_the_root() {
    let dir = workspace("fuzz", GLOB);
    let (spec, corpus) = (dir.join("spec"), dir.join("corpus"));
    fs::write(dir.join("outside.calc"), "1 + 1").unwrap();
    std::os::unix::fs::symlink(dir.join("outside.calc"), corpus.join("programs/out.calc")).unwrap();
    let job = |program: &str| {
        let manifest = read(&spec).unwrap();
        let templates = format!(
            "[[template]]\nid = \"t\"\nprogram = \"programs/{program}.calc\"\n[[template.hole]]\n\
             name = \"X\"\nsort = \"Int\"\nfind = \"1\"\nliteral = \"1\"\nrange = {{ min = 0, max \
             = 9 }}\n"
        );
        let templates = TemplateList::decode(&templates, &spec).unwrap();
        std::thread::Builder::new()
            .stack_size(DEFINITION_STACK_BYTES)
            .spawn(move || {
                fuzz_job(
                    &manifest,
                    &templates,
                    "t",
                    FuzzJob::Rule {
                        rule: "add",
                        fired: true,
                    },
                    &FuzzOptions {
                        budget: k_rust_fuzz::Budget::Cases(4),
                        max_work: Some(20_000),
                        ..FuzzOptions::default()
                    },
                )
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let (document, _) = job("out");
    let refusal = &document["job"]["refusal"];
    assert_eq!(refusal["stage"], "template", "{document:#}");
    assert_eq!(
        refusal["detail"],
        "program \"programs/out.calc\": programs/out.calc escapes the corpus root `../corpus`",
        "{document:#}"
    );

    // `a1` is `1 + 2`, read under the root: the template is admitted with its hole on the `1`
    // of that text, and the campaign runs its instances.
    let (document, _) = job("a1");
    assert_eq!(document["job"]["refusal"], Value::Null, "{document:#}");
    assert_eq!(document["job"]["outcome"], "fuzzed", "{document:#}");
    assert_eq!(
        document["attempts"][0]["fuzz"]["identity"]["budget"]["cases"], "4",
        "{document:#}"
    );
}
