//! `krs run` and `krs search` bind a definition's inputs by parameter name: from a case document
//! (`--case`), from `--input NAME=JSON` documents of the typed encoding, and from `-c` text, with
//! FILE bound to the main parameter whatever its K name.
//!
//! `fixtures/inputs` has no main parameter, and copies each of its four parameters
//! (`Map<Int, Int>`, `Bytes`, `Int` and a declared sort) into its own cell, so a run of depth 0
//! shows the values its inputs were given. `fixtures/inferred-main` has one parameter, `entry`,
//! whose configuration variable is `$ENTRY`, made main by being read in the computation cell.
//! `fixtures/bytes-main`'s main parameter is a `Bytes`, `rom` (`$ROM`), beside an `Int`.
//!
//! A case may also state how it is run and the end it expects; `krs run --case` and
//! `krs search --case` check the end against it (exit 0 met, 1 unmet, 3 inconclusive), and a
//! document of named cases is run one case at a time with `--case-name`. These run on
//! `fixtures/ends`, which copies each input into its own cell, has an unobservable cell at the
//! top and one in a group, steps `finish(v)` to `done(v)` by the rule `finish`, and `toss(v)` to
//! `done(0)` or `done(1)`. An inline definition, `STATUS`, has an exit cell and a run that
//! cannot decide which of two states it reaches.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::sync::{Arc, Mutex, Weak};

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const INPUTS: &str = include_str!("fixtures/inputs/src/lib.rs");
const INFERRED_MAIN: &str = include_str!("fixtures/inferred-main/src/lib.rs");
const BYTES_MAIN: &str = include_str!("fixtures/bytes-main/src/lib.rs");
const ENDS: &str = include_str!("fixtures/ends/src/lib.rs");

/// A definition whose exit cell, `status`, `quit c` sets to `c`; `open a` steps only where
/// `unsure(a)` holds, which no equation decides at `2`, so a run of `open 2` splits on it and has
/// no one end.
const STATUS: &str = r#"
use k::builtin::{Bool, Int, KSequence};
use k::KResult;
use k::Term;

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("quit {code}")]
    Quit { code: Int },
    #[k::syntax("open {a}")]
    Open { a: Int },
}

#[k::function(total, internal)]
pub fn Opaque(a: Term<Int>) -> Term<Int>;

#[k::function(partial, internal)]
pub fn Unsure(a: Term<Int>) -> Term<Bool>;

#[k::equation]
#[k::requires(Opaque(a) == 1)]
fn unsure_one(Unsure(a): Term<Bool>) -> Term<Bool> {
    true
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    quit: { k: [Quit(code), ..], status: _ } => { k: [..], status: code };
    #[k::requires(Unsure(a))]
    open: { k: [Open(a), ..], status: _ } => { k: [..], status: 1 };
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(exit)]
    pub status: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], status: 0 }
    }
}
"#;

/// A fixture materialized as a package, shared by the tests that overlap in this process: its
/// manifest path keys the collector's directory and result cache, so the tests that share it
/// build it once, and they run `krs` on it one at a time.
struct Project {
    package: &'static str,
    directory: TempDir,
    _target: SharedFixtureTarget,
    target: PathBuf,
    turn: Mutex<()>,
}

impl Project {
    fn shared(slot: &'static Mutex<Weak<Self>>, package: &'static str, source: &str) -> Arc<Self> {
        let mut slot = slot
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(project) = slot.upgrade() {
            return project;
        }
        let target = shared_fixture_target();
        let directory = temp_dir();
        fs::create_dir_all(directory.path().join("src")).unwrap();
        fs::write(directory.path().join("src/lib.rs"), source).unwrap();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        fs::write(
            directory.path().join("Cargo.toml"),
            format!(
                "[package]\nname = \"{package}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CLI-INPUTS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
            ),
        )
        .unwrap();
        let project = Arc::new(Self {
            package,
            directory,
            target: target.path().to_path_buf(),
            _target: target,
            turn: Mutex::new(()),
        });
        *slot = Arc::downgrade(&project);
        project
    }

    fn path(&self) -> &Path {
        self.directory.path()
    }

    /// Write `contents` at `relative` inside the package directory.
    fn write(&self, relative: &str, contents: impl AsRef<[u8]>) {
        let path = self.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    /// `krs VERB --package .. --definition main ARGUMENTS`, from the package directory.
    fn krs(&self, verb: &str, arguments: &[&str]) -> Output {
        let _turn = self
            .turn
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        self.command(verb, arguments).output().unwrap()
    }

    /// The process [`Self::krs`] runs, for a caller that holds the turn and sets more of it.
    fn command(&self, verb: &str, arguments: &[&str]) -> std::process::Command {
        let mut process = krs_command!();
        fixture_build_env(&mut process, &self.target);
        process
            .current_dir(self.path())
            .arg(verb)
            .args(["--package", self.package, "--definition", "main"])
            .args(arguments);
        process
    }
}

fn inputs() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, "krs-cli-inputs-fixture", INPUTS)
}

fn inferred_main() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, "krs-cli-inferred-main-fixture", INFERRED_MAIN)
}

fn bytes_main() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, "krs-cli-bytes-main-fixture", BYTES_MAIN)
}

fn ends() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, "krs-cli-case-ends-fixture", ENDS)
}

fn status() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, "krs-cli-case-status-fixture", STATUS)
}

/// The inputs of a case on `fixtures/ends` whose program is `pgm`: each other input is copied into
/// its own cell, `w` and `z` into the unobservable ones.
fn ends_inputs(pgm: &Value) -> Value {
    json!({
        "pgm": pgm,
        "regs": {"A": 1},
        "f": {"Flags": {"zf": true, "cf": false}},
        "pc": 256,
        "bus": [{"Read": {"addr": 5}}],
        "memory": {"5": 6},
        "ime": true,
        "w": 9,
        "z": 4,
    })
}

/// Every observable cell of `fixtures/ends`'s end from [`ends_inputs`], with `k` holding `k`.
fn ends_cells(k: &Value) -> Value {
    json!({
        "k": k,
        "regs": {"A": 1},
        "f": {"Flags": {"zf": true, "cf": false}},
        "pc": 256,
        "bus": [{"Read": {"addr": 5}}],
        "memory": {"5": 6},
        "cpu": {"ime": true},
        "timer": [],
        "threads": {"thread": [{"id": 0, "count": 0}]},
        "objects": {"obj": [{"oid": 0}]},
        "procs": {"process": [{"pid": 0, "ticks": 0}]},
        "mark": [],
    })
}

/// A named case of a document on `fixtures/ends`.
fn ends_case(name: &str, pgm: &Value, expect: &Value) -> Value {
    json!({"name": name, "inputs": ends_inputs(pgm), "expect": expect})
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn json(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            stdout(output),
            stderr(output)
        )
    })
}

/// The bytes 0 to 255 as K prints a `Bytes` literal.
fn every_byte_literal() -> String {
    let mut literal = String::from("b\"");
    for byte in 0..=255_u8 {
        match byte {
            b'\t' => literal.push_str("\\t"),
            b'\n' => literal.push_str("\\n"),
            0x0c => literal.push_str("\\f"),
            b'\r' => literal.push_str("\\r"),
            b'"' => literal.push_str("\\\""),
            b'\\' => literal.push_str("\\\\"),
            0x20..=0x7e => literal.push(char::from(byte)),
            _ => {
                let _ = write!(literal, "\\x{byte:02x}");
            }
        }
    }
    literal.push('"');
    literal
}

/// The inputs a refusal or a call leaves as they are: an empty memory, two bytes, and `Halt`.
const OTHER_INPUTS: [&str; 6] = [
    "--input",
    "memory={}",
    "--input",
    r#"rom={"$hex": "00ff"}"#,
    "--input",
    r#"entry="Halt""#,
];

/// A case whose values come from a data file and a binary file, with no K text, runs from the
/// state they denote; the same values written in one JSON case give the same state, and
/// `krs search` takes the case as `krs run` does.
#[test]
fn a_case_from_a_data_file_and_a_binary_file() {
    let project = inputs();
    // Paths are relative to the document that names them: the case's directory here.
    project.write(
        "cases/boot.toml",
        r#"[inputs]
memory = { "$data-file" = "data/memory.toml" }
rom = { "$file" = "data/boot.bin" }
pc = 256
entry = { Load = { addr = 2, len = 3 } }
"#,
    );
    project.write(
        "cases/data/memory.toml",
        "\"0x0100\" = 0\n\"0x0101\" = 195\n\"2\" = 7\n",
    );
    // Every byte, so the file is no UTF-8 text and no byte is decoded or re-encoded.
    project.write("cases/data/boot.bin", (0..=255_u8).collect::<Vec<_>>());
    let every_byte = (0..=255_u8).fold(String::new(), |mut hex, byte| {
        let _ = write!(hex, "{byte:02x}");
        hex
    });
    project.write(
        "cases/boot.json",
        format!(
            r#"{{"inputs": {{"memory": [[2, 7], [256, 0], [257, 195]], "rom": {{"$hex": "{every_byte}"}}, "pc": "0x100", "entry": {{"Load": [2, 3]}}}}}}"#
        ),
    );

    let run = project.krs("run", &["--case", "cases/boot.toml", "--depth", "0"]);
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert_eq!(
        stdout(&run),
        format!(
            "<generatedTop>\n  <k>\n    .K\n  </k>\n  <memory>\n    2 |-> 7\n    256 |-> 0\n    257 |-> 195\n  </memory>\n  <rom>\n    {}\n  </rom>\n  <pc>\n    256\n  </pc>\n  <entry>\n    load(2, 3)\n  </entry>\n</generatedTop>\n",
            every_byte_literal()
        )
    );
    assert!(
        stderr(&run).ends_with("krs run: depth-bound after 0 steps; <k> is empty\n"),
        "{}",
        stderr(&run)
    );

    let toml = project.krs(
        "run",
        &[
            "--case",
            "cases/boot.toml",
            "--depth",
            "0",
            "--output",
            "kore",
        ],
    );
    let json = project.krs(
        "run",
        &[
            "--case",
            "cases/boot.json",
            "--depth",
            "0",
            "--output",
            "kore",
        ],
    );
    assert_eq!(toml.status.code(), Some(0), "{}", stderr(&toml));
    assert_eq!(json.status.code(), Some(0), "{}", stderr(&json));
    assert_eq!(stdout(&toml), stdout(&json));

    let search = project.krs("search", &["--case", "cases/boot.json"]);
    assert_eq!(search.status.code(), Some(0), "{}", stderr(&search));
    assert_eq!(stdout(&search), stdout(&run));
}

/// FILE binds the main parameter; a definition with none refuses it before reading it, naming
/// the missing main parameter and listing the parameters by name and declared type.
#[test]
fn no_main_parameter_refuses_file() {
    let project = inputs();
    let run = project.krs("run", &["absent.txt", "--input", "pc=1"]);
    assert_eq!(run.status.code(), Some(2), "{}", stderr(&run));
    assert_eq!(
        stderr(&run).lines().next(),
        Some(
            "error[krs::exec::program]: the #[k::init] has no main parameter (none is marked #[k::config_var(main)] or read in the computation cell), so FILE binds nothing; bind its parameters by name: memory: Map<Int, Int>, rom: Bytes, pc: Int, entry: Op"
        ),
        "{}",
        stderr(&run)
    );
}

/// On a definition whose main parameter is `$ENTRY`, FILE binds it as `-c` text of `entry`;
/// binding it by name instead needs no FILE, and doing both binds it twice.
#[test]
fn file_binds_the_main_parameter() {
    let project = inferred_main();
    project.write("prog.txt", "go\n");

    let file = project.krs("run", &["prog.txt"]);
    assert_eq!(file.status.code(), Some(0), "{}", stderr(&file));
    assert_eq!(stdout(&file), "<k>\n  go ~> .K\n</k>\n");

    let by_name = project.krs("run", &["--input", r#"ENTRY="Halt""#]);
    assert_eq!(by_name.status.code(), Some(0), "{}", stderr(&by_name));
    assert_eq!(stdout(&by_name), "<k>\n  halt ~> .K\n</k>\n");

    let twice = project.krs("run", &["prog.txt", "--input", r#"entry="Halt""#]);
    assert_eq!(twice.status.code(), Some(2), "{}", stderr(&twice));
    assert_eq!(
        stderr(&twice).lines().next(),
        Some(
            "error[krs::exec::variable]: configuration variable `$ENTRY` (init parameter entry) is bound twice"
        )
    );

    let unbound = project.krs("run", &[]);
    assert_eq!(unbound.status.code(), Some(2), "{}", stderr(&unbound));
    assert_eq!(
        stderr(&unbound).lines().next(),
        Some(
            "error[krs::exec::program]: the main parameter `entry` ($ENTRY: Op) is unbound; pass FILE, `-` for standard input, or bind `entry` by name"
        )
    );
}

/// A file that is not UTF-8 text is refused for a main parameter that reads text, naming the
/// parameter and its type: only a parse at the parameter's sort says what the file denotes, and
/// text that is not UTF-8 has none.
#[test]
fn a_text_main_parameter_refuses_a_file_that_is_not_text() {
    let project = inferred_main();
    project.write("prog.bin", [0x67, 0x6f, 0xff, 0x0a]);
    let run = project.krs("run", &["prog.bin"]);
    assert_eq!(run.status.code(), Some(2), "{}", stderr(&run));
    assert_eq!(
        stderr(&run).lines().next(),
        Some(
            "error[krs::exec::program]: `prog.bin` is not UTF-8 text, and the main parameter `entry` ($ENTRY: Op) reads a file as text, parsed at its sort; only a main parameter of type exactly `Bytes` takes a file's bytes"
        ),
        "{}",
        stderr(&run)
    );
}

/// On a definition whose main parameter is a `Bytes`, FILE is its value: the file's bytes,
/// unchanged, here every byte, so the file is no UTF-8 text. The state is the one the same file
/// bound by name as `{"$file": ..}` gives, standard input gives the same bytes, and FILE together
/// with a binding of `rom` by name binds it twice.
#[test]
fn a_bytes_main_parameter_takes_the_files_bytes() {
    let project = bytes_main();
    project.write("rom.bin", (0..=255_u8).collect::<Vec<_>>());
    let file = project.krs("run", &["rom.bin", "--input", "pc=256", "--depth", "0"]);
    assert_eq!(file.status.code(), Some(0), "{}", stderr(&file));
    assert_eq!(
        stdout(&file),
        format!(
            "<generatedTop>\n  <k>\n    .K\n  </k>\n  <rom>\n    {}\n  </rom>\n  <pc>\n    256\n  </pc>\n</generatedTop>\n",
            every_byte_literal()
        )
    );

    let by_name = project.krs(
        "run",
        &[
            "--input",
            r#"rom={"$file": "rom.bin"}"#,
            "--input",
            "pc=256",
            "--depth",
            "0",
        ],
    );
    assert_eq!(by_name.status.code(), Some(0), "{}", stderr(&by_name));
    assert_eq!(stdout(&by_name), stdout(&file));

    let stdin = {
        let _turn = project
            .turn
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut process = project.command("run", &["-", "--input", "pc=256", "--depth", "0"]);
        process.stdin(fs::File::open(project.path().join("rom.bin")).unwrap());
        process.output().unwrap()
    };
    assert_eq!(stdin.status.code(), Some(0), "{}", stderr(&stdin));
    assert_eq!(stdout(&stdin), stdout(&file));

    let twice = project.krs(
        "run",
        &[
            "rom.bin",
            "--input",
            r#"rom={"$hex": "00"}"#,
            "--input",
            "pc=256",
        ],
    );
    assert_eq!(twice.status.code(), Some(2), "{}", stderr(&twice));
    assert_eq!(
        stderr(&twice).lines().next(),
        Some(
            "error[krs::exec::variable]: configuration variable `$ROM` (init parameter rom) is bound twice"
        )
    );
}

/// An input that applies a function is the definition's computation: the first state is
/// simplified before the first step, so a run of depth 0 shows the application's value, at a
/// whole input and inside a map.
#[test]
fn a_call_is_evaluated_before_the_first_step() {
    let project = inputs();
    let run = project.krs(
        "run",
        &[
            "--input",
            r#"memory={"0": {"$call": {"Boot": [1]}}}"#,
            "--input",
            "rom=[]",
            "--input",
            r#"entry="Halt""#,
            "--input",
            r#"pc={"$call": {"Boot": {"n": 0}}}"#,
            "--depth",
            "0",
        ],
    );
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    let printed = stdout(&run);
    assert!(
        printed.contains("<memory>\n    0 |-> 257\n  </memory>"),
        "{printed}"
    );
    assert!(printed.contains("<pc>\n    256\n  </pc>"), "{printed}");
    assert!(
        stderr(&run).ends_with("krs run: depth-bound after 0 steps; <k> is empty\n"),
        "{}",
        stderr(&run)
    );
}

/// An application that has no value leaves no initial state: the run ends undefined after 0
/// steps and names the application.
#[test]
fn a_call_without_value_is_reported() {
    let project = inputs();
    let mut arguments = OTHER_INPUTS.to_vec();
    arguments.extend(["--input", r#"pc={"$call": {"OnlyZero": [1]}}"#]);
    let run = project.krs("run", &arguments);
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert!(
        stderr(&run).ends_with(
            "krs run: undefined after 0 steps; <k> is empty\nnote: `onlyZero ( 1 )` has no value: its function is partial and defined by its equations alone, and none applies there, so no state holds it\n"
        ),
        "{}",
        stderr(&run)
    );

    arguments.extend(["--output", "json"]);
    let report = json(&project.krs("run", &arguments));
    assert_eq!(report["run"]["halt"], "undefined");
    assert_eq!(report["run"]["steps"], 0);
    let valueless = report["run"]["valueless"].as_array().unwrap();
    assert_eq!(valueless.len(), 1);
    assert_eq!(valueless[0]["term"]["label"]["name"], "onlyZero");
}

/// Each refusal names the input, its declared type, the position in the document and the reason.
#[test]
fn refusals_name_parameter_type_and_position() {
    let project = inputs();
    project.write("pc.toml", "[inputs]\npc = 1\n");
    project.write("odd.toml", "[inputs]\npc = 1\n[other]\n");
    let cases: [(&[&str], &str); 12] = [
        (
            &["--input", "pc=1", "--input", r#"entry="Nope""#],
            r#"input `entry` (Op): the string "Nope" is no value of Op; it takes a constructor form; its constructors are Halt, Load"#,
        ),
        (
            &["--input", r#"memory={"1": 2, "01": 3}"#],
            r#"input `memory` (Map<Int, Int>) at `["1"]`: this key decodes to the same value as the key at `["01"]`; K's map of two bindings of one key has no value"#,
        ),
        (
            &["--input", r#"pc={"$file": "odd.toml"}"#],
            "input `pc` (Int): `$file` gives a value of sort Bytes, which is not at most Int",
        ),
        (
            &["--input", r#"pc={"Boot": {"n": 0}}"#],
            r#"input `pc` (Int): `krs_cli_inputs_fixture::Boot` is a function; write {"$call": {"Boot": ..}} to apply it"#,
        ),
        (
            &[
                "--input",
                "pc=1",
                "--input",
                r#"entry={"$call": {"Halt": []}}"#,
            ],
            r#"input `entry` (Op): `krs_cli_inputs_fixture::Instr::Halt` is a constructor; write it without $call: {"Halt": ..}"#,
        ),
        (
            &["--input", r#"rom="abc""#],
            r#"input `rom` (Bytes): the string "abc" is no value of Bytes; it takes an array of integers in 0..=255, {"$hex": ..} or {"$file": ..}; a string has no determined byte encoding"#,
        ),
        (
            &["--input", r#"rom={"$file": "absent.bin"}"#],
            "input `rom` (Bytes): `$file` `absent.bin`: could not read `absent.bin`: No such file or directory (os error 2)",
        ),
        (
            &["--input", "pc={"],
            "input `pc` (Int): the document is no JSON: EOF while parsing an object at line 1 column 1",
        ),
        (
            &["--input", "pc=1", "--input", "nope=1"],
            "unknown configuration variable `nope`; the definition declares",
        ),
        (
            &[],
            "missing configuration variables; pass -c pc=VALUE; missing",
        ),
        (
            &["--input", "pc=1", "-c", "PC=2"],
            "configuration variable `$PC` (init parameter pc) is bound twice",
        ),
        (
            &["--case", "pc.toml", "--input", "$PC=2"],
            "configuration variable `$PC` (init parameter pc) is bound twice",
        ),
    ];
    for (extra, expected) in cases {
        // The other inputs come after, so the refusal concerns the document under test.
        let mut arguments = extra.to_vec();
        for (option, value) in OTHER_INPUTS.chunks(2).map(|pair| (pair[0], pair[1])) {
            let name = value.split_once('=').unwrap().0;
            if !extra
                .iter()
                .any(|argument| argument.starts_with(&format!("{name}=")))
            {
                arguments.extend([option, value]);
            }
        }
        let run = project.krs("run", &arguments);
        assert_eq!(
            run.status.code(),
            Some(2),
            "{arguments:?}: {}",
            stderr(&run)
        );
        assert_eq!(
            stderr(&run).lines().next(),
            Some(format!("error[krs::exec::variable]: {expected}").as_str()),
            "{arguments:?}"
        );
    }
    // A case document that is none is the case's refusal, not an input's.
    let odd = project.krs("run", &["--case", "odd.toml"]);
    assert_eq!(odd.status.code(), Some(2), "{}", stderr(&odd));
    assert_eq!(
        stderr(&odd).lines().next(),
        Some(
            "error[krs::exec::case]: case `odd.toml`: unknown key `other` in a case; a case has the keys `inputs`, `run` and `expect`"
        )
    );
}

/// A case whose run meets its expectation exits 0, after the run's own output; one whose run does
/// not exits 1 and names the first differing cell with both canonical documents, and the cells
/// that also differ. The expectation omits the unobservable cells, `z` and `cpu.w`, and states
/// every other; `--output json` carries the verdict and the `krs-difference/3` difference.
#[test]
fn a_run_meets_or_misses_its_expectation() {
    let project = ends();
    let finish = json!({"Finish": {"value": 3}});
    let done = json!({"$seq": [{"Done": {"value": 3}}]});
    let met = json!({"inputs": ends_inputs(&finish), "expect": {"halt": "stuck", "cells": ends_cells(&done)}});
    project.write("met.json", met.to_string());
    let run = project.krs("run", &["--case", "met.json"]);
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert!(
        stdout(&run).contains("<k>\n    done(3) ~> .K\n  </k>"),
        "{}",
        stdout(&run)
    );
    assert!(
        stderr(&run).ends_with(
            "krs run: stuck after 1 step; <k> starts with `done(3)`\nkrs run: expectation met\n"
        ),
        "{}",
        stderr(&run)
    );
    let report = json(&project.krs("run", &["--case", "met.json", "--output", "json"]));
    assert_eq!(report["expectation"], json!({"verdict": "met"}));

    let mut cells = ends_cells(&done);
    cells["pc"] = json!(257);
    cells["regs"] = json!({"A": 1, "B": 2});
    let unmet =
        json!({"inputs": ends_inputs(&finish), "expect": {"halt": "stuck", "cells": cells}});
    project.write("unmet.json", unmet.to_string());
    let run = project.krs("run", &["--case", "unmet.json"]);
    assert_eq!(run.status.code(), Some(1), "{}", stderr(&run));
    assert!(
        stderr(&run).ends_with(
            "krs run: expectation unmet at `regs[\"B\"]`\n  expected: 2\n  actual:   nothing (the position is absent on this side)\n  also differ: `pc`\n"
        ),
        "{}",
        stderr(&run)
    );
    let report = json(&project.krs("run", &["--case", "unmet.json", "--output", "json"]));
    assert_eq!(report["schema"], "krs-exec/3");
    let expectation = &report["expectation"];
    assert_eq!(expectation["verdict"], "unmet", "{expectation}");
    let difference = &expectation["difference"];
    assert_eq!(difference["format"], "krs-difference/3");
    assert_eq!(difference["path"], "regs[\"B\"]");
    assert_eq!(difference["also_differ"], json!(["pc"]));
    assert_eq!(difference["left"]["name"], "expected");
    assert_eq!(difference["left"]["value"]["document"], 2);
    assert_eq!(difference["right"]["name"], "actual");
    assert_eq!(difference["right"]["value"], Value::Null);
    assert_eq!(
        difference["not_compared"],
        json!(["cpu.w", "z"]),
        "{difference}"
    );

    // The first differing cell in declaration order, both sides shown as documents.
    let mut cells = ends_cells(&done);
    cells["pc"] = json!(257);
    let unmet =
        json!({"inputs": ends_inputs(&finish), "expect": {"halt": "stuck", "cells": cells}});
    project.write("pc.json", unmet.to_string());
    let run = project.krs("run", &["--case", "pc.json"]);
    assert_eq!(run.status.code(), Some(1), "{}", stderr(&run));
    assert!(
        stderr(&run)
            .ends_with("krs run: expectation unmet at `pc`\n  expected: 257\n  actual:   256\n"),
        "{}",
        stderr(&run)
    );
}

/// An expectation must state each cell it is compared on, and may narrow them with `compare`:
/// one that omits a compared cell is refused before the run, naming the cell and its type; a
/// narrowing to `pc` needs only `pc`; an unobservable cell may be stated, with any value, and is
/// never compared, but naming one in `compare` is refused.
#[test]
fn an_expectation_states_the_cells_it_is_compared_on() {
    let project = ends();
    let finish = json!({"Finish": {"value": 3}});
    let done = json!({"$seq": [{"Done": {"value": 3}}]});
    let mut cells = ends_cells(&done);
    cells.as_object_mut().unwrap().remove("bus");
    project.write(
        "partial.json",
        json!({"inputs": ends_inputs(&finish), "expect": {"halt": "stuck", "cells": cells}})
            .to_string(),
    );
    let run = project.krs("run", &["--case", "partial.json"]);
    assert_eq!(run.status.code(), Some(2), "{}", stderr(&run));
    assert_eq!(
        stderr(&run).lines().next(),
        Some(
            "error[krs::exec::case]: case `partial.json`: `expect.cells`: the expected end does not state the compared cell `bus` (List<Event>)"
        ),
        "{}",
        stderr(&run)
    );
    assert!(!stdout(&run).contains("<k>"), "{}", stdout(&run));

    project.write(
        "narrow.json",
        json!({"inputs": ends_inputs(&finish), "expect": {"halt": "stuck", "compare": ["pc"], "cells": {"pc": 256, "z": 0}}}).to_string(),
    );
    let run = project.krs("run", &["--case", "narrow.json"]);
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert!(
        stderr(&run).ends_with("krs run: expectation met\n"),
        "{}",
        stderr(&run)
    );

    let mut cells = ends_cells(&done);
    cells["z"] = json!(0);
    cells["cpu"]["w"] = json!(0);
    project.write(
        "unobservable.json",
        json!({"inputs": ends_inputs(&finish), "expect": {"halt": "stuck", "cells": cells}})
            .to_string(),
    );
    let run = project.krs("run", &["--case", "unobservable.json"]);
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));

    project.write(
        "compare-z.json",
        json!({"inputs": ends_inputs(&finish), "expect": {"halt": "stuck", "compare": ["z"], "cells": {"z": 4}}}).to_string(),
    );
    let run = project.krs("run", &["--case", "compare-z.json"]);
    assert_eq!(run.status.code(), Some(2), "{}", stderr(&run));
    assert_eq!(
        stderr(&run).lines().next(),
        Some(
            "error[krs::exec::case]: case `compare-z.json`: `expect.compare`: the cell `z` is unobservable: no use of the definition may observe it, so it is never compared"
        ),
        "{}",
        stderr(&run)
    );
}

/// A document of named cases runs the case `--case-name` selects; without a name it lists them,
/// and a name it does not hold is a usage error, as is a name for the one case of a document. The
/// document's `run` stops each case before the rule `finish`, so the expected end is stopped
/// there; a case expecting another halt differs at the halt.
#[test]
fn named_cases_are_selected_by_name() {
    let project = ends();
    let finish = json!({"Finish": {"value": 3}});
    // A case names a rule as --stop-before does, by KRS item or K label, in `run` and in
    // `expect.rule` alike.
    let stopped = json!({"halt": "stopped", "rule": "crate::finish", "compare": ["k"], "cells": {"k": {"$seq": [{"Finish": {"value": 3}}]}}});
    let stuck = json!({"halt": "stuck", "compare": ["k"], "cells": {"k": {"$seq": [{"Finish": {"value": 3}}]}}});
    project.write(
        "cases/named.json",
        json!({
            "run": {"stop_before": ["crate::finish"]},
            "case": [ends_case("stopped", &finish, &stopped), ends_case("stuck", &finish, &stuck)],
        })
        .to_string(),
    );
    let run = project.krs(
        "run",
        &["--case", "cases/named.json", "--case-name", "stopped"],
    );
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert!(
        stderr(&run).ends_with("krs run: expectation met\n"),
        "{}",
        stderr(&run)
    );
    let report = json(&project.krs(
        "run",
        &[
            "--case",
            "cases/named.json",
            "--case-name",
            "stopped",
            "--output",
            "json",
        ],
    ));
    assert_eq!(
        report["expectation"],
        json!({"verdict": "met", "case": "stopped"})
    );

    let run = project.krs(
        "run",
        &["--case", "cases/named.json", "--case-name", "stuck"],
    );
    assert_eq!(run.status.code(), Some(1), "{}", stderr(&run));
    assert!(
        stderr(&run).ends_with(
            "krs run: expectation unmet at the end's halt\n  expected: stuck\n  actual:   stopped at `crate::finish`\n"
        ),
        "{}",
        stderr(&run)
    );

    let unnamed = project.krs("run", &["--case", "cases/named.json"]);
    assert_eq!(unnamed.status.code(), Some(2), "{}", stderr(&unnamed));
    assert!(
        stderr(&unnamed).contains(
            "the case document `cases/named.json` holds named cases; select one with --case-name NAME: `stopped`, `stuck`"
        ),
        "{}",
        stderr(&unnamed)
    );
    let unknown = project.krs(
        "run",
        &["--case", "cases/named.json", "--case-name", "nope"],
    );
    assert_eq!(unknown.status.code(), Some(2), "{}", stderr(&unknown));
    assert!(
        stderr(&unknown).contains(
            "--case-name `nope`: the case document `cases/named.json` holds no case of that name; its cases are `stopped`, `stuck`"
        ),
        "{}",
        stderr(&unknown)
    );
    project.write(
        "one.json",
        json!({"inputs": ends_inputs(&finish)}).to_string(),
    );
    let one = project.krs("run", &["--case", "one.json", "--case-name", "stopped"]);
    assert_eq!(one.status.code(), Some(2), "{}", stderr(&one));
    assert!(
        stderr(&one).contains(
            "--case-name `stopped`: the case document `one.json` holds one case, which has no name; omit --case-name"
        ),
        "{}",
        stderr(&one)
    );
    // The case's `run.depth` and `--depth` would both bound the run.
    project.write(
        "deep.json",
        json!({"inputs": ends_inputs(&finish), "run": {"depth": 0}}).to_string(),
    );
    let twice = project.krs("run", &["--case", "deep.json", "--depth", "1"]);
    assert_eq!(twice.status.code(), Some(2), "{}", stderr(&twice));
    assert!(
        stderr(&twice).contains(
            "--depth and the `run.depth` of the case `deep.json` both bound the run; give one"
        ),
        "{}",
        stderr(&twice)
    );
}

/// A case names a rule as the stop flags do, by KRS item or K label, in `run` and in
/// `expect.rule`, and its `run` stops are the run's only stops: the stop flags with them are a
/// usage error.
#[test]
fn a_case_names_its_rules_as_the_stop_flags_do() {
    let project = ends();
    let finish = json!({"Finish": {"value": 3}});
    let stopped = json!({"halt": "stopped", "rule": "crate::finish", "compare": ["k"], "cells": {"k": {"$seq": [{"Finish": {"value": 3}}]}}});
    project.write(
        "cases/stops.json",
        json!({"run": {"stop_before": ["crate::finish"]}, "case": [ends_case("stopped", &finish, &stopped)]})
            .to_string(),
    );
    let run = project.krs(
        "run",
        &["--case", "cases/stops.json", "--case-name", "stopped"],
    );
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    // The case's `run` stops and the stop flags would both say where the run ends.
    let twice = project.krs(
        "run",
        &[
            "--case",
            "cases/stops.json",
            "--case-name",
            "stopped",
            "--stop-after",
            "crate::finish",
        ],
    );
    assert_eq!(twice.status.code(), Some(2), "{}", stderr(&twice));
    assert!(
        stderr(&twice).contains(
            "--stop-before, --stop-after and --stop-count, and the `run` stops of the case `cases/stops.json`, both say where the run ends; give one"
        ),
        "{}",
        stderr(&twice)
    );
    // A bare path is no KRS item, which has `::`, so it is read as a K label, which `finish`
    // is not: the expectation is refused before the run.
    let mut bare = stopped;
    bare["rule"] = json!("finish");
    project.write(
        "bare-rule.json",
        json!({"inputs": ends_inputs(&finish), "run": {"stop_before": ["crate::finish"]}, "expect": bare}).to_string(),
    );
    let refused = project.krs("run", &["--case", "bare-rule.json"]);
    assert_eq!(refused.status.code(), Some(2), "{}", stderr(&refused));
    assert!(
        stderr(&refused).lines().next().is_some_and(|line| line
            .starts_with("error[krs::exec::case]: case `bare-rule.json`: `expect.rule`: ")),
        "{}",
        stderr(&refused)
    );
}

/// A run that stops at a rule it does not name has no end class to compare, so its expectation is
/// inconclusive, which exits 3, not 1.
#[test]
fn an_expectation_without_an_end_to_compare_is_inconclusive() {
    let project = ends();
    let finish = json!({"Finish": {"value": 3}});
    project.write(
        "unnamed-stop.json",
        json!({
            "inputs": ends_inputs(&finish),
            // Two names select two rules, so the stop does not say which one it was.
            "run": {"stop_after": ["org_krs_cli_inputs--finish", "org_krs_cli_inputs--toss_heads"]},
            "expect": {"halt": "stopped", "rule": "org_krs_cli_inputs--finish", "compare": ["pc"], "cells": {"pc": 256}},
        })
        .to_string(),
    );
    let run = project.krs("run", &["--case", "unnamed-stop.json"]);
    assert_eq!(run.status.code(), Some(3), "{}", stderr(&run));
    assert!(
        stderr(&run).ends_with(
            "krs run: expectation inconclusive: an end of the actual side stopped at a rule it does not name, so its class cannot be compared\n"
        ),
        "{}",
        stderr(&run)
    );
    let report = json(&project.krs("run", &["--case", "unnamed-stop.json", "--output", "json"]));
    assert_eq!(report["expectation"]["verdict"], "inconclusive");
}

/// `krs run` follows one path: an end of it that differs is unmet, but one that agrees meets the
/// expectation only where no state of the path has several successors. `toss(0)` steps to
/// `done(0)` or `done(1)` by the rules of the `nondet` group `toss`, so an expectation both ends
/// meet is inconclusive by a run, which points at `krs search --case`, and one neither meets is
/// unmet; `finish(3)` has one successor at each state, so its run meets an expectation.
#[test]
fn a_run_meets_an_expectation_only_on_the_only_path() {
    let project = ends();
    let toss = json!({"Toss": {"value": 0}});
    let both = json!({"halt": "stuck", "compare": ["pc"], "cells": {"pc": 256}});
    let neither = json!({"halt": "stuck", "compare": ["k"], "cells": {"k": {"$seq": [{"Done": {"value": 2}}]}}});
    project.write(
        "choice.json",
        json!({"case": [ends_case("both", &toss, &both), ends_case("neither", &toss, &neither)]})
            .to_string(),
    );
    let run = project.krs("run", &["--case", "choice.json", "--case-name", "both"]);
    assert_eq!(run.status.code(), Some(3), "{}", stderr(&run));
    let text = stderr(&run);
    let verdict = text
        .lines()
        .find(|line| line.starts_with("krs run: expectation"))
        .unwrap_or_default();
    assert!(
        verdict.starts_with(
            "krs run: expectation inconclusive: every end the actual side has meets the expectation, but it may have others: the run took one successor of the state after 0 steps, which has 2 successors, by `"
        ) && verdict.ends_with("`, so another path may end otherwise")
            && verdict.contains("`crate::toss_heads`")
            && verdict.contains("`crate::toss_tails`"),
        "{text}"
    );
    assert!(
        text.ends_with(
            "note: krs search --case checks every final state against the expectation\n"
        ),
        "{text}"
    );
    let report = json(&project.krs(
        "run",
        &[
            "--case",
            "choice.json",
            "--case-name",
            "both",
            "--output",
            "json",
        ],
    ));
    let expectation = &report["expectation"];
    assert_eq!(expectation["verdict"], "inconclusive", "{expectation}");
    assert_eq!(expectation["case"], "both", "{expectation}");
    assert!(
        expectation["reason"]
            .as_str()
            .is_some_and(|reason| reason.contains("which has 2 successors")),
        "{expectation}"
    );
    assert!(expectation.get("difference").is_none(), "{expectation}");

    let run = project.krs("run", &["--case", "choice.json", "--case-name", "neither"]);
    assert_eq!(run.status.code(), Some(1), "{}", stderr(&run));
    assert!(
        stderr(&run).contains("krs run: expectation unmet at `k[0].Done.value`\n  expected: 2\n"),
        "{}",
        stderr(&run)
    );
}

/// The verdict's status replaces the exit cell's: `quit 7` ends with 7 in the exit cell, which a
/// run without an expectation exits with, and a case that expects it exits 0, one that expects
/// another value 1. A run that splits on a condition it cannot decide has no one end, so its
/// expectation is inconclusive, exit 3, not unmet.
#[test]
fn the_verdict_s_status_replaces_the_exit_cell_s() {
    let project = status();
    let quit = json!({"pgm": {"Quit": {"code": 7}}});
    project.write("plain.json", json!({"inputs": quit}).to_string());
    let run = project.krs("run", &["--case", "plain.json"]);
    assert_eq!(run.status.code(), Some(7), "{}", stderr(&run));
    for (name, expected, code) in [("met", 7, 0), ("unmet", 8, 1)] {
        project.write(
            &format!("{name}.json"),
            json!({"inputs": quit, "expect": {"halt": "stuck", "compare": ["status"], "cells": {"status": expected}}})
                .to_string(),
        );
        let run = project.krs("run", &["--case", &format!("{name}.json")]);
        assert_eq!(run.status.code(), Some(code), "{name}: {}", stderr(&run));
        assert!(
            stderr(&run).contains(&format!("krs run: expectation {name}")),
            "{}",
            stderr(&run)
        );
    }

    let open = json!({"inputs": {"pgm": {"Open": {"a": 2}}}, "expect": {"halt": "stuck", "compare": ["status"], "cells": {"status": 1}}});
    project.write("open.json", open.to_string());
    let run = project.krs("run", &["--case", "open.json"]);
    assert_eq!(run.status.code(), Some(3), "{}", stderr(&run));
    assert!(
        stderr(&run).contains(
            "krs run: expectation inconclusive: the run has no one end: the run reaches 2 states, under conditions over `unsure ( 2 )`"
        ),
        "{}",
        stderr(&run)
    );
    assert!(stdout(&run).is_empty(), "{}", stdout(&run));
    let report = json(&project.krs("run", &["--case", "open.json", "--output", "json"]));
    assert_eq!(report["expectation"]["verdict"], "inconclusive", "{report}");
    assert!(report.get("run").is_none(), "{report}");
}

/// `krs search --case` checks every final state against the expectation: `toss(0)` ends as
/// `done(0)` or `done(1)`, so an expectation of `done(1)` is unmet by one of them, while one
/// that leaves `k` out is met by both. A search of reachable states has no ends to check.
#[test]
fn a_search_checks_every_end_against_the_expectation() {
    let project = ends();
    let toss = json!({"Toss": {"value": 0}});
    let heads =
        json!({"halt": "stuck", "cells": ends_cells(&json!({"$seq": [{"Done": {"value": 1}}]}))});
    let any = json!({"halt": "stuck", "compare": ["pc"], "cells": {"pc": 256}});
    project.write(
        "toss.json",
        json!({"case": [ends_case("heads", &toss, &heads), ends_case("any", &toss, &any)]})
            .to_string(),
    );
    let heads = project.krs("search", &["--case", "toss.json", "--case-name", "heads"]);
    assert_eq!(heads.status.code(), Some(1), "{}", stderr(&heads));
    assert!(
        stderr(&heads).ends_with(
            "krs search: 2 solutions\nkrs search: expectation unmet at `k[0].Done.value`\n  expected: 1\n  actual:   0\n  (one of the 2 actual ends; the expectation holds of every end or is unmet)\n"
        ),
        "{}",
        stderr(&heads)
    );
    let any = project.krs("search", &["--case", "toss.json", "--case-name", "any"]);
    assert_eq!(any.status.code(), Some(0), "{}", stderr(&any));
    assert!(
        stderr(&any).ends_with("krs search: expectation met\n"),
        "{}",
        stderr(&any)
    );
    let all = project.krs(
        "search",
        &["--case", "toss.json", "--case-name", "any", "--mode", "all"],
    );
    assert_eq!(all.status.code(), Some(2), "{}", stderr(&all));
    assert!(
        stderr(&all).contains("krs search --mode all returns reachable states, not ends"),
        "{}",
        stderr(&all)
    );
}

/// A named case in an included file reads its paths relative to that file, in its inputs and in
/// its expectation alike: here both name `mem.json` beside the included file, not beside the
/// document that includes it.
#[test]
fn an_included_case_reads_its_files_beside_it() {
    let project = ends();
    let mut inputs = ends_inputs(&json!({"Finish": {"value": 3}}));
    inputs["memory"] = json!({"$data-file": "mem.json"});
    let expect = json!({"halt": "stuck", "compare": ["memory"], "cells": {"memory": {"$data-file": "mem.json"}}});
    project.write(
        "cases/sub/list.json",
        json!([{"name": "included", "inputs": inputs, "expect": expect}]).to_string(),
    );
    project.write("cases/sub/mem.json", r#"{"7": 8}"#);
    project.write(
        "cases/top.toml",
        "[[case]]\n\"$data-file\" = \"sub/list.json\"\n",
    );
    let run = project.krs(
        "run",
        &["--case", "cases/top.toml", "--case-name", "included"],
    );
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert!(
        stdout(&run).contains("<memory>\n    7 |-> 8\n  </memory>"),
        "{}",
        stdout(&run)
    );
    assert!(
        stderr(&run).ends_with("krs run: expectation met\n"),
        "{}",
        stderr(&run)
    );
}
