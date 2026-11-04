//! `krs run` and `krs search` bind a definition's inputs by parameter name: from a case document
//! (`--case`), from `--input NAME=JSON` documents of the typed encoding, and from `-c` text, with
//! FILE bound to the main parameter whatever its K name.
//!
//! `fixtures/inputs` has no main parameter, and copies each of its four parameters
//! (`Map<Int, Int>`, `Bytes`, `Int` and a declared sort) into its own cell, so a run of depth 0
//! shows the values its inputs were given. `fixtures/inferred-main` has one parameter, `entry`,
//! whose configuration variable is `$ENTRY`, made main by being read in the computation cell.
//! `fixtures/bytes-main`'s main parameter is a `Bytes`, `rom` (`$ROM`), beside an `Int`.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::sync::{Arc, Mutex, Weak};

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::Value;

const INPUTS: &str = include_str!("fixtures/inputs/src/lib.rs");
const INFERRED_MAIN: &str = include_str!("fixtures/inferred-main/src/lib.rs");
const BYTES_MAIN: &str = include_str!("fixtures/bytes-main/src/lib.rs");

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
    assert_eq!(twice.status.code(), Some(1), "{}", stderr(&twice));
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
    assert_eq!(run.status.code(), Some(1), "{}", stderr(&run));
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
    assert_eq!(twice.status.code(), Some(1), "{}", stderr(&twice));
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
    let cases: [(&[&str], &str); 13] = [
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
        (
            &["--case", "odd.toml"],
            "case `odd.toml`: unknown key `other` in a case; a case has the key `inputs`",
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
            Some(1),
            "{arguments:?}: {}",
            stderr(&run)
        );
        assert_eq!(
            stderr(&run).lines().next(),
            Some(format!("error[krs::exec::variable]: {expected}").as_str()),
            "{arguments:?}"
        );
    }
}
