//! `krs kink coverage`'s syntax family at the KRS level: each production of an authored sort is
//! named by the Rust path of its declaration, and each value of a `k::bits!` template's field is
//! an obligation listed with the encodings that reach it.
//!
//! The fixture is a small machine in the style of the boundary fixture of `tests/kink.rs`: a
//! program runs opcodes, a decode function turns each into an `Instr`, and a rule per variant
//! executes it. The decode reads a 6-bit template `01 rr ss` with two fields, `r` and `s`, and a
//! literal hole: `0x1f` is `halt`, so the template's equation requires `op != 0x1f`. The corpus
//! decodes `0x10`, `0x15` (`r` and `s` 0 and 1), `0x1f` and `0x03`; no case decodes to
//! `Instr::Jump`.

#![cfg(feature = "kink")]

use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::Output;
use std::sync::OnceLock;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::Value;

const LIBRARY: &str = r#"use k::builtin::{Bool, Int, KSequence};
use k::{KItem, KResult, Term};

k::sorts! {
    Cmd: KItem;
    Inst: KItem;
}

#[k::constructors(sort = Cmd, result = KResult)]
#[k::precedence((Run) > (Seq))]
pub enum CmdSyntax {
    #[k::syntax("{first} ; {rest}")]
    Seq { first: Cmd, rest: Cmd },
    #[k::syntax("run {op}")]
    Run { op: Int },
}

#[k::constructors(sort = Inst, result = KResult)]
pub enum Instr {
    #[k::syntax("ld {dst} {src}")]
    Ld { dst: Int, src: Int },
    #[k::syntax("halt")]
    Halt(),
    #[k::syntax("nop")]
    Nop(),
    #[k::syntax("jump")]
    Jump(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
    #[k::cell]
    pub halted: Bool,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Cmd) -> Self {
        Self {
            k: k::k![pgm],
            acc: 0,
            halted: false,
        }
    }
}

k::rules! {
    for Machine;
    use CmdSyntax::*;
    use Instr::*;

    seq: { k: [Seq(first, rest), ..] } => { k: [first, rest, ..] };
    run: { k: [Run(op), ..] } => { k: [crate::Decode(op), ..] };
    ld: { k: [Ld(dst, src), ..], acc: _ } => { k: [..], acc: dst };
    halt: { k: [Halt(), ..], halted: _ } => { k: [..], halted: true };
    nop: { k: [Nop(), ..] } => { k: [..] };
    jump: { k: [Jump(), ..], acc: _ } => { k: [..], acc: 0 };
}

#[k::function(total, internal)]
pub fn Decode(op: Term<Int>) -> Term<Inst>;

k::equations! {
    for Decode;
    decode_halt: 0x1f => Instr::Halt();
    #[k::requires(op != 0x1f)]
    decode_ld: op @ k::bits!("01 rr ss") => Instr::Ld(r, s);
    #[k::equation(owise)]
    decode_other: n => Instr::Nop();
}
"#;

const CASES: [(&str, &str); 3] = [
    ("load", "run 16 ; run 21"),
    ("halt", "run 31"),
    ("other", "run 3"),
];

/// The fixture package with its corpus, built once for the tests of this process.
struct Package {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Package {
    fn new() -> Self {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let directory = temp_dir();
        let root = directory.path();
        fs::create_dir_all(root.join("src")).unwrap();
        fs::create_dir_all(root.join("kink/cases")).unwrap();
        fs::write(root.join("src/lib.rs"), LIBRARY).unwrap();
        let mut flow = "[spec]\nkrs = { definition = \"main\" }\n".to_owned();
        for (id, program) in CASES {
            writeln!(
                flow,
                "\n[[program]]\nid = \"{id}\"\nfile = \"cases/{id}.g\""
            )
            .unwrap();
            fs::write(
                root.join(format!("kink/cases/{id}.g")),
                format!("{program}\n"),
            )
            .unwrap();
        }
        fs::write(root.join("kink/FLOW.toml"), flow).unwrap();
        fs::write(
            root.join("Cargo.toml"),
            format!(
                "[package]\nname = \"krs-cli-kink-syntax\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"SYNTAX\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
                serde_json::to_string(krs.to_str().unwrap()).unwrap(),
            ),
        )
        .unwrap();
        Self {
            directory,
            target: shared_fixture_target(),
        }
    }

    /// `krs kink coverage ARGUMENTS` on the package.
    fn coverage(&self, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.directory.path())
            .args(["kink", "coverage"])
            .args(arguments)
            .args(["--package", "krs-cli-kink-syntax", "--definition", "main"]);
        process.output().unwrap()
    }
}

/// The package, and the coverage document of its first run and of a second run that reads the
/// first one's records.
fn documents() -> &'static (Value, Value, String, String) {
    static DOCUMENTS: OnceLock<(Value, Value, String, String)> = OnceLock::new();
    DOCUMENTS.get_or_init(|| {
        let package = Package::new();
        let first = json(&package.coverage(&[]));
        let second = json(&package.coverage(&[]));
        let verdicts = stdout(&package.coverage(&["--output", "verdicts"]));
        let again = stdout(&package.coverage(&["--output", "verdicts"]));
        (first, second, verdicts, again)
    })
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn json(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            stdout(output),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

/// The syntax item whose id is `id`.
fn item<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["families"]["syntax"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|item| item["id"] == id)
        .unwrap_or_else(|| panic!("no syntax item {id}: {:#}", document["families"]["syntax"]))
}

/// The target of the open obligation `id`.
fn target<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["targets"]
        .as_array()
        .unwrap()
        .iter()
        .find(|target| target["item"] == id)
        .unwrap_or_else(|| panic!("no target for {id}: {:#}", document["targets"]))
}

/// The 1-based line of the first line of the library that contains `text`.
fn line_of(text: &str) -> u64 {
    let index = LIBRARY
        .lines()
        .position(|line| line.contains(text))
        .unwrap_or_else(|| panic!("{text:?} is not in the library"));
    u64::try_from(index).unwrap() + 1
}

fn strings(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .unwrap_or_else(|| panic!("{value} is no array"))
        .iter()
        .map(|item| item.as_str().unwrap())
        .collect()
}

/// A variant no step takes, inspects or builds is unreached, named by its Rust path at its
/// declaration, and its target names the rule that inspects it; a variant a step takes as an
/// operand is reached.
#[test]
fn an_unreached_variant_is_named_by_rust_path_with_its_inspecting_sentences() {
    let (document, ..) = documents();
    assert_eq!(document["krs"]["version"], 6, "{:#}", document["krs"]);
    let jump = item(document, "syntax:crate::Instr::Jump");
    assert_eq!(jump["kind"], "production");
    assert_eq!(jump["status"], "unreached");
    assert_eq!(jump["krs"]["item"], "crate::Instr::Jump");
    assert_eq!(jump["krs"]["file"], "src/lib.rs");
    assert_eq!(jump["krs"]["line"], line_of("Jump(),"));
    assert_eq!(strings(&jump["inspecting_rules"]), ["rule:crate::jump"]);
    let text = target(document, "syntax:crate::Instr::Jump")["text"]
        .as_str()
        .unwrap();
    assert!(text.contains("crate::Instr::Jump"), "{text}");
    assert!(text.contains("rule:crate::jump inspect"), "{text}");
    for reached in [
        "crate::Instr::Ld",
        "crate::Instr::Halt",
        "crate::Instr::Nop",
        "crate::CmdSyntax::Seq",
        "crate::CmdSyntax::Run",
    ] {
        assert_eq!(
            item(document, &format!("syntax:{reached}"))["status"],
            "reached",
            "{reached}"
        );
    }
    let counts = &document["families"]["syntax"]["counts"]["productions"];
    assert_eq!(counts["obligations"], 6, "{counts}");
    assert_eq!(counts["covered"], 5, "{counts}");
}

/// A field value no case's decode bound is open, and its target lists the encodings that reach
/// it; one a case bound is reached by that case.
#[test]
fn a_missing_field_value_lists_its_encodings() {
    let (document, ..) = documents();
    let reached = item(document, "syntax:crate::decode_ld:r=1");
    assert_eq!(reached["kind"], "field-value");
    assert_eq!(reached["status"], "reached");
    assert_eq!(strings(&reached["reached_by"]), ["load"]);
    let missing = item(document, "syntax:crate::decode_ld:r=2");
    assert_eq!(missing["status"], "unreached");
    assert_eq!(missing["template"], "01 rr ss");
    assert_eq!(missing["field"], "r");
    assert_eq!(missing["value"], "2");
    assert_eq!(strings(&missing["krs"]["encodings"]), ["0x18-0x1b"]);
    assert_eq!(missing["krs"]["rule"], "crate::decode_ld");
    assert_eq!(missing["krs"]["file"], "src/lib.rs");
    assert_eq!(missing["krs"]["line"], line_of("decode_ld:"));
    let text = target(document, "syntax:crate::decode_ld:r=2")["text"]
        .as_str()
        .unwrap();
    assert!(
        text.starts_with(
            "a case in which crate::decode_ld fires with field r of k::bits!(\"01 rr ss\") = 2 (0b10): encodings 0x18-0x1b"
        ),
        "{text}"
    );
    // The cases whose runs match the template are the closest to one that reaches the value.
    assert!(
        text.ends_with("; the cases that match its templates: load"),
        "{text}"
    );
    let binders = document["families"]["syntax"]["binders"]
        .as_array()
        .unwrap();
    assert_eq!(binders.len(), 1, "{binders:#?}");
    assert_eq!(binders[0]["variable"], "VarOp");
    let values = binders[0]["values"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| value["value"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(values, ["16", "21"]);
}

/// The literal hole `op != 0x1f` is no point of the template's domain: no field value lists it
/// among its encodings, so `r = 3` and `s = 3` are reached by three encodings each.
#[test]
fn the_holes_combination_is_excluded_from_the_universe() {
    let (document, ..) = documents();
    assert_eq!(
        strings(&item(document, "syntax:crate::decode_ld:r=3")["krs"]["encodings"]),
        ["0x1c-0x1e"]
    );
    assert_eq!(
        strings(&item(document, "syntax:crate::decode_ld:s=3")["krs"]["encodings"]),
        ["0x13", "0x17", "0x1b"]
    );
    let fields = document["families"]["syntax"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|item| item["kind"] == "field-value")
        .collect::<Vec<_>>();
    let ids = fields
        .iter()
        .map(|item| item["id"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        ids,
        [
            "syntax:crate::decode_ld:r=0",
            "syntax:crate::decode_ld:r=1",
            "syntax:crate::decode_ld:r=2",
            "syntax:crate::decode_ld:r=3",
            "syntax:crate::decode_ld:s=0",
            "syntax:crate::decode_ld:s=1",
            "syntax:crate::decode_ld:s=2",
            "syntax:crate::decode_ld:s=3",
        ]
    );
    let points = fields
        .iter()
        .filter(|item| item["field"] == "r")
        .flat_map(|item| strings(&item["krs"]["encodings"]))
        .collect::<Vec<_>>();
    assert_eq!(points, ["0x10-0x13", "0x14-0x17", "0x18-0x1b", "0x1c-0x1e"]);
    let counts = &document["families"]["syntax"]["counts"]["field_values"];
    assert_eq!(counts["obligations"], 8, "{counts}");
    assert_eq!(counts["covered"], 4, "{counts}");
}

/// The syntax family and the verdicts are the same bytes whether the runs are computed or read
/// from the records.
#[test]
fn the_syntax_family_is_byte_stable() {
    let (first, second, verdicts, again) = documents();
    assert_eq!(
        serde_json::to_string(&first["families"]["syntax"]).unwrap(),
        serde_json::to_string(&second["families"]["syntax"]).unwrap()
    );
    assert_eq!(
        serde_json::to_string(&first["targets"]).unwrap(),
        serde_json::to_string(&second["targets"]).unwrap()
    );
    assert_eq!(verdicts, again);
    assert!(verdicts.contains("krs_annotation = 6"), "{verdicts}");
    assert!(
        verdicts.contains("\"syntax:crate::decode_ld:r=2\""),
        "{verdicts}"
    );
}

/// A template with an alias is read as a template: its tests are the template's, so the guard's
/// one authored operand is the hole, and the cases that match it are those whose decode had an
/// opcode the template's fixed bits and range admit.
#[test]
fn an_aliased_templates_tests_are_the_templates() {
    let (document, ..) = documents();
    let rule = document["families"]["rules"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|rule| rule["krs"]["item"] == "crate::decode_ld")
        .unwrap();
    let guard = &rule["guard"]["krs"];
    let authored = guard["authored"]
        .as_array()
        .unwrap()
        .iter()
        .map(|operand| operand["text"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(authored, ["op != 0x1f"], "{guard:#}");
    assert_eq!(guard["templates"]["binders"][0]["text"], "\"01 rr ss\"");
    assert_eq!(strings(&rule["krs"]["matched_by"]), ["load"]);
}

/// The condition flips of the aliased template's sentence are placed in its guard as for any
/// sentence: the alias changes which conjuncts are authored, not the condition's display tree,
/// so a flip's occurrence there is reached at its arm's match or at the operand that renders
/// the flipped atom, never left unplaced.
#[test]
fn an_aliased_templates_flips_are_placed_in_its_guard() {
    let (document, ..) = documents();
    let rule = document["families"]["rules"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|rule| rule["krs"]["item"] == "crate::decode_ld")
        .unwrap();
    let flips = &document["families"]["flips"];
    assert_eq!(flips["run"], true, "{flips:#}");
    let mut placed = 0;
    for flip in flips["items"].as_array().unwrap() {
        for occurrence in flip["occurrences"].as_array().unwrap() {
            if occurrence["rule"] != "rule:crate::decode_ld" {
                continue;
            }
            placed += 1;
            assert_eq!(occurrence["unplaced"], Value::Null, "{flip:#}");
            match occurrence["reach"].as_str() {
                Some("match") => {}
                Some("operand") => {
                    let operand = rule["guard"]["operands"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .find(|operand| operand["path"] == occurrence["path"])
                        .unwrap_or_else(|| panic!("{flip:#}\n{:#}", rule["guard"]));
                    assert_eq!(operand["kind"], "atom", "{operand:#}\n{flip:#}");
                    assert_eq!(
                        operand["krs"]["text"], flip["text"],
                        "{operand:#}\n{flip:#}"
                    );
                }
                _ => panic!("{flip:#}"),
            }
        }
    }
    assert!(placed > 0, "no flip occurs in crate::decode_ld: {flips:#}");
}
