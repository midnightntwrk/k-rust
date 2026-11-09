//! `krs kink coverage`'s syntax family at the KRS level: each production of an authored sort is
//! named by the Rust path of its declaration, and each value of a `k::bits!` template's field is
//! an obligation listed with the encodings that reach it.
//!
//! The fixture is a small machine in the style of the boundary fixture of `tests/kink.rs`: a
//! program runs opcodes, a decode function turns each into an `Instr`, and a rule per variant
//! executes it. The decode reads a 6-bit template `01 rr ss` with two fields, `r` and `s`, and a
//! literal hole: `0x1f` is `halt`, so the template's equation requires `op != 0x1f`. The corpus
//! decodes `0x10`, `0x15` (`r` and `s` 0 and 1), `0x1f` and `0x03`; no case decodes to
//! `Instr::Jump`. Three rules take templates of their own: `wrap` an aliased one whose condition
//! calls a function the package declares under the name `add`, `pair` two without an alias, and
//! `mask` one with holes and no field.

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
#[k::precedence((Run, Wrap, Pair, Mask) > (Seq))]
pub enum CmdSyntax {
    #[k::syntax("{first} ; {rest}")]
    Seq { first: Cmd, rest: Cmd },
    #[k::syntax("run {op}")]
    Run { op: Int },
    #[k::syntax("wrap {op}")]
    Wrap { op: Int },
    #[k::syntax("pair {hi} {lo}")]
    Pair { hi: Int, lo: Int },
    #[k::syntax("mask {op}")]
    Mask { op: Int },
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
    use crate::Add as add;

    seq: { k: [Seq(first, rest), ..] } => { k: [first, rest, ..] };
    run: { k: [Run(op), ..] } => { k: [crate::Decode(op), ..] };
    ld: { k: [Ld(dst, src), ..], acc: _ } => { k: [..], acc: dst };
    halt: { k: [Halt(), ..], halted: _ } => { k: [..], halted: true };
    nop: { k: [Nop(), ..] } => { k: [..] };
    jump: { k: [Jump(), ..], acc: _ } => { k: [..], acc: 0 };
    #[k::requires(add(r, 1) == 0)]
    wrap: { k: [Wrap(op @ k::bits!("10 rr")), ..], acc: _ } => { k: [..], acc: r };
    pair: { k: [Pair(k::bits!("1 aa"), k::bits!("bb 0")), ..], acc: _ } => { k: [..], acc: a + b };
    mask: { k: [Mask(k::bits!("01 __")), ..] } => { k: [..] };
}

#[k::function(total, internal)]
pub fn Add(a: Term<Int>, b: Term<Int>) -> Term<Int>;

k::equations! {
    for Add;
    add_wrapping: (a, b) => (a + b) % 4;
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

const CASES: [(&str, &str); 5] = [
    ("load", "run 16 ; run 21"),
    ("halt", "run 31"),
    ("other", "run 3"),
    ("wrap", "wrap 11 ; mask 5"),
    ("pair", "pair 6 4"),
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
        // The clock never decides a run of the tests (R4-WALLCLOCK).
        let mut flow =
            "[spec]\nkrs = { definition = \"main\" }\n\n[budget]\ntime_ms = 600000\n".to_owned();
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

    /// `krs kink fuzz ARGUMENTS` on the package.
    fn fuzz(&self, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.directory.path())
            .args(["kink", "fuzz"])
            .args(arguments)
            .args(["--package", "krs-cli-kink-syntax", "--definition", "main"]);
        process.output().unwrap()
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

/// The `families.syntax.binders` entry of the binder K writes `variable` in the sentence the
/// loaded definition labels `label`.
fn binder<'d>(document: &'d Value, label: &str, variable: &str) -> &'d Value {
    let binders = &document["families"]["syntax"]["binders"];
    binders
        .as_array()
        .unwrap()
        .iter()
        .find(|binder| {
            binder["variable"] == variable
                && binder["sentences"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|sentence| sentence["label"] == label)
        })
        .unwrap_or_else(|| panic!("no binder {variable} of {label}: {binders:#}"))
}

/// The values a binder took.
fn binder_values(binder: &Value) -> Vec<&str> {
    binder["values"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| value["value"].as_str().unwrap())
        .collect()
}

/// The field-value items of the sentence whose KRS item is `rule`.
fn field_values<'d>(document: &'d Value, rule: &str) -> Vec<&'d Value> {
    document["families"]["syntax"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|item| item["kind"] == "field-value" && item["krs"]["rule"] == rule)
        .collect()
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
    assert_eq!(document["krs"]["version"], 10, "{:#}", document["krs"]);
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
        "crate::CmdSyntax::Wrap",
        "crate::CmdSyntax::Pair",
        "crate::CmdSyntax::Mask",
    ] {
        assert_eq!(
            item(document, &format!("syntax:{reached}"))["status"],
            "reached",
            "{reached}"
        );
    }
    let counts = &document["families"]["syntax"]["counts"]["productions"];
    assert_eq!(counts["obligations"], 9, "{counts}");
    assert_eq!(counts["covered"], 8, "{counts}");
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
        text.ends_with("; the cases that match its templates: load, halt"),
        "{text}"
    );
    let binder = binder(document, "syntax--decode_ld", "VarOp");
    assert_eq!(binder_values(binder), ["16", "21"]);
}

/// A missing field value is a fuzz goal: its item names the binder a fired instance binds and
/// the encodings at which the field has the value, its target spells `fuzz --cover`, and the job
/// finds an opcode in `0x18-0x1b` over the `load` case's first opcode, which `coverage` confirms
/// as reaching the value (CS-8).
#[test]
fn a_field_value_job_finds_an_encoding_that_reaches_the_value() {
    let (document, ..) = documents();
    let id = "syntax:crate::decode_ld:r=2";
    let missing = item(document, id);
    assert_eq!(missing["binder"]["variable"], "VarOp", "{missing:#}");
    assert_eq!(strings(&missing["binder"]["encodings"]), ["0x18-0x1b"]);
    let hint = target(document, id)["fuzz"].as_str().unwrap();
    assert!(
        hint.ends_with(&format!("--template ID --cover {id}")),
        "{hint}"
    );
    assert!(hint.starts_with("krs kink fuzz "), "{hint}");

    let package = Package::new();
    fs::write(
        package.directory.path().join("kink/TEMPLATES.toml"),
        "[[template]]\nid = \"load\"\nprogram = \"load\"\n\n  [[template.hole]]\n  name = \"OP\"\n  \
         sort = \"Int\"\n  find = \"16\"\n  literal = \"16\"\n  range = { min = 0, max = 63 }\n",
    )
    .unwrap();
    let output = package.fuzz(&["--template", "load", "--cover", id, "--cases", "200"]);
    let fuzzed = json(&output);
    assert_eq!(output.status.code(), Some(0), "{fuzzed:#}");
    assert_eq!(fuzzed["job"]["kind"], "cover", "{fuzzed:#}");
    assert_eq!(fuzzed["job"]["item"]["id"], id, "{fuzzed:#}");
    assert_eq!(fuzzed["job"]["item"]["kind"], "field-value", "{fuzzed:#}");
    let confirmation = &fuzzed["attempts"][0]["confirmation"];
    assert_eq!(confirmation["status"], "covered", "{confirmation:#}");
    let op = fuzzed["attempts"][0]["candidate"]["holes"][0]["k-text"]
        .as_str()
        .and_then(|op| op.parse::<u32>().ok())
        .unwrap_or_else(|| panic!("{fuzzed:#}"));
    assert!((0x18..=0x1b).contains(&op), "{fuzzed:#}");
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
    let fields = field_values(document, "crate::decode_ld");
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
    // With the 8 values of `pair`'s two templates and the 4 of `wrap`'s.
    assert_eq!(counts["obligations"], 20, "{counts}");
    assert_eq!(counts["covered"], 7, "{counts}");
}

/// The templates of a rule of `k::rules!` without an alias have hidden binders, which the
/// compiled definition writes `Bits` and `Bits1`, in the rule the loaded definition labels
/// `SYNTAX.pair` (written `rule [pair]:`): every run records their values, so the field values
/// the case `pair 6 4` binds are reached by it.
#[test]
fn a_rules_hidden_binders_record_their_field_values() {
    let (document, ..) = documents();
    assert_eq!(
        binder_values(binder(document, "SYNTAX.pair", "VarBits")),
        ["6"]
    );
    assert_eq!(
        binder_values(binder(document, "SYNTAX.pair", "VarBits1")),
        ["4"]
    );
    for reached in ["syntax:crate::pair:a=2", "syntax:crate::pair:b=2"] {
        let reached = item(document, reached);
        assert_eq!(reached["status"], "reached", "{reached:#}");
        assert_eq!(strings(&reached["reached_by"]), ["pair"], "{reached:#}");
    }
    let missing = item(document, "syntax:crate::pair:b=3");
    assert_eq!(missing["status"], "unreached");
    assert_eq!(missing["template"], "bb 0");
    assert_eq!(strings(&missing["krs"]["encodings"]), ["0x6"]);
    assert_eq!(field_values(document, "crate::pair").len(), 8);
}

/// `wrap`'s condition `add(r, 1) == 0` calls the package's function `Add`, imported as `add`,
/// which is `(a + b) % 4`: it holds at `r = 3`. A conjunct is decided only through K's builtin
/// operations, never by a function's Rust name, so this one is taken to hold, `r = 3` is in the
/// domain, and the case `wrap 11` reaches it.
#[test]
fn a_function_named_like_a_builtin_is_not_evaluated_as_one() {
    let (document, ..) = documents();
    let top = item(document, "syntax:crate::wrap:r=3");
    assert_eq!(strings(&top["krs"]["encodings"]), ["0xb"]);
    assert_eq!(top["status"], "reached", "{top:#}");
    assert_eq!(strings(&top["reached_by"]), ["wrap"]);
    assert_eq!(
        binder_values(binder(document, "SYNTAX.wrap", "VarOp")),
        ["11"]
    );
    // The undecided conjunct takes no value out of the domain.
    assert_eq!(field_values(document, "crate::wrap").len(), 4);
}

/// `mask`'s template `01 __` has holes and no field: it gives no field value and no binder, and
/// it is no template whose values could not be enumerated.
#[test]
fn a_template_without_a_field_has_no_field_value() {
    let (document, ..) = documents();
    assert!(field_values(document, "crate::mask").is_empty());
    let syntax = &document["families"]["syntax"];
    assert_eq!(syntax["krs"]["unenumerated"], Value::Null, "{syntax:#}");
    assert!(
        syntax["binders"]
            .as_array()
            .unwrap()
            .iter()
            .all(|binder| binder["sentences"][0]["label"] != "SYNTAX.mask"),
        "{syntax:#}"
    );
    assert_eq!(
        item(document, "syntax:crate::CmdSyntax::Mask")["status"],
        "reached"
    );
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
    assert!(verdicts.contains("krs_annotation = 10"), "{verdicts}");
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
    assert_eq!(strings(&rule["krs"]["matched_by"]), ["load", "halt"]);
}

/// The condition flips of the aliased template's sentence are placed in its guard as for any
/// sentence: the alias changes which conjuncts are authored, not the condition's display tree,
/// so a flip's occurrence there is reached at its arm's match or at the operand that renders
/// the flipped atom, never left unplaced. An occurrence reached at the match is reached by the
/// cases that match the KRS pattern, its templates included (the row's `krs.matched_by`), not by
/// every case that evaluated the function (the row's K-level `matched_by`).
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
    assert_eq!(strings(&rule["krs"]["matched_by"]), ["load", "halt"]);
    assert_eq!(strings(&rule["matched_by"]), ["load", "halt", "other"]);
    let mut placed = 0;
    let mut matched = 0;
    for flip in flips["items"].as_array().unwrap() {
        for occurrence in flip["occurrences"].as_array().unwrap() {
            if occurrence["rule"] != "rule:crate::decode_ld" {
                continue;
            }
            placed += 1;
            assert_eq!(occurrence["unplaced"], Value::Null, "{flip:#}");
            match occurrence["reach"].as_str() {
                Some("match") => {
                    matched += 1;
                    assert_eq!(
                        strings(&occurrence["reached_by"]),
                        ["load", "halt"],
                        "{flip:#}"
                    );
                }
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
    assert!(
        matched > 0,
        "no flip of crate::decode_ld is reached at its match: {flips:#}"
    );
}

/// An argued syntax item is named by its KRS id: an unreached variant by its Rust path and a
/// field value by its template's rule and field. Each has status `argued` with its argument, stays
/// among the family's obligations, and gives no target; the verdicts rendering lists both. The
/// K-level name of the variant names no item, so it refuses the command.
#[test]
fn an_argued_syntax_item_is_named_by_its_krs_id() {
    let package = Package::new();
    let manifest = package.directory.path().join("kink/FLOW.toml");
    let flow = fs::read_to_string(&manifest).unwrap();
    let argue = |entries: &[(&str, &str)]| {
        let mut text = flow.clone();
        for (item, argument) in entries {
            write!(
                text,
                "\n[[coverage.argued]]\nitem = \"{item}\"\nargument = \"{argument}\"\n"
            )
            .unwrap();
        }
        fs::write(&manifest, text).unwrap();
    };
    argue(&[
        ("syntax:crate::Instr::Jump", "no opcode decodes to a jump"),
        (
            "syntax:crate::decode_ld:r=2",
            "no program loads into register 2",
        ),
    ]);
    let output = package.coverage(&["--tier", "1"]);
    let document = json(&output);
    assert_eq!(output.status.code(), Some(0), "{document:#}");
    for (id, argument, kind) in [
        (
            "syntax:crate::Instr::Jump",
            "no opcode decodes to a jump",
            "production",
        ),
        (
            "syntax:crate::decode_ld:r=2",
            "no program loads into register 2",
            "field-value",
        ),
    ] {
        let argued = item(&document, id);
        assert_eq!(argued["kind"], kind, "{argued:#}");
        assert_eq!(argued["status"], "argued", "{argued:#}");
        assert_eq!(argued["unargued_status"], "unreached", "{argued:#}");
        assert_eq!(argued["argument"], argument, "{argued:#}");
        assert!(
            document["targets"]
                .as_array()
                .unwrap()
                .iter()
                .all(|target| target["item"] != id),
            "{id}: {:#}",
            document["targets"]
        );
    }
    let counts = &document["families"]["syntax"]["counts"];
    assert_eq!(counts["productions"]["argued"], 1, "{counts}");
    assert_eq!(counts["field_values"]["argued"], 1, "{counts}");
    assert_eq!(document["summary"]["per_family"]["syntax"]["argued"], 2);
    let verdicts = stdout(&package.coverage(&["--tier", "1", "--output", "verdicts"]));
    assert!(
        verdicts.contains(
            "\nargued = [\n  { id = \"syntax:crate::decode_ld:r=2\", standing = \"text\" },\n  \
             { id = \"syntax:crate::Instr::Jump\", standing = \"text\" },\n]\n"
        ) || verdicts.contains(
            "\nargued = [\n  { id = \"syntax:crate::Instr::Jump\", standing = \"text\" },\n  \
             { id = \"syntax:crate::decode_ld:r=2\", standing = \"text\" },\n]\n"
        ),
        "{verdicts}"
    );

    argue(&[("syntax:Jump", "no opcode decodes to a jump")]);
    let output = package.coverage(&["--tier", "1"]);
    let refused = json(&output);
    assert_eq!(output.status.code(), Some(2), "{refused:#}");
    assert_eq!(refused["spec"]["reason"], "argued-stale", "{refused:#}");
    assert!(
        refused["spec"]["detail"]
            .as_str()
            .unwrap()
            .contains("`syntax:Jump`: no family lists it"),
        "{refused:#}"
    );
}

/// The syntax paths item whose id is `id`.
fn path_item<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["families"]["syntax_paths"]["items"]
        .as_array()
        .unwrap_or_else(|| panic!("no syntax paths: {:#}", document["families"]))
        .iter()
        .find(|item| item["id"] == id)
        .unwrap_or_else(|| panic!("no path {id}: {:#}", document["families"]["syntax_paths"]))
}

/// At depth 2, a template with several fields gives its joint field values: one item per
/// combination of its fields' values some point of its arm domain gives, so `decode_ld`'s
/// `01 rr ss` under `op != 0x1f` has the 15 combinations other than `r = 3, s = 3`. A combination
/// is reached where a comparable case decoded an opcode that has it: `0x10` and `0x15`. A
/// combination whose field values are each reached is on the frontier and has a target with its
/// encodings; one with a field value no case reached is not. The productions' paths are named by
/// Rust path: `Seq` holding `Run` at either argument is reached by the case that sequences two
/// runs.
#[test]
fn a_templates_joint_field_values_are_its_depth_2_paths() {
    let package = Package::new();
    let document = json(&package.coverage(&["--depth", "2"]));
    let family = &document["families"]["syntax_paths"];
    let joint = family["items"]
        .as_array()
        .unwrap_or_else(|| panic!("{:#}", document["families"]))
        .iter()
        .filter(|item| item["kind"] == "field-values" && item["krs"]["rule"] == "crate::decode_ld")
        .map(|item| item["id"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(joint.len(), 15, "{joint:?}");
    assert!(
        !joint.contains(&"path:crate::decode_ld:r=3,s=3"),
        "{joint:?}"
    );
    let reached = path_item(&document, "path:crate::decode_ld:r=0,s=0");
    assert_eq!(reached["status"], "reached", "{reached:#}");
    assert_eq!(strings(&reached["covered_by"]), ["load"]);
    assert_eq!(
        strings(&reached["krs"]["parts"]),
        ["crate::decode_ld:r=0", "crate::decode_ld:s=0"]
    );
    let frontier = path_item(&document, "path:crate::decode_ld:r=0,s=1");
    assert_eq!(
        (&frontier["status"], &frontier["frontier"]),
        (&serde_json::json!("unreached"), &serde_json::json!(true)),
        "{frontier:#}"
    );
    let text = target(&document, "path:crate::decode_ld:r=0,s=1")["text"]
        .as_str()
        .unwrap();
    assert!(
        text.starts_with(
            "a case in which crate::decode_ld fires with the fields of k::bits!(\"01 rr ss\") at \
             once r = 0 (0b00), s = 1 (0b01): encodings 0x11"
        ),
        "{text}"
    );
    let off = path_item(&document, "path:crate::decode_ld:r=2,s=0");
    assert_eq!(off["frontier"], false, "{off:#}");
    assert!(
        document["targets"]
            .as_array()
            .unwrap()
            .iter()
            .all(|target| target["item"] != "path:crate::decode_ld:r=2,s=0")
    );
    assert_eq!(
        family["counts"]["field_values"]["obligations"]
            .as_u64()
            .unwrap(),
        15,
        "{:#}",
        family["counts"]
    );
    assert_eq!(family["counts"]["field_values"]["covered"], 2);
    for argument in [0, 1] {
        let id = format!("path:crate::CmdSyntax::Seq/{argument}/crate::CmdSyntax::Run");
        assert!(
            strings(&path_item(&document, &id)["covered_by"]).contains(&"load"),
            "{id}"
        );
    }
    // A template with one field has no joint value: its field values are the syntax family's.
    assert!(
        family["items"]
            .as_array()
            .unwrap()
            .iter()
            .all(|item| item["kind"] != "field-values" || item["krs"]["rule"] == "crate::decode_ld"),
        "{family:#}"
    );
}
