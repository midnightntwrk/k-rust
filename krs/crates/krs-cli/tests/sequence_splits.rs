//! A matched computation determines its parts (KSEQSPLITS). A rule's pattern binds its
//! variables, so a K sequence pattern means one thing only when every computation it matches
//! splits into its parts in one way. A part has a known length when it is one item (a
//! constructor, a binder declared at an item sort, an alias or rewrite of one item) or a binder of
//! sort `K` another occurrence fixes; a rest and any other `K` part have an unknown length. A
//! pattern with at most one part of unknown length is admitted with its K; one with two or more is
//! refused with one text that names them, on every route: a readable rule, a `cells!` rule and
//! claim, an instance's computation child and a group record's, each read and written in both
//! spellings. A closed computation's part of unknown length followed by an item matches the
//! computations that end with the items after it, a match from the computation's end the target
//! does not perform: refused, as a stated limit.
//!
//! The admitted `KCell(b, ..)`, `KCell(b, c, ..)` and `KCell(b, c)` with `b`, `c` declared
//! `KSequence` emitted `<k> B:K ... </k>`, `B:K ~> C:K ...` and `B:K ~> C:K`: `~>` is associative
//! with unit `.K`, so each matched a computation of n items in n + 1 or more ways, `.K` parts
//! included, binding the parts differently in each. They are refused now.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A machine with the computation cell `k`, a second computation cell `aux`, a fixed group `gg`
/// with a computation child `hk`, a Map collection `th` whose instances hold a computation child
/// `tk`, a list `ll` and an `Int` cell `acc` the probes change; `Make`, `Keep` (a `KSequence`
/// field) and `Skip` are the items.
const SOURCE: &str = r#"
use k::builtin::{Int, KSequence, List, list};
use k::{KItem, KResult};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Make, Keep, Skip))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("make({x})")] Make { x: Int },
    #[k::syntax("keep({body})")] Keep { body: KSequence },
    #[k::syntax("skip")] Skip(),
}

#[k::cell]
pub struct Gg {
    #[k::cell]
    pub ha: Int,
    #[k::cell]
    pub hk: KSequence,
}

#[k::cell]
pub struct Th {
    #[k::cell]
    pub tid: Int,
    #[k::cell]
    pub tk: KSequence,
}

#[k::cell]
pub struct Ths {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub th: Th,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub aux: KSequence,
    #[k::cell]
    pub ll: List,
    #[k::cell]
    pub acc: Int,
    #[k::cell(nested)]
    pub gg: Gg,
    #[k::cell(nested)]
    pub ths: Ths,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            aux: k::k![],
            ll: list::empty(),
            acc: 0,
            gg: Gg { ha: 0, hk: k::k![] },
            ths: Ths { th: Th { tid: 0, tk: k::k![] } },
        }
    }
}

{SENTENCES}
"#;

const KC: &str = "k::configuration::";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is [`SOURCE`] with `sentences`.
fn package(root: &Path, name: &str, sentences: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        SOURCE.replace("{SENTENCES}", sentences),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-SPLITS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// The verdict on the sentence `probe` of the package at `manifest`: its first error line with the
/// text its caret marks, or the emitted sentence on one line without the `acc` change.
fn verdict(target: &Path, manifest: &Path) -> String {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let output = manifest.with_file_name("emitted");
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let run = process
        .args(["emit-k", "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main", "--output"])
        .arg(&output)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    if !run.status.success() {
        let stderr = String::from_utf8(run.stderr).unwrap();
        let lines = stderr.lines().collect::<Vec<_>>();
        let index = lines
            .iter()
            .position(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("no error:\n{stderr}"));
        // `--> path`, ` |`, `N | source`, ` |   ^^^`.
        let marked = lines
            .get(index + 3)
            .zip(lines.get(index + 4))
            .and_then(|(source, carets)| {
                let source = source.split_once(" | ")?.1;
                let carets = carets.split_once(" | ")?.1;
                let start = carets.find('^')?;
                let width = carets[start..].chars().take_while(|c| *c == '^').count();
                source.get(start..start + width).map(str::to_owned)
            })
            .unwrap_or_default();
        return format!("{} at `{marked}`", lines[index]);
    }
    let mut k = fs::read_to_string(output.join("definition.k")).unwrap();
    if let Ok(spec) = fs::read_to_string(output.join("spec.k")) {
        k.push_str(&spec);
    }
    let k = krs_test_support::without_source_comments(&k);
    // The sentence labelled `probe`: a rule or claim names it in brackets, an equation in its
    // attributes.
    let mut sentences = Vec::<String>::new();
    for line in k.lines().map(str::trim) {
        if line.starts_with("rule ") || line.starts_with("claim ") {
            sentences.push(line.to_owned());
        } else if line.is_empty() || line.starts_with("syntax ") || line.starts_with("endmodule") {
            sentences.push(String::new());
        } else if let Some(sentence) = sentences.last_mut().filter(|sentence| !sentence.is_empty())
        {
            sentence.push(' ');
            sentence.push_str(line);
        }
    }
    sentences
        .into_iter()
        .find(|sentence| sentence.contains("[probe]:") || sentence.contains("--probe)]"))
        .unwrap_or_else(|| panic!("`probe` is emitted:\n{k}"))
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .replace(" <acc> _ => 1 </acc>", "")
        .replace(" <acc> _ </acc>", "")
}

/// The verdict of each row, `name: verdict`, in the rows' order.
fn table(rows: &[(String, String)]) -> String {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    rows.iter()
        .map(|(name, sentences)| {
            // A package name is an identifier: `..` is `rest`, `@` is `as`.
            let slug = name
                .replace("..", "rest")
                .replace('@', "as")
                .replace(|c: char| !c.is_ascii_alphanumeric(), "-");
            let manifest = package(temporary.path(), &format!("split-{slug}"), sentences);
            format!("{name}: {}", verdict(target.path(), &manifest))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The probe rows: each a name, its items (`b`, `c` binders, `make`, `keep_b`, `skip`, `alias_b`)
/// and whether it ends in a rest.
const ROWS: [(&str, &[&str], bool); 9] = [
    ("b,..", &["b"], true),
    ("b,c,..", &["b", "c"], true),
    ("make,b,..", &["make", "b"], true),
    ("make,b,c", &["make", "b", "c"], false),
    ("b,make,..", &["b", "make"], true),
    ("b,make", &["b", "make"], false),
    ("make,b", &["make", "b"], false),
    ("keep(b),b,..", &["keep_b", "b"], true),
    ("skip,b@make,..", &["skip", "alias_b"], true),
];

/// A row's items, written readable or, `qualified`, in `cells!`.
fn items(parts: &[&str], open: bool, qualified: bool) -> String {
    let q = if qualified { "Cmd::" } else { "" };
    let mut items = parts
        .iter()
        .map(|part| match *part {
            "make" => format!("{q}Make {{ x }}"),
            "keep_b" => format!("{q}Keep {{ body: b }}"),
            "skip" => format!("{q}Skip()"),
            "alias_b" => format!("b @ {q}Make {{ x }}"),
            binder => binder.to_owned(),
        })
        .collect::<Vec<_>>();
    if open {
        items.push("..".to_owned());
    }
    items.join(", ")
}

/// A row's binders, `x` the `Make` field's.
fn binders(parts: &[&str]) -> Vec<&'static str> {
    let mut names = Vec::new();
    for part in parts {
        let more: &[&'static str] = match *part {
            "b" | "keep_b" => &["b"],
            "c" => &["c"],
            "make" => &["x"],
            "alias_b" => &["b", "x"],
            _ => &[],
        };
        for name in more {
            if !names.contains(name) {
                names.push(*name);
            }
        }
    }
    names
}

/// The rule or claim `probe` matching a row's items on `route` with its `b` and `c` declared at
/// `sort` (none: inferred, readable only).
fn sentence(route: &str, parts: &[&str], open: bool, sort: Option<&str>) -> String {
    let names = binders(parts);
    let readable_items = items(parts, open, false);
    let cells_items = items(parts, open, true);
    let r#where = sort.map_or_else(String::new, |sort| {
        let declared = names
            .iter()
            .filter(|name| **name != "x")
            .map(|name| format!("{name}: {sort}"))
            .collect::<Vec<_>>();
        format!(" where {}", declared.join(", "))
    });
    // A `cells!` sentence declares its binders; a readable one with `sort` none infers them.
    let mut parameters = String::new();
    for name in &names {
        let sort = if *name == "x" {
            "Int"
        } else {
            sort.unwrap_or_default()
        };
        write!(parameters, "{name}: {sort},\n    ").unwrap();
    }
    let readable = |entry: &str| {
        format!(
            "k::rules! {{\n    for Machine;\n    use Cmd::*;\n\n    probe: {{ {entry}, acc: _ }} => {{ acc: 1 }}{where};\n}}\n",
            r#where = r#where
        )
    };
    let single_body = |entry: &str| {
        format!(
            "#[k::rule(label = \"probe\")]\npub fn probe(\n    {parameters}k::cells! {{ {entry}, acc: {KC}Cell(k::rewrite!(_ => 1)), .. }}: Machine,\n) {{}}\n"
        )
    };
    // A sentence with a result restates the items, an alias by its name.
    let restated = cells_items.replace("b @ Cmd::Make { x }", "b");
    match route {
        "readable" => readable(&format!("k: [{readable_items}]")),
        "instance-readable" => readable(&format!(
            "th: {{ Th {{ tk: [{readable_items}], .. }}, .. }}"
        )),
        "group-readable" => readable(&format!("gg: Gg {{ hk: [{readable_items}], .. }}")),
        "cells-rule" => single_body(&format!("k: {KC}KCell({cells_items})")),
        "group-cells" => single_body(&format!("Gg::hk: {KC}KCell({cells_items})")),
        "cells-claim" => format!(
            "#[k::claim(all_paths, label = \"probe\")]\npub fn probe(\n    {parameters}k::cells! {{ k: {KC}KCell({}), acc: {KC}Cell(_), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: {KC}KCell({}), acc: {KC}Cell(1), ..state }}\n}}\n",
            cells_items.replace(", ..", ", rest @ .."),
            restated.replace(", ..", ", ..rest"),
        ),
        "instance-cells" => format!(
            "#[k::rule(label = \"probe\")]\npub fn probe(\n    {parameters}k::cells! {{ Ths::th: {{ me @ k::fragment![crate::Th {{ tk: [{cells_items}], .. }}], i @ .. }}, acc: {KC}Cell(_), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ Ths::th: {{ me, ..i }}, acc: {KC}Cell(1), ..state }}\n}}\n"
        ),
        _ => unreachable!("route {route}"),
    }
}

/// The routes every row is judged on.
const ROUTES: [&str; 7] = [
    "readable",
    "cells-rule",
    "cells-claim",
    "instance-readable",
    "instance-cells",
    "group-readable",
    "group-cells",
];

/// Every row with `b` and `c` declared `KSequence`, on every route: two or more parts of unknown
/// length (`b` and a rest, `b` and `c`) are refused with one text, true of each, at the computation;
/// one part of unknown length is admitted last (`make,b`) and refused before an item, a match from
/// the computation's end (`b,make`); `b` fixed by the `Keep` field before it has a known length
/// (`keep(b),b,..`); and a `KSequence` alias of one item is a stated limit, refused before any
/// split is judged (in a single-body rule `@` is refused first).
#[test]
fn two_parts_of_unknown_length_are_refused_on_every_route() {
    let rows = ROWS
        .iter()
        .flat_map(|(name, parts, open)| {
            ROUTES.iter().map(move |route| {
                (
                    format!("{name} {route}"),
                    sentence(route, parts, *open, Some("KSequence")),
                )
            })
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        b,.. readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `k`
        b,.. cells-rule: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, ..`
        b,.. cells-claim: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (claim): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, rest @ ..`
        b,.. instance-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, ..`
        b,.. instance-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, ..]`
        b,.. group-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, ..]`
        b,.. group-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, ..`
        b,c,.. readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b`, `c`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `k`
        b,c,.. cells-rule: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b`, `c`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, c, ..`
        b,c,.. cells-claim: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (claim): the computation pattern has several parts of unknown length, `b`, `c`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, c, rest @ ..`
        b,c,.. instance-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b`, `c`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, c, ..`
        b,c,.. instance-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b`, `c`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, c, ..]`
        b,c,.. group-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b`, `c`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, c, ..]`
        b,c,.. group-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b`, `c`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, c, ..`
        make,b,.. readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `k`
        make,b,.. cells-rule: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Cmd::Make { x }, b, ..`
        make,b,.. cells-claim: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (claim): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Cmd::Make { x }, b, rest @ ..`
        make,b,.. instance-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Make { x }, b, ..`
        make,b,.. instance-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Cmd::Make { x }, b, ..]`
        make,b,.. group-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Make { x }, b, ..]`
        make,b,.. group-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Cmd::Make { x }, b, ..`
        make,b,c readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and `c`: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `k`
        make,b,c cells-rule: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and `c`: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Cmd::Make { x }, b, c`
        make,b,c cells-claim: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (claim): the computation pattern has several parts of unknown length, `b` and `c`: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Cmd::Make { x }, b, c`
        make,b,c instance-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and `c`: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Make { x }, b, c`
        make,b,c instance-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and `c`: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Cmd::Make { x }, b, c]`
        make,b,c group-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and `c`: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Make { x }, b, c]`
        make,b,c group-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and `c`: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Cmd::Make { x }, b, c`
        b,make,.. readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `k`
        b,make,.. cells-rule: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, Cmd::Make { x }, ..`
        b,make,.. cells-claim: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (claim): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, Cmd::Make { x }, rest @ ..`
        b,make,.. instance-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, Make { x }, ..`
        b,make,.. instance-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, Cmd::Make { x }, ..]`
        b,make,.. group-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, Make { x }, ..]`
        b,make,.. group-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, Cmd::Make { x }, ..`
        b,make readable: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Make`
        b,make cells-rule: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Cmd::Make { x }`
        b,make cells-claim: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Cmd::Make { x }`
        b,make instance-readable: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Make { x }`
        b,make instance-cells: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Cmd::Make`
        b,make group-readable: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Make`
        b,make group-cells: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Cmd::Make { x }`
        make,b readable: rule [probe]: <k> make ( X:Int ) ~> B:K </k>
        make,b cells-rule: rule [probe]: <k> make ( X:Int ) ~> B:K </k>
        make,b cells-claim: claim [probe]: <k> make ( X:Int ) ~> B:K </k>
        make,b instance-readable: rule [probe]: <th> <tk> make ( X:Int ) ~> B:K </tk> ... </th>
        make,b instance-cells: rule [probe]: <th> <tk> make ( X:Int ) ~> B:K </tk> ... </th>
        make,b group-readable: rule [probe]: <hk> make ( X:Int ) ~> B:K </hk>
        make,b group-cells: rule [probe]: <hk> make ( X:Int ) ~> B:K </hk>
        keep(b),b,.. readable: rule [probe]: <k> keep ( B:K ) ~> B:K ... </k>
        keep(b),b,.. cells-rule: rule [probe]: <k> keep ( B:K ) ~> B:K ... </k>
        keep(b),b,.. cells-claim: claim [probe]: <k> keep ( B:K ) ~> B:K ~> Rest:K </k>
        keep(b),b,.. instance-readable: rule [probe]: <th> <tk> keep ( B:K ) ~> B:K ~> Tail0:K </tk> ... </th>
        keep(b),b,.. instance-cells: rule [probe]: <th> <tk> keep ( B:K ) ~> B:K ... </tk> ... </th>
        keep(b),b,.. group-readable: rule [probe]: <hk> keep ( B:K ) ~> B:K ... </hk>
        keep(b),b,.. group-cells: rule [probe]: <hk> keep ( B:K ) ~> B:K ... </hk>
        skip,b@make,.. readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): an alias of sort `K` that names one item of a matched computation is not supported yet; declare the alias at the item's sort (`k::KItem`, or a sort below it) at `b @ Make { x }`
        skip,b@make,.. cells-rule: error[krs::syntax::invalid-pattern-as]: `name @ pattern` (K's #as) names the term a pattern matched, so it stands only where a sentence matches: a subject, or a `k::matches!` pattern in a condition; a single-body rule's subject outside its `k::rewrite!` islands is kept as it is, as a context's and a context alias's are around their hole, and a result only builds; here it stands in the subject of a single-body `cells!` rule at `b`
        skip,b@make,.. cells-claim: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (claim): an alias of sort `K` that names one item of a matched computation is not supported yet; declare the alias at the item's sort (`k::KItem`, or a sort below it) at `b @ Cmd::Make { x }`
        skip,b@make,.. instance-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): an alias of sort `K` that names one item of a matched computation is not supported yet; declare the alias at the item's sort (`k::KItem`, or a sort below it) at `b @ Make { x }`
        skip,b@make,.. instance-cells: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): an alias of sort `K` that names one item of a matched computation is not supported yet; declare the alias at the item's sort (`k::KItem`, or a sort below it) at `b @ Cmd::Make { x }`
        skip,b@make,.. group-readable: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): an alias of sort `K` that names one item of a matched computation is not supported yet; declare the alias at the item's sort (`k::KItem`, or a sort below it) at `b @ Make { x }`
        skip,b@make,.. group-cells: error[krs::syntax::invalid-pattern-as]: `name @ pattern` (K's #as) names the term a pattern matched, so it stands only where a sentence matches: a subject, or a `k::matches!` pattern in a condition; a single-body rule's subject outside its `k::rewrite!` islands is kept as it is, as a context's and a context alias's are around their hole, and a result only builds; here it stands in the subject of a single-body `cells!` rule at `b`"#]].assert_eq(&table(&rows));
}

/// Every row with `b` and `c` declared at an item sort, `KItem` or the constructor sort `Stmt`, on
/// the readable and the `cells!` rule routes, and readable with `b` and `c` inferred, which an item
/// position infers `KItem` and a `KSequence` field infers `K`: each part has a known length, so
/// each row splits one way and is admitted with its K (an alias in a single-body rule refuses `@`
/// first).
#[test]
fn a_part_at_an_item_sort_has_a_known_length() {
    let rows = ROWS
        .iter()
        .flat_map(|(name, parts, open)| {
            [
                ("readable", Some("KItem")),
                ("cells-rule", Some("k::KItem")),
                ("readable", Some("Stmt")),
                ("cells-rule", Some("Stmt")),
                ("readable", None),
            ]
            .into_iter()
            .map(move |(route, sort)| {
                (
                    format!("{name} {route} {}", sort.unwrap_or("inferred")),
                    sentence(route, parts, *open, sort),
                )
            })
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r"
        b,.. readable KItem: rule [probe]: <k> B:KItem ... </k>
        b,.. cells-rule k::KItem: rule [probe]: <k> B:KItem ... </k>
        b,.. readable Stmt: rule [probe]: <k> B:Stmt ... </k>
        b,.. cells-rule Stmt: rule [probe]: <k> B:Stmt ... </k>
        b,.. readable inferred: rule [probe]: <k> B:KItem ... </k>
        b,c,.. readable KItem: rule [probe]: <k> B:KItem ~> C:KItem ... </k>
        b,c,.. cells-rule k::KItem: rule [probe]: <k> B:KItem ~> C:KItem ... </k>
        b,c,.. readable Stmt: rule [probe]: <k> B:Stmt ~> C:Stmt ... </k>
        b,c,.. cells-rule Stmt: rule [probe]: <k> B:Stmt ~> C:Stmt ... </k>
        b,c,.. readable inferred: rule [probe]: <k> B:KItem ~> C:KItem ... </k>
        make,b,.. readable KItem: rule [probe]: <k> make ( X:Int ) ~> B:KItem ... </k>
        make,b,.. cells-rule k::KItem: rule [probe]: <k> make ( X:Int ) ~> B:KItem ... </k>
        make,b,.. readable Stmt: rule [probe]: <k> make ( X:Int ) ~> B:Stmt ... </k>
        make,b,.. cells-rule Stmt: rule [probe]: <k> make ( X:Int ) ~> B:Stmt ... </k>
        make,b,.. readable inferred: rule [probe]: <k> make ( X:Int ) ~> B:KItem ... </k>
        make,b,c readable KItem: rule [probe]: <k> make ( X:Int ) ~> B:KItem ~> C:KItem </k>
        make,b,c cells-rule k::KItem: rule [probe]: <k> make ( X:Int ) ~> B:KItem ~> C:KItem </k>
        make,b,c readable Stmt: rule [probe]: <k> make ( X:Int ) ~> B:Stmt ~> C:Stmt </k>
        make,b,c cells-rule Stmt: rule [probe]: <k> make ( X:Int ) ~> B:Stmt ~> C:Stmt </k>
        make,b,c readable inferred: rule [probe]: <k> make ( X:Int ) ~> B:KItem ~> C:KItem </k>
        b,make,.. readable KItem: rule [probe]: <k> B:KItem ~> make ( X:Int ) ... </k>
        b,make,.. cells-rule k::KItem: rule [probe]: <k> B:KItem ~> make ( X:Int ) ... </k>
        b,make,.. readable Stmt: rule [probe]: <k> B:Stmt ~> make ( X:Int ) ... </k>
        b,make,.. cells-rule Stmt: rule [probe]: <k> B:Stmt ~> make ( X:Int ) ... </k>
        b,make,.. readable inferred: rule [probe]: <k> B:KItem ~> make ( X:Int ) ... </k>
        b,make readable KItem: rule [probe]: <k> B:KItem ~> make ( X:Int ) </k>
        b,make cells-rule k::KItem: rule [probe]: <k> B:KItem ~> make ( X:Int ) </k>
        b,make readable Stmt: rule [probe]: <k> B:Stmt ~> make ( X:Int ) </k>
        b,make cells-rule Stmt: rule [probe]: <k> B:Stmt ~> make ( X:Int ) </k>
        b,make readable inferred: rule [probe]: <k> B:KItem ~> make ( X:Int ) </k>
        make,b readable KItem: rule [probe]: <k> make ( X:Int ) ~> B:KItem </k>
        make,b cells-rule k::KItem: rule [probe]: <k> make ( X:Int ) ~> B:KItem </k>
        make,b readable Stmt: rule [probe]: <k> make ( X:Int ) ~> B:Stmt </k>
        make,b cells-rule Stmt: rule [probe]: <k> make ( X:Int ) ~> B:Stmt </k>
        make,b readable inferred: rule [probe]: <k> make ( X:Int ) ~> B:KItem </k>
        keep(b),b,.. readable KItem: rule [probe]: <k> keep ( B:KItem ) ~> B:KItem ... </k>
        keep(b),b,.. cells-rule k::KItem: rule [probe]: <k> keep ( B:KItem ) ~> B:KItem ... </k>
        keep(b),b,.. readable Stmt: rule [probe]: <k> keep ( B:Stmt ) ~> B:Stmt ... </k>
        keep(b),b,.. cells-rule Stmt: rule [probe]: <k> keep ( B:Stmt ) ~> B:Stmt ... </k>
        keep(b),b,.. readable inferred: rule [probe]: <k> keep ( B:K ) ~> B:K ... </k>
        skip,b@make,.. readable KItem: rule [probe]: <k> skip ~> ( make ( X:Int ) #as B:KItem ) ... </k>
        skip,b@make,.. cells-rule k::KItem: error[krs::syntax::invalid-pattern-as]: `name @ pattern` (K's #as) names the term a pattern matched, so it stands only where a sentence matches: a subject, or a `k::matches!` pattern in a condition; a single-body rule's subject outside its `k::rewrite!` islands is kept as it is, as a context's and a context alias's are around their hole, and a result only builds; here it stands in the subject of a single-body `cells!` rule at `b`
        skip,b@make,.. readable Stmt: rule [probe]: <k> skip ~> ( make ( X:Int ) #as B:Stmt ) ... </k>
        skip,b@make,.. cells-rule Stmt: error[krs::syntax::invalid-pattern-as]: `name @ pattern` (K's #as) names the term a pattern matched, so it stands only where a sentence matches: a subject, or a `k::matches!` pattern in a condition; a single-body rule's subject outside its `k::rewrite!` islands is kept as it is, as a context's and a context alias's are around their hole, and a result only builds; here it stands in the subject of a single-body `cells!` rule at `b`
        skip,b@make,.. readable inferred: rule [probe]: <k> skip ~> ( make ( X:Int ) #as B:Stmt ) ... </k>"]].assert_eq(&table(&rows));
}

/// A binder of sort `K` another occurrence fixes has a known length where that occurrence's place
/// does not depend on a part of unknown length: another cell (`aux: KCell(b)`, a list's item
/// `keep(b)`), an item before it, an item after it in a closed computation. An occurrence after it
/// in an open computation (`b, keep(b), ..`) or on a rewrite's right side fixes nothing. A closed
/// computation that names one binder twice (`b, b`) splits one way; with a rest it does not. A
/// rewrite whose left side has unknown length is such a part, and a named rest is a rest. Its own
/// item after it still matches the computation from its end (`b, keep(b)`), and so does an item
/// after two parts the item fixes one of. A context's computation is judged the same way, an equation's function
/// context's with the binders the equation's subject fixes (`Peek(b)`), and the readable `swap`,
/// whose K matched `B = C = .K` and changed nothing, is refused.
#[test]
fn a_binder_another_occurrence_fixes_has_a_known_length() {
    let single_body = |parameters: &str, entries: &str| {
        format!(
            "#[k::rule(label = \"probe\")]\npub fn probe(\n    {parameters}\n    k::cells! {{ {entries}, acc: {KC}Cell(k::rewrite!(_ => 1)), .. }}: Machine,\n) {{}}\n"
        )
    };
    let kk = format!("{KC}KCell");
    let rows = [
        ("another-cell", single_body("b: KSequence,", &format!("k: {kk}(b, ..), aux: {kk}(b)"))),
        ("another-cell/open", single_body("x: Int,\n    b: KSequence,", &format!("k: {kk}(Cmd::Make {{ x }}, b, ..), aux: {kk}(Cmd::Keep {{ body: b }}, ..)"))),
        ("another-cell/crossed", single_body("b: KSequence,\n    c: KSequence,", &format!("k: {kk}(b, c, ..), aux: {kk}(c, b, ..)"))),
        ("list-item", single_body("b: KSequence,", &format!("k: {kk}(b, ..), ll: {KC}Cell([Cmd::Keep {{ body: b }}])"))),
        ("rewrite-right", single_body("b: KSequence,", &format!("k: {kk}(b, ..), aux: {kk}(k::rewrite!(_ => b))"))),
        ("item-before/closed", single_body("b: KSequence,\n    x: Int,", &format!("k: {kk}(Cmd::Keep {{ body: b }}, b, Cmd::Make {{ x }})"))),
        ("item-after/open", single_body("b: KSequence,", &format!("k: {kk}(b, Cmd::Keep {{ body: b }}, ..)"))),
        ("item-after/closed", single_body("b: KSequence,", &format!("k: {kk}(b, Cmd::Keep {{ body: b }})"))),
        ("item-after/fixes-one", single_body("b: KSequence,\n    c: KSequence,", &format!("k: {kk}(b, c, Cmd::Keep {{ body: c }})"))),
        ("twice/closed", single_body("b: KSequence,", &format!("k: {kk}(b, b)"))),
        ("twice/open", single_body("b: KSequence,", &format!("k: {kk}(b, b, ..)"))),
        ("twice/back", single_body("b: KSequence,", &format!("k: {kk}(b, b, Cmd::Skip())"))),
        ("rewrite/open", single_body("b: KSequence,", &format!("k: {kk}(k::rewrite!(b => Cmd::Make {{ x: 1 }}), ..)"))),
        ("rewrite/closed", single_body("b: KSequence,", &format!("k: {kk}(k::rewrite!(b => Cmd::Make {{ x: 1 }}))"))),
        ("named-rest", format!("#[k::rule(label = \"probe\")]\npub fn probe(\n    b: KSequence,\n    k::cells! {{ k: {kk}(b, tail @ ..), acc: {KC}Cell(_), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: {kk}(..tail), acc: {KC}Cell(1), ..state }}\n}}\n")),
        ("context", format!("#[k::context(hole = h)]\nfn probe(\n    h: Int,\n    b: KSequence,\n    k::cells! {{ k: {kk}(Cmd::Make {{ x: h }}, b, ..), .. }}: Machine,\n) {{}}\n")),
        ("function-context", format!("#[k::function(partial, internal)]\npub fn Peek(body: k::Term<KSequence>) -> k::Term<Int>;\n\n#[k::equation]\nfn probe(\n    b: KSequence,\n    k::term![Peek(b)]: k::Term<Int>,\n    k::cells! {{ k: {kk}(b, ..), .. }}: Machine,\n) -> k::Term<Int> {{\n    0\n}}\n")),
        ("function-context/unfixed", format!("#[k::function(partial, internal)]\npub fn Peek(body: k::Term<KSequence>) -> k::Term<Int>;\n\n#[k::equation]\nfn probe(\n    c: KSequence,\n    b: KSequence,\n    k::term![Peek(c)]: k::Term<Int>,\n    k::cells! {{ k: {kk}(b, ..), .. }}: Machine,\n) -> k::Term<Int> {{\n    0\n}}\n")),
        ("swap", "k::rules! {\n    for Machine;\n    use Cmd::*;\n\n    probe: { k: [b, c, ..] } => { k: [c, b, ..] } where b: KSequence, c: KSequence;\n}\n".to_owned()),
    ]
    .map(|(name, sentences)| (name.to_owned(), sentences));
    expect_test::expect![[r#"
        another-cell: rule [probe]: <k> B:K ... </k> <aux> B:K </aux>
        another-cell/open: rule [probe]: <k> make ( X:Int ) ~> B:K ... </k> <aux> keep ( B:K ) ... </aux>
        another-cell/crossed: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b`, `c`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, c, ..`
        list-item: rule [probe]: <k> B:K ... </k> <ll> ListItem(keep ( B:K )) </ll>
        rewrite-right: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, ..`
        item-before/closed: rule [probe]: <k> keep ( B:K ) ~> B:K ~> make ( X:Int ) </k>
        item-after/open: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, Cmd::Keep { body: b }, ..`
        item-after/closed: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Cmd::Keep { body: b }`
        item-after/fixes-one: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Cmd::Keep { body: c }`
        twice/closed: rule [probe]: <k> B:K ~> B:K </k>
        twice/open: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b`, `b`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, b, ..`
        twice/back: error[krs::collect::invalid-configuration]: not supported: a computation matched from its end: the closed computation pattern has an item after a part of sort `K` whose length its front does not fix, so it matches the computations that end with the items after that part, and the target matches a computation from its front only; when the part is one item, declare its binder at an item sort (`KItem`, or a sort below it) at `Cmd::Skip()`
        rewrite/open: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `k::rewrite!(b => ..)` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `k::rewrite!(b => Cmd::Make { x: 1 }), ..`
        rewrite/closed: rule [probe]: <k> (B:K => make ( 1 )) </k>
        named-rest: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, tail @ ..`
        context: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (context): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `Cmd::Make { x: h }, b, ..`
        function-context: rule [[ peek ( B:K ) => 0 ]] <k> B:K ... </k> [label(org_krs_splits--probe)]
        function-context/unfixed: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (equation): the computation pattern has several parts of unknown length, `b` and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `b, ..`
        swap: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-SPLITS::probe (rule): the computation pattern has several parts of unknown length, `b`, `c`, and the rest: a computation it matches can split between them in more than one way, each binding them differently, so the pattern does not determine what they match; give all of them but one a known length, by declaring a binder at an item sort (`KItem`, or a sort below it) or by matching one item in its place at `k`"#]].assert_eq(&table(&rows));
}
