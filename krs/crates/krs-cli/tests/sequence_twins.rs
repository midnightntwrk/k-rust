//! A sequence cell's rests have one verdict at every position that holds them (SEQTWINS): a
//! top sequence leaf (`aux`), the computation cell (`k`), a List leaf (`ll`), an instance's
//! computation child (`tk`, `jk`), and the `cells!` `KCell(..)` twin. Each row is checked
//! through `krs check` and `krs emit-k`, which run the macro and the collector on the same
//! source, and compared with its twin's line or K.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, Set, list, set};
use k::{KItem, KResult};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("put({a}, {b})")] Put { a: Int, b: Int },
}

#[k::cell]
pub struct Th {
    #[k::cell]
    pub tid: Int,
    #[k::cell]
    pub tl: List,
    #[k::cell]
    pub tk: KSequence,
}

#[k::cell]
pub struct Ths {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub th: Th,
}

#[k::cell]
pub struct Job {
    #[k::cell]
    pub jk: KSequence,
}

#[k::cell]
pub struct Jobs {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub job: Job,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub ll: List,
    #[k::cell]
    pub aux: KSequence,
    #[k::cell]
    pub ss: Set,
    #[k::cell]
    pub out: List,
    #[k::cell(nested)]
    pub ths: Ths,
    #[k::cell(nested)]
    pub jobs: Jobs,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            ll: list::empty(),
            aux: k::k![],
            ss: set::empty(),
            out: list::empty(),
            ths: Ths { th: Th { tid: 0, tl: list::empty(), tk: k::k![] } },
            jobs: Jobs { job: Job { jk: k::k![] } },
        }
    }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is the preamble and `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-SEQTWINS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String) {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .args(extra)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The row's verdict: its first error line, or the emitted sentence `go` (a rule or a claim) on
/// one line.
fn verdict(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    if !success {
        return stderr
            .lines()
            .find(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("no error:\n{stderr}"))
            .to_owned();
    }
    let mut k = fs::read_to_string(output.join("definition.k")).unwrap();
    if let Ok(spec) = fs::read_to_string(output.join("spec.k")) {
        k.push_str(&spec);
    }
    let k = krs_test_support::without_source_comments(&k);
    let start = ["rule [go]:", "claim [go]:"]
        .iter()
        .find_map(|head| k.find(head))
        .unwrap_or_else(|| panic!("`go` is emitted:\n{k}"));
    let end = ["rule [", "claim [", "endmodule"]
        .iter()
        .filter_map(|next| k[start + 1..].find(next))
        .min()
        .map_or(k.len(), |end| start + 1 + end);
    k[start..end]
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

/// A readable rule, or claim, of the one clause `body`.
fn readable(body: &str, claim: bool) -> String {
    let (block, attribute) = if claim {
        ("claims", "#[k::claim(all_paths)] ")
    } else {
        ("rules", "")
    };
    format!("k::{block}! {{\n    for Machine;\n    use Cmd::*;\n\n    {attribute}{body}\n}}\n")
}

/// A `cells!` rule, or claim, with the term parameters `parameters`.
fn cells(parameters: &str, subject: &str, result: &str, claim: bool) -> String {
    let attribute = if claim {
        "k::claim(all_paths, "
    } else {
        "k::rule("
    };
    format!(
        "#[{attribute}label = \"go\")]\npub fn go(\n    {parameters}k::cells! {{ {subject}, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ {result}, ..state }}\n}}\n"
    )
}

/// The verdict of each row, `name: verdict`, in the rows' order.
fn verdicts(rows: &[(&str, String)]) -> Vec<String> {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    rows.iter()
        .map(|(name, source)| {
            let manifest = package(temporary.path(), &format!("seq-{name}"), source);
            format!("{name}: {}", verdict(target.path(), &manifest))
        })
        .collect()
}

/// The verdict of `name` in `lines`, without its name.
fn of<'a>(lines: &'a [String], name: &str) -> &'a str {
    lines
        .iter()
        .find_map(|line| line.strip_prefix(&format!("{name}: ")))
        .unwrap_or_else(|| panic!("row `{name}`"))
}

/// Item 1: `[..] => [..]` on a sequence leaf keeps whatever the cell holds, so the rule changes
/// no cell, as its `cells!` twin `KCell(..) => KCell(..)` and a List leaf's `[..] => [..]` do,
/// whichever cell the rule names first; the claim states the cell kept, with the twin's K.
#[test]
fn an_item_less_sequence_the_result_keeps_changes_no_cell_as_its_twins() {
    const KC: &str = "k::configuration::";
    let rule = |body: &str| readable(body, false);
    let claim = |body: &str| readable(body, true);
    let lines = verdicts(&[
        ("aux", rule("go: { aux: [..] } => { aux: [..] };")),
        ("k", rule("go: { k: [..] } => { k: [..] };")),
        ("aux-unwritten", rule("go: { aux: [..] } => { };")),
        (
            "aux-then-ll",
            rule("go: { aux: [..], ll: [..] } => { aux: [..], ll: [..] };"),
        ),
        (
            "ll-then-aux",
            rule("go: { ll: [..], aux: [..] } => { ll: [..], aux: [..] };"),
        ),
        (
            "aux-then-k",
            rule("go: { aux: [..], k: [..] } => { aux: [..], k: [..] };"),
        ),
        (
            "cells-aux",
            cells(
                "",
                &format!("aux: {KC}KCell(..)"),
                &format!("aux: {KC}KCell(..)"),
                false,
            ),
        ),
        ("claim-aux", claim("go: { aux: [..] } => { aux: [..] };")),
        ("claim-k", claim("go: { k: [..] } => { k: [..] };")),
        (
            "claim-cells-aux",
            cells(
                "",
                &format!("aux: {KC}KCell(..)"),
                &format!("aux: {KC}KCell(..)"),
                true,
            ),
        ),
        (
            "claim-cells-k",
            cells(
                "",
                &format!("k: {KC}KCell(..)"),
                &format!("k: {KC}KCell(..)"),
                true,
            ),
        ),
    ]);
    expect_test::expect![[r"
        aux: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        k: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        aux-unwritten: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        aux-then-ll: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        ll-then-aux: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        aux-then-k: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        cells-aux: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        claim-aux: claim [go]: <aux> .K ... </aux>
        claim-k: claim [go]: <k> .K ... </k>
        claim-cells-aux: claim [go]: <aux> .K ... </aux>
        claim-cells-k: claim [go]: <k> .K ... </k>"]]
    .assert_eq(&lines.join("\n"));
    for (row, twin) in [
        ("aux", "cells-aux"),
        ("k", "cells-aux"),
        ("aux-unwritten", "cells-aux"),
        ("aux-then-ll", "ll-then-aux"),
        ("aux-then-k", "cells-aux"),
        ("claim-aux", "claim-cells-aux"),
        ("claim-k", "claim-cells-k"),
    ] {
        assert_eq!(of(&lines, row), of(&lines, twin), "{row} vs {twin}");
    }
}

/// Item 2: `_` among an instance's computation child's items is one item, as it is in the
/// computation cell's head, a top sequence leaf's brackets and the `cells!` fragment's child,
/// and as a named item there is: braced and bracketed, rule and claim.
#[test]
fn a_wildcard_item_of_an_instance_computation_child_is_one_item() {
    let row = |child: &str, claim: bool| {
        readable(
            &format!("go: {{ k: [Go(), ..], {child} }} => {{ k: [..] }};"),
            claim,
        )
    };
    let lines = verdicts(&[
        ("tk", row("th: { Th { tk: [_, ..], .. }, .. }", false)),
        ("jk", row("job: [Job { jk: [_, ..], .. }, ..]", false)),
        ("claim-tk", row("th: { Th { tk: [_, ..], .. }, .. }", true)),
        ("tk-named", row("th: { Th { tk: [y, ..], .. }, .. }", false)),
        (
            "aux",
            readable("go: { aux: [_, ..], ll: _ } => { ll: [] };", false),
        ),
    ]);
    expect_test::expect![[r"
        tk: rule [go]: <k> go => .K ... </k> <th> <tk> _:KItem ~> Tail0:K </tk> ... </th>
        jk: rule [go]: <k> go => .K ... </k> <jobs> <job> <jk> _:KItem ~> Tail0:K </jk> ... </job> ... </jobs>
        claim-tk: claim [go]: <k> go => .K ... </k> <th> <tk> _:KItem ~> Tail0:K </tk> ... </th>
        tk-named: rule [go]: <k> go => .K ... </k> <th> <tk> Y:KItem ~> Tail0:K </tk> ... </th>
        aux: rule [go]: <aux> _:KItem ... </aux> <ll> _ => .List </ll>"]]
    .assert_eq(&lines.join("\n"));
    assert_eq!(
        of(&lines, "tk").replace("_:KItem", "Y:KItem"),
        of(&lines, "tk-named")
    );
    assert_eq!(
        of(&lines, "tk").replace("rule", "claim"),
        of(&lines, "claim-tk")
    );
}
