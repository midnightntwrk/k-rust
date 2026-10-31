//! A leaf cell holds any term of its declared sort or of a subsort, in every
//! rule form and in claims: `2` or a binder a guard narrows to `Int` fills a
//! `Value` cell, a `Value` fills a `Stmt` cell, and any term fills a `KItem`
//! cell. A term of an unrelated sort is still refused at the term. An
//! initializer leaf of a strict subsort is cast to its cell's sort, which K
//! otherwise reads from the initial content.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence};
use k::{KItem, KResult};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Tick, Load, Copy, Fill, Stash, Unstash, Reset, Seq))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("tick")]
    Tick(),
    #[k::syntax("load")]
    Load(),
    #[k::syntax("copy")]
    Copy(),
    #[k::syntax("fill")]
    Fill(),
    #[k::syntax("stash")]
    Stash(),
    #[k::syntax("unstash")]
    Unstash(),
    #[k::syntax("reset")]
    Reset(),
    #[k::syntax("seq ( {first} , {second} )")]
    Seq { first: Stmt, second: Stmt },
}

#[k::constructors(sort = Value, result = KResult)]
pub enum ValueSyntax {
    #[k::syntax("unit")]
    Unit(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Value,
    #[k::cell]
    pub prog: Stmt,
    #[k::cell]
    pub slot: KItem,
}
"#;

const INIT: &str = r#"
impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "ACC")] acc: Value,
        #[k::config_var(name = "SLOT")] slot: KItem,
    ) -> Self {
        Self {
            k: k::k![pgm],
            acc,
            prog: StmtSyntax::Skip(),
            slot,
        }
    }
}
"#;

const RULES: &str = r"
k::rules! {
    for Machine;
    use StmtSyntax::*;
    use ValueSyntax::*;

    seq: { k: [Seq { first: a, second: b }, ..] } => { k: [a, b, ..] };
    #[k::requires(vv == 1)]
    pick: { k: [Skip(), ..], acc: vv } => { k: [..], acc: 2 };
    add: { k: [Tick(), ..], acc: vv } => { k: [..], acc: vv + 10 };
    load: { k: [Load(), ..], prog: _ } => { k: [..], prog: Unit() };
    copy: { k: [Copy(), ..], acc: vv, prog: _ } => { k: [..], prog: vv };
    fill: { k: [Fill(), ..], slot: _ } => { k: [..], slot: 2 };
    stash: { k: [Stash(), ..], slot: _ } => { k: [..], slot: Tick() };
    unstash: { k: [Unstash(), ..], slot: Tick() } => { k: [..], slot: 3 };
}

#[k::rule]
pub fn reset(
    k::cells! { k: k::configuration::KCell(StmtSyntax::Reset(), tail @ ..), acc: k::configuration::Cell(_), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), acc: k::configuration::Cell(2), ..state }
}

k::claims! {
    for Machine;
    use StmtSyntax::*;

    #[k::claim(all_paths)]
    picks: { k: [Skip()], acc: 1 } => { k: [], acc: 2 };
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is the preamble and `body`.
fn package(root: &Path, name: &str, body: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{body}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CONTENT\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
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
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The first diagnostic's headline and the source text its caret marks.
fn first_diagnostic(stderr: &str) -> (String, String) {
    let lines = stderr.lines().collect::<Vec<_>>();
    let index = lines
        .iter()
        .position(|line| line.starts_with("error["))
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
    (lines[index].to_owned(), marked)
}

/// Emits the package's K and returns `definition.k` and `spec.k`.
fn emitted(target: &Path, manifest: &Path) -> (String, String) {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    (
        fs::read_to_string(output.join("definition.k")).unwrap(),
        fs::read_to_string(output.join("spec.k")).unwrap(),
    )
}

/// The body lines of the sentence `kind [label]:` in the emitted K, joined.
fn sentence(k: &str, kind: &str, label: &str) -> String {
    let start = k
        .find(&format!("{kind} [{label}]:"))
        .unwrap_or_else(|| panic!("no {kind} {label}:\n{k}"));
    k[start..]
        .lines()
        .skip(1)
        .take_while(|line| {
            let line = line.trim();
            !line.is_empty()
                && !["rule", "claim", "//", "endmodule"]
                    .iter()
                    .any(|start| line.starts_with(start))
        })
        .map(str::trim)
        .collect::<Vec<_>>()
        .join(" ")
}

/// The final configuration of `krs run` on `program`, flattened.
fn run(target: &Path, manifest: &Path, program: &str, acc: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (_, stdout, stderr) = krs(
        target,
        manifest,
        "run",
        &[
            file.to_str().unwrap(),
            "-c",
            &format!("ACC={acc}"),
            "-c",
            "SLOT=0",
        ],
    );
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("<generatedTop>"), "{stdout}\n{stderr}");
    flat
}

/// Every rule form writes and matches a strict subsort of a leaf cell's sort,
/// the guard over a `Value` binder narrows it to `Int` and runs where `acc`
/// holds 1, a `KItem` cell holds an integer and a statement, and the claim
/// over a `Value` cell is proven.
#[test]
fn a_leaf_cell_holds_any_term_of_a_subsort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "subsorts", &format!("{INIT}{RULES}"));
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &["--backend", "haskell"]);
    assert!(success, "{stderr}");
    let (definition, spec) = emitted(target.path(), &manifest);
    expect_test::expect![[r#"
        [
            "<k> skip => .K ... </k> <acc> Vv:Int => 2 </acc> requires Vv:Int ==Int 1",
            "<k> tick => .K ... </k> <acc> Vv:Int => Vv:Int +Int 10 </acc>",
            "<k> load => .K ... </k> <prog> _ => unit </prog>",
            "<k> copy => .K ... </k> <acc> Vv:Value </acc> <prog> _ => Vv:Value </prog>",
            "<k> fill => .K ... </k> <slot> _ => 2 </slot>",
            "<k> stash => .K ... </k> <slot> _ => tick </slot>",
            "<k> unstash => .K ... </k> <slot> tick => 3 </slot>",
            "<k> reset ~> Tail:K => .K ~> Tail:K </k> <acc> _ => 2 </acc>",
            "<k> skip => .K </k> <acc> 1 => 2 </acc>",
        ]
    "#]]
    .assert_debug_eq(
        &[
            "pick", "add", "load", "copy", "fill", "stash", "unstash", "reset",
        ]
        .map(|label| sentence(&definition, "rule", label))
        .into_iter()
        .chain([sentence(&spec, "claim", "picks")])
        .collect::<Vec<_>>(),
    );

    let applied = run(target.path(), &manifest, "skip", "1");
    assert!(applied.contains("<k> .K </k> <acc> 2 </acc>"), "{applied}");
    let stuck = run(target.path(), &manifest, "skip", "3");
    assert!(
        stuck.contains("<k> skip ~> .K </k> <acc> 3 </acc>"),
        "{stuck}"
    );
    let slot = run(target.path(), &manifest, "seq ( stash , unstash )", "1");
    assert!(
        slot.contains("<k> .K </k>") && slot.contains("<slot> 3 </slot>"),
        "{slot}"
    );

    let (success, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    assert!(success, "{stdout}\n{stderr}");
    assert!(stdout.contains("SPEC.picks: proven"), "{stdout}");
}

/// A content of a sort that is not below the cell's is refused at the term.
/// K gives a cell the sort of its initial content, so `prog: Unit()`, a
/// `Value` in a `Stmt` cell, is emitted cast to the cell's sort,
/// `( unit ):Stmt`, and the cell stays the `Stmt` cell the rules read and
/// write.
#[test]
fn a_cell_content_outside_the_cell_sort_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let unrelated = package(
        temporary.path(),
        "unrelated",
        &format!(
            "{INIT}k::rules! {{\n    for Machine;\n    use StmtSyntax::*;\n\n    bad: {{ k: [Load(), ..], acc: _ }} => {{ k: [..], acc: Tick() }};\n}}\n"
        ),
    );
    let (success, _, stderr) = krs(
        target.path(),
        &unrelated,
        "check",
        &["--backend", "haskell"],
    );
    assert!(!success, "{stderr}");
    assert_eq!(
        first_diagnostic(&stderr),
        (
            "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-CONTENT::bad (rule): application result sort ORG-KRS-CONTENT::Stmt (sort) is not admissible at sort ORG-KRS-CONTENT::Value (sort)".to_owned(),
            "Tick".to_owned(),
        ),
        "{stderr}"
    );

    let narrower = package(
        temporary.path(),
        "narrower",
        &format!(
            "{}{RULES}",
            INIT.replace("StmtSyntax::Skip()", "ValueSyntax::Unit()")
        ),
    );
    let (success, _, stderr) = krs(target.path(), &narrower, "check", &[]);
    assert!(success, "{stderr}");
    let (definition, _) = emitted(target.path(), &narrower);
    assert!(
        definition.contains("<prog> ( unit ):Stmt </prog>"),
        "{definition}"
    );
    let state = run(target.path(), &narrower, "copy", "1");
    assert!(state.contains("<prog> 1 </prog>"), "{state}");
}
