//! A readable record's value (a cell value, a list element, a computation
//! item) is a pattern below the rule's subject, so `|` and parentheses at
//! its root read as they do below a constructor: an alias may stand inside
//! each alternative, `(s @ P1 | s @ P2)` being `s @ (P1 | P2)`, and a bare
//! name binds. The bracket spelling emits the K of the `list::concat`
//! spelling, runs, and proves as a claim.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, int, list};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Save, Pick, Pick2, Pick3, Report) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("save")] Save(),
    #[k::syntax("pick")] Pick(),
    #[k::syntax("pick2")] Pick2(),
    #[k::syntax("pick3")] Pick3(),
    #[k::syntax("report")] Report(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "PC")] pc: Int,
    ) -> Self {
        Self { k: k::k![pgm], stack: list::empty(), frame: Frame { pc, gas: 7 } }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;
    seq: Seq(s1, s2) => k::k![s1, s2];
}
"#;

/// The machine rules with `{STACK}`, the subject of `restore`'s stack cell,
/// in one spelling.
const RULES: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    save: { k: [Save(), ..], stack: s, frame: f } => { k: [..], stack: list::concat(list::item(f), s) };
    restore: { k: [Pick(), ..], stack: {STACK}, frame: _ } => { k: [..], stack: s, frame: saved };
    report: { k: [Report(), ..], frame: Frame { pc: p, gas: g } } => { k: [int::add(int::mul(100, p), g), ..] };
}
";

const CLAIM: &str = r"
k::claims! {
    for Machine;
    use Cmd::*;

    #[k::claim(all_paths)]
    restore_claim: { k: [Pick()], stack: [(saved @ Frame { pc: 0, .. } | saved @ Frame { pc: 1, .. })], frame: _ } => { k: [], stack: [], frame: saved };
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is the preamble and
/// `source`; every package shares one K namespace.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-ALTERNATIVES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

fn rules(stack: &str) -> String {
    RULES.replace("{STACK}", stack)
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

/// The K source `krs emit-k` writes for the package.
fn emitted_k(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k")).unwrap()
}

/// The emitted rule labelled `label`, up to the next rule.
fn rule<'a>(k: &'a str, label: &str) -> &'a str {
    let start = k
        .find(&format!("rule [{label}]:"))
        .unwrap_or_else(|| panic!("rule `{label}` is emitted:\n{k}"));
    let end = ["rule [", "endmodule"]
        .iter()
        .filter_map(|next| k[start + 1..].find(next))
        .min()
        .map_or(k.len(), |end| start + 1 + end);
    k[start..end].trim_end()
}

/// An alias inside each alternative of a list element emits the K of the
/// `list::concat` spelling, with or without parentheses; the alias over the
/// `|` is the same pattern with `#as` written once.
#[test]
fn an_alias_inside_a_list_elements_alternatives_names_the_element() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let emitted = |name: &str, stack: &str| {
        emitted_k(
            target.path(),
            &package(temporary.path(), name, &rules(stack)),
        )
    };
    let concat = emitted(
        "concat",
        "list::concat(list::item(saved @ Frame { pc: 0, .. } | saved @ Frame { pc: 1, .. }), s)",
    );
    let parenthesized = emitted(
        "parenthesized",
        "[(saved @ Frame { pc: 0, .. } | saved @ Frame { pc: 1, .. }), s @ ..]",
    );
    let bare = emitted(
        "bare",
        "[saved @ Frame { pc: 0, .. } | saved @ Frame { pc: 1, .. }, s @ ..]",
    );
    let over = emitted(
        "over",
        "[saved @ (Frame { pc: 0, .. } | Frame { pc: 1, .. }), s @ ..]",
    );
    assert_eq!(parenthesized, concat);
    assert_eq!(bare, concat);
    expect_test::expect![[r"
        rule [restore]:
            <k> pick => .K ... </k>
            <stack> ListItem(( ( <frame> <pc> 0 </pc> <gas> _ </gas> </frame> #as Saved:FrameCell ) #Or ( <frame> <pc> 1 </pc> <gas> _ </gas> </frame> #as Saved:FrameCell ) )) S:List => S:List </stack>
            (_:FrameCell => Saved:FrameCell)"]]
    .assert_eq(rule(&concat, "restore"));
    expect_test::expect![[r"
        rule [restore]:
            <k> pick => .K ... </k>
            <stack> ListItem(( ( <frame> <pc> 0 </pc> <gas> _ </gas> </frame> #Or <frame> <pc> 1 </pc> <gas> _ </gas> </frame> ) #as Saved:FrameCell )) S:List => S:List </stack>
            (_:FrameCell => Saved:FrameCell)"]]
    .assert_eq(rule(&over, "restore"));
}

/// The bracket spelling restores a saved frame whose `pc` is 0 or 1 and is
/// stuck on any other, and its claim form is proven.
#[test]
fn an_alias_inside_alternatives_runs_and_proves() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "runs",
        &format!(
            "{}{CLAIM}",
            rules("[(saved @ Frame { pc: 0, .. } | saved @ Frame { pc: 1, .. }), s @ ..]")
        ),
    );
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "save pick report").unwrap();
    let runs = ["0", "1", "5"].map(|pc| {
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[program.to_str().unwrap(), "-c", &format!("PC={pc}")],
        );
        assert!(success, "PC={pc}:\n{stdout}\n{stderr}");
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let start = flat.find("<k>").unwrap();
        let end = flat.find("</stack>").unwrap() + "</stack>".len();
        format!("PC={pc} => {}", &flat[start..end])
    });
    expect_test::expect![[r#"
        [
            "PC=0 => <k> 7 ~> .K </k> <stack> .List </stack>",
            "PC=1 => <k> 107 ~> .K </k> <stack> .List </stack>",
            "PC=5 => <k> pick ~> report ~> .K </k> <stack> ListItem ( <frame> <pc> 5 </pc> <gas> 7 </gas> </frame> ) </stack>",
        ]
    "#]]
    .assert_debug_eq(&runs);
    let (success, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    assert!(
        success && format!("{stdout}{stderr}").contains("1 of 1 claim proven"),
        "{stdout}\n{stderr}"
    );
}

/// At a readable value's root a bare name binds, inside parentheses and
/// `|` as alone, so a name the other alternative does not bind is an error
/// and a unit constructor is written `Name()`.
#[test]
fn a_bare_name_in_a_readable_values_alternatives_binds() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "binders",
        &format!(
            "{}k::rules! {{\n    for Machine;\n    use Cmd::*;\n    look: {{ k: [Pick2(), ..], pc: (p) }} => {{ k: [p, ..] }};\n}}\n",
            rules("[(saved @ Frame { pc: 0, .. } | saved @ Frame { pc: 1, .. }), s @ ..]")
        ),
    );
    expect_test::expect![[r"
        rule [look]:
            <k> pick2 => P:Int ... </k>
            <pc> P:Int </pc>"]]
    .assert_eq(rule(&emitted_k(target.path(), &manifest), "look"));
    for (name, value) in [
        ("unbound", "pc: (0 | p)"),
        ("units", "k: [(Pick2 | Pick3), ..]"),
    ] {
        let head = if name == "units" {
            ""
        } else {
            "k: [Pick2(), ..], "
        };
        let manifest = package(
            temporary.path(),
            name,
            &format!(
                "k::rules! {{\n    for Machine;\n    use Cmd::*;\n    look: {{ {head}{value} }} => {{ k: [..] }};\n}}\n"
            ),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{stderr}");
        let variable = if name == "units" { "Pick2" } else { "p" };
        assert!(
            stderr.contains(&format!(
                "error[krs::syntax::invalid-pattern-or]: variable `{variable}` is not bound in all alternatives"
            )),
            "{stderr}"
        );
    }
}
