//! A `cells!` rule's computation remainder `tail @ ..` is the variable
//! `Tail:K`, a value a result may write: at a `KSequence` field it saves the
//! continuation, and a result that does not put it back with `..tail` has
//! moved it, so the computation cell's new content is what the result lists.
//! A map remainder is a value too while it is put back; moving one out of
//! its cell is refused, and so are a dropped remainder and the configuration
//! remainder as a term.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, List, Map, int, list, map};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Park, Resume, Bump, Report, Keep, Drop, Store, WrapK) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("park")] Park(),
    #[k::syntax("resume")] Resume(),
    #[k::syntax("bump")] Bump(),
    #[k::syntax("report")] Report(),
    #[k::syntax("keep")] Keep(),
    #[k::syntax("drop")] Drop(),
    #[k::syntax("store")] Store(),
    #[k::syntax("wrapk ( {body} )")] WrapK { body: KSequence },
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
    #[k::cell]
    pub env: Map,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "PC")] pc: Int,
        #[k::config_var(name = "GAS")] gas: Int,
        #[k::config_var(name = "ENV")] env: Map,
    ) -> Self {
        Self { k: k::k![pgm], stack: list::empty(), frame: Frame { pc, gas }, env }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;
    seq: Seq(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use Cmd::*;
    resume: { k: [Resume(), ..], stack: [WrapK { body: b }, s @ ..] } => { k: [b, ..], stack: s };
    bump: { k: [Bump(), ..], frame: Frame { pc: p, gas: g } } => { k: [..], frame: Frame { pc: int::add(p, 1), gas: int::sub(g, 1) } };
    report: { k: [Report(), ..], frame: Frame { pc: p, gas: g } } => { k: [int::add(int::mul(100, p), g), ..] };
}
"#;

/// `park` saves the rest of the computation in a `WrapK` on the stack and
/// moves it; `keep` saves a copy and keeps it; `store` reads a map
/// remainder it puts back.
const RULES: &str = r#"
#[k::rule(label = "park")]
pub fn park(
    s: k::Term<List>,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Park(), tail @ ..),
        stack: k::configuration::Cell(s),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Bump(), crate::Cmd::Resume()),
        stack: k::configuration::Cell(list::concat(list::item(crate::Cmd::WrapK { body: tail }), s)),
        ..state
    }
}

#[k::rule(label = "keep")]
pub fn keep(
    s: k::Term<List>,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Keep(), tail @ ..),
        stack: k::configuration::Cell(s),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Bump(), crate::Cmd::Resume(), ..tail),
        stack: k::configuration::Cell(list::concat(list::item(crate::Cmd::WrapK { body: tail }), s)),
        ..state
    }
}

#[k::rule(label = "store")]
pub fn store(
    v: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Store(), tail @ ..),
        env: k::configuration::Cell(k::map![0 -> v, rest @ ..]),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(map::size(rest), ..tail),
        env: k::configuration::Cell(k::map![0 -> v, ..rest]),
        ..state
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

/// Writes a one-package workspace whose library is `library`.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-REMAINDER-VALUES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// A moved remainder is the subject's last item and is absent from the
/// cell's new content; a kept one stays on both sides; a map remainder put
/// back is a value of its cell's map.
#[test]
fn a_computation_remainder_is_a_value_moved_unless_put_back() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "values", &format!("{PREAMBLE}{RULES}"));
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let k = fs::read_to_string(output.join("definition.k")).unwrap();
    expect_test::expect![[r"
        rule [park]:
            <k> park ~> Tail:K => bump ~> resume </k>
            <stack> S:List => ListItem(wrapk ( Tail:K )) S:List </stack>
        rule [keep]:
            <k> keep ~> Tail:K => bump ~> resume ~> Tail:K </k>
            <stack> S:List => ListItem(wrapk ( Tail:K )) S:List </stack>
        rule [store]:
            <k> store ~> Tail:K => size(Rest:Map) ~> Tail:K </k>
            <env> 0 |-> V:Int Rest:Map </env>"]]
    .assert_eq(
        &["park", "keep", "store"]
            .map(|label| rule(&k, label))
            .join("\n"),
    );
    let program = manifest.with_file_name("program.txt");
    let runs = ["park report", "keep report"].map(|source| {
        fs::write(&program, source).unwrap();
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[
                program.to_str().unwrap(),
                "-c",
                "PC=0",
                "-c",
                "GAS=13",
                "-c",
                "ENV=.Map",
            ],
        );
        assert!(success, "{source}:\n{stdout}\n{stderr}");
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let start = flat.find("<k>").unwrap();
        let end = flat.find("</stack>").unwrap() + "</stack>".len();
        format!("{source} => {}", &flat[start..end])
    });
    expect_test::expect![[r#"
        [
            "park report => <k> 112 ~> .K </k> <stack> .List </stack>",
            "keep report => <k> 112 ~> report ~> .K </k> <stack> .List </stack>",
        ]
    "#]]
    .assert_debug_eq(&runs);
}

/// `krs check`'s first error headline.
fn first_error(target: &Path, manifest: &Path) -> String {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    stderr
        .lines()
        .find(|line| line.starts_with("error"))
        .unwrap_or_else(|| panic!("no error:\n{stderr}"))
        .to_owned()
}

/// A bound remainder the rule neither puts back nor uses, a moved map
/// remainder, the configuration remainder as a term, and one item or a
/// sequence literal at a `K` field are refused.
#[test]
fn remainders_the_rule_cannot_write_are_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "dropped",
            r#"
#[k::rule(label = "lost")]
pub fn lost(
    k::cells! { k: k::configuration::KCell(crate::Cmd::Drop(), tail @ ..), state @ .. }: crate::Machine,
) -> crate::Machine {
    k::cells! { k: k::configuration::KCell(crate::Cmd::Bump()), ..state }
}
"#,
        ),
        (
            "moved-map",
            r#"
#[k::rule(label = "moved")]
pub fn moved(
    v: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Drop(), tail @ ..),
        env: k::configuration::Cell(k::map![0 -> v, rest @ ..]),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map::update(rest, 1, v)),
        ..state
    }
}
"#,
        ),
        (
            "state-term",
            r#"
#[k::rule(label = "whole")]
pub fn whole(
    s: k::Term<List>,
    k::cells! { k: k::configuration::KCell(crate::Cmd::Drop(), tail @ ..), stack: k::configuration::Cell(s), state @ .. }: crate::Machine,
) -> crate::Machine {
    k::cells! { k: k::configuration::KCell(..tail), stack: k::configuration::Cell(list::concat(list::item(state), s)), ..state }
}
"#,
        ),
        (
            "one-item",
            r"
k::rules! {
    for Machine;
    use Cmd::*;
    one: { k: [Keep(), ..], stack: s } => { k: [..], stack: [WrapK { body: Bump() }, ..s] };
}
",
        ),
        (
            "sequence-literal",
            r"
k::rules! {
    for Machine;
    use Cmd::*;
    two: { k: [Keep(), ..], stack: s } => { k: [..], stack: [WrapK { body: k::k![Bump(), Report()] }, ..s] };
}
",
        ),
    ];
    let errors = cases.map(|(name, rules)| {
        let manifest = package(temporary.path(), name, &format!("{PREAMBLE}{rules}"));
        format!("{name}: {}", first_error(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            "dropped: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-REMAINDER-VALUES::lost (rule): the computation remainder `tail` is neither put back with `..tail` nor used, so the rule would drop the rest of the computation: keep it with `..tail`, or use it in a condition",
            "moved-map: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-REMAINDER-VALUES::moved (rule): the result writes the whole `env` cell without putting back its map remainder `rest`; a rule cannot move a map remainder yet, so keep it with `..rest`",
            "state-term: error[krs::syntax::unsupported-rule-body]: unsupported rule body: this name is the remainder of the configuration: it stands for the cells this rule leaves out, which K completes from the declaration, so it is not a term a result can write",
            "one-item: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-REMAINDER-VALUES::one (rule): application result sort ORG-KRS-REMAINDER-VALUES::Stmt (sort) is not admissible at sort K",
            "sequence-literal: error[krs::syntax::unsupported-term-expression]: unsupported term expression: macros are not terms unless they are compiler-owned `fragment!`, `id!`, `bytes!`, `anonymous!`, `lexeme!`, `is!`, `project!`, `matches!`, `or_bool!`, or `rewrite!` islands",
        ]
    "#]]
    .assert_debug_eq(&errors);
}
