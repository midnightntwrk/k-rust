//! Which binders a `cells!` rule's conditions see: every variable its left
//! side binds. A computation remainder `tail @ ..` is the variable `Tail:K`
//! and a map remainder `rest @ ..` the variable `Rest:Map`, so
//! `#[k::requires]` and `#[k::ensures]` may name them; the configuration
//! remainder `state @ ..` and a collection's instance remainder stand for
//! cells the rule leaves out and bind no variable, so naming them in a
//! condition is a KRS error at the name.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, Map, int, kequal, map};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Look, Look2, Look3, Look4, Report) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("look")] Look(),
    #[k::syntax("look2")] Look2(),
    #[k::syntax("look3")] Look3(),
    #[k::syntax("look4")] Look4(),
    #[k::syntax("report")] Report(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub typed: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "ENV")] env: Map,
    ) -> Self {
        Self { k: k::k![pgm], env, typed: map::empty() }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;
    seq: Seq(s1, s2) => k::k![s1, s2];
}
"#;

/// Rules whose conditions name the computation and map remainders.
const RULES: &str = r#"
#[k::rule(label = "look")]
#[k::requires(map::size(rest) == 0)]
pub fn look(
    v: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Look(), tail @ ..),
        env: k::configuration::Cell(k::map![0 -> v, rest @ ..]),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(v, ..tail),
        env: k::configuration::Cell(k::map![0 -> v, ..rest]),
        ..state
    }
}

#[k::rule(label = "look2")]
#[k::requires(k::is!(KResult, tail))]
pub fn look2(
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Look2(), tail @ ..),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        ..state
    }
}

#[k::rule(label = "look3")]
#[k::requires(!map::in_keys(1, rest) && map::get(rest, 2) == v)]
pub fn look3(
    v: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Look3(), tail @ ..),
        typed: k::configuration::Cell(k::map![0 -> v, rest @ ..]),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(v, ..tail),
        typed: k::configuration::Cell(k::map![0 -> v, ..rest]),
        ..state
    }
}

#[k::rule(label = "look4")]
#[k::ensures(k::is!(KResult, tail))]
pub fn look4(
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Look4(), tail @ ..),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-REMAINDERS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// `krs check`'s first error headline and its `-->` location.
fn first_error(target: &Path, manifest: &Path) -> String {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    let headline = stderr
        .lines()
        .find(|line| line.starts_with("error"))
        .unwrap_or_else(|| panic!("no error:\n{stderr}"));
    let location = stderr
        .lines()
        .find_map(|line| line.trim_start().strip_prefix("--> "))
        .and_then(|path| path.split_once("src/lib.rs:"))
        .map_or("unlocated", |(_, location)| location);
    format!("{headline} @ {location}")
}

/// A guard over the computation remainder emits `Tail:K`, and over a map
/// remainder `Rest:Map`, read at the map cell's element types; an ensures
/// condition sees them too.
#[test]
fn conditions_name_the_computation_and_map_remainders() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "remainders",
        &format!("{PREAMBLE}{RULES}"),
    );
    let k = emitted_k(target.path(), &manifest);
    expect_test::expect![[r"
        rule [look]:
            <k> look ~> Tail:K => V:Int ~> Tail:K </k>
            <env> 0 |-> V:Int Rest:Map </env>
            requires size(Rest:Map) ==Int 0
        rule [look2]:
            <k> look2 ~> Tail:K => .K ~> Tail:K </k>
            requires isKResult(Tail:K)
        rule [look3]:
            <k> look3 ~> Tail:K => V:Int ~> Tail:K </k>
            <typed> 0 |-> V:Int Rest:Map </typed>
            requires (notBool 1 in_keys(Rest:Map)) andThenBool ({Rest:Map [ 2 ]}:>Int ==Int V:Int)
        rule [look4]:
            <k> look4 ~> Tail:K => .K ~> Tail:K </k>
            ensures isKResult(Tail:K)"]]
    .assert_eq(
        &["look", "look2", "look3", "look4"]
            .map(|label| rule(&k, label))
            .join("\n"),
    );
}

/// The guards decide where the rules apply: `look2` only before one
/// finished value, `look` only on a one-entry environment.
#[test]
fn remainder_guards_run() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "remainders-run",
        &format!("{PREAMBLE}{RULES}"),
    );
    let program = manifest.with_file_name("program.txt");
    let runs = [
        ("look2 5", ".Map"),
        ("look2 5 report", ".Map"),
        ("look", "0 |-> 5"),
        ("look", "0 |-> 5 1 |-> 6"),
    ]
    .map(|(source, env)| {
        fs::write(&program, source).unwrap();
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[program.to_str().unwrap(), "-c", &format!("ENV={env}")],
        );
        assert!(success, "{source}:\n{stdout}\n{stderr}");
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let start = flat.find("<k>").unwrap();
        let end = flat.find("</k>").unwrap() + "</k>".len();
        format!("{source} with ENV={env} => {}", &flat[start..end])
    });
    expect_test::expect![[r#"
        [
            "look2 5 with ENV=.Map => <k> 5 ~> .K </k>",
            "look2 5 report with ENV=.Map => <k> look2 ~> 5 report ~> .K </k>",
            "look with ENV=0 |-> 5 => <k> 5 ~> .K </k>",
            "look with ENV=0 |-> 5 1 |-> 6 => <k> look ~> .K </k>",
        ]
    "#]]
    .assert_debug_eq(&runs);
}

/// The threads fixture's `join`, whose instance pattern binds the
/// computation remainder `tail0` and the instance remainder `instances0`,
/// with `condition` added.
fn join_with(condition: &str) -> String {
    let source = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/configuration-cells/packages/threads/src/lib.rs"),
    )
    .unwrap();
    let join = "#[k::rule(label = \"join\")]\n";
    assert!(source.contains(join));
    source.replace(join, &format!("{join}{condition}\n"))
}

/// The configuration remainder and an instance remainder bind no variable:
/// a condition that names one is refused at the name; an instance's
/// computation remainder is a `K` variable a guard may name.
#[test]
fn conditions_cannot_name_configuration_or_instance_remainders() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let state = |attribute: &str| {
        RULES.replace(
            "#[k::requires(k::is!(KResult, tail))]",
            &format!("{attribute}\n#[k::requires(k::is!(KResult, tail))]"),
        )
    };
    let cases = [
        (
            "state-requires",
            format!(
                "{PREAMBLE}{}",
                state("#[k::requires(kequal::eq(state, state))]")
                    .replace("#[k::requires(k::is!(KResult, tail))]\n", "")
            ),
        ),
        (
            "state-ensures",
            format!(
                "{PREAMBLE}{}",
                state("#[k::ensures(kequal::eq(state, state))]")
            ),
        ),
        (
            "instances-requires",
            join_with("#[k::requires(kequal::eq(instances0, instances0))]"),
        ),
    ];
    let errors = cases.map(|(name, source)| {
        let manifest = package(temporary.path(), name, &source);
        format!("{name}: {}", first_error(target.path(), &manifest))
    });
    expect_test::expect![[r#"
        [
            "state-requires: error[krs::syntax::unsupported-rule-body]: unsupported rule body: this name is the remainder of the configuration: it stands for the cells this rule leaves out, which K completes from the declaration, so it is not a term a condition can test @ 66:26",
            "state-ensures: error[krs::syntax::unsupported-rule-body]: unsupported rule body: this name is the remainder of the configuration: it stands for the cells this rule leaves out, which K completes from the declaration, so it is not a term a condition can test @ 66:25",
            "instances-requires: error[krs::syntax::unsupported-rule-body]: unsupported rule body: this name is the remainder of a collection's instances: it stands for the instances this rule leaves out, which stay as they are, so it is not a term a condition can test @ 150:26",
        ]
    "#]]
    .assert_debug_eq(&errors);
    let manifest = package(
        temporary.path(),
        "instance-tail",
        &join_with("#[k::requires(k::is!(KResult, tail0))]"),
    );
    assert!(
        rule(&emitted_k(target.path(), &manifest), "join").contains("requires isKResult(Tail0:K)"),
        "the instance's computation remainder is a guard variable"
    );
}
