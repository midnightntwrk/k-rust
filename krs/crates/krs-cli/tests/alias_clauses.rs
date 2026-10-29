//! An alias clause runs two ways. Forward, as a desugar clause does, it expands every subject
//! written in a program or a rule into its result. Backward, when a result is printed, every term
//! its result matches prints as its subject, built from what that match bound. So the subject is
//! built too: a construct that only matches (`_`, `name @ pattern`, `A | B`, an open record, a
//! list's anonymous rest) and a name the result does not use have no value there, and the printed
//! alias would not denote the printed value. Each is refused at the construct, or at the name,
//! with a message that says what would print and points to `#[k::desugar]`, which runs one way.
//! What the result computes is admitted: a concrete printed value holds no unevaluated
//! application, so the reverse does not fire on it, and a symbolic one holds the very application
//! the clause expands to, so the printed alias denotes it.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Bool, Int, KSequence, List};
use k::{KItem, KResult, Term};

k::sorts! {
    Value: KResult;
    impl Value for Int, Bool;
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Data {
    #[k::syntax("red")] Red(),
    #[k::syntax("box({a})")] Box { a: Int },
    #[k::syntax("tag({a})")] Tag { a: Int },
    #[k::syntax("pair({a}, {b})")] Pair { a: Int, b: Int },
    #[k::syntax("one({a})")] One { a: Value },
    #[k::syntax("two({a}, {b})")] Two { a: KItem, b: List },
    #[k::syntax("flag({a})")] Flag { a: Bool },
    #[k::syntax("mk({a}, {b})")] Mk { a: Int, b: Int },
    #[k::syntax("probe({a})")] Probe { a: Value },
    #[k::syntax("calc({a}, {b})")] Calc { a: Int, b: Int },
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Al {
    #[k::syntax("whole({a})")] #[k::alias] Whole { a: Value },
    #[k::syntax("pairs({a}, {b})")] #[k::alias] Pairs { a: Int, b: Int },
    #[k::syntax("items({a})")] #[k::alias] Items { a: List },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Value) -> Self {
        Self { k: k::k![pgm] }
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

/// A one-package workspace named `aliases` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"aliases\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-ALIAS-CLAUSES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// Runs `krs <command>` on the package's `main` definition: whether it passed, its stdout and
/// its stderr.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "aliases", "--definition", "main"])
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

/// Each case's `krs check` refusal: its `error[..]` headlines with the locations they point at.
fn refusals<const N: usize>(cases: [(&'static str, &str); N]) -> String {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    cases
        .map(|(name, source)| {
            let manifest = package(&temporary.path().join(name), source);
            let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
            assert!(!success, "{name}: {stderr}");
            let directory = format!("{}/", manifest.parent().unwrap().display());
            let lines = stderr
                .lines()
                .map(str::trim)
                .filter(|line| line.starts_with("error") || line.starts_with("--> "))
                .map(|line| line.replace(&directory, ""))
                .collect::<Vec<_>>();
            format!("{name}:\n{}", lines.join("\n"))
        })
        .join("\n")
}

/// `_`, `name @ pattern`, `A | B`, an open record and a list's anonymous rest in an alias
/// clause's subject are refused at the construct, and a name the subject binds and the result
/// does not use at the name, the result's own `let` names apart: printing builds the subject
/// from the bindings of what the result matched, which give none of them a value. On main each
/// printed as a term that does not denote the value: `wild(1, _Krs_Wildcard0:Int)`,
/// `named(green #And red)`, `either(box(1) #Or tag(1))`, `rec(pair(1, _Krs_Wildcard0:Int))`,
/// `lst(ListItem ( 1 ) _Krs_Wildcard0:List)`, `free(1, Y:Int)`.
#[test]
fn a_construct_printing_cannot_build_is_refused_in_an_alias_subject() {
    expect_test::expect![[r"
        wildcard:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and `_` names no term the match gives a value: it prints as a variable (`_Krs_Wildcard0`) where the term stood; name the term and use the name in the result, or write `#[k::desugar]` for an expansion that runs one way; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:46:31
        pattern-alias:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and `name @ pattern` (K's #as) is a test of the term's shape, which building cannot make: it prints as the conjunction `pattern #And term`, no term, and for a term the pattern does not match, as an alias that does not expand back to it; write `#[k::desugar]` for an expansion that runs one way; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:46:29
        alternatives:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and `A | B` (K's #Or) denotes no one term: it prints as the disjunction `A #Or B`; write one alias clause per alternative, each with the result, or `#[k::desugar]` for an expansion that runs one way; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:46:30
        open-record:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and the fields `..` leaves open have no value from that match: they print as variables (`_Krs_Wildcard0`); name every field and use it in the result, or write `#[k::desugar]` for an expansion that runs one way; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:46:27
        anonymous-rest:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and the elements an anonymous `..` leaves unnamed have no value from that match: they print as a variable (`_Krs_Wildcard0`); name the rest, `rest @ ..`, and use it in the result, or write `#[k::desugar]` for an expansion that runs one way; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:46:32
        unused-name:
        error[krs::expand::irreversible-alias]: alias clause `free`: its subject binds `y`, which its result does not use; an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and no match binds `y`, so it would print as a variable where the term stood; use `y` in the result, or write `#[k::desugar]` for an expansion that runs one way
        --> src/lib.rs:46:31
        unused-rest:
        error[krs::expand::irreversible-alias]: alias clause `head`: its subject binds `rest`, which its result does not use; an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and no match binds `rest`, so it would print as a variable where the term stood; use `rest` in the result, or write `#[k::desugar]` for an expansion that runs one way
        --> src/lib.rs:46:32
        shadowed-name:
        error[krs::expand::irreversible-alias]: alias clause `free`: its subject binds `y`, which its result does not use; an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and no match binds `y`, so it would print as a variable where the term stood; use `y` in the result, or write `#[k::desugar]` for an expansion that runs one way
        --> src/lib.rs:46:31"]]
    .assert_eq(&refusals([
        (
            "wildcard",
            "#[k::alias]\nfn wild(k::term![Al::Pairs(x, _)]: Term<Value>) -> Term<Value> {\n    Data::Box(x)\n}\n",
        ),
        (
            "pattern-alias",
            "#[k::alias]\nfn named(k::term![Al::Whole(y @ Data::Red())]: Term<Value>) -> Term<Value> {\n    Data::One(y)\n}\n",
        ),
        (
            "alternatives",
            "#[k::alias]\nfn either(k::term![Al::Whole(Data::Box(x) | Data::Tag(x))]: Term<Value>) -> Term<Value> {\n    Data::Pair(x, x)\n}\n",
        ),
        (
            "open-record",
            "#[k::alias]\nfn rec(k::term![Al::Whole(Data::Pair { a: x, .. })]: Term<Value>) -> Term<Value> {\n    Data::Box(x)\n}\n",
        ),
        (
            "anonymous-rest",
            "#[k::alias]\nfn head(k::term![Al::Items([x, ..])]: Term<Value>) -> Term<Value> {\n    Data::Two(x, [])\n}\n",
        ),
        (
            "unused-name",
            "#[k::alias]\nfn free(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {\n    Data::Box(x)\n}\n",
        ),
        (
            "unused-rest",
            "#[k::alias]\nfn head(k::term![Al::Items([x, rest @ ..])]: Term<Value>) -> Term<Value> {\n    Data::Two(x, [])\n}\n",
        ),
        (
            "shadowed-name",
            "#[k::alias]\nfn free(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {\n    Data::Box({\n        let y = x;\n        y\n    })\n}\n",
        ),
    ]));
}

/// The emitted rules that mention `needle`, one per line.
fn rules(k: &str, needle: &str) -> String {
    k.lines()
        .map(str::trim)
        .filter(|line| line.starts_with("rule ") && line.contains(needle))
        .collect::<Vec<_>>()
        .join("\n")
}

const TWO_WAY: &str = r"
#[k::alias]
fn items(k::term![Al::Items([x, rest @ ..])]: Term<Value>) -> Term<Value> {
    Data::Two(x, rest)
}

#[k::alias]
fn whole(k::term![Al::Whole(a)]: Term<Value>) -> Term<Value> {
    Data::Flag(k::matches!(a, Data::Box(_)))
}

#[k::alias]
fn pairs(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {
    Data::Pair(
        {
            let z = y;
            z
        },
        x + 1,
    )
}

#[k::rule]
fn mk(k::term![Data::Mk(a, b)]: Term<Value>) -> Term<Value> {
    Data::Two(a, [b, b])
}

#[k::rule]
fn probe(k::term![Data::Probe(a)]: Term<Value>) -> Term<Value> {
    Al::Whole(a)
}

#[k::rule]
fn calc(k::term![Data::Calc(a, b)]: Term<Value>) -> Term<Value> {
    Al::Pairs(a, b)
}
";

/// An alias whose subject every result match builds is accepted: a named rest the result uses
/// is the list the match bound, and the result may compute (`k::matches!`, a `let`, an operator).
/// A printed value the result matches prints as the alias: `two(1, [2, 2])` as
/// `items([1, 2, 2])`. A computed result's printed value is evaluated, which holds no application
/// of the clause's generated function, so it prints expanded: `flag(true)`, `pair(5, 5)`. The
/// computing aliases are written in rules, whose `#let` and `:=K` k-rust lowers; a program that
/// writes one meets them unlowered (finding NT-8-1).
#[test]
fn a_two_way_alias_is_accepted_and_prints_backwards() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), TWO_WAY);
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let k = fs::read_to_string(output.join("definition.k")).unwrap();
    let mut printed = Vec::new();
    for program in ["mk(1, 2)", "probe(box(3))", "calc(4, 5)"] {
        let file = manifest.with_file_name("program.txt");
        fs::write(&file, program).unwrap();
        let (_, stdout, stderr) = krs(target.path(), &manifest, "run", &[file.to_str().unwrap()]);
        let state = stdout
            .lines()
            .skip_while(|line| line.trim() != "<k>")
            .skip(1)
            .take_while(|line| line.trim() != "</k>")
            .map(str::trim)
            .collect::<Vec<_>>()
            .join(" ");
        assert!(!state.is_empty(), "{program}: {stdout}\n{stderr}");
        printed.push(format!("{program} => {state}"));
    }
    expect_test::expect![[r"
        rule items ( ListItem(X:KItem) Rest:List ) => two ( X:KItem , Rest:List ) [label(krsRule_DIGEST)]
        rule whole ( A:Value ) => flag ( ( box ( _ ) :=K A:Value ) ) [label(krsRule_DIGEST)]
        rule pairs ( X:Int , Y:Int ) => pair ( ( #let Z:Int = Y:Int #in Z:Int ) , X:Int +Int 1 ) [label(krsRule_DIGEST)]
        mk(1, 2) => items(ListItem ( 1 ) ListItem ( 2 ) ListItem ( 2 )) ~> .K
        probe(box(3)) => flag(true) ~> .K
        calc(4, 5) => pair(5, 5) ~> .K"]]
    .assert_eq(
        &[
            rules(&k, "rule items"),
            rules(&k, "rule whole"),
            rules(&k, "rule pairs"),
        ]
        .iter()
        .map(|rule| {
            rule.split("krsRule_")
                .next()
                .map(|head| format!("{head}krsRule_DIGEST)]"))
                .unwrap_or_default()
        })
        .chain(printed)
        .collect::<Vec<_>>()
        .join("\n"),
    );
}
