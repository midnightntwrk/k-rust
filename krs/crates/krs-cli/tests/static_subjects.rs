//! A desugar's or an alias's subject is matched by static expansion against a program's terms as
//! they are written, before anything evaluates, so KRS emits it as that match reads it (NT-14):
//! - an alias's or a desugar's application below the subject's root is written expanded, where
//!   the expansion needs no value: its arguments are ground (each clause of the production is
//!   matched against them), or the production is not recursive and has one clause whose
//!   parameters are plain names (the arguments take their places). A program's application is
//!   expanded before the clause is tried, so the clause matches the expansion;
//! - a desugar clause's alternatives `A | B` are one clause per alternative, which static
//!   expansion matches, where it does not match an or-pattern;
//! - a Bytes token is written as a program writes it.
//!
//! What the expansion would need a value for is refused at the application, and a function's
//! application or a sort test below the root is refused at the construct: there it would stand
//! for its spelling rather than its value. The class tiers show the ground, one-clause case
//! (`Cmd::Dz()`, `Cmd::Az()`), a Bytes token and a desugar's alternatives, each run by K7; the
//! cases here are those no generated case writes.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Bytes, Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Data {
    #[k::syntax("red")] Red(),
    #[k::syntax("box({a})")] Box { a: Int },
    #[k::syntax("tag({a})")] Tag { a: Int },
    #[k::syntax("pair({a}, {b})")] Pair { a: Value, b: Value },
    #[k::syntax("one({a})")] One { a: Value },
}

#[k::function(partial, sort = Int, syntax = "size({a})")]
pub struct Size {
    pub a: Term<Value>,
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Sugar {
    #[k::syntax("nought()")] #[k::desugar] Nought(),
    #[k::syntax("twice({a})")] #[k::desugar] Twice { a: Value },
    #[k::syntax("digit({a})")] #[k::desugar] Digit { a: Int },
    #[k::syntax("nest({a})")] #[k::desugar(recursive)] Nest { a: Int },
    #[k::syntax("first({a}, {b})")] #[k::desugar] First { a: Value, b: Value },
    #[k::syntax("succ({a})")] #[k::desugar] Succ { a: Int },
    #[k::syntax("pick({a}, {b})")] #[k::desugar] Pick { a: Value, b: Value },
    #[k::syntax("unbox({a})")] #[k::desugar] Unbox { a: Value },
    #[k::syntax("alt({a}, {b})")] #[k::desugar] Alt { a: Value, b: Value },
    #[k::syntax("bz({a})")] #[k::desugar] Bz { a: Bytes },
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Al {
    #[k::syntax("zero()")] #[k::alias] Zero(),
    #[k::syntax("whole({a})")] #[k::alias] Whole { a: Value },
}

#[k::desugar]
fn nought(k::term![Sugar::Nought()]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::desugar]
fn twice(k::term![Sugar::Twice(a)]: Term<Value>) -> Term<Value> {
    Data::Pair(a, a)
}

#[k::desugar]
fn digit_zero(k::term![Sugar::Digit(0)]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::desugar]
fn digit_one(k::term![Sugar::Digit(1)]: Term<Value>) -> Term<Value> {
    Data::Box(1)
}

#[k::desugar]
fn first(k::term![Sugar::First(a, b)]: Term<Value>) -> Term<Value> {
    Data::One(a)
}

#[k::desugar]
fn succ(k::term![Sugar::Succ(a)]: Term<Value>) -> Term<Value> {
    Data::Box(a + 1)
}

#[k::desugar]
fn unbox(k::term![Sugar::Unbox(Data::Box(a))]: Term<Value>) -> Term<Value> {
    Data::Tag(a)
}

#[k::desugar]
fn either(
    k::term![Sugar::Alt(z @ (Data::Box(x) | Data::Tag(x)), Data::Red())]: Term<Value>,
) -> Term<Value> {
    Data::Pair(z, Data::One(Data::Box(x)))
}

#[k::desugar]
fn bz(k::term![Sugar::Bz(k::bytes!(b"a\"\n"))]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::alias]
fn zero(k::term![Al::Zero()]: Term<Value>) -> Term<Value> {
    Data::Tag(9)
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

/// `Sugar::Nest`'s clauses: it counts down to `red`.
const NEST: &str = "#[k::desugar]\nfn nest_zero(k::term![Sugar::Nest(0)]: Term<Value>) -> Term<Value> {\n    Data::Red()\n}\n\n#[k::desugar]\nfn nest_one(k::term![Sugar::Nest(1)]: Term<Value>) -> Term<Value> {\n    Data::One(Sugar::Nest(0))\n}\n\n";

/// The clauses of the productions the preamble leaves without one.
const OTHER_CLAUSES: &str = "#[k::alias]\nfn whole(k::term![Al::Whole(a)]: Term<Value>) -> Term<Value> {\n    Data::Pair(Data::Red(), a)\n}\n\n#[k::desugar]\nfn picks(k::term![Sugar::Pick(a, b)]: Term<Value>) -> Term<Value> {\n    Data::Pair(a, b)\n}\n\n";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `statics` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"statics\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-STATIC-SUBJECTS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .args(["--package", "statics", "--definition", "main"])
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

/// The emitted rules of `k` that start with `rule NAME`, one per line, their generated label
/// digests written `DIGEST`.
fn rules(k: &str, names: &[&str]) -> String {
    k.lines()
        .map(str::trim)
        .filter(|line| {
            names
                .iter()
                .any(|name| line.starts_with(&format!("rule {name} ")))
        })
        .map(|rule| {
            rule.split("krsRule_")
                .next()
                .map(|head| format!("{head}krsRule_DIGEST)]"))
                .unwrap_or_default()
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The package's emitted K and each program's final computation under `krs run`.
fn emitted_and_run(source: &str, programs: &[&str]) -> (String, Vec<String>) {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), source);
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
    for program in programs {
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
    (k, printed)
}

const EXPANDED: &str = "#[k::desugar]
fn ground(k::term![Sugar::Pick(x, Sugar::Nought())]: Term<Value>) -> Term<Value> {
    Data::One(x)
}

#[k::desugar]
fn recursive(k::term![Sugar::Pick(Sugar::Nest(1), Data::Tag(b))]: Term<Value>) -> Term<Value> {
    Data::One(Data::Box(b))
}

#[k::desugar]
fn named(k::term![Sugar::Pick(Sugar::Twice(Data::Box(y)), Data::Box(0))]: Term<Value>) -> Term<Value> {
    Data::One(Data::Box(y))
}

#[k::alias]
fn whole(k::term![Al::Whole(Sugar::Digit(1))]: Term<Value>) -> Term<Value> {
    Data::Tag(1)
}

#[k::alias]
fn whole_zero(k::term![Al::Whole(Al::Zero())]: Term<Value>) -> Term<Value> {
    Data::Tag(0)
}

#[k::alias]
fn whole_two(k::term![Al::Whole(Data::Box(2))]: Term<Value>) -> Term<Value> {
    Data::Tag(2)
}

#[k::rule]
fn tagged(k::term![Data::Tag(a)]: Term<Value>) -> Term<Value> {
    Data::One(Data::Tag(a))
}
";

/// A static application below a subject's root is written expanded where the expansion needs no
/// value, and the clause applies to a program that writes the application: a ground one
/// (`nought()` is `red`; `digit(1)` is `box(1)`, the one of `digit`'s two clauses that matches
/// `1`, and `nest(1)` is `one(red)`, through `nest`'s recursion), and one whose production has a
/// single clause of plain names (`twice(box(y))` is `pair(box(y), box(y))`, whose `y` matches
/// one value twice). An alias's subject is expanded too, and prints backwards: `tag(0)` prints
/// as `whole(zero())`, the alias whose expansion it is (`zero()` is `tag(9)`). An alias whose
/// subject holds a literal prints a conjunction of the literals of every such alias of its
/// production (`tag(1)` as `whole(box(1 #And 2))`): finding NT-14-1, the printer's, which
/// `whole_two`, written without a static application, shows as well.
#[test]
fn a_static_application_below_a_subject_root_is_written_expanded() {
    let (k, printed) = emitted_and_run(
        &format!("{NEST}{EXPANDED}"),
        &[
            "pick(box(3), nought())",
            "pick(nest(1), tag(4))",
            "pick(twice(box(5)), box(0))",
            "whole(digit(1))",
            "tag(1)",
            "tag(2)",
            "whole(zero())",
        ],
    );
    expect_test::expect![[r"
        rule whole ( box ( 1 ) ) => tag ( 1 ) [label(krsRule_DIGEST)]
        rule whole ( box ( 2 ) ) => tag ( 2 ) [label(krsRule_DIGEST)]
        rule whole ( tag ( 9 ) ) => tag ( 0 ) [label(krsRule_DIGEST)]
        rule pick ( X:Value , red ) => one ( X:Value ) [label(krsRule_DIGEST)]
        rule pick ( one ( red ) , tag ( B:Int ) ) => one ( box ( B:Int ) ) [label(krsRule_DIGEST)]
        rule pick ( pair ( box ( Y:Int ) , box ( Y:Int ) ) , box ( 0 ) ) => one ( box ( Y:Int ) ) [label(krsRule_DIGEST)]
        pick(box(3), nought()) => one(box(3)) ~> .K
        pick(nest(1), tag(4)) => one(box(4)) ~> .K
        pick(twice(box(5)), box(0)) => one(box(5)) ~> .K
        whole(digit(1)) => one(whole(box(1 #And 2))) ~> .K
        tag(1) => one(whole(box(1 #And 2))) ~> .K
        tag(2) => one(whole(box(2 #And 2))) ~> .K
        whole(zero()) => one(whole(zero())) ~> .K"]].assert_eq(
        &[
            rules(&k, &["pick", "whole"]),
            printed.join("\n"),
        ]
        .join("\n"),
    );
}

/// A desugar clause's alternatives are one clause per alternative, each applying to a program
/// that writes it, through an alias's name too.
#[test]
fn a_desugar_subject_alternatives_are_one_clause_each() {
    let (k, printed) = emitted_and_run(
        &format!("{NEST}{OTHER_CLAUSES}"),
        &["alt(box(1), red)", "alt(tag(2), red)"],
    );
    expect_test::expect![[r"
        rule alt ( ( tag ( X:Int ) #as Z:Value ) , red ) => pair ( Z:Value , one ( box ( X:Int ) ) ) [label(krsRule_DIGEST)]
        rule alt ( ( box ( X:Int ) #as Z:Value ) , red ) => pair ( Z:Value , one ( box ( X:Int ) ) ) [label(krsRule_DIGEST)]
        alt(box(1), red) => pair(box(1), one(box(1))) ~> .K
        alt(tag(2), red) => pair(tag(2), one(box(2))) ~> .K"]]
        .assert_eq(&[rules(&k, &["alt"]), printed.join("\n")].join("\n"));
}

/// A Bytes token in a static subject is written as a program writes it, `b"a\"\n"`, where the
/// transport spelling is `b"\x61\x22\x0a"`, so the clause applies to a program writing it.
#[test]
fn a_bytes_token_in_a_static_subject_is_written_as_a_program_writes_it() {
    let (k, printed) = emitted_and_run(&format!("{NEST}{OTHER_CLAUSES}"), &["bz(b\"a\\\"\\n\")"]);
    expect_test::expect![[r#"
        rule bz ( b"a\"\n" ) => red [label(krsRule_DIGEST)]
        bz(b"a\"\n") => red ~> .K"#]]
    .assert_eq(&[rules(&k, &["bz"]), printed.join("\n")].join("\n"));
}

/// What an expansion needs a value for is refused at the application, with why: the arguments
/// are not ground and the production is recursive, has two clauses, or has a clause whose
/// parameter is no plain name; the clause drops an argument that binds a name, or copies one
/// that is a pattern; its result computes; no clause matches ground arguments; in an alias's
/// subject as in a desugar's. A function's application and a sort test below a static subject's
/// root would stand for their spelling there, and are refused at the construct.
#[test]
fn what_a_static_subject_cannot_mean_is_refused() {
    let clause = |name: &str, subject: &str| {
        format!(
            "{NEST}{OTHER_CLAUSES}#[k::desugar]\nfn {name}(k::term![Sugar::Pick({subject}, Data::Red())]: Term<Value>) -> Term<Value> {{\n    Data::Red()\n}}\n"
        )
    };
    let recursive = clause("recursive", "Sugar::Nest(x)");
    let clauses = clause("clauses", "Sugar::Digit(x)");
    let pattern = clause("pattern", "Sugar::Unbox(x)");
    let drops = clause("drops", "Sugar::First(x, Data::Box(y))");
    let copies = clause("copies", "Sugar::Twice(Data::Box(_))");
    let computes = clause("computes", "Sugar::Succ(x)");
    let unmatched = clause("unmatched", "Sugar::Digit(2)");
    let function = clause("function", "Data::One(Size(x))");
    let sort_test = clause("sort_test", "k::is!(Int, x)");
    let alias = format!(
        "{NEST}{OTHER_CLAUSES}#[k::alias]\nfn whole_digit(k::term![Al::Whole(Sugar::Digit(x))]: Term<Value>) -> Term<Value> {{\n    Data::Box(x)\n}}\n"
    );
    let alias_function = format!(
        "{NEST}{OTHER_CLAUSES}#[k::alias]\nfn whole_size(k::term![Al::Whole(Data::Box(Size(x)))]: Term<Value>) -> Term<Value> {{\n    Data::One(x)\n}}\n"
    );
    expect_test::expect![[r"
        recursive:
        error[krs::analysis::invalid-static-clause]: desugar clause `recursive`: `Sugar::Nest` is marked `#[k::desugar]`, so a program's `Sugar::Nest` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but these arguments are not ground, and `Sugar::Nest` is recursive, so its expansion depends on the values a program gives them: write the term it expands to instead
        --> src/lib.rs:132:35
        clauses:
        error[krs::analysis::invalid-static-clause]: desugar clause `clauses`: `Sugar::Digit` is marked `#[k::desugar]`, so a program's `Sugar::Digit` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but these arguments are not ground, and `Sugar::Digit` has 2 clauses, so which one expands it depends on the values a program gives them: write the term it expands to instead
        --> src/lib.rs:132:33
        pattern:
        error[krs::analysis::invalid-static-clause]: desugar clause `pattern`: `Sugar::Unbox` is marked `#[k::desugar]`, so a program's `Sugar::Unbox` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but these arguments are not ground, and the parameters of `Sugar::Unbox`'s clause are not distinct plain names of its argument sorts, so whether the clause applies depends on the values a program gives them: write the term it expands to instead
        --> src/lib.rs:132:33
        drops:
        error[krs::analysis::invalid-static-clause]: desugar clause `drops`: `Sugar::First` is marked `#[k::desugar]`, so a program's `Sugar::First` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but its clause drops argument 2, which binds `y` here, so `y` would have no value: write the term it expands to instead
        --> src/lib.rs:132:31
        copies:
        error[krs::analysis::invalid-static-clause]: desugar clause `copies`: `Sugar::Twice` is marked `#[k::desugar]`, so a program's `Sugar::Twice` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but its clause copies argument 1, which here holds a pattern that matches more than one term apart from its names (`_`, `A | B`, `name @ P`), so each copy would match a term of its own: write the term it expands to instead
        --> src/lib.rs:132:32
        computes:
        error[krs::analysis::invalid-static-clause]: desugar clause `computes`: `Sugar::Succ` is marked `#[k::desugar]`, so a program's `Sugar::Succ` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but its clause expands it to a term that computes (a builtin function's application), which this subject would match as written: write the term it expands to instead
        --> src/lib.rs:132:34
        unmatched:
        error[krs::analysis::invalid-static-clause]: desugar clause `unmatched`: `Sugar::Digit` is marked `#[k::desugar]`, so a program's `Sugar::Digit` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but no clause of `Sugar::Digit` matches these arguments, so a program's application stays unexpanded and this clause never applies: write the term it expands to instead
        --> src/lib.rs:132:35
        function:
        error[krs::analysis::function-in-pattern]: the function `Size` stands in the subject of a desugar clause, which static expansion matches against a program's terms as they are written, before anything evaluates: there an application stands for its own spelling, not for the value it denotes everywhere else (`f(x + 1)` would expand the program `f(y + 1)` but not `f(1 + y)`), so the clause would rewrite some spellings of a value and not others: to rewrite a computation, write a rule (`#[k::rule]`) or the function's equation (`#[k::equation]`); to expand a term a program writes, write it with constructors
        --> src/lib.rs:132:44
        sort-test:
        error[krs::analysis::invalid-sort-test]: `k::is!` and `k::project!` compute from a term, and a pattern matches terms as they are: restrict a binder's sort with a typed parameter or `where x: Sort` instead; here it stands in the subject of a `#[k::desugar]` clause
        --> src/lib.rs:132:35
        alias:
        error[krs::analysis::invalid-static-clause]: alias clause `whole_digit`: `Sugar::Digit` is marked `#[k::desugar]`, so a program's `Sugar::Digit` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but these arguments are not ground, and `Sugar::Digit` has 2 clauses, so which one expands it depends on the values a program gives them: write the term it expands to instead
        --> src/lib.rs:132:35
        alias-function:
        error[krs::analysis::function-in-pattern]: the function `Size` stands in the subject of an alias clause, which static expansion matches against a program's terms as they are written, before anything evaluates: there an application stands for its own spelling, not for the value it denotes everywhere else (`f(x + 1)` would expand the program `f(y + 1)` but not `f(1 + y)`), so the clause would rewrite some spellings of a value and not others: to rewrite a computation, write a rule (`#[k::rule]`) or the function's equation (`#[k::equation]`); to expand a term a program writes, write it with constructors
        --> src/lib.rs:132:44"]].assert_eq(&refusals([
        ("recursive", recursive.as_str()),
        ("clauses", clauses.as_str()),
        ("pattern", pattern.as_str()),
        ("drops", drops.as_str()),
        ("copies", copies.as_str()),
        ("computes", computes.as_str()),
        ("unmatched", unmatched.as_str()),
        ("function", function.as_str()),
        ("sort-test", sort_test.as_str()),
        ("alias", alias.as_str()),
        ("alias-function", alias_function.as_str()),
    ]));
}
