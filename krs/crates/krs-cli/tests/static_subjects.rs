//! A desugar's or an alias's subject is matched by static expansion against the terms a program
//! or a rule writes, as they are written, before anything evaluates, so KRS emits it as that
//! match reads it (NT-14):
//! - an alias's or a desugar's application below the subject's root is written expanded, where
//!   the expansion needs no value: its arguments are ground (the one clause of the production
//!   that matches them, by constructors, names and tokens), or the production is not recursive
//!   and has one clause whose parameters are plain names (the arguments take their places). A
//!   program's application is expanded before the clause is tried, so the clause matches the
//!   expansion. A clause that is not recursive applies once on a path, as the expansion that
//!   runs does; an expansion that repeats an application on its path, or grows past a bound,
//!   is refused;
//! - a desugar clause's alternatives `A | B` are one clause per alternative, distributed over
//!   what stands above them, a static application included;
//! - a collection of two or more parts, which static expansion matches in one spelling only, is
//!   refused; the empty collection and one element stay. A map literal is refused as the update
//!   it denotes, the one way KRS writes a map it builds, which even for one entry no term KRS
//!   writes meets as written;
//! - a Bytes token is written in one spelling wherever KRS writes it, the one a program writes.
//!
//! What the expansion would need a value for is refused at the application, and a function's
//! application or a sort test below the root is refused at the construct: there it would stand
//! for its spelling rather than its value. The class tiers run the generated cases; the cases
//! here are those no generated case writes.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Bytes, Int, KSequence, List, Map, Set, set};
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
    #[k::syntax("mk({a})")] Mk { a: Int },
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
    #[k::syntax("lp({a})")] #[k::desugar(recursive)] Lp { a: Int },
    #[k::syntax("gr({a})")] #[k::desugar(recursive)] Gr { a: Int },
    #[k::syntax("pp({a})")] #[k::desugar] Pp { a: Value },
    #[k::syntax("qq({a})")] #[k::desugar] Qq { a: Value },
    #[k::syntax("mw({a})")] #[k::desugar] Mw { a: Map },
    #[k::syntax("sw({a})")] #[k::desugar] Sw { a: Set },
    #[k::syntax("lw({a})")] #[k::desugar] Lw { a: List },
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

#[k::desugar]
fn lp(k::term![Sugar::Lp(0)]: Term<Value>) -> Term<Value> {
    Sugar::Lp(0)
}

#[k::desugar]
fn gr(k::term![Sugar::Gr(0)]: Term<Value>) -> Term<Value> {
    Data::One(Sugar::Gr(0))
}

#[k::desugar]
fn pp(k::term![Sugar::Pp(x)]: Term<Value>) -> Term<Value> {
    Data::One(Sugar::Qq(x))
}

#[k::desugar]
fn qq_red(k::term![Sugar::Qq(Data::Red())]: Term<Value>) -> Term<Value> {
    Sugar::Pp(Data::Tag(0))
}

#[k::desugar]
fn qq_tag(k::term![Sugar::Qq(Data::Tag(0))]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::desugar]
fn mw(k::term![Sugar::Mw(m)]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::desugar]
fn sw(k::term![Sugar::Sw(set::item(1))]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::desugar]
fn lw(k::term![Sugar::Lw([1])]: Term<Value>) -> Term<Value> {
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
    package_with(root, PREAMBLE, source)
}

/// A one-package workspace named `statics` whose library is `preamble` and `source`.
fn package_with(root: &Path, preamble: &str, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{preamble}{source}")).unwrap();
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
    emitted_and_run_with(PREAMBLE, source, programs, "k")
}

/// The emitted K of the package of `preamble` and `source`, and each program's final `cell`
/// under `krs run`.
fn emitted_and_run_with(
    preamble: &str,
    source: &str,
    programs: &[&str],
    cell: &str,
) -> (String, Vec<String>) {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package_with(temporary.path(), preamble, source);
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
            .skip_while(|line| line.trim() != format!("<{cell}>"))
            .skip(1)
            .take_while(|line| line.trim() != format!("</{cell}>"))
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

#[k::desugar]
fn aliased(k::term![Sugar::Pick(Sugar::Twice(n @ Data::Tag(y)), Data::Box(1))]: Term<Value>) -> Term<Value> {
    Data::One(n)
}

#[k::desugar]
fn dropped(k::term![Sugar::Pick(Sugar::First(x, Data::Box(y)), Data::Box(2))]: Term<Value>) -> Term<Value> {
    Data::One(x)
}

#[k::desugar]
fn either_digit(k::term![Sugar::Pick(Sugar::Digit(0 | 1), Data::Box(3))]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::alias]
fn whole_zero(k::term![Al::Whole(Al::Zero())]: Term<Value>) -> Term<Value> {
    Data::Tag(0)
}

#[k::rule]
fn tagged(k::term![Data::Mk(1)]: Term<Value>) -> Term<Value> {
    Data::Tag(0)
}
";

/// A static application below a subject's root is written expanded where the expansion needs no
/// value, and the clause applies to a program that writes the application: a ground one
/// (`nought()` is `red`, and `nest(1)` is `one(red)`, through `nest`'s recursion), and one whose
/// production has a single clause of plain names (`twice(box(y))` is `pair(box(y), box(y))`,
/// whose `y` matches one value twice, and so is `twice(n @ tag(y))`, whose alias and name match
/// one value twice; `first(x, box(y))` drops `box(y)`, whose `y` the clause names nowhere else).
/// Alternatives in an application's arguments are distributed first, `digit(0 | 1)` being
/// `red | box(1)`, a clause each. An alias's subject is expanded too, and prints backwards:
/// `tag(0)` prints as `whole(zero())`, the alias whose expansion it is (`zero()` is `tag(9)`).
#[test]
fn a_static_application_below_a_subject_root_is_written_expanded() {
    let (k, printed) = emitted_and_run(
        &format!("{NEST}{EXPANDED}"),
        &[
            "pick(box(3), nought())",
            "pick(nest(1), tag(4))",
            "pick(twice(box(5)), box(0))",
            "pick(twice(tag(6)), box(1))",
            "pick(first(box(7), box(8)), box(2))",
            "pick(digit(0), box(3))",
            "pick(digit(1), box(3))",
            "mk(1)",
            "whole(zero())",
        ],
    );
    expect_test::expect![[r"
        rule pick ( one ( X:Value ) , box ( 2 ) ) => one ( X:Value ) [label(krsRule_DIGEST)]
        rule pick ( pair ( ( tag ( Y:Int ) #as N:Value ) , ( tag ( Y:Int ) #as N:Value ) ) , box ( 1 ) ) => one ( N:Value ) [label(krsRule_DIGEST)]
        rule whole ( tag ( 9 ) ) => tag ( 0 ) [label(krsRule_DIGEST)]
        rule pick ( red , box ( 3 ) ) => red [label(krsRule_DIGEST)]
        rule pick ( X:Value , red ) => one ( X:Value ) [label(krsRule_DIGEST)]
        rule pick ( one ( red ) , tag ( B:Int ) ) => one ( box ( B:Int ) ) [label(krsRule_DIGEST)]
        rule pick ( box ( 1 ) , box ( 3 ) ) => red [label(krsRule_DIGEST)]
        rule pick ( pair ( box ( Y:Int ) , box ( Y:Int ) ) , box ( 0 ) ) => one ( box ( Y:Int ) ) [label(krsRule_DIGEST)]
        pick(box(3), nought()) => one(box(3)) ~> .K
        pick(nest(1), tag(4)) => one(box(4)) ~> .K
        pick(twice(box(5)), box(0)) => one(box(5)) ~> .K
        pick(twice(tag(6)), box(1)) => one(tag(6)) ~> .K
        pick(first(box(7), box(8)), box(2)) => one(box(7)) ~> .K
        pick(digit(0), box(3)) => red ~> .K
        pick(digit(1), box(3)) => red ~> .K
        mk(1) => whole(zero()) ~> .K
        whole(zero()) => whole(zero()) ~> .K"]].assert_eq(
        &[
            rules(&k, &["pick", "whole"]),
            printed.join("\n"),
        ]
        .join("\n"),
    );
}

/// A token below a subject's root is matched by the value it denotes, as program expansion
/// matches it (NT-22 review M2): `fl(1.50)` is `fl(1.5)`, which its one clause expands to
/// `tag(1)`, so the clause written `pick(fl(1.50), box(9))` is written `pick(tag(1), box(9))`
/// and applies to a program's `fl(1.5)`, `fl(1.50)` and `fl(15e-1)` (the binary32 `fl(1.5f)`
/// is another value, which no clause matches); `digit(01)` is `digit(1)`.
#[test]
fn a_token_below_a_subject_root_is_matched_by_its_value() {
    let source = r#"
#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Fl {
    #[k::syntax("fl({a})")] #[k::desugar] Fl { a: k::builtin::Float },
}

#[k::desugar]
fn fl_one(k::term![Fl::Fl(1.5)]: Term<Value>) -> Term<Value> {
    Data::Tag(1)
}

#[k::desugar]
fn spelled(k::term![Sugar::Pick(Fl::Fl(1.50), Data::Box(9))]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::desugar]
fn padded(k::term![Sugar::Pick(Sugar::Digit(01), Data::Box(8))]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::alias]
fn whole(k::term![Al::Whole(a)]: Term<Value>) -> Term<Value> {
    Data::One(a)
}
"#;
    let (k, printed) = emitted_and_run(
        &format!("{NEST}{source}"),
        &[
            "pick(fl(1.5), box(9))",
            "pick(fl(1.50), box(9))",
            "pick(fl(15e-1), box(9))",
            "pick(digit(1), box(8))",
        ],
    );
    expect_test::expect![[r"
        rule pick ( box ( 1 ) , box ( 8 ) ) => red [label(krsRule_DIGEST)]
        rule pick ( tag ( 1 ) , box ( 9 ) ) => red [label(krsRule_DIGEST)]
        rule fl ( 1.5 ) => tag ( 1 ) [label(krsRule_DIGEST)]
        pick(fl(1.5), box(9)) => red ~> .K
        pick(fl(1.50), box(9)) => red ~> .K
        pick(fl(15e-1), box(9)) => red ~> .K
        pick(digit(1), box(8)) => red ~> .K"]]
    .assert_eq(&[rules(&k, &["pick", "fl"]), printed.join("\n")].join("\n"));
}

/// An alias whose subject holds a literal prints back only the terms its clause's result matches
/// with that literal (NT-14-1): with `whole(box(1)) => tag(1)` and `whole(box(2)) => tag(2)`,
/// `tag(1)` and `tag(2)` print as their own clause's subject, and `tag(3)`, which no clause
/// matches, prints as it is, never as `whole(box(1 #And 3))`. The clauses are written without a
/// static application, so only the printer decides it.
#[test]
fn an_alias_whose_subject_holds_a_literal_prints_only_what_it_matches() {
    let (_, printed) = emitted_and_run(
        &format!(
            "{NEST}{OTHER_CLAUSES}#[k::alias]\nfn whole_one(k::term![Al::Whole(Data::Box(1))]: Term<Value>) -> Term<Value> {{\n    Data::Tag(1)\n}}\n\n#[k::alias]\nfn whole_two(k::term![Al::Whole(Data::Box(2))]: Term<Value>) -> Term<Value> {{\n    Data::Tag(2)\n}}\n"
        ),
        &["tag(1)", "tag(2)", "tag(3)"],
    );
    assert_eq!(
        printed,
        [
            "tag(1) => whole(box(1)) ~> .K",
            "tag(2) => whole(box(2)) ~> .K",
            "tag(3) => tag(3) ~> .K"
        ]
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

/// The definition `BYTES` holds a desugar of a Bytes token and a rule, an equation and an
/// initializer that each write its application: every Bytes token KRS writes has one spelling,
/// so each term meets the subject, as kompile expands it.
const BYTES: &str = r#"
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
    #[k::syntax("one({a})")] One { a: Value },
    #[k::syntax("mk({a})")] Mk { a: Int },
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Sugar {
    #[k::syntax("bz({a})")] #[k::desugar] Bz { a: Bytes },
}

#[k::function(partial, sort = Value, syntax = "made({a})")]
pub struct Made {
    pub a: Term<Int>,
}

#[k::desugar]
fn bz(k::term![Sugar::Bz(k::bytes!(b"a\"\\\n\x0c'\x00\xff"))]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::equation]
fn made(k::term![Made(0)]: Term<Value>) -> Term<Value> {
    Sugar::Bz(k::bytes!(b"a\"\\\n\x0c'\x00\xff"))
}

#[k::rule]
fn by_rule(k::term![Data::Mk(0)]: Term<Value>) -> Term<Value> {
    Sugar::Bz(k::bytes!(b"a\"\\\n\x0c'\x00\xff"))
}

#[k::rule]
fn by_equation(k::term![Data::Mk(1)]: Term<Value>) -> Term<Value> {
    Data::One(Made(0))
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub seen: Value,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Value) -> Self {
        Self {
            k: k::k![pgm],
            seen: Sugar::Bz(k::bytes!(b"a\"\\\n\x0c'\x00\xff")),
        }
    }
}
"#;

/// A Bytes token is written in one spelling wherever KRS writes it, which a program writes too
/// (`b"a\x22\\\n\f'\x00\xff"`: `krs run`'s, but for `"`, which emitted K's `#token` cannot carry as
/// `\"`), so a static subject KRS writes meets the terms a rule, an equation and an initializer
/// write, and a program's own spelling. A program writing the same bytes with other escapes
/// (`b"\x61\x22.."`) is the same term, which the clause expands too: static expansion matches a
/// token by its value (finding NT-14-2).
#[test]
fn a_bytes_token_is_written_in_one_spelling() {
    let (k, printed) = emitted_and_run_with(
        BYTES,
        "",
        &[
            "mk(0)",
            "mk(1)",
            "bz(b\"a\\x22\\\\\\n\\f'\\x00\\xff\")",
            r#"bz(b"\x61\x22\x5c\x0a\x0c\x27\x00\xFF")"#,
        ],
        "k",
    );
    let (_, seen) = emitted_and_run_with(BYTES, "", &["mk(0)"], "seen");
    expect_test::expect![[r#"
        rule bz ( b"a\x22\\\n\f'\x00\xff" ) => red [label(krsRule_DIGEST)]
        mk(0) => red ~> .K
        mk(1) => one(red) ~> .K
        bz(b"a\x22\\\n\f'\x00\xff") => red ~> .K
        bz(b"\x61\x22\x5c\x0a\x0c\x27\x00\xFF") => red ~> .K
        mk(0) => red"#]]
    .assert_eq(&[rules(&k, &["bz"]), printed.join("\n"), seen.join("\n")].join("\n"));
}

/// What an expansion needs a value for is refused at the application, with why: the arguments
/// are not ground and the production is recursive, has two clauses, or has a clause whose
/// parameter is no plain name; the clause drops an argument that binds a name the clause uses
/// elsewhere, or copies one holding `_`; its result computes; no clause matches ground
/// arguments; a clause that is not recursive would apply again on its own path; the expansion
/// repeats an application on its path, at the root or below it; in an alias's subject as in a
/// desugar's. A function's application, a map literal (the update it denotes) and a sort test
/// below a static subject's root would stand for their spelling there, and are refused at the
/// construct, as a collection of two or more parts is.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of the refusals, each case a line, and their pinned messages."
)]
fn what_a_static_subject_cannot_mean_is_refused() {
    let clause = |name: &str, subject: &str| {
        format!(
            "{NEST}{OTHER_CLAUSES}#[k::desugar]\nfn {name}(k::term![Sugar::Pick({subject}, Data::Red())]: Term<Value>) -> Term<Value> {{\n    Data::Red()\n}}\n"
        )
    };
    let alias = |name: &str, subject: &str| {
        format!(
            "{NEST}{OTHER_CLAUSES}#[k::alias]\nfn {name}(k::term![Al::Whole({subject})]: Term<Value>) -> Term<Value> {{\n    Data::Box(x)\n}}\n"
        )
    };
    let recursive = clause("recursive", "Sugar::Nest(x)");
    let clauses = clause("clauses", "Sugar::Digit(x)");
    let pattern = clause("pattern", "Sugar::Unbox(x)");
    let drops = format!(
        "{NEST}{OTHER_CLAUSES}#[k::desugar]\nfn drops(k::term![Sugar::Pick(Sugar::First(x, Data::Box(y)), Data::Box(y))]: Term<Value>) -> Term<Value> {{\n    Data::Red()\n}}\n"
    );
    let copies = clause("copies", "Sugar::Twice(Data::Box(_))");
    let computes = clause("computes", "Sugar::Succ(x)");
    let unmatched = clause("unmatched", "Sugar::Digit(2)");
    let blocked = clause("blocked", "Sugar::Pp(Data::Red())");
    let loops = clause("loops", "Sugar::Lp(0)");
    let grows = clause("grows", "Sugar::Gr(0)");
    let set = clause(
        "set",
        "Data::One(Sugar::Sw(set::concat(set::item(1), set::item(2))))",
    );
    let list = clause("list", "Data::One(Sugar::Lw([1, 2]))");
    let map = clause("map", "Data::One(Sugar::Mw(map![1 -> 2]))");
    let function = clause("function", "Data::One(Size(x))");
    let sort_test = clause("sort_test", "k::is!(Int, x)");
    let in_alias = alias("whole_digit", "Sugar::Digit(x)");
    let alias_function = alias("whole_size", "Data::Box(Size(x))");
    expect_test::expect![[r"
        recursive:
        error[krs::analysis::invalid-static-clause]: desugar clause `recursive`: `Sugar::Nest` is marked `#[k::desugar]`, so a program's `Sugar::Nest` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but these arguments are not ground, and `Sugar::Nest` is recursive, so its expansion depends on the values a program gives them: write one clause for each clause of `Sugar::Nest` instead, each with that clause's arguments and its expansion written out
        --> src/lib.rs:180:35
        clauses:
        error[krs::analysis::invalid-static-clause]: desugar clause `clauses`: `Sugar::Digit` is marked `#[k::desugar]`, so a program's `Sugar::Digit` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but these arguments are not ground, and `Sugar::Digit` has 2 clauses, so which one expands it depends on the values a program gives them: write one clause for each clause of `Sugar::Digit` instead, each with that clause's arguments and its expansion written out
        --> src/lib.rs:180:33
        pattern:
        error[krs::analysis::invalid-static-clause]: desugar clause `pattern`: `Sugar::Unbox` is marked `#[k::desugar]`, so a program's `Sugar::Unbox` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but these arguments are not ground, and the parameters of `Sugar::Unbox`'s clause are not distinct plain names of its argument sorts, so whether the clause applies depends on the values a program gives them: write one clause for each clause of `Sugar::Unbox` instead, each with that clause's arguments and its expansion written out
        --> src/lib.rs:180:33
        drops:
        error[krs::analysis::invalid-static-clause]: desugar clause `drops`: `Sugar::First` is marked `#[k::desugar]`, so a program's `Sugar::First` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but its clause drops argument 2, which binds `y` here, a name this clause uses elsewhere, which would have no value: write the term it expands to instead
        --> src/lib.rs:180:31
        copies:
        error[krs::analysis::invalid-static-clause]: desugar clause `copies`: `Sugar::Twice` is marked `#[k::desugar]`, so a program's `Sugar::Twice` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but its clause copies argument 1, which here holds a pattern that matches more than one term apart from its names (`_`, `A | B`), so each copy would match a term of its own: write the term it expands to instead
        --> src/lib.rs:180:32
        computes:
        error[krs::analysis::invalid-static-clause]: desugar clause `computes`: `Sugar::Succ` is marked `#[k::desugar]`, so a program's `Sugar::Succ` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but its clause expands it to a term that computes (a builtin function's application), which this subject would match as written: write the term it expands to instead
        --> src/lib.rs:180:34
        unmatched:
        error[krs::analysis::invalid-static-clause]: desugar clause `unmatched`: `Sugar::Digit` is marked `#[k::desugar]`, so a program's `Sugar::Digit` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but no clause of `Sugar::Digit` matches these arguments, so a program's application stays unexpanded and this clause never applies: write arguments a clause of `Sugar::Digit` matches
        --> src/lib.rs:180:35
        blocked:
        error[krs::analysis::invalid-static-clause]: desugar clause `blocked`: `Sugar::Pp` is marked `#[k::desugar]`, so a program's `Sugar::Pp` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but the clause of `Sugar::Pp` that matches it, `pp`, already rewrote an application this one stands in, and `Sugar::Pp` is not recursive, so a program's expansion leaves this application unexpanded and this clause never applies: write the term it expands to instead
        --> src/lib.rs:180:33
        loops:
        error[krs::analysis::invalid-static-clause]: desugar clause `loops`: `Sugar::Lp` is marked `#[k::desugar]`, so a program's `Sugar::Lp` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but its expansion writes this very application again on its own path, so it never ends: write the term it expands to instead
        --> src/lib.rs:180:31
        grows:
        error[krs::analysis::invalid-static-clause]: desugar clause `grows`: `Sugar::Gr` is marked `#[k::desugar]`, so a program's `Sugar::Gr` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but its expansion writes this very application again on its own path, so it never ends: write the term it expands to instead
        --> src/lib.rs:180:31
        set:
        error[krs::analysis::collection-in-static-subject]: desugar clause `set`: a set of two or more parts matches only one way of writing it: static expansion matches a program's terms as they are written, before anything evaluates, and does not reorder a set's elements or a map's entries or regroup a list's parts, so the clause would rewrite one spelling of the collection and not the others (`[1, 2, 3]` but not `list::concat([1, 2], [3])`); the empty collection and one element or entry have one spelling: write the parts as a constructor's arguments, or rewrite the collection with a rule
        --> src/lib.rs:180:49
        list:
        error[krs::analysis::collection-in-static-subject]: desugar clause `list`: a list of two or more parts matches only one way of writing it: static expansion matches a program's terms as they are written, before anything evaluates, and does not reorder a set's elements or a map's entries or regroup a list's parts, so the clause would rewrite one spelling of the collection and not the others (`[1, 2, 3]` but not `list::concat([1, 2], [3])`); the empty collection and one element or entry have one spelling: write the parts as a constructor's arguments, or rewrite the collection with a rule
        --> src/lib.rs:180:51
        map:
        error[krs::analysis::function-in-pattern]: the builtin function `k::builtin::map::update`, which a map literal `map![k -> v, ..]` denotes, stands in the subject of a desugar clause, which static expansion matches against a program's terms as they are written, before anything evaluates: there an application stands for its own spelling, not for the value it denotes everywhere else (`f(x + 1)` would expand the program `f(y + 1)` but not `f(1 + y)`), so the clause would rewrite some spellings of a value and not others: to rewrite a computation, write a rule (`#[k::rule]`) or the function's equation (`#[k::equation]`); to expand a term a program writes, write it with constructors
        --> src/lib.rs:180:49
        function:
        error[krs::analysis::function-in-pattern]: the function `Size` stands in the subject of a desugar clause, which static expansion matches against a program's terms as they are written, before anything evaluates: there an application stands for its own spelling, not for the value it denotes everywhere else (`f(x + 1)` would expand the program `f(y + 1)` but not `f(1 + y)`), so the clause would rewrite some spellings of a value and not others: to rewrite a computation, write a rule (`#[k::rule]`) or the function's equation (`#[k::equation]`); to expand a term a program writes, write it with constructors
        --> src/lib.rs:180:44
        sort-test:
        error[krs::analysis::invalid-sort-test]: `k::is!` and `k::project!` compute from a term, and a pattern matches terms as they are: restrict a binder's sort with a typed parameter or `where x: Sort` instead; here it stands in the subject of a `#[k::desugar]` clause
        --> src/lib.rs:180:35
        alias:
        error[krs::analysis::invalid-static-clause]: alias clause `whole_digit`: `Sugar::Digit` is marked `#[k::desugar]`, so a program's `Sugar::Digit` is expanded before this clause is tried, and the clause matches its expansion, which KRS writes here where it needs no value; but these arguments are not ground, and `Sugar::Digit` has 2 clauses, so which one expands it depends on the values a program gives them: write one clause for each clause of `Sugar::Digit` instead, each with that clause's arguments and its expansion written out
        --> src/lib.rs:180:35
        alias-function:
        error[krs::analysis::function-in-pattern]: the function `Size` stands in the subject of an alias clause, which static expansion matches against a program's terms as they are written, before anything evaluates: there an application stands for its own spelling, not for the value it denotes everywhere else (`f(x + 1)` would expand the program `f(y + 1)` but not `f(1 + y)`), so the clause would rewrite some spellings of a value and not others: to rewrite a computation, write a rule (`#[k::rule]`) or the function's equation (`#[k::equation]`); to expand a term a program writes, write it with constructors
        --> src/lib.rs:180:44"]].assert_eq(&refusals([
        ("recursive", recursive.as_str()),
        ("clauses", clauses.as_str()),
        ("pattern", pattern.as_str()),
        ("drops", drops.as_str()),
        ("copies", copies.as_str()),
        ("computes", computes.as_str()),
        ("unmatched", unmatched.as_str()),
        ("blocked", blocked.as_str()),
        ("loops", loops.as_str()),
        ("grows", grows.as_str()),
        ("set", set.as_str()),
        ("list", list.as_str()),
        ("map", map.as_str()),
        ("function", function.as_str()),
        ("sort-test", sort_test.as_str()),
        ("alias", in_alias.as_str()),
        ("alias-function", alias_function.as_str()),
    ]));
}
