//! A user list prints in its program spelling: its elements with its separator, and the empty
//! list as no text, which is how a program writes it and how the grammar reads it back. K's
//! spelling of the terminator (`.Ints`) is rule syntax, which no program grammar reads, so where
//! no text writes an empty list (a `NeList`'s, one beside another list's text, or a list's one
//! element, whose text would be the enclosing list's empty one too) the print falls back to it and
//! says so.
//!
//! One package declares a list per shape the grammar tests use: `Ints` (`,`), the `NeList`
//! `Alts` (`|`), `Gaps` (no separator) and `Rows`, a list of `Ints` (`;`), each at an argument
//! of a call form, beside one at the end of a production (`tail`) and two side by side (`two`),
//! and the recursive alias `nest`, whose clauses write the list. Each program is printed by
//! `krs parse --output program` (the program grammar's text) and by `krs run` (a configuration
//! value's); rules build the terms no text writes. Every command runs with
//! `KRS_CHECK_PRINTS=1` ([`krs_test_support::CHECK_PRINTS`]), so each print that claims to be
//! the term is read back as it.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const LIBRARY: &str = r#"use k::builtin::{Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Stmt: KResult;
}

/// `1, 2, 3`.
#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil(),
}

/// `1 | 2`, never empty.
#[k::syntax_list(separator = "|", non_empty)]
pub enum Alts {
    Cons { head: Int, tail: Alts },
    Nil(),
}

/// `1 2 3`, juxtaposed.
#[k::syntax_list(separator = "")]
pub enum Gaps {
    Cons { head: Int, tail: Gaps },
    Nil(),
}

/// `1, 2; 3`: a list of lists.
#[k::syntax_list(separator = ";")]
pub enum Rows {
    Cons { head: Ints, tail: Rows },
    Nil(),
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Program {
    #[k::syntax("ints({items})")] IntsStmt { items: Ints },
    #[k::syntax("alts({items})")] AltsStmt { items: Alts },
    #[k::syntax("gaps({items})")] GapsStmt { items: Gaps },
    #[k::syntax("rows({items})")] RowsStmt { items: Rows },
    #[k::syntax("tail {items}")] Tail { items: Ints },
    #[k::syntax("two {a} {b}")] Two { a: Ints, b: Ints },
    #[k::syntax("make({n})")] Make { n: Int },
    #[k::syntax("nil")] NilV(),
    #[k::syntax("pair({head}, {tail})")] Pair { head: Int, tail: Stmt },
    #[k::syntax("nest({items})")] #[k::alias(recursive)] Nest { items: Ints },
}

#[k::alias]
fn nest_nil(k::term![Program::Nest(Ints::Nil())]: Term<Stmt>) -> Term<Stmt> {
    Program::NilV()
}

#[k::alias]
fn nest_cons(k::term![Program::Nest(Ints::Cons(i, is))]: Term<Stmt>) -> Term<Stmt> {
    Program::Pair(i, Program::Nest(is))
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub items: Ints,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm], items: Ints::Cons(1, Ints::Nil()) }
    }
}

k::rules! {
    for Stmt;
    use Program::*;

    one_empty_row: Make(1) => RowsStmt(Rows::Cons(Ints::Nil(), Rows::Nil()));
    no_alts: Make(2) => AltsStmt(Alts::Nil());
    beside: Make(3) => Two(Ints::Nil(), Ints::Cons(1, Ints::Nil()));
    no_rows: Make(5) => RowsStmt(Rows::Nil());
    pairs: Make(6) => Pair(1, Pair(2, NilV()));
}

k::rules! {
    for Machine;
    use Program::*;

    empty_cell: { k: [Make(4), ..], items: _ } => { k: [..], items: Ints::Nil() };
}
"#;

/// Each program, and how both commands print it: the list in its program spelling, which reads
/// back.
const PROGRAMS: [(&str, &str); 20] = [
    ("ints()", "ints()"),
    ("ints(7)", "ints(7)"),
    ("ints(1, 2, 3)", "ints(1 , 2 , 3)"),
    ("alts(4)", "alts(4)"),
    ("alts(1 | 2 | 3)", "alts(1 | 2 | 3)"),
    ("gaps()", "gaps()"),
    ("gaps(7)", "gaps(7)"),
    ("gaps(1 2 3)", "gaps(1  2  3)"),
    ("rows(1)", "rows(1)"),
    ("rows(1, 2; 3)", "rows(1 , 2 ; 3)"),
    ("rows(; 1)", "rows( ; 1)"),
    ("rows(1;)", "rows(1 ; )"),
    ("rows(;)", "rows( ; )"),
    // The empty list at the end of the text is no text after the production's space.
    ("tail", "tail "),
    ("tail 1, 2", "tail 1 , 2"),
    ("two 1 2", "two 1 2"),
    // The alias clauses write the list: `nest(..)` prints back through them.
    ("nest(1, 2)", "nest(1 , 2)"),
    ("nest()", "nest()"),
    ("nil", "nest()"),
    ("pair(1, nil)", "nest(1)"),
];

/// Each term a rule builds, as `krs run` prints it, and the sort of the empty list no text
/// writes where it stands, if any.
const BUILT: [(&str, &str, Option<&str>); 5] = [
    // The one element of a list: no text, which would read as the empty `Rows`.
    ("make(1)", "rows(.Ints)", Some("Ints")),
    // A `NeList` has no empty text.
    ("make(2)", "alts(.Alts)", Some("Alts")),
    // Beside another list's text, which the empty text cannot be told from.
    ("make(3)", "two .Ints 1", Some("Ints")),
    // `Rows` reads no text as `[]` and as `[[]]`, since its elements can be no text.
    ("make(5)", "rows(.Rows)", Some("Rows")),
    ("make(6)", "nest(1 , 2)", None),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A package of `library` with the K namespace `namespace`.
fn package(root: &Path, library: &str, namespace: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), library).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"lists\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// `krs <command>` on the package's `main` definition, with `input` as FILE and the options
/// `extra`: whether it passed, its stdout and its stderr.
fn krs(
    target: &Path,
    manifest: &Path,
    command: &str,
    input: Option<&Path>,
    extra: &[&str],
) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "lists", "--definition", "main"]);
    if command == "parse" {
        process.args(["--output", "program"]);
    }
    process.args(extra);
    if let Some(input) = input {
        process.arg(input);
    }
    let output = process
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

/// The `warning:` lines of `stderr`.
fn warnings(stderr: &str) -> Vec<&str> {
    stderr
        .lines()
        .filter(|line| line.starts_with("warning:"))
        .collect()
}

/// The warning for an empty list of sort `sort` that no text writes where it stands.
fn empty_list(sort: &str) -> String {
    format!(
        "warning: an empty list of sort `{sort}` stands where no text writes it: a program writes an empty list as no text, which does not read back as it there (beside other text, as a list's one element, or where another list reads no text too), and writes no empty `NeList`; printed as its terminator, which neither a program nor a configuration value reads"
    )
}

/// The `<k>` cell's content in `state`, a printed configuration.
fn computation(state: &str) -> &str {
    state
        .lines()
        .map(str::trim)
        .find(|line| line.ends_with("~> .K"))
        .unwrap_or_else(|| panic!("{state}"))
}

/// Each list shape a program writes prints in its program spelling, read back by both commands;
/// a term a rule built that holds an empty list where no text writes it prints K's terminator
/// there and says so, its other parts still read back; an empty list that stands alone in a
/// cell prints as no text and reads back.
#[test]
fn a_user_list_prints_in_its_program_spelling() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        &temporary.path().join("lists"),
        LIBRARY,
        "ORG-KRS-USER-LIST-PRINTS",
    );
    let (checked, _, stderr) = krs(target.path(), &manifest, "check", None, &[]);
    assert!(checked, "{stderr}");
    let program = temporary.path().join("program.txt");
    for (written, printed) in PROGRAMS {
        fs::write(&program, format!("{written}\n")).unwrap();
        let (parsed, parse_out, parse_err) =
            krs(target.path(), &manifest, "parse", Some(&program), &[]);
        assert!(parsed, "{written}: {parse_err}");
        assert_eq!(
            (
                parse_out.strip_suffix('\n').unwrap_or(&parse_out),
                warnings(&parse_err)
            ),
            (printed, vec![]),
            "{written}"
        );
        let (ran, state, run_err) = krs(target.path(), &manifest, "run", Some(&program), &[]);
        assert!(ran, "{written}: {state}{run_err}");
        assert_eq!(
            (computation(&state), warnings(&run_err)),
            (format!("{printed} ~> .K").as_str(), vec![]),
            "{written}"
        );
    }
    for (written, printed, unwritten) in BUILT {
        fs::write(&program, format!("{written}\n")).unwrap();
        let (ran, state, stderr) = krs(target.path(), &manifest, "run", Some(&program), &[]);
        assert!(ran, "{written}: {state}{stderr}");
        let expected = unwritten.map(empty_list).into_iter().collect::<Vec<_>>();
        assert_eq!(
            (computation(&state), warnings(&stderr)),
            (
                format!("{printed} ~> .K").as_str(),
                expected.iter().map(String::as_str).collect::<Vec<_>>()
            ),
            "{written}"
        );
    }
    fs::write(&program, "make(4)\n").unwrap();
    let (ran, state, stderr) = krs(target.path(), &manifest, "run", Some(&program), &[]);
    assert!(ran, "{state}{stderr}");
    let items = state
        .split("<items>")
        .nth(1)
        .and_then(|rest| rest.split("</items>").next())
        .unwrap_or_else(|| panic!("{state}"));
    assert_eq!((items.trim(), warnings(&stderr)), ("", vec![]), "{state}");
}
