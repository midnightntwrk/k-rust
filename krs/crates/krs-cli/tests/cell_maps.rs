//! A cell's whole built `map![..]`, an initializer cell's and a `cells!`
//! result's, is a collection literal: each entry is written over the map
//! before it, so the map is total and of two keys that evaluate equal the later
//! one wins, where K's join of the entries would leave the cell undefined.
//!
//! The emitted K of an initializer's maps (two keys, a key over a
//! configuration variable, the empty map, a rest) and of a result's maps
//! (written over the empty map, and over a remainder the subject leaves); a
//! result that writes over a remainder at a key the subject does not match,
//! and a key written twice, are errors; and `krs run` gives the later entry
//! where two keys meet, in the initial configuration and in a rule's result.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A semantics whose initializer and rules write whole cell maps. `{TWO}` is
/// the `two` rule's result map, `{OVER}` and `{ANON}` those of the rules whose
/// subjects leave a remainder, bound and anonymous.
const SOURCE: &str = r#"
use k::builtin::{Int, KSequence, Map, map};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("two({a},{b})")]
    Two { a: Int, b: Int },
    #[k::syntax("over({a},{b})")]
    Over { a: Int, b: Int },
    #[k::syntax("anon({a},{b})")]
    Anon { a: Int, b: Int },
    #[k::syntax("done")]
    Done,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub keyed: Map,
    #[k::cell]
    pub empty: Map,
    #[k::cell]
    pub based: Map,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Exp,
        #[k::config_var(name = "A")] a: Int,
        #[k::config_var(name = "B")] b: Int,
        #[k::config_var(name = "BASE")] base: Map,
    ) -> Self {
        Self {
            k: k::k![pgm],
            env: map![a -> 1, b -> 2],
            keyed: k::configuration::Cell::new(map![0 -> a]),
            empty: map![],
            based: map![0 -> 1, ..base],
        }
    }
}

#[k::rule(label = "two")]
fn two(
    a: Term<Int>,
    b: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Two(a, b), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell({TWO}),
        ..state
    }
}

#[k::rule(label = "over")]
fn over(
    a: Term<Int>,
    b: Term<Int>,
    v: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Over(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> v, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell({OVER}),
        ..state
    }
}

#[k::rule(label = "anon")]
fn anon(
    a: Term<Int>,
    b: Term<Int>,
    v: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Anon(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> v, ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell({ANON}),
        ..state
    }
}
"#;

/// The result maps of the accepted source: two keys over the empty map, and,
/// over each remainder, a key the subject matched.
const ACCEPTED: [(&str, &str); 3] = [
    ("TWO", "map![a -> 1, b -> 2]"),
    ("OVER", "map![a -> 10, ..rest]"),
    ("ANON", "map![a -> b]"),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// [`SOURCE`] with its result maps, `ACCEPTED`'s unless `replaced` names one.
fn source(replaced: &[(&str, &str)]) -> String {
    ACCEPTED
        .iter()
        .fold(SOURCE.to_owned(), |source, (name, accepted)| {
            let written = replaced
                .iter()
                .find(|(other, _)| other == name)
                .map_or(*accepted, |(_, written)| *written);
            source.replace(&format!("{{{name}}}"), written)
        })
}

/// Writes the package `name` with `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CELL-MAPS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// An initializer's maps are their calls, the empty map is `.Map` and a rest
/// is the base the entries are written over; a result's map over the empty map
/// is its calls, and over a remainder at keys the subject matched it is the
/// remainder joined with its entries, which is the same map.
#[test]
fn a_cells_whole_map_emits_the_calls_it_denotes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "cellmaps", &source(&[]));
    let output = temporary.path().join("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    let lines = definition
        .lines()
        .map(str::trim)
        .filter(|line| {
            ["<env>", "<keyed>", "<empty>", "<based>"]
                .iter()
                .any(|cell| line.starts_with(cell))
        })
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r#"
        <env> .Map [ $A:Int <- 1 ] [ $B:Int <- 2 ] </env>
        <keyed> .Map [ 0 <- $A:Int ] </keyed>
        <empty> .Map </empty>
        <based> $BASE:Map [ 0 <- 1 ] </based>
        <env> A:Int |-> V:Int => A:Int |-> B:Int ... </env>
        <env> A:Int |-> V:Int Rest:Map => A:Int |-> 10 Rest:Map </env>
        <env> E:Map => .Map [ A:Int <- 1 ] [ B:Int <- 2 ] </env>"#]]
    .assert_eq(&lines);
}

/// The first `error[..]` headline of `krs check` with the result maps
/// `replaced`, and the text its location underlines.
fn check_error(target: &Path, replaced: &[(&str, &str)]) -> (String, String) {
    let temporary = temp_dir();
    let text = source(replaced);
    let manifest = package(temporary.path(), "cellmaps", &text);
    let (success, _, stderr) = krs(target, &manifest, "check", &[]);
    assert!(!success, "{replaced:?} was accepted");
    let mut lines = stderr
        .lines()
        .skip_while(|line| !line.starts_with("error["));
    let headline = lines
        .next()
        .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
        .to_owned();
    let location = lines
        .find_map(|line| line.trim_start().strip_prefix("--> "))
        .unwrap_or_else(|| panic!("no location:\n{stderr}"));
    let mut parts = location.rsplit(':');
    let column = parts.next().unwrap().parse::<usize>().unwrap();
    let line = parts.next().unwrap().parse::<usize>().unwrap();
    let width = lines
        .find(|line| line.contains('^'))
        .map_or(0, |line| line.matches('^').count());
    let written = text.lines().nth(line - 1).unwrap();
    (headline, written[column - 1..column - 1 + width].to_owned())
}

/// Over a remainder the subject leaves, a result writes only at keys the
/// subject matched: the remainder may hold any other key, where K's frame,
/// which joins the remainder with the entries, has no value; so such a key is
/// an error at the key, bound or anonymous. Writing it would need a term that
/// moves the remainder, `items Rest => Rest [ k <- v ]`, which the IR has no
/// shape for (finding NT-9-1). A key written twice is an error at its second
/// spelling.
#[test]
fn a_key_the_remainder_can_hold_and_a_key_written_twice_are_errors() {
    let target = shared_fixture_target();
    let errors = [
        ("OVER", "map![a -> 10, b -> v, ..rest]"),
        ("ANON", "map![a -> 20, b -> 30]"),
        ("TWO", "map![a -> 1, a -> 2]"),
    ]
    .map(|replaced| check_error(target.path(), &[replaced]));
    expect_test::expect![[r#"
        [
            (
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-CELL-MAPS::over (rule): the result writes an entry over the map the subject leaves unread (`..` or `rest @ ..`) at a key the subject does not match, and that map may already hold the key: a result's whole `map![..]` writes each entry over the map before it, here that remainder, but K's cell frame only joins the remainder with the result's entries, which has no value where the two share a key, so KRS cannot write it yet; match the key in the subject, or read the whole map (`env: Cell(m)`) and write `map![k -> v, ..m]`",
                "b",
            ),
            (
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-CELL-MAPS::anon (rule): the result writes an entry over the map the subject leaves unread (`..` or `rest @ ..`) at a key the subject does not match, and that map may already hold the key: a result's whole `map![..]` writes each entry over the map before it, here that remainder, but K's cell frame only joins the remainder with the result's entries, which has no value where the two share a key, so KRS cannot write it yet; match the key in the subject, or read the whole map (`env: Cell(m)`) and write `map![k -> v, ..m]`",
                "b",
            ),
            (
                "error[krs::syntax::invalid-state-macro]: invalid `map!` payload: a map writes one key twice; each entry is written over the map before it, so the earlier value could never be read: write the key once",
                "a",
            ),
        ]
    "#]]
    .assert_debug_eq(&errors);
}

/// Two keys that evaluate equal are one entry, whose value the later entry
/// writes: the initializer's `map![a -> 1, b -> 2]` started with `$A` and `$B`
/// both 5, and the rule `two`'s result for `two(3,3)`; with distinct keys both
/// entries stay. Under K's join both had no value.
#[test]
fn the_later_of_two_equal_keys_wins_at_run_time() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "cellmaps", &source(&[]));
    let runs = [
        ("done", "5", "5"),
        ("done", "5", "6"),
        ("two(3,3)", "5", "6"),
        ("two(3,4)", "5", "6"),
    ]
    .map(|(program, a, b)| {
        let file = manifest.with_file_name("program.txt");
        fs::write(&file, program).unwrap();
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[
                file.to_str().unwrap(),
                "-c",
                &format!("A={a}"),
                "-c",
                &format!("B={b}"),
                "-c",
                "BASE=.Map",
            ],
        );
        assert!(
            stdout.contains("<generatedTop>"),
            "`krs run {program}` failed ({success}):\n{stdout}\n{stderr}"
        );
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let start = flat.find("<env> ").unwrap() + "<env> ".len();
        let end = start + flat[start..].find(" </env>").unwrap();
        format!("{program} with A={a} B={b} => env: {}", &flat[start..end])
    });
    expect_test::expect![[r#"
        [
            "done with A=5 B=5 => env: 5 |-> 2",
            "done with A=5 B=6 => env: 5 |-> 1 6 |-> 2",
            "two(3,3) with A=5 B=6 => env: 3 |-> 2",
            "two(3,4) with A=5 B=6 => env: 3 |-> 1 4 |-> 2",
        ]
    "#]]
    .assert_debug_eq(&runs);
}
