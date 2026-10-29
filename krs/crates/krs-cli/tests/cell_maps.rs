//! A cell's whole built `map![..]`, an initializer cell's, a `cells!`
//! result's and a claim's end state's, has the collection literal's value: each
//! entry is written over the map before it, so the map is total and of two keys
//! that evaluate equal the later one wins.
//!
//! It is emitted as K's join of its entries wherever the join provably has that
//! value (one entry; keys that are ground tokens with different values; keys
//! the subject matched as distinct entries of the map), and as the update chain
//! otherwise. The tests pin the emitted K of an initializer's maps (two
//! configuration-variable keys, a value over a configuration variable, the empty
//! map, ground keys, a rest), of results over the empty map, over a remainder
//! (bound and anonymous, a matched key written under two spellings, an optional
//! cell and a collection instance), over a whole map the subject bound, and of
//! claims' end states; the errors (a key the remainder can hold, a key written
//! twice); the claims' native proofs; and `krs run` where two keys meet.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A semantics whose initializer, rules and claims write whole cell maps. Each
/// `{NAME}` is a result map [`ACCEPTED`] fills, or a test replaces.
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
    #[k::syntax("hex({a})")]
    Hex { a: Int },
    #[k::syntax("whole({a},{b})")]
    Whole { a: Int, b: Int },
    #[k::syntax("opt({a})")]
    Opt { a: Int },
    #[k::syntax("slot({a})")]
    Slot { a: Int },
    #[k::syntax("put({a},{v})")]
    Put { a: Int, v: Int },
    #[k::syntax("done")]
    Done,
}

#[k::cell]
pub struct Objs {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub obj: Obj,
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub oid: Int,
    #[k::cell]
    pub slots: Map,
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
    #[k::cell]
    pub ground: Map,
    #[k::cell(multiplicity = "?")]
    pub opt: Option<Map>,
    #[k::cell(nested)]
    pub objs: Objs,
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
            ground: map![1 -> 10, 0x2 -> 20],
            opt: Some(map![1 -> 1]),
            objs: Objs { obj: Obj { oid: 0, slots: map![] } },
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

#[k::rule(label = "hex")]
fn hex(
    a: Term<Int>,
    v: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Hex(a), tail @ ..),
        env: k::configuration::Cell(map![1 -> v, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![1 -> a, 0x1 -> 6, ..rest]),
        ..state
    }
}

#[k::rule(label = "whole")]
fn whole(
    a: Term<Int>,
    b: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Whole(a, b), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 1, b -> 2, ..e]),
        ..state
    }
}

#[k::rule(label = "opt")]
fn opt(
    a: Term<Int>,
    v: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Opt(a), tail @ ..),
        opt: Some(k::configuration::Cell(map![a -> v, rest @ ..])),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        opt: Some(k::configuration::Cell(map![a -> 2, (a) -> 3, ..rest])),
        ..state
    }
}

#[k::rule(label = "slot")]
fn slot(
    a: Term<Int>,
    v: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Slot(a), tail @ ..),
        Objs::obj: {
            me @ k::fragment![crate::Obj { slots: map![a -> v, rest @ ..], .. }],
            instances0 @ ..
        },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Objs::obj: {
            k::fragment![crate::Obj { slots: map![a -> 4, (a) -> 5, ..rest], ..me }],
            ..instances0
        },
        ..state
    }
}

#[k::rule(label = "put")]
fn put(
    a: Term<Int>,
    v: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Put(a, v), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> v, ..e]),
        ..state
    }
}

/// The end state's keys are the ones the start state matched: the join.
#[k::claim(all_paths, label = "matched-keys")]
fn matched_keys(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Over(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0, b -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> 0]),
        ..state
    }
}

/// One entry: the join.
#[k::claim(all_paths, label = "one-key")]
fn one_key(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Over(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10]),
        ..state
    }
}

/// Two symbolic keys the start state did not match: the chain, which also
/// covers `a == b`.
#[k::claim(all_paths, label = "unmatched-keys")]
fn unmatched_keys(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Put(a, 10), ExpSyntax::Put(b, 11), tail @ ..),
        env: k::configuration::Cell(map![]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> 11]),
        ..state
    }
}
"#;

/// The result maps of the accepted source: two symbolic keys over the empty
/// map, a key the subject matched written twice over a bound remainder, and a
/// key the subject matched over an anonymous one.
const ACCEPTED: [(&str, &str); 3] = [
    ("TWO", "map![a -> 1, b -> 2]"),
    ("OVER", "map![a -> 9, (a) -> 10, ..rest]"),
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

/// The emitted K of every built whole map: the join where it provably has the
/// update chain's value, the chain otherwise, and the chain over a whole map the
/// subject bound (`map![a -> 1, b -> 2, ..e]`).
#[test]
fn a_built_cell_map_emits_the_join_where_it_has_the_value_and_the_chain_otherwise() {
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
    let cells = [
        "<env>", "<keyed>", "<empty>", "<based>", "<ground>", "<opt", "<slots>", "rule [",
        "claim [",
    ];
    let lines = ["definition.k", "spec.k"]
        .iter()
        .flat_map(|file| {
            fs::read_to_string(output.join(file))
                .unwrap()
                .lines()
                .map(str::trim)
                .filter(|line| cells.iter().any(|cell| line.starts_with(cell)))
                .map(str::to_owned)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r#"
        <env> .Map [ $A:Int <- 1 ] [ $B:Int <- 2 ] </env>
        <keyed> 0 |-> $A:Int </keyed>
        <empty> .Map </empty>
        <based> $BASE:Map [ 0 <- 1 ] </based>
        <ground> 1 |-> 10 2 |-> 20 </ground>
        <opt multiplicity="?"> 1 |-> 1 </opt>
        <slots> .Map </slots>
        rule [anon]:
        <env> A:Int |-> V:Int => A:Int |-> B:Int ... </env>
        rule [hex]:
        <env> 1 |-> V:Int Rest:Map => 1 |-> 6 Rest:Map </env>
        rule [opt]:
        <opt> A:Int |-> V:Int Rest:Map => A:Int |-> 3 Rest:Map </opt>
        rule [over]:
        <env> A:Int |-> V:Int Rest:Map => A:Int |-> 10 Rest:Map </env>
        rule [put]:
        <env> E:Map => E:Map [ A:Int <- V:Int ] </env>
        rule [slot]:
        <slots> A:Int |-> V:Int Rest:Map => A:Int |-> 5 Rest:Map </slots>
        rule [two]:
        <env> E:Map => .Map [ A:Int <- 1 ] [ B:Int <- 2 ] </env>
        rule [whole]:
        <env> E:Map => E:Map [ A:Int <- 1 ] [ B:Int <- 2 ] </env>
        claim [matched-keys]:
        <env> A:Int |-> 0 B:Int |-> 0 => A:Int |-> 10 B:Int |-> 0 </env>
        claim [one-key]:
        <env> A:Int |-> 0 => A:Int |-> 10 </env>
        claim [unmatched-keys]:
        <env> .Map => .Map [ A:Int <- 10 ] [ B:Int <- 11 ] </env>"#]]
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
/// an error at the key, bound or anonymous, whose advice is the form `whole`
/// writes (`map![k -> v, ..m]` over `Cell(m)`). Writing it over the remainder
/// would need the remainder bound on the left alone, `K |-> V Rest => Rest [ K
/// <- W ]`, which the IR has no frame for (finding NT-9-1). A key written twice
/// in one spelling is an error at its second spelling, as in a literal.
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
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-CELL-MAPS::over (rule): the result writes an entry over the map the subject leaves unread (`..` or `rest @ ..`) at a key the subject does not match, and that map may already hold the key: a result's whole `map![..]` writes each entry over the map before it, here that remainder, but K's cell frame only joins the remainder with the result's entries, which has no value where the two share a key, so KRS cannot write it yet; bind the whole map instead, `env: Cell(m)` (inside `Some(..)` for an optional cell), and write `map![k -> v, ..m]`, which writes the entries over `m`",
                "b",
            ),
            (
                "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-CELL-MAPS::anon (rule): the result writes an entry over the map the subject leaves unread (`..` or `rest @ ..`) at a key the subject does not match, and that map may already hold the key: a result's whole `map![..]` writes each entry over the map before it, here that remainder, but K's cell frame only joins the remainder with the result's entries, which has no value where the two share a key, so KRS cannot write it yet; bind the whole map instead, `env: Cell(m)` (inside `Some(..)` for an optional cell), and write `map![k -> v, ..m]`, which writes the entries over `m`",
                "b",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: the key `a` is written twice; two keys written as the same term are one key, so the earlier entry's value would never be read: write the key once, with the value it maps to",
                "a",
            ),
        ]
    "#]]
    .assert_debug_eq(&errors);
}

/// Two keys that evaluate equal are one entry, whose value the later entry
/// writes: the initializer's `map![a -> 1, b -> 2]` started with `$A` and `$B`
/// both 5, the rule `two`'s result for `two(3,3)`, and `whole`'s entries
/// written over the map it read for `whole(5,5)`; with distinct keys both
/// entries stay. Under K's join the first two had no value.
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
        ("whole(5,5)", "5", "6"),
        ("whole(3,4)", "5", "6"),
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
            "whole(5,5) with A=5 B=6 => env: 5 |-> 2 6 |-> 2",
            "whole(3,4) with A=5 B=6 => env: 3 |-> 1 4 |-> 2 5 |-> 1 6 |-> 2",
        ]
    "#]]
    .assert_debug_eq(&runs);
}

/// The claims prove natively: the end state's join over the keys the start
/// state matched, the one-entry join, and the chain of two keys the start state
/// did not match, which the rules build too.
#[test]
fn claims_over_built_maps_prove() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "cellmaps", &source(&[]));
    let (_, stdout, stderr) = krs(target.path(), &manifest, "prove", &[]);
    let mut statuses = stdout
        .lines()
        .chain(stderr.lines())
        .filter(|line| line.contains("SPEC.") && line.contains(": "))
        .map(|line| line.trim().to_owned())
        .collect::<Vec<_>>();
    statuses.sort();
    expect_test::expect![[r#"
        [
            "ORG-KRS-CELL-MAPS-SPEC.matched-keys: proven",
            "ORG-KRS-CELL-MAPS-SPEC.one-key: proven",
            "ORG-KRS-CELL-MAPS-SPEC.unmatched-keys: proven",
        ]
    "#]]
    .assert_debug_eq(&statuses);
}
