//! A Set cell collection is a set of its instances, and a pattern looks it up
//! by an instance as it looks a set up by an element: an instance whose every
//! cell is written and whose names the rest of the pattern binds is computed,
//! and the rule applies when the collection holds the instance it computes
//! (decision NT-Q6). K writes an instance as the cells it holds, where no K
//! frontend reads a function, so each construct the instance computes is
//! written as a fresh variable, `Krs_InstanceN`, which a guard of the rule
//! equates with the value: `Obj { oid: n + 1, hits: 0 }` is
//! `<obj> <oid> Krs_Instance0 </oid> <hits> 0 </hits> </obj>` with
//! `requires Krs_Instance0 ==K N +Int 1`, the same rule, since the set holds
//! the instance once.
//!
//! The tests pin the emitted K of computed instances (an operator, a call in a
//! `cells!` rule, a removed instance, a labelled one the result updates, one
//! whose names another instance or a map entry binds first, and the author's
//! `requires` after the guards); the errors (an instance that selects, by `..`
//! or a name nothing else binds, a cycle, a name bound nowhere, and in a Map
//! collection's instance the notation, the sort test and the record update
//! the walker leaves to resolution); `krs run` on the rules; and the claims'
//! native proofs.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A semantics with a Set collection of objects and a Map collection of rows.
/// Each `{NAME}` is a rule [`ACCEPTED`] fills, or a test replaces.
const SOURCE: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence, Map, Set, int, map, set};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    cmd (Mk, Touch, Probe, Drop, Bump, Next, Via, Find, Check, Dup, Dz, Mkb, Bags, Bagm, Bagc)
    > right seq (Seq)
)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("mk {oid}")] Mk { oid: Int },
    #[k::syntax("touch {oid}")] Touch { oid: Int },
    #[k::syntax("probe {oid}")] Probe { oid: Int },
    #[k::syntax("drop {oid}")] Drop { oid: Int },
    #[k::syntax("bump {oid}")] Bump { oid: Int },
    #[k::syntax("next {oid}")] Next { oid: Int },
    #[k::syntax("via {key}")] Via { key: Int },
    #[k::syntax("find {oid}")] Find { oid: Int },
    #[k::syntax("check {oid}")] Check { oid: Int },
    #[k::syntax("dup {oid}")] Dup { oid: Int },
    #[k::syntax("dz {oid}")] Dz { oid: Int },
    #[k::syntax("mkb {id}")] Mkb { id: Int },
    #[k::syntax("bags {id}")] Bags { id: Int },
    #[k::syntax("bagm {id}")] Bagm { id: Int },
    #[k::syntax("bagc {id}")] Bagc { id: Int },
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::cell]
pub struct Objects {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub obj: Obj,
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub oid: Int,
    #[k::cell]
    pub hits: Int,
}

/// A Set collection whose instances hold a set and a map.
#[k::cell]
pub struct Sacks {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub bag: Bag,
}

#[k::cell]
pub struct Bag {
    #[k::cell]
    pub key: Int,
    #[k::cell]
    pub s: Set,
    #[k::cell]
    pub m: Map,
}

#[k::cell]
pub struct Meta {
    #[k::cell]
    pub a: Int,
    #[k::cell]
    pub b: Int,
}

#[k::cell]
pub struct Table {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub row: Row,
}

#[k::cell]
pub struct Row {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub value: Stmt,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell(nested)]
    pub objects: Objects,
    #[k::cell(nested)]
    pub table: Table,
    #[k::cell(nested)]
    pub sacks: Sacks,
    #[k::cell(nested)]
    pub meta: Meta,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: map![1 -> 4],
            objects: Objects { obj: Obj { oid: 0, hits: 0 } },
            table: Table { row: Row { id: 0, value: Cmd::Mk(0) } },
            sacks: Sacks { bag: Bag { key: 0, s: set![], m: map![] } },
            meta: Meta { a: 0, b: 0 },
        }
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

    mk: {
        k: [Mk(n), ..],
        obj: { .. },
    } => {
        k: [..],
        obj: { Obj { oid: n, .. }, .. },
    };

    touch: {
        k: [Touch(n), ..],
        obj: { o @ Obj { oid: n, hits: h }, .. },
    } => {
        k: [..],
        obj: { Obj { hits: int::add(h, 1), ..o }, .. },
    };

    {PROBE}

    drop: {
        k: [Drop(n), ..],
        obj: { Obj { oid: n + 1, hits: 0 }, .. },
    } => {
        k: [..],
        obj: { .. },
    };

    bump: {
        k: [Bump(n), ..],
        obj: { o @ Obj { oid: n + 1, hits: 0 }, .. },
    } => {
        k: [..],
        obj: { Obj { hits: 1, ..o }, .. },
    };

    next: {
        k: [Next(n), ..],
        obj: { Obj { oid: n, hits: h }, Obj { oid: n + 1, hits: h }, .. },
    } => {
        k: [..],
    };

    dup: {
        k: [Dup(n), ..],
        obj: { Obj { oid: n + 1, hits: 0 }, Obj { oid: n + 1, hits: 0 }, .. },
    } => {
        k: [..],
    };

    #[k::requires(10 / n > 0)]
    dz: {
        k: [Dz(n), ..],
        obj: { Obj { oid: n + 100, hits: 0 }, .. },
    } => {
        k: [..],
    };

    mkb: {
        k: [Mkb(n), ..],
        bag: { .. },
    } => {
        k: [..],
        bag: { Bag { key: n, s: set![n, n + 1], m: map![n -> n + 1] }, .. },
    };

    bags: {
        k: [Bags(n), ..],
        bag: { Bag { key: n, s: set![n + 1, n], m: map![n -> n + 1] }, .. },
    } => {
        k: [..],
    };

    bagm: {
        k: [Bagm(n), ..],
        bag: { Bag { key: n - 1, s: set![n - 1, n], m: map![n - 1 -> n] }, .. },
    } => {
        k: [..],
    };

    #[k::requires(n > 0)]
    check: {
        k: [Check(n), ..],
        obj: { Obj { oid: n * 2, hits: n - 1 }, .. },
    } => {
        k: [..],
    };
}

#[k::rule(label = "find")]
fn find(
    n: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Find(n), tail @ ..),
        Objects::obj: {
            me @ k::fragment![crate::Obj { oid: n + 1, hits: 0 }],
            instances0 @ ..
        },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Objects::obj: { k::fragment![crate::Obj { ..me }], ..instances0 },
        ..state
    }
}

/// A readable map read's value binder stays fresh, so a `cells!` rule reads
/// the instance's id from an `env` entry.
#[k::rule(label = "via")]
fn via(
    x: k::Term<Int>,
    v: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Via(x), tail @ ..),
        env: k::configuration::Cell(map![x -> v, ..]),
        Objects::obj: {
            k::fragment![crate::Obj { oid: int::add(v, 1), hits: 0 }],
            instances0 @ ..
        },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Objects::obj: { ..instances0 },
        ..state
    }
}

/// An exact map cell is part of the instance's value, its key read as a
/// key is.
#[k::rule(label = "bagc")]
fn bagc(
    n: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Bagc(n), tail @ ..),
        Sacks::bag: {
            k::fragment![crate::Bag { key: n + 1, s: set![n + 2, n + 1], m: map![n + 1 -> int::add(n, 2)] }],
            instances0 @ ..
        },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Sacks::bag: { ..instances0 },
        ..state
    }
}

{EXTRA}

k::claims! {
    for Machine;
    use Cmd::*;

    /// The probe finds the one object it computes.
    #[k::claim(all_paths)]
    found: {
        k: [Probe(n), ..],
        obj: { Obj { oid: int::add(n, 1), hits: 0 } },
    } => {
        k: [..],
    };

    /// Among two objects, the probe finds the one it computes.
    #[k::claim(all_paths)]
    found_among_two: {
        k: [Probe(n), ..],
        obj: { Obj { oid: m, hits: 1 }, Obj { oid: int::add(n, 1), hits: 0 } },
    } => {
        k: [..],
    };

    /// An object with the id the probe computes and other hits is no match.
    #[k::claim(all_paths)]
    other_hits: {
        k: [Probe(n), ..],
        obj: { Obj { oid: int::add(n, 1), hits: 1 } },
    } => {
        k: [..],
    };
}
"#;

/// The rules a test may replace, as [`SOURCE`] writes them.
const ACCEPTED: [(&str, &str); 2] = [
    (
        "PROBE",
        "probe: {\n        k: [Probe(n), ..],\n        obj: { Obj { oid: n + 1, hits: 0 }, .. },\n    } => {\n        k: [..],\n    };",
    ),
    ("EXTRA", ""),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// [`SOURCE`] with its rules, `ACCEPTED`'s unless `replaced` names one.
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

/// Writes the package `objects` with `source` under `root`.
fn package(root: &Path, source: &str) -> PathBuf {
    let directory = root.join("objects");
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"objects\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-SET-INSTANCES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "objects", "--definition", "main"])
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

/// The emitted rules that look an instance up: each construct an instance
/// computes is a fresh variable, which the rule's guard equates with its value,
/// before the author's `requires`. A label names the instance the result
/// updates in place; an instance whose names another instance (`next`) or a
/// map entry (`via`, a `cells!` rule) binds is looked up after it.
#[test]
fn a_computed_instance_is_emitted_with_its_guards() {
    let rules = emitted_rules(&["probe", "drop", "bump", "next", "via", "check", "find"]);
    expect_test::expect![[r"
        rule [probe]:
        <k> probe N:Int => .K ... </k>
        <obj>
        <oid> Krs_Instance0:Int </oid>
        <hits> 0 </hits>
        </obj>
        requires Krs_Instance0:Int ==K (N:Int +Int 1)
        rule [drop]:
        <k> drop N:Int => .K ... </k>
        (<obj>
        <oid> Krs_Instance0:Int </oid>
        <hits> 0 </hits>
        </obj> => .Bag)
        requires Krs_Instance0:Int ==K (N:Int +Int 1)
        rule [bump]:
        <k> bump N:Int => .K ... </k>
        <obj>
        <oid> Krs_Instance0:Int </oid>
        <hits> 0 => 1 </hits>
        </obj>
        requires Krs_Instance0:Int ==K (N:Int +Int 1)
        rule [next]:
        <k> next N:Int => .K ... </k>
        <obj>
        <oid> N:Int </oid>
        <hits> H:Int </hits>
        </obj>
        <obj>
        <oid> Krs_Instance0:Int </oid>
        <hits> H:Int </hits>
        </obj>
        requires Krs_Instance0:Int ==K (N:Int +Int 1)
        rule [via]:
        <k> via X:Int ~> Tail:K => .K ~> Tail:K </k>
        <env> X:Int |-> V:Int ... </env>
        (<obj>
        <oid> Krs_Instance0:Int </oid>
        <hits> 0 </hits>
        </obj> => .Bag)
        requires Krs_Instance0:Int ==K (V:Int +Int 1)
        rule [check]:
        <k> check N:Int => .K ... </k>
        <obj>
        <oid> Krs_Instance0:Int </oid>
        <hits> Krs_Instance1:Int </hits>
        </obj>
        requires (Krs_Instance0:Int ==K (N:Int *Int 2)) andThenBool ((Krs_Instance1:Int ==K (N:Int -Int 1)) andThenBool (N:Int >Int 0))
        rule [find]:
        <k> find N:Int ~> Tail:K => .K ~> Tail:K </k>
        <obj>
        <oid> Krs_Instance0:Int </oid>
        <hits> 0 </hits>
        </obj>
        requires Krs_Instance0:Int ==K (N:Int +Int 1)"]].assert_eq(&rules);
}

/// Two computed instances in one rule are two guarded elements; the guards
/// come before the author's condition, which reads what they found (`dz`);
/// set and map cells, a `cells!` instance's exact map cell among them
/// (`bagc`), are part of the value looked up.
#[test]
fn set_and_map_cells_and_two_instances_are_emitted_with_their_guards() {
    let rules = emitted_rules(&["dup", "dz", "bags", "bagc"]);
    expect_test::expect![[r"
        rule [dup]:
        <k> dup N:Int => .K ... </k>
        <obj>
        <oid> Krs_Instance0:Int </oid>
        <hits> 0 </hits>
        </obj>
        <obj>
        <oid> Krs_Instance1:Int </oid>
        <hits> 0 </hits>
        </obj>
        requires (Krs_Instance0:Int ==K (N:Int +Int 1)) andThenBool (Krs_Instance1:Int ==K (N:Int +Int 1))
        rule [dz]:
        <k> dz N:Int => .K ... </k>
        <obj>
        <oid> Krs_Instance0:Int </oid>
        <hits> 0 </hits>
        </obj>
        requires (Krs_Instance0:Int ==K (N:Int +Int 100)) andThenBool ((10 /Int N:Int) >Int 0)
        rule [bags]:
        <k> bags N:Int => .K ... </k>
        <bag>
        <key> N:Int </key>
        <s> Krs_Instance0:Set </s>
        <m> Krs_Instance1:Map </m>
        </bag>
        requires (Krs_Instance0:Set ==K SetItem(N:Int +Int 1) |Set SetItem(N:Int)) andThenBool (Krs_Instance1:Map ==K .Map [ N:Int <- N:Int +Int 1 ])
        rule [bagc]:
        <k> bagc N:Int ~> Tail:K => .K ~> Tail:K </k>
        (<bag>
        <key> Krs_Instance0:Int </key>
        <s> Krs_Instance1:Set </s>
        <m> Krs_Instance2:Int |-> Krs_Instance3:Int </m>
        </bag> => .Bag)
        requires (Krs_Instance0:Int ==K (N:Int +Int 1)) andThenBool ((Krs_Instance1:Set ==K SetItem(N:Int +Int 2) |Set SetItem(N:Int +Int 1)) andThenBool ((Krs_Instance2:Int ==K (N:Int +Int 1)) andThenBool (Krs_Instance3:Int ==K (N:Int +Int 2))))"]].assert_eq(&rules);
}

/// The emitted rules `labels` of [`SOURCE`], one line each.
fn emitted_rules(labels: &[&str]) -> String {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), &source(&[]));
    let output = temporary.path().join("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    let mut rules = Vec::new();
    for label in labels {
        let rule = definition
            .lines()
            .skip_while(|line| line.trim() != format!("rule [{label}]:"))
            .take_while(|line| {
                !line.trim().is_empty()
                    && line.trim() != "endmodule"
                    && (line.trim() == format!("rule [{label}]:") || !line.contains("rule ["))
            })
            .map(str::trim)
            .collect::<Vec<_>>()
            .join("\n");
        rules.push(rule);
    }
    rules.join("\n")
}

/// The first `error[..]` headline of `krs check` with the rules `replaced`,
/// and the text its location underlines.
fn check_error(target: &Path, replaced: &[(&str, &str)]) -> (String, String) {
    let temporary = temp_dir();
    let text = source(replaced);
    let manifest = package(temporary.path(), &text);
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

/// The probe rule `probe` written over the subject `subject`.
fn probe(subject: &str) -> String {
    format!("probe: {{ k: [Probe(n), ..], {subject} }} => {{ k: [..] }};")
}

/// An instance that selects one by matching (`..` in it, a name nothing else
/// binds) is matched cells, where a function never matches; an instance whose
/// names no order of lookups binds is a cycle (here the value of an entry
/// whose own key reads it); one that reads a name bound
/// nowhere reads a value nothing gave. A Map collection's instance is matched:
/// the notation, the sort test and the record update the walker reads as in a
/// key are refused there by resolution. A `cells!` instance's map cell with
/// `..` leaves entries open, so its instance selects. A claim's state reads
/// its instances' cells as any pattern, where an operation is spelled as its
/// call. An ordinary map key that holds an open group record selects too.
#[test]
fn an_instance_that_is_not_computed_is_refused() {
    let target = shared_fixture_target();
    let cycle = "#[k::rule(label = \"cycle\")]\nfn cycle(\n    v: k::Term<Int>,\n    k::cells! {\n        k: k::configuration::KCell(Cmd::Probe(0), tail @ ..),\n        Objects::obj: {\n            k::fragment![crate::Obj { oid: int::add(v, 2), hits: 0 }],\n            instances0 @ ..\n        },\n        env: k::configuration::Cell(map![int::add(v, 1) -> v, ..]),\n        state @ ..\n    }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), ..state }\n}\n";
    let open_map = "#[k::rule(label = \"open-map\")]\nfn open_map(\n    n: k::Term<Int>,\n    k::cells! {\n        k: k::configuration::KCell(Cmd::Probe(n), tail @ ..),\n        Sacks::bag: {\n            k::fragment![crate::Bag { key: n + 1, s: set![], m: map![1 -> 2, ..] }],\n            instances0 @ ..\n        },\n        state @ ..\n    }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), ..state }\n}\n";
    let claim = "k::claims! {\n    for Machine;\n    use Cmd::*;\n\n    #[k::claim(all_paths)]\n    spelled: { k: [Probe(n), ..], obj: { Obj { oid: n + 1, hits: 0 } } } => { k: [..] };\n}\n";
    let errors = [
        vec![("PROBE", probe("obj: { Obj { oid: n + 1, .. }, .. }"))],
        vec![("PROBE", probe("obj: { Obj { oid: n + 1, hits: h }, .. }"))],
        vec![("EXTRA", cycle.to_owned())],
        vec![(
            "PROBE",
            "probe: { k: [Probe(0), ..], obj: { Obj { oid: m + 1, hits: 0 }, .. } } => { k: [..] };"
                .to_owned(),
        )],
        vec![("PROBE", probe("row: { Row { id: n + 1, value: Mk(0) }, .. }"))],
        vec![(
            "PROBE",
            probe("row: { Row { id: k::project!(Int, n), value: Mk(0) }, .. }"),
        )],
        vec![(
            "PROBE",
            "probe: { k: [Probe(n), v @ Mk { .. }, ..], row: { Row { id: n, value: Mk { oid: 1, ..v } }, .. } } => { k: [..] };"
                .to_owned(),
        )],
        vec![("EXTRA", open_map.to_owned())],
        vec![("EXTRA", claim.to_owned())],
        vec![("PROBE", probe("env: { Meta { a: n + 1, .. } -> v, .. }"))],
    ]
    .map(|replaced| {
        let replaced = replaced
            .iter()
            .map(|(name, text)| (*name, text.as_str()))
            .collect::<Vec<_>>();
        check_error(target.path(), &replaced)
    });
    expect_test::expect![[r#"
        [
            (
                "error[krs::analysis::function-in-pattern]: the operator `+`, a builtin function, stands in a Set collection's instance that also holds `..`, which leaves the instance's other cells open, so the instance selects one by matching the instances the collection holds as they stand, rather than computing the instance looked up; the operator `+`, a builtin function, denotes the value evaluation produces, which no cell of an instance holds, so this pattern describes an instance that never occurs and the sentence never applies: bind the selected part elsewhere in the pattern and write every cell to look the instance up, or match a variable here and relate it to the application in a guard (`requires`)",
                "+",
            ),
            (
                "error[krs::analysis::function-in-pattern]: the operator `+`, a builtin function, stands in a Set collection's instance that also holds the name `h`, which nothing else binds, so the instance selects one by matching the instances the collection holds as they stand, rather than computing the instance looked up; the operator `+`, a builtin function, denotes the value evaluation produces, which no cell of an instance holds, so this pattern describes an instance that never occurs and the sentence never applies: bind the selected part elsewhere in the pattern and write every cell to look the instance up, or match a variable here and relate it to the application in a guard (`requires`)",
                "+",
            ),
            (
                "error[krs::analysis::function-in-pattern]: the builtin function `k::builtin::int::add` stands in a Set collection's instance that reads `v`, which only the values of the collection's entries this key or another computed key looks up bind: no order of lookups gives a computed key the names it reads, so matching would choose an entry and evaluate the builtin function `k::builtin::int::add` on each, a selection holding a function, which never matches an evaluated instance; bind those names elsewhere in the pattern, or match a variable here and relate it to the application in a guard (`requires`)",
                "int::add",
            ),
            (
                "error[krs::expand::unbound-name]: `m` is not bound in this sentence: it stands only below the operator `+`, a builtin function, in a Set collection's instance, and an instance is evaluated to look it up in the collection, so the instance reads `m` and binds nothing; bind `m` elsewhere in the pattern",
                "m",
            ),
            (
                "error[krs::analysis::function-in-pattern]: the operator `+`, a builtin function, stands in a Map collection's instance, which the pattern matches against the instances the collection holds: a Map collection pairs an instance's key cell with the whole instance, key cell included, as the value it maps to, so its cells are values a match compares (decision D1), where a Set collection's computed instance is looked up as the set's element; those cells have their functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`)",
                "+",
            ),
            (
                "error[krs::analysis::invalid-sort-test]: `k::project!(Int, ..)` is a projection, which is a function call and cannot be matched; restrict the binder with a typed parameter or `where x: Int`",
                "k::project!(Int, n)",
            ),
            (
                "error[krs::syntax::invalid-record-update]: a record update `Ctor { f: e, ..base }` stands in a Map collection's instance, which the pattern matches against the instances the collection holds: a Map collection pairs an instance's key cell with the whole instance, key cell included, as the value it maps to, so its cells are values a match compares (decision D1), where a Set collection's computed instance is looked up as the set's element; `..base` builds a record from the record `base` matched, which only a term a sentence builds can say, and a pattern denotes no record by it: name the fields the pattern constrains, and leave out the others with `..`",
                "Mk",
            ),
            (
                "error[krs::analysis::function-in-pattern]: the operator `+`, a builtin function, stands in a Set collection's instance that also holds `..` in a cell's map, which leaves its other entries open, so the instance selects one by matching the instances the collection holds as they stand, rather than computing the instance looked up; the operator `+`, a builtin function, denotes the value evaluation produces, which no cell of an instance holds, so this pattern describes an instance that never occurs and the sentence never applies: bind the selected part elsewhere in the pattern and write every cell to look the instance up, or match a variable here and relate it to the application in a guard (`requires`)",
                "+",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: `+` is not a pattern: a pattern writes a builtin operation as its call, `int::add(..)`, `string::concat(..)`, or `float::add(..)`, where a pattern holds an application at all: in a simplification's or a claim's subject, or in a map's key or a set's element, which are looked up",
                "+",
            ),
            (
                "error[krs::analysis::function-in-pattern]: the operator `+`, a builtin function, stands in a map key that also holds an open record `Ctor { .. }`, so the key selects an entry by matching the evaluated keys the map holds rather than computing the key looked up; the operator `+`, a builtin function, denotes the value evaluation produces, which no evaluated key is, so the key never matches: bind the selected part elsewhere in the pattern to look the entry up, or match a variable here and relate it to the application in a guard (`requires`)",
                "+",
            ),
        ]
    "#]].assert_debug_eq(&errors);
}

/// The probe applies when the collection holds the object it computes, and is
/// stuck otherwise, with an object of that id but other hits too; `drop`
/// removes the object it computes, `bump` updates it, `next` finds an object
/// beside the one before it with the same hits, the `cells!` rule `via` removes
/// one whose id an `env` entry gives, `check` finds one whose two cells it
/// computes, under the author's condition, and the `cells!` rule `find` one it
/// computes with an operator, which its label keeps. Among four objects the
/// probe finds the last in either order of creation; `dup` never finds two
/// instances in one; `dz`'s guards hold before its condition, which divides
/// by `n`, is read; `bags`, `bagm` and the `cells!` rule `bagc` compare set
/// and map cells (`==K` on a `Set` and a `Map`).
#[test]
fn a_computed_instance_is_looked_up_at_run_time() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), &source(&[]));
    let runs = [
        "mk 3 probe 2",
        "mk 3 touch 3 probe 2",
        "probe 5",
        "mk 4 mk 3 touch 4 probe 3",
        "mk 3 drop 2 probe 2",
        "mk 3 bump 2 probe 2",
        "mk 3 mk 4 touch 3 touch 4 next 3",
        "mk 3 mk 4 touch 3 next 3",
        "mk 5 via 1",
        "mk 4 touch 4 check 2",
        "mk 4 check 2",
        "mk 0 check 0",
        "mk 3 find 2",
        "mk 1 mk 2 mk 3 mk 40 probe 39",
        "mk 40 mk 3 mk 2 mk 1 probe 39",
        "mk 1 mk 2 mk 3 dup 1",
        "mk 1 dz 0",
        "mk 105 dz 5",
        "mkb 5 bags 5",
        "mkb 5 bags 4",
        "mkb 5 bagm 6",
        "mkb 5 bagc 4",
        "mkb 5 bagc 5",
    ]
    .map(|program| {
        let file = manifest.with_file_name("program.txt");
        fs::write(&file, program).unwrap();
        let (success, stdout, stderr) =
            krs(target.path(), &manifest, "run", &[file.to_str().unwrap()]);
        assert!(
            stdout.contains("<generatedTop>"),
            "`krs run {program}` failed ({success}):\n{stdout}\n{stderr}"
        );
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let cell = |name: &str| {
            let start = flat.find(&format!("<{name}> ")).unwrap() + name.len() + 3;
            let end = start + flat[start..].find(&format!(" </{name}>")).unwrap();
            flat[start..end].to_owned()
        };
        format!(
            "{program} => k: {}; objects: {}; sacks: {}",
            cell("k"),
            cell("objects"),
            cell("sacks")
        )
    });
    expect_test::expect![[r#"
        [
            "mk 3 probe 2 => k: .K; objects: <obj> <oid> 3 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mk 3 touch 3 probe 2 => k: probe 2 ~> .K; objects: <obj> <oid> 3 </oid> <hits> 1 </hits> </obj>; sacks: .BagCellSet",
            "probe 5 => k: probe 5 ~> .K; objects: .ObjCellSet; sacks: .BagCellSet",
            "mk 4 mk 3 touch 4 probe 3 => k: probe 3 ~> .K; objects: <obj> <oid> 3 </oid> <hits> 0 </hits> </obj> <obj> <oid> 4 </oid> <hits> 1 </hits> </obj>; sacks: .BagCellSet",
            "mk 3 drop 2 probe 2 => k: probe 2 ~> .K; objects: .ObjCellSet; sacks: .BagCellSet",
            "mk 3 bump 2 probe 2 => k: probe 2 ~> .K; objects: <obj> <oid> 3 </oid> <hits> 1 </hits> </obj>; sacks: .BagCellSet",
            "mk 3 mk 4 touch 3 touch 4 next 3 => k: .K; objects: <obj> <oid> 3 </oid> <hits> 1 </hits> </obj> <obj> <oid> 4 </oid> <hits> 1 </hits> </obj>; sacks: .BagCellSet",
            "mk 3 mk 4 touch 3 next 3 => k: next 3 ~> .K; objects: <obj> <oid> 3 </oid> <hits> 1 </hits> </obj> <obj> <oid> 4 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mk 5 via 1 => k: .K; objects: .ObjCellSet; sacks: .BagCellSet",
            "mk 4 touch 4 check 2 => k: .K; objects: <obj> <oid> 4 </oid> <hits> 1 </hits> </obj>; sacks: .BagCellSet",
            "mk 4 check 2 => k: check 2 ~> .K; objects: <obj> <oid> 4 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mk 0 check 0 => k: check 0 ~> .K; objects: <obj> <oid> 0 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mk 3 find 2 => k: .K; objects: <obj> <oid> 3 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mk 1 mk 2 mk 3 mk 40 probe 39 => k: .K; objects: <obj> <oid> 1 </oid> <hits> 0 </hits> </obj> <obj> <oid> 2 </oid> <hits> 0 </hits> </obj> <obj> <oid> 3 </oid> <hits> 0 </hits> </obj> <obj> <oid> 40 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mk 40 mk 3 mk 2 mk 1 probe 39 => k: .K; objects: <obj> <oid> 1 </oid> <hits> 0 </hits> </obj> <obj> <oid> 2 </oid> <hits> 0 </hits> </obj> <obj> <oid> 3 </oid> <hits> 0 </hits> </obj> <obj> <oid> 40 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mk 1 mk 2 mk 3 dup 1 => k: dup 1 ~> .K; objects: <obj> <oid> 1 </oid> <hits> 0 </hits> </obj> <obj> <oid> 2 </oid> <hits> 0 </hits> </obj> <obj> <oid> 3 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mk 1 dz 0 => k: dz 0 ~> .K; objects: <obj> <oid> 1 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mk 105 dz 5 => k: .K; objects: <obj> <oid> 105 </oid> <hits> 0 </hits> </obj>; sacks: .BagCellSet",
            "mkb 5 bags 5 => k: .K; objects: .ObjCellSet; sacks: <bag> <key> 5 </key> <s> SetItem ( 5 ) SetItem ( 6 ) </s> <m> 5 |-> 6 </m> </bag>",
            "mkb 5 bags 4 => k: bags 4 ~> .K; objects: .ObjCellSet; sacks: <bag> <key> 5 </key> <s> SetItem ( 5 ) SetItem ( 6 ) </s> <m> 5 |-> 6 </m> </bag>",
            "mkb 5 bagm 6 => k: .K; objects: .ObjCellSet; sacks: <bag> <key> 5 </key> <s> SetItem ( 5 ) SetItem ( 6 ) </s> <m> 5 |-> 6 </m> </bag>",
            "mkb 5 bagc 4 => k: .K; objects: .ObjCellSet; sacks: .BagCellSet",
            "mkb 5 bagc 5 => k: bagc 5 ~> .K; objects: .ObjCellSet; sacks: <bag> <key> 5 </key> <s> SetItem ( 5 ) SetItem ( 6 ) </s> <m> 5 |-> 6 </m> </bag>",
        ]
    "#]].assert_debug_eq(&runs);
}

/// The claims over a symbolic id prove natively where the collection holds the
/// object the probe computes, alone or beside another, and not where the
/// object of that id has other hits.
#[test]
fn claims_over_a_computed_instance_prove() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), &source(&[]));
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
            "ORG-KRS-SET-INSTANCES-SPEC.found-among-two: proven",
            "ORG-KRS-SET-INSTANCES-SPEC.found: proven",
            "ORG-KRS-SET-INSTANCES-SPEC.other-hits: failed",
        ]
    "#]]
    .assert_debug_eq(&statuses);
}
