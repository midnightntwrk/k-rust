//! A function application where a rule's or an equation's pattern matches a term
//! (`krs::analysis::function-in-pattern`), and a name a map key or a set element reads below one
//! (`krs::expand::unbound-name`), end to end: authored packages through `krs check`. The class
//! tests cover the computation cell of every sentence form below its root; these cover the roots
//! of the slots a rule matches, the other places a rule matches, the places the application is
//! the meaning, and the instances of a cell collection.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, Map};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("load({n})")]
    Load { n: Int },
    #[k::syntax("wrap({e})")]
    Wrap { e: KItem },
    #[k::syntax("done")]
    Done(),
}

#[k::function(partial, sort = Int, syntax = "size({a})")]
pub struct Size {
    pub a: Term<KItem>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Exp,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub stack: List,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            acc: ExpSyntax::Done(),
            env: k::map![],
            stack: k::builtin::list::empty(),
        }
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

/// A one-package workspace named `patterns` whose library is `preamble` and `source`.
fn package(root: &Path, preamble: &str, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{preamble}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"patterns\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-FUNCTION-PATTERNS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// `krs check` of the package: whether it passed, and its `error[..]` headlines with the
/// locations they point at.
fn check(target: &Path, manifest: &Path) -> (bool, Vec<String>) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args(["check", "--manifest-path"])
        .arg(manifest)
        .args(["--package", "patterns", "--definition", "main"])
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    let directory = format!("{}/", manifest.parent().unwrap().display());
    let errors = stderr
        .lines()
        .filter(|line| line.starts_with("error") || line.trim_start().starts_with("--> "))
        .map(|line| line.trim().replace(&directory, ""))
        .collect();
    (output.status.success(), errors)
}

/// Each case's package and its `krs check` outcome.
fn outcomes<const N: usize>(
    cases: [(&'static str, &str); N],
) -> [(&'static str, (bool, Vec<String>)); N] {
    outcomes_after(PREAMBLE, cases)
}

/// [`outcomes`] with each case after `preamble`.
fn outcomes_after<const N: usize>(
    preamble: &str,
    cases: [(&'static str, &str); N],
) -> [(&'static str, (bool, Vec<String>)); N] {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    cases.map(|(name, source)| {
        let manifest = package(&temporary.path().join(name), preamble, source);
        (name, check(target.path(), &manifest))
    })
}

/// A function at the root of each slot a rule or an equation matches that the class tests do not
/// generate: an anywhere rule's and a single-body rule's subject, a cell's content, and a
/// function-context cell. The class tests' term family covers a fn rule's subject root, a `for
/// Sort` clause's, and a readable and a `cells!` computation item (`terms/rule/subject-root/Size(x)`,
/// `terms/sort-rule/subject-root/..`, `terms/readable/item-root/..`, `terms/cells/item-root/..`),
/// whose messages the cases here share.
const ROOT_CASES: [(&str, &str); 5] = [
    (
        "anywhere-subject",
        "#[k::rule(anywhere, label = \"twist\")]\nfn twist(k::term![Size(x)]: Term<Int>) -> Term<Int> {\n    0\n}\n",
    ),
    (
        "single-body-subject",
        "#[k::rule(label = \"twist\")]\nfn twist(k::term![Size(k::rewrite!(x => ExpSyntax::Done()))]: Term<Int>) {}\n",
    ),
    (
        "readable-cell",
        "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    reset: { k: [Wrap(x), ..], acc: Size(x) } => { k: [..], acc: Done() };\n}\n",
    ),
    (
        "cells-cell",
        "#[k::rule(label = \"clear\")]\npub fn clear(\n    x: KItem,\n    k::cells! { k: k::configuration::KCell(ExpSyntax::Wrap(x), tail @ ..), acc: k::configuration::Cell(Size(x)), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), acc: k::configuration::Cell(ExpSyntax::Done()), ..state }\n}\n",
    ),
    (
        "function-context",
        "#[k::equation]\nfn probe(\n    x: Term<KItem>,\n    k::term![Size(x)]: Term<Int>,\n    k::cells! { acc: k::configuration::Cell(Size(x)), .. }: Machine,\n) -> Term<Int> {\n    0\n}\n",
    ),
];

#[test]
fn a_function_at_the_root_of_any_slot_a_rule_matches_is_refused() {
    let outcomes = outcomes(ROOT_CASES);
    expect_test::expect![[r#"
        [
            (
                "anywhere-subject",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable and relate it to the application in a guard (`requires`), or, to define the function, write an equation (`#[k::equation]`, or a `k::equations!` row)",
                        "--> src/lib.rs:50:19",
                    ],
                ),
            ),
            (
                "single-body-subject",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:50:19",
                    ],
                ),
            ),
            (
                "readable-cell",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:37",
                    ],
                ),
            ),
            (
                "cells-cell",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:104",
                    ],
                ),
            ),
            (
                "function-context",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:53:45",
                    ],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

#[test]
fn a_function_below_the_root_of_any_pattern_a_rule_matches_is_refused() {
    let outcomes = outcomes([
        (
            "readable-cell",
            "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    reset: { k: [Done(), ..], acc: Wrap(Size(x)) } => { k: [..], acc: Done() };\n}\n",
        ),
        (
            "cells-cell",
            "#[k::rule(label = \"clear\")]\npub fn clear(\n    x: KItem,\n    k::cells! { k: k::configuration::KCell(ExpSyntax::Done(), tail @ ..), acc: k::configuration::Cell(ExpSyntax::Wrap(Size(x))), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), acc: k::configuration::Cell(ExpSyntax::Done()), ..state }\n}\n",
        ),
        (
            "function-context",
            "#[k::equation]\nfn probe(\n    x: Term<KItem>,\n    k::term![Size(x)]: Term<Int>,\n    k::cells! { acc: k::configuration::Cell(ExpSyntax::Wrap(Size(x))), .. }: Machine,\n) -> Term<Int> {\n    0\n}\n",
        ),
        (
            "collection-function",
            "#[k::rule(label = \"count\")]\nfn count(k::term![ExpSyntax::Load(k::builtin::list::size(l))]: Term<Exp>) -> Term<Exp> {\n    ExpSyntax::Done()\n}\n",
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "readable-cell",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:41",
                    ],
                ),
            ),
            (
                "cells-cell",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:52:119",
                    ],
                ),
            ),
            (
                "function-context",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:53:61",
                    ],
                ),
            ),
            (
                "collection-function",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the builtin function `k::builtin::list::size` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`",
                        "--> src/lib.rs:50:35",
                    ],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// The application is the meaning at an equation's root (a fn's and a table row's), anywhere in a
/// simplification's and a claim's subject, in a map key whose names the pattern binds elsewhere,
/// and in a result.
#[test]
fn an_application_that_is_the_meaning_is_accepted() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let source = r"
#[k::equation]
fn size_wrap(k::term![Size(ExpSyntax::Wrap(x))]: Term<Int>) -> Term<Int> {
    Size(x)
}

#[k::simplification]
fn size_of_size(k::term![Size(ExpSyntax::Wrap(Size(x)))]: Term<Int>) -> Term<Int> {
    Size(x)
}

k::rules! {
    for Machine;
    use ExpSyntax::*;
    read: { k: [Load(n), ..], env: { Size(n) -> v, .. } } => { k: [Wrap(v), ..] };
}

k::equations! {
    for Size;

    size_done: (ExpSyntax::Done()) => 0;
}

#[k::simplification]
fn size_root(k::term![Size(x)]: Term<Int>) -> Term<Int> {
    Size(x)
}

k::claims! {
    for Machine;
    use ExpSyntax::*;
    #[k::claim(all_paths)]
    sized: { k: [Wrap(Size(x)), ..] } => { k: [..] };
    #[k::claim(all_paths)]
    sized_root: { k: [Size(x), ..] } => { k: [..] };
}
";
    let manifest = package(&temporary.path().join("accepted"), PREAMBLE, source);
    let (success, errors) = check(target.path(), &manifest);
    assert!(success, "{errors:#?}");
}

/// A map key is evaluated, so a name only a function application in a key reads binds nothing.
#[test]
fn a_name_only_a_function_in_a_map_key_reads_is_unbound() {
    let outcomes = outcomes([
        (
            "readable-builtin",
            "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    read: { k: [Done(), ..], env: { k::builtin::int::add(x, 1) -> v, .. } } => { k: [Wrap(v), ..] };\n}\n",
        ),
        (
            "readable-function",
            "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    read: { k: [Done(), ..], env: { Size(ExpSyntax::Wrap(n)) -> v, .. } } => { k: [Wrap(v), ..] };\n}\n",
        ),
        (
            "cells",
            "#[k::rule(label = \"read\")]\npub fn read(\n    n: KItem,\n    v: KItem,\n    k::cells! { k: k::configuration::KCell(ExpSyntax::Done(), tail @ ..), env: k::configuration::Cell(k::map![Size(n) -> v, ..]), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(ExpSyntax::Wrap(v), ..tail), ..state }\n}\n",
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "readable-builtin",
                (
                    false,
                    [
                        "error[krs::expand::unbound-name]: `x` is not bound in this sentence: it stands only below the builtin function `k::builtin::int::add` in a map key, and a key is evaluated to look its entry up, so the key reads `x` and binds nothing; bind `x` elsewhere in the pattern",
                        "--> src/lib.rs:52:58",
                    ],
                ),
            ),
            (
                "readable-function",
                (
                    false,
                    [
                        "error[krs::expand::unbound-name]: `n` is not bound in this sentence: it stands only below the function `Size` in a map key, and a key is evaluated to look its entry up, so the key reads `n` and binds nothing; bind `n` elsewhere in the pattern",
                        "--> src/lib.rs:52:58",
                    ],
                ),
            ),
            (
                "cells",
                (
                    false,
                    [
                        "error[krs::expand::unbound-name]: `n` is not bound in this sentence: it stands only below the function `Size` in a map key, and a key is evaluated to look its entry up, so the key reads `n` and binds nothing; bind `n` elsewhere in the pattern",
                        "--> src/lib.rs:53:116",
                    ],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// A name a key reads is bound by the rest of the pattern, in any cell order, and a name a key
/// matches as it stands binds there.
#[test]
fn a_name_a_map_key_reads_may_be_bound_elsewhere() {
    let source = r#"
k::rules! {
    for Machine;
    use ExpSyntax::*;
    after: { env: { Size(n) -> v, .. }, k: [Wrap(n), ..] } => { k: [Load(1), ..] };
    matched: { k: [Done(), ..], env: { Wrap(n) -> v, .. } } => { k: [Wrap(n), ..] };
}

#[k::rule(label = "read")]
pub fn read(
    n: Int,
    v: KItem,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Load(n), tail @ ..), env: k::configuration::Cell(k::map![k::builtin::int::add(n, 1) -> v, ..]), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(ExpSyntax::Wrap(v), ..tail), ..state }
}
"#;
    let [(_, (success, errors))] = outcomes([("bound", source)]);
    assert!(success, "{errors:#?}");
}

/// A constructor holding a set, for the set-element cases.
const BAG: &str = "#[k::constructors(sort = Exp, result = KResult)]\npub enum BagSyntax {\n    #[k::syntax(\"bag({s})\")]\n    Bag { s: k::builtin::Set },\n}\n";

/// A set is looked up by its elements as a map by its keys, so a name only a function
/// application in a set element reads binds nothing, in a fn rule's subject, a readable cell and
/// a `cells!` cell alike.
#[test]
fn a_name_only_a_function_in_a_set_element_reads_is_unbound() {
    let outcomes = outcomes([
        (
            "rule-subject",
            &format!(
                "{BAG}#[k::rule(label = \"has\")]\nfn has(BagSyntax::Bag {{ s: k::builtin::set::concat(k::builtin::set::item(Size(n)), rest) }}: Term<Exp>) -> Term<Exp> {{\n    BagSyntax::Bag {{ s: rest }}\n}}\n"
            ),
        ),
        (
            "readable",
            &format!(
                "{BAG}k::rules! {{\n    for Machine;\n    use ExpSyntax::*;\n    pick: {{ k: [Done(), ..], acc: BagSyntax::Bag {{ s: k::builtin::set::concat(k::builtin::set::item(Size(n)), rest) }} }} => {{ k: [..], acc: BagSyntax::Bag {{ s: rest }} }};\n}}\n"
            ),
        ),
        (
            "cells",
            &format!(
                "{BAG}#[k::rule(label = \"pick\")]\npub fn pick(\n    n: KItem,\n    rest: k::builtin::Set,\n    k::cells! {{ k: k::configuration::KCell(ExpSyntax::Done(), tail @ ..), acc: k::configuration::Cell(BagSyntax::Bag {{ s: k::builtin::set::concat(k::builtin::set::item(Size(n)), rest) }}), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), acc: k::configuration::Cell(BagSyntax::Bag {{ s: rest }}), ..state }}\n}}\n"
            ),
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "rule-subject",
                (
                    false,
                    [
                        "error[krs::expand::unbound-name]: `n` is not bound in this sentence: it stands only below the function `Size` in a set element, and an element is evaluated to look it up in the set, so the element reads `n` and binds nothing; bind `n` elsewhere in the pattern",
                        "--> src/lib.rs:55:79",
                    ],
                ),
            ),
            (
                "readable",
                (
                    false,
                    [
                        "error[krs::expand::unbound-name]: `n` is not bound in this sentence: it stands only below the function `Size` in a set element, and an element is evaluated to look it up in the set, so the element reads `n` and binds nothing; bind `n` elsewhere in the pattern",
                        "--> src/lib.rs:57:106",
                    ],
                ),
            ),
            (
                "cells",
                (
                    false,
                    [
                        "error[krs::expand::unbound-name]: `n` is not bound in this sentence: it stands only below the function `Size` in a set element, and an element is evaluated to look it up in the set, so the element reads `n` and binds nothing; bind `n` elsewhere in the pattern",
                        "--> src/lib.rs:58:174",
                    ],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}

/// A name a set element reads is bound by the rest of the pattern, and a name an element
/// matches as it stands binds there.
#[test]
fn a_name_a_set_element_reads_may_be_bound_elsewhere() {
    let source = format!(
        "{BAG}k::rules! {{\n    for Machine;\n    use ExpSyntax::*;\n    after: {{ acc: BagSyntax::Bag {{ s: k::builtin::set::concat(k::builtin::set::item(Size(n)), rest) }}, k: [Wrap(n), ..] }} => {{ k: [Load(1), ..], acc: BagSyntax::Bag {{ s: rest }} }};\n    matched: {{ k: [Done(), ..], acc: BagSyntax::Bag {{ s: k::builtin::set::concat(k::builtin::set::item(Wrap(n)), rest) }} }} => {{ k: [Wrap(n), ..], acc: BagSyntax::Bag {{ s: rest }} }};\n}}\n"
    );
    let [(_, (success, errors))] = outcomes([("bound", source.as_str())]);
    assert!(success, "{errors:#?}");
}

/// A configuration of a Set, a Map and a List collection, each its parent's only child.
const COLLECTIONS: &str = r#"
use k::builtin::{Int, KSequence};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("wrap({e})")]
    Wrap { e: KItem },
    #[k::syntax("done")]
    Done(),
}

#[k::function(partial, sort = Int, syntax = "size({a})")]
pub struct Size {
    pub a: Term<KItem>,
}

#[k::cell]
pub struct Pool {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub member: Member,
}

#[k::cell]
pub struct Member {
    #[k::cell]
    pub item: Exp,
}

#[k::cell]
pub struct Table {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub row: Row,
}

#[k::cell]
pub struct Row {
    #[k::cell]
    pub id: Exp,
    #[k::cell]
    pub value: Exp,
}

#[k::cell]
pub struct Queue {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub job: Job,
}

#[k::cell]
pub struct Job {
    #[k::cell]
    pub payload: Exp,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub pool: Pool,
    #[k::cell(nested)]
    pub table: Table,
    #[k::cell(nested)]
    pub queue: Queue,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            pool: Pool { member: Member { item: ExpSyntax::Done() } },
            table: Table { row: Row { id: ExpSyntax::Done(), value: ExpSyntax::Done() } },
            queue: Queue { job: Job { payload: ExpSyntax::Done() } },
        }
    }
}
"#;

/// A cell collection's instance is the cells K writes where the collection stands, which a
/// pattern matches as the collection holds them, whatever its type: a function in a child of a
/// List, a Map (its key included) or a Set collection's instance never matches and is refused
/// (decision D1), so no name stands only below one (X4 has nothing to read there).
#[test]
fn a_cell_collection_matches_the_cells_of_its_instances() {
    let outcomes = outcomes_after(
        COLLECTIONS,
        [
            (
                "list-child",
                "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    take: { k: [Wrap(n), ..], job: [Job { payload: Size(n) }, ..] } => { k: [..] };\n}\n",
            ),
            (
                "map-key",
                "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    take: { k: [Wrap(n), ..], row: { Row { id: Size(n), value: Done() }, .. } } => { k: [..] };\n}\n",
            ),
            (
                "map-value",
                "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    take: { k: [Wrap(n), ..], row: { Row { id: n, value: Size(n) }, .. } } => { k: [..] };\n}\n",
            ),
            (
                "set-instance",
                "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    take: { k: [Wrap(n), ..], member: { Member { item: Size(n) }, .. } } => { k: [..] };\n}\n",
            ),
            (
                "constructor",
                "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    take: { k: [Wrap(n), ..], member: { Member { item: Wrap(n) }, .. } } => { k: [..] };\n}\n",
            ),
        ],
    );
    expect_test::expect![[r#"
        [
            (
                "list-child",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands in a collection's value or element, which the pattern matches against the values the collection holds; a function application denotes the value evaluation produces, and those values have their functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`); only a map read's key and a set's element, `set::item(..)`, are looked up by the value a function there computes",
                        "--> src/lib.rs:88:52",
                    ],
                ),
            ),
            (
                "map-key",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands in a collection's value or element, which the pattern matches against the values the collection holds; a function application denotes the value evaluation produces, and those values have their functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`); only a map read's key and a set's element, `set::item(..)`, are looked up by the value a function there computes",
                        "--> src/lib.rs:88:48",
                    ],
                ),
            ),
            (
                "map-value",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands in a collection's value or element, which the pattern matches against the values the collection holds; a function application denotes the value evaluation produces, and those values have their functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`); only a map read's key and a set's element, `set::item(..)`, are looked up by the value a function there computes",
                        "--> src/lib.rs:88:58",
                    ],
                ),
            ),
            (
                "set-instance",
                (
                    false,
                    [
                        "error[krs::analysis::function-in-pattern]: the function `Size` stands in a collection's value or element, which the pattern matches against the values the collection holds; a function application denotes the value evaluation produces, and those values have their functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`); only a map read's key and a set's element, `set::item(..)`, are looked up by the value a function there computes",
                        "--> src/lib.rs:88:56",
                    ],
                ),
            ),
            (
                "constructor",
                (
                    true,
                    [],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}
