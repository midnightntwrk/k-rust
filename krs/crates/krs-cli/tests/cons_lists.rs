//! Bracket list notation for cons lists (F6) end to end: a package written
//! with `[a, b, rest @ ..]` and `[e, ..rest]` emits exactly the K of the same
//! package written with the nested constructor terms they denote, for a
//! `#[k::cons_list]` enum (a KEVM-shaped word stack and KMIR-shaped
//! projections) and a `#[k::syntax_list]` sort, in a function body's
//! `match`, `k::equations!` rows, an equation result, a constructor field,
//! readable records, and a claim; a readable record's anonymous `..` is one
//! shared rest; `krs expand` writes the constructors; and malformed lists,
//! lists at positions that are no cons list, and cons-list enums of the
//! wrong shape are errors.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A package with one placeholder `{NAME}` per list; [`SPELLINGS`] fills each
/// with list notation or with the constructor terms it denotes.
const SOURCE: &str = r#"
use k::builtin::{Int, KSequence, int};
use k::{KItem, KResult, Term};

k::sorts! {
    WordStack: KItem;
    Projection: KItem;
    Projections: KItem;
    Op: KItem;
}

/// KEVM's word stack.
#[k::constructors(sort = WordStack, result = KResult)]
#[k::cons_list]
#[k::precedence((StackEmpty, StackCons))]
pub enum Stack {
    #[k::syntax(".WordStack")]
    StackEmpty(),
    #[k::syntax("{head} : {tail}")]
    StackCons { head: Int, tail: WordStack },
}

#[k::constructors(sort = Projection, result = KResult)]
pub enum ProjectionElem {
    #[k::syntax("deref")]
    Deref,
    #[k::syntax("field({index}, {ty})")]
    Field { index: Int, ty: Int },
}

/// KMIR's projections.
#[k::constructors(sort = Projections, result = KResult)]
#[k::cons_list]
pub enum ProjectionList {
    #[k::syntax("projectionsCons({head}, {tail})")]
    ProjectionsCons { head: Projection, tail: Projections },
    #[k::syntax(".Projections")]
    ProjectionsEmpty(),
}

#[k::syntax_list(separator = ",")]
pub enum Operands {
    Cons { head: Int, tail: Operands },
    Nil(),
}

#[k::constant]
pub const WORD: Int = 0x20;

#[k::constructors(sort = Op, result = KResult)]
pub enum Instr {
    #[k::syntax("ADD")]
    Add,
    #[k::syntax("SWAP")]
    Swap,
    #[k::syntax("RESET")]
    Reset,
    #[k::syntax("PAIR")]
    Pair,
    #[k::syntax("PUSH({value})")]
    Push { value: Int },
    #[k::syntax("LOAD({at})")]
    Load { at: Projections },
    #[k::syntax("BUMP")]
    Bump,
}

#[k::function(total, internal)]
pub fn Chop(value: Term<Int>) -> Term<Int> {
    value % 256
}

#[k::function(total, internal)]
pub fn Depth(stack: Term<WordStack>) -> Term<Int> {
    match stack {
        {EMPTY_PATTERN} => 0,
        {POP_PATTERN} => 1 + Depth(rest),
    }
}

#[k::function(total, internal)]
pub fn SumTwo(stack: Term<WordStack>) -> Term<Int> {
    match stack {
        {TWO_PATTERN} => a + b,
        _ => 0,
    }
}

#[k::function(total, internal)]
pub fn Words(n: Term<Int>) -> Term<WordStack> {
    k::term![{WORDS}]
}

#[k::function(total, internal)]
pub fn Top(stack: Term<WordStack>) -> Term<Int>;

k::equations! {
    for Top;
    top: {TOP_ROW} => a;
    #[k::equation(owise)]
    top_empty: _ => 0;
}

#[k::function(total, internal)]
pub fn Indices(projections: Term<Projections>) -> Term<Int>;

k::equations! {
    for Indices;
    use ProjectionElem::*;
    indices_deref: {DEREF_ROW} => Indices(rest);
    indices_field: {FIELD_ROW} => index + Indices(rest);
    indices_end: {PROJECTIONS_END} => 0;
}

#[k::function(total, internal)]
pub fn Arity(operands: Term<Operands>) -> Term<Int> {
    match operands {
        {OPERANDS_END} => 0,
        {OPERANDS_CONS} => 1 + Arity(rest),
    }
}

#[k::function(total, internal)]
pub fn Pairs(a: Term<Int>, b: Term<Int>) -> Term<Operands> {
    k::term![{OPERANDS_PAIR}]
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(name = "wordStack")]
    pub word_stack: WordStack,
    #[k::cell]
    pub projections: Projections,
    #[k::cell]
    pub gas: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Op) -> Self {
        Self {
            k: k::k![pgm],
            word_stack: Stack::StackEmpty(),
            projections: ProjectionList::ProjectionsEmpty(),
            gas: 0,
        }
    }
}

k::rules! {
    for Machine;
    use Instr::*;

    add: { k: [Add(), ..], word_stack: {ADD_BEFORE} } => { k: [..], word_stack: {ADD_AFTER} };
    swap: { word_stack: {SWAP_BEFORE}, k: [Swap(), ..] } => { k: [..], word_stack: {SWAP_AFTER} };
    reset: { k: [Reset(), ..], word_stack: _ } => { k: [..], word_stack: {EMPTY} };
    pair: { k: [Pair(), ..], word_stack: {EXACT_TWO} } => { k: [..], word_stack: {SWAPPED_TWO} };
    push: { k: [Push(v), ..], word_stack: s } => { k: [..], word_stack: {PUSHED} };
    load: { k: [Load({LOAD_AT}), ..] } => { k: [..] };
    bump: { k: [Bump(), ..], projections: {BUMP_BEFORE} } => { k: [..], projections: {BUMP_AFTER} };
}

k::claims! {
    for Machine;
    use Instr::*;

    #[k::claim(all_paths)]
    add_claim: { k: [Add()], word_stack: {CLAIM_BEFORE} } => { k: [], word_stack: {CLAIM_AFTER} };
}
"#;

/// Each placeholder of [`SOURCE`], the constructor terms it is written with,
/// and the list notation that denotes them.
const SPELLINGS: &[(&str, &str, &str)] = &[
    ("EMPTY_PATTERN", "Stack::StackEmpty()", "[]"),
    ("POP_PATTERN", "Stack::StackCons(_, rest)", "[_, rest @ ..]"),
    (
        "TWO_PATTERN",
        "Stack::StackCons(a, Stack::StackCons(b, _))",
        "[a, b, ..]",
    ),
    (
        "WORDS",
        "Stack::StackCons(WORD, Stack::StackCons(n * WORD, Stack::StackCons(WORD + 1, Stack::StackEmpty())))",
        "[WORD, n * WORD, WORD + 1]",
    ),
    ("TOP_ROW", "Stack::StackCons(a, _)", "[a, ..]"),
    (
        "DEREF_ROW",
        "ProjectionList::ProjectionsCons(Deref(), rest)",
        "[Deref(), rest @ ..]",
    ),
    (
        "FIELD_ROW",
        "ProjectionList::ProjectionsCons(Field { index, .. }, rest)",
        "[Field { index, .. }, rest @ ..]",
    ),
    (
        "PROJECTIONS_END",
        "ProjectionList::ProjectionsEmpty()",
        "[]",
    ),
    ("OPERANDS_END", "Operands::Nil()", "[]"),
    ("OPERANDS_CONS", "Operands::Cons(_, rest)", "[_, rest @ ..]"),
    (
        "OPERANDS_PAIR",
        "Operands::Cons(a, Operands::Cons(b, Operands::Nil()))",
        "[a, b]",
    ),
    (
        "ADD_BEFORE",
        "Stack::StackCons(a, Stack::StackCons(b, rest))",
        "[a, b, rest @ ..]",
    ),
    (
        "ADD_AFTER",
        "Stack::StackCons(Chop(a + b), rest)",
        "[Chop(a + b), ..rest]",
    ),
    (
        "SWAP_BEFORE",
        "Stack::StackCons(a, Stack::StackCons(b, rest))",
        "[a, b, rest @ ..]",
    ),
    (
        "SWAP_AFTER",
        "Stack::StackCons(b, Stack::StackCons(a, rest))",
        "[b, a, ..rest]",
    ),
    ("EMPTY", "Stack::StackEmpty()", "[]"),
    (
        "EXACT_TWO",
        "Stack::StackCons(a, Stack::StackCons(b, Stack::StackEmpty()))",
        "[a, b]",
    ),
    (
        "SWAPPED_TWO",
        "Stack::StackCons(b, Stack::StackCons(a, Stack::StackEmpty()))",
        "[b, a]",
    ),
    ("PUSHED", "Stack::StackCons(v, s)", "[v, ..s]"),
    (
        "LOAD_AT",
        "ProjectionList::ProjectionsCons(ProjectionElem::Deref(), _)",
        "[ProjectionElem::Deref(), ..]",
    ),
    (
        "BUMP_BEFORE",
        "ProjectionList::ProjectionsCons(f @ ProjectionElem::Field { index: i, .. }, rest)",
        "[f @ ProjectionElem::Field { index: i, .. }, rest @ ..]",
    ),
    (
        "BUMP_AFTER",
        "ProjectionList::ProjectionsCons(ProjectionElem::Field { index: i + 1, ..f }, rest)",
        "[ProjectionElem::Field { index: i + 1, ..f }, ..rest]",
    ),
    (
        "CLAIM_BEFORE",
        "Stack::StackCons(1, Stack::StackCons(2, rest))",
        "[1, 2, rest @ ..]",
    ),
    ("CLAIM_AFTER", "Stack::StackCons(3, rest)", "[3, ..rest]"),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes the package `name` with `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        format!("#![allow(unused_imports)]\n{source}"),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CONS-LISTS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// [`SOURCE`] with each placeholder written as list notation or as the
/// constructor terms.
fn spelled(lists: bool) -> String {
    SPELLINGS
        .iter()
        .fold(SOURCE.to_owned(), |source, (name, constructors, list)| {
            let placeholder = format!("{{{name}}}");
            assert!(source.contains(&placeholder), "{placeholder} is unused");
            source.replace(&placeholder, if lists { list } else { constructors })
        })
}

/// The emitted `.k` files of a package, the definition and its spec
/// module, by name.
fn definition_k(target: &Path, root: &Path, name: &str, source: &str) -> String {
    let manifest = package(root, name, source);
    let output = root.join("emitted");
    let (success, _, stderr) = krs(
        target,
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let mut files = fs::read_dir(&output)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
        .collect::<Vec<_>>();
    files.sort();
    files.iter().fold(String::new(), |mut emitted, path| {
        let name = path.file_name().unwrap().to_string_lossy();
        writeln!(emitted, "// {name}").unwrap();
        emitted.push_str(&fs::read_to_string(path).unwrap());
        emitted
    })
}

#[test]
fn list_notation_emits_the_k_of_the_constructors_it_denotes() {
    let target = shared_fixture_target();
    let constructors = temp_dir();
    let lists = temp_dir();
    let constructor_k = definition_k(target.path(), constructors.path(), "lists", &spelled(false));
    let list_k = definition_k(target.path(), lists.path(), "lists", &spelled(true));
    assert_eq!(list_k, constructor_k);
    for sentence in [
        "<wordStack> A:Int : B:Int : Rest:WordStack => chop ( A:Int +Int B:Int ) : Rest:WordStack </wordStack>",
        "rule depth ( _ : Rest:WordStack ) => 1 +Int depth ( Rest:WordStack )",
        "rule pairs ( A:Int , B:Int ) => A:Int , B:Int , .Operands",
        "<projections> projectionsCons ( field ( I:Int , Krs_UpdateFTy:Int ) , Rest:Projections ) => projectionsCons ( field ( I:Int +Int 1 , Krs_UpdateFTy:Int ) , Rest:Projections ) </projections>",
        "<wordStack> 1 : 2 : Rest:WordStack => 3 : Rest:WordStack </wordStack>",
    ] {
        assert!(list_k.contains(sentence), "{sentence}:\n{list_k}");
    }
}

/// A readable record's anonymous `..` on a cons-list cell is one rest, the
/// same on both sides, like the computation cell's: the rule is the one
/// written with a named rest, whose binder is the generated rest variable.
#[test]
fn a_record_cells_anonymous_rest_is_one_shared_rest() {
    let target = shared_fixture_target();
    let named = temp_dir();
    let anonymous = temp_dir();
    let rules = |add: &str, swap: &str| {
        let source = spelled(true);
        let (named_add, named_swap) = (
            "add: { k: [Add(), ..], word_stack: [a, b, rest @ ..] } => { k: [..], word_stack: [Chop(a + b), ..rest] };",
            "swap: { word_stack: [a, b, rest @ ..], k: [Swap(), ..] } => { k: [..], word_stack: [b, a, ..rest] };",
        );
        assert!(source.contains(named_add) && source.contains(named_swap));
        source.replace(named_add, add).replace(named_swap, swap)
    };
    let named_k = definition_k(
        target.path(),
        named.path(),
        "lists",
        &rules(
            "add: { k: [Add(), ..], word_stack: [a, b, krs_rest @ ..] } => { k: [..], word_stack: [Chop(a + b), ..krs_rest] };",
            "swap: { word_stack: [a, b, krs_rest @ ..], k: [Swap(), ..] } => { k: [..], word_stack: [b, a, ..krs_rest] };",
        ),
    );
    let anonymous_k = definition_k(
        target.path(),
        anonymous.path(),
        "lists",
        &rules(
            "add: { k: [Add(), ..], word_stack: [a, b, ..] } => { k: [..], word_stack: [Chop(a + b), ..] };",
            "swap: { word_stack: [a, b, ..], k: [Swap(), ..] } => { k: [..], word_stack: [b, a, ..] };",
        ),
    );
    assert_eq!(
        anonymous_k,
        named_k.replace("KrsRest:WordStack", "Krs_RestWordStack:WordStack")
    );
    assert!(
        anonymous_k.contains(
            "<wordStack> A:Int : B:Int : Krs_RestWordStack:WordStack => B:Int : A:Int : Krs_RestWordStack:WordStack </wordStack>"
        ),
        "{anonymous_k}"
    );
}

#[test]
fn expand_writes_the_constructors_list_notation_denotes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "lists", &spelled(true));
    let (success, stdout, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let start = stdout
        .find("pub fn bump(")
        .expect("the readable rule is written");
    let start = stdout[..start].rfind("#[k::rule(").unwrap();
    let end = start + stdout[start..].find("\n}\n").unwrap() + 3;
    expect_test::expect![[r#"
        #[k::rule(label = "bump")]
        pub fn bump(
            i: k::Term<k::builtin::Int>,
            f_ty: k::Term<k::builtin::Int>,
            rest: crate::Projections,
            k::cells! {
                k : k::configuration::KCell(crate ::Instr::Bump(), tail @ ..), projections :
                k::configuration::Cell(crate ::ProjectionList::ProjectionsCons(crate
                ::ProjectionElem::Field(i, f_ty), rest)), state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(..tail), projections : k::configuration::Cell(crate
                ::ProjectionList::ProjectionsCons(crate
                ::ProjectionElem::Field(k::builtin::int::add(i, 1), f_ty), rest)), ..state
            }
        }
    "#]]
    .assert_eq(&stdout[start..end]);
}

/// The first `error[..]` headline and its message of `krs check` on a
/// package whose last item is `item`.
fn check_error(target: &Path, item: &str) -> String {
    let temporary = temp_dir();
    let source = spelled(true) + item;
    let manifest = package(temporary.path(), "lists", &source);
    let (success, _, stderr) = krs(target, &manifest, "check", &[]);
    assert!(!success, "{item} was accepted");
    stderr
        .lines()
        .find(|line| line.starts_with("error["))
        .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
        .to_owned()
}

#[test]
fn malformed_and_misplaced_lists_are_errors() {
    let target = shared_fixture_target();
    let errors = [
        // A list is matched from its front.
        "#[k::function(total, internal)]
         pub fn Last(stack: Term<WordStack>) -> Term<Int> {
             match stack { [.., x] => x, _ => 0 }
         }",
        "#[k::function(total, internal)]
         pub fn Middle(stack: Term<WordStack>) -> Term<Int> {
             match stack { [a, .., b] => a + b, _ => 0 }
         }",
        "#[k::function(total, internal)]
         pub fn Any(stack: Term<WordStack>) -> Term<Int> {
             match stack { [..] => 1 }
         }",
        // An anonymous rest is shared only in a readable record cell.
        "#[k::function(total, internal)]
         pub fn Grow(stack: Term<WordStack>) -> Term<WordStack> { k::term![[1, ..]] }",
        // A readable record cell's rest is one rest on both sides.
        "k::rules! {
             for Machine;
             drop_rest: { k: [Instr::Reset(), ..], word_stack: [a, ..] } => { k: [..], word_stack: [a] };
         }",
        "k::rules! {
             for Machine;
             back: { k: [Instr::Reset(), ..], word_stack: [.., a] } => { k: [..] };
         }",
        // A position whose sort is no cons list.
        "#[k::function(total, internal)]
         pub fn NotAList(n: Term<Int>) -> Term<Int> { k::term![[n, n]] }",
        "k::rules! {
             for Machine;
             spend: { k: [Instr::Reset(), ..], gas: [n, ..] } => { k: [..], gas: [0, ..] };
         }",
        // The computation cell's rest is anonymous.
        "k::rules! {
             for Machine;
             named: { k: [x, rest @ ..] } => { k: [..rest] };
         }",
    ]
    .map(|item| check_error(target.path(), item));
    expect_test::expect![[r#"
        [
            "error[krs::syntax::invalid-list-notation]: `..` may only end a list: a cons list is matched and built from its front, so its back is no constructor pattern; name the elements before the rest",
            "error[krs::syntax::invalid-list-notation]: `..` may only end a list: a cons list is matched and built from its front, so its back is no constructor pattern; name the elements before the rest",
            "error[krs::syntax::invalid-list-notation]: `[..]` and `[rest @ ..]` name no element: the first matches any list, so write `_`, and the second is the binder `rest` itself",
            "error[krs::syntax::invalid-list-notation]: an anonymous `..` keeps the rest only in a readable record cell, where the pattern's `..` matched it; elsewhere name it: `rest @ ..` in the pattern and `..rest` in the result",
            "error[krs::syntax::invalid-list-notation]: the pattern's `..` keeps the rest of the list, so the result ends in `..` too; to drop or move the rest, name it: `rest @ ..`",
            "error[krs::syntax::invalid-list-notation]: `..` may only end a list: a cons list is matched from its front, so its back is no constructor pattern",
            "error[krs::analysis::invalid-list-notation]: list notation builds a cons list, but this position has sort `Int`, which is not one: a cons list is a `#[k::syntax_list]` sort or the sort of a `#[k::cons_list]` constructors enum",
            "error[krs::analysis::invalid-list-notation]: the cell `gas` holds `Int`, which is not a cons list: a bracketed cell value is the computation cell's items, a List collection's instances, or the elements of a cell whose sort is a `#[k::syntax_list]` sort or a `#[k::cons_list]` enum's",
            "error[krs::collect::invalid-configuration]: `k` is the computation cell, whose rest is the anonymous `..`; a named rest (`rest @ ..`, `..rest`) belongs to a cons-list cell",
        ]
    "#]].assert_debug_eq(&errors);
}

/// A `#[k::cons_list]` enum has an empty constructor and a cons whose tail is
/// the list itself, and no sort is built by two cons lists.
#[test]
fn cons_list_enums_of_the_wrong_shape_are_errors() {
    let target = shared_fixture_target();
    let errors = [
        "k::sorts! { Chain: KItem; }
         #[k::constructors(sort = Chain, result = KResult)]
         #[k::cons_list]
         pub enum OneField {
             #[k::syntax(\"nil\")]
             PNil(),
             #[k::syntax(\"one({a})\")]
             POne { a: Int },
         }",
        "k::sorts! { Chain: KItem; }
         #[k::constructors(sort = Chain, result = KResult)]
         #[k::cons_list]
         pub enum TwoEmpty {
             #[k::syntax(\"nil\")]
             PNil(),
             #[k::syntax(\"none\")]
             PNone(),
         }",
        "k::sorts! { Chain: KItem; }
         #[k::constructors(sort = Chain, result = KResult)]
         #[k::cons_list]
         #[k::precedence((PNil, PCons, PMore))]
         pub enum Three {
             #[k::syntax(\"nil\")]
             PNil(),
             #[k::syntax(\"{h} ; {t}\")]
             PCons { h: Int, t: Chain },
             #[k::syntax(\"more\")]
             PMore(),
         }",
        "k::sorts! { Chain: KItem; }
         #[k::constructors(sort = Chain, result = KResult)]
         #[k::cons_list]
         pub enum IntTail {
             #[k::syntax(\"{h} ; {t}\")]
             PCons { h: Int, t: Int },
             #[k::syntax(\"nil\")]
             PNil(),
         }",
        "#[k::constructors(sort = WordStack, result = KResult)]
         #[k::cons_list]
         pub enum SecondStack {
             #[k::syntax(\"{h} :: {t}\")]
             SecondCons { h: Int, t: WordStack },
             #[k::syntax(\"nil2\")]
             SecondEmpty(),
         }",
    ]
    .map(|item| check_error(target.path(), item));
    expect_test::expect![[r#"
        [
            "error[krs::syntax::invalid-cons-list]: `POne` has 1 field: a cons list has one constructor with no field, the empty list, and one with two, the head and the tail",
            "error[krs::syntax::invalid-cons-list]: `PNil` and `PNone` both have no field: a cons list has one constructor with no field, the empty list, and one with two, the head and the tail",
            "error[krs::syntax::invalid-cons-list]: `PMore` is a third constructor of `Three`: a cons list has one constructor with no field, the empty list, and one with two, the head and the tail, and nothing else",
            "error[krs::analysis::invalid-cons-list]: the tail `t` of `PCons` has sort `Int`, but a cons list's tail is the list itself, `Chain`",
            "error[krs::analysis::invalid-cons-list]: `WordStack` is built by two cons lists, `SecondCons` and `StackCons`, so list notation at `WordStack` would not say which; keep `#[k::cons_list]` on one enum",
        ]
    "#]].assert_debug_eq(&errors);
}

/// A configuration whose computation cell is not called `k`, matched after
/// the stack, reads like one that is: the collector gives the computation
/// cell the head and the stack its list (`KWasm`'s `instrs` and `valstack`).
#[test]
fn the_configuration_says_which_bracketed_cell_is_the_computation_cell() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let source = r#"
use k::builtin::{Int, KSequence};
use k::{KItem, KResult};

k::sorts! {
    ValStack: KItem;
    Instruction: KItem;
}

#[k::constructors(sort = ValStack, result = KResult)]
#[k::cons_list]
#[k::precedence((ValCons, ValEmpty))]
pub enum Vals {
    #[k::syntax("{head} : {tail}")]
    ValCons { head: Int, tail: ValStack },
    #[k::syntax(".ValStack")]
    ValEmpty(),
}

#[k::constructors(sort = Instruction, result = KResult)]
pub enum Instr {
    #[k::syntax("add")]
    Add,
    #[k::syntax("drop")]
    Drop,
}

#[k::configuration]
pub struct Machine {
    #[k::cell(name = "instrs")]
    pub instrs: KSequence,
    #[k::cell(name = "valstack")]
    pub valstack: ValStack,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: KSequence) -> Self {
        Self { instrs: k::k![program], valstack: Vals::ValEmpty() }
    }
}

k::rules! {
    for Machine;
    use Instr::*;

    add: { valstack: [a, b, ..], instrs: [Add(), ..] } => { valstack: [a + b, ..], instrs: [..] };
    drop: { instrs: [Drop(), ..], valstack: [_, ..] } => { instrs: [..], valstack: [..] };
    #[k::rule(priority = 100)]
    double: { valstack: [a, ..] } => { valstack: [a, a, ..] };
}
"#;
    let definition = definition_k(target.path(), temporary.path(), "machine", source);
    for sentence in [
        "<instrs> add => .K ... </instrs>\n    <valstack> A:Int : B:Int : Krs_RestValstack:ValStack => A:Int +Int B:Int : Krs_RestValstack:ValStack </valstack>",
        "<instrs> drop => .K ... </instrs>\n    <valstack> _ : Krs_RestValstack:ValStack => Krs_RestValstack:ValStack </valstack>",
        "rule [double]:\n    <valstack> A:Int : Krs_RestValstack:ValStack => A:Int : A:Int : Krs_RestValstack:ValStack </valstack>",
    ] {
        assert!(definition.contains(sentence), "{sentence}:\n{definition}");
    }
}
