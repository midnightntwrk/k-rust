//! Index reads and collection methods (`m[k]`, `l[i]`, `m.contains_key(k)`,
//! `s.union(t)`) end to end: a package written with them emits exactly the K
//! of the same package written with the calls they denote, in a function
//! body, an equation table and an equation fn, a readable rule (a computed
//! key, a guard, a result, a typed map), a rule fn, a claim, and an
//! initializer; `krs expand` writes the calls; and a receiver that chooses no
//! collection, a method its collection lacks, a malformed method, and an
//! index or a method in a pattern are errors.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A package with one placeholder `{NAME}` per term; [`SPELLINGS`] fills each
/// with a call or with the notation that denotes it.
const SOURCE: &str = r#"
use k::builtin::{Bool, Int, KSequence, List, Map, Set, int, list, map, set};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("visit({n})")]
    Visit { n: Int },
    #[k::syntax("drop({n})")]
    Drop { n: Int },
    #[k::syntax("peek")]
    Peek,
    #[k::syntax("tally")]
    Tally,
}

#[k::function(total, internal)]
pub fn Sizes(m: Term<Map>, l: Term<List>, s: Term<Set>) -> Term<Int> {
    k::term![{SIZES}]
}

#[k::function(total, internal)]
pub fn Covered(m: Term<Map>, s: Term<Set>, t: Term<Set>) -> Term<Bool> {
    k::term![{COVERED}]
}

#[k::function(total, internal)]
pub fn Listed(m: Term<Map>, s: Term<Set>) -> Term<Int> {
    k::term![{LISTED}]
}

/// A receiver and an operand a `let` binds have their values' sorts.
#[k::function(total, internal)]
pub fn LetBound(m: Term<Map>, a: Term<Int>) -> Term<Int> {
    k::term![int::add({LET_SIZE}, {LET_DOUBLE})]
}

#[k::function(partial, internal)]
pub fn Lookup(m: Term<Map>, key: Term<Int>) -> Term<Int>;

k::equations! {
    for Lookup;
    lookup: (m, key) => {LOOKUP};
}

#[k::function(partial, internal)]
pub fn Last(l: Term<List>) -> Term<Int>;

#[k::equation]
fn last(k::term![Last(l)]: Term<Int>) -> Term<Int> {
    {LAST}
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub stack: List,
    #[k::cell]
    pub seen: Set,
    #[k::cell]
    pub counts: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            env: {INIT_ENV},
            stack: {INIT_STACK},
            seen: set::empty(),
            counts: map::empty(),
        }
    }
}

k::rules! {
    for Machine;
    use ExpSyntax::*;

    #[k::requires({VISIT_REQUIRES})]
    visit: { k: [Visit(n), ..], env: e, stack: st, seen: s, counts: c } => {
        k: [..],
        env: {VISIT_ENV},
        stack: {VISIT_STACK},
        seen: {VISIT_SEEN},
        counts: {VISIT_COUNTS},
    };
    // The key is computed from the stack, which another cell binds.
    peek: { k: [Peek(), ..], env: { {PEEK_KEY} -> v, .. }, stack: st } => { k: [v, ..] };
}

#[k::rule(label = "drop", priority = 60)]
fn drop(
    n: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Drop(n), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell({DROP_ENV}),
        ..state
    }
}

#[k::claim(all_paths, label = "drop-claim")]
#[k::requires({CLAIM_REQUIRES})]
fn drop_claim(
    n: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Drop(n), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell({CLAIM_ENV}),
        ..state
    }
}
"#;

/// Each placeholder of [`SOURCE`], the calls it is written with, and the
/// notation that denotes them. Together they write every row of the method
/// table, the index of a `Map` and of a `List`, and both methods whose
/// receiver is the call's second argument.
const SPELLINGS: &[(&str, &str, &str)] = &[
    (
        "SIZES",
        "map::size(m) + list::size(l) + set::size(s)",
        "m.len() + l.len() + s.len()",
    ),
    (
        "COVERED",
        "set::is_subset(map::keys(m), set::intersect(set::difference(set::union(s, t), s), t))",
        "m.keys().is_subset(s.union(t).difference(s).intersection(t))",
    ),
    (
        "LISTED",
        "list::size(map::keys_list(m)) + list::size(map::values(m)) + list::size(set::to_list(s))",
        "m.keys_list().len() + m.values().len() + s.to_list().len()",
    ),
    ("LOOKUP", "map::get(m, key)", "m[key]"),
    ("LAST", "list::get(l, -1)", "l[-1]"),
    (
        "INIT_ENV",
        "map::update(map::empty(), 1, 2)",
        "map::empty().update(1, 2)",
    ),
    (
        "INIT_STACK",
        "list::update(list::item(3), 0, 4)",
        "list::item(3).update(0, 4)",
    ),
    (
        "VISIT_REQUIRES",
        "map::in_keys(n, e) && list::contains(n, st) && !set::contains(n, s)",
        "e.contains_key(n) && st.contains(n) && !s.contains(n)",
    ),
    (
        "VISIT_ENV",
        "map::update_all(map::remove_all(map::remove(map::update(e, n, map::get_or_default(e, n, 0)), 0), s), e)",
        "e.update(n, e.get_or(n, 0)).without(0).without_all(s).extend(e)",
    ),
    ("VISIT_STACK", "list::update(st, 0, n)", "st.update(0, n)"),
    (
        "VISIT_SEEN",
        "set::union(s, set::item(n))",
        "s.union(set::item(n))",
    ),
    (
        "VISIT_COUNTS",
        "map::update(c, n, map::get(c, n) + 1)",
        "c.update(n, c[n] + 1)",
    ),
    ("PEEK_KEY", "list::size(st)", "st.len()"),
    (
        "LET_SIZE",
        "{ let n = m; map::size(n) }",
        "{ let n = m; n.len() }",
    ),
    (
        "LET_DOUBLE",
        "{ let b = a; int::add(b, b) }",
        "{ let b = a; b + b }",
    ),
    ("DROP_ENV", "map::remove(e, n)", "e.without(n)"),
    ("CLAIM_REQUIRES", "map::in_keys(n, e)", "e.contains_key(n)"),
    (
        "CLAIM_ENV",
        "map::update(e, n, map::get(e, n))",
        "e.update(n, e[n])",
    ),
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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-COLLECTIONS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// [`SOURCE`] with each placeholder written with notation or with calls.
fn spelled(notation: bool) -> String {
    SPELLINGS
        .iter()
        .fold(SOURCE.to_owned(), |source, (name, call, written)| {
            let placeholder = format!("{{{name}}}");
            assert!(source.contains(&placeholder), "{placeholder} is unused");
            source.replace(&placeholder, if notation { written } else { call })
        })
}

/// The emitted `.k` files of a package, by name.
fn emitted_k(target: &Path, root: &Path, source: &str) -> Vec<(String, String)> {
    let manifest = package(root, "collections", source);
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
        .map(|path| {
            (
                path.file_name().unwrap().to_string_lossy().into_owned(),
                fs::read_to_string(&path).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    files.sort();
    files
}

#[test]
fn collection_notation_emits_the_k_of_the_calls_it_denotes() {
    let target = shared_fixture_target();
    let calls = temp_dir();
    let notation = temp_dir();
    let call_k = emitted_k(target.path(), calls.path(), &spelled(false));
    let notation_k = emitted_k(target.path(), notation.path(), &spelled(true));
    assert_eq!(notation_k, call_k);
    let sentences = notation_k
        .iter()
        .flat_map(|(_, text)| text.lines())
        .filter(|line| {
            let line = line.trim_start();
            line.starts_with("rule ")
                || line.starts_with("<env>")
                || line.starts_with("<stack>")
                || line.starts_with("<seen>")
                || line.starts_with("<counts>")
                || line.starts_with("<k>")
                || line.starts_with("requires")
        })
        .map(str::trim)
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r#"
        <k> $PGM:Exp </k>
        <env> .Map [ 1 <- 2 ] </env>
        <stack> ListItem(3) [ 0 <- 4 ] </stack>
        <seen> .Set </seen>
        <counts> .Map </counts>
        rule [drop]:
        <k> drop ( N:Int ) ~> Tail:K => .K ~> Tail:K </k>
        <env> E:Map => E:Map [ N:Int <- undef ] </env>
        rule listed ( M:Map , S:Set ) => (size(keys_list(M:Map)) +Int size(values(M:Map))) +Int size(Set2List(S:Set)) [label(krsRule_615b3d82a26367d2a7aa05d0)]
        rule last ( L:List ) => {L:List [ -1 ]}:>Int [label(krsRule_7d21ad45cc2a73edb122c2f5)]
        rule covered ( M:Map , S:Set , T:Set ) => keys(M:Map) <=Set intersectSet((S:Set |Set T:Set) -Set S:Set, T:Set) [label(krsRule_8be4fdb3e54ee1b9ecb3d4a2)]
        rule lookup ( M:Map , Key:Int ) => {M:Map [ Key:Int ]}:>Int [label(krsRule_ca9c6cb787329cb196b90848)]
        rule sizes ( M:Map , L:List , S:Set ) => (size(M:Map) +Int size(L:List)) +Int size(S:Set) [label(krsRule_cc124f9a8f35c9e67f745b2e)]
        rule letBound ( M:Map , A:Int ) => ( #let N:Map = M:Map #in size(N:Map) ) +Int ( #let B:Int = A:Int #in B:Int +Int B:Int ) [label(krsRule_ece27c839115a2c3e2b7ad22)]
        rule [peek]:
        <k> peek => V:KItem ... </k>
        <env> size(St:List) |-> V:KItem ... </env>
        <stack> St:List </stack>
        rule [visit]:
        <k> visit ( N:Int ) => .K ... </k>
        <env> E:Map => updateMap(removeAll(E:Map [ N:Int <- {E:Map [ N:Int ] orDefault 0}:>KItem ] [ 0 <- undef ], S:Set), E:Map) </env>
        <stack> St:List => St:List [ 0 <- N:Int ] </stack>
        <seen> S:Set => S:Set |Set SetItem(N:Int) </seen>
        <counts> C:Map => C:Map [ N:Int <- {C:Map [ N:Int ]}:>Int +Int 1 ] </counts>
        requires (N:Int in_keys(E:Map) andThenBool N:Int in St:List) andThenBool (notBool N:Int in S:Set)
        requires "definition.k"
        <k> drop ( N:Int ) ~> Tail:K => .K ~> Tail:K </k>
        <env> E:Map => E:Map [ N:Int <- {E:Map [ N:Int ]}:>KItem ] </env>
        requires N:Int in_keys(E:Map)"#]].assert_eq(&sentences);
}

/// A readable rule whose result binds a receiver with `let`: `krs expand`
/// writes a readable result's `let` into a `cells!` rule, which refuses it
/// (finding S0-17), so this rule stays out of [`SOURCE`], which the expansion
/// test reads.
const LET_RESULT: (&str, &str) = (
    "{ let l = list::item(1); list::update(st, 0, list::size(l)) }",
    "{ let l = list::item(1); st.update(0, l.len()) }",
);

/// A receiver and an operand a `let` binds have their values' sorts, so they
/// choose as the value would: in a fn body (`LetBound`) and in a readable
/// rule's result.
#[test]
fn a_let_bound_receiver_chooses_as_its_value() {
    let target = shared_fixture_target();
    let rule = |stack: &str| {
        format!(
            "k::rules! {{ for Machine; use ExpSyntax::*; tally: {{ k: [Tally(), ..], stack: st }} => {{ k: [..], stack: {stack} }}; }}"
        )
    };
    let calls = temp_dir();
    let notation = temp_dir();
    let call_k = emitted_k(
        target.path(),
        calls.path(),
        &(spelled(false) + &rule(LET_RESULT.0)),
    );
    let notation_k = emitted_k(
        target.path(),
        notation.path(),
        &(spelled(true) + &rule(LET_RESULT.1)),
    );
    assert_eq!(notation_k, call_k);
    let definition = &notation_k
        .iter()
        .find(|(name, _)| name == "definition.k")
        .expect("a definition is emitted")
        .1;
    for sentence in [
        "( #let N:Map = M:Map #in size(N:Map) ) +Int ( #let B:Int = A:Int #in B:Int +Int B:Int )",
        "<stack> St:List => ( #let L:List = ListItem(1) #in St:List [ 0 <- size(L:List) ] ) </stack>",
    ] {
        assert!(definition.contains(sentence), "{sentence}:\n{definition}");
    }
}

#[test]
fn expand_writes_the_calls_collection_notation_denotes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "collections", &spelled(true));
    let (success, stdout, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let start = stdout
        .find("pub fn visit(")
        .expect("the readable rule is written");
    let start = stdout[..start].rfind("#[k::requires(").unwrap();
    let end = start + stdout[start..].find("\n}\n").unwrap() + 3;
    expect_test::expect![[r"
        #[k::requires(
            k::builtin::bool::and_then(
                k::builtin::bool::and_then(
                    k::builtin::map::in_keys(n, e),
                    k::builtin::list::contains(n, st)
                ),
                k::builtin::bool::not(k::builtin::set::contains(n, s))
            )
        )]
        pub fn visit(
            n: k::Term<k::builtin::Int>,
            e: k::Term<k::builtin::Map>,
            st: k::Term<k::builtin::List>,
            s: k::Term<k::builtin::Set>,
            c: k::Term<k::builtin::Map>,
            k::cells! {
                k : k::configuration::KCell(crate ::ExpSyntax::Visit(n), tail @ ..), env :
                k::configuration::Cell(e), stack : k::configuration::Cell(st), seen :
                k::configuration::Cell(s), counts : k::configuration::Cell(c), state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(..tail), env :
                k::configuration::Cell(k::builtin::map::update_all(k::builtin::map::remove_all(k::builtin::map::remove(k::builtin::map::update(e,
                n, k::builtin::map::get_or_default(e, n, 0)), 0), s), e)), stack :
                k::configuration::Cell(k::builtin::list::update(st, 0, n)), seen :
                k::configuration::Cell(k::builtin::set::union(s, k::builtin::set::item(n))),
                counts : k::configuration::Cell(k::builtin::map::update(c, n,
                k::builtin::int::add(k::builtin::map::get(c, n), 1))), ..state
            }
        }
    "]].assert_eq(&stdout[start..end]);
    // The expanded crate is collected again.
    let expanded = package(temporary.path(), "expanded", "");
    fs::write(expanded.with_file_name("src").join("lib.rs"), &stdout).unwrap();
    let (success, _, stderr) = krs(target.path(), &expanded, "check", &[]);
    assert!(success, "the expanded crate does not check:\n{stderr}");
}

/// The first `error[..]` headline and its message of `krs check` on a
/// package whose last item is `item`, with the help lines that follow it.
fn check_error(target: &Path, item: &str) -> String {
    let temporary = temp_dir();
    let source = spelled(true) + item;
    let manifest = package(temporary.path(), "collections", &source);
    let (success, _, stderr) = krs(target, &manifest, "check", &[]);
    assert!(!success, "{item} was accepted");
    let mut lines = stderr
        .lines()
        .skip_while(|line| !line.starts_with("error["));
    let headline = lines
        .next()
        .unwrap_or_else(|| panic!("no error headline:\n{stderr}"));
    let mut message = headline.to_owned();
    for help in lines
        .take_while(|line| !line.starts_with("error"))
        .filter_map(|line| line.trim_start().strip_prefix("= help: "))
    {
        message.push_str(" [help: ");
        message.push_str(help);
        message.push(']');
    }
    message
}

#[test]
fn a_receiver_that_chooses_no_collection_and_a_method_it_lacks_are_errors() {
    let target = shared_fixture_target();
    let errors = [
        // A receiver no occurrence sorts more precisely than `KItem`.
        "#[k::function(total, internal)]
         pub fn Count(x: Term<KItem>) -> Term<Int> { k::term![x.len()] }",
        // A receiver of a sort that is no collection.
        "#[k::function(total, internal)]
         pub fn Count(x: Term<Int>) -> Term<Int> { k::term![x.len()] }",
        // A scalar domain's operation of the same name is named, when the
        // receiver lies in that domain: `bytes::update` for a `Bytes`, none
        // for an `Int`.
        "#[k::function(total, internal)]
         pub fn Patch(b: Term<k::builtin::Bytes>) -> Term<k::builtin::Bytes> {
             k::term![b.update(0, 1)]
         }",
        "#[k::function(total, internal)]
         pub fn Patch(x: Term<Int>) -> Term<Int> { k::term![x.update(0, 1)] }",
        // A method of another collection.
        "#[k::function(total, internal)]
         pub fn Join(m: Term<Map>, n: Term<Map>) -> Term<Map> { k::term![m.union(n)] }",
        "#[k::function(partial, internal)]
         pub fn First(s: Term<Set>) -> Term<Int> { k::term![s[0]] }",
        // A name in no table keeps the scalar domains' error.
        "#[k::function(total, internal)]
         pub fn Count(m: Term<Map>) -> Term<Int> { k::term![m.size()] }",
        "#[k::function(total, internal)]
         pub fn Less(a: Term<Int>, b: Term<Int>) -> Term<Bool> { k::term![a.lt(b)] }",
        // A method takes the arguments of the call it denotes.
        "#[k::function(total, internal)]
         pub fn Count(m: Term<Map>) -> Term<Int> { k::term![m.len(1)] }",
        // A turbofish names a scalar domain, as before, with the help that a
        // collection method takes none.
        "#[k::function(total, internal)]
         pub fn Count(m: Term<Map>) -> Term<Int> { k::term![m.len::<Int>()] }",
        "#[k::function(total, internal)]
         pub fn Has(m: Term<Map>) -> Term<Bool> { k::term![m.contains_key::<Map>(1)] }",
    ]
    .map(|item| check_error(target.path(), item));
    expect_test::expect![[r#"
        [
            "error[krs::analysis::ambiguous-operator]: `.len()` has the receiver `x`, which no occurrence sorts more precisely than `KItem`, so it chooses no collection; narrow it (the typed binder `x: Term<Map>`) or write the call you mean: `map::size(..)`, `list::size(..)`, or `set::size(..)`",
            "error[krs::syntax::invalid-expression-notation]: `.len()` has a receiver of sort `Int`, which is no collection: an index and the collection methods read a `Map`, a `List` or a `Set`",
            "error[krs::syntax::invalid-expression-notation]: `.update(..)` has a receiver of sort `Bytes`, which is no collection: an index and the collection methods read a `Map`, a `List` or a `Set`; a builtin operation of a scalar domain names its domain: `update::<Bytes>`",
            "error[krs::syntax::invalid-expression-notation]: `.update(..)` has a receiver of sort `Int`, which is no collection: an index and the collection methods read a `Map`, a `List` or a `Set`",
            "error[krs::syntax::invalid-expression-notation]: the method `.union(..)` reads a `Set`, and the receiver is a `Map`, whose methods are `[..]`, `.get_or(..)`, `.contains_key(..)`, `.update(..)`, `.without(..)`, `.without_all(..)`, `.extend(..)`, `.keys()`, `.keys_list()`, `.values()`, and `.len()`",
            "error[krs::syntax::invalid-expression-notation]: an index reads a `Map` or a `List`, and the receiver is a `Set`, whose methods are `.len()`, `.contains(..)`, `.union(..)`, `.difference(..)`, `.intersection(..)`, `.is_subset(..)`, and `.to_list()`",
            "error[krs::syntax::invalid-expression-notation]: `.size(..)` is neither a collection method nor a builtin operation of any domain; a term's methods are the collection methods (`m.get_or(k, d)`, `s.contains(x)`, ..) and builtin operations, written `receiver.operation::<Domain>(..)`",
            "error[krs::syntax::invalid-expression-notation]: a method call names its builtin domain in a turbofish: write `lt::<Int>`, `lt::<String>`, or `lt::<Float>`",
            "error[krs::syntax::invalid-expression-notation]: `.len()` takes no argument besides its receiver",
            "error[krs::syntax::invalid-expression-notation]: the builtin module `int` has no operation `len` [help: a collection method takes no turbofish: its receiver's sort chooses the collection]",
            "error[krs::syntax::invalid-expression-notation]: `Map` is not a builtin domain; a method call names `Int`, `Bool`, `String`, `Float`, `Bytes`, or `K` [help: a collection method takes no turbofish: its receiver's sort chooses the collection]",
        ]
    "#]].assert_debug_eq(&errors);
}

/// An index or a method where a pattern matches a term applies a function,
/// as the call does; each names the pattern form or the guard to write.
#[test]
fn an_index_or_a_method_in_a_pattern_is_a_function_in_a_pattern() {
    let target = shared_fixture_target();
    let errors = [
        "k::rules! {
             for Machine;
             use ExpSyntax::*;
             read: { k: [Visit(e[0]), ..], env: e } => { k: [..] };
         }",
        "k::rules! {
             for Machine;
             use ExpSyntax::*;
             count: { k: [Visit(e.len()), ..], env: e } => { k: [..] };
         }",
    ]
    .map(|item| check_error(target.path(), item));
    expect_test::expect![[r#"
        [
            "error[krs::analysis::function-in-pattern]: the index `[..]`, a builtin lookup, stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: write `{ k -> v, .. }` to read an entry (`[x, ..]` reads a list's first element), or match a variable here and compare it with the index in a guard (`requires`)",
            "error[krs::analysis::function-in-pattern]: the collection method `.len()`, a builtin function, stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: read the value into a name and compare it in a guard (`requires`)",
        ]
    "#]].assert_debug_eq(&errors);
}

/// Every reading of the method table, each collection's operation a method
/// or an index denotes, is written in [`SPELLINGS`] beside its call, so a new
/// row needs its spelling here.
#[test]
fn every_reading_of_the_method_table_has_a_spelling() {
    let mut missing = Vec::new();
    for method in krs_ir::CollectionMethod::ALL {
        for domain in method.domains() {
            let marker = method
                .reading(domain)
                .expect("a listed domain reads")
                .facade_marker();
            let call = format!("{}::{}(", marker.module, marker.name);
            let written = match method.spelling() {
                krs_ir::CollectionMethodSpelling::Index => "[".to_owned(),
                krs_ir::CollectionMethodSpelling::Method => format!(".{}(", method.rust_name()),
            };
            if !SPELLINGS
                .iter()
                .any(|(_, calls, notation)| calls.contains(&call) && notation.contains(&written))
            {
                missing.push(format!("{} in {}", method.written(), domain.name()));
            }
        }
    }
    assert!(
        missing.is_empty(),
        "readings without a spelling: {missing:?}"
    );
}
