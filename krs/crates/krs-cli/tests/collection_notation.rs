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
        <env> E:Map => updateMap(removeAll(E:Map [ N:Int <- (E:Map [ N:Int ] orDefault 0) ] [ 0 <- undef ], S:Set), E:Map) </env>
        <stack> St:List => St:List [ 0 <- N:Int ] </stack>
        <seen> S:Set => S:Set |Set SetItem(N:Int) </seen>
        <counts> C:Map => C:Map [ N:Int <- {C:Map [ N:Int ]}:>Int +Int 1 ] </counts>
        requires (N:Int in_keys(E:Map) andThenBool N:Int in St:List) andThenBool (notBool N:Int in S:Set)
        requires "definition.k"
        <k> drop ( N:Int ) ~> Tail:K => .K ~> Tail:K </k>
        <env> E:Map => E:Map [ N:Int <- (E:Map [ N:Int ]) ] </env>
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

/// A package with one placeholder `{NAME}` per collection literal;
/// [`LITERALS`] fills each with the literal or with the calls it denotes.
const LITERAL_SOURCE: &str = r#"
use k::builtin::{Bool, Int, KSequence, List, Map, Set, list, map, set};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("pair({a},{b})")]
    Pair { a: Int, b: Int },
    #[k::syntax("mark({n})")]
    Mark { n: Int },
    #[k::syntax("peek")]
    Peek,
}

#[k::function(total, internal)]
pub fn Build(a: Term<Int>, b: Term<Int>, m: Term<Map>, s: Term<Set>) -> Term<Map> {
    k::term![{BUILD}]
}

#[k::function(total, internal)]
pub fn Empties(a: Term<Int>) -> Term<Map> {
    k::term![{EMPTIES}]
}

#[k::function(partial, internal)]
pub fn Lookup(m: Term<Map>, key: Term<Int>) -> Term<Int>;

k::equations! {
    for Lookup;
    lookup: (m, key) => {LOOKUP};
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub seen: Set,
    #[k::cell]
    pub stack: List,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            env: map::empty(),
            seen: {INIT_SEEN},
            stack: {INIT_STACK},
        }
    }
}

k::rules! {
    for Machine;
    use ExpSyntax::*;

    #[k::requires({PAIR_REQUIRES})]
    pair: { k: [Pair(a, b), ..], env: e, seen: s } => {
        k: [..],
        env: {PAIR_ENV},
        seen: {PAIR_SEEN},
    };
    // The key is computed from the set another cell binds.
    peek: { k: [Peek(), ..], env: { {PEEK_KEY} -> v, .. }, seen: s } => { k: [v, ..] };
}

#[k::rule(label = "mark", priority = 60)]
fn mark(
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Mark(n), tail @ ..),
        seen: k::configuration::Cell({MARK_SEEN_BEFORE}),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        seen: k::configuration::Cell({MARK_SEEN_AFTER}),
        ..state
    }
}

#[k::claim(all_paths, label = "pair-claim")]
#[k::requires({CLAIM_REQUIRES})]
fn pair_claim(
    a: Term<Int>,
    b: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Pair(a, b), tail @ ..),
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

/// Each placeholder of [`LITERAL_SOURCE`], the calls it is written with, and
/// the literals that denote them: a map's entries, each written over the map
/// before it, and a set's elements, joined, over the empty collection or a
/// rest; the empty map and set; a set's singleton, matched in a pattern.
const LITERALS: &[(&str, &str, &str)] = &[
    (
        "BUILD",
        "map::update(map::update(m, a, 1), b, set::union(s, set::union(set::item(a), set::item(3))))",
        "map![a -> 1, b -> set![a, 3, ..s], ..m]",
    ),
    (
        "EMPTIES",
        "map::update(map::update(map::empty(), a, set::empty()), 1, set::item(a))",
        "map![a -> set![], 1 -> set![a]]",
    ),
    (
        "LOOKUP",
        "map::get(map::update(m, key, 2), key)",
        "map![key -> 2, ..m][key]",
    ),
    (
        "INIT_SEEN",
        "set::union(set::item(1), set::item(2))",
        "set![1, 2]",
    ),
    (
        "INIT_STACK",
        "list::item(map::update(map::empty(), 1, 2))",
        "list::item(map![1 -> 2])",
    ),
    (
        "PAIR_REQUIRES",
        "map::in_keys(a, map::update(map::empty(), a, b)) && !set::contains(0, set::item(b))",
        "map![a -> b].contains_key(a) && !set![b].contains(0)",
    ),
    (
        "PAIR_ENV",
        "map::update(map::update(e, a, 1), b, 2)",
        "map![a -> 1, b -> 2, ..e]",
    ),
    (
        "PAIR_SEEN",
        "set::union(s, set::union(set::item(a), set::item(b)))",
        "set![a, b, ..s]",
    ),
    (
        "PEEK_KEY",
        "set::size(set::union(s, set::item(1)))",
        "set![1, ..s].len()",
    ),
    ("MARK_SEEN_BEFORE", "set::item(n)", "set![n]"),
    (
        "MARK_SEEN_AFTER",
        "set::union(set::item(n), set::item(1))",
        "set![n, 1]",
    ),
    (
        "CLAIM_REQUIRES",
        "map::in_keys(a, map::update(e, a, b))",
        "map![a -> b, ..e].contains_key(a)",
    ),
    // A `cells!` cell's whole value `map![..]` is the cell's own map, which
    // that surface reads as K's concatenation; a literal below it is a term.
    (
        "CLAIM_ENV",
        "map::update_all(e, map::update(map::empty(), a, b))",
        "e.extend(map![a -> b])",
    ),
];

/// [`LITERAL_SOURCE`] with each placeholder written with literals or with
/// calls.
fn literal_spelled(literals: bool) -> String {
    LITERALS.iter().fold(
        LITERAL_SOURCE.to_owned(),
        |source, (name, call, written)| {
            let placeholder = format!("{{{name}}}");
            assert!(source.contains(&placeholder), "{placeholder} is unused");
            source.replace(&placeholder, if literals { written } else { call })
        },
    )
}

/// A collection literal emits the K of the calls it denotes wherever a term
/// is built, in a guard, in a computed key, and, as the empty collection or
/// a set's singleton, in a pattern: a map's later entry is written over the
/// earlier ones, and a set's elements are joined with `|Set`.
#[test]
fn collection_literals_emit_the_k_of_the_calls_they_denote() {
    let target = shared_fixture_target();
    let calls = temp_dir();
    let literals = temp_dir();
    let call_k = emitted_k(target.path(), calls.path(), &literal_spelled(false));
    let literal_k = emitted_k(target.path(), literals.path(), &literal_spelled(true));
    assert_eq!(literal_k, call_k);
    let sentences = literal_k
        .iter()
        .flat_map(|(_, text)| text.lines())
        .filter(|line| {
            let line = line.trim_start();
            line.starts_with("rule ")
                || line.starts_with("<env>")
                || line.starts_with("<seen>")
                || line.starts_with("<stack>")
                || line.starts_with("requires")
        })
        .map(str::trim)
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r#"
        <env> .Map </env>
        <seen> SetItem(1) |Set SetItem(2) </seen>
        <stack> ListItem(.Map [ 1 <- 2 ]) </stack>
        rule build ( A:Int , B:Int , M:Map , S:Set ) => M:Map [ A:Int <- 1 ] [ B:Int <- S:Set |Set (SetItem(A:Int) |Set SetItem(3)) ] [label(krsRule_0432a5ea69e36249ca34707c)]
        rule empties ( A:Int ) => .Map [ A:Int <- .Set ] [ 1 <- SetItem(A:Int) ] [label(krsRule_24827f3ce5331722585d973c)]
        rule lookup ( M:Map , Key:Int ) => {M:Map [ Key:Int <- 2 ] [ Key:Int ]}:>Int [label(krsRule_ca9c6cb787329cb196b90848)]
        rule [mark]:
        <seen> SetItem(N:Int) => SetItem(N:Int) |Set SetItem(1) </seen>
        rule [pair]:
        <env> E:Map => E:Map [ A:Int <- 1 ] [ B:Int <- 2 ] </env>
        <seen> S:Set => S:Set |Set (SetItem(A:Int) |Set SetItem(B:Int)) </seen>
        requires A:Int in_keys(.Map [ A:Int <- B:Int ]) andThenBool (notBool 0 in SetItem(B:Int))
        rule [peek]:
        <env> size(S:Set |Set SetItem(1)) |-> V:KItem ... </env>
        <seen> S:Set </seen>
        requires "definition.k"
        <env> E:Map => updateMap(E:Map, .Map [ A:Int <- B:Int ]) </env>
        requires A:Int in_keys(E:Map [ A:Int <- B:Int ])"#]].assert_eq(&sentences);
}

/// `krs expand` writes the calls a literal denotes in a sentence, and the
/// expanded crate is collected again.
#[test]
fn expand_writes_the_calls_a_collection_literal_denotes() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "collections", &literal_spelled(true));
    let (success, stdout, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let start = stdout
        .find("pub fn pair(")
        .expect("the readable rule is written");
    let start = stdout[..start].rfind("#[k::requires(").unwrap();
    let end = start + stdout[start..].find("\n}\n").unwrap() + 3;
    expect_test::expect![[r"
        #[k::requires(
            k::builtin::bool::and_then(
                k::builtin::map::in_keys(
                    a,
                    k::builtin::map::update(k::builtin::map::empty(), a, b)
                ),
                k::builtin::bool::not(k::builtin::set::contains(0, k::builtin::set::item(b)))
            )
        )]
        pub fn pair(
            a: k::Term<k::builtin::Int>,
            b: k::Term<k::builtin::Int>,
            e: k::Term<k::builtin::Map>,
            s: k::Term<k::builtin::Set>,
            k::cells! {
                k : k::configuration::KCell(crate ::ExpSyntax::Pair(a, b), tail @ ..), env :
                k::configuration::Cell(e), seen : k::configuration::Cell(s), state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(..tail), env :
                k::configuration::Cell(k::builtin::map::update(k::builtin::map::update(e, a, 1),
                b, 2)), seen : k::configuration::Cell(k::builtin::set::union(s,
                k::builtin::set::union(k::builtin::set::item(a), k::builtin::set::item(b)))),
                ..state
            }
        }
    "]]
    .assert_eq(&stdout[start..end]);
    let expanded = package(temporary.path(), "expanded", "");
    fs::write(expanded.with_file_name("src").join("lib.rs"), &stdout).unwrap();
    let (success, _, stderr) = krs(target.path(), &expanded, "check", &[]);
    assert!(success, "the expanded crate does not check:\n{stderr}");
}

/// Two keys that evaluate equal are one entry, whose value the later entry
/// writes, and two equal elements one element: `krs run` of `pair(3,3)`
/// leaves `3 |-> 2` and adds one `SetItem(3)` to the initial `set![1, 2]`,
/// and `pair(3,4)` both entries and both elements.
#[test]
fn a_later_key_wins_and_equal_elements_collapse_at_run_time() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "collections", &literal_spelled(true));
    let cells = ["pair(3,3)", "pair(3,4)"].map(|program| {
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
            let open = format!("<{name}> ");
            let start = flat
                .find(&open)
                .unwrap_or_else(|| panic!("no <{name}>:\n{stdout}"))
                + open.len();
            let end = start + flat[start..].find(&format!(" </{name}>")).unwrap();
            flat[start..end].to_owned()
        };
        format!("{program} => env: {} | seen: {}", cell("env"), cell("seen"))
    });
    expect_test::expect![[r#"
        [
            "pair(3,3) => env: 3 |-> 2 | seen: SetItem ( 1 ) SetItem ( 2 ) SetItem ( 3 )",
            "pair(3,4) => env: 3 |-> 1 4 |-> 2 | seen: SetItem ( 1 ) SetItem ( 2 ) SetItem ( 3 ) SetItem ( 4 )",
        ]
    "#]].assert_debug_eq(&cells);
}

/// The first `error[..]` headline of `krs check` on a package whose last
/// item is `item`, and the column and width its location underlines.
fn check_error_at(target: &Path, item: &str) -> (String, String) {
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "collections", &(spelled(true) + item));
    let (success, _, stderr) = krs(target, &manifest, "check", &[]);
    assert!(!success, "{item} was accepted");
    let mut lines = stderr
        .lines()
        .skip_while(|line| !line.starts_with("error["));
    let headline = lines
        .next()
        .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
        .to_owned();
    let column = lines
        .find_map(|line| line.trim_start().strip_prefix("--> "))
        .and_then(|location| location.rsplit(':').next())
        .unwrap_or_else(|| panic!("no location:\n{stderr}"))
        .to_owned();
    let width = lines
        .find(|line| line.contains('^'))
        .map_or(0, |line| line.matches('^').count());
    (headline, format!("column {column}, width {width}"))
}

/// A malformed literal is an error at its token: a key written twice, an
/// anonymous or misplaced rest, a rest alone, an entry without `->`, K's
/// `.Map`; a literal that applies a function where a pattern matches a term is
/// a function in a pattern, as its call is, told over the whole literal, and
/// so is a constant's map.
#[test]
fn malformed_collection_literals_and_literals_in_a_pattern_are_errors() {
    let target = shared_fixture_target();
    let function = |body: &str| {
        format!(
            "#[k::function(total, internal)]
pub fn Build(a: Term<Int>, m: Term<Map>, s: Term<Set>) -> Term<Map> {{ k::term![{body}] }}"
        )
    };
    let rule = |cells: &str| {
        format!(
            "k::rules! {{ for Machine; use ExpSyntax::*;
read: {{ k: [Visit(n), ..], {cells} }} => {{ k: [..] }}; }}"
        )
    };
    let items = [
        "map![a -> 1, a -> 2]",
        "map![a -> 1, ..]",
        "map![..m, a -> 1]",
        "map![..m]",
        "map![a => 1]",
        "map![a, 1]",
        "map![.Map]",
    ]
    .map(function)
    .into_iter()
    .chain(
        [
            "env: map![n -> 1, 2 -> 3]",
            "seen: set![n, 1]",
            "env: map![n -> v, ..]",
            "seen: set![n, ..]",
        ]
        .map(rule),
    )
    .chain(["#[k::constant]\nconst ONE: Map = map![1 -> 2];".to_owned()]);
    let errors = items
        .map(|item| check_error_at(target.path(), &item))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            (
                "error[krs::syntax::invalid-expression-notation]: the key `a` is written twice; two keys written as the same term are one key, so the earlier entry's value would never be read: write the key once, with the value it maps to",
                "column 93, width 1",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: in a term, `map![..]` is a literal, and its rest is the map its entries are written over, `map![k -> v, ..m]`; an anonymous `..` names no map. A pattern reads a map's entries with `{ k -> v, .. }`, or `map![k -> v, ..]` in a `cells!` entry",
                "column 93, width 1",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: the base `..rest` of a `map![..]` comes last: the written entries are applied over it, as `Ctor { f: e, ..base }` writes its fields over `base`",
                "column 85, width 1",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: `map![..m]` has no entry: it is the map `m` itself, so write `m`",
                "column 85, width 1",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: `=>` is a rewrite; a map's entry is written `key -> value`",
                "column 87, width 1",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: a map's entry is written `key -> value`",
                "column 86, width 1",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: `.Map` is K's empty map; a term writes the empty map `map![]`",
                "column 85, width 1",
            ),
            (
                "error[krs::analysis::function-in-pattern]: the builtin function `k::builtin::map::update` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: a pattern reads a map's entries (`{ k -> v, .. }` in a readable record, `map![k -> v, ..]` in a `cells!` entry), or match a variable here and relate it to the map in a guard (`requires`)",
                "column 33, width 20",
            ),
            (
                "error[krs::analysis::function-in-pattern]: the builtin function `k::builtin::set::union` stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match the elements with `set::concat(set::item(x), rest)`, whose operands are disjoint, or match a variable here and relate it to the set in a guard (`requires`)",
                "column 34, width 10",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: in a term, `map![..]` is a literal, and its rest is the map its entries are written over, `map![k -> v, ..m]`; an anonymous `..` names no map. A pattern reads a map's entries with `{ k -> v, .. }`, or `map![k -> v, ..]` in a `cells!` entry",
                "column 46, width 1",
            ),
            (
                "error[krs::syntax::invalid-expression-notation]: in a term, `set![..]` is a literal, and its rest is the set its elements join, `set![x, ..s]`; an anonymous `..` names no set. A pattern matches a set's elements with `set::concat(set::item(x), rest)`",
                "column 42, width 1",
            ),
            (
                "error[krs::analysis::invalid-constant]: the value of constant `ONE` applies a builtin operation; a constant names a ground constructor term, which every use can match, and a function application is evaluated, not matched",
                "column 18, width 12",
            ),
        ]
    "#]].assert_debug_eq(&errors);
}

/// A package whose builtin imports name no `map` and no `set`, with
/// `{IMPORT}` and `{MAP_CELL}` to fill.
const IMPORT_SOURCE: &str = r#"#![allow(unused_imports)]
use k::builtin::{Int, KSequence, List, Map};
use k::{KItem, KResult, Term};
{IMPORT}

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum ExpSyntax {
    #[k::syntax("look({n})")]
    Look { n: Int },
    #[k::syntax("wrap({m})")]
    Wrap { m: Map },
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub ret: Exp,
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
    pub boxed: Exp,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            env: {MAP_CELL},
            stack: k::builtin::list::item(map![1 -> 2]),
            boxed: ExpSyntax::Wrap(map![1 -> 2]),
            frame: Frame { ret: ExpSyntax::Look(0) },
        }
    }
}

#[k::rule(label = "box")]
fn boxing(
    n: Term<Int>,
    b: Term<Exp>,
    f: Term<Frame>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Look(n), tail @ ..),
        boxed: k::configuration::Cell(b),
        frame: f,
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        boxed: k::configuration::Cell(ExpSyntax::Wrap { m: map![n -> 1] }),
        frame: k::fragment![Frame { ret: ExpSyntax::Wrap { m: map![n -> 2] } }],
        ..state
    }
}
"#;

/// A collection literal is notation for calls, which rustc receives, so it
/// needs no import of `map`, below a cell of an initializer (a call's
/// argument, a constructor's) or of a `cells!` result (a record's field, a
/// fragment's); a cell's own `map![..]`, which the enclosing macro consumes,
/// still credits the import that names it, also where it writes entries and
/// is read as a literal.
#[test]
fn a_literal_needs_no_import_and_a_cells_own_map_credits_its_import() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let check = |name: &str, import: &str, map_cell: &str| {
        let manifest = package(temporary.path(), name, "");
        fs::write(
            manifest.with_file_name("src").join("lib.rs"),
            IMPORT_SOURCE
                .replace("{IMPORT}", import)
                .replace("{MAP_CELL}", map_cell),
        )
        .unwrap();
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(success, "{name}:\n{stderr}");
    };
    check("literals", "", "k::builtin::map::empty()");
    // The import is denied if unused: a cell's own map must credit it, the
    // empty map and a map that writes entries, which is read as a literal.
    check("own-map", "#[deny(unused_imports)]\nuse k::map;", "map![]");
    check(
        "own-literal",
        "#[deny(unused_imports)]\nuse k::map;",
        "k::configuration::Cell::new(map![1 -> 2])",
    );
}
