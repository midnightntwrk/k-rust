//! An alias clause runs two ways. Forward, as a desugar clause does, it expands every subject
//! written in a program or a rule into its result. Backward, when a result is printed, every term
//! its result matches prints as its subject, built from what that match bound. So the subject is
//! built too: a construct that only matches (`_`, `name @ pattern`, `A | B`, an open record, a
//! list's anonymous rest) and a name the result does not use have no value there, and the printed
//! alias would not denote the printed value. Each is refused at the construct, or at the name,
//! with a message that says what would print and points to `#[k::desugar]`, which runs one way.
//! What the result computes is admitted: a concrete printed value holds no unevaluated
//! application, so the reverse does not fire on it, and a symbolic one holds the very application
//! the clause expands to, so the printed alias denotes it.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Bool, Int, KSequence, List, Set, set};
use k::{KItem, KResult, Term};

k::sorts! {
    Value: KResult;
    impl Value for Int, Bool;
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Data {
    #[k::syntax("red")] Red(),
    #[k::syntax("box({a})")] Box { a: Int },
    #[k::syntax("tag({a})")] Tag { a: Int },
    #[k::syntax("pair({a}, {b})")] Pair { a: Int, b: Int },
    #[k::syntax("one({a})")] One { a: Value },
    #[k::syntax("two({a}, {b})")] Two { a: KItem, b: List },
    #[k::syntax("flag({a})")] Flag { a: Bool },
    #[k::syntax("mk({a}, {b})")] Mk { a: Int, b: Int },
    #[k::syntax("probe({a})")] Probe { a: Value },
    #[k::syntax("calc({a}, {b})")] Calc { a: Int, b: Int },
    #[k::syntax("bs({a}, {b})")] Bs { a: KItem, b: Set },
}

#[k::function(partial, sort = Int, syntax = "size({a})")]
pub struct Size {
    pub a: Term<KItem>,
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Al {
    #[k::syntax("whole({a})")] #[k::alias] Whole { a: Value },
    #[k::syntax("pairs({a}, {b})")] #[k::alias] Pairs { a: Int, b: Int },
    #[k::syntax("items({a})")] #[k::alias] Items { a: List },
    #[k::syntax("elems({a})")] #[k::alias] Elems { a: Set },
    #[k::syntax("zero()")] #[k::alias] Zero(),
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Sugar {
    #[k::syntax("nought()")] #[k::desugar] Nought(),
}

#[k::alias]
fn zero(k::term![Al::Zero()]: Term<Value>) -> Term<Value> {
    Data::Red()
}

#[k::desugar]
fn nought(k::term![Sugar::Nought()]: Term<Value>) -> Term<Value> {
    Data::Red()
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

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `aliases` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"aliases\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-ALIAS-CLAUSES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .args(["--package", "aliases", "--definition", "main"])
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

/// `_`, `name @ pattern`, `A | B`, an open record and a list's anonymous rest (at the front, the
/// back or the middle) in an alias clause's subject are refused at the construct, and a name the
/// subject binds and the result does not use at the name, the result's own `let` names apart:
/// printing builds the subject from the bindings of what the result matched, which give none of
/// them a value. On main each printed as a term that does not denote the value:
/// `wild(1, _Krs_Wildcard0:Int)`, `named(green #And red)`, `either(box(1) #Or tag(1))`,
/// `rec(pair(1, _Krs_Wildcard0:Int))`, `lst(ListItem ( 1 ) _Krs_Wildcard0:List)`,
/// `free(1, Y:Int)`.
#[test]
fn a_construct_printing_cannot_build_is_refused_in_an_alias_subject() {
    expect_test::expect![[r"
        wildcard:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and `_` names no term the match gives a value: it prints as a variable (`_Krs_Wildcard0`) where the term stood; name the term and use the name in the result, or write `#[k::desugar]` for an expansion that runs one way; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:70:31
        pattern-alias:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and `name @ pattern` (K's #as) is a test of the term's shape, which building cannot make: it prints as the conjunction `term #And pattern`, no term, and for a term the pattern does not match, as an alias that does not expand back to it; write `#[k::desugar]` for an expansion that runs one way; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:70:29
        alternatives:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and `A | B` (K's #Or) denotes no one term: it prints as the disjunction `A #Or B`; write one alias clause per alternative, each with the result, or `#[k::desugar]` for an expansion that runs one way; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:70:30
        open-record:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and the fields `..` leaves open have no value from that match: they print as variables (`_Krs_Wildcard0`); name every field and use it in the result, or write `#[k::desugar]` for an expansion that runs one way; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:70:27
        anonymous-rest:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and the elements an anonymous `..` leaves unnamed have no value from that match: they print as a variable (`_Krs_Wildcard0`); a list of an element and a rest is moreover one spelling of the list, which static expansion matches as written: name the whole list and use the name in the result; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:70:32
        back-rest:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and the elements an anonymous `..` leaves unnamed have no value from that match: they print as a variable (`_Krs_Wildcard0`); a list of an element and a rest is moreover one spelling of the list, which static expansion matches as written: name the whole list and use the name in the result; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:70:29
        middle-rest:
        error[krs::expand::irreversible-alias]: an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and the elements an anonymous `..` leaves unnamed have no value from that match: they print as a variable (`_Krs_Wildcard0`); a list of an element and a rest is moreover one spelling of the list, which static expansion matches as written: name the whole list and use the name in the result; here it stands in the subject of a `#[k::alias]` fn
        --> src/lib.rs:70:32
        unused-name:
        error[krs::expand::irreversible-alias]: alias clause `free`: its subject binds `y`, which its result does not use; an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and no match binds `y`, so it would print as a variable where the term stood; use `y` in the result, or write `#[k::desugar]` for an expansion that runs one way
        --> src/lib.rs:70:31
        unused-rest:
        error[krs::expand::irreversible-alias]: alias clause `head`: its subject binds `rest`, which its result does not use; an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and no match binds `rest`, so it would print as a variable where the term stood; use `rest` in the result, or write `#[k::desugar]` for an expansion that runs one way
        --> src/lib.rs:70:32
        shadowed-name:
        error[krs::expand::irreversible-alias]: alias clause `free`: its subject binds `y`, which its result does not use; an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and no match binds `y`, so it would print as a variable where the term stood; use `y` in the result, or write `#[k::desugar]` for an expansion that runs one way
        --> src/lib.rs:70:31"]]
    .assert_eq(&refusals([
        (
            "wildcard",
            "#[k::alias]\nfn wild(k::term![Al::Pairs(x, _)]: Term<Value>) -> Term<Value> {\n    Data::Box(x)\n}\n",
        ),
        (
            "pattern-alias",
            "#[k::alias]\nfn named(k::term![Al::Whole(y @ Data::Red())]: Term<Value>) -> Term<Value> {\n    Data::One(y)\n}\n",
        ),
        (
            "alternatives",
            "#[k::alias]\nfn either(k::term![Al::Whole(Data::Box(x) | Data::Tag(x))]: Term<Value>) -> Term<Value> {\n    Data::Pair(x, x)\n}\n",
        ),
        (
            "open-record",
            "#[k::alias]\nfn rec(k::term![Al::Whole(Data::Pair { a: x, .. })]: Term<Value>) -> Term<Value> {\n    Data::Box(x)\n}\n",
        ),
        (
            "anonymous-rest",
            "#[k::alias]\nfn head(k::term![Al::Items([x, ..])]: Term<Value>) -> Term<Value> {\n    Data::Two(x, [])\n}\n",
        ),
        (
            "back-rest",
            "#[k::alias]\nfn last(k::term![Al::Items([.., z])]: Term<Value>) -> Term<Value> {\n    Data::Two(z, [])\n}\n",
        ),
        (
            "middle-rest",
            "#[k::alias]\nfn ends(k::term![Al::Items([a, .., z])]: Term<Value>) -> Term<Value> {\n    Data::Two(a, [z])\n}\n",
        ),
        (
            "unused-name",
            "#[k::alias]\nfn free(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {\n    Data::Box(x)\n}\n",
        ),
        (
            "unused-rest",
            "#[k::alias]\nfn head(k::term![Al::Items([x, rest @ ..])]: Term<Value>) -> Term<Value> {\n    Data::Two(x, [])\n}\n",
        ),
        (
            "shadowed-name",
            "#[k::alias]\nfn free(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {\n    Data::Box({\n        let y = x;\n        y\n    })\n}\n",
        ),
    ]));
}

/// Below an alias subject's root, what a term's head tells is refused at the term once names and
/// sorts are resolved: a set's concatenation, which static expansion matches as written, in one
/// order of its parts, as in a desugar's subject (NT-14), and whose parts the result's match may
/// moreover bind overlapping (on main `bs(1, set::item(1))` printed
/// `elems(SetItem ( 1 ) SetItem ( 1 ))`, no set). An alias's or a desugar's application there is
/// written expanded, where the expansion needs no value, and refused otherwise
/// (`static_subjects.rs`); a function's application is refused at the construct. A
/// reference-code subject spells no map's concatenation: `map![..]` there is the update it
/// denotes.
#[test]
fn what_a_head_tells_is_refused_below_an_alias_subject_root() {
    expect_test::expect![[r"
        set-concatenation-rest:
        error[krs::analysis::collection-in-static-subject]: alias clause `elems`: a set of two or more parts matches only one way of writing it: static expansion matches a program's terms as they are written, before anything evaluates, and does not reorder a set's elements or a map's entries or regroup a list's parts, so the clause would rewrite one spelling of the collection and not the others (`[1, 2, 3]` but not `list::concat([1, 2], [3])`); the empty collection and one element or entry have one spelling: write the parts as a constructor's arguments, or rewrite the collection with a rule
        --> src/lib.rs:70:29
        set-concatenation-items:
        error[krs::analysis::collection-in-static-subject]: alias clause `elems`: a set of two or more parts matches only one way of writing it: static expansion matches a program's terms as they are written, before anything evaluates, and does not reorder a set's elements or a map's entries or regroup a list's parts, so the clause would rewrite one spelling of the collection and not the others (`[1, 2, 3]` but not `list::concat([1, 2], [3])`); the empty collection and one element or entry have one spelling: write the parts as a constructor's arguments, or rewrite the collection with a rule
        --> src/lib.rs:70:29"]]
    .assert_eq(&refusals([
        (
            "set-concatenation-rest",
            "#[k::alias]\nfn elems(k::term![Al::Elems(set::concat(set::item(x), rest))]: Term<Value>) -> Term<Value> {\n    Data::Bs(x, rest)\n}\n",
        ),
        (
            "set-concatenation-items",
            "#[k::alias]\nfn elems(k::term![Al::Elems(set::concat(set::item(x), set::item(y)))]: Term<Value>) -> Term<Value> {\n    Data::Two(x, [y])\n}\n",
        ),
    ]));
}

/// A clause for each alias production of the preamble but `Al::Pairs`, so that a package whose
/// mistake is told after the clauses are matched with their productions has no other.
const OTHER_CLAUSES: &str = "#[k::alias]\nfn whole(k::term![Al::Whole(a)]: Term<Value>) -> Term<Value> {\n    Data::One(a)\n}\n\n#[k::alias]\nfn items(k::term![Al::Items([x])]: Term<Value>) -> Term<Value> {\n    Data::Two(x, [])\n}\n\n#[k::alias]\nfn elems(k::term![Al::Elems(set::item(x))]: Term<Value>) -> Term<Value> {\n    Data::Two(x, [])\n}\n\n";

/// A function's application in an alias subject would stand for its spelling, which static
/// expansion matches as written, rather than its value (finding NT-8-2, decided with NT-11-5):
/// it is refused at the application, as in a desugar's subject, with what to write instead (on
/// main KRS emitted it and every native route refused it, `IllegalFunctionOnLhs`).
/// `#[k::requires]` on an alias clause, which K applies unconditionally, is refused at the
/// attribute, as on a desugar clause (finding NT-8-3; on main the internal
/// `krs::collect::provenance-mismatch`).
#[test]
fn a_function_or_a_condition_on_an_alias_clause_is_refused() {
    expect_test::expect![[r"
        function-in-subject:
        error[krs::analysis::function-in-pattern]: the function `Size` stands in the subject of an alias clause, which static expansion matches against a program's terms as they are written, before anything evaluates: there an application stands for its own spelling, not for the value it denotes everywhere else (`f(x + 1)` would expand the program `f(y + 1)` but not `f(1 + y)`), so the clause would rewrite some spellings of a value and not others: to rewrite a computation, write a rule (`#[k::rule]`) or the function's equation (`#[k::equation]`); to expand a term a program writes, write it with constructors
        --> src/lib.rs:85:29
        requires:
        error[krs::syntax::invalid-rule-key]: an alias clause has no `#[k::requires]`: K rewrites the definition and the program with it once, before anything runs, and prints each term its result matches back as its subject, so there is nothing to test a condition against
        --> src/lib.rs:85:6"]]
    .assert_eq(&refusals([
        (
            "function-in-subject",
            &format!("{OTHER_CLAUSES}#[k::alias]\nfn sized(k::term![Al::Pairs(Size(x), y)]: Term<Value>) -> Term<Value> {{\n    Data::Two(x, [y])\n}}\n"),
        ),
        (
            "requires",
            &format!("{OTHER_CLAUSES}#[k::alias]\n#[k::requires(x > 0)]\nfn pairs(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {{\n    Data::Pair(y, x)\n}}\n"),
        ),
    ]));
}

/// A static clause's result is the term a program's expansion writes in place of the production's
/// application, which then evaluates as the same term in a rule's result does, so it is a term of
/// the production's sort or below it (finding NT-12-3): a set from an alias of `Value`, a
/// `String` from a desugar of `Value`, refused at the result. On main KRS emitted both, and a
/// program's `nought()` was the projection of `"s"` to `Value`, which has no value.
#[test]
fn a_static_result_of_a_sort_not_below_its_productions_is_refused() {
    expect_test::expect![[r"
        alias-set:
        error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-ALIAS-CLAUSES::pairs (alias): the result of alias clause `pairs` has sort `Set`, which is not below `Value`, the sort of the production `Al::Pairs` it expands: a program's application of the production is replaced by the result where a `Value` stands, and a term of sort `Set` is not one there; write a result of sort `Value`, or of a sort below it
        --> src/lib.rs:86:5
        desugar-string:
        error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-ALIAS-CLAUSES::nought_again (desugar): the result of desugar clause `nought_again` has sort `String`, which is not below `Value`, the sort of the production `Sugar::Nought` it expands: a program's application of the production is replaced by the result where a `Value` stands, and a term of sort `String` is not one there; write a result of sort `Value`, or of a sort below it
        --> src/lib.rs:91:5"]]
    .assert_eq(&refusals([
        (
            "alias-set",
            &format!("{OTHER_CLAUSES}#[k::alias]\nfn pairs(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<KItem> {{\n    set::item(x + y)\n}}\n"),
        ),
        (
            "desugar-string",
            &format!("{OTHER_CLAUSES}#[k::alias]\nfn pairs(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {{\n    Data::Pair(y, x)\n}}\n\n#[k::desugar]\nfn nought_again(k::term![Sugar::Nought()]: Term<Value>) -> Term<KItem> {{\n    \"s\"\n}}\n"),
        ),
    ]));
}

/// Two clauses of one static production whose subjects some term matches are refused at the one
/// written later: a static clause takes no `priority` or `owise`, so nothing states which of the two a
/// program's expansion applies where both match, and the emitted definition would pick one by an
/// order the author never wrote (NT-22). A literal beside a binder (`pairs(1, y)` and
/// `pairs(x, y)` both match `pairs(1, 2)`), two spellings of one value (`01` is `1`), and one
/// subject written twice overlap. Subjects no term matches both of are accepted: other literals,
/// and a repeated binder beside two different values (`pairs(x, x)` and `pairs(1, 2)`).
#[test]
fn two_static_clauses_whose_subjects_overlap_are_refused() {
    expect_test::expect![[r"
        literal-and-binder:
        error[krs::analysis::invalid-static-clause]: alias clauses `one_first` and `any_first` of `Al::Pairs` overlap: `Al::Pairs(1, _)` matches both subjects, and the clauses of a production marked `#[k::alias]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
        --> src/lib.rs:90:23
        one-value:
        error[krs::analysis::invalid-static-clause]: alias clauses `one_two` and `padded` of `Al::Pairs` overlap: `Al::Pairs(1, 2)` matches both subjects, and the clauses of a production marked `#[k::alias]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
        --> src/lib.rs:90:20
        written-twice:
        error[krs::analysis::invalid-static-clause]: desugar clauses `nought` and `nought_again` of `Sugar::Nought` overlap: `Sugar::Nought()` matches both subjects, and the clauses of a production marked `#[k::desugar]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
        --> src/lib.rs:90:26"]]
    .assert_eq(&refusals([
        (
            "literal-and-binder",
            &format!("{OTHER_CLAUSES}#[k::alias]\nfn one_first(k::term![Al::Pairs(1, y)]: Term<Value>) -> Term<Value> {{\n    Data::Box(y)\n}}\n\n#[k::alias]\nfn any_first(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {{\n    Data::Pair(x, y)\n}}\n"),
        ),
        (
            "one-value",
            &format!("{OTHER_CLAUSES}#[k::alias]\nfn one_two(k::term![Al::Pairs(1, 2)]: Term<Value>) -> Term<Value> {{\n    Data::Red()\n}}\n\n#[k::alias]\nfn padded(k::term![Al::Pairs(01, y)]: Term<Value>) -> Term<Value> {{\n    Data::Box(y)\n}}\n"),
        ),
        (
            "written-twice",
            &format!("{OTHER_CLAUSES}#[k::alias]\nfn pairs(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {{\n    Data::Pair(y, x)\n}}\n\n#[k::desugar]\nfn nought_again(k::term![Sugar::Nought()]: Term<Value>) -> Term<Value> {{\n    Data::Box(1)\n}}\n"),
        ),
    ]));
    let target = shared_fixture_target();
    let temporary = temp_dir();
    for (name, source) in [
        (
            "other-literals",
            format!(
                "{OTHER_CLAUSES}#[k::alias]\nfn one(k::term![Al::Pairs(1, y)]: Term<Value>) -> Term<Value> {{\n    Data::Box(y)\n}}\n\n#[k::alias]\nfn two(k::term![Al::Pairs(2, y)]: Term<Value>) -> Term<Value> {{\n    Data::Tag(y)\n}}\n"
            ),
        ),
        (
            "repeated-binder",
            format!(
                "{OTHER_CLAUSES}#[k::alias]\nfn same(k::term![Al::Pairs(x, x)]: Term<Value>) -> Term<Value> {{\n    Data::Box(x)\n}}\n\n#[k::alias]\nfn one_two(k::term![Al::Pairs(1, 2)]: Term<Value>) -> Term<Value> {{\n    Data::Red()\n}}\n"
            ),
        ),
    ] {
        let manifest = package(&temporary.path().join(name), &source);
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(success, "{name}: {stderr}");
    }
}

/// Desugar productions for the overlap tests, each with the place sorts a case needs: a value, two
/// integers, two values, and a `KItem`.
const OVERLAP_PRODUCTIONS: &str = "#[k::constructors(sort = Value, result = KResult)]\n#[rustfmt::skip]\npub enum Pr {\n    #[k::syntax(\"dw({a})\")] #[k::desugar] Dw { a: Value },\n    #[k::syntax(\"dp({a}, {b})\")] #[k::desugar] Dp { a: Int, b: Int },\n    #[k::syntax(\"dv({a}, {b})\")] #[k::desugar] Dv { a: Value, b: Value },\n    #[k::syntax(\"dk({a})\")] #[k::desugar] Dk { a: KItem },\n}\n\n";

/// A desugar clause `name` with the parameters `parameters` (the subject and any typed binders),
/// whose result is `Data::Tag(result)`.
fn desugar(name: &str, parameters: &str, result: usize) -> String {
    format!(
        "#[k::desugar]\nfn {name}({parameters}: Term<Value>) -> Term<Value> {{\n    Data::Tag({result})\n}}\n\n"
    )
}

/// A source holding [`OVERLAP_PRODUCTIONS`] and `clauses`, each `(name, parameters)` a desugar
/// clause, in the order given; a production of `Pr` none of them expands, and `Al::Pairs`, get a
/// clause of their own, which no other clause shares a production with.
fn overlap_case(clauses: &[(&str, &str)]) -> String {
    let written = clauses
        .iter()
        .enumerate()
        .map(|(index, (name, parameters))| desugar(name, parameters, index))
        .collect::<String>();
    let fillers = [("Dw", "a"), ("Dp", "a, b"), ("Dv", "a, b"), ("Dk", "a")]
        .into_iter()
        .filter(|(production, _)| !written.contains(&format!("Pr::{production}(")))
        .map(|(production, arguments)| {
            desugar(
                &format!("fill_{}", production.to_lowercase()),
                &format!("k::term![Pr::{production}({arguments})]"),
                0,
            )
        })
        .collect::<String>();
    format!(
        "{OTHER_CLAUSES}#[k::alias]\nfn pairs(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {{\n    Data::Pair(y, x)\n}}\n\n{OVERLAP_PRODUCTIONS}{fillers}{written}"
    )
}

/// The overlap is reported where it is added, reading the source top to bottom: at the clause
/// written later, whatever the two clauses' names (`zz_first` is written above `aa_second`, and
/// would come second by name), naming the two in the order written. The earlier clause's subject
/// is labelled, a term both subjects match is named, `_` standing for any integer there, and the
/// repairs are given.
#[test]
fn an_overlap_is_reported_at_the_clause_written_later() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        &temporary.path().join("order"),
        &overlap_case(&[
            ("zz_first", "k::term![Pr::Dp(1, y)]"),
            ("aa_second", "k::term![Pr::Dp(x, y)]"),
        ]),
    );
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success, "{stderr}");
    let directory = format!("{}/", manifest.parent().unwrap().display());
    let diagnostic = stderr
        .lines()
        .skip_while(|line| !line.starts_with("error["))
        .take_while(|line| !line.is_empty())
        .map(|line| line.trim_end().replace(&directory, ""))
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r"
        error[krs::analysis::invalid-static-clause]: desugar clauses `zz_first` and `aa_second` of `Pr::Dp` overlap: `Pr::Dp(1, _)` matches both subjects, and the clauses of a production marked `#[k::desugar]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
           --> src/lib.rs:119:23
            |
        114 | fn zz_first(k::term![Pr::Dp(1, y)]: Term<Value>) -> Term<Value> {
            |                      ------ `zz_first`, written earlier, matches `Pr::Dp(1, _)` too
        ...
        119 | fn aa_second(k::term![Pr::Dp(x, y)]: Term<Value>) -> Term<Value> {
            |                       ^^^^^^
            |
            = help: make one subject more specific, so that no term matches both; or, where one clause is meant for the terms the other does not match, write the computation as a function whose fallback equation is `#[k::equation(owise)]`, or as rules whose fallback is `#[k::rule(owise)]`, which state the order a static clause cannot"]].assert_eq(&diagnostic);
}

/// What the overlap check compares, each row a case that a narrower check would decide otherwise:
/// - the subjects as KRS writes them, `dw(zero())` being `dw(red)`, not as authored;
/// - every alternative of a desugar's `A | B` against the other clause (`dp(2, y)`, the second
///   alternative, meets `dp(2, 3)`);
/// - every two clauses, not only neighbours (the first and the third of three);
/// - a typed binder's sort's subsorts, not that sort alone (`x: Int` meets `3`, and a `KItem`
///   binder meets `red`, a `Value`);
/// - every clause of the production wherever it is written, in another Rust module too.
#[test]
fn overlapping_static_clauses_are_found_wherever_they_overlap() {
    expect_test::expect![[r"
        restated:
        error[krs::analysis::invalid-static-clause]: desugar clauses `named` and `spelled` of `Pr::Dw` overlap: `Pr::Dw(Data::Red())` matches both subjects, and the clauses of a production marked `#[k::desugar]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
        --> src/lib.rs:119:21
        second-alternative:
        error[krs::analysis::invalid-static-clause]: desugar clauses `either` and `two_three` of `Pr::Dp` overlap: `Pr::Dp(2, 3)` matches both subjects, and the clauses of a production marked `#[k::desugar]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
        --> src/lib.rs:119:23
        first-and-third:
        error[krs::analysis::invalid-static-clause]: desugar clauses `one_one` and `one` of `Pr::Dp` overlap: `Pr::Dp(1, 1)` matches both subjects, and the clauses of a production marked `#[k::desugar]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
        --> src/lib.rs:124:17
        typed-subsort:
        error[krs::analysis::invalid-static-clause]: desugar clauses `int` and `three` of `Pr::Dw` overlap: `Pr::Dw(3)` matches both subjects, and the clauses of a production marked `#[k::desugar]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
        --> src/lib.rs:119:19
        kitem-binder:
        error[krs::analysis::invalid-static-clause]: desugar clauses `any` and `red` of `Pr::Dk` overlap: `Pr::Dk(Data::Red())` matches both subjects, and the clauses of a production marked `#[k::desugar]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
        --> src/lib.rs:119:17
        two-modules:
        error[krs::analysis::invalid-static-clause]: desugar clauses `first` and `second` of `Pr::Dp` overlap: `Pr::Dp(1, _)` matches both subjects, and the clauses of a production marked `#[k::desugar]` state no order between them (a static clause takes no `priority` or `owise`), so which of the two a program's expansion applies there is arbitrary
        --> src/lib.rs:122:20"]]
    .assert_eq(&refusals([
        (
            "restated",
            &overlap_case(&[
                ("named", "k::term![Pr::Dw(Al::Zero())]"),
                ("spelled", "k::term![Pr::Dw(Data::Red())]"),
            ]),
        ),
        (
            "second-alternative",
            &overlap_case(&[
                ("either", "k::term![Pr::Dp(1 | 2, y)]"),
                ("two_three", "k::term![Pr::Dp(2, 3)]"),
            ]),
        ),
        (
            "first-and-third",
            &overlap_case(&[
                ("one_one", "k::term![Pr::Dp(1, 1)]"),
                ("two", "k::term![Pr::Dp(2, y)]"),
                ("one", "k::term![Pr::Dp(1, y)]"),
            ]),
        ),
        (
            "typed-subsort",
            &overlap_case(&[
                ("int", "x: Int, k::term![Pr::Dw(x)]"),
                ("three", "k::term![Pr::Dw(3)]"),
            ]),
        ),
        (
            "kitem-binder",
            &overlap_case(&[
                ("any", "k::term![Pr::Dk(x)]"),
                ("red", "k::term![Pr::Dk(Data::Red())]"),
            ]),
        ),
        (
            "two-modules",
            &format!(
                "{}pub mod more {{\n    use super::*;\n\n    {}}}\n",
                overlap_case(&[("first", "k::term![Pr::Dp(1, y)]")]),
                desugar("second", "k::term![Pr::Dp(x, y)]", 2),
            ),
        ),
    ]));
}

/// Subjects no term matches both of are accepted, each row a case that a coarser check would
/// refuse: the alternatives of one clause, which share its result, are not compared with each
/// other (`1 | 01` are one value); `name @ pattern` binds `name` to the term the pattern matches,
/// so `dv(n @ box(y), n)` needs two equal arguments, which `dv(box(1), box(2))` does not have; and
/// a typed binder admits only its sort's terms, so `x: Int` meets neither `y: Bool` nor `red`.
#[test]
fn static_clauses_no_term_matches_both_of_are_accepted() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    for (name, source) in [
        (
            "own-alternatives",
            overlap_case(&[
                ("one", "k::term![Pr::Dp(1 | 01, y)]"),
                ("two", "k::term![Pr::Dp(2, y)]"),
            ]),
        ),
        (
            "as-pattern",
            overlap_case(&[
                ("same", "k::term![Pr::Dv(n @ Data::Box(y), n)]"),
                ("different", "k::term![Pr::Dv(Data::Box(1), Data::Box(2))]"),
            ]),
        ),
        (
            "typed-sorts",
            overlap_case(&[
                ("int", "x: Int, k::term![Pr::Dw(x)]"),
                ("bool", "y: Bool, k::term![Pr::Dw(y)]"),
            ]),
        ),
        (
            "typed-beside-constructor",
            overlap_case(&[
                ("int", "x: Int, k::term![Pr::Dw(x)]"),
                ("red", "k::term![Pr::Dw(Data::Red())]"),
            ]),
        ),
    ] {
        let manifest = package(&temporary.path().join(name), &source);
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(success, "{name}: {stderr}");
    }
}

/// The emitted rules that mention `needle`, one per line.
fn rules(k: &str, needle: &str) -> String {
    k.lines()
        .map(str::trim)
        .filter(|line| line.starts_with("rule ") && line.contains(needle))
        .collect::<Vec<_>>()
        .join("\n")
}

const TWO_WAY: &str = r"
#[k::alias]
fn items(k::term![Al::Items([x])]: Term<Value>) -> Term<Value> {
    Data::Two(x, [])
}

#[k::alias]
fn whole(k::term![Al::Whole(a)]: Term<Value>) -> Term<Value> {
    Data::Flag(k::matches!(a, Data::Box(_)))
}

#[k::alias]
fn pairs(k::term![Al::Pairs(x, y)]: Term<Value>) -> Term<Value> {
    Data::Pair(
        {
            let z = y;
            z
        },
        x + 1,
    )
}

#[k::alias]
fn elems(k::term![Al::Elems(set::item(x))]: Term<Value>) -> Term<Value> {
    Data::Bs(x, set::empty())
}

#[k::rule]
fn mk(k::term![Data::Mk(a, b)]: Term<Value>) -> Term<Value> {
    Data::Two(a, [])
}

#[k::rule]
fn probe(k::term![Data::Probe(a)]: Term<Value>) -> Term<Value> {
    Al::Whole(a)
}

#[k::rule]
fn calc(k::term![Data::Calc(a, b)]: Term<Value>) -> Term<Value> {
    Al::Pairs(a, b)
}
";

/// An alias whose subject every result match builds is accepted, a list of one element among
/// them, and the result may compute (`k::matches!`, a `let`, an operator). A printed value the
/// result matches prints as the alias: `two(1, [])` as `items([1])`. A list of an element and a
/// named rest is refused, as a list of several parts in any static subject is: static expansion
/// matches it as written, one of its spellings (`static_subjects.rs`). A computed result's printed value is evaluated, which holds no application
/// of the clause's generated function, so it prints expanded: `flag(true)`, `pair(5, 5)`. The
/// computing aliases are written in rules, whose `#let` and `:=K` k-rust lowers; a program that
/// writes one meets them unlowered (finding NT-8-1).
#[test]
fn a_two_way_alias_is_accepted_and_prints_backwards() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), TWO_WAY);
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
    for program in ["mk(1, 2)", "probe(box(3))", "calc(4, 5)"] {
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
    expect_test::expect![[r"
        rule items ( ListItem(X:KItem) ) => two ( X:KItem , .List ) [label(krsRule_DIGEST)]
        rule whole ( A:Value ) => flag ( ( box ( _ ) :=K A:Value ) ) [label(krsRule_DIGEST)]
        rule pairs ( X:Int , Y:Int ) => pair ( ( #let Z:Int = Y:Int #in Z:Int ) , X:Int +Int 1 ) [label(krsRule_DIGEST)]
        mk(1, 2) => items(ListItem ( 1 )) ~> .K
        probe(box(3)) => flag(true) ~> .K
        calc(4, 5) => pair(5, 5) ~> .K"]]
    .assert_eq(
        &[
            rules(&k, "rule items"),
            rules(&k, "rule whole"),
            rules(&k, "rule pairs"),
        ]
        .iter()
        .map(|rule| {
            rule.split("krsRule_")
                .next()
                .map(|head| format!("{head}krsRule_DIGEST)]"))
                .unwrap_or_default()
        })
        .chain(printed)
        .collect::<Vec<_>>()
        .join("\n"),
    );
}
