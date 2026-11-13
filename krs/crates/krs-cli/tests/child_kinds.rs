//! An instance's child, or a group record's, is a cell: its content means what the same spelling
//! means at a cell of the same kind outside every instance, its twin, whichever reader reads it.
//!
//! A computation child's brackets with a named rest are its items before that rest, a remainder
//! as a computation cell's `KCell(x, rest @ ..)` binds, which the signature declares no more than
//! the twin's: kept, moved out into another computation cell, moved in, and written into a
//! created instance, each with the twin's K. A map read or a map's entries in a group record's
//! child, inside a `?` group's `Some(..)` or an instance record, is the map the `cells!` twin's
//! `k::map![..]` writes.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A machine with a Map collection `th` whose instances hold a list `tl`, a computation `tk`, a
/// map `tm` and a group `tg` (a map `gm` and an `Int` `ga`); top cells of the same kinds (`ll`,
/// `aux`, `env`), a fixed group `gg` (a map `hm`, an `Int` `ha` and a computation `hk`) and a `?`
/// group `og` (a map `om` and an `Int` `ov`); `{SENTENCES}` is the sentences under test.
const SOURCE: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence, List, Map, list, map};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Go, Hold, Open, Park) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("hold")] Hold(),
    #[k::syntax("open {n}")] Open { n: Int },
    #[k::syntax("park")] Park(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::cell]
pub struct Tg {
    #[k::cell]
    pub gm: Map,
    #[k::cell]
    pub ga: Int,
}

#[k::cell]
pub struct Th {
    #[k::cell]
    pub tid: Int,
    #[k::cell]
    pub tl: List,
    #[k::cell]
    pub tk: KSequence,
    #[k::cell]
    pub tm: Map,
    #[k::cell(nested)]
    pub tg: Tg,
}

#[k::cell]
pub struct Ths {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub th: Th,
}

#[k::cell]
pub struct Gg {
    #[k::cell]
    pub hm: Map,
    #[k::cell]
    pub ha: Int,
    #[k::cell]
    pub hk: KSequence,
}

#[k::cell]
pub struct Og {
    #[k::cell]
    pub om: Map,
    #[k::cell]
    pub ov: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub ll: List,
    #[k::cell]
    pub aux: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub out: List,
    #[k::cell(nested)]
    pub gg: Gg,
    #[k::cell(multiplicity = "?", nested)]
    pub og: Option<Og>,
    #[k::cell(nested)]
    pub ths: Ths,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            ll: list::empty(),
            aux: k::k![],
            env: k::map![],
            out: list::empty(),
            gg: Gg { hm: k::map![], ha: 0, hk: k::k![] },
            og: Some(Og { om: k::map![0 -> 7], ov: 0 }),
            ths: Ths { th: Th { tid: 0, tl: list::empty(), tk: k::k![], tm: k::map![], tg: Tg { gm: k::map![0 -> 5], ga: 0 } } },
        }
    }
}

{SENTENCES}
"#;

const KC: &str = "k::configuration::";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is [`SOURCE`] with `sentences`.
fn package(root: &Path, name: &str, sentences: &str) -> PathBuf {
    package_with(root, name, SOURCE, sentences)
}

/// Writes a one-package workspace whose library is `source` with `sentences`.
fn package_with(root: &Path, name: &str, source: &str, sentences: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        source.replace("{SENTENCES}", sentences),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CHILD-KINDS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The verdict on the sentence `go` of `sentences`: the emitted rule on one line, or the first
/// error line.
fn verdict(target: &Path, root: &Path, name: &str, sentences: &str) -> String {
    emitted(target, &package(root, name, sentences))
}

/// The verdict on the sentence `go` of the package at `manifest`: the emitted rule on one line, or
/// the first error line.
fn emitted(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    if !success {
        return stderr
            .lines()
            .find(|line| line.starts_with("error["))
            .unwrap_or_else(|| panic!("no error headline:\n{stderr}"))
            .to_owned();
    }
    let mut k = krs_test_support::without_source_comments(
        &fs::read_to_string(output.join("definition.k")).unwrap(),
    );
    // A claim is emitted to the specification.
    if let Ok(spec) = fs::read_to_string(output.join("spec.k")) {
        k.push_str(&krs_test_support::without_source_comments(&spec));
    }
    let start = k
        .find("rule [go]:")
        .or_else(|| k.find("claim [go]:"))
        .unwrap_or_else(|| panic!("`go` is emitted:\n{k}"));
    let end = ["rule [", "claim [", "endmodule"]
        .iter()
        .filter_map(|next| k[start + 1..].find(next))
        .min()
        .map_or(k.len(), |end| start + 1 + end);
    k[start..end]
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

/// A readable rule `go`.
fn readable(clause: &str) -> String {
    format!("k::rules! {{\n    for Machine;\n    use Cmd::*;\n\n    {clause}\n}}\n")
}

/// A readable claim `go`.
fn readable_claim(clause: &str) -> String {
    format!(
        "k::claims! {{\n    for Machine;\n    use Cmd::*;\n\n    #[k::claim(all_paths)] {clause}\n}}\n"
    )
}

/// A `cells!` claim `go` with the typed parameters `params`, from `subject` to `result`.
fn cells_claim(params: &str, subject: &str, result: &str) -> String {
    format!(
        "#[k::claim(all_paths, label = \"go\")]\npub fn go(\n    {params}k::cells! {{ {subject}, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ {result}, ..state }}\n}}\n"
    )
}

/// A `cells!` rule `go` with the typed parameters `params`, from `subject` to `result`.
fn cells(params: &str, subject: &str, result: &str) -> String {
    format!(
        "#[k::rule(label = \"go\")]\npub fn go(\n    {params}k::cells! {{ {subject}, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ {result}, ..state }}\n}}\n"
    )
}

/// The verdict of each row, `name: verdict`.
fn table(rows: &[(&str, String)]) -> String {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    rows.iter()
        .map(|(name, sentences)| {
            format!(
                "{name}: {}",
                verdict(target.path(), temporary.path(), name, sentences)
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// A `cells!` instance's computation child written in brackets with a named rest is its items
/// before that remainder, as the twin `KCell(x, rest @ ..)` is, undeclared as the twin's is: kept
/// (`kept`, beside the twin `kept-twin` and the `k::k!` spelling), moved out (`out`), moved in
/// (`in`), and written into a created instance (`created`), each with the twin's K. Declaring the
/// rest is refused as declaring the twin's is (`kept-declared`); a list child's rest is a term
/// binder its signature declares, as its twin's is (`list-declared`), and refused undeclared as
/// the twin's is (`list-undeclared`).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of the spellings beside their twins, its expectation inline."
)]
fn a_computation_child_s_named_rest_is_its_twin_s_remainder() {
    let th = |child: &str| {
        format!("Ths::th: {{ me @ k::fragment![crate::Th {{ {child}, .. }}], i @ .. }}")
    };
    let thr =
        |child: &str| format!("Ths::th: {{ k::fragment![crate::Th {{ {child}, ..me }}], ..i }}");
    let go = format!("k: {KC}KCell(Cmd::Go(), ..)");
    let kept = format!("k: {KC}KCell(..)");
    let rows = [
        (
            "kept",
            cells(
                "",
                &format!("{go}, {}", th("tk: [Cmd::Go(), rest @ ..]")),
                &format!("{kept}, {}", thr("tk: [Cmd::Hold(), ..rest]")),
            ),
        ),
        (
            "kept-k",
            cells(
                "",
                &format!("{go}, {}", th("tk: k::k![Cmd::Go(), rest @ ..]")),
                &format!("{kept}, {}", thr("tk: k::k![Cmd::Hold(), ..rest]")),
            ),
        ),
        (
            "kept-twin",
            cells(
                "",
                &format!("{go}, aux: {KC}KCell(Cmd::Go(), rest @ ..)"),
                &format!("{kept}, aux: {KC}KCell(Cmd::Hold(), ..rest)"),
            ),
        ),
        (
            "kept-declared",
            cells(
                "rest: KSequence,\n    ",
                &format!("{go}, {}", th("tk: [Cmd::Go(), rest @ ..]")),
                &format!("{kept}, {}", thr("tk: [Cmd::Hold(), ..rest]")),
            ),
        ),
        (
            "kept-declared-twin",
            cells(
                "rest: KSequence,\n    ",
                &format!("{go}, aux: {KC}KCell(Cmd::Go(), rest @ ..)"),
                &format!("{kept}, aux: {KC}KCell(Cmd::Hold(), ..rest)"),
            ),
        ),
        (
            "out",
            cells(
                "",
                &format!(
                    "{go}, {}, aux: {KC}KCell()",
                    th("tk: [Cmd::Go(), rest @ ..]")
                ),
                &format!("{kept}, {}, aux: {KC}KCell(..rest)", thr("tk: []")),
            ),
        ),
        (
            "in",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), rest @ ..), {}", th("tk: []")),
                &format!("k: {KC}KCell(), {}", thr("tk: [..rest]")),
            ),
        ),
        (
            "created",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), rest @ ..), Ths::th: {{ i @ .. }}"),
                &format!(
                    "k: {KC}KCell(), Ths::th: {{ k::fragment![crate::Th {{ tid: 1, tl: [], tk: [Cmd::Hold(), ..rest], tm: k::map![], tg: crate::Tg {{ gm: k::map![], ga: 0 }} }}], ..i }}"
                ),
            ),
        ),
        (
            "list-declared",
            cells(
                "x: Int,\n    rest: List,\n    ",
                &format!("{go}, {}, out: {KC}Cell(_)", th("tl: [x, rest @ ..]")),
                &format!("{kept}, {}, out: {KC}Cell(rest)", thr("tl: [x]")),
            ),
        ),
        (
            "list-undeclared",
            cells(
                "x: Int,\n    ",
                &format!("{go}, {}, out: {KC}Cell(_)", th("tl: [x, rest @ ..]")),
                &format!("{kept}, {}, out: {KC}Cell(rest)", thr("tl: [x]")),
            ),
        ),
        (
            "list-undeclared-twin",
            cells(
                "x: Int,\n    ",
                &format!("{go}, ll: {KC}Cell([x, rest @ ..]), out: {KC}Cell(_)"),
                &format!("{kept}, ll: {KC}Cell([x]), out: {KC}Cell(rest)"),
            ),
        ),
    ];
    expect_test::expect![[r"
        kept: rule [go]: <k> go => .K ... </k> <th> <tk> go ~> Rest:K => hold ~> Rest:K </tk> ... </th>
        kept-k: rule [go]: <k> go => .K ... </k> <th> <tk> go ~> Rest:K => hold ~> Rest:K </tk> ... </th>
        kept-twin: rule [go]: <k> go => .K ... </k> <aux> go ~> Rest:K => hold ~> Rest:K </aux>
        kept-declared: error[krs::syntax::unsupported-rule-signature]: the rest `rest` of the computation child `tk` is a remainder of the computation, as a computation cell's `KCell(x, rest @ ..)` rest is, and a rule's typed parameters declare no remainder: leave `rest` out of them
        kept-declared-twin: error[krs::syntax::unsupported-rule-signature]: unsupported rule signature: typed term parameters must declare every term binder of the subject and function context, in first-occurrence order (hole binders included; `_`, remainders, HERE, instance labels and local binders excluded)
        out: rule [go]: <k> go => .K ... </k> <th> <tk> go ~> Rest:K => .K </tk> ... </th> <aux> .K => Rest:K </aux>
        in: rule [go]: <k> go ~> Rest:K => .K </k> <th> <tk> .K => Rest:K </tk> ... </th>
        created: rule [go]: <k> go ~> Rest:K => .K </k> (.Bag => <th> <tid> 1 </tid> <tl> .List </tl> <tk> hold ~> Rest:K </tk> <tm> .Map </tm> <tg> <gm> .Map </gm> <ga> 0 </ga> </tg> </th>)
        list-declared: rule [go]: <k> go => .K ... </k> <th> <tl> ListItem(X:Int) Rest:List => ListItem(X:Int) </tl> ... </th> <out> _ => Rest:List </out>
        list-undeclared: error[krs::syntax::unsupported-rule-signature]: the rest `rest` of the list child `tl` is a list, a term of the child's sort, as a list cell's `Cell([x, rest @ ..])` rest is, and a rule's typed parameters declare every term it binds: declare `rest` among them at the child's sort
        list-undeclared-twin: error[krs::syntax::unsupported-rule-signature]: unsupported rule signature: typed term parameters must declare every term binder of the subject and function context, in first-occurrence order (hole binders included; `_`, remainders, HERE, instance labels and local binders excluded)"]].assert_eq(&table(&rows));
}

/// [`SOURCE`] with a cons list `Ws` and its constant `EMPTY`, a `List` constant `ELS`, a computation
/// constructor `Saved`, an instance child `tw: Ws`, a top cell `ww: Ws`, and a list child `hl` of the
/// fixed group `gg`.
fn named_rest_source() -> String {
    let source = SOURCE
        .replace("use k::KResult;", "use k::{KItem, KResult};")
        .replace(
            "    Stmt;\n    Value: Stmt + KResult;",
            "    Stmt;\n    Ws: KItem;\n    Value: Stmt + KResult;",
        )
        .replace("(Go, Hold, Open, Park)", "(Go, Hold, Open, Park, Saved)")
        .replace(
            "    #[k::syntax(\"park\")] Park(),\n",
            "    #[k::syntax(\"park\")] Park(),\n    #[k::syntax(\"saved({body})\")] Saved { body: KSequence },\n",
        )
        .replace(
            "#[k::cell]\npub struct Tg {",
            "#[k::constructors(sort = Ws, result = KResult)]\n#[k::cons_list]\n#[k::precedence((WsNil, WsCons))]\npub enum Wst {\n    #[k::syntax(\".Ws\")]\n    WsNil(),\n    #[k::syntax(\"{head} : {tail}\")]\n    WsCons { head: Int, tail: Ws },\n}\n\n#[k::constant]\nconst EMPTY: Ws = Wst::WsNil();\n\n#[k::constant]\nconst ELS: List = list::item(5);\n\n#[k::constant]\nconst PRELUDE: KSequence = Cmd::Hold();\n\n#[k::cell]\npub struct Tg {",
        )
        .replace(
            "    #[k::cell]\n    pub tm: Map,\n",
            "    #[k::cell]\n    pub tm: Map,\n    #[k::cell]\n    pub tw: Ws,\n",
        )
        .replace("tm: k::map![], tg:", "tm: k::map![], tw: Wst::WsNil(), tg:")
        .replace(
            "    #[k::cell]\n    pub hk: KSequence,\n}",
            "    #[k::cell]\n    pub hk: KSequence,\n    #[k::cell]\n    pub hl: List,\n}",
        )
        .replace("hk: k::k![] }", "hk: k::k![], hl: list::empty() }")
        .replace(
            "    #[k::cell]\n    pub out: List,\n",
            "    #[k::cell]\n    pub out: List,\n    #[k::cell]\n    pub ww: Ws,\n",
        )
        .replace("out: list::empty(),", "out: list::empty(),\n            ww: Wst::WsNil(),");
    assert!(
        [
            "const EMPTY",
            "pub tw: Ws",
            "pub hl: List",
            "pub ww: Ws",
            "Saved { body"
        ]
        .iter()
        .all(|part| source.contains(part)),
        "the source has the constants, `tw`, `hl`, `ww` and `Saved`"
    );
    source
}

/// A result's `..name` in a child's brackets is what `name` is, as at the twin cell: a constant is
/// the list it denotes (`constant-list`, `constant-cons`, a fixed fragment's list child
/// `constant-fragment`, each beside its twin), a declared term of sort `K` the computation written
/// after the items (`term`), a remainder the subject binds the remainder written back, which a
/// list child does not hold (`remainder-in-list`), and a name bound nowhere an unbound name
/// (`unbound`).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of the spellings beside their twins, its expectation inline."
)]
fn a_result_s_named_rest_is_what_the_name_is() {
    let source = named_rest_source();
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let th = |child: &str| {
        format!("Ths::th: {{ me @ k::fragment![crate::Th {{ {child}, .. }}], i @ .. }}")
    };
    let thr =
        |child: &str| format!("Ths::th: {{ k::fragment![crate::Th {{ {child}, ..me }}], ..i }}");
    let put = format!("k: {KC}KCell(Cmd::Open {{ n: x }}, ..)");
    let kept = format!("k: {KC}KCell(..)");
    let x = "x: Int,\n    ";
    let rows = [
        (
            "constant-list",
            cells(
                x,
                &format!("{put}, {}", th("tl: _")),
                &format!("{kept}, {}", thr("tl: [x, ..ELS]")),
            ),
        ),
        (
            "constant-list-twin",
            cells(
                x,
                &format!("{put}, ll: {KC}Cell(_)"),
                &format!("{kept}, ll: {KC}Cell([x, ..ELS])"),
            ),
        ),
        (
            "constant-cons",
            cells(
                x,
                &format!("{put}, {}", th("tw: _")),
                &format!("{kept}, {}", thr("tw: [x, ..EMPTY]")),
            ),
        ),
        (
            "constant-cons-twin",
            cells(
                x,
                &format!("{put}, ww: {KC}Cell(_)"),
                &format!("{kept}, ww: {KC}Cell([x, ..EMPTY])"),
            ),
        ),
        (
            "constant-fragment",
            cells(
                x,
                &format!("{put}, gg: k::fragment![crate::Gg {{ .. }}]"),
                &format!("{kept}, gg: k::fragment![crate::Gg {{ hl: [x, ..ELS], .. }}]"),
            ),
        ),
        (
            "constant-fragment-twin",
            cells(
                x,
                &format!("{put}, Gg::hl: {KC}Cell(_)"),
                &format!("{kept}, Gg::hl: {KC}Cell([x, ..ELS])"),
            ),
        ),
        (
            "term",
            cells(
                "t: KSequence,\n    ",
                &format!(
                    "k: {KC}KCell(Cmd::Saved {{ body: t }}, ..), {}",
                    th("tk: []")
                ),
                &format!("{kept}, {}", thr("tk: [Cmd::Hold(), ..t]")),
            ),
        ),
        (
            "term-twin",
            cells(
                "t: KSequence,\n    ",
                &format!("k: {KC}KCell(Cmd::Saved {{ body: t }}, ..), aux: {KC}KCell()"),
                &format!("{kept}, aux: {KC}KCell(Cmd::Hold(), ..t)"),
            ),
        ),
        (
            "remainder-in-list",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), rest @ ..), {}", th("tl: []")),
                &format!("k: {KC}KCell(), {}", thr("tl: [1, ..rest]")),
            ),
        ),
        (
            "unbound",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), ..), {}", th("tk: []")),
                &format!("{kept}, {}", thr("tk: [Cmd::Hold(), ..zz]")),
            ),
        ),
    ];
    let table = rows
        .iter()
        .map(|(name, sentences)| {
            let manifest = package_with(temporary.path(), name, &source, sentences);
            format!("{name}: {}", emitted(target.path(), &manifest))
        })
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r"
        constant-list: rule [go]: <k> open X:Int => .K ... </k> <th> <tl> _ => ListItem(X:Int) ListItem(5) </tl> ... </th>
        constant-list-twin: rule [go]: <k> open X:Int => .K ... </k> <ll> _ => ListItem(X:Int) ListItem(5) </ll>
        constant-cons: rule [go]: <k> open X:Int => .K ... </k> <th> <tw> _ => X:Int : . Ws </tw> ... </th>
        constant-cons-twin: rule [go]: <k> open X:Int => .K ... </k> <ww> _ => X:Int : . Ws </ww>
        constant-fragment: rule [go]: <k> open X:Int => .K ... </k> <hl> _ => ListItem(X:Int) ListItem(5) </hl>
        constant-fragment-twin: rule [go]: <k> open X:Int => .K ... </k> <hl> _ => ListItem(X:Int) ListItem(5) </hl>
        term: rule [go]: <k> saved ( T:K ) => .K ... </k> <th> <tk> .K => hold ~> T:K </tk> ... </th>
        term-twin: rule [go]: <k> saved ( T:K ) => .K ... </k> <aux> .K => hold ~> T:K </aux>
        remainder-in-list: error[krs::syntax::invalid-list-notation]: `..rest` in the list child `tl` writes `rest`, which the subject binds as the rest of a computation (`rest @ ..`), and a list's rest is a list: a remainder is written back only into a cell of its own kind; write the list's elements, or name a list's rest in the subject (`[x, rest @ ..]`, with `rest` declared at the list's sort) and write that
        unbound: error[krs::expand::unbound-name]: `zz` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one"]].assert_eq(&table);
}

/// A map read or a map's entries in a group record's child, inside a `?` group's `Some(..)` or an
/// instance record, is the map its `cells!` twin's `k::map![..]` writes, read (`read-og`,
/// `read-inst`), kept by the record's `..` (`kept-og`, `kept-inst`) and written (`write-og`,
/// `write-inst`), each beside its twin. A map read in a result names no map, as at a record's top
/// level (`read-in-result`). A named rest there is the rest of the map, a map term, as in its
/// `cells!` twin, which declares it (`named`, `named-twin`); in a group record at a readable
/// record's top level, read as its children's own cells, it is a stated limit (`named-top`).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of the spellings beside their twins, its expectation inline."
)]
fn a_map_read_in_an_instance_or_present_group_record_is_its_twin_s() {
    let th = |child: &str| format!("th: {{ me @ Th {{ {child}, .. }}, .. }}");
    let thr = |child: &str| format!("th: {{ Th {{ {child}, ..me }}, .. }}");
    let cth = |child: &str| {
        format!("Ths::th: {{ me @ k::fragment![crate::Th {{ {child}, .. }}], i @ .. }}")
    };
    let cthr =
        |child: &str| format!("Ths::th: {{ k::fragment![crate::Th {{ {child}, ..me }}], ..i }}");
    let go = format!("k: {KC}KCell(Cmd::Go(), ..)");
    let kept = format!("k: {KC}KCell(..)");
    let rows = [
        (
            "read-og",
            readable(
                "go: { k: [Go(), ..], og: Some(Og { om: { 0 -> v, .. }, .. }), out: _ } => { k: [..], out: [v] };",
            ),
        ),
        (
            "read-og-twin",
            cells(
                "v: Int,\n    ",
                &format!(
                    "{go}, og: Some(k::fragment![crate::Og {{ om: k::map![0 -> v, ..], .. }}]), out: {KC}Cell(_)"
                ),
                &format!("{kept}, out: {KC}Cell([v])"),
            ),
        ),
        (
            "read-inst",
            readable(&format!(
                "go: {{ k: [Go(), ..], {}, out: _ }} => {{ k: [..], out: [v] }};",
                th("tg: Tg { gm: { 0 -> v, .. }, .. }")
            )),
        ),
        (
            "read-inst-twin",
            cells(
                "v: Int,\n    ",
                &format!(
                    "{go}, {}, out: {KC}Cell(_)",
                    cth("tg: crate::Tg { gm: k::map![0 -> v, ..], .. }")
                ),
                &format!("{kept}, out: {KC}Cell([v])"),
            ),
        ),
        (
            "kept-og",
            readable(
                "go: { k: [Go(), ..], og: Some(Og { om: { 0 -> v, .. }, .. }) } => { k: [..], og: Some(Og { ov: v, .. }) };",
            ),
        ),
        (
            "kept-og-twin",
            cells(
                "v: Int,\n    ",
                &format!(
                    "{go}, og: Some(k::fragment![crate::Og {{ om: k::map![0 -> v, ..], .. }}])"
                ),
                &format!("{kept}, og: Some(k::fragment![crate::Og {{ ov: v, .. }}])"),
            ),
        ),
        (
            "kept-inst",
            readable(&format!(
                "go: {{ k: [Go(), ..], {} }} => {{ k: [..], {} }};",
                th("tg: Tg { gm: { 0 -> v, .. }, .. }"),
                thr("tg: Tg { ga: v, .. }")
            )),
        ),
        (
            "kept-inst-twin",
            cells(
                "v: Int,\n    ",
                &format!(
                    "{go}, {}",
                    cth("tg: crate::Tg { gm: k::map![0 -> v, ..], .. }")
                ),
                &format!("{kept}, {}", cthr("tg: crate::Tg { ga: v, .. }")),
            ),
        ),
        (
            "write-og",
            readable(
                "go: { k: [Go(), ..], og: Some(Og { .. }) } => { k: [..], og: Some(Og { om: { 0 -> 1 }, .. }) };",
            ),
        ),
        (
            "write-og-twin",
            cells(
                "",
                &format!("{go}, og: Some(k::fragment![crate::Og {{ .. }}])"),
                &format!("{kept}, og: Some(k::fragment![crate::Og {{ om: k::map![0 -> 1], .. }}])"),
            ),
        ),
        (
            "write-inst",
            readable(&format!(
                "go: {{ k: [Go(), ..], {} }} => {{ k: [..], {} }};",
                th("tg: Tg { .. }"),
                thr("tg: Tg { gm: { 0 -> 1 }, .. }")
            )),
        ),
        (
            "write-inst-twin",
            cells(
                "",
                &format!("{go}, {}", cth("tg: crate::Tg { .. }")),
                &format!(
                    "{kept}, {}",
                    cthr("tg: crate::Tg { gm: k::map![0 -> 1], .. }")
                ),
            ),
        ),
        (
            "read-in-result",
            readable(&format!(
                "go: {{ k: [Go(), ..], {} }} => {{ k: [..], {} }};",
                th("tg: Tg { .. }"),
                thr("tg: Tg { gm: { 0 -> 1, .. }, .. }")
            )),
        ),
        (
            "named",
            readable(&format!(
                "go: {{ k: [Go(), ..], {}, out: _ }} => {{ k: [..], out: [v] }};",
                th("tg: Tg { gm: { 0 -> v, r @ .. }, .. }")
            )),
        ),
        (
            "named-twin",
            cells(
                "v: Int,\n    r: Map,\n    ",
                &format!(
                    "{go}, {}, out: {KC}Cell(_)",
                    cth("tg: crate::Tg { gm: k::map![0 -> v, r @ ..], .. }")
                ),
                &format!("{kept}, out: {KC}Cell([v])"),
            ),
        ),
        (
            "named-top",
            readable(
                "go: { k: [Go(), ..], gg: Gg { hm: { 0 -> v, r @ .. }, .. }, out: _ } => { k: [..], out: [v] };",
            ),
        ),
    ];
    expect_test::expect![[r"
        read-og: rule [go]: <k> go => .K ... </k> <og> <om> 0 |-> V:KItem _ </om> <ov> _ </ov> </og> <out> _ => ListItem(V:KItem) </out>
        read-og-twin: rule [go]: <k> go => .K ... </k> <og> <om> 0 |-> V:Int _ </om> <ov> _ </ov> </og> <out> _ => ListItem(V:Int) </out>
        read-inst: rule [go]: <k> go => .K ... </k> <th> <tg> <gm> 0 |-> V:KItem _ </gm> <ga> _ </ga> </tg> ... </th> <out> _ => ListItem(V:KItem) </out>
        read-inst-twin: rule [go]: <k> go => .K ... </k> <th> <tg> <gm> 0 |-> V:Int _ </gm> <ga> _ </ga> </tg> ... </th> <out> _ => ListItem(V:Int) </out>
        kept-og: rule [go]: <k> go => .K ... </k> (<og> <om> ( 0 |-> V:Int _ #as OgOm:Map ) </om> <ov> _ </ov> </og> => <og> <om> OgOm:Map </om> <ov> V:Int </ov> </og>)
        kept-og-twin: rule [go]: <k> go => .K ... </k> (<og> <om> ( 0 |-> V:Int _ #as OgOm:Map ) </om> <ov> _ </ov> </og> => <og> <om> OgOm:Map </om> <ov> V:Int </ov> </og>)
        kept-inst: rule [go]: <k> go => .K ... </k> <th> (<tg> <gm> ( 0 |-> V:Int _ #as MeTgGm:Map ) </gm> <ga> _ </ga> </tg> => <tg> <gm> MeTgGm:Map </gm> <ga> V:Int </ga> </tg>) ... </th>
        kept-inst-twin: rule [go]: <k> go => .K ... </k> <th> (<tg> <gm> ( 0 |-> V:Int _ #as MeTgGm:Map ) </gm> <ga> _ </ga> </tg> => <tg> <gm> MeTgGm:Map </gm> <ga> V:Int </ga> </tg>) ... </th>
        write-og: rule [go]: <k> go => .K ... </k> (<og> <om> _ </om> <ov> OgOv:Int </ov> </og> => <og> <om> .Map [ 0 <- 1 ] </om> <ov> OgOv:Int </ov> </og>)
        write-og-twin: rule [go]: <k> go => .K ... </k> (<og> <om> _ </om> <ov> OgOv:Int </ov> </og> => <og> <om> .Map [ 0 <- 1 ] </om> <ov> OgOv:Int </ov> </og>)
        write-inst: rule [go]: <k> go => .K ... </k> <th> (<tg> <gm> _ </gm> <ga> MeTgGa:Int </ga> </tg> => <tg> <gm> .Map [ 0 <- 1 ] </gm> <ga> MeTgGa:Int </ga> </tg>) ... </th>
        write-inst-twin: rule [go]: <k> go => .K ... </k> <th> (<tg> <gm> _ </gm> <ga> MeTgGa:Int </ga> </tg> => <tg> <gm> .Map [ 0 <- 1 ] </gm> <ga> MeTgGa:Int </ga> </tg>) ... </th>
        read-in-result: error[krs::syntax::rust-syntax]: the entry of the cell `gm` writes braces holding a rest in a result (`{ k -> v, .. }`, `{ k -> v, ..m }`): a readable record's braces holding a rest are a map read, a pattern, which writes nothing; a result's map is a term, the literal over a map `m` its subject binds, the map whole or its rest named `m @ ..` (`map![k -> v, ..m]`), or those entries alone (`{ k -> v }`, `map![k -> v]`); keeping the entries a result does not name, with `..`, is a frame write no route lowers yet (a stated limitation)
        named: rule [go]: <k> go => .K ... </k> <th> <tg> <gm> 0 |-> V:KItem R:Map </gm> <ga> _ </ga> </tg> ... </th> <out> _ => ListItem(V:KItem) </out>
        named-twin: rule [go]: <k> go => .K ... </k> <th> <tg> <gm> 0 |-> V:Int R:Map </gm> <ga> _ </ga> </tg> ... </th> <out> _ => ListItem(V:Int) </out>
        named-top: rule [go]: <k> go => .K ... </k> <gg> <hm> 0 |-> V:KItem R:Map </hm> <ha> _ </ha> <hk> _ </hk> </gg> <out> _ => ListItem(V:KItem) </out>"]].assert_eq(&table(&rows));
}

/// Rules writing and reading a map in an instance's group record and reading one in a `?` group's
/// record run: `open` creates an instance whose group's map holds `0 -> 5` and `park` copies the
/// present group's entry `0` (`7`, from the initializer) and the instance group's into `out`.
#[test]
fn a_map_read_in_a_present_group_and_an_instance_group_runs() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rules = format!(
        "k::rules! {{\n    for Stmt;\n    use Cmd::*;\n\n    seq: Seq(s1, s2) => k::k![s1, s2];\n}}\n\nk::rules! {{\n    for Machine;\n    use Cmd::*;\n\n    {}\n    {}\n}}\n",
        "open: { k: [Open(n), ..], th: { .. } } => { k: [..], th: { Th { tid: n, tl: [], tk: [], tm: map::empty(), tg: Tg { gm: { 0 -> 5 }, ga: 0 } }, .. } };",
        "park: { k: [Park(), ..], og: Some(Og { om: { 0 -> a, .. }, .. }), th: { Th { tg: Tg { gm: { 0 -> b, .. }, .. }, .. }, .. }, out: _ } => { k: [..], out: [a, b] };",
    );
    let manifest = package(temporary.path(), "run-maps", &rules);
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "open 1 park\n").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stdout}\n{stderr}");
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let start = flat.find("<out>").unwrap();
    let end = flat.find("</out>").unwrap() + "</out>".len();
    expect_test::expect!["<out> ListItem ( 7 ) ListItem ( 5 ) </out>"].assert_eq(&flat[start..end]);
}

/// One spelling has one meaning on every route: a cell's content, an instance's child and a group
/// record's child read alike, each beside its twin (CHILDLEFT).
/// - A remainder is written back only as the rest of a cell of its own kind, at a cell as at a
///   child: a computation's rest in a list cell (`remainder-list`, `remainder-list-whole`), a
///   map's in a list cell or a computation (`map-rest-list`, `map-rest-computation`), a
///   computation's in a map (`remainder-map`), each one refusal, the list child's
///   (`remainder-list-child`).
/// - A name bound nowhere is an unbound name wherever its rest is written (`unbound-computation`,
///   `unbound-map`, beside `unbound-list`).
/// - A claim's result sees the start state's remainders as a rule's does (`claim-list-undeclared`,
///   beside `list-undeclared`; `claim-map-rest-moved`, beside `map-rest-moved`).
/// - A top-level readable group record writes a map child over the group's term
///   (`top-write`, beside its twin) and names a map child's rest (`top-named`, `top-named-back`,
///   each beside its twin).
/// - A record child's `k::k![..]` is its computation's content (`k-result`, beside the brackets
///   `k-result-brackets`; `k-fragment`, `k-fragment-result`, beside `k-fragment-twin`).
/// - A pattern child's `[..]` is its whole content (`any-computation`, beside `any-computation-twin`;
///   a list child's is refused as its twin's is, `any-list`, `any-list-twin`).
/// - A readable `map![k -> v, ..]` is a literal (NT-19), whose `..` names no map, at a group
///   record's child as at its top cell: refused alike (`map-pattern`, `map-pattern-present`,
///   `map-pattern-instance-group`, `map-pattern-instance`, `map-pattern-cell`), beside the braces that
///   read the map (`map-braces`).
/// - A subject that names its rest is told to put it back (`named-rest-kept`).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of the spellings beside their twins, its expectation inline."
)]
fn every_spelling_of_a_child_means_its_twin() {
    let source = named_rest_source();
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let th = |child: &str| {
        format!("Ths::th: {{ me @ k::fragment![crate::Th {{ {child}, .. }}], i @ .. }}")
    };
    let thr =
        |child: &str| format!("Ths::th: {{ k::fragment![crate::Th {{ {child}, ..me }}], ..i }}");
    let rth = |child: &str| format!("th: {{ me @ Th {{ {child}, .. }}, .. }}");
    let go = format!("k: {KC}KCell(Cmd::Go(), ..)");
    let rest = format!("k: {KC}KCell(Cmd::Go(), rest @ ..)");
    let kept = format!("k: {KC}KCell(..)");
    let done = format!("k: {KC}KCell()");
    let map_rest = format!("env: {KC}Cell(k::map![0 -> _, r @ ..])");
    let map_out = format!("env: {KC}Cell(k::map![0 -> 1])");
    let x = "x: Int,\n    ";
    let rows = [
        (
            "remainder-list",
            cells(
                "",
                &format!("{rest}, ll: {KC}Cell(_)"),
                &format!("{done}, ll: {KC}Cell([1, ..rest])"),
            ),
        ),
        (
            "remainder-list-whole",
            cells(
                "",
                &format!("{rest}, ll: {KC}Cell(_)"),
                &format!("{done}, ll: {KC}Cell(rest)"),
            ),
        ),
        (
            "remainder-list-child",
            cells(
                "",
                &format!("{rest}, {}", th("tl: []")),
                &format!("{done}, {}", thr("tl: [1, ..rest]")),
            ),
        ),
        (
            "map-rest-list",
            cells(
                "",
                &format!("{go}, {map_rest}, ll: {KC}Cell(_)"),
                &format!("{kept}, {map_out}, ll: {KC}Cell([1, ..r])"),
            ),
        ),
        (
            "map-rest-computation",
            cells(
                "",
                &format!("{go}, {map_rest}, aux: {KC}KCell()"),
                &format!("{kept}, {map_out}, aux: {KC}KCell(Cmd::Hold(), ..r)"),
            ),
        ),
        (
            "remainder-map",
            cells(
                "",
                &format!("{rest}, env: {KC}Cell(_)"),
                &format!("{done}, env: {KC}Cell(k::map![0 -> 1, ..rest])"),
            ),
        ),
        (
            "unbound-computation",
            cells(
                "",
                &format!("{go}, aux: {KC}KCell()"),
                &format!("{kept}, aux: {KC}KCell(Cmd::Hold(), ..zz)"),
            ),
        ),
        (
            "unbound-map",
            cells(
                "",
                &format!("{go}, env: {KC}Cell(_)"),
                &format!("{kept}, env: {KC}Cell(k::map![0 -> 1, ..zz])"),
            ),
        ),
        (
            "unbound-list",
            cells(
                "",
                &format!("{go}, ll: {KC}Cell(_)"),
                &format!("{kept}, ll: {KC}Cell([1, ..zz])"),
            ),
        ),
        (
            "claim-list-undeclared",
            cells_claim(
                x,
                &format!("{go}, {}, out: {KC}Cell(_)", th("tl: [x, rest @ ..]")),
                &format!("{kept}, {}, out: {KC}Cell(rest)", thr("tl: [x]")),
            ),
        ),
        (
            "list-undeclared",
            cells(
                x,
                &format!("{go}, {}, out: {KC}Cell(_)", th("tl: [x, rest @ ..]")),
                &format!("{kept}, {}, out: {KC}Cell(rest)", thr("tl: [x]")),
            ),
        ),
        (
            "claim-map-rest-moved",
            cells_claim(
                "",
                &format!(
                    "{go}, gg: k::fragment![crate::Gg {{ hm: k::map![0 -> _, r @ ..], .. }}], env: {KC}Cell(_)"
                ),
                &format!("{kept}, env: {KC}Cell(r)"),
            ),
        ),
        (
            "map-rest-moved",
            cells(
                "",
                &format!(
                    "{go}, gg: k::fragment![crate::Gg {{ hm: k::map![0 -> _, r @ ..], .. }}], env: {KC}Cell(_)"
                ),
                &format!("{kept}, env: {KC}Cell(r)"),
            ),
        ),
        (
            "top-write",
            readable(
                "go: { k: [Go(), ..], gg: Gg { .. } } => { k: [..], gg: Gg { hm: { 0 -> 1 }, .. } };",
            ),
        ),
        (
            "top-write-twin",
            cells(
                "",
                &format!("{go}, gg: k::fragment![crate::Gg {{ .. }}]"),
                &format!("{kept}, gg: k::fragment![crate::Gg {{ hm: k::map![0 -> 1], .. }}]"),
            ),
        ),
        (
            "top-named",
            readable(
                "go: { k: [Go(), ..], gg: Gg { hm: { 0 -> v, r @ .. }, .. }, env: _ } => { k: [..], env: r };",
            ),
        ),
        (
            "top-named-twin",
            cells(
                "v: Int,\n    ",
                &format!(
                    "{go}, gg: k::fragment![crate::Gg {{ hm: k::map![0 -> v, r @ ..], .. }}], env: {KC}Cell(_)"
                ),
                &format!("{kept}, env: {KC}Cell(r)"),
            ),
        ),
        (
            "top-named-back",
            readable(
                "go: { k: [Go(), ..], gg: Gg { hm: { 0 -> v, r @ .. }, .. } } => { k: [..], gg: Gg { hm: { 0 -> 1, ..r }, ha: v, .. } };",
            ),
        ),
        (
            "top-named-back-twin",
            cells(
                "v: Int,\n    ",
                &format!("{go}, gg: k::fragment![crate::Gg {{ hm: k::map![0 -> v, r @ ..], .. }}]"),
                &format!(
                    "{kept}, gg: k::fragment![crate::Gg {{ hm: k::map![0 -> 1, ..r], ha: v, .. }}]"
                ),
            ),
        ),
        (
            "k-result",
            cells(
                "",
                &format!("{go}, {}", th("tk: [Cmd::Go(), ..]")),
                &format!("{kept}, {}", thr("tk: k::k![Cmd::Hold(), ..]")),
            ),
        ),
        (
            "k-result-brackets",
            cells(
                "",
                &format!("{go}, {}", th("tk: [Cmd::Go(), ..]")),
                &format!("{kept}, {}", thr("tk: [Cmd::Hold(), ..]")),
            ),
        ),
        (
            "k-fragment",
            cells(
                "",
                &format!(
                    "{go}, gg: k::fragment![crate::Gg {{ hk: k::k![Cmd::Go(), ..], .. }}], out: {KC}Cell(_)"
                ),
                &format!("{kept}, out: {KC}Cell([1])"),
            ),
        ),
        (
            "k-fragment-result",
            cells(
                "",
                &format!("{go}, gg: k::fragment![crate::Gg {{ .. }}]"),
                &format!(
                    "{kept}, gg: k::fragment![crate::Gg {{ hk: k::k![Cmd::Hold(), ..], .. }}]"
                ),
            ),
        ),
        (
            "k-fragment-twin",
            cells(
                "",
                &format!("{go}, Gg::hk: {KC}KCell(Cmd::Go(), ..), out: {KC}Cell(_)"),
                &format!("{kept}, out: {KC}Cell([1])"),
            ),
        ),
        (
            "any-computation",
            cells(
                "",
                &format!("{go}, {}", th("tk: [..]")),
                &format!("{kept}, {}", thr("tk: [Cmd::Hold(), ..]")),
            ),
        ),
        (
            "any-computation-twin",
            cells(
                "",
                &format!("{go}, aux: {KC}KCell(..)"),
                &format!("{kept}, aux: {KC}KCell(Cmd::Hold(), ..)"),
            ),
        ),
        (
            "any-list",
            cells(
                "",
                &format!("{go}, {}", th("tl: [..]")),
                &format!("{kept}, {}", thr("tl: [1, ..]")),
            ),
        ),
        (
            "any-list-twin",
            cells(
                "",
                &format!("{go}, ll: {KC}Cell([..])"),
                &format!("{kept}, ll: {KC}Cell([1, ..])"),
            ),
        ),
        (
            "map-pattern",
            readable(
                "go: { k: [Go(), ..], gg: Gg { hm: k::map![0 -> v, ..], .. }, out: _ } => { k: [..], out: [v] };",
            ),
        ),
        (
            "map-pattern-present",
            readable_claim(
                "go: { k: [Go(), ..], og: Some(Og { om: k::map![0 -> v, ..], .. }), out: _ } => { k: [..], out: [v] };",
            ),
        ),
        (
            "map-pattern-instance-group",
            readable(&format!(
                "go: {{ k: [Go(), ..], {}, out: _ }} => {{ k: [..], out: [v] }};",
                rth("tg: Tg { gm: k::map![0 -> v, ..], .. }")
            )),
        ),
        (
            "map-pattern-instance",
            readable(&format!(
                "go: {{ k: [Go(), ..], {}, out: _ }} => {{ k: [..], out: [v] }};",
                rth("tm: k::map![0 -> v, ..]")
            )),
        ),
        (
            "map-pattern-cell",
            readable(
                "go: { k: [Go(), ..], env: map![0 -> v, ..], out: _ } => { k: [..], out: [v] };",
            ),
        ),
        (
            "map-braces",
            readable(
                "go: { k: [Go(), ..], gg: Gg { hm: { 0 -> v, .. }, .. }, out: _ } => { k: [..], out: [v] };",
            ),
        ),
        (
            "named-rest-kept",
            cells(
                "x: Int,\n    r: List,\n    ",
                &format!("{go}, {}", th("tl: [x, r @ ..]")),
                &format!("{kept}, {}", thr("tl: [x, ..]")),
            ),
        ),
    ];
    let table = rows
        .iter()
        .map(|(name, sentences)| {
            let manifest = package_with(temporary.path(), name, &source, sentences);
            format!("{name}: {}", emitted(target.path(), &manifest))
        })
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r"
        remainder-list: error[krs::syntax::invalid-list-notation]: `..rest` in the list cell `ll` writes `rest`, which the subject binds as the rest of a computation (`rest @ ..`), and a list's rest is a list: a remainder is written back only into a cell of its own kind; write the list's elements, or name a list's rest in the subject (`[x, rest @ ..]`, with `rest` declared at the list's sort) and write that
        remainder-list-whole: error[krs::syntax::invalid-list-notation]: the list cell `ll` is written `rest`, which the subject binds as the rest of a computation (`rest @ ..`), and a list cell holds a list: a remainder is written back only into a cell of its own kind; write the list's elements, or name a list's rest in the subject (`[x, rest @ ..]`, with `rest` declared at the list's sort) and write that
        remainder-list-child: error[krs::syntax::invalid-list-notation]: `..rest` in the list child `tl` writes `rest`, which the subject binds as the rest of a computation (`rest @ ..`), and a list's rest is a list: a remainder is written back only into a cell of its own kind; write the list's elements, or name a list's rest in the subject (`[x, rest @ ..]`, with `rest` declared at the list's sort) and write that
        map-rest-list: error[krs::syntax::invalid-list-notation]: `..r` in the list cell `ll` writes `r`, which the subject binds as the rest of a map (`r @ ..`), and a list's rest is a list: a remainder is written back only into a cell of its own kind; write the list's elements, or name a list's rest in the subject (`[x, rest @ ..]`, with `rest` declared at the list's sort) and write that
        map-rest-computation: error[krs::syntax::invalid-list-notation]: `..r` in the computation cell `aux` writes `r`, which the subject binds as the rest of a map (`r @ ..`), and a computation's rest is a computation: a remainder is written back only into a cell of its own kind; write the computation's items, or name a computation's rest in the subject (`KCell(x, rest @ ..)`) and write that
        remainder-map: error[krs::syntax::invalid-list-notation]: `..rest` in the map cell `env` writes `rest`, which the subject binds as the rest of a computation (`rest @ ..`), and a map's rest is a map: a remainder is written back only into a cell of its own kind; write the map's entries, or name a map's rest in the subject (`k::map![k -> v, rest @ ..]`) and write that
        unbound-computation: error[krs::expand::unbound-name]: `zz` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one
        unbound-map: error[krs::expand::unbound-name]: `zz` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one
        unbound-list: error[krs::expand::unbound-name]: `zz` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one
        claim-list-undeclared: error[krs::syntax::unsupported-rule-signature]: the rest `rest` of the list child `tl` is a list, a term of the child's sort, as a list cell's `Cell([x, rest @ ..])` rest is, and a rule's typed parameters declare every term it binds: declare `rest` among them at the child's sort
        list-undeclared: error[krs::syntax::unsupported-rule-signature]: the rest `rest` of the list child `tl` is a list, a term of the child's sort, as a list cell's `Cell([x, rest @ ..])` rest is, and a rule's typed parameters declare every term it binds: declare `rest` among them at the child's sort
        claim-map-rest-moved: claim [go]: <k> go => .K ... </k> <hm> 0 |-> _ R:Map </hm> <env> _ => R:Map </env>
        map-rest-moved: rule [go]: <k> go => .K ... </k> <hm> 0 |-> _ R:Map </hm> <env> _ => R:Map </env>
        top-write: rule [go]: <k> go => .K ... </k> <hm> _ => 0 |-> 1 </hm>
        top-write-twin: rule [go]: <k> go => .K ... </k> <hm> _ => 0 |-> 1 </hm>
        top-named: rule [go]: <k> go => .K ... </k> <gg> <hm> 0 |-> V:KItem R:Map </hm> <ha> _ </ha> <hk> _ </hk> <hl> _ </hl> </gg> <env> _ => R:Map </env>
        top-named-twin: rule [go]: <k> go => .K ... </k> <hm> 0 |-> V:Int R:Map </hm> <env> _ => R:Map </env>
        top-named-back: error[krs::syntax::rust-syntax]: expected one of: identifier, `::`, `<`, `_`, literal, `const`, `ref`, `mut`, `&`, parentheses, square brackets, `..`, `const`
        top-named-back-twin: rule [go]: <k> go => .K ... </k> <hm> 0 |-> V:Int R:Map => 0 |-> 1 R:Map </hm> <ha> _ => V:Int </ha>
        k-result: rule [go]: <k> go => .K ... </k> <th> <tk> go => hold ... </tk> ... </th>
        k-result-brackets: rule [go]: <k> go => .K ... </k> <th> <tk> go => hold ... </tk> ... </th>
        k-fragment: rule [go]: <k> go => .K ... </k> <hk> go ... </hk> <out> _ => ListItem(1) </out>
        k-fragment-result: error[krs::syntax::invalid-list-notation]: an anonymous `..` in a result record's field keeps no rest: a group's record is read as one term of the group, which writes each child's whole content, so its child keeps none yet (a stated limitation), and a constructor's field is a term; in either a list's rest is named instead, `rest @ ..` in the pattern and `..rest` in the result, and a fixed group's computation child keeps its rest written as its own cell (`c: [x, ..]` in a readable record, `G::c: KCell(x, ..)` in `cells!`); a `?` group's computation child (`Some(G { c: [x, ..], .. })`) is not supported yet in a rule, with or without a rest
        k-fragment-twin: rule [go]: <k> go => .K ... </k> <hk> go ... </hk> <out> _ => ListItem(1) </out>
        any-computation: rule [go]: <k> go => .K ... </k> <th> <tk> .K => hold ... </tk> ... </th>
        any-computation-twin: rule [go]: <k> go => .K ... </k> <aux> .K => hold ... </aux>
        any-list: error[krs::syntax::invalid-list-notation]: `[..]` names no element of the list child `tl`, as `Cell([..])` names none at a list cell: it would match any list, so write `_` to match the list whole, or a binder `rest` declared at the list's sort to write it again (`[a, ..rest]`)
        any-list-twin: error[krs::syntax::invalid-list-notation]: `[..]` and `[rest @ ..]` name no element: the first matches any list, so write `_`, or a binder `rest` to write the list again (`[a, ..rest]`), and the second is the binder `rest` itself
        map-pattern: error[krs::syntax::invalid-expression-notation]: the entry of the cell `gg` holds `map![..]` with an anonymous `..`: in a readable record `map![..]` is a literal, a term, whose `..` names no map; a readable record's map read is its braces, `{ k -> v, .. }`, and a result's map is a term, the literal over a map `m` its subject binds (`map![k -> v, ..m]`)
        map-pattern-present: error[krs::syntax::invalid-expression-notation]: the entry of the cell `og` holds `map![..]` with an anonymous `..`: in a readable record `map![..]` is a literal, a term, whose `..` names no map; a readable record's map read is its braces, `{ k -> v, .. }`, and a result's map is a term, the literal over a map `m` its subject binds (`map![k -> v, ..m]`)
        map-pattern-instance-group: error[krs::syntax::invalid-expression-notation]: the entry of the cell `th` holds `map![..]` with an anonymous `..`: in a readable record `map![..]` is a literal, a term, whose `..` names no map; a readable record's map read is its braces, `{ k -> v, .. }`, and a result's map is a term, the literal over a map `m` its subject binds (`map![k -> v, ..m]`)
        map-pattern-instance: error[krs::syntax::invalid-expression-notation]: the entry of the cell `th` holds `map![..]` with an anonymous `..`: in a readable record `map![..]` is a literal, a term, whose `..` names no map; a readable record's map read is its braces, `{ k -> v, .. }`, and a result's map is a term, the literal over a map `m` its subject binds (`map![k -> v, ..m]`)
        map-pattern-cell: error[krs::syntax::invalid-expression-notation]: the entry of the cell `env` holds `map![..]` with an anonymous `..`: in a readable record `map![..]` is a literal, a term, whose `..` names no map; a readable record's map read is its braces, `{ k -> v, .. }`, and a result's map is a term, the literal over a map `m` its subject binds (`map![k -> v, ..m]`)
        map-braces: rule [go]: <k> go => .K ... </k> <hm> 0 |-> V:KItem ... </hm> <out> _ => ListItem(V:KItem) </out>
        named-rest-kept: error[krs::syntax::invalid-list-notation]: the entry of the cell `tl` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; the subject names the rest `r` (`r @ ..`), which leaves the result's `..` nothing to keep: put `r` back to keep it (`[x, ..r]`), or write the list without `..` to drop it, or to move it where `r` is written elsewhere"]].assert_eq(&table);
}

/// CHILDLEFT round 2, each row beside its twin:
/// - a readable top map cell names its rest as its `cells!` twin does: read (`flat-read`), moved into
///   another cell (`flat-moved`), written whole (`flat-whole`), written over (`flat-over`), each beside
///   its twin; braces holding a rest in a result are a map read, with a text that says what writes a
///   map (`flat-braces-result`);
/// - a readable group record child's `[..]` is its whole content (`group-any`), as `KCell(..)` is
///   (`group-any-twin`);
/// - an instance rest bound nowhere is an unbound name (`unbound-instances`);
/// - a map's rest written whole into a list cell is the remainder refusal (`map-rest-whole-list`);
/// - a readable `map![..]` with an anonymous rest is a literal at a group record's child as at its top
///   cell (`group-map-literal`, `cell-map-literal`), and a `cells!` instance child's built
///   `k::map![..]` says what its `..` names (`built-map-literal`);
/// - a remainder written as a list's rest below a content's root or in a condition is the remainder
///   refusal (`remainder-nested-list`, `remainder-condition`);
/// - a constant after `..` is no rest (`constant-rest`), and stands as an item (`constant-item`);
/// - a readable top-level group record written over a subject term macro says so
///   (`term-macro-subject`), and the item-4 pairing keeps a negative literal's spelling
///   (`negative-subject`).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table of the spellings beside their twins, its expectation inline."
)]
fn round_two_spellings_mean_their_twins() {
    let source = named_rest_source();
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let th = |child: &str| {
        format!("Ths::th: {{ me @ k::fragment![crate::Th {{ {child}, .. }}], i @ .. }}")
    };
    let thr =
        |child: &str| format!("Ths::th: {{ k::fragment![crate::Th {{ {child}, ..me }}], ..i }}");
    let go = format!("k: {KC}KCell(Cmd::Go(), ..)");
    let kept = format!("k: {KC}KCell(..)");
    let named = format!("env: {KC}Cell(k::map![0 -> v, r @ ..])");
    let v = "v: Int,\n    ";
    let rows = [
        (
            "flat-read",
            readable(
                "go: { k: [Go(), ..], env: { 0 -> v, r @ .. }, out: _ } => { k: [..], out: [v] };",
            ),
        ),
        (
            "flat-read-twin",
            cells(
                v,
                &format!("{go}, {named}, out: {KC}Cell(_)"),
                &format!("{kept}, out: {KC}Cell([v])"),
            ),
        ),
        (
            "flat-moved",
            readable(
                "go: { k: [Go(), ..], env: { 0 -> v, r @ .. }, hm: _ } => { k: [..], hm: r };",
            ),
        ),
        (
            "flat-moved-twin",
            cells(
                v,
                &format!("{go}, {named}, Gg::hm: {KC}Cell(_)"),
                &format!("{kept}, Gg::hm: {KC}Cell(r)"),
            ),
        ),
        (
            "flat-whole",
            readable("go: { k: [Go(), ..], env: { 0 -> v, r @ .. } } => { k: [..], env: r };"),
        ),
        (
            "flat-whole-twin",
            cells(
                v,
                &format!("{go}, {named}"),
                &format!("{kept}, env: {KC}Cell(r)"),
            ),
        ),
        (
            "flat-over",
            readable(
                "go: { k: [Go(), ..], env: { 0 -> v, r @ .. } } => { k: [..], env: map![0 -> 1, ..r] };",
            ),
        ),
        (
            "flat-over-twin",
            cells(
                v,
                &format!("{go}, {named}"),
                &format!("{kept}, env: {KC}Cell(k::map![0 -> 1, ..r])"),
            ),
        ),
        (
            "flat-braces-result",
            readable(
                "go: { k: [Go(), ..], env: { 0 -> v, r @ .. } } => { k: [..], env: { 0 -> 1, ..r } };",
            ),
        ),
        (
            "group-any",
            readable(
                "go: { k: [Go(), ..], gg: Gg { hk: [..], .. }, out: _ } => { k: [..], out: [1] };",
            ),
        ),
        (
            "group-any-twin",
            cells(
                "",
                &format!("{go}, Gg::hk: {KC}KCell(..), out: {KC}Cell(_)"),
                &format!("{kept}, out: {KC}Cell([1])"),
            ),
        ),
        (
            "unbound-instances",
            cells(
                "",
                &format!("{go}, Ths::th: {{ i @ .. }}"),
                &format!("{kept}, Ths::th: {{ ..zz }}"),
            ),
        ),
        (
            "map-rest-whole-list",
            cells(
                "",
                &format!("{go}, env: {KC}Cell(k::map![0 -> _, r @ ..]), ll: {KC}Cell(_)"),
                &format!("{kept}, env: {KC}Cell(k::map![0 -> 1]), ll: {KC}Cell(r)"),
            ),
        ),
        (
            "group-map-literal",
            readable(
                "go: { k: [Go(), ..], gg: Gg { hm: map![0 -> v, ..], .. }, out: _ } => { k: [..], out: [v] };",
            ),
        ),
        (
            "cell-map-literal",
            readable(
                "go: { k: [Go(), ..], env: map![0 -> v, ..], out: _ } => { k: [..], out: [v] };",
            ),
        ),
        (
            "built-map-literal",
            cells(
                "",
                &format!("{go}, {}", th("tm: _")),
                &format!("{kept}, {}", thr("tm: k::map![0 -> 1, ..]")),
            ),
        ),
        (
            "remainder-nested-list",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), rest @ ..), out: {KC}Cell(_)"),
                &format!("k: {KC}KCell(), out: {KC}Cell([[1, ..rest]])"),
            ),
        ),
        (
            "remainder-condition",
            format!(
                "#[k::rule(label = \"go\")]\n#[k::requires(list::size([1, ..rest]).eq::<Int>(2))]\npub fn go(\n    k::cells! {{ k: {KC}KCell(Cmd::Go(), rest @ ..), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: {KC}KCell(..rest), ..state }}\n}}\n"
            ),
        ),
        (
            "constant-rest",
            cells(
                "",
                &format!("{go}, aux: {KC}KCell()"),
                &format!("{kept}, aux: {KC}KCell(Cmd::Hold(), ..PRELUDE)"),
            ),
        ),
        (
            "constant-item",
            cells(
                "",
                &format!("{go}, aux: {KC}KCell()"),
                &format!("{kept}, aux: {KC}KCell(Cmd::Hold(), PRELUDE)"),
            ),
        ),
        (
            "term-macro-subject",
            readable(
                "go: { k: [Go(), ..], gg: k::term![Gg { .. }] } => { k: [..], gg: Gg { hm: { 0 -> 1 }, .. } };",
            ),
        ),
        (
            "negative-subject",
            readable(
                "go: { k: [Go(), ..], gg: Gg { ha: -1, .. } } => { k: [..], gg: Gg { hm: { 0 -> 1 }, .. } };",
            ),
        ),
    ];
    let table = rows
        .iter()
        .map(|(name, sentences)| {
            let manifest = package_with(temporary.path(), name, &source, sentences);
            format!("{name}: {}", emitted(target.path(), &manifest))
        })
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r"
        flat-read: rule [go]: <k> go => .K ... </k> <env> 0 |-> V:KItem R:Map </env> <out> _ => ListItem(V:KItem) </out>
        flat-read-twin: rule [go]: <k> go => .K ... </k> <env> 0 |-> V:Int R:Map </env> <out> _ => ListItem(V:Int) </out>
        flat-moved: rule [go]: <k> go => .K ... </k> <env> 0 |-> V:KItem R:Map </env> <hm> _ => R:Map </hm>
        flat-moved-twin: rule [go]: <k> go => .K ... </k> <env> 0 |-> V:Int R:Map </env> <hm> _ => R:Map </hm>
        flat-whole: rule [go]: <k> go => .K ... </k> <env> 0 |-> V:KItem R:Map => R:Map </env>
        flat-whole-twin: rule [go]: <k> go => .K ... </k> <env> 0 |-> V:Int R:Map => R:Map </env>
        flat-over: rule [go]: <k> go => .K ... </k> <env> 0 |-> V:KItem R:Map => R:Map [ 0 <- 1 ] </env>
        flat-over-twin: rule [go]: <k> go => .K ... </k> <env> 0 |-> V:Int R:Map => 0 |-> 1 R:Map </env>
        flat-braces-result: error[krs::syntax::rust-syntax]: the entry of the cell `env` writes braces holding a rest in a result (`{ k -> v, .. }`, `{ k -> v, ..m }`): a readable record's braces holding a rest are a map read, a pattern, which writes nothing; a result's map is a term, the literal over a map `m` its subject binds, the map whole or its rest named `m @ ..` (`map![k -> v, ..m]`), or those entries alone (`{ k -> v }`, `map![k -> v]`); keeping the entries a result does not name, with `..`, is a frame write no route lowers yet (a stated limitation)
        group-any: rule [go]: <k> go => .K ... </k> <gg> <hm> _ </hm> <ha> _ </ha> <hk> _ </hk> <hl> _ </hl> </gg> <out> _ => ListItem(1) </out>
        group-any-twin: rule [go]: <k> go => .K ... </k> <hk> .K ... </hk> <out> _ => ListItem(1) </out>
        unbound-instances: error[krs::expand::unbound-name]: `zz` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one
        map-rest-whole-list: error[krs::syntax::invalid-list-notation]: the list cell `ll` is written `r`, which the subject binds as the rest of a map (`r @ ..`), and a list cell holds a list: a remainder is written back only into a cell of its own kind; write the list's elements, or name a list's rest in the subject (`[x, rest @ ..]`, with `rest` declared at the list's sort) and write that
        group-map-literal: error[krs::syntax::invalid-expression-notation]: the entry of the cell `gg` holds `map![..]` with an anonymous `..`: in a readable record `map![..]` is a literal, a term, whose `..` names no map; a readable record's map read is its braces, `{ k -> v, .. }`, and a result's map is a term, the literal over a map `m` its subject binds (`map![k -> v, ..m]`)
        cell-map-literal: error[krs::syntax::invalid-expression-notation]: the entry of the cell `env` holds `map![..]` with an anonymous `..`: in a readable record `map![..]` is a literal, a term, whose `..` names no map; a readable record's map read is its braces, `{ k -> v, .. }`, and a result's map is a term, the literal over a map `m` its subject binds (`map![k -> v, ..m]`)
        built-map-literal: error[krs::syntax::invalid-expression-notation]: the entry of the cell `th` builds `k::map![..]` with an anonymous `..`, which names no map: a built map's rest is the map its entries are written over (`k::map![k -> v, ..m]`), and keeping the entries a subject's `..` matched is a frame write no route lowers yet (a stated limitation), so a rule names that rest in its subject (`k::map![k -> v, rest @ ..]`) and builds the map over it (`k::map![k -> w, ..rest]`)
        remainder-nested-list: error[krs::syntax::invalid-list-notation]: `..rest` in a list inside the cell `out` writes `rest`, which the subject binds as the rest of a computation (`rest @ ..`), and a list's rest is a list: a remainder is written back only into a cell of its own kind; write the list's elements, or name a list's rest in the subject (`[x, rest @ ..]`, with `rest` declared at the list's sort) and write that
        remainder-condition: error[krs::syntax::invalid-list-notation]: `..rest` in a list in the condition writes `rest`, which the subject binds as the rest of a computation (`rest @ ..`), and a list's rest is a list: a remainder is written back only into a cell of its own kind; write the list's elements, or name a list's rest in the subject (`[x, rest @ ..]`, with `rest` declared at the list's sort) and write that
        constant-rest: error[krs::expand::unbound-name]: `PRELUDE` after `..` is no name this sentence binds: a computation's or a map's rest writes back a remainder or a term binder its subject binds, and a constant is neither; a K-sorted constant stands as an item (`KCell(x, PRELUDE)`)
        constant-item: rule [go]: <k> go => .K ... </k> <aux> .K => hold ~> hold </aux>
        term-macro-subject: error[krs::syntax::rust-syntax]: not supported yet: a result group record whose child is a map entry, over a subject written as a term macro (`k::term![..]`); write the subject's group as its record (`g: G { .. }`) or a record of its children
        negative-subject: rule [go]: <k> go => .K ... </k> <ha> -1 </ha> <hm> _ => 0 |-> 1 </hm>"]].assert_eq(&table);
}

/// A wrapper-style configuration with a `Cell<KSequence>` leaf `saved`, and two map leaves.
const WRAPPED: &str = r#"
use k::KResult;
use k::builtin::{KSequence, Map, map};

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("hold")] Hold(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: k::configuration::KCell<KSequence>,
    #[k::cell]
    pub saved: k::configuration::Cell<KSequence>,
    #[k::cell]
    pub env: k::configuration::Cell<Map>,
    #[k::cell]
    pub env2: k::configuration::Cell<Map>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![pgm]),
            saved: k::configuration::Cell::new(k::k![]),
            env: k::configuration::Cell::new(map![]),
            env2: k::configuration::Cell::new(map![]),
        }
    }
}

{SENTENCES}
"#;

/// A remainder is a term of its kind's sort, welcome wherever a term of that sort is: a computation
/// remainder saved whole into a `K`-sorted leaf (`saved`), a map remainder into a `Map` leaf
/// (`map-leaf`).
#[test]
fn a_remainder_is_a_term_of_its_sort_at_a_leaf_of_that_sort() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rows = [
        (
            "saved",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), tail @ ..), saved: {KC}Cell(_)"),
                &format!("k: {KC}KCell(), saved: {KC}Cell(tail)"),
            ),
        ),
        (
            "map-leaf",
            cells(
                "",
                &format!(
                    "k: {KC}KCell(Cmd::Go(), ..), env: {KC}Cell(map![0 -> _, r @ ..]), env2: {KC}Cell(_)"
                ),
                &format!("k: {KC}KCell(..), env: {KC}Cell(map![0 -> 1]), env2: {KC}Cell(r)"),
            ),
        ),
    ];
    let table = rows
        .iter()
        .map(|(name, sentences)| {
            let manifest = package_with(temporary.path(), name, WRAPPED, sentences);
            format!("{name}: {}", emitted(target.path(), &manifest))
        })
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r"
        saved: rule [go]: <k> go ~> Tail:K => .K </k> <saved> _ => Tail:K </saved>
        map-leaf: rule [go]: <k> go => .K ... </k> <env> 0 |-> _ R:Map => 0 |-> 1 </env> <env2> _ => R:Map </env2>"]].assert_eq(&table);
}
