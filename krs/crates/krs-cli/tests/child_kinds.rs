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
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        SOURCE.replace("{SENTENCES}", sentences),
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
    let manifest = package(root, name, sentences);
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        &manifest,
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
    let k = krs_test_support::without_source_comments(
        &fs::read_to_string(output.join("definition.k")).unwrap(),
    );
    let start = k
        .find("rule [go]:")
        .unwrap_or_else(|| panic!("`go` is emitted:\n{k}"));
    let end = ["rule [", "endmodule"]
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

/// A map read or a map's entries in a group record's child, inside a `?` group's `Some(..)` or an
/// instance record, is the map its `cells!` twin's `k::map![..]` writes, read (`read-og`,
/// `read-inst`), kept by the record's `..` (`kept-og`, `kept-inst`) and written (`write-og`,
/// `write-inst`), each beside its twin. A map read in a result names no map, as at a record's top
/// level (`read-in-result`), and a named rest binds a map no readable rule can use (`named`).
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
        read-in-result: error[krs::syntax::rust-syntax]: the entry of the cell `gm` reads a map (`{ k -> v, .. }`) in a result: a map read is a pattern, and a readable record's result has no map write yet (a stated limitation; a `cells!` result has `Cell(k::map![k -> v, ..])`)
        named: error[krs::syntax::invalid-list-notation]: the subject names the rest of the map `..r` in a group record's child, which a readable rule can never use: no readable result writes a map over it and no readable condition reads it, so write `..`, or match the child whole with a binder `m` and build its new map from it (`map::update(m, k, w)`); a `cells!` rule whose subject names the rest (`k::map![k -> v, rest @ ..]`) may put it back under other entries (`k::map![k -> w, ..rest]`)"]].assert_eq(&table(&rows));
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
