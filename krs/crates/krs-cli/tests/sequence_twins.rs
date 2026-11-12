//! A sequence cell's rests have one verdict at every position that holds them (SEQTWINS): a
//! top sequence leaf (`aux`), the computation cell (`k`), a List leaf (`ll`), an instance's
//! computation child (`tk`, `jk`), and the `cells!` `KCell(..)` twin. Each row is checked
//! through `krs check` and `krs emit-k`, which run the macro and the collector on the same
//! source, and compared with its twin's line or K.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, Set, list, set};
use k::{KItem, KResult};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("put({a}, {b})")] Put { a: Int, b: Int },
}

#[k::cell]
pub struct Th {
    #[k::cell]
    pub tid: Int,
    #[k::cell]
    pub tl: List,
    #[k::cell]
    pub tk: KSequence,
}

#[k::cell]
pub struct Ths {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub th: Th,
}

#[k::cell]
pub struct Job {
    #[k::cell]
    pub jk: KSequence,
}

#[k::cell]
pub struct Jobs {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub job: Job,
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
    pub ss: Set,
    #[k::cell]
    pub out: List,
    #[k::cell(nested)]
    pub ths: Ths,
    #[k::cell(nested)]
    pub jobs: Jobs,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            ll: list::empty(),
            aux: k::k![],
            ss: set::empty(),
            out: list::empty(),
            ths: Ths { th: Th { tid: 0, tl: list::empty(), tk: k::k![] } },
            jobs: Jobs { job: Job { jk: k::k![] } },
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

/// Writes a one-package workspace whose library is the preamble and `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    library_package(root, name, &format!("{PREAMBLE}{source}"))
}

/// Writes a one-package workspace whose library is `library`.
fn library_package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-SEQTWINS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition: whether it succeeded, its stderr,
/// and its stdout.
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
        String::from_utf8(output.stderr).unwrap(),
        String::from_utf8(output.stdout).unwrap(),
    )
}

/// The row's verdict: its first error line, or the emitted sentence `go` (a rule or a claim) on
/// one line.
fn verdict(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, stderr, _) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    if !success {
        return stderr
            .lines()
            .find(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("no error:\n{stderr}"))
            .to_owned();
    }
    let mut k = fs::read_to_string(output.join("definition.k")).unwrap();
    if let Ok(spec) = fs::read_to_string(output.join("spec.k")) {
        k.push_str(&spec);
    }
    let k = krs_test_support::without_source_comments(&k);
    let start = ["rule [go]:", "claim [go]:"]
        .iter()
        .find_map(|head| k.find(head))
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

/// A readable rule, or claim, of the one clause `body`.
fn readable(body: &str, claim: bool) -> String {
    let (block, attribute) = if claim {
        ("claims", "#[k::claim(all_paths)] ")
    } else {
        ("rules", "")
    };
    format!("k::{block}! {{\n    for Machine;\n    use Cmd::*;\n\n    {attribute}{body}\n}}\n")
}

/// A `cells!` rule, or claim, with the term parameters `parameters`.
fn cells(parameters: &str, subject: &str, result: &str, claim: bool) -> String {
    let attribute = if claim {
        "k::claim(all_paths, "
    } else {
        "k::rule("
    };
    format!(
        "#[{attribute}label = \"go\")]\npub fn go(\n    {parameters}k::cells! {{ {subject}, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ {result}, ..state }}\n}}\n"
    )
}

/// The verdict of each row, `name: verdict`, in the rows' order.
fn verdicts(rows: &[(&str, String)]) -> Vec<String> {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    rows.iter()
        .map(|(name, source)| {
            let manifest = package(temporary.path(), &format!("seq-{name}"), source);
            format!("{name}: {}", verdict(target.path(), &manifest))
        })
        .collect()
}

/// The verdict of `name` in `lines`, without its name.
fn of<'a>(lines: &'a [String], name: &str) -> &'a str {
    lines
        .iter()
        .find_map(|line| line.strip_prefix(&format!("{name}: ")))
        .unwrap_or_else(|| panic!("row `{name}`"))
}

/// Item 1: `[..] => [..]` on a sequence leaf keeps whatever the cell holds, so the rule changes
/// no cell, as its `cells!` twin `KCell(..) => KCell(..)` and a List leaf's `[..] => [..]` do,
/// whichever cell the rule names first; the claim states the cell kept, with the twin's K.
#[test]
fn an_item_less_sequence_the_result_keeps_changes_no_cell_as_its_twins() {
    const KC: &str = "k::configuration::";
    let rule = |body: &str| readable(body, false);
    let claim = |body: &str| readable(body, true);
    let lines = verdicts(&[
        ("aux", rule("go: { aux: [..] } => { aux: [..] };")),
        ("k", rule("go: { k: [..] } => { k: [..] };")),
        ("aux-unwritten", rule("go: { aux: [..] } => { };")),
        (
            "aux-then-ll",
            rule("go: { aux: [..], ll: [..] } => { aux: [..], ll: [..] };"),
        ),
        (
            "ll-then-aux",
            rule("go: { ll: [..], aux: [..] } => { ll: [..], aux: [..] };"),
        ),
        (
            "aux-then-k",
            rule("go: { aux: [..], k: [..] } => { aux: [..], k: [..] };"),
        ),
        (
            "cells-aux",
            cells(
                "",
                &format!("aux: {KC}KCell(..)"),
                &format!("aux: {KC}KCell(..)"),
                false,
            ),
        ),
        ("claim-aux", claim("go: { aux: [..] } => { aux: [..] };")),
        ("claim-k", claim("go: { k: [..] } => { k: [..] };")),
        (
            "claim-cells-aux",
            cells(
                "",
                &format!("aux: {KC}KCell(..)"),
                &format!("aux: {KC}KCell(..)"),
                true,
            ),
        ),
        (
            "claim-cells-k",
            cells(
                "",
                &format!("k: {KC}KCell(..)"),
                &format!("k: {KC}KCell(..)"),
                true,
            ),
        ),
    ]);
    expect_test::expect![[r"
        aux: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        k: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        aux-unwritten: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        aux-then-ll: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        ll-then-aux: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        aux-then-k: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        cells-aux: error[krs::analysis::rule-changes-no-cell]: rule `go` changes no cell: every cell it names keeps its content, so if it applies, it applies again to the configuration it leaves, forever, and changes nothing
        claim-aux: claim [go]: <aux> .K ... </aux>
        claim-k: claim [go]: <k> .K ... </k>
        claim-cells-aux: claim [go]: <aux> .K ... </aux>
        claim-cells-k: claim [go]: <k> .K ... </k>"]]
    .assert_eq(&lines.join("\n"));
    for (row, twin) in [
        ("aux", "cells-aux"),
        ("k", "cells-aux"),
        ("aux-unwritten", "cells-aux"),
        ("aux-then-ll", "ll-then-aux"),
        ("aux-then-k", "cells-aux"),
        ("claim-aux", "claim-cells-aux"),
        ("claim-k", "claim-cells-k"),
    ] {
        assert_eq!(of(&lines, row), of(&lines, twin), "{row} vs {twin}");
    }
}

/// Item 2: `_` among an instance's computation child's items is one item, as it is in the
/// computation cell's head, a top sequence leaf's brackets and the `cells!` fragment's child,
/// and as a named item there is: braced and bracketed, rule and claim.
#[test]
fn a_wildcard_item_of_an_instance_computation_child_is_one_item() {
    let row = |child: &str, claim: bool| {
        readable(
            &format!("go: {{ k: [Go(), ..], {child} }} => {{ k: [..] }};"),
            claim,
        )
    };
    let lines = verdicts(&[
        ("tk", row("th: { Th { tk: [_, ..], .. }, .. }", false)),
        ("jk", row("job: [Job { jk: [_, ..], .. }, ..]", false)),
        ("claim-tk", row("th: { Th { tk: [_, ..], .. }, .. }", true)),
        ("tk-named", row("th: { Th { tk: [y, ..], .. }, .. }", false)),
        (
            "aux",
            readable("go: { aux: [_, ..], ll: _ } => { ll: [] };", false),
        ),
    ]);
    expect_test::expect![[r"
        tk: rule [go]: <k> go => .K ... </k> <th> <tk> _:KItem ~> Tail0:K </tk> ... </th>
        jk: rule [go]: <k> go => .K ... </k> <jobs> <job> <jk> _:KItem ~> Tail0:K </jk> ... </job> ... </jobs>
        claim-tk: claim [go]: <k> go => .K ... </k> <th> <tk> _:KItem ~> Tail0:K </tk> ... </th>
        tk-named: rule [go]: <k> go => .K ... </k> <th> <tk> Y:KItem ~> Tail0:K </tk> ... </th>
        aux: rule [go]: <aux> _:KItem ... </aux> <ll> _ => .List </ll>"]]
    .assert_eq(&lines.join("\n"));
    assert_eq!(
        of(&lines, "tk").replace("_:KItem", "Y:KItem"),
        of(&lines, "tk-named")
    );
    assert_eq!(
        of(&lines, "tk").replace("rule", "claim"),
        of(&lines, "claim-tk")
    );
}

/// Item 3: a subject `[..]` matches whatever the cell holds, and a result `[a, ..]` puts `a` in
/// front of it, keeping the rest: at a top sequence leaf, the computation cell and a List leaf,
/// as at an instance's child and through `KCell(..)`.
#[test]
fn an_item_less_subject_whose_result_writes_items_keeps_its_rest() {
    const KC: &str = "k::configuration::";
    let rule = |body: &str| readable(body, false);
    let lines = verdicts(&[
        (
            "aux",
            rule("go: { aux: [..], out: [a, ..] } => { aux: [a, ..], out: [..] };"),
        ),
        (
            "cells-aux",
            cells(
                "a: KItem,\n    rest: List,\n    ",
                &format!("aux: {KC}KCell(..), out: {KC}Cell([a, rest @ ..])"),
                &format!("aux: {KC}KCell(a, ..), out: {KC}Cell(rest)"),
                false,
            ),
        ),
        (
            "k",
            rule("go: { k: [..], out: [a, ..] } => { k: [a, ..], out: [..] };"),
        ),
        (
            "claim-aux",
            readable(
                "go: { aux: [..], out: [a, ..] } => { aux: [a, ..], out: [..] };",
                true,
            ),
        ),
        (
            "ll",
            rule("go: { k: [Put(a, b), ..], ll: [..] } => { k: [..], ll: [a, ..] };"),
        ),
        (
            "ll-named",
            rule("go: { k: [Put(a, b), ..], ll: l } => { k: [..], ll: [a, ..l] };"),
        ),
        (
            "ll-back",
            rule("go: { k: [Put(a, b), ..], ll: [..] } => { k: [..], ll: [.., a] };"),
        ),
        (
            "tk",
            rule(
                "go: { k: [Put(a, b), ..], th: { me @ Th { tk: [..], .. }, .. } } => { k: [..], th: { Th { tk: [a, ..], ..me }, .. } };",
            ),
        ),
    ]);
    expect_test::expect![[r"
        aux: rule [go]: <aux> .K => A:KItem ... </aux> <out> ListItem(A:KItem) Krs_RestOut:List => Krs_RestOut:List </out>
        cells-aux: rule [go]: <aux> .K => A:KItem ... </aux> <out> ListItem(A:KItem) Rest:List => Rest:List </out>
        k: rule [go]: <k> .K => A:KItem ... </k> <out> ListItem(A:KItem) Krs_RestOut:List => Krs_RestOut:List </out>
        claim-aux: claim [go]: <aux> .K => A:KItem ... </aux> <out> ListItem(A:KItem) Krs_RestOut:List => Krs_RestOut:List </out>
        ll: rule [go]: <k> put ( A:Int , B:Int ) => .K ... </k> <ll> Krs_RestLl:List => ListItem(A:Int) Krs_RestLl:List </ll>
        ll-named: rule [go]: <k> put ( A:Int , B:Int ) => .K ... </k> <ll> L:List => ListItem(A:Int) L:List </ll>
        ll-back: rule [go]: <k> put ( A:Int , B:Int ) => .K ... </k> <ll> Krs_RestLl:List => Krs_RestLl:List ListItem(A:Int) </ll>
        tk: rule [go]: <k> put ( A:Int , B:Int ) => .K ... </k> <th> <tk> .K ~> Tail0:K => A:Int ~> Tail0:K </tk> ... </th>"]]
    .assert_eq(&lines.join("\n"));
    let cell = |line: &str, name: &str| {
        let start = line.find(&format!("<{name}>")).unwrap();
        let end = line.find(&format!("</{name}>")).unwrap();
        line[start..end].to_owned()
    };
    assert_eq!(
        cell(of(&lines, "aux"), "aux"),
        cell(of(&lines, "cells-aux"), "aux")
    );
    assert_eq!(
        cell(of(&lines, "ll"), "ll").replace("Krs_RestLl", "L"),
        cell(of(&lines, "ll-named"), "ll")
    );
}

/// Item 4: a second rest is the pattern's own mistake, judged before the names its result
/// reads: a list holds at most one rest whether or not the result reads the element between
/// them, at a List, Set or sequence leaf, a Map or List collection, or a group.
#[test]
fn a_second_rest_is_refused_before_the_names_the_result_reads() {
    let mut rows = Vec::new();
    for cell in ["ll", "ss", "th", "jobs"] {
        rows.push((
            format!("{cell}-unread"),
            readable(
                &format!("go: {{ k: [Go(), ..], {cell}: [.., x, ..] }} => {{ k: [..] }};"),
                false,
            ),
        ));
        rows.push((
            format!("{cell}-read"),
            readable(
                &format!(
                    "go: {{ k: [Go(), ..], {cell}: [.., x, ..], out: _ }} => {{ k: [..], out: [x] }};"
                ),
                false,
            ),
        ));
    }
    rows.push((
        "aux-read".to_owned(),
        readable(
            "go: { aux: [.., x, ..], out: _ } => { aux: [..], out: [x] };",
            false,
        ),
    ));
    rows.push((
        "ll-read-by-k".to_owned(),
        readable(
            "go: { k: [Go(), ..], ll: [.., x, ..] } => { k: [x, ..] };",
            true,
        ),
    ));
    let named = rows
        .iter()
        .map(|(name, source)| (name.as_str(), source.clone()))
        .collect::<Vec<_>>();
    let lines = verdicts(&named);
    let unread = of(&lines, "ll-unread").to_owned();
    expect_test::expect!["error[krs::syntax::invalid-list-notation]: a list holds at most one rest `..`: the elements before it are the list's front and those after it its back, so with a second rest the elements between the two would have no fixed place; join two lists with `list::concat(xs, ys)`"]
    .assert_eq(&unread);
    for line in &lines {
        let (name, verdict) = line.split_once(": ").unwrap();
        assert_eq!(verdict, unread, "{name}");
    }
}

/// Round 2, D1: a computation's `[..]` (`KCell(..)`) matches every computation, as a variable
/// matches every content, so a rule whose every cell pattern is one or the other, with no
/// requires guard, is enabled in every configuration: `always-enabled-rule`, as its List twin.
/// An item that constrains what the rule reads leaves it a step.
#[test]
fn an_item_less_sequence_subject_alone_is_always_enabled() {
    const KC: &str = "k::configuration::";
    let rule = |body: &str| readable(body, false);
    let lines = verdicts(&[
        ("aux", rule("go: { aux: [..] } => { aux: [Go(), ..] };")),
        ("k", rule("go: { k: [..] } => { k: [Go(), ..] };")),
        (
            "k-and-aux",
            rule("go: { k: [..], aux: [..] } => { k: [..], aux: [Go(), ..] };"),
        ),
        (
            "cells-aux",
            cells(
                "",
                &format!("aux: {KC}KCell(..)"),
                &format!("aux: {KC}KCell(Cmd::Go(), ..)"),
                false,
            ),
        ),
        ("ll", rule("go: { ll: [..] } => { ll: [Go(), ..] };")),
        (
            "aux-guarded",
            rule("go: { aux: [..], ll: [x, ..] } => { aux: [x, ..], ll: [..] };"),
        ),
    ]);
    expect_test::expect![[r"
        aux: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, or a computation's `[..]` (`KCell(..)`), which no item constrains, and it has no requires guard
        k: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, or a computation's `[..]` (`KCell(..)`), which no item constrains, and it has no requires guard
        k-and-aux: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, or a computation's `[..]` (`KCell(..)`), which no item constrains, and it has no requires guard
        cells-aux: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, or a computation's `[..]` (`KCell(..)`), which no item constrains, and it has no requires guard
        ll: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, and it has no requires guard
        aux-guarded: rule [go]: <aux> .K => X:KItem ... </aux> <ll> ListItem(X:KItem) Krs_RestLl:List => Krs_RestLl:List </ll>"]].assert_eq(&lines.join("\n"));
    assert_eq!(of(&lines, "aux"), of(&lines, "cells-aux"));
    assert_eq!(of(&lines, "aux"), of(&lines, "k"));
}

/// Round 2, D3: readable `ll: [..] => ll: [a, ..]` matches any list and puts `a` in front of it.
/// `krs expand` prints it in the spelling `cells!` reads, with the rest named (`Cell(rest)`,
/// `Cell([a, ..rest])`), and that print emits the rule's K but for the rest's name, as the
/// hand-written named twin does. `cells!` keeps `Cell([..])` in a subject as a stated limit,
/// whose text names that spelling.
#[test]
fn an_item_less_list_subject_prints_with_its_rest_named() {
    const KC: &str = "k::configuration::";
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable_source = readable(
        "go: { k: [Put(a, b), ..], ll: [..] } => { k: [..], ll: [a, ..] };",
        false,
    );
    let manifest = package(temporary.path(), "seq-print-readable", &readable_source);
    let (success, stderr, print) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let printed = library_package(temporary.path(), "seq-print-printed", &print);
    let lines = [
        ("readable".to_owned(), verdict(target.path(), &manifest)),
        ("printed".to_owned(), verdict(target.path(), &printed)),
    ]
    .into_iter()
    .chain(
        verdicts(&[
            (
                "cells-named",
                cells(
                    "a: Int,\n    b: Int,\n    rest: List,\n    ",
                    &format!("k: {KC}KCell(Cmd::Put {{ a, b }}, ..), ll: {KC}Cell(rest)"),
                    &format!("k: {KC}KCell(..), ll: {KC}Cell([a, ..rest])"),
                    false,
                ),
            ),
            (
                "cells-dots",
                cells(
                    "a: Int,\n    b: Int,\n    ",
                    &format!("k: {KC}KCell(Cmd::Put {{ a, b }}, ..), ll: {KC}Cell([..])"),
                    &format!("k: {KC}KCell(..), ll: {KC}Cell([a, ..])"),
                    false,
                ),
            ),
        ])
        .into_iter()
        .filter_map(|line| {
            line.split_once(": ")
                .map(|(name, verdict)| (name.to_owned(), verdict.to_owned()))
        }),
    )
    .map(|(name, verdict)| format!("{name}: {verdict}"))
    .collect::<Vec<_>>();
    expect_test::expect![[r"
        readable: rule [go]: <k> put ( A:Int , B:Int ) => .K ... </k> <ll> Krs_RestLl:List => ListItem(A:Int) Krs_RestLl:List </ll>
        printed: rule [go]: <k> put ( A:Int , B:Int ) => .K ... </k> <ll> Rest:List => ListItem(A:Int) Rest:List </ll>
        cells-named: rule [go]: <k> put ( A:Int , B:Int ) => .K ... </k> <ll> Rest:List => ListItem(A:Int) Rest:List </ll>
        cells-dots: error[krs::syntax::invalid-list-notation]: `[..]` and `[rest @ ..]` name no element: the first matches any list, so write `_`, or a binder `rest` to write the list again (`[a, ..rest]`), and the second is the binder `rest` itself"]].assert_eq(&lines.join("\n"));
    assert!(
        print.contains("Cell(rest)") && print.contains("Cell([a, ..rest])"),
        "{print}"
    );
    let unnamed = |line: &str| line.replace("Krs_RestLl", "Rest");
    assert_eq!(unnamed(of(&lines, "readable")), of(&lines, "printed"));
    assert_eq!(of(&lines, "printed"), of(&lines, "cells-named"));
}

/// Round 2, Q4: a refused list value's names serve only the reading of the names the clause
/// writes elsewhere, so a map value of the same name is no duplicate binding ahead of the
/// value's own refusal: a list holds at most one rest, in either cell order, as when the names
/// differ.
#[test]
fn a_refused_value_s_names_raise_nothing_ahead_of_its_refusal() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let preamble = PREAMBLE
        .replace("List, Set, list, set}", "List, Map, Set, list, set}")
        .replace(
            "    #[k::cell]\n    pub out: List,\n",
            "    #[k::cell]\n    pub out: List,\n    #[k::cell]\n    pub env: Map,\n",
        )
        .replace(
            "out: list::empty(),",
            "out: list::empty(),\n            env: k::map![],",
        );
    assert!(
        preamble.contains("pub env: Map"),
        "the preamble has a Map cell"
    );
    let lines = [
        (
            "shared",
            "go: { k: [Go(), ..], ll: [.., v, ..], env: { 0 -> v, .. } } => { k: [..] };",
        ),
        (
            "shared-map-first",
            "go: { k: [Go(), ..], env: { 0 -> v, .. }, ll: [.., v, ..] } => { k: [..] };",
        ),
        (
            "apart",
            "go: { k: [Go(), ..], ll: [.., v, ..], env: { 0 -> w, .. } } => { k: [..] };",
        ),
    ]
    .map(|(name, body)| {
        let manifest = library_package(
            temporary.path(),
            &format!("seq-q4-{name}"),
            &format!("{preamble}{}", readable(body, false)),
        );
        format!("{name}: {}", verdict(target.path(), &manifest))
    });
    let apart = of(&lines, "apart").to_owned();
    assert!(apart.contains("a list holds at most one rest"), "{apart}");
    for line in &lines {
        let (name, verdict) = line.split_once(": ").unwrap();
        assert_eq!(verdict, apart, "{name}");
    }
}

/// Rounds 2 to 5: the advice of a rest on one side names a spelling that works for its cell's
/// kind and route. A list matched by `[..]` has no rest to name there (`[rest @ ..]` is refused),
/// so it is matched whole, `_` to drop it or a binder to move it; a record child is paired with
/// its subject twin as the pairing pairs it (`child-ll`, `two-instances`), and a child its
/// subject instance does not name has none (`unmatched-child`). A readable rule keeps a
/// computation's rest, and `cells!` names it to put it back after other items (`cells-k-moved`,
/// accepted), to move it into another computation cell (`cells-k-into-aux`, accepted, FRAMEMOVE)
/// or to drop it where a condition reads it (`cells-k-condition`, accepted). Another list names
/// its rest (`rest @ ..`).
#[test]
fn a_rest_mismatch_advises_a_spelling_its_subject_admits() {
    let rule = |body: &str| readable(body, false);
    let lines = verdicts(&[
        ("ll", rule("go: { ll: [..] } => { ll: [] };")),
        ("ll-dropped", rule("go: { ll: _ } => { ll: [] };")),
        (
            "aux",
            rule("go: { aux: [..], ll: _ } => { aux: [], ll: [] };"),
        ),
        (
            "ll-items",
            rule("go: { ll: [x, ..], out: _ } => { ll: [], out: [x] };"),
        ),
        ("k", rule("go: { k: [Go(), ..] } => { k: [] };")),
        (
            "child-ll",
            rule(
                "go: { k: [Go(), ..], th: { me @ Th { tl: [..], .. }, .. } } => { k: [..], th: { Th { tl: [], ..me }, .. } };",
            ),
        ),
        (
            "cells-k",
            cells(
                "",
                "k: k::configuration::KCell(Cmd::Go(), ..)",
                "k: k::configuration::KCell()",
                false,
            ),
        ),
        (
            "two-instances",
            rule(
                "go: { k: [Go(), ..], th: { a @ Th { tl: [..], .. }, b @ Th { tl: [x, ..], .. }, .. } } => { k: [..], th: { Th { tl: [], ..a }, Th { tl: [..], ..b }, .. } };",
            ),
        ),
        (
            "unmatched-child",
            rule(
                "go: { k: [Go(), ..], th: { a @ Th { tid: 0, .. }, b @ Th { tl: [..], .. }, .. } } => { k: [..], th: { Th { tl: [1, ..], ..a }, Th { tl: [..], ..b }, .. } };",
            ),
        ),
        (
            "cells-k-condition",
            "#[k::rule(label = \"go\")]\n#[k::requires(k::is!(KResult, rest))]\npub fn go(\n    k::cells! { k: k::configuration::KCell(Cmd::Go(), rest @ ..), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(), ..state }\n}\n".to_owned(),
        ),
        (
            "cells-k-moved",
            cells(
                "a: Int,\n    b: Int,\n    ",
                "k: k::configuration::KCell(Cmd::Put { a, b }, rest @ ..)",
                "k: k::configuration::KCell(Cmd::Go(), ..rest)",
                false,
            ),
        ),
        (
            "cells-k-into-aux",
            cells(
                "",
                "k: k::configuration::KCell(Cmd::Go(), rest @ ..), aux: k::configuration::KCell()",
                "k: k::configuration::KCell(), aux: k::configuration::KCell(..rest)",
                false,
            ),
        ),
    ]);
    expect_test::expect![[r"
        ll: error[krs::syntax::invalid-list-notation]: the entry of the cell `ll` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; write `..` on both sides to keep the rest, or match the list whole to drop or move it: `_` drops it, and a binder `rest` moves it (`..rest`)
        ll-dropped: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, and it has no requires guard
        aux: error[krs::syntax::invalid-list-notation]: the entry of the cell `aux` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; write `..` on both sides to keep the rest: a readable rule keeps a computation's rest, and a `cells!` rule whose subject names it (`KCell(x, rest @ ..)`) may put it back after other items (`KCell(y, ..rest)`), move it into another computation cell (`aux: KCell(..rest)`), or drop it where a condition reads it
        ll-items: error[krs::syntax::invalid-list-notation]: the entry of the cell `ll` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; write `..` on both sides to keep the rest, or name it in the subject (`rest @ ..`) to drop or move it
        k: error[krs::syntax::invalid-list-notation]: the entry of the cell `k` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; write `..` on both sides to keep the rest: a readable rule keeps a computation's rest, and a `cells!` rule whose subject names it (`KCell(x, rest @ ..)`) may put it back after other items (`KCell(y, ..rest)`), move it into another computation cell (`aux: KCell(..rest)`), or drop it where a condition reads it
        child-ll: error[krs::syntax::invalid-list-notation]: the entry of the cell `tl` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; write `..` on both sides to keep the rest, or match the list whole to drop or move it: `_` drops it, and a binder `rest` moves it (`..rest`)
        cells-k: error[krs::syntax::invalid-list-notation]: the entry of the cell `k` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; write `..` on both sides to keep the rest, or name it in the subject (`KCell(x, rest @ ..)`) to put it back after other items (`KCell(y, ..rest)`), to move it into another computation cell (`aux: KCell(..rest)`), or to drop it where a condition reads it: a named rest the rule neither puts back nor uses is refused
        two-instances: error[krs::syntax::invalid-list-notation]: the entry of the cell `tl` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; write `..` on both sides to keep the rest, or match the list whole to drop or move it: `_` drops it, and a binder `rest` moves it (`..rest`)
        unmatched-child: error[krs::syntax::invalid-list-notation]: the entry of the cell `tl` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it writes the whole list, which drops a rest the subject leaves unnamed; write `..` on both sides to keep the rest, or name it in the subject (`rest @ ..`) to drop or move it
        cells-k-condition: rule [go]: <k> go ~> Rest:K => .K </k> requires isKResult(Rest:K)
        cells-k-moved: rule [go]: <k> put ( A:Int , B:Int ) ~> Rest:K => go ~> Rest:K </k>
        cells-k-into-aux: rule [go]: <k> go ~> Rest:K => .K </k> <aux> .K => Rest:K </aux>"]].assert_eq(&lines.join("\n"));
}

/// The rows of [`a_map_or_collection_rest_mismatch_advises_a_spelling_that_works`], over the
/// preamble with the Map cells `env` and `env2`.
fn map_and_collection_rows() -> [(&'static str, String); 10] {
    const KC: &str = "k::configuration::";
    let rule = |body: &str| readable(body, false);
    let v = "v: KItem,\n    ";
    [
        (
            "env",
            cells(
                v,
                &format!("env: {KC}Cell(map![0 -> v, ..])"),
                &format!("env: {KC}Cell(map![0 -> 1])"),
                false,
            ),
        ),
        (
            "readable-env",
            rule("go: { k: [Go(), ..], env: { 0 -> v, .. }, env2: e } => { k: [..], env: e };"),
        ),
        (
            "env-back",
            cells(
                v,
                &format!("env: {KC}Cell(map![0 -> v, rest @ ..])"),
                &format!("env: {KC}Cell(map![0 -> 1, ..rest])"),
                false,
            ),
        ),
        (
            "env-moved",
            cells(
                v,
                &format!("env: {KC}Cell(map![0 -> v, rest @ ..]), env2: {KC}Cell(map![])"),
                &format!("env: {KC}Cell(map![0 -> 1]), env2: {KC}Cell(rest)"),
                false,
            ),
        ),
        (
            "env-condition",
            format!(
                "#[k::rule(label = \"go\")]\n#[k::requires(map::size(rest) == 0)]\npub fn go(\n    v: KItem,\n    k::cells! {{ env: {KC}Cell(map![0 -> v, rest @ ..]), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ env: {KC}Cell(map![0 -> 1]), ..state }}\n}}\n"
            ),
        ),
        (
            "readable-env-whole",
            rule("go: { k: [Go(), ..], env: m } => { k: [..], env: map::update(m, 0, 1) };"),
        ),
        (
            "job",
            rule(
                "go: { k: [Go(), ..], job: [Job { jk: [] }, ..] } => { k: [..], job: [Job { jk: [Go()] }] };",
            ),
        ),
        (
            "cells-job",
            cells(
                "",
                &format!(
                    "k: {KC}KCell(Cmd::Go(), ..), Jobs::job: [k::fragment![crate::Job {{ jk: [] }}], ..]"
                ),
                &format!(
                    "k: {KC}KCell(..), Jobs::job: [k::fragment![crate::Job {{ jk: [Cmd::Go()] }}]]"
                ),
                false,
            ),
        ),
        (
            "job-kept",
            rule(
                "go: { k: [Go(), ..], job: [Job { jk: [] }, ..] } => { k: [..], job: [Job { jk: [Go()] }, ..] };",
            ),
        ),
        (
            "job-named",
            rule(
                "go: { k: [Go(), ..], job: [Job { jk: [] }, rest @ ..] } => { k: [..], job: [Job { jk: [Go()] }] };",
            ),
        ),
    ]
}

/// FRAMEMOVE, item 2: a map's and a collection's rest-mismatch advice names only spellings that
/// work there. A map's result has no `..`, so a `cells!` rule names the rest and puts it back
/// under other entries (`env-back`), moves it into another cell (`env-moved`) or drops it where
/// a condition reads it (`env-condition`); a readable record names no map rest a result writes,
/// so it matches the map whole and builds the new map from it (`readable-env-whole`). A
/// collection keeps its other instances with `..` on both sides (`job-kept`): a rule that
/// removes them is not supported yet (`job-named`).
#[test]
fn a_map_or_collection_rest_mismatch_advises_a_spelling_that_works() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let preamble = PREAMBLE
        .replace("List, Set, list, set}", "List, Map, Set, list, map, set}")
        .replace(
            "    #[k::cell]\n    pub out: List,\n",
            "    #[k::cell]\n    pub out: List,\n    #[k::cell]\n    pub env: Map,\n    #[k::cell]\n    pub env2: Map,\n",
        )
        .replace(
            "out: list::empty(),",
            "out: list::empty(),\n            env: k::map![],\n            env2: k::map![],",
        );
    assert!(
        preamble.contains("pub env2: Map") && preamble.contains("env2: k::map![]"),
        "the preamble has two Map cells"
    );
    let lines = map_and_collection_rows().map(|(name, source)| {
        let manifest = library_package(
            temporary.path(),
            &format!("seq-fm-{name}"),
            &format!("{preamble}{source}"),
        );
        format!("{name}: {}", verdict(target.path(), &manifest))
    });
    expect_test::expect![[r"
        env: error[krs::syntax::invalid-list-notation]: the entry of the cell `env` has a rest (`..`) on one side of the rule only: the subject's `..` matches the entries of the map it leaves unnamed, and the result, which writes the whole map and has no `..`, would keep them to K but drop them to a Rust reader; name the rest in the subject (`map![k -> v, rest @ ..]`) to put it back under other entries (`map![k -> w, ..rest]`), to move it into another cell (`Cell(rest)`), or to drop it where a condition reads it: a named rest the rule neither puts back nor uses is refused
        readable-env: error[krs::syntax::invalid-list-notation]: the entry of the cell `env` has a rest (`..`) on one side of the rule only: the subject's `..` matches the entries of the map it leaves unnamed, and the result, which writes the whole map and has no `..`, would keep them to K but drop them to a Rust reader; a readable record names no rest of a map that a result can write, so match the map whole with a binder `m` and build its new map from it (`map::update(m, k, w)`); a `cells!` rule whose subject names the rest (`map![k -> v, rest @ ..]`) may put it back under other entries (`map![k -> w, ..rest]`), move it into another cell (`Cell(rest)`), or drop it where a condition reads it
        env-back: rule [go]: <env> 0 |-> V:KItem Rest:Map => 0 |-> 1 Rest:Map </env>
        env-moved: rule [go]: <env> 0 |-> V:KItem Rest:Map => 0 |-> 1 </env> <env2> .Map => Rest:Map </env2>
        env-condition: rule [go]: <env> 0 |-> V:KItem Rest:Map => 0 |-> 1 </env> requires size(Rest:Map) ==Int 0
        readable-env-whole: rule [go]: <k> go => .K ... </k> <env> M:Map => M:Map [ 0 <- 1 ] </env>
        job: error[krs::syntax::invalid-list-notation]: the entry of the cell `job` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; write `..` on both sides to keep the rest: a rule does not remove a collection's other instances yet
        cells-job: error[krs::syntax::invalid-list-notation]: the entry of the cell `job` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; write `..` on both sides to keep the rest: a rule does not remove a collection's other instances yet
        job-kept: rule [go]: <k> go => .K ... </k> <jobs> <job> <jk> .K => go </jk> </job> ... </jobs>
        job-named: error[krs::analysis::collection-entry]: not supported yet: the pattern binds the other instances of the collection `job` to `rest` (`rest @ ..`), and a result that does not put them back with `..rest` removes them, which a rule does not state yet"]].assert_eq(&lines.join("\n"));
}

/// The rows of [`a_moved_rest_has_one_rule_at_fixed_and_optional_cells`], over the preamble with
/// a `?` computation cell `ok`, a Map cell `env` and a Map child `tm` of `Th`.
fn optional_and_child_rows() -> [(&'static str, String); 10] {
    const KC: &str = "k::configuration::";
    let rule = |body: &str| readable(body, false);
    let th = "th: { me @ Th { tm: { 0 -> v, rest @ .. }, .. }, .. }";
    [
        (
            "ok-out",
            cells(
                "",
                &format!(
                    "k: {KC}KCell(Cmd::Go(), ..), ok: Some({KC}KCell(Cmd::Put {{ a: 1, b: 2 }}, rest @ ..)), aux: {KC}KCell()"
                ),
                &format!("k: {KC}KCell(..), ok: Some({KC}KCell()), aux: {KC}KCell(..rest)"),
                false,
            ),
        ),
        (
            "ok-in",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), rest @ ..), ok: Some({KC}KCell())"),
                &format!("k: {KC}KCell(), ok: Some({KC}KCell(..rest))"),
                false,
            ),
        ),
        (
            "ok-condition",
            format!(
                "#[k::rule(label = \"go\")]\n#[k::requires(k::is!(KResult, rest))]\npub fn go(\n    k::cells! {{ k: {KC}KCell(Cmd::Go(), ..), ok: Some({KC}KCell(Cmd::Go(), rest @ ..)), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: {KC}KCell(..), ok: Some({KC}KCell()), ..state }}\n}}\n"
            ),
        ),
        (
            "ok-swap",
            cells(
                "",
                &format!(
                    "k: {KC}KCell(Cmd::Go(), rest @ ..), ok: Some({KC}KCell(Cmd::Go(), other @ ..))"
                ),
                &format!("k: {KC}KCell(..other), ok: Some({KC}KCell(..rest))"),
                false,
            ),
        ),
        (
            "ok-mismatch",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), ..), ok: Some({KC}KCell(Cmd::Go(), ..))"),
                &format!("k: {KC}KCell(..), ok: Some({KC}KCell())"),
                false,
            ),
        ),
        (
            "readable-ok-mismatch",
            rule("go: { k: [Go(), ..], ok: Some([Go(), ..]) } => { k: [..], ok: Some([]) };"),
        ),
        (
            "readable-tm-whole",
            rule(
                "go: { k: [Go(), ..], th: { me @ Th { tm: m, .. }, .. } } => { k: [..], th: { Th { tm: map::update(m, 0, 1), ..me }, .. } };",
            ),
        ),
        (
            "readable-tm-named",
            rule(&format!(
                "go: {{ k: [Go(), ..], {th} }} => {{ k: [..], th: {{ Th {{ tm: {{ 0 -> 1 }}, ..me }}, .. }} }};"
            )),
        ),
        (
            "readable-env-named",
            rule(
                "go: { k: [Go(), ..], env: { 0 -> v, rest @ .. }, out: _ } => { k: [..], out: [v] };",
            ),
        ),
        (
            "tk-into-aux",
            cells(
                "rest: KSequence,\n    ",
                &format!(
                    "Ths::th: {{ me @ k::fragment![crate::Th {{ tk: [Cmd::Go(), rest @ ..], .. }}], i @ .. }}, aux: {KC}KCell()"
                ),
                &format!(
                    "Ths::th: {{ k::fragment![crate::Th {{ tk: [], ..me }}], ..i }}, aux: {KC}KCell(..rest)"
                ),
                false,
            ),
        ),
    ]
}

/// FRAMEMOVE round 2: a computation's rest moves by one rule at a fixed and a present `?`
/// computation cell (`ok`): out of it (`ok-out`), into it (`ok-in`), dropped where a condition
/// reads it (`ok-condition`) and swapped (`ok-swap`); a `?` computation's rest mismatch advises
/// those spellings, and on the readable route, which reads no `?` computation's items yet, the
/// `cells!` ones. A readable map read names no rest a result writes, at a record child
/// (`readable-tm-named`) and at a top cell (`readable-env-named`) alike, and the whole binder
/// it advises builds the new map at a child (`readable-tm-whole`). An instance child's
/// computation rest moved into another computation cell is a stated limit (`tk-into-aux`).
#[test]
fn a_moved_rest_has_one_rule_at_fixed_and_optional_cells() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let preamble = PREAMBLE
        .replace("List, Set, list, set}", "List, Map, Set, list, map, set}")
        .replace(
            "    #[k::cell]\n    pub tk: KSequence,\n}",
            "    #[k::cell]\n    pub tk: KSequence,\n    #[k::cell]\n    pub tm: Map,\n}",
        )
        .replace("tk: k::k![] } }", "tk: k::k![], tm: k::map![] } }")
        .replace(
            "    #[k::cell]\n    pub out: List,\n",
            "    #[k::cell]\n    pub out: List,\n    #[k::cell]\n    pub env: Map,\n    #[k::cell(multiplicity = \"?\")]\n    pub ok: Option<KSequence>,\n",
        )
        .replace(
            "out: list::empty(),",
            "out: list::empty(),\n            env: k::map![],\n            ok: k::absent!(k::k![]),",
        );
    assert!(
        [
            "pub tm: Map",
            "tm: k::map![]",
            "pub ok: Option<KSequence>",
            "ok: k::absent!"
        ]
        .iter()
        .all(|part| preamble.contains(part)),
        "the preamble has `tm`, `env` and `ok`"
    );
    let lines = optional_and_child_rows().map(|(name, source)| {
        let manifest = library_package(
            temporary.path(),
            &format!("seq-fm2-{name}"),
            &format!("{preamble}{source}"),
        );
        format!("{name}: {}", verdict(target.path(), &manifest))
    });
    expect_test::expect![[r"
        ok-out: rule [go]: <k> go => .K ... </k> <ok> put ( 1 , 2 ) ~> Rest:K => .K </ok> <aux> .K => Rest:K </aux>
        ok-in: rule [go]: <k> go ~> Rest:K => .K </k> <ok> .K => Rest:K </ok>
        ok-condition: rule [go]: <k> go => .K ... </k> <ok> go ~> Rest:K => .K </ok> requires isKResult(Rest:K)
        ok-swap: rule [go]: <k> go ~> Rest:K => Other:K </k> <ok> go ~> Other:K => Rest:K </ok>
        ok-mismatch: error[krs::syntax::invalid-list-notation]: the entry of the cell `ok` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; write `..` on both sides to keep the rest, or name it in the subject (`KCell(x, rest @ ..)`) to put it back after other items (`KCell(y, ..rest)`), to move it into another computation cell (`aux: KCell(..rest)`), or to drop it where a condition reads it: a named rest the rule neither puts back nor uses is refused
        readable-ok-mismatch: error[krs::syntax::invalid-list-notation]: the entry of the cell `ok` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; a readable record does not read the items of a `?` computation cell yet; a `cells!` rule writes them in `Some(KCell(..))`, where `..` on both sides keeps the rest and a subject that names it (`Some(KCell(x, rest @ ..))`) may put it back after other items (`KCell(y, ..rest)`), move it into another computation cell (`aux: KCell(..rest)`), or drop it where a condition reads it
        readable-tm-whole: rule [go]: <k> go => .K ... </k> <th> <tm> M:Map => M:Map [ 0 <- 1 ] </tm> ... </th>
        readable-tm-named: error[krs::syntax::invalid-list-notation]: the subject names the rest of the map `..rest`, and the result neither puts it back with `..rest` nor uses it, so the rule would drop it: a readable record names no rest a result can write or a condition can read, so a rule that changes the map matches it whole with a binder `m` and builds its new map from it (`map::update(m, k, w)`), and a `cells!` rule whose subject names the rest (`map![k -> v, rest @ ..]`) may put it back under other entries (`map![k -> w, ..rest]`), move it into another cell (`Cell(rest)`), or drop it where a condition reads it
        readable-env-named: error[krs::syntax::invalid-list-notation]: the subject names the rest of the map `..rest`, which the rule leaves as it is, as it does the whole cell the result leaves out, so the name binds nothing a readable rule can use: write `..`; a readable record names no rest a result can write or a condition can read, so a rule that changes the map matches it whole with a binder `m` and builds its new map from it (`map::update(m, k, w)`), and a `cells!` rule whose subject names the rest (`map![k -> v, rest @ ..]`) may put it back under other entries (`map![k -> w, ..rest]`), move it into another cell (`Cell(rest)`), or drop it where a condition reads it
        tk-into-aux: error[krs::analysis::invalid-list-notation]: list notation builds a list, but this position has sort `K`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum; brackets are a computation's items only as the entry of a computation cell or child (`KCell(x, ..)`, `cc: [x, ..]`), and a term of sort `K` elsewhere, a constructor's field or a function's argument, is a binder of that sort, such as a computation cell's `rest @ ..`; an instance or group child's brackets with a named rest (`rest @ ..`, `..rest`), and a `?` computation's items in a readable record, are not supported yet"]].assert_eq(&lines.join("\n"));
}

/// The rows of [`a_built_computation_writes_every_rest_it_names`]: the rests a built
/// computation names, then the wrappers the expander passes on and a `?` group's computation.
fn built_computation_rows() -> Vec<(&'static str, String)> {
    let mut rows = built_rest_rows().to_vec();
    rows.extend(passed_on_rows());
    rows
}

/// The rests a built computation names: created, a `K` field, another sort, an instance child's.
fn built_rest_rows() -> [(&'static str, String); 5] {
    const KC: &str = "k::configuration::";
    [
        (
            "created",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), rest @ ..), ok: None"),
                &format!("k: {KC}KCell(), ok: Some({KC}KCell(Cmd::Go(), ..rest))"),
                false,
            ),
        ),
        (
            "created-condition",
            format!(
                "#[k::rule(label = \"go\")]\n#[k::requires(k::is!(KResult, rest))]\npub fn go(\n    k::cells! {{ k: {KC}KCell(Cmd::Go(), rest @ ..), ok: None, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: {KC}KCell(), ok: Some({KC}KCell(Cmd::Go(), ..rest)), ..state }}\n}}\n"
            ),
        ),
        (
            "field",
            cells(
                "t: KSequence,\n    ",
                &format!("k: {KC}KCell(Cmd::Saved {{ body: t }}, ..), aux: {KC}KCell()"),
                &format!("k: {KC}KCell(..), aux: {KC}KCell(..t)"),
                false,
            ),
        ),
        (
            "field-map",
            cells(
                "m: Map,\n    ",
                &format!("k: {KC}KCell(Cmd::Held {{ m }}, ..), aux: {KC}KCell()"),
                &format!("k: {KC}KCell(..), aux: {KC}KCell(..m)"),
                false,
            ),
        ),
        (
            "child-rest",
            cells(
                "rest: KSequence,\n    ",
                &format!(
                    "Ths::th: {{ me @ k::fragment![crate::Th {{ tk: [Cmd::Go(), rest @ ..], .. }}], i @ .. }}, aux: {KC}KCell()"
                ),
                &format!(
                    "Ths::th: {{ k::fragment![crate::Th {{ tk: [], ..me }}], ..i }}, aux: {KC}KCell(..rest)"
                ),
                false,
            ),
        ),
    ]
}

/// The wrappers the expander passes on, and a `?` group's computation child.
fn passed_on_rows() -> [(&'static str, String); 5] {
    const KC: &str = "k::configuration::";
    [
        (
            "olist-kcell",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), ..), olist: Some({KC}KCell(Cmd::Go()))"),
                &format!("k: {KC}KCell(..), olist: Some({KC}KCell())"),
                false,
            ),
        ),
        (
            "omap-kcell",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), ..), omap: Some({KC}KCell(Cmd::Go()))"),
                &format!("k: {KC}KCell(..), omap: Some({KC}KCell())"),
                false,
            ),
        ),
        (
            "aux-some",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), ..), aux: Some({KC}KCell(Cmd::Go()))"),
                &format!("k: {KC}KCell(..), aux: Some({KC}KCell())"),
                false,
            ),
        ),
        (
            "og-in",
            cells(
                "",
                &format!(
                    "k: {KC}KCell(Cmd::Go(), rest @ ..), og: Some(k::fragment![crate::Og {{ oc: [], .. }}])"
                ),
                &format!(
                    "k: {KC}KCell(), og: Some(k::fragment![crate::Og {{ oc: [Cmd::Go(), ..rest], .. }}])"
                ),
                false,
            ),
        ),
        (
            "og-kept",
            cells(
                "",
                &format!(
                    "k: {KC}KCell(Cmd::Go(), ..), og: Some(k::fragment![crate::Og {{ oc: [Cmd::Go(), ..], .. }}])"
                ),
                &format!(
                    "k: {KC}KCell(..), og: Some(k::fragment![crate::Og {{ oc: [Cmd::Put {{ a: 1, b: 2 }}, ..], .. }}])"
                ),
                false,
            ),
        ),
    ]
}

/// The preamble of [`a_built_computation_writes_every_rest_it_names`] and its round-4 sibling:
/// the `K` and `Map` fields `Saved` and `Held`, the `?` cells `ok`, `olist`, `omap` and the `?`
/// group `og` with its computation child `oc`, and the Map cells `env` and `env2`.
fn built_computation_preamble() -> String {
    let preamble = PREAMBLE
        .replace("List, Set, list, set}", "List, Map, Set, list, map, set}")
        .replace(
            "    #[k::syntax(\"put({a}, {b})\")] Put { a: Int, b: Int },\n",
            "    #[k::syntax(\"put({a}, {b})\")] Put { a: Int, b: Int },\n    #[k::syntax(\"saved({body})\")] Saved { body: KSequence },\n    #[k::syntax(\"held({m})\")] Held { m: Map },\n",
        )
        .replace(
            "#[k::configuration]\n",
            "#[k::cell]\npub struct Og {\n    #[k::cell]\n    pub oc: KSequence,\n    #[k::cell]\n    pub on: Int,\n}\n\n#[k::configuration]\n",
        )
        .replace(
            "    #[k::cell]\n    pub out: List,\n",
            "    #[k::cell]\n    pub out: List,\n    #[k::cell]\n    pub env: Map,\n    #[k::cell]\n    pub env2: Map,\n    #[k::cell(multiplicity = \"?\")]\n    pub ok: Option<KSequence>,\n    #[k::cell(multiplicity = \"?\")]\n    pub olist: Option<List>,\n    #[k::cell(multiplicity = \"?\")]\n    pub omap: Option<Map>,\n    #[k::cell(multiplicity = \"?\", nested)]\n    pub og: Option<Og>,\n",
        )
        .replace(
            "out: list::empty(),",
            "out: list::empty(),\n            env: k::map![],\n            env2: k::map![],\n            ok: k::absent!(k::k![]),\n            olist: k::absent!(list::empty()),\n            omap: k::absent!(k::map![]),\n            og: k::absent!(Og { oc: k::k![], on: 0 }),",
        );
    assert!(
        [
            "Saved { body",
            "pub struct Og",
            "pub og: Option<Og>",
            "og: k::absent!"
        ]
        .iter()
        .all(|part| preamble.contains(part)),
        "the preamble has `Saved`, `Held`, `ok`, `olist`, `omap` and `og`"
    );
    preamble
}

/// FRAMEMOVE round 3: a built computation writes every rest it names, or is refused with a true
/// text. A cell created from `None` ends in the rest its `..rest` names (`created`, with a
/// condition too), as an exact one does; `..t` writes any `K` the subject binds, a constructor's
/// `K` field as a rest (`field`), and another sort is refused naming it (`field-map`). An
/// instance child's named computation rest is a stated limit (`child-rest`), as a `?` group's
/// computation child is (`og-in`, `og-kept`). A `KCell(..)` entry on a `?` List or Map
/// (`olist-kcell`, `omap-kcell`) and `Some(..)` on a fixed computation (`aux-some`) are told
/// their cells' own spelling.
#[test]
fn a_built_computation_writes_every_rest_it_names() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let preamble = built_computation_preamble();
    let lines = built_computation_rows()
        .into_iter()
        .map(|(name, source)| {
            let manifest = library_package(
                temporary.path(),
                &format!("seq-fm3-{name}"),
                &format!("{preamble}{source}"),
            );
            format!("{name}: {}", verdict(target.path(), &manifest))
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        created: rule [go]: <k> go ~> Rest:K => .K </k> (.Bag => <ok> go ~> Rest:K </ok>)
        created-condition: rule [go]: <k> go ~> Rest:K => .K </k> (.Bag => <ok> go ~> Rest:K </ok>) requires isKResult(Rest:K)
        field: rule [go]: <k> saved ( T:K ) => .K ... </k> <aux> .K => T:K </aux>
        field-map: error[krs::syntax::invalid-list-notation]: `..m` in a computation writes the computation `m` after the result's items, and `m` is a term of sort `Map`, not a computation (`K`): write it as an item, without `..`
        child-rest: error[krs::analysis::invalid-list-notation]: list notation builds a list, but this position has sort `K`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum; brackets are a computation's items only as the entry of a computation cell or child (`KCell(x, ..)`, `cc: [x, ..]`), and a term of sort `K` elsewhere, a constructor's field or a function's argument, is a binder of that sort, such as a computation cell's `rest @ ..`; an instance or group child's brackets with a named rest (`rest @ ..`, `..rest`), and a `?` computation's items in a readable record, are not supported yet
        olist-kcell: error[krs::analysis::cell-wrapper]: the cell `olist` holds an optional `List` leaf, and the entry's wrapper is not that content's: `KCell(..)` wraps a computation's items and `Cell(..)` a leaf's value, on the cell that holds one; write its entry as `Some(k::configuration::Cell(..))`
        omap-kcell: error[krs::analysis::cell-wrapper]: the cell `omap` holds an optional `Map` leaf, and the entry's wrapper is not that content's: `KCell(..)` wraps a computation's items and `Cell(..)` a leaf's value, on the cell that holds one; write its entry as `Some(k::configuration::Cell(..))`
        aux-some: error[krs::analysis::optional-presence]: the cell `aux` holds a computation and is not optional (it is declared without `multiplicity = "?"`), so it is always there: `Some(..)` and `None` are the presence of an optional cell, which `aux` has none of
        og-in: error[krs::analysis::collection-entry]: not supported yet: the present group `og` is written whole, as one term naming every child, and its record writes the child `oc` as a computation's items, which no term of the group holds yet
        og-kept: error[krs::syntax::invalid-list-notation]: an anonymous `..` keeps the rest only in a list cell's own brackets, where the pattern's `..` matched it; elsewhere a list's rest is named: `rest @ ..` in the pattern and `..rest` in the result; a `?` group's computation child (`Some(G { c: [x, ..], .. })`) is not supported yet in a rule, with or without a rest: the present group is read as one term, which holds no computation's items"#]].assert_eq(&lines.join("\n"));
}

/// A function of a `K` argument, for [`rest_text_rows`].
const SIZE: &str = "#[k::function(total, internal)]\npub fn Size(body: k::Term<KSequence>) -> k::Term<Int>;\nk::equations! {\n    for Size;\n    size_any: b => 0;\n}\n";

/// The rows of [`each_rest_text_is_true_of_its_input`].
fn rest_text_rows() -> [(&'static str, String); 12] {
    const KC: &str = "k::configuration::";
    let rule = |body: &str| readable(body, false);
    let moved = |name: &'static str, binder: &str, held: &str| {
        (
            name,
            cells(
                &format!("t: {binder},\n    "),
                &format!("k: {KC}KCell({held}, ..), aux: {KC}KCell()"),
                &format!("k: {KC}KCell(..), aux: {KC}KCell(..t)"),
                false,
            ),
        )
    };
    [
        (
            "env-written",
            rule(
                "go: { k: [Go(), ..], env: { 0 -> v, rest @ .. }, env2: e } => { k: [..], env: e };",
            ),
        ),
        (
            "env-kept",
            rule("go: { k: [Go(), ..], env: { 0 -> v, rest @ .. } } => { k: [..] };"),
        ),
        (
            "cell-brackets",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), ..), aux: {KC}Cell([Cmd::Go()])"),
                &format!("k: {KC}KCell(..), aux: {KC}Cell([])"),
                false,
            ),
        ),
        (
            "field-brackets",
            cells(
                "",
                &format!("k: {KC}KCell(Cmd::Go(), ..)"),
                &format!("k: {KC}KCell(Cmd::Saved {{ body: [Cmd::Go()] }}, ..)"),
                false,
            ),
        ),
        (
            "argument-brackets",
            format!(
                "{SIZE}{}",
                cells(
                    "",
                    &format!("k: {KC}KCell(Cmd::Go(), ..)"),
                    &format!("k: {KC}KCell(Size([Cmd::Go()]), ..)"),
                    false,
                )
            ),
        ),
        (
            "argument-binder",
            format!(
                "{SIZE}{}",
                cells(
                    "t: KSequence,\n    ",
                    &format!("k: {KC}KCell(Cmd::Saved {{ body: t }}, ..)"),
                    &format!("k: {KC}KCell(Size(t), ..)"),
                    false,
                )
            ),
        ),
        moved("sort-term", "k::Term<KSequence>", "Cmd::Saved { body: t }"),
        moved(
            "sort-path",
            "k::builtin::KSequence",
            "Cmd::Saved { body: t }",
        ),
        (
            "sort-alias",
            format!(
                "pub type Seq = KSequence;\n{}",
                moved("", "Seq", "Cmd::Saved { body: t }").1
            ),
        ),
        moved("sort-map", "k::Term<Map>", "Cmd::Held { m: t }"),
        (
            "og-kept",
            cells(
                "",
                &format!(
                    "k: {KC}KCell(Cmd::Go(), ..), og: Some(k::fragment![crate::Og {{ oc: [Cmd::Go(), ..], .. }}])"
                ),
                &format!(
                    "k: {KC}KCell(..), og: Some(k::fragment![crate::Og {{ oc: [Cmd::Put {{ a: 1, b: 2 }}, ..], .. }}])"
                ),
                false,
            ),
        ),
        (
            "readable-og-kept",
            rule(
                "go: { k: [Go(), ..], og: Some(Og { oc: [Go(), ..], .. }) } => { k: [..], og: Some(Og { oc: [Put(1, 2), ..], .. }) };",
            ),
        ),
    ]
}

/// FRAMEMOVE round 4: each rest text is true of its input. A top readable map read's named rest
/// is a dropped rest where the result writes the cell (`env-written`) and binds nothing where it
/// leaves it out (`env-kept`); brackets at a `K` place that is no computation cell's or child's
/// entry name the binder spelling (`field-brackets`, `argument-brackets`, accepted
/// `argument-binder`), and a `Cell(..)` on a computation is told its wrapper first
/// (`cell-brackets`); a `..t` is a computation by `t`'s resolved sort, however spelled
/// (`sort-term`, `sort-path`, `sort-alias`), and another sort is refused naming it (`sort-map`);
/// a `?` group's computation child is a stated limit, rest or not (`og-kept`, its readable twin).
#[test]
fn each_rest_text_is_true_of_its_input() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let preamble = built_computation_preamble();
    let lines = rest_text_rows().map(|(name, source)| {
        let manifest = library_package(
            temporary.path(),
            &format!("seq-fm4-{name}"),
            &format!("{preamble}{source}"),
        );
        format!("{name}: {}", verdict(target.path(), &manifest))
    });
    expect_test::expect![[r"
        env-written: error[krs::syntax::invalid-list-notation]: the subject names the rest of the map `..rest`, and the result neither puts it back with `..rest` nor uses it, so the rule would drop it: a readable record names no rest a result can write or a condition can read, so a rule that changes the map matches it whole with a binder `m` and builds its new map from it (`map::update(m, k, w)`), and a `cells!` rule whose subject names the rest (`map![k -> v, rest @ ..]`) may put it back under other entries (`map![k -> w, ..rest]`), move it into another cell (`Cell(rest)`), or drop it where a condition reads it
        env-kept: error[krs::syntax::invalid-list-notation]: the subject names the rest of the map `..rest`, which the rule leaves as it is, as it does the whole cell the result leaves out, so the name binds nothing a readable rule can use: write `..`; a readable record names no rest a result can write or a condition can read, so a rule that changes the map matches it whole with a binder `m` and builds its new map from it (`map::update(m, k, w)`), and a `cells!` rule whose subject names the rest (`map![k -> v, rest @ ..]`) may put it back under other entries (`map![k -> w, ..rest]`), move it into another cell (`Cell(rest)`), or drop it where a condition reads it
        cell-brackets: error[krs::analysis::cell-wrapper]: the cell `aux` holds a computation, and the entry's wrapper is not that content's: `KCell(..)` wraps a computation's items and `Cell(..)` a leaf's value, on the cell that holds one; write its entry as `k::configuration::KCell(..)`
        field-brackets: error[krs::analysis::invalid-list-notation]: list notation builds a list, but this position has sort `K`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum; brackets are a computation's items only as the entry of a computation cell or child (`KCell(x, ..)`, `cc: [x, ..]`), and a term of sort `K` elsewhere, a constructor's field or a function's argument, is a binder of that sort, such as a computation cell's `rest @ ..`; an instance or group child's brackets with a named rest (`rest @ ..`, `..rest`), and a `?` computation's items in a readable record, are not supported yet
        argument-brackets: error[krs::analysis::invalid-list-notation]: list notation builds a list, but this position has sort `K`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum; brackets are a computation's items only as the entry of a computation cell or child (`KCell(x, ..)`, `cc: [x, ..]`), and a term of sort `K` elsewhere, a constructor's field or a function's argument, is a binder of that sort, such as a computation cell's `rest @ ..`; an instance or group child's brackets with a named rest (`rest @ ..`, `..rest`), and a `?` computation's items in a readable record, are not supported yet
        argument-binder: rule [go]: <k> saved ( T:K ) => size ( T:K ) ... </k> rule size ( B:K ) => 0 [label(org_krs_seqtwins--size_any)]
        sort-term: rule [go]: <k> saved ( T:K ) => .K ... </k> <aux> .K => T:K </aux>
        sort-path: rule [go]: <k> saved ( T:K ) => .K ... </k> <aux> .K => T:K </aux>
        sort-alias: rule [go]: <k> saved ( T:K ) => .K ... </k> <aux> .K => T:K </aux>
        sort-map: error[krs::syntax::invalid-list-notation]: `..t` in a computation writes the computation `t` after the result's items, and `t` is a term of sort `Map`, not a computation (`K`): write it as an item, without `..`
        og-kept: error[krs::syntax::invalid-list-notation]: an anonymous `..` keeps the rest only in a list cell's own brackets, where the pattern's `..` matched it; elsewhere a list's rest is named: `rest @ ..` in the pattern and `..rest` in the result; a `?` group's computation child (`Some(G { c: [x, ..], .. })`) is not supported yet in a rule, with or without a rest: the present group is read as one term, which holds no computation's items
        readable-og-kept: error[krs::syntax::invalid-list-notation]: an anonymous `..` keeps the rest only in a list cell's own brackets, where the pattern's `..` matched it; elsewhere a list's rest is named: `rest @ ..` in the pattern and `..rest` in the result; a `?` group's computation child (`Some(G { c: [x, ..], .. })`) is not supported yet in a rule, with or without a rest: the present group is read as one term, which holds no computation's items"]].assert_eq(&lines.join("\n"));
}

/// The verdict of the library `library`'s readable rule `go`, its `krs expand` print's `go`
/// function, and that print's verdict.
fn printed_twin(name: &str, library: &str) -> (String, String, String) {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = library_package(temporary.path(), &format!("seq-{name}-readable"), library);
    let (success, stderr, print) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let printed = library_package(temporary.path(), &format!("seq-{name}-printed"), &print);
    let start = print.find("pub fn go(").expect("the print holds `go`");
    let end = print[start..]
        .find("\n}\n")
        .map_or(print.len(), |end| start + end + 2);
    (
        verdict(target.path(), &manifest),
        print[start..end]
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" "),
        verdict(target.path(), &printed),
    )
}

/// Round 3, R2-1: the print names a `[..]` subject's kept rest fresh where it makes it, so an
/// author's name spelled like the print's own placeholder is printed as written: the print is
/// the readable rule, its K the readable K but for the rest's name.
#[test]
fn a_named_rest_never_renames_an_author_s_name() {
    let (readable_k, print, printed_k) = printed_twin(
        "r21",
        &format!(
            "{PREAMBLE}{}",
            readable(
                "go: { k: [Put(list_rest_0, b), ..], ll: [..] } => { k: [..], ll: [list_rest_0, ..] };",
                false,
            )
        ),
    );
    expect_test::expect![[r"
        rule [go]: <k> put ( ListRest0:Int , B:Int ) => .K ... </k> <ll> Krs_RestLl:List => ListItem(ListRest0:Int) Krs_RestLl:List </ll>
        pub fn go( list_rest_0: k::Term<k::builtin::Int>, b: k::Term<k::builtin::Int>, rest: k::Term<k::builtin::List>, k::cells! { k : k::configuration::KCell(crate ::Cmd::Put(list_rest_0, b), ..), ll : k::configuration::Cell(rest), state @ .. }: crate::Machine, ) -> crate::Machine { k::cells! { k : k::configuration::KCell(..), ll : k::configuration::Cell([list_rest_0, ..rest]), ..state } }
        rule [go]: <k> put ( ListRest0:Int , B:Int ) => .K ... </k> <ll> Rest:List => ListItem(ListRest0:Int) Rest:List </ll>"]].assert_eq(&format!("{readable_k}\n{print}\n{printed_k}"));
    assert_eq!(readable_k.replace("Krs_RestLl", "Rest"), printed_k);
}

/// Round 3, R2-2: the printed rest's name is fresh against every name the printed sentence
/// holds, a restated condition's path segments included: beside `crate::rest::Check(a)` it is
/// `rest_2`, and the print emits the readable K but for the rest's name.
#[test]
fn a_named_rest_is_fresh_against_the_restated_condition() {
    const CHECK: &str = r"
pub mod rest {
    use k::Term;
    use k::builtin::{Bool, Int};

    #[k::function(total, internal)]
    pub fn Check(value: Term<Int>) -> Term<Bool>;

    k::equations! {
        for Check;
        check_any: n => true;
    }
}
";
    let (readable_k, print, printed_k) = printed_twin(
        "r22",
        &format!(
            "{PREAMBLE}{CHECK}{}",
            readable(
                "#[k::requires(crate::rest::Check(a))] go: { k: [Put(a, b), ..], ll: [..] } => { k: [..], ll: [a, ..] };",
                false,
            )
        ),
    );
    expect_test::expect![[r"
        rule [go]: <k> put ( A:Int , B:Int ) => .K ... </k> <ll> Krs_RestLl:List => ListItem(A:Int) Krs_RestLl:List </ll> requires check ( A:Int ) rule check ( N:Int ) => true [label(org_krs_seqtwins--rest--check_any)]
        pub fn go( a: k::Term<k::builtin::Int>, b: k::Term<k::builtin::Int>, rest_2: k::Term<k::builtin::List>, k::cells! { k : k::configuration::KCell(crate ::Cmd::Put(a, b), ..), ll : k::configuration::Cell(rest_2), state @ .. }: crate::Machine, ) -> crate::Machine { k::cells! { k : k::configuration::KCell(..), ll : k::configuration::Cell([a, ..rest_2]), ..state } }
        rule [go]: <k> put ( A:Int , B:Int ) => .K ... </k> <ll> Rest2:List => ListItem(A:Int) Rest2:List </ll> requires check ( A:Int ) rule check ( N:Int ) => true [label(org_krs_seqtwins--rest--check_any)]"]].assert_eq(&format!("{readable_k}\n{print}\n{printed_k}"));
    assert!(print.contains("Cell(rest_2)"), "{print}");
    assert_eq!(readable_k.replace("Krs_RestLl", "Rest2"), printed_k);
}

/// Round 3, D1's twin: a collection's instance list that names no instance, its rest kept
/// (`[..]`, `{ .. }`), matches every content of the collection, as `KCell(..)` matches every
/// computation, so beside it a rule whose other patterns constrain nothing is
/// `always-enabled-rule`. A rule about a group held by a collection (`for Th`) applies only
/// where an instance exists, so it is never always enabled, whatever its patterns.
#[test]
fn an_item_less_instance_list_matches_every_collection() {
    let rule = |body: &str| readable(body, false);
    let group = |group: &str, body: &str| {
        format!("k::rules! {{\n    for {group};\n    use Cmd::*;\n\n    {body}\n}}\n")
    };
    let lines = verdicts(&[
        (
            "list-collection",
            rule("go: { aux: [..], job: [..] } => { aux: [Go(), ..], job: [..] };"),
        ),
        (
            "list-leaf",
            rule("go: { ll: [..], job: [..] } => { ll: [Go(), ..], job: [..] };"),
        ),
        (
            "map-collection",
            rule("go: { aux: [..], th: { .. } } => { aux: [Go(), ..], th: { .. } };"),
        ),
        (
            "named-instance",
            rule(
                "go: { aux: [..], th: { Th { tid: 0, .. }, .. } } => { aux: [Go(), ..], th: { Th { tid: 0, .. }, .. } };",
            ),
        ),
        (
            "no-instance",
            rule("go: { aux: [..], job: [] } => { aux: [Go(), ..], job: [] };"),
        ),
        (
            "for-th-variable",
            group("Th", "go: { tl: l } => { tl: [1, ..l] };"),
        ),
        (
            "for-th-computation",
            group("Th", "go: { tk: [..] } => { tk: [Go(), ..] };"),
        ),
    ]);
    expect_test::expect![[r"
        list-collection: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, or a computation's `[..]` (`KCell(..)`), which no item constrains, or a collection's instance list that names no instance (`[..]`, `{ .. }`), which every content of the collection matches, and it has no requires guard
        list-leaf: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, or a collection's instance list that names no instance (`[..]`, `{ .. }`), which every content of the collection matches, and it has no requires guard
        map-collection: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, or a computation's `[..]` (`KCell(..)`), which no item constrains, or a collection's instance list that names no instance (`[..]`, `{ .. }`), which every content of the collection matches, and it has no requires guard
        named-instance: rule [go]: <aux> .K => go ... </aux> <th> <tid> 0 </tid> ... </th>
        no-instance: rule [go]: <aux> .K => go ... </aux> <jobs> .Bag </jobs>
        for-th-variable: rule [go]: <th> <tl> L:List => ListItem(1) L:List </tl> ... </th>
        for-th-computation: rule [go]: <th> <tk> .K => go ... </tk> ... </th>"]].assert_eq(&lines.join("\n"));
}

/// Round 4, the printer: the print names a `[..]` subject's kept rest where it makes it, on a
/// second print once the sentence's names are known, so nothing printed is renamed, not even an
/// item spelled like the first print's reserved placeholder (a constructor `__krs_list_rest_0`,
/// which krs admits).
#[test]
fn a_named_rest_renames_no_item() {
    let preamble = PREAMBLE.replace(
        "#[k::syntax(\"go\")] Go(),",
        "#[k::syntax(\"go\")] Go(),\n    #[k::syntax(\"odd\")] __krs_list_rest_0(),",
    );
    assert!(
        preamble.contains("__krs_list_rest_0()"),
        "the preamble declares the item"
    );
    let (readable_k, print, printed_k) = printed_twin(
        "printer",
        &format!(
            "{preamble}{}",
            readable(
                "go: { k: [__krs_list_rest_0(), ..], ll: [..] } => { k: [..], ll: [Go(), ..] };",
                false,
            )
        ),
    );
    expect_test::expect![[r"
        rule [go]: <k> odd => .K ... </k> <ll> Krs_RestLl:List => ListItem(go) Krs_RestLl:List </ll>
        pub fn go( rest: k::Term<k::builtin::List>, k::cells! { k : k::configuration::KCell(crate ::Cmd::__krs_list_rest_0(), ..), ll : k::configuration::Cell(rest), state @ .. }: crate::Machine, ) -> crate::Machine { k::cells! { k : k::configuration::KCell(..), ll : k::configuration::Cell([crate ::Cmd::Go(), ..rest]), ..state } }
        rule [go]: <k> odd => .K ... </k> <ll> Rest:List => ListItem(go) Rest:List </ll>"]].assert_eq(&format!("{readable_k}\n{print}\n{printed_k}"));
    assert!(print.contains("Cmd::__krs_list_rest_0()"), "{print}");
    assert_eq!(readable_k.replace("Krs_RestLl", "Rest"), printed_k);
}

/// Round 5, the printer: a sorted wildcard (a map read's value `_` narrowed to `Int`, printed as the
/// binder `_int`) is printed by its name where it
/// is printed, so nothing printed is renamed, not even a constructor spelled like the wildcard's
/// reserved id (`__krs_wildcard_0`, which krs admits).
#[test]
fn a_sorted_wildcard_renames_no_item() {
    let preamble = PREAMBLE
        .replace("List, Set, list, set}", "List, Map, Set, list, set}")
        .replace(
            "    #[k::cell]\n    pub out: List,\n",
            "    #[k::cell]\n    pub out: List,\n    #[k::cell]\n    pub env: Map,\n",
        )
        .replace(
            "out: list::empty(),",
            "out: list::empty(),\n            env: k::map![],",
        )
        .replace(
            "#[k::syntax(\"go\")] Go(),",
            "#[k::syntax(\"go\")] Go(),\n    #[k::syntax(\"odd\")] __krs_wildcard_0(),",
        );
    assert!(preamble.contains("pub env: Map") && preamble.contains("__krs_wildcard_0()"));
    let (readable_k, print, printed_k) = printed_twin(
        "wildcard",
        &format!(
            "{preamble}{}",
            readable(
                "go: { k: [__krs_wildcard_0(), ..], env: { 0 -> _, .. } } => { k: [..] } where _: Int;",
                false,
            )
        ),
    );
    expect_test::expect![[r"
        rule [go]: <k> odd => .K ... </k> <env> 0 |-> _:Int ... </env>
        pub fn go( _int: k::Term<k::builtin::Int>, k::cells! { k : k::configuration::KCell(crate ::Cmd::__krs_wildcard_0(), ..), env : k::configuration::Cell(map![0 -> _int, ..]), state @ .. }: crate::Machine, ) -> crate::Machine { k::cells! { k : k::configuration::KCell(..), ..state } }
        rule [go]: <k> odd => .K ... </k> <env> 0 |-> _Int:Int ... </env>"]].assert_eq(&format!("{readable_k}\n{print}\n{printed_k}"));
    assert!(print.contains("Cmd::__krs_wildcard_0()"), "{print}");
    assert!(print.contains("_int: k::Term<k::builtin::Int>"), "{print}");
    // The wildcard's binder reads back as a K variable used once, `_Int`, the readable `_`.
    assert_eq!(readable_k.replace("_:Int", "_Int:Int"), printed_k);
}
