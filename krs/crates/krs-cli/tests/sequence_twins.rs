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

/// Round 2, Q5: the advice of a rest on one side names a spelling that works for its subject. A
/// list matched by `[..]` has no rest to name there (`[rest @ ..]` is refused), so it is matched
/// whole, `_` to drop it or a binder to move it; a readable computation keeps its rest, which
/// `cells!` names; a subject with items names its rest (`rest @ ..`).
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
    ]);
    expect_test::expect![[r"
        ll: error[krs::syntax::invalid-list-notation]: the entry of the cell `ll` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; write `..` on both sides to keep the rest, or match the list whole to drop or move it: `_` drops it, and a binder `rest` moves it (`..rest`)
        ll-dropped: error[krs::analysis::always-enabled-rule]: rule `go` is always enabled, so execution never terminates: every cell pattern it names is a variable or `_` of the cell's sort, and it has no requires guard
        aux: error[krs::syntax::invalid-list-notation]: the entry of the cell `aux` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; write `..` on both sides to keep the rest: a readable rule keeps a computation's rest, and a `cells!` rule's `KCell(.., rest @ ..)` drops or moves it
        ll-items: error[krs::syntax::invalid-list-notation]: the entry of the cell `ll` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader; write `..` on both sides to keep the rest, or name it in the subject (`rest @ ..`) to drop or move it"]].assert_eq(&lines.join("\n"));
}
