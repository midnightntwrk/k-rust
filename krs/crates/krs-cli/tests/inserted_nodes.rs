//! Every node KRS inserts into a definition, which no authored token denotes, carries a typed
//! inserted frame in the emitted source map: a definedness test and the `andThenBool` that
//! joins it, a lookup guard, a name KRS made for no token, a cell frame the language adds, and a
//! local function's scaffolding. A node that renders authored syntax, once or many times (a
//! `k::bits!` long form, a guarded value, a frame the author wrote as `..`), carries none, and a
//! frame from an authored `..` has that token as its authored range. Each entry records its
//! depth in the rendered definition: the rendered ranges nest, a node strictly inside another is
//! deeper, and nodes of one range are told apart by depth.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};
use serde_json::Value;

/// One construct of each inserted family and of each rendering: a division and a map read in
/// conditions, a computed key and a set element KRS looks up, a projection and a refutable `let`
/// in a key, a desugaring's `k::matches!`, which KRS lifts into a local function, a `k::bits!`
/// template, a record update taking a field the subject matches by a pattern, machine-form rules
/// with the computation cell's `[p, ..]`, a map read's `{ k -> v, .. }`, a list cell's `[a, ..]`
/// and a closed `[p]`, a read of the input stream, block-form rules with their implicit tail and
/// `have` remainder, a `#[k::rule] fn` over a term, a `cells!` rule binding `tail @ ..`, an
/// `if`/`else` function and a constant it uses, a configuration with a nested cell, and a context
/// alias.
const PACKAGE: &str = r#"use k::builtin::{Int, KSequence, List, Map, Set};
use k::KResult;
use k::Term;

k::sorts! {
    Stmt;
    Arg;
    Value: KResult;
    impl Value for Int;
    impl Arg for Int;
}

#[k::constructors(sort = Arg, result = KResult)]
pub enum ArgSyntax {
    #[k::syntax("pair {a} {b}")]
    Pair { a: Int, b: Int },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Div, Look, Key, Elem, Pick, Flag, Read, Bits, Pop, Stop, Reset, Skip, Proj, Part, Save, Input))]
pub enum StmtSyntax {
    #[k::syntax("div {a}")]
    Div { a: Int },
    #[k::syntax("look {a}")]
    Look { a: Int },
    #[k::syntax("key {a}")]
    Key { a: Int },
    #[k::syntax("elem {a}")]
    Elem { a: Int },
    #[k::syntax("pick {a}")]
    #[k::desugar]
    Pick { a: Int },
    #[k::syntax("flag {b}")]
    Flag { b: k::builtin::Bool },
    #[k::syntax("read {a}")]
    Read { a: Int },
    #[k::syntax("bits {a}")]
    Bits { a: Int },
    #[k::syntax("pop")]
    Pop(),
    #[k::syntax("stop")]
    Stop(),
    #[k::syntax("reset")]
    Reset(),
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("proj {a}")]
    Proj { a: Arg },
    #[k::syntax("part {a}")]
    Part { a: Arg },
    #[k::syntax("save")]
    Save(),
    #[k::syntax("input")]
    Input(),
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub fuel: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub keys: Map,
    #[k::cell]
    pub items: List,
    #[k::cell]
    pub elems: Set,
    #[k::cell]
    pub acc: Value,
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell(stream = "stdin")]
    pub input: List,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: k::builtin::map![1 -> 5],
            keys: k::builtin::map![1 -> 1],
            items: k::builtin::list::item(7),
            elems: k::builtin::set::item(1),
            acc: 0,
            frame: Frame { pc: 1, fuel: 2 },
            input: k::builtin::list::empty(),
        }
    }
}

#[k::desugar]
fn pick(k::term![StmtSyntax::Pick(a)]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Flag(k::matches!(10 / a, 5))
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    #[k::requires(10 / a > 1)]
    div: { k: [Div(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(m[a] > 0)]
    look: { k: [Look(a), ..], env: m, acc: _ } => { k: [..], acc: 1 };
    key: { k: [Key(a), ..], keys: kk, env: { kk[a] -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    elem: { k: [Elem(a), ..], keys: kk, elems: k::builtin::set::item(kk[a]), acc: _ } => { k: [..], acc: 1 };
    #[k::requires(b)]
    flag: { k: [Flag(b), ..], acc: _ } => { k: [..], acc: 1 };
    pop: { k: [Pop(), ..], items: [_, ..] } => { k: [..], items: [..] };
    stop: { k: [Stop()] } => { k: [] };
    proj: { k: [Proj(a), ..], keys: { k::project!(Int, a) -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    part: { k: [Part(a), ..], keys: { { let ArgSyntax::Pair { a: _, b } = a; b } -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    save: { k: [Save(), ..], frame: f @ Frame { pc: 1, .. } } => { k: [..], frame: Frame { fuel: 0, ..f } };
    input: { k: [Input(), ..], input: k::builtin::list::concat(k::builtin::list::item(i), more), acc: _ } => { k: [..], input: more, acc: i } where i: Int;
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    read: Read(a) => Skip() where have env[a -> let _];
    bits: Bits(k::bits!("0aaa")) => Skip();
}

#[k::rule]
pub fn reset(
    k::cells! { k: k::configuration::KCell(StmtSyntax::Reset(), tail @ ..), acc: k::configuration::Cell(_), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), acc: k::configuration::Cell(2), ..state }
}

#[k::rule]
pub fn drain(x: Term<k::KItem>, k::term![k::builtin::set::item(x)]: Term<k::KItem>) -> Term<k::KItem> {
    StmtSyntax::Skip()
}

#[k::context_alias(name = operand_eval, here = site)]
fn operand_eval(
    k::cells! { k: k::configuration::KCell(site, tail @ ..), state @ .. }: Machine,
) {
}

#[k::constant]
pub const LIMIT: Int = 9;

#[k::function(total, internal)]
pub fn Clamp(value: Term<Int>) -> Term<Int> {
    if value < 0 { 0 } else { value + LIMIT }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-INSERTED\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Emits the package's `main` definition into `output`.
fn emit(target: &Path, manifest: &Path, output: &Path) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let result = process
        .args(["emit-k", "--manifest-path"])
        .arg(manifest)
        .args([
            "--package",
            "inserted-nodes",
            "--definition",
            "main",
            "--output",
        ])
        .arg(output)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

/// One rendered node of `definition.k`.
#[derive(Debug)]
struct Node {
    start: usize,
    end: usize,
    depth: u64,
    kind: String,
    text: String,
    /// The inserted frame's kind, if any, and its anchor's text in `src/lib.rs`.
    inserted: Option<(String, Option<String>)>,
    /// The node's exact authored range's text in `src/lib.rs`.
    authored: Option<String>,
}

/// The text of `range` when it is in the fixture's `src/lib.rs`, else its file and bytes.
fn range_text(library: &str, range: &Value) -> String {
    let start = usize::try_from(range["start_byte"].as_u64().unwrap()).unwrap();
    let end = usize::try_from(range["end_byte"].as_u64().unwrap()).unwrap();
    let file = &range["file"];
    if file["package"]["cargo_name"] == "inserted-nodes"
        && file["package_relative_path"] == "src/lib.rs"
    {
        library[start..end].to_owned()
    } else {
        format!("{file}:{start}-{end}")
    }
}

fn nodes(definition: &str, sources: &Value, library: &str) -> Vec<Node> {
    assert_eq!(sources["schema_version"], 3);
    let mut nodes = Vec::new();
    for entry in sources["entries"].as_array().unwrap() {
        let Some(generated) = entry.get("generated") else {
            continue;
        };
        if generated["artifact"] != "definition.k" {
            continue;
        }
        let frames = entry["origin"].as_array().unwrap();
        let authored = frames
            .iter()
            .filter(|frame| frame["frame_type"] == "ranged" && frame["kind"] == "authored")
            .collect::<Vec<_>>();
        let inserted = frames
            .iter()
            .filter(|frame| frame["frame_type"] == "inserted")
            .collect::<Vec<_>>();
        assert!(inserted.len() <= 1, "one insertion per node: {entry}");
        let start = usize::try_from(generated["start_byte"].as_u64().unwrap()).unwrap();
        let end = usize::try_from(generated["end_byte"].as_u64().unwrap()).unwrap();
        nodes.push(Node {
            start,
            end,
            depth: entry["depth"].as_u64().unwrap(),
            kind: entry["node_kind"].as_str().unwrap().to_owned(),
            text: definition[start..end].to_owned(),
            inserted: inserted.first().map(|frame| {
                (
                    frame["kind"].as_str().unwrap().to_owned(),
                    frame
                        .get("anchor")
                        .map(|anchor| range_text(library, anchor)),
                )
            }),
            authored: match authored.as_slice() {
                [frame] => Some(range_text(library, &frame["range"])),
                _ => None,
            },
        });
    }
    // In text order, outer nodes first.
    nodes.sort_by_key(|node| (node.start, std::cmp::Reverse(node.end), node.depth));
    nodes
}

/// The emitted rule sentence whose text starts with `head`.
fn sentence<'a>(nodes: &'a [Node], head: &str) -> &'a Node {
    let found = nodes
        .iter()
        .filter(|node| node.kind == "rule" && node.text.trim_start().starts_with(head))
        .collect::<Vec<_>>();
    assert_eq!(
        found.len(),
        1,
        "one sentence starts with {head:?}: {found:#?}"
    );
    found[0]
}

/// The nodes inside `sentence` whose text is `text`.
fn within<'a>(nodes: &'a [Node], sentence: &Node, text: &str) -> Vec<&'a Node> {
    let found = nodes
        .iter()
        .filter(|node| {
            sentence.start <= node.start && node.end <= sentence.end && node.text == text
        })
        .collect::<Vec<_>>();
    assert!(!found.is_empty(), "{text:?} in {:?}", sentence.text);
    found
}

/// The nodes within `outer`'s range, `outer` among them.
fn nested<'a>(nodes: &'a [Node], outer: &Node) -> Vec<&'a Node> {
    nodes
        .iter()
        .filter(|node| outer.start <= node.start && node.end <= outer.end)
        .collect()
}

fn inserted(node: &Node) -> Option<&str> {
    node.inserted.as_ref().map(|(kind, _)| kind.as_str())
}

/// Every node of `text` in the sentence starting with `head` is inserted as `kind`
/// (`None`: renders authored syntax).
fn assert_kind(nodes: &[Node], head: &str, text: &str, kind: Option<&str>) {
    let sentence = sentence(nodes, head);
    for node in within(nodes, sentence, text) {
        assert_eq!(
            inserted(node),
            kind,
            "{text:?} in {:?}: {node:#?}",
            sentence.text
        );
    }
}

/// Each cell frame of the sentence starting with `head`, as (text, inserted kind, authored text).
fn frames<'a>(nodes: &'a [Node], head: &str) -> Vec<(&'a str, Option<&'a str>, Option<&'a str>)> {
    let sentence = sentence(nodes, head);
    nodes
        .iter()
        .filter(|node| {
            node.kind == "cell_frame" && sentence.start <= node.start && node.end <= sentence.end
        })
        .map(|node| (node.text.as_str(), inserted(node), node.authored.as_deref()))
        .collect()
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One census of the fixture's families."
)]
fn every_inserted_node_is_marked_and_renderings_are_not() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "inserted-nodes", PACKAGE);
    let output = temporary.path().join("emitted");
    emit(target.path(), &manifest, &output);
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    let sources: Value =
        serde_json::from_str(&fs::read_to_string(output.join("sources.json")).unwrap()).unwrap();
    let nodes = nodes(&definition, &sources, PACKAGE);

    // A definedness test, each of its nodes and the `andThenBool` that joins it are inserted,
    // anchored at the construct they test; the condition the author wrote is not.
    let div = "rule [div]";
    let test = within(&nodes, sentence(&nodes, div), "A:Int =/=Int 0");
    assert_eq!(
        test[0].inserted,
        Some(("definedness_test".to_owned(), Some("/".to_owned())))
    );
    assert_kind(&nodes, div, "0", Some("definedness_test"));
    let joined = within(
        &nodes,
        sentence(&nodes, div),
        "(A:Int =/=Int 0) andThenBool ((10 /Int A:Int) >Int 1)",
    );
    assert!(
        joined
            .iter()
            .any(|node| node.kind == "term" && inserted(node) == Some("definedness_test")),
        "the conjunction that joins the test: {joined:#?}"
    );
    assert!(
        joined
            .iter()
            .any(|node| node.kind == "rule_condition" && inserted(node).is_none()),
        "the condition the author wrote: {joined:#?}"
    );
    assert_kind(&nodes, div, "(10 /Int A:Int) >Int 1", None);
    assert_kind(&nodes, div, "10 /Int A:Int", None);
    assert_kind(
        &nodes,
        "rule [look]",
        "A:Int in_keys(M:Map)",
        Some("definedness_test"),
    );
    assert_kind(
        &nodes,
        "rule [look]",
        "isInt(M:Map [ A:Int ])",
        Some("definedness_test"),
    );

    // A looked-up key or element is a fresh name in the pattern that a guard equates with the
    // construct; the name, the guard and the condition KRS writes for it are inserted, and the
    // guarded construct is the author's.
    for head in ["rule [key]", "rule [elem]"] {
        assert_kind(&nodes, head, "Krs_Instance0:KItem", Some("lookup_guard"));
        assert_kind(
            &nodes,
            head,
            "Krs_Instance0:KItem ==K (Kk:Map [ A:Int ])",
            Some("lookup_guard"),
        );
        assert_kind(&nodes, head, "(Kk:Map [ A:Int ])", None);
    }

    // A `k::bits!` template's hidden binder is a name KRS made; the template's tests and field
    // reads render the template and are authored.
    let bits = "rule [bits]";
    assert_kind(&nodes, bits, "Krs_Bits0:Int", Some("generated_binder"));
    for text in [
        "Krs_Bits0:Int <Int 16",
        "16",
        "(bitRangeInt(Krs_Bits0:Int, 3, 1)) ==Int 0",
        "bitRangeInt(Krs_Bits0:Int, 3, 1)",
        "3",
    ] {
        assert_kind(&nodes, bits, text, None);
    }

    // A desugaring's `k::matches!` is lifted into a local function: its call, its equations'
    // heads, results and conditions, and the `false` equation's negated copy are KRS's; the
    // `true` equation's test is the author's, and its definedness test is a test.
    let pick = sentence(&nodes, "rule pick");
    let calls = nodes
        .iter()
        .filter(|node| {
            pick.start <= node.start && node.end <= pick.end && node.text.starts_with("krsLocal_")
        })
        .collect::<Vec<_>>();
    assert!(!calls.is_empty());
    for call in calls {
        assert_eq!(inserted(call), Some("local_function"), "{call:#?}");
    }
    let equations = nodes
        .iter()
        .filter(|node| node.kind == "rule" && node.text.trim_start().starts_with("rule krsLocal_"))
        .collect::<Vec<_>>();
    assert_eq!(equations.len(), 2, "{equations:#?}");
    for equation in equations {
        let inside = |text: &str| {
            nodes
                .iter()
                .filter(|node| {
                    equation.start <= node.start
                        && node.end <= equation.end
                        && node.text.starts_with(text)
                })
                .collect::<Vec<_>>()
        };
        for head in inside("krsLocal_") {
            assert_eq!(inserted(head), Some("local_function"), "{head:#?}");
        }
        if equation.text.contains("=> false") {
            for node in inside("notBool ( 5 :=K 10 /Int A:Int )") {
                assert_eq!(inserted(node), Some("local_function"), "{node:#?}");
            }
        } else {
            for node in inside("( 5 :=K 10 /Int A:Int )") {
                assert_eq!(inserted(node), None, "{node:#?}");
            }
        }
        // The definedness test KRS states for the division is the same in both equations,
        // although the `false` equation's division is the local function's copy: a copy is
        // the insertion of the pass that makes it.
        let tests = inside("A:Int =/=Int 0");
        assert!(!tests.is_empty(), "{equation:#?}");
        for node in tests {
            assert_eq!(
                node.inserted,
                Some(("definedness_test".to_owned(), Some("/".to_owned()))),
                "{node:#?}"
            );
        }
    }

    // A projection in a key and a refutable `let` in a key are guarded: the guard, each node
    // of it and the condition KRS writes for it are inserted, and the key's value is the
    // author's.
    let proj = sentence(&nodes, "rule [proj]");
    for guard in within(&nodes, proj, "isInt(A:Arg)") {
        for node in nested(&nodes, guard) {
            assert_eq!(inserted(node), Some("lookup_guard"), "{node:#?}");
        }
    }
    let part = sentence(&nodes, "rule [part]");
    for guard in within(&nodes, part, "( pair _ _ :=K A:Arg )") {
        for node in nested(&nodes, guard) {
            assert_eq!(inserted(node), Some("lookup_guard"), "{node:#?}");
        }
    }
    for value in within(&nodes, part, "( #let pair _ B:Int = A:Arg #in B:Int )") {
        for node in nested(&nodes, value) {
            assert_eq!(inserted(node), None, "{node:#?}");
        }
    }

    // A record update takes the fields it does not list from its base under names KRS makes.
    // Where the subject matches such a field by a pattern, KRS adds an alias of that name over
    // the pattern, whose own bytes (the parentheses, `#as` and the name) are all KRS's, while
    // the pattern is the author's.
    let save = "rule [save]";
    assert_kind(
        &nodes,
        save,
        "( 1 #as Krs_UpdateFPc:Int )",
        Some("generated_binder"),
    );
    assert_kind(&nodes, save, "Krs_UpdateFPc:Int", Some("generated_binder"));
    assert_kind(&nodes, save, "1", None);

    // An `else`'s negation of the earlier condition and a constant at its use render authored
    // syntax.
    let clamp = "rule clamp ( Value:Int ) => Value";
    assert_kind(&nodes, clamp, "notBool (Value:Int <Int 0)", None);
    assert_kind(&nodes, clamp, "Value:Int <Int 0", None);
    assert_kind(&nodes, clamp, "9", None);

    // A frame the author wrote as `..` is authored at that token, in the machine form's
    // computation cell, map read and list cell, and in `cells!`; the block form's computation
    // tail and `have` remainder are the language's.
    for head in ["rule [div]", "rule [look]", "rule [flag]"] {
        assert_eq!(frames(&nodes, head), [(" ...", None, Some(".."))], "{head}");
    }
    assert_eq!(
        frames(&nodes, "rule [key]"),
        [(" ...", None, Some("..")), (" ...", None, Some(".."))]
    );
    assert!(frames(&nodes, "rule [stop]").is_empty());
    assert_eq!(
        frames(&nodes, "rule [reset]"),
        [(" ~> Tail:K", None, Some("tail @ .."))]
    );
    assert_eq!(
        frames(&nodes, "rule [read]"),
        [
            (" ...", Some("cell_frame"), Some("Read(a)")),
            (" ...", Some("cell_frame"), Some("env"))
        ]
    );
    assert_eq!(
        frames(&nodes, "rule [bits]"),
        [(" ...", Some("cell_frame"), Some("Bits(k::bits!(\"0aaa\"))"))]
    );
    assert_eq!(
        frames(&nodes, "rule [input]"),
        [
            (" ...", None, Some("..")),
            (" ...", Some("cell_frame"), Some("input"))
        ],
        "the input stream's rest"
    );
    assert_eq!(
        frames(&nodes, "rule [drain]"),
        [(
            " ...",
            Some("cell_frame"),
            Some("k::term![k::builtin::set::item(x)]")
        )],
        "a `#[k::rule] fn` over a term"
    );
    for node in within(&nodes, sentence(&nodes, "rule [pop]"), "Krs_RestItems:List") {
        assert_eq!(inserted(node), None);
        assert_eq!(node.authored.as_deref(), Some(".."));
    }

    // A cell's declaration and its initializer cell span the same text, the declaration
    // shallower, and a nested cell's children are below both.
    let depth = |kind: &str, head: &str| {
        let found = nodes
            .iter()
            .filter(|node| node.kind == kind && node.text.trim_start().starts_with(head))
            .collect::<Vec<_>>();
        assert_eq!(found.len(), 1, "{kind} {head}: {found:#?}");
        found[0].depth
    };
    assert!(depth("cell", "<frame>") < depth("initializer_cell", "<frame>"));
    assert!(depth("initializer_cell", "<frame>") < depth("cell", "<pc>"));
    assert!(depth("cell", "<pc>") < depth("initializer_cell", "<pc>"));
    // A configuration variable and a context alias's `HERE` are rendered at a term's occurrence,
    // below it.
    for (kind, text) in [
        ("configuration_variable", "$PGM:Stmt"),
        ("context_alias", "HERE"),
    ] {
        let deepest_term = nodes
            .iter()
            .filter(|node| node.kind == "term" && node.text == text)
            .map(|node| node.depth)
            .max()
            .unwrap();
        assert!(deepest_term < depth(kind, text), "{kind} {text}");
    }

    // The rendered ranges nest: no two cross, a node strictly inside another is deeper, and two
    // nodes of one range are at different depths. This holds in the configuration too, whose
    // cell declarations and initializer cells are two trees of the Definition IR rendered as one
    // text, the nested `frame` holding its children, and whose variables are rendered where the
    // initializer uses them, and in the context alias.
    for (index, a) in nodes.iter().enumerate() {
        for b in &nodes[index + 1..] {
            let crossing = (a.start < b.start && b.start < a.end && a.end < b.end)
                || (b.start < a.start && a.start < b.end && b.end < a.end);
            assert!(!crossing, "{a:#?} crosses {b:#?}");
            if (a.start, a.end) == (b.start, b.end) {
                assert_ne!(a.depth, b.depth, "{a:#?} ties {b:#?}");
                continue;
            }
            let (outer, inner) = if a.start <= b.start && b.end <= a.end {
                (a, b)
            } else if b.start <= a.start && a.end <= b.end {
                (b, a)
            } else {
                continue;
            };
            if inner.start < inner.end {
                assert!(outer.depth < inner.depth, "{outer:#?} holds {inner:#?}");
            }
        }
    }
}
