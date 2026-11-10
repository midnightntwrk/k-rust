//! The emitted K names its Rust sources without a sidecar: `definition.k` and `spec.k` open
//! with a header, and each rule-like sentence, the configuration and each production the author
//! wrote have a `// KRS <package>/<file>: <item>` line above them, naming the Rust item an agent
//! greps for; a literal that is the whole value of a constant written at its place names the
//! constant after it, `65295 /* IF */`.
//!
//! A function-shorthand equation names its function and branch, an equation of a function
//! lifted out of an item names that item, and an equation of a function only claims apply says
//! so. A constructor's production lists its named fields. The lines hold no line or column, so
//! an edit that only moves Rust lines leaves the emitted K byte-identical, `raw_k!`'s comment
//! included. The comments are K layout: removing them leaves the K a source without constants
//! emits.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{
    fixture_build_env, krs_command, shared_fixture_target, temp_dir, without_constant_names,
};

const NAMESPACE: &str = "ORG-KRS-SOURCES";

const PREAMBLE: &str = r#"use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({value})")] Go { value: Int },
    #[k::syntax("halt")] Halt(),
    #[k::syntax("halted")] Halted(),
}

/// Applied only by the initializer, which every run starts from.
#[k::function(total, internal)]
pub fn Seed(value: Term<Int>) -> Term<Int> {
    int::add(value, 2)
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm, ExpSyntax::Go { value: Seed(0) }],
        }
    }
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    halt: Halt() => Halted();
}
"#;

/// Every form of sentence a `// KRS` line names.
const SENTENCES: &str = r#"
#[k::function(total, sort = Int, syntax = "h({value})")]
pub struct H {
    pub value: Term<Int>,
}

/// A function whose one equation the shorthand writes.
#[k::function(total, internal)]
pub fn Double(value: Term<Int>) -> Term<Int> {
    int::add(value, value)
}

/// A branching body: `pick_1`, `pick_2_1`, `pick_2_2`, `pick_3`, and the labelled `other`.
#[k::function(total, internal)]
pub fn Pick(left: Term<Int>, right: Term<Int>) -> Term<Int> {
    match left {
        0 => 0,
        1 => match right {
            0 => 1,
            _ => 2,
        },
        2 => Double(right),
        #[k::label(other)]
        _ => 4,
    }
}

#[k::function(total, internal)]
pub fn Small(value: Term<Int>) -> Term<Int>;

k::equations! {
    for Small;
    small_zero: 0 => 1;
    #[k::equation(owise)]
    small_other: _ => 0;
}

/// A function only the claim applies.
#[k::function(total, internal)]
pub fn Helper(value: Term<Int>) -> Term<Int> {
    int::add(Inner(value), 1)
}

/// Applied only by `Helper`'s equation, so only through the claim.
#[k::function(total, internal)]
pub fn Inner(value: Term<Int>) -> Term<Int> {
    int::add(value, 3)
}

/// Program syntax: a program may write it, though only the claim applies it.
#[k::function(total, sort = Int, syntax = "visible({value})")]
pub struct Visible {
    pub value: Term<Int>,
}

#[k::equation]
fn visible_any(k::term![Visible(x)]: Term<Int>) -> Term<Int> {
    x
}

#[k::rule]
fn go(k::term![ExpSyntax::Go { value }]: Term<Exp>) -> Term<Exp> {
    H(Pick(value, Small(value)))
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum MarkSyntax {
    #[k::syntax("mark({n}, {s})")] Mark { n: Int, s: k::builtin::Set },
}

/// The `let` block in the element the pattern computes is lifted out of the rule into a
/// function the rule applies.
#[k::rule]
fn mark(
    k::term![MarkSyntax::Mark { n, s: k::builtin::set::item({ let m = n; m + 1 }) }]: Term<Exp>,
) -> Term<Exp> {
    ExpSyntax::Halt()
}

/// Its sentence has a capability line, below the `// KRS` line.
#[k::rule(anywhere)]
fn halt_anywhere(k::term![ExpSyntax::Halt()]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Halted()
}

#[k::context(hole = h)]
fn go_value(k::term![ExpSyntax::Go { value: h }]: Term<Exp>) {}

#[k::simplification]
fn double_twice(k::term![Double(Double(x))]: Term<Int>) -> Term<Int> {
    int::add(Double(x), Double(x))
}

pub mod helpers {
    use super::H;
    use k::Term;
    use k::builtin::Int;

    #[k::equation]
    fn h_any(k::term![H(x)]: Term<Int>) -> Term<Int> {
        x
    }
}

k::claims! {
    for Machine;
    use ExpSyntax::*;

    #[k::claim(all_paths)]
    halts: {
        k: [Halt(), Go { value: n }],
    } => {
        k: [Halted(), Go { value: Visible({ let a = Helper(n); a }) }],
    };
}
"#;

/// A `raw_k!` sentence, whose opaque text may apply any function.
const RAW: &str = r##"
#[k::function(total, internal)]
pub fn Helper(value: Term<Int>) -> Term<Int> {
    int::add(value, 1)
}

k::raw_k!(r#"rule <k> halted => .K ... </k> [label(raw-halted)]"#);

k::claims! {
    for Machine;
    use ExpSyntax::*;

    #[k::claim(all_paths)]
    halts: {
        k: [Go { value: n }],
    } => {
        k: [Go { value: Helper(n) }],
    };
}
"##;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `sources` whose library is the preamble and `source`.
fn package(root: &Path, source: &str, raw: bool) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    let allow_raw = if raw { "allow-raw-k = true\n" } else { "" };
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"sources\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{NAMESPACE}\"\n{allow_raw}\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// `krs emit-k` of the package's `main` definition into `directory`: `definition.k` and
/// `spec.k`; every sentence's generated range in `sources.json` starts at its keyword (a
/// production's at its documentation comment, if it has one) and holds no `// KRS` line, which
/// stays outside every range.
fn emit_k(target: &Path, manifest: &Path, directory: &str) -> (String, String) {
    let output = manifest.with_file_name(directory);
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let result = process
        .args(["emit-k", "--manifest-path"])
        .arg(manifest)
        .args(["--package", "sources", "--definition", "main", "--output"])
        .arg(&output)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    let spec = fs::read_to_string(output.join("spec.k")).unwrap_or_default();
    let sources: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(output.join("sources.json")).unwrap()).unwrap();
    let mut sentences = 0;
    for entry in sources["entries"].as_array().unwrap() {
        let kind = entry["node_kind"].as_str().unwrap();
        let generated = &entry["generated"];
        if !matches!(kind, "rule" | "configuration" | "production") || generated.is_null() {
            continue;
        }
        let text = match generated["artifact"].as_str().unwrap() {
            "definition.k" => &definition,
            _ => &spec,
        };
        let range = &text[usize::try_from(generated["start_byte"].as_u64().unwrap()).unwrap()
            ..usize::try_from(generated["end_byte"].as_u64().unwrap()).unwrap()];
        assert!(
            [
                "  rule ",
                "  claim ",
                "  context",
                "  configuration",
                "  syntax ",
                "  // "
            ]
            .iter()
            .any(|keyword| range.starts_with(keyword))
                && !range.contains("// KRS"),
            "{kind} range {range:?}"
        );
        sentences += 1;
    }
    assert!(sentences > 0);
    (definition, spec)
}

/// The header of an artifact written from `packages`: `definition.k`'s when `definition`.
fn header(packages: &str, definition: bool) -> String {
    let mutations = if definition {
        "// Mutations of this K are patches in the corpus's mutations/<topic>.toml (kink/ beside Cargo.toml by default), each edit anchored by `rule = <label>`;\n\
         // `krs kink check` resolves them and shows each edit's Rust line. Why K patches, not Rust edits: https://github.com/midnightntwrk/k-rust/blob/main/kink/decisions.md#m-mutation-input\n"
    } else {
        ""
    };
    format!(
        "// Generated by `krs emit-k` from {packages}. Do not edit; edit the Rust sources and emit again.\n\
         // The `// KRS <package>/<file>: <item>` line above a sentence names the Rust item it comes from.\n\
         // A default label spells that item's path: `<namespace>--<module>--…--<item>`.\n\
         {mutations}\n"
    )
}

/// The line directly above the first line of `text` that starts with `sentence` (after its
/// indentation).
fn line_above<'a>(text: &'a str, sentence: &str) -> &'a str {
    let lines = text.lines().collect::<Vec<_>>();
    let index = lines
        .iter()
        .position(|line| line.trim_start().starts_with(sentence))
        .unwrap_or_else(|| panic!("{sentence:?} is not in\n{text}"));
    lines[index - 1]
}

/// The line above the first line of `text` that starts with `sentence`, past the sentence's own
/// documentation comment lines: its `// KRS` line, when it has one.
fn marker_above<'a>(text: &'a str, sentence: &str) -> &'a str {
    let lines = text.lines().collect::<Vec<_>>();
    let mut index = lines
        .iter()
        .position(|line| line.trim_start().starts_with(sentence))
        .unwrap_or_else(|| panic!("{sentence:?} is not in\n{text}"));
    loop {
        index -= 1;
        let line = lines[index].trim_start();
        if !line.starts_with("// ") || line.starts_with("// KRS ") {
            return lines[index];
        }
    }
}

/// The `// KRS` line above the rule labelled `label`.
fn above_label<'a>(text: &'a str, label: &str) -> &'a str {
    let needle = format!("label({label})]");
    let lines = text.lines().collect::<Vec<_>>();
    let end = lines
        .iter()
        .position(|line| line.contains(&needle))
        .unwrap_or_else(|| panic!("{needle} is not in\n{text}"));
    let start = (0..=end)
        .rev()
        .find(|index| lines[*index].starts_with("  rule "))
        .unwrap();
    lines[start - 1]
}

/// Each sentence from a KRS item has the `// KRS` line naming it, sorts and subsorts none, and
/// both artifacts open with the header, which names every package a module or sentence of the
/// artifact is written from: in `definition.k` the framework module's `krs` and the definition's
/// own, in `spec.k`, which holds only the claims, the definition's.
#[test]
fn each_sentence_names_its_rust_item_and_both_artifacts_open_with_the_header() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), SENTENCES, false);
    let (definition, spec) = emit_k(target.path(), &manifest, "emitted");
    assert!(
        definition.starts_with(&format!("{}module ", header("krs, sources", true))),
        "{definition}"
    );
    assert!(
        spec.starts_with(&format!("{}requires ", header("sources", false))),
        "{spec}"
    );
    let ns = "org_krs_sources";
    let file = "  // KRS sources/src/lib.rs";
    for (label, expected) in [
        (format!("{ns}--go"), format!("{file}: go")),
        (format!("{ns}--helpers--h_any"), format!("{file}: h_any")),
        (format!("{ns}--double"), format!("{file}: Double")),
        (format!("{ns}--pick_1"), format!("{file}: Pick, branch 1")),
        (
            format!("{ns}--pick_2_1"),
            format!("{file}: Pick, branch 2.1"),
        ),
        (
            format!("{ns}--pick_2_2"),
            format!("{file}: Pick, branch 2.2"),
        ),
        (format!("{ns}--pick_3"), format!("{file}: Pick, branch 3")),
        (
            format!("{ns}--other"),
            format!("{file}: Pick, branch other"),
        ),
        (format!("{ns}--small_zero"), format!("{file}: small_zero")),
        (
            format!("{ns}--helper"),
            format!("{file}: Helper (claim helper: only claims apply it)"),
        ),
        (
            format!("{ns}--inner"),
            format!("{file}: Inner (claim helper: only claims apply it)"),
        ),
        (format!("{ns}--visible_any"), format!("{file}: visible_any")),
        (format!("{ns}--seed"), format!("{file}: Seed")),
        (
            format!("{ns}--double_twice"),
            format!("{file}: double_twice"),
        ),
    ] {
        assert_eq!(above_label(&definition, &label), expected, "{label}");
    }
    assert_eq!(
        line_above(&definition, "rule [halt]:"),
        format!("{file}: halt")
    );
    assert_eq!(
        line_above(&definition, "configuration"),
        format!("{file}: Machine")
    );
    assert_eq!(
        line_above(&definition, "context "),
        format!("{file}: go_value")
    );
    // The `// KRS` line comes first, then the capability line, directly above its rule.
    assert_eq!(
        line_above(&definition, "// krs-capability: AnywhereRule"),
        format!("{file}: halt_anywhere")
    );
    assert_eq!(
        above_label(&definition, &format!("{ns}--halt_anywhere")),
        format!("  // krs-capability: AnywhereRule {ns}--halt_anywhere")
    );
    assert_eq!(
        line_above(&spec, "claim [halts]:"),
        format!("{file}: halts")
    );
    // The `let` blocks lifted out of the rule, which a run applies, and out of the claim, an
    // equation of a function only the claim applies.
    let mut local = definition
        .lines()
        .filter(|line| line.contains(", local function"))
        .collect::<Vec<_>>();
    local.sort_unstable();
    assert_eq!(
        local,
        [
            format!("{file}: halts, local function (claim helper: only claims apply it)"),
            format!("{file}: mark, local function"),
        ],
        "{definition}"
    );
    // A run reaches `Pick`, `Small` and `Double` through `go`, `Seed` through the initializer,
    // and `Visible` through program syntax, so none of them is a claim helper.
    assert_eq!(
        definition.matches("(claim helper:").count(),
        3,
        "{definition}"
    );
    assert_production_lines(&definition, file);
}

/// The `// KRS` lines of [`SENTENCES`]' productions: a function's production names the function,
/// a struct's or a `fn`'s alike, and a constructor's names its enum variant and fields; the
/// lifted function's production, the sorts and the subsorts have none.
fn assert_production_lines(definition: &str, file: &str) {
    // A function's production names the function, a struct's or a `fn`'s alike, and a
    // constructor's names its enum variant and fields.
    for (production, expected) in [
        ("syntax Int ::= \"h\"", format!("{file}: H")),
        ("syntax Int ::= \"double\"", format!("{file}: Double")),
        ("syntax Int ::= \"visible\"", format!("{file}: Visible")),
        (
            "syntax Exp ::= \"go\"",
            format!("{file}: ExpSyntax::Go {{ value }}"),
        ),
        (
            "syntax Exp ::= \"halt\"",
            format!("{file}: ExpSyntax::Halt"),
        ),
        (
            "syntax Exp ::= \"mark\"",
            format!("{file}: MarkSyntax::Mark {{ n, s }}"),
        ),
    ] {
        assert_eq!(
            marker_above(definition, production),
            expected,
            "{definition}"
        );
    }
    // The function lifted out of `mark`'s `let` block is KRS's, so its production has no line.
    assert!(
        !marker_above(definition, "syntax Int ::= \"krsLocal_").contains("// KRS"),
        "{definition}"
    );
    // Only rule-like sentences, the configuration and the authored productions have the line:
    // the sorts and subsorts, which `k::sorts!` declares as a list, have none.
    let krs_lines = definition.matches("// KRS ").count() - 1;
    let sentences = definition.matches("\n  rule ").count()
        + definition.matches("\n  context ").count()
        + 1
        + definition.matches(" ::= \"").count()
        - definition.matches(" ::= \"krsLocal_").count();
    assert_eq!(krs_lines, sentences, "{definition}");
    let lines = definition.lines().collect::<Vec<_>>();
    for (index, line) in lines.iter().enumerate() {
        if line.trim_start().starts_with("syntax ") && !line.contains(" ::= \"") {
            assert!(!lines[index - 1].contains("// KRS"), "{line}");
        }
    }
}

/// A `raw_k!` sentence keeps its own comment, without line or column, and no `// KRS` line;
/// its opaque text may apply any function, so no equation is marked a claim helper.
#[test]
fn a_raw_sentence_keeps_its_comment_without_position_and_unmarks_claim_helpers() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), RAW, true);
    let (definition, _) = emit_k(target.path(), &manifest, "emitted");
    assert_eq!(
        line_above(&definition, "rule <k> halted"),
        "  // raw_k! sources/src/lib.rs (opaque to KRS)"
    );
    assert!(
        definition.contains("  // KRS sources/src/lib.rs: Helper\n"),
        "{definition}"
    );
    assert!(!definition.contains("claim helper"), "{definition}");
}

/// The comments hold no source position: blank lines inserted at the top of the Rust file,
/// which move every item and the `raw_k!`, leave both artifacts byte-identical.
#[test]
fn moving_rust_lines_leaves_both_artifacts_byte_identical() {
    let target = shared_fixture_target();
    for (name, source, raw) in [("sentences", SENTENCES, false), ("raw", RAW, true)] {
        let temporary = temp_dir();
        let manifest = package(temporary.path(), source, raw);
        let before = emit_k(target.path(), &manifest, "before");
        let library = manifest.with_file_name("src").join("lib.rs");
        let text = fs::read_to_string(&library).unwrap();
        fs::write(&library, format!("\n\n\n{text}")).unwrap();
        let after = emit_k(target.path(), &manifest, "after");
        assert_eq!(before, after, "{name}");
    }
}

/// Productions of each shape and literals from constants: the select-vector shape (a rule that
/// writes the interrupt flag register `IF`), a named-field variant, a zero-field variant, a
/// struct constructor, a syntactic list, and constants of `Int`, `String` and `Bool`, used
/// directly, through another constant, inside a larger term, in arithmetic, and as part of a
/// constant whose value is a larger term.
const MARKERS: &str = r#"
use k::builtin::{Bool, String};

k::sorts! {
    Status: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum Step {
    #[k::syntax("selectVector")] SelectVector(),
    #[k::syntax("write({address}, {value})")] Write { address: Int, value: Int },
    #[k::syntax("say({text}, {loud})")] Say { text: String, loud: Bool },
    #[k::syntax("report({flags})")] Report { flags: Status },
}

#[k::constructor(sort = Status, syntax = "flags({z}, {n}, {h}, {c})")]
pub struct Flags {
    pub z: Term<Bool>,
    pub n: Term<Bool>,
    pub h: Term<Bool>,
    pub c: Term<Bool>,
}

#[k::syntax_list(separator = ",")]
pub enum Operands {
    Cons { head: Int, tail: Operands },
    Nil(),
}

/// The interrupt flag register.
#[k::constant]
pub const IF: Int = 0xFF0F;

/// The same register under another name.
#[k::constant]
pub const FLAGS_REGISTER: Int = IF;

#[k::constant]
pub const GREETING: String = "hi";

#[k::constant]
pub const LOUD: Bool = true;

/// A constant whose value is a larger term holding another constant.
#[k::constant]
pub const RESET: Exp = Step::Write { address: IF, value: 0 };

#[k::function(total, internal)]
pub fn Count(operands: Term<Operands>) -> Term<Int> {
    match operands {
        Operands::Nil() => 0,
        Operands::Cons { tail, .. } => 1 + Count(tail),
    }
}

k::rules! {
    for Exp;
    use Step::*;

    select_vector: SelectVector() => Write { address: IF, value: 1 };
    aliased: Write { address: FLAGS_REGISTER, value: 1 } => RESET;
    shifted: Write { address: 1, value: 1 } => Write { address: IF + 1, value: 2 };
    said: Say { text: GREETING, loud: LOUD } => Report { flags: Flags(LOUD, false, false, true) };
}
"#;

/// The text of every `term` node `sources.json` in `directory` places in `definition.k`.
fn term_ranges(manifest: &Path, directory: &str, definition: &str) -> Vec<String> {
    let sources: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(manifest.with_file_name(directory).join("sources.json")).unwrap(),
    )
    .unwrap();
    sources["entries"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| {
            entry["node_kind"] == "term" && entry["generated"]["artifact"] == "definition.k"
        })
        .map(|entry| {
            let generated = &entry["generated"];
            definition[usize::try_from(generated["start_byte"].as_u64().unwrap()).unwrap()
                ..usize::try_from(generated["end_byte"].as_u64().unwrap()).unwrap()]
                .to_owned()
        })
        .collect()
}

/// A production the author wrote names its item, as a rule does: an enum variant by its path,
/// with its named fields in production order, a struct constructor with its fields, so that
/// `flags(_, _, _, _)` is readable. A derived production names no item: the syntactic list's
/// `List{..}` family and the generated cell sorts have no line.
#[test]
fn a_production_names_its_item_and_a_constructor_its_fields() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), MARKERS, false);
    let (definition, _) = emit_k(target.path(), &manifest, "emitted");
    let file = "  // KRS sources/src/lib.rs";
    for (production, expected) in [
        (
            "syntax Exp ::= \"selectVector\"",
            format!("{file}: Step::SelectVector"),
        ),
        (
            "syntax Exp ::= \"write\"",
            format!("{file}: Step::Write {{ address, value }}"),
        ),
        (
            "syntax Exp ::= \"say\"",
            format!("{file}: Step::Say {{ text, loud }}"),
        ),
        (
            "syntax Status ::= \"flags\"",
            format!("{file}: Flags {{ z, n, h, c }}"),
        ),
        ("syntax Int ::= \"count\"", format!("{file}: Count")),
    ] {
        assert_eq!(
            marker_above(&definition, production),
            expected,
            "{definition}"
        );
    }
    // The list's cons is the `List{..}` family K generates for the whole enum, and its
    // terminator is not written at all.
    assert!(
        !marker_above(&definition, "syntax Operands ::= List{Int, \",\"}").contains("// KRS"),
        "{definition}"
    );
    assert!(!definition.contains("Operands::"), "{definition}");
    // No line names a cell sort: the configuration's cells are K's, not productions.
    assert!(!definition.contains("Cell\n"), "{definition}");
    for line in definition.lines().filter(|line| line.contains("// KRS ")) {
        assert!(!line.contains("Cell"), "{line}");
    }
}

/// A literal that is the whole value of exactly one constant written at its place names it:
/// `IF` directly, `FLAGS_REGISTER` (defined as `IF`) by the name the author wrote, `GREETING`
/// and `LOUD` of `String` and `Bool`, `LOUD` inside a larger term, `IF` as an operand of
/// arithmetic, which K writes unfolded. A literal that is a part of a constant's value, `RESET`'s
/// `65295` and `0`, is not that constant's whole value, and no literal the author wrote names
/// one. The name is K layout outside the literal's range, and removing it leaves the K of the
/// same package with the literals written in place of the constants.
#[test]
fn a_literal_names_the_constant_whose_whole_value_it_is() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), MARKERS, false);
    let (definition, _) = emit_k(target.path(), &manifest, "emitted");
    for (label, expected) in [
        (
            "select-vector",
            "<k> selectVector => write ( 65295 /* IF */ , 1 ) ... </k>",
        ),
        (
            "aliased",
            "<k> write ( 65295 /* FLAGS_REGISTER */ , 1 ) => write ( 65295 , 0 ) ... </k>",
        ),
        (
            "shifted",
            "<k> write ( 1 , 1 ) => write ( 65295 /* IF */ +Int 1 , 2 ) ... </k>",
        ),
        (
            "said",
            "<k> say ( \"hi\" /* GREETING */ , true /* LOUD */ ) => report ( flags ( true /* LOUD */ , false , false , true ) ) ... </k>",
        ),
    ] {
        let lines = definition.lines().collect::<Vec<_>>();
        let at = lines
            .iter()
            .position(|line| line.trim_start() == format!("rule [{label}]:"))
            .unwrap_or_else(|| panic!("rule [{label}] is not in\n{definition}"));
        assert_eq!(lines[at + 1].trim_start(), expected, "{definition}");
    }
    assert_eq!(definition.matches("/* ").count(), 6, "{definition}");
    // Each literal's own range is the literal: the name follows it as layout.
    let terms = term_ranges(&manifest, "emitted", &definition);
    assert!(
        terms.iter().filter(|term| term.as_str() == "65295").count() >= 4,
        "{terms:?}"
    );
    for named in [
        "65295 /* IF */",
        "65295 /* FLAGS_REGISTER */",
        "\"hi\" /* GREETING */",
        "true /* LOUD */",
    ] {
        assert!(!terms.iter().any(|term| term == named), "{terms:?}");
    }
    // The same package with each constant's value written at its uses emits the same K but for
    // the names.
    let inline = MARKERS
        .replace(
            "Write { address: FLAGS_REGISTER, value: 1 } => RESET",
            "Write { address: 65295, value: 1 } => Write { address: 65295, value: 0 }",
        )
        .replace("IF + 1", "65295 + 1")
        .replace("address: IF, value: 1 }", "address: 65295, value: 1 }")
        .replace("text: GREETING, loud: LOUD", "text: \"hi\", loud: true")
        .replace("Flags(LOUD,", "Flags(true,");
    let inline_directory = temp_dir();
    let inline_manifest = package(inline_directory.path(), &inline, false);
    let (inline_definition, _) = emit_k(target.path(), &inline_manifest, "emitted");
    assert!(!inline_definition.contains("/* "), "{inline_definition}");
    assert_eq!(
        without_constant_names(&definition),
        inline_definition,
        "{definition}"
    );
}
