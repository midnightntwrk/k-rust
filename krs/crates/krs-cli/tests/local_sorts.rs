//! A local names its value, so the value is read where the local is used, at the sort its uses
//! stand at: `{ let y = v; y }` means what `v` means written there, and a mistake `v` makes there
//! is its own, met inside it. Each row writes one construct directly and through a local at one
//! position: an accepted construct is accepted through the local with the K of the direct form
//! under the `#let`, and a refused one is refused with the direct form's error, at the same text.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const BASE: &str = r#"
use k::builtin::{Bool, Int, KSequence, List, list};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("hold({a})")] Hold { a: KItem },
    #[k::syntax("two({a}, {b})")] Two { a: Int, b: Bool },
    #[k::syntax("az({a})")] #[k::alias] Az { a: KItem },
    #[k::syntax("dz({a})")] #[k::desugar] Dz { a: KItem },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], acc: 0 }
    }
}

#[k::function(partial, sort = Int, syntax = "size({a})")]
pub struct Size {
    pub a: Term<KItem>,
}
"#;

/// The alias and the desugar clause the base's productions need, unless a row writes one.
const ALIAS: &str =
    "#[k::alias]\nfn az(k::term![Cmd::Az(x)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Hold(x)\n}\n";
const DESUGAR: &str =
    "#[k::desugar]\nfn dz(k::term![Cmd::Dz(x)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Go()\n}\n";

/// A readable rule whose condition is `HOLE`.
const RULE_CONDITION: &str = "k::rules! {\n    for Machine;\n    use Cmd::*;\n\n    #[k::requires(HOLE)]\n    probe: { k: [Hold(x), ..] } => { k: [..] };\n}\n";
/// A readable rule that writes `HOLE` as a computation item.
const RULE_ITEM: &str = "k::rules! {\n    for Machine;\n    use Cmd::*;\n\n    probe: { k: [Hold(x), ..] } => { k: [HOLE, ..] };\n}\n";
/// An equation whose condition is `HOLE`.
const EQUATION_CONDITION: &str = "#[k::requires(HOLE)]\n#[k::equation]\nfn size(k::term![Size(x)]: Term<Int>) -> Term<Int> {\n    1\n}\n";
/// An alias clause whose result's root is `HOLE`, read at the fn's `KItem`.
const ALIAS_ROOT: &str =
    "#[k::alias]\nfn az(k::term![Cmd::Az(x)]: Term<Stmt>) -> Term<KItem> {\n    HOLE\n}\n";
/// A desugar clause whose result's root is `HOLE`, read at the fn's `KItem`.
const DESUGAR_ROOT: &str =
    "#[k::desugar]\nfn dz(k::term![Cmd::Dz(x)]: Term<Stmt>) -> Term<KItem> {\n    HOLE\n}\n";
/// A `cells!` claim whose condition is `HOLE`, over the binder `x` declared `KItem`.
const CLAIM_CONDITION: &str = concat!(
    "#[k::claim(all_paths, label = \"probe-claim\")]\n",
    "#[k::requires(HOLE)]\n",
    "pub fn probe_claim(\n    x: Term<KItem>,\n",
    "    k::cells! { k: k::configuration::KCell(Cmd::Hold(x), tail @ ..), state @ .. }: Machine,\n",
    ") -> Machine {\n    k::cells! { k: k::configuration::KCell(..tail), ..state }\n}\n"
);

/// One construct at one position: the template, the direct spelling and the spelling through a
/// local.
struct Row {
    name: &'static str,
    template: &'static str,
    direct: &'static str,
    through: &'static str,
}

const ROWS: &[Row] = &[
    // R1: `x` at a condition is read at `Bool`, through the local as written there.
    Row {
        name: "binder-at-rule-condition",
        template: RULE_CONDITION,
        direct: "x",
        through: "{ let y = x; y }",
    },
    Row {
        name: "binder-at-rule-condition-block-value",
        template: RULE_CONDITION,
        direct: "x",
        through: "{ let y = { x }; y }",
    },
    Row {
        name: "binder-at-equation-condition",
        template: EQUATION_CONDITION,
        direct: "x",
        through: "{ let y = x; y }",
    },
    Row {
        name: "item-read-at-rule-condition",
        template: RULE_CONDITION,
        direct: "list::get(list::item(x), 0)",
        through: "{ let y = list::get(list::item(x), 0); y }",
    },
    // A use at a `KItem` field beside one at `Bool`: the value is read at `Bool`.
    Row {
        name: "uses-at-kitem-and-bool",
        template: RULE_CONDITION,
        direct: "k::matches!(Hold(x), _) && x",
        through: "{ let y = x; k::matches!(Hold(y), _) && y }",
    },
    // R2: a value of another sort at a condition is refused inside it.
    Row {
        name: "int-literal-at-rule-condition",
        template: RULE_CONDITION,
        direct: "1",
        through: "{ let y = 1; y }",
    },
    Row {
        name: "int-application-at-rule-condition",
        template: RULE_CONDITION,
        direct: "x + 1",
        through: "{ let y = x + 1; y }",
    },
    // Uses at sorts that share none: the value is refused where it does not fit.
    Row {
        name: "literal-at-int-and-bool",
        template: RULE_ITEM,
        direct: "Two(1, 1)",
        through: "{ let y = 1; Two(y, y) }",
    },
    Row {
        name: "binder-at-int-and-bool",
        template: RULE_ITEM,
        direct: "Two(x, x)",
        through: "{ let y = x; Two(y, y) }",
    },
    // R3: a static clause's result root of another sort, inside the value.
    Row {
        name: "alias-result-root",
        template: ALIAS_ROOT,
        direct: "x",
        through: "{ let y = x; y }",
    },
    Row {
        name: "desugar-result-root",
        template: DESUGAR_ROOT,
        direct: "x < 1",
        through: "{ let y = x < 1; y }",
    },
    // R4: an object term as a predicate's body, inside the value.
    Row {
        name: "object-term-as-predicate-body",
        template: CLAIM_CONDITION,
        direct: "k::ml::exists(|v: Int| 1)",
        through: "k::ml::exists(|v: Int| { let y = 1; y })",
    },
    // R5: in a `cells!` claim's condition the condition's sort is met before the binder's.
    Row {
        name: "int-application-at-claim-condition",
        template: CLAIM_CONDITION,
        direct: "x + 1",
        through: "{ let y = x + 1; y }",
    },
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `library`.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-LOCAL\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The first error's headline and the source text its caret marks.
fn first_error(stderr: &str) -> String {
    let lines = stderr.lines().collect::<Vec<_>>();
    let Some(index) = lines.iter().position(|line| line.starts_with("error[")) else {
        return format!("no error: {stderr}");
    };
    // `--> path`, ` |`, `N | source`, ` |   ^^^`.
    let marked = lines
        .get(index + 3)
        .zip(lines.get(index + 4))
        .and_then(|(source, carets)| {
            let source = source.split_once(" | ")?.1;
            let carets = carets.split_once(" | ")?.1;
            let start = carets.find('^')?;
            let width = carets[start..].chars().take_while(|c| *c == '^').count();
            source.get(start..start + width).map(str::to_owned)
        })
        .unwrap_or_default();
    format!("{} at `{marked}`", lines[index])
}

/// The emitted sentences of the row's own, the probe rule or the equation, each on one line.
fn probe_sentences(definition: &str) -> Vec<String> {
    let mut sentences = Vec::<String>::new();
    let mut open = false;
    for line in definition.lines().map(str::trim) {
        if line.starts_with("rule ") {
            open = line.starts_with("rule [probe]") || line.starts_with("rule size");
            if open {
                sentences.push(line.to_owned());
            }
        } else if line.is_empty()
            || line == "endmodule"
            || line.starts_with("//")
            || line.starts_with("syntax")
        {
            open = false;
        } else if open && let Some(sentence) = sentences.last_mut() {
            sentence.push(' ');
            sentence.push_str(line);
        }
    }
    sentences
}

/// The verdict on `library`: its first error, or its probe's K.
fn verdict(target: &Path, root: &Path, name: &str, library: &str) -> String {
    let manifest = package(root, name, library);
    let output = root.join(name).join("emitted");
    let (success, _, stderr) = krs(
        target,
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    if !success {
        return first_error(&stderr);
    }
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    format!("accepted: {}", probe_sentences(&definition).join(" | "))
}

/// The library of `row` with `spelling` in its hole.
fn library(row: &Row, spelling: &str) -> String {
    let mut library = BASE.to_owned();
    let sentence = row.template.replace("HOLE", spelling);
    if !sentence.contains("fn az(") {
        library.push_str(ALIAS);
    }
    if !sentence.contains("fn dz(") {
        library.push_str(DESUGAR);
    }
    library.push_str(&sentence);
    library
}

/// `accepted` K through the local, with each block `( #let Y:S = T #in B )` read as `B` with `T`
/// for `Y:S`, so that it is comparable with the direct form's.
fn through_the_block(through: &str) -> String {
    let mut text = through.to_owned();
    while let Some(start) = text.find("( #let ") {
        let inner = start + "( #let ".len();
        let mut depth = 1_usize;
        let mut end = None;
        for (offset, character) in text[inner..].char_indices() {
            match character {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(inner + offset);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(end) = end else {
            break;
        };
        let block = text[inner..end].trim_end().to_owned();
        let Some((binder, rest)) = block.split_once(" = ") else {
            break;
        };
        let Some((value, body)) = rest.split_once(" #in ") else {
            break;
        };
        let read = body.replace(binder, value);
        text.replace_range(start..=end, &read);
    }
    text
}

/// Each construct through a local has the verdict it has written at the local's use: the direct
/// form's K under the block where it is accepted (`#let Y:Bool = X:Bool`: the binder read at the
/// condition's `Bool`), and the direct form's error, at the same text inside the value, where it is
/// refused.
#[test]
fn a_value_through_a_local_is_judged_where_the_local_is_used() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let verdicts = std::thread::scope(|scope| {
        let handles = ROWS
            .iter()
            .map(|row| {
                let (target, root) = (target.path(), temporary.path());
                scope.spawn(move || {
                    let direct = verdict(
                        target,
                        root,
                        &format!("{}-direct", row.name),
                        &library(row, row.direct),
                    );
                    let through = verdict(
                        target,
                        root,
                        &format!("{}-local", row.name),
                        &library(row, row.through),
                    );
                    (row.name, direct, through)
                })
            })
            .collect::<Vec<_>>();
        handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .collect::<Vec<_>>()
    });
    let mut lines = Vec::new();
    for (name, direct, through) in &verdicts {
        let same = if direct.starts_with("accepted") {
            *direct == through_the_block(through)
        } else {
            direct == through
        };
        assert!(same, "{name}:\n  direct:  {direct}\n  through: {through}");
        lines.push(format!("{name}: {through}"));
    }
    expect_test::expect![[r"
        binder-at-rule-condition: accepted: rule [probe]: <k> hold ( X:Bool ) => .K ... </k> requires ( #let Y:Bool = X:Bool #in Y:Bool )
        binder-at-rule-condition-block-value: accepted: rule [probe]: <k> hold ( X:Bool ) => .K ... </k> requires ( #let Y:Bool = X:Bool #in Y:Bool )
        binder-at-equation-condition: accepted: rule size ( X:Bool ) => 1 requires ( #let Y:Bool = X:Bool #in Y:Bool ) [label(org_krs_local--size)]
        item-read-at-rule-condition: accepted: rule [probe]: <k> hold ( X:KItem ) => .K ... </k> requires (0 <Int size(ListItem(X:KItem))) andThenBool (isBool(ListItem(X:KItem) [ 0 ]) andThenBool ( #let Y:Bool = {ListItem(X:KItem) [ 0 ]}:>Bool #in Y:Bool ))
        uses-at-kitem-and-bool: accepted: rule [probe]: <k> hold ( X:Bool ) => .K ... </k> requires ( #let Y:Bool = X:Bool #in ( _ :=K hold ( Y:Bool ) ) andThenBool Y:Bool )
        int-literal-at-rule-condition: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-LOCAL::probe (rule): literal `1` of sort Int is not admissible at sort Bool at `1`
        int-application-at-rule-condition: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-LOCAL::probe (rule): application result sort Int is not admissible at sort Bool at `+`
        literal-at-int-and-bool: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-LOCAL::probe (rule): literal `1` of sort Int is not admissible at sort Bool at `1`
        binder-at-int-and-bool: error[krs::analysis::incompatible-binder]: binder `x` is bound at `KItem`, but an occurrence needs `Int` at `x`
        alias-result-root: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-LOCAL::az (alias): the result of alias clause `az` has sort `KItem`, which is not below `Stmt`, the sort of the production `Cmd::Az` it expands: a program's application of the production is replaced by the result where a `Stmt` stands, and a term of sort `KItem` is not one there; write a result of sort `Stmt`, or of a sort below it: declare the fn's result `-> Term<Stmt>`, which reads `x` at `Stmt`, or the binder's sort, `x: Stmt` at `x`
        desugar-result-root: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-LOCAL::dz (desugar): the result of desugar clause `dz` has sort `Bool`, which is not below `Stmt`, the sort of the production `Cmd::Dz` it expands: a program's application of the production is replaced by the result where a `Stmt` stands, and a term of sort `Bool` is not one there; write a result of sort `Stmt`, or of a sort below it at `<`
        object-term-as-predicate-body: error[krs::analysis::invalid-ml-predicate]: a predicate is expected here, but this is an object term; an object Bool enters matching logic only as `ml::equals(true, <term>)` (K's `{ true #Equals B }`) at `1`
        int-application-at-claim-condition: error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-LOCAL::probe_claim (claim): application result sort Int is not admissible at sort Bool at `+`"]].assert_eq(&lines.join("\n"));
}
