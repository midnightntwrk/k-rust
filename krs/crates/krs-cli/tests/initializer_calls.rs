//! What the initializer of a definition that holds a cell group may call.
//!
//! A group package's rules name the definition's cells, so the configuration is emitted in
//! `<NS>-CONFIGURATION`, a module below the group package's. The configuration sentence names
//! the productions of its initial terms, and a K sentence may name only productions declared in
//! its module's import closure. A production's declaration needs only its sorts, and its
//! equations are rules of the definition, which the initial term is evaluated in. So the
//! configuration module declares the productions its initializer names that its imports do not
//! supply, and their equations stay in the modules of their packages.
//!
//! The fixture `group-boot/board` of the configuration-cells gate holds `group_core::Core` and
//! starts from productions no program can contain: of its own package, and of `group-boot/rom`,
//! which depends on the group's package. Two productions stay refused, each with the arrangement
//! that works: one over a cell sort, and one in a group that a precedence sentence orders.
//!
//! The configuration sentence is also typed in its module, and a K module reads only its own
//! subsort sentences and those of the modules it imports. A subsort sentence needs only its two
//! sorts. So the configuration module holds each subsort sentence its configuration's typing
//! reads that its imports do not supply: one into `Map`, `List` or `Set`, which have no `-SYNTAX`
//! module, or into a framework sort. The fixture `group-slot` starts cells of sorts above `Map`
//! and `List`; a subsort sentence the typing does not read stays in the module of its package.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// The configuration-cells gate's workspace.
fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/configuration-cells/Cargo.toml")
        .canonicalize()
        .unwrap()
}

const BOARD: &str = "krs-configuration-cells-group-boot-board";
const BOARD_DEPENDENCIES: [&str; 2] = [
    "krs-configuration-cells-group-core",
    "krs-configuration-cells-group-boot-rom",
];

/// Runs `krs <command>` on `package`'s `main` definition, composed with the `main` definition of
/// each package of `dependencies`.
fn krs(
    target: &Path,
    manifest: &Path,
    package: &str,
    dependencies: &[&str],
    command: &str,
    extra: &[&str],
) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"]);
    for dependency in dependencies {
        process.args(["--dependency", &format!("{dependency}:main")]);
    }
    let output = process
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

/// The emitted K of a definition.
fn emitted(
    target: &Path,
    manifest: &Path,
    package: &str,
    dependencies: &[&str],
    output: &Path,
) -> String {
    let (success, _, stderr) = krs(
        target,
        manifest,
        package,
        dependencies,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k")).unwrap()
}

/// The lines of the module `name` of an emitted definition that are not comments or blank.
fn module(definition: &str, name: &str) -> Vec<String> {
    definition
        .split("\nmodule ")
        .find_map(|text| text.strip_prefix(&format!("{name}\n")))
        .unwrap_or_else(|| panic!("no module {name} in:\n{definition}"))
        .split("\nendmodule")
        .next()
        .unwrap()
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with("//"))
        .map(str::to_owned)
        .collect()
}

/// The content of the first `<name>` cell in whitespace-flattened text.
fn cell(flat: &str, name: &str) -> String {
    let open = format!("<{name}> ");
    let start = flat
        .find(&open)
        .unwrap_or_else(|| panic!("no `<{name}>` in:\n{flat}"))
        + open.len();
    let end = start + flat[start..].find(&format!(" </{name}>")).unwrap();
    flat[start..end].to_owned()
}

/// The cells a run of `program` on the board ends with, stopped after `depth` steps when given.
fn board_cells(target: &Path, directory: &Path, program: &str, depth: Option<&str>) -> [String; 6] {
    let file = directory.join("program.txt");
    fs::write(&file, program).unwrap();
    let mut extra = vec![file.to_str().unwrap()];
    if let Some(depth) = depth {
        extra.extend(["--depth", depth]);
    }
    let (_, stdout, stderr) = krs(
        target,
        &fixtures(),
        BOARD,
        &BOARD_DEPENDENCIES,
        "run",
        &extra,
    );
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("<core>"), "{stdout}\n{stderr}");
    ["pc", "acc", "timer", "mode", "mem", "shadow"].map(|name| cell(&flat, name))
}

/// The holder checks, and its run starts from the state its functions compute: `Shadow()`, an
/// `internal` `Map`-valued function of its own package whose equation applies `Tick`;
/// `rom::RomImage()`, of a package that depends on the group's, whose equation applies
/// `rom::RomWord()`; `rom::Cost(..)`, over a sort of the group's package; `Tick(..)`, which the
/// holder's rules apply too; and `Mode::Cold()`, a constructor that is not `pub`.
#[test]
fn an_initializer_calls_functions_no_program_can_contain() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let (success, _, stderr) = krs(
        target.path(),
        &fixtures(),
        BOARD,
        &BOARD_DEPENDENCIES,
        "check",
        &[],
    );
    assert!(success, "{stderr}");

    assert_eq!(
        board_cells(target.path(), temporary.path(), "done", Some("0")),
        ["0", "3", "11", "cold", "3 |-> 9 4 |-> 10", "0 |-> 10"].map(str::to_owned),
    );
    // The rules apply `Tick` and `Mode::Warm()`, and read what `RomImage()` computed.
    assert_eq!(
        board_cells(
            target.path(),
            temporary.path(),
            "inc ; load ( 4 ) ; store ( 5 ) ; done",
            None
        ),
        [
            "3",
            "10",
            "31",
            "warm",
            "3 |-> 9 4 |-> 10 5 |-> 10",
            "0 |-> 10"
        ]
        .map(str::to_owned),
    );
}

/// The configuration module declares exactly the productions its configuration names, none of
/// them `private`, since two modules name each. Their equations stay in the modules of their
/// packages, with `RomWord`, which only an equation names, and `Mode::Warm`, which only rules
/// name and which stays `private`.
#[test]
fn the_configuration_module_declares_the_productions_its_initializer_names() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let definition = emitted(
        target.path(),
        &fixtures(),
        BOARD,
        &BOARD_DEPENDENCIES,
        &temporary.path().join("emitted"),
    );
    let declarations = |name: &str| {
        module(&definition, name)
            .into_iter()
            .filter(|line| line.starts_with("syntax ") || line.starts_with("imports "))
            .collect::<Vec<_>>()
    };
    expect_test::expect![[r#"
        [
            "imports INT-SYNTAX",
            "imports KRS-GROUP-BOOT-BOARD-SYNTAX",
            "imports MAP",
            "syntax Int ::= \"cost\" \"(\" Instr \")\" [symbol(cost), function, total]",
            "syntax Phase ::= \"cold\" [symbol(modeCold), format(%1)]",
            "syntax Map ::= \"romImage\" \"(\" \")\" [symbol(romImage), function, total]",
            "syntax Map ::= \"shadow\" \"(\" \")\" [symbol(shadow), function, total]",
            "syntax Int ::= \"tick\" \"(\" Int \")\" [symbol(tick), function, total]",
        ]
    "#]]
    .assert_debug_eq(&declarations("KRS-GROUP-BOOT-BOARD-CONFIGURATION"));
    expect_test::expect![[r#"
        [
            "imports INT",
            "imports KRS-GROUP-BOOT-BOARD-CONFIGURATION",
            "imports KRS-GROUP-BOOT-BOARD-SYNTAX",
            "imports KRS-GROUP-BOOT-ROM",
            "imports KRS-GROUP-CORE",
            "imports MAP",
            "syntax Phase ::= \"warm\" [symbol(modeWarm), private, format(%1)]",
        ]
    "#]]
    .assert_debug_eq(&declarations("KRS-GROUP-BOOT-BOARD"));
    expect_test::expect![[r#"
        [
            "imports INT",
            "imports KRS-GROUP-BOOT-ROM-SYNTAX",
            "imports KRS-GROUP-CORE",
            "imports MAP",
            "syntax Int ::= \"romWord\" \"(\" \")\" [symbol(romWord), function, total]",
        ]
    "#]]
    .assert_debug_eq(&declarations("KRS-GROUP-BOOT-ROM"));
    let equations = |name: &str| {
        module(&definition, name)
            .into_iter()
            .filter_map(|line| {
                let text = line.strip_prefix("rule ")?;
                (!text.starts_with('[')).then(|| text.split(" (").next().unwrap().to_owned())
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        equations("KRS-GROUP-BOOT-ROM"),
        ["cost", "cost", "cost", "romImage", "romWord"]
    );
    assert_eq!(equations("KRS-GROUP-BOOT-BOARD"), ["shadow", "tick"]);
    assert!(
        equations("KRS-GROUP-BOOT-BOARD-CONFIGURATION").is_empty(),
        "{definition}"
    );
}

/// The group and a rule for it, which needs the configuration of the definition that holds it.
const LIB: &str = r#"
use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Instr;
}

#[k::constructors(sort = Instr, result = KResult)]
pub enum Op {
    #[k::syntax("inc")]
    Inc(),
}

#[k::cell]
pub struct Core {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
}

k::rules! {
    for Core;
    use Op::*;

    inc: { k: [Inc(), ..], pc } => { k: [..], pc: int::add(pc, 1) };
}
"#;

/// A holder of the group with a cell `extra` of sort `sort`, which starts as `initial`.
fn holder(declarations: &str, sort: &str, initial: &str) -> String {
    format!(
        r"
use k::builtin::{{Int, Map}};
use k::{{KItem, KResult, Term}};
{declarations}
#[k::configuration]
pub struct Board {{
    #[k::cell(nested)]
    pub core: lib::Core,
    #[k::cell]
    pub extra: {sort},
}}

impl Board {{
    #[k::init]
    pub fn init(pgm: lib::Instr) -> Self {{
        Self {{
            core: lib::Core {{ k: k::k![pgm], pc: 0 }},
            extra: {initial},
        }}
    }}
}}
"
    )
}

/// A workspace of `lib` and the holder `board` with this source; the manifest of `board`.
fn workspace(root: &Path, board: &str) -> PathBuf {
    workspace_of(root, LIB, board)
}

/// A workspace of the group's package with the source `lib` and the holder `board` with this
/// source; the manifest of `board`.
fn workspace_of(root: &Path, lib: &str, board: &str) -> PathBuf {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    let write = |name: &str, source: &str, dependencies: &str| {
        let directory = root.join(name);
        fs::create_dir_all(directory.join("src")).unwrap();
        fs::write(
            directory.join("src/lib.rs"),
            format!("#![allow(unused_imports, dead_code)]\n{source}"),
        )
        .unwrap();
        fs::write(
            directory.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"ORG-{}\"\n\n[package.metadata.krs.definitions.main]\n",
                name.to_ascii_uppercase()
            ),
        )
        .unwrap();
        directory.join("Cargo.toml")
    };
    write("lib", lib, "");
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"lib\", \"board\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    write("board", board, "lib = { path = \"../lib\" }\n")
}

/// The `error[..]` headline of a refused `krs check` of `board`, and the item it names.
fn refusal(target: &Path, manifest: &Path) -> String {
    let (success, _, stderr) = krs(target, manifest, "board", &["lib"], "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    stderr
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("error") || line.starts_with("= note: "))
        .collect::<Vec<_>>()
        .join("\n")
}

/// A group of one level has no sentence that orders it, so its productions are declared like
/// any other: the configuration module declares the one the initializer names, with its group.
#[test]
fn a_production_in_a_group_no_sentence_orders_is_declared() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = workspace(
        temporary.path(),
        &holder(
            r#"
k::sorts! {
    Mode;
}

#[k::constructors(sort = Mode, result = KResult)]
#[k::precedence((Ready, Halted))]
enum ModeSyntax {
    #[k::syntax("ready")]
    Ready(),
    #[k::syntax("halted")]
    Halted(),
}
"#,
            "Mode",
            "ModeSyntax::Ready()",
        ),
    );
    let definition = emitted(
        target.path(),
        &manifest,
        "board",
        &["lib"],
        &temporary.path().join("emitted"),
    );
    let productions = |name: &str| {
        module(&definition, name)
            .into_iter()
            .filter(|line| line.starts_with("syntax Mode ::="))
            .map(|line| {
                // The group's emitted name is a hash of its identity.
                let group = line.find("group(").map(|start| {
                    let end = start + line[start..].find(')').unwrap();
                    line[start..=end].to_owned()
                });
                group.map_or(line.clone(), |group| line.replace(&group, "group(..)"))
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        productions("ORG-BOARD-CONFIGURATION"),
        [r#"syntax Mode ::= "ready" [symbol(modeSyntaxReady), group(..), format(%1)]"#]
    );
    assert_eq!(
        productions("ORG-BOARD"),
        [r#"syntax Mode ::= "halted" [symbol(modeSyntaxHalted), private, group(..), format(%1)]"#]
    );
}

/// A production over a cell sort is refused: the configuration sentence declares the sort.
#[test]
fn a_production_over_a_cell_sort_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = workspace(
        temporary.path(),
        &holder(
            r"
#[k::function(partial, internal)]
pub fn Spare() -> Term<lib::Core>;

#[k::function(total, internal)]
pub fn Snap(core: Term<KItem>) -> Term<Int> {
    7
}
",
            "Int",
            "Snap(Spare())",
        ),
    );
    expect_test::expect![[r"
        error[krs::partition::configuration-visibility]: the rules of `ORG-LIB` need the configuration, so it is emitted in `ORG-BOARD-CONFIGURATION`, a module below theirs; the configuration names `spare`, which `ORG-BOARD` declares over the cell sort `CoreCell`; the configuration sentence declares its cell sorts, so the production and the configuration would each need the other declared first, and `ORG-BOARD-CONFIGURATION` does not declare `spare`. An initializer may call a production of `ORG-BOARD` or of a package it depends on whose argument and result sorts are not cell sorts
        = note: in ORG-BOARD::Spare (constructor)"]]
    .assert_eq(&refusal(target.path(), &manifest));
}

/// A production in a group that a precedence sentence orders is refused: the sentence stays in
/// its package's module with the group's other productions. Program syntax is offered only where
/// every production the sentence orders could be program syntax: `After` holds a `Map`, and K
/// has no `MAP-SYNTAX` module.
#[test]
fn a_production_in_an_ordered_group_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let ordered = |field: &str, syntax: &str| {
        holder(
            &format!(
                r#"
k::sorts! {{
    Mode;
}}

#[k::constructors(sort = Mode, result = KResult)]
#[k::precedence((Ready) > (After))]
enum ModeSyntax {{
    #[k::syntax("ready")]
    Ready(),
    #[k::syntax("after {{mode}}{syntax}")]
    After {{ mode: Mode{field} }},
}}
"#
            ),
            "Mode",
            "ModeSyntax::Ready()",
        )
    };
    let manifest = workspace(&temporary.path().join("plain"), &ordered("", ""));
    expect_test::expect![[r"
        error[krs::partition::configuration-visibility]: the rules of `ORG-LIB` need the configuration, so it is emitted in `ORG-BOARD-CONFIGURATION`, a module below theirs; the configuration names `modeSyntaxReady`, which `ORG-BOARD` declares in a group that one of its precedence or associativity sentences orders; K applies priorities and associativity per module and the sentence stays in `ORG-BOARD` with the group's other productions, so `ORG-BOARD-CONFIGURATION` cannot declare `modeSyntaxReady`. Declare the production the initializer calls outside every ordered group, in `ORG-BOARD` or in a package it depends on, or make every production those sentences order program syntax (`pub`, not `internal`), which lets programs contain them
        = note: in ORG-BOARD::Ready (constructor enum:ModeSyntax)"]]
    .assert_eq(&refusal(target.path(), &manifest));

    let manifest = workspace(
        &temporary.path().join("map"),
        &ordered(", seen: Map<Int, Int>", " {seen}"),
    );
    expect_test::expect![[r"
        error[krs::partition::configuration-visibility]: the rules of `ORG-LIB` need the configuration, so it is emitted in `ORG-BOARD-CONFIGURATION`, a module below theirs; the configuration names `modeSyntaxReady`, which `ORG-BOARD` declares in a group that one of its precedence or associativity sentences orders; K applies priorities and associativity per module and the sentence stays in `ORG-BOARD` with the group's other productions, so `ORG-BOARD-CONFIGURATION` cannot declare `modeSyntaxReady`. Declare the production the initializer calls outside every ordered group, in `ORG-BOARD` or in a package it depends on
        = note: in ORG-BOARD::Ready (constructor enum:ModeSyntax)"]]
    .assert_eq(&refusal(target.path(), &manifest));
}

const SLOT: &str = "krs-configuration-cells-group-slot";
const SLOT_DEPENDENCIES: [&str; 1] = ["krs-configuration-cells-group-core"];

/// The `syntax` and `imports` lines of the module `name` of an emitted definition.
fn declarations(definition: &str, name: &str) -> Vec<String> {
    module(definition, name)
        .into_iter()
        .filter(|line| line.starts_with("syntax ") || line.starts_with("imports "))
        .collect()
}

/// The `syntax` lines of `board`'s configuration module and of its semantics module, for a
/// holder with these declarations and a cell `extra` of sort `sort` that starts as `initial`,
/// beside a group's package with the source `lib`.
fn placed(lib: &str, declared: &str, sort: &str, initial: &str) -> (Vec<String>, Vec<String>) {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = workspace_of(temporary.path(), lib, &holder(declared, sort, initial));
    let definition = emitted(
        target.path(),
        &manifest,
        "board",
        &["lib"],
        &temporary.path().join("emitted"),
    );
    let syntax = |name: &str| {
        declarations(&definition, name)
            .into_iter()
            .filter(|line| line.starts_with("syntax "))
            .collect::<Vec<_>>()
    };
    (syntax("ORG-BOARD-CONFIGURATION"), syntax("ORG-BOARD"))
}

/// A `Map`-valued function no program can contain.
const BOOT: &str = r"
#[k::function(total, internal)]
pub fn Boot() -> Term<Map<Int, Int>> {
    k::map![1 -> 2]
}
";
const BOOT_K: &str = r#"syntax Map ::= "boot" "(" ")" [symbol(boot), function, total]"#;

/// The holder of `group-slot` checks and runs: `store`, of sort `Store`, starts from a `Map`,
/// `trail`, of sort `Trail`, from a `List`, and `journal` from a constructor whose `Store` field
/// holds a `Map`. The configuration module holds the two subsort sentences, which are not
/// program syntax, and the semantics module of their package, which imports it, holds neither.
#[test]
fn the_configuration_module_holds_the_subsorts_its_typing_reads() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let (success, _, stderr) = krs(
        target.path(),
        &fixtures(),
        SLOT,
        &SLOT_DEPENDENCIES,
        "check",
        &[],
    );
    assert!(success, "{stderr}");
    let definition = emitted(
        target.path(),
        &fixtures(),
        SLOT,
        &SLOT_DEPENDENCIES,
        &temporary.path().join("emitted"),
    );
    assert_eq!(
        declarations(&definition, "KRS-GROUP-SLOT-CONFIGURATION"),
        [
            "imports INT-SYNTAX",
            "imports KRS-GROUP-SLOT-SYNTAX",
            "imports LIST",
            "imports MAP",
            r#"syntax Map ::= "image" "(" ")" [symbol(image), function, total]"#,
            "syntax Store ::= Map",
            "syntax Trail ::= List",
        ]
    );
    assert_eq!(
        declarations(&definition, "KRS-GROUP-SLOT"),
        [
            "imports INT-SYNTAX",
            "imports KRS-GROUP-CORE",
            "imports KRS-GROUP-SLOT-CONFIGURATION",
            "imports KRS-GROUP-SLOT-SYNTAX",
            "imports LIST",
            "imports MAP",
        ]
    );

    let cells = |program: &str| {
        let file = temporary.path().join("program.txt");
        fs::write(&file, program).unwrap();
        let (_, stdout, stderr) = krs(
            target.path(),
            &fixtures(),
            SLOT,
            &SLOT_DEPENDENCIES,
            "run",
            &[file.to_str().unwrap()],
        );
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(flat.contains("<core>"), "{stdout}\n{stderr}");
        ["store", "trail", "journal"].map(|name| cell(&flat, name))
    };
    assert_eq!(
        cells("done"),
        [
            "3 |-> 9 4 |-> 10",
            "ListItem ( 0 )",
            "was ( 3 |-> 9 4 |-> 10 )"
        ]
        .map(str::to_owned),
    );
    // The rule `write`, above the configuration, places a `Map` and a `List` in the same cells.
    assert_eq!(
        cells("inc ; load ( 4 ) ; store ( 5 ) ; done"),
        [
            "3 |-> 9 4 |-> 10 5 |-> 10",
            "ListItem ( 5 )",
            "was ( 3 |-> 9 4 |-> 10 )"
        ]
        .map(str::to_owned),
    );

    let (success, partition, stderr) = krs(
        target.path(),
        &fixtures(),
        SLOT,
        &SLOT_DEPENDENCIES,
        "check",
        &["--partition"],
    );
    assert!(success, "{stderr}");
    assert!(
        partition.ends_with(
            "KRS-GROUP-SLOT-CONFIGURATION (sentences the configuration depends on, held in place of their packages' modules)\n  subsort Store ::= Map: of KRS-GROUP-SLOT\n  subsort Trail ::= List: of KRS-GROUP-SLOT\n  production Image: of KRS-GROUP-SLOT\n"
        ),
        "{partition}"
    );
}

/// Only the sentences the configuration module does not see move: of the chain from `Map` to
/// `Slot`, `Slot ::= Mid` is program syntax, which the module imports, and `Mid ::= Map` is not.
#[test]
fn a_subsort_sentence_the_configuration_module_sees_stays() {
    let (configuration, board) = placed(
        LIB,
        &format!(
            r"
k::sorts! {{
    Slot;
    Mid;
    impl Slot for Mid;
    impl Mid for Map;
}}
{BOOT}"
        ),
        "Slot",
        "Boot()",
    );
    assert_eq!(configuration, [BOOT_K, "syntax Mid ::= Map"]);
    assert_eq!(board, [] as [&str; 0]);
}

/// A subsort sentence the configuration's typing does not read stays in the module of its
/// package, as it does in a definition whose configuration has no module of its own: the cell of
/// sort `Slot` starts from a constructor of `Slot`.
#[test]
fn a_subsort_sentence_the_configuration_does_not_read_stays() {
    let (configuration, board) = placed(
        LIB,
        &format!(
            r#"
k::sorts! {{
    Slot;
    impl Slot for Map;
}}

#[k::constructors(sort = Slot, result = KResult)]
pub enum Slots {{
    #[k::syntax("empty")]
    Empty(),
}}
{BOOT}"#
        ),
        "Slot",
        "Slots::Empty()",
    );
    assert_eq!(configuration, [] as [&str; 0]);
    assert_eq!(board, [BOOT_K, "syntax Slot ::= Map"]);
}

/// An argument is typed as a cell's content is: `Pack` takes a `Slot` and the initializer gives
/// it a `Set`.
#[test]
fn an_argument_reads_the_subsort_order() {
    let (configuration, board) = placed(
        LIB,
        r"
use k::builtin::Set;

k::sorts! {
    Slot;
    Packed;
    impl Slot for Set;
}

#[k::function(partial, internal)]
pub fn Pack(slot: Term<Slot>) -> Term<Packed>;

#[k::function(total, internal)]
pub fn Seen() -> Term<Set<Int>> {
    k::set![1, 2]
}
",
        "Packed",
        "Pack(Seen())",
    );
    assert_eq!(
        configuration,
        [
            r#"syntax Packed ::= "pack" "(" Slot ")" [symbol(pack), function]"#,
            r#"syntax Set ::= "seen" "(" ")" [symbol(seen), function, total]"#,
            "syntax Slot ::= Set",
        ]
    );
    assert_eq!(board, [] as [&str; 0]);
}

/// A subsort into a framework sort is not program syntax either: a cell of sort `KResult`
/// starts from a `Val`.
#[test]
fn a_subsort_into_a_framework_sort_is_held() {
    let (configuration, board) = placed(
        LIB,
        r"
k::sorts! {
    Val: KResult;
}

#[k::function(partial, internal)]
pub fn Unit() -> Term<Val>;
",
        "KResult",
        "Unit()",
    );
    assert_eq!(
        configuration,
        [
            r#"syntax Val ::= "unit" "(" ")" [symbol(unit), function]"#,
            "syntax KResult ::= Val",
        ]
    );
    assert_eq!(board, [] as [&str; 0]);
}

/// The subsort sentence may be the group's package's: its module is above the configuration
/// too, and imports the configuration module.
#[test]
fn a_subsort_sentence_of_the_groups_package_is_held() {
    let lib = format!(
        "{LIB}
k::sorts! {{
    Slot;
    impl Slot for k::builtin::Map;
}}
"
    );
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = workspace_of(temporary.path(), &lib, &holder(BOOT, "lib::Slot", "Boot()"));
    let definition = emitted(
        target.path(),
        &manifest,
        "board",
        &["lib"],
        &temporary.path().join("emitted"),
    );
    let syntax = |name: &str| {
        declarations(&definition, name)
            .into_iter()
            .filter(|line| line.starts_with("syntax "))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        syntax("ORG-BOARD-CONFIGURATION"),
        [BOOT_K, "syntax Slot ::= Map"]
    );
    assert_eq!(syntax("ORG-LIB"), [] as [&str; 0]);
    assert!(
        declarations(&definition, "ORG-LIB")
            .contains(&"imports ORG-BOARD-CONFIGURATION".to_owned()),
        "{definition}"
    );
}
