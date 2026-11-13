//! The lints on declared ends (END-CLASSES-lints): `krs check` warns where an end is shown to
//! hold at a state where a rule applies (`krs::analysis::end-not-terminal`), where two ends of
//! different classes are shown to hold at one state (`krs::analysis::end-classes-overlap`), and
//! where a rule that goes after the others makes a `refused` end of every head no other rule
//! takes (`krs::analysis::end-catch-all`). Each is a warning: the definition is accepted. A pair
//! whose two sides both have a condition is not judged, so an end separated from a rule by its
//! condition is silent.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// The machine both definitions share: a computation, an accumulator, a timer and a memory.
/// `{ops}` are the variants of `Op`, `{items}` the ends and the rules.
const MACHINE: &str = r#"
use k::Term;
use k::builtin::{Int, KSequence, Map, int, map};
use k::configuration::{Cell, KCell};

k::sorts! {
    Instr;
    Ext;
    Fault;
}

#[k::constructors(sort = Instr, result = KResult)]
#[rustfmt::skip]
pub enum Op {
{ops}
}

#[k::constructors(sort = Ext, result = KResult)]
#[rustfmt::skip]
pub enum Call {
    #[k::syntax("ping")] Ping(),
    #[k::syntax("pong")] Pong(),
}

#[k::constructors(sort = Fault, result = KResult, internal)]
#[rustfmt::skip]
pub enum FaultOp {
    /// A call the machine does not know.
    #[k::end(refused)]
    #[k::syntax("unknown ( {call} )")] Unknown { call: Ext },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
    #[k::cell]
    pub timer: Int,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Instr) -> Self {
        Self {
            k: k::k![pgm],
            acc: 0,
            timer: 0,
            mem: k::map![7 -> 2],
        }
    }
}

{items}
"#;

/// Every finding the lints make.
const SHOWN_OPS: &str = r#"
    /// The shorthand on a constructor a rule takes: the end holds where `answer` applies.
    #[k::end(refused)]
    #[k::syntax("read ( {addr} )")] Read { addr: Int },
    #[k::end(finished)]
    #[k::syntax("halt")] Halt(),
    #[k::syntax("spin")] Spin(),
    #[k::syntax("wait")] Wait(),
"#;

const SHOWN: &str = r"
/// Covered by the rule `spin`, which has no condition: a rule applies wherever this holds.
#[k::end(finished)]
#[k::requires(int::le(3, acc))]
fn spun(
    acc: Term<Int>,
    k::cells! { k: KCell(Op::Spin(), ..), acc: Cell(acc), .. }: Machine,
) {
}

/// Meets the rule `wake`: neither has a condition, and neither covers the other.
#[k::end(finished)]
fn waiting(k::cells! { k: KCell(Op::Wait(), ..), acc: Cell(0), .. }: Machine) {}

/// A `refused` end inside the `finished` end the constructor `Halt` declares.
#[k::end(refused)]
#[k::requires(int::le(3, acc))]
fn hot_halt(
    acc: Term<Int>,
    k::cells! { k: KCell(Op::Halt(), ..), acc: Cell(acc), .. }: Machine,
) -> Term<Int> {
    acc
}

k::rules! {
    for Machine;
    use Call::*;
    use FaultOp::*;
    use Op::*;

    /// Answers a read below 8, and no other.
    #[k::requires(int::lt(addr, 8))]
    answer: {
        k: [Read { addr }, ..],
        acc: _,
    } => {
        k: [..],
        acc: addr,
    };

    spin: {
        k: [Spin(), ..],
        acc,
    } => {
        k: [Spin(), ..],
        acc: int::add(acc, 1),
    };

    wake: {
        k: [Wait(), ..],
        timer: 1,
    } => {
        k: [..],
        timer: 0,
    };

    pong: {
        k: [Pong(), ..],
    } => {
        k: [..],
    };

    /// Whatever call no rule answers is unknown, a forgotten one included.
    #[k::rule(owise)]
    other: {
        k: [call, ..],
    } => {
        k: [Unknown { call }, ..],
    };
}
";

/// Ends the lints say nothing of.
const SILENT_OPS: &str = r#"
    #[k::syntax("inc")] Inc(),
    #[k::syntax("read ( {addr} )")] Read { addr: Int },
    /// No rule takes it.
    #[k::end(finished)]
    #[k::syntax("halt")] Halt(),
    #[k::syntax("stop")] Stop(),
"#;

const SILENT: &str = r"
/// Separated from `inc` by its condition: `inc` applies below 3, this holds from 3 on.
#[k::end(refused)]
#[k::requires(int::le(3, acc))]
fn overflow(
    acc: Term<Int>,
    k::cells! { k: KCell(Op::Inc(), ..), acc: Cell(acc), .. }: Machine,
) -> Term<Int> {
    acc
}

/// Separated from `answer` by a condition over a function the lints do not read.
#[k::end(refused)]
#[k::requires(!map::in_keys(addr, mem))]
fn unmapped_read(
    addr: Term<Int>,
    mem: Term<Map>,
    k::cells! { k: KCell(Op::Read { addr }, ..), mem: Cell(mem), .. }: Machine,
) -> Term<Int> {
    addr
}

/// Beside `unstop`, whose left side reads a map: whether one state matches both is not read.
#[k::end(finished)]
fn stopped(k::cells! { k: KCell(Op::Stop(), ..), acc: Cell(0), .. }: Machine) {}

/// The computation is empty, where no rule's left side matches.
#[k::end(finished)]
fn drained(k::cells! { k: KCell(), .. }: Machine) {}

k::rules! {
    for Machine;
    use Call::*;
    use FaultOp::*;
    use Op::*;

    #[k::requires(int::lt(acc, 3))]
    inc: {
        k: [Inc(), ..],
        acc,
    } => {
        k: [..],
        acc: int::add(acc, 1),
    };

    answer: {
        k: [Read { addr }, ..],
        mem: { addr -> value, .. },
        acc: _,
    } => {
        k: [..],
        acc: value,
    };

    unstop: {
        k: [Stop(), ..],
        mem: { 0 -> _, .. },
    } => {
        k: [..],
    };

    /// A refusal of one call, stated: no other head becomes `unknown`.
    ping: {
        k: [Ping(), ..],
    } => {
        k: [Unknown { call: Ping() }, ..],
    };
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes the package `name` whose definition is [`MACHINE`] with `ops` and `items`.
fn package(root: &Path, name: &str, ops: &str, items: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/lib.rs"),
        MACHINE.replace("{ops}", ops).replace("{items}", items),
    )
    .unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"END-LINTS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// `krs check` of the package's `main` definition: whether it passed, and each diagnostic's
/// headline, the source line it points at, and its notes and help.
fn checked(target: &Path, manifest: &Path) -> (bool, Vec<String>) {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args(["check", "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    let mut lines = Vec::new();
    let mut pointed = false;
    for line in stderr.lines() {
        let trimmed = line.trim_start();
        if line.starts_with("error") || line.starts_with("warning") {
            lines.push(line.to_owned());
            pointed = true;
        } else if pointed
            && let Some((number, source)) = line.split_once(" | ")
            && number.trim().parse::<usize>().is_ok()
        {
            lines.push(format!("at `{}`", source.trim()));
            pointed = false;
        } else if trimmed.starts_with("= note:") || trimmed.starts_with("= help:") {
            lines.push(trimmed.to_owned());
        }
    }
    (output.status.success(), lines)
}

/// Each of the three lints, and each way an end is shown to hold where a rule applies: the
/// constructor's end a rule takes at the head (with the advice to declare it on a `fn`), the
/// end a rule without a condition covers, and the end that meets a rule. The definition is
/// accepted.
#[test]
fn an_end_shown_to_hold_where_a_rule_applies_or_beside_another_class_is_warned() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "shown", SHOWN_OPS, SHOWN);
    let (success, lines) = checked(target.path(), &manifest);
    assert!(success, "{lines:#?}");
    expect_test::expect![[r#"
        [
            "warning[krs::analysis::end-not-terminal]: the end `read` holds at every state the rule `answer` applies to: `read` has no condition, and its pattern matches every state the left side of `answer` matches. A rule applies at those states, so the run is not over there, and `read` is true at states that are not ends",
            "at `#[k::syntax(\"read ( {addr} )\")] Read { addr: Int },`",
            "= help: `read` is declared on a constructor, so it holds wherever the main computation cell starts with that constructor, whatever the other cells hold, and `answer` takes the constructor there. An end states where no rule applies: declare it with `#[k::end(refused)]` on a `fn` whose `k::cells!` pattern and `#[k::requires]` state the states `answer` leaves, in the package that holds `answer`",
            "warning[krs::analysis::end-not-terminal]: a rule applies at every state of the end `spun`: the rule `spin` has no condition, and its left side matches every state the pattern of `spun` matches, so `spin` or a rule that goes before it applies there. `spun` is true at no state where the run is over",
            "at `fn spun(`",
            "= help: narrow the pattern of `spun`, or give it a `#[k::requires]` that is false wherever `spin` applies",
            "warning[krs::analysis::end-not-terminal]: the end `waiting` holds at states where a rule applies: neither `waiting` nor the rule `wake` has a condition, and the pattern of `waiting` and the left side of `wake` both match every state with `k: [Op::Wait(), ..]`. `wake` or a rule that goes before it applies there, so the run is not over, and `waiting` is true at states that are not ends",
            "at `fn waiting(k::cells! { k: KCell(Op::Wait(), ..), acc: Cell(0), .. }: Machine) {}`",
            "= help: narrow the pattern of `waiting`, or give it a `#[k::requires]` that is false wherever `wake` applies",
            "warning[krs::analysis::end-classes-overlap]: the end `halt` (finished) holds at every state of the end `hot_halt` (refused): `halt` has no condition, and its pattern matches every state the pattern of `hot_halt` matches. A state where the run is over is in one class, and this one is in both, so the definition contradicts itself there",
            "at `#[k::syntax(\"halt\")] Halt(),`",
            "= help: state in each end's pattern or `#[k::requires]` what keeps its states out of the other",
            "warning[krs::analysis::end-catch-all]: the rule `other` makes a state of the refused end `unknown` out of every head of sort `Ext` no other rule takes: the head of its subject in the main computation cell is a binder of that sort, it is `owise`, so it applies where no other rule does, and the state it gives is in `unknown`. A head the definition has no rule for by omission is then refused like one it refuses on purpose, and no run ends at it outside the declared ends",
            "at `other: {`",
            "= help: a refusal is stated, not inferred from the absence of a rule: write a rule to `unknown` for each head that is refused, or declare the end on a `fn` whose `k::cells!` pattern names it, and leave the other heads without a rule, where a run ends at no declared end",
        ]
    "#]].assert_debug_eq(&lines);
}

/// No warning for an end a condition separates from the rule on the same head, for one whose
/// rule is separated by a condition the lints do not read, for a constructor no rule takes,
/// for an end beside a rule whose left side reads a map, or for a rule that states one refusal.
#[test]
fn an_end_not_shown_to_hold_where_a_rule_applies_is_silent() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "silent", SILENT_OPS, SILENT);
    let (success, lines) = checked(target.path(), &manifest);
    assert!(success, "{lines:#?}");
    assert_eq!(lines, Vec::<String>::new());
}
