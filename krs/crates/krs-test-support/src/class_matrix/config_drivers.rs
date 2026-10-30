//! K7's drivers for the configuration families on the run base ([`super::Base::Run`]): for each
//! readable record and `cells!` rule, the program that applies the case's sentence, and the cells
//! the run must end with ([`super::k7`]).
//!
//! What a spelling matches or writes in its cell is stated here from what it denotes there, never
//! from what KRS emits or runs:
//!
//! - **Subject:** the rule `{ k: [C(), ..], CELL: S } => { k: [..] }` applies where the cell holds
//!   a *witness* of `S`, a value it matches, and must not apply where the cell holds a
//!   *counter-witness*, a value it does not match. The program writes the witness into the cell
//!   with the base's driver commands, one step each, and then applies the case's command,
//!   `then(setpc(0), cNAME)`, three steps that leave the computation cell empty; where the start
//!   configuration holds a witness already (a binder and `_` match every value, and the
//!   collections start with no instance), it is the command alone. The counter run writes the
//!   counter-witness and must stop before the command applies.
//! - **Result:** the rule `{ k: [C(x, y), ..], CELL: OLD } => { k: [..], CELL: S }` writes `S`'s
//!   value with the command's binders at `x` = 1 and `y` = 2 (`y` = 1 for a map whose two keys may
//!   be equal, so that its later entry's value is the map's). The program first writes a value
//!   `OLD` matches and `S` does not (5, `[5]`, `{5 ↦ 5}`, the jobs 5 and 6, the object 5), so the
//!   value the run ends with is the result's, not the start's.
//! - **The computation cell:** its subject case holds no command (`{ k: S, pc: _ } => { pc: 1 }`),
//!   so its program is the witness itself (`go` is a computation with one item, `skip` leaves the
//!   empty one) and the run ends with `pc` = 1; its result case writes the computation after
//!   `then(cNAME(1, 2), go)`, whose `go` is the rest a readable `..` keeps.
//!
//! A spelling written in another kind's notation than its cell's (`Some(x)` on a leaf, brackets on
//! a map) denotes nothing there, and a spelling with no witness, value or counter-witness says why;
//! `cargo test -p krs-test-support --test k7` pins the reasons and their counts.

use super::k7::{Ground, K7, Run, SkipKind, Status};
use super::{CellKind, Command, Side};

/// A spelling written in another kind's notation than its cell's.
const NOTATION: &str =
    "the spelling is no notation of its cell's kind, so it denotes nothing there";
/// A binder of the cell's whole content.
const BINDER: &str = "a binder matches every value of the cell";
/// `_` as the cell's content.
const WILDCARD: &str = "`_` matches every value of the cell";
/// A group record whose child is a binder.
const RECORD: &str = "a group record whose every child is a binder matches every group";
/// A list or a map that is all `..`.
const REST: &str = "`..` alone matches every value of the cell";
/// A cell record as an item of the computation or of a list.
const CELL_ITEM: &str = "a cell record as an item, which no program writes";
/// `_` in a result.
const WILDCARD_RESULT: &str = "`_` builds no value";
/// The binder `x`, an `Int`, as a cell's content of another sort.
const BINDER_SORT: &str = "x = 1 is no value of the cell's sort";
/// `..` in a result whose subject reads the cell whole.
const RESULT_REST: &str = "`..` in a result is the rest a `..` of the subject's entry matched, and the subject's `old` matches the cell whole";
/// A result's instance list whose shape is not the subject's.
const RESULT_LINE_UP: &str =
    "the result's instance list does not line up with the subject's, which reads the front one";
/// An anonymous `..` in a map literal.
const ANONYMOUS_REST: &str = "a map literal's rest is the map its entries are written over, and an anonymous `..` names none";

/// What K7 runs a case on: its plan, and its counter run or why it has none.
pub(super) struct Plans {
    pub(super) k7: K7,
    pub(super) counter: Result<Run, &'static str>,
}

/// Why a case K7 does not run has no counter run.
const NOT_RUN: &str = "K7 does not run the case";
/// Why a result case has no counter run.
const BUILT: &str = "a result builds its value: no value of the cell is one it does not match";

/// A program that sets cells up, and the rewrite steps it takes.
#[derive(Clone, Debug)]
struct Setup {
    program: Ground,
    steps: u64,
}

impl Setup {
    /// The command `name` applied to `fields`, which takes one step.
    fn command(name: &str, fields: Vec<Ground>) -> Self {
        Self {
            program: Ground::ctor(&format!("Cmd::{name}"), fields),
            steps: 1,
        }
    }

    /// `then(self, next)`: one step that puts both in the computation cell, then each.
    fn then(self, next: Self) -> Self {
        Self {
            steps: 1 + self.steps + next.steps,
            program: Ground::ctor("Cmd::Then", vec![self.program, next.program]),
        }
    }

    /// The program's text in the run base's program grammar.
    fn text(&self) -> String {
        self.program
            .program()
            .expect("a driver writes only terms the program grammar or a maker writes")
    }
}

fn int(value: i64) -> Ground {
    Ground::Int(value)
}

/// `go`, a computation with one item, on which no sentence of the base applies.
fn go() -> Setup {
    Setup {
        program: Ground::ctor("Cmd::Go", Vec::new()),
        steps: 0,
    }
}

/// `skip`, which leaves the computation cell empty.
fn skip() -> Setup {
    Setup::command("Skip", Vec::new())
}

fn set_pc(value: i64) -> Setup {
    Setup::command("SetPc", vec![int(value)])
}

fn set_stack(items: &[i64]) -> Setup {
    Setup::command(
        "SetStack",
        vec![Ground::List(items.iter().copied().map(int).collect())],
    )
}

fn map(entries: &[(i64, i64)]) -> Ground {
    Ground::map(
        entries
            .iter()
            .map(|(key, value)| (int(*key), int(*value)))
            .collect(),
    )
}

fn set_env(entries: &[(i64, i64)]) -> Setup {
    Setup::command("SetEnv", vec![map(entries)])
}

fn set_ret(value: i64) -> Setup {
    Setup::command("SetRet", vec![int(value)])
}

/// The optional cell present, holding `value`, whether the state held it or not.
fn set_counter(value: i64) -> Setup {
    Setup::command("SetCounter", vec![int(value)])
}

/// The optional cell absent: created, then removed, whether the state held it or not.
fn absent() -> Setup {
    set_counter(0).then(Setup::command("DropCounter", Vec::new()))
}

/// An instance of the List collection `job` at its front.
fn add_job(payload: i64) -> Setup {
    Setup::command("AddJob", vec![int(payload)])
}

/// An instance of the Set collection `bag`.
fn add_obj(key: i64, entries: &[(i64, i64)]) -> Setup {
    Setup::command("AddObj", vec![int(key), map(entries)])
}

/// An instance of `job` as a run reads it.
fn job(payload: i64) -> Ground {
    Ground::ctor("job", vec![int(payload)])
}

/// An instance of `bag` as a run reads it.
fn obj(key: i64, entries: &[(i64, i64)]) -> Ground {
    Ground::ctor("bag", vec![int(key), map(entries)])
}

impl Plans {
    /// A case K7 does not run, for want of `kind`.
    fn skip(kind: SkipKind, reason: &'static str) -> Self {
        Self {
            k7: K7::skip(kind, reason),
            counter: Err(NOT_RUN),
        }
    }
}

/// What a subject spelling matches in its cell.
struct Matched {
    /// The setup that writes a witness, or `None` where the start configuration holds one.
    witness: Option<Setup>,
    /// The setup that writes a counter-witness, `None` for the start configuration, or why no
    /// value of the cell is one.
    counter: Result<Option<Setup>, &'static str>,
}

impl Matched {
    /// A spelling that matches every value of its cell: the start configuration is a witness.
    const fn every(reason: &'static str) -> Self {
        Self {
            witness: None,
            counter: Err(reason),
        }
    }

    /// A spelling that matches what `witness` writes and not what `counter` writes.
    const fn between(witness: Setup, counter: Setup) -> Self {
        Self {
            witness: Some(witness),
            counter: Ok(Some(counter)),
        }
    }
}

/// What a computation-cell spelling matches: the program that is a witness, and the one that is
/// a counter-witness, or why there is none.
struct Computation {
    witness: Setup,
    counter: Result<Setup, &'static str>,
}

/// What a result spelling writes: the cell's value after the step, and the value of `y`.
struct Written {
    value: Ground,
    y: i64,
}

impl Written {
    const fn value(value: Ground) -> Self {
        Self { value, y: 2 }
    }
}

/// The cell a run reads for each kind (`k7::Run::cells`).
const fn path(kind: CellKind) -> &'static str {
    match kind {
        CellKind::KSequence => "k",
        CellKind::Leaf => "pc",
        CellKind::List => "stack",
        CellKind::Map => "env",
        CellKind::Group => "frame.ret",
        CellKind::Optional => "counter",
        CellKind::Collection => "queue.job[payload]",
        CellKind::SetCollection => "shelf.bag{key,m}",
    }
}

/// What a result case's program writes first: a value its subject's `OLD` matches and no result
/// spelling writes (for the collections, two jobs, 5 at the front, and the object 5).
fn old(kind: CellKind) -> Setup {
    match kind {
        CellKind::KSequence => unreachable!("the computation cell's result case has its own plan"),
        CellKind::Leaf => set_pc(5),
        CellKind::List => set_stack(&[5]),
        CellKind::Map => set_env(&[(5, 5)]),
        CellKind::Group => set_ret(5),
        CellKind::Optional => set_counter(5),
        CellKind::Collection => add_job(6).then(add_job(5)),
        CellKind::SetCollection => add_obj(5, &[(5, 5)]),
    }
}

/// K7's plan and counter plan for a readable record writing `spelling` into `kind`'s cell on
/// `side`, whose command is `command` (none for the computation cell's subject).
pub(super) fn readable(
    kind: CellKind,
    side: Side,
    spelling: &str,
    command: Option<&Command>,
) -> Plans {
    match (kind, side, command) {
        (CellKind::KSequence, Side::Subject, _) => {
            computation_subject(readable_computation(spelling))
        }
        (CellKind::KSequence, _, Some(command)) => {
            // `{ k: [C(x, y), ..] } => { k: S }` after `then(cNAME(1, 2), go)`.
            let apply = apply(command, 2).then(go());
            computation_result(&apply, readable_written(kind, spelling))
        }
        (_, Side::Subject, Some(command)) => subject(readable_matched(kind, spelling), command),
        (_, _, Some(command)) => result(kind, readable_written(kind, spelling), command),
        (_, _, None) => unreachable!("only the computation cell's subject has no command"),
    }
}

/// K7's plan and counter plan for a `cells!` rule writing `spelling` into `kind`'s cell on
/// `side`, as [`readable`].
pub(super) fn cells(
    kind: CellKind,
    side: Side,
    spelling: &str,
    command: Option<&Command>,
) -> Plans {
    match (kind, side, command) {
        (CellKind::KSequence, Side::Subject, _) => computation_subject(cells_computation(spelling)),
        // `k: KCell(C(x, y))`, the whole cell, rewritten to `k: S`: the program is the command.
        (CellKind::KSequence, _, Some(command)) => {
            computation_result(&apply(command, 2), cells_written(kind, spelling))
        }
        (_, Side::Subject, Some(command)) => subject(cells_matched(kind, spelling), command),
        (_, _, Some(command)) => result(kind, cells_written(kind, spelling), command),
        (_, _, None) => unreachable!("only the computation cell's subject has no command"),
    }
}

/// The case's command applied to `x` = 1 and `y`.
fn apply(command: &Command, y: i64) -> Setup {
    Setup::command(&command.name, vec![int(1), int(y)])
}

/// The plan of a subject case: the witness written, then the command; the counter run on the
/// counter-witness, which must stop before the command applies.
fn subject(matched: Result<Matched, &'static str>, command: &Command) -> Plans {
    let matched = match matched {
        Ok(matched) => matched,
        Err(reason) => return Plans::skip(SkipKind::Witness, reason),
    };
    let apply = || Setup::command(&command.name, Vec::new());
    let then_apply = |setup: Option<Setup>| match setup {
        Some(setup) => setup.then(apply()),
        None => apply(),
    };
    let witness = then_apply(matched.witness);
    let plan = K7::Run(Run {
        program: witness.text(),
        variables: Vec::new(),
        depth: witness.steps,
        steps: witness.steps,
        cells: vec![("k".to_owned(), Ground::Seq(Vec::new()))],
        status: Status::Liveness,
    });
    let counter = matched.counter.map(|setup| {
        let counter = then_apply(setup);
        Run {
            program: counter.text(),
            variables: Vec::new(),
            depth: counter.steps,
            steps: counter.steps - 1,
            cells: Vec::new(),
            status: Status::Liveness,
        }
    });
    Plans { k7: plan, counter }
}

/// The plan of the computation cell's subject case, `{ k: S, pc: _ } => { pc: 1 }`: the witness
/// program, then the case's step; the counter program, which must take its own steps only.
fn computation_subject(computation: Result<Computation, &'static str>) -> Plans {
    let computation = match computation {
        Ok(computation) => computation,
        Err(reason) => return Plans::skip(SkipKind::Witness, reason),
    };
    let steps = computation.witness.steps + 1;
    let plan = K7::Run(Run {
        program: computation.witness.text(),
        variables: Vec::new(),
        depth: steps,
        steps,
        cells: vec![("pc".to_owned(), int(1))],
        status: Status::Liveness,
    });
    let counter = computation.counter.map(|counter| Run {
        program: counter.text(),
        variables: Vec::new(),
        depth: counter.steps + 1,
        steps: counter.steps,
        cells: Vec::new(),
        status: Status::Liveness,
    });
    Plans { k7: plan, counter }
}

/// The plan of a result case: the subject's old value written, then the command, and the cell
/// holds the written value.
fn result(kind: CellKind, written: Result<Written, &'static str>, command: &Command) -> Plans {
    let written = match written {
        Ok(written) => written,
        Err(reason) => return Plans::skip(SkipKind::Value, reason),
    };
    let program = old(kind).then(apply(command, written.y));
    let plan = K7::Run(Run {
        program: program.text(),
        variables: Vec::new(),
        depth: program.steps,
        steps: program.steps,
        cells: vec![
            ("k".to_owned(), Ground::Seq(Vec::new())),
            (path(kind).to_owned(), written.value.clone()),
        ],
        status: status(&written.value),
    });
    Plans {
        k7: plan,
        counter: Err(BUILT),
    }
}

/// The plan of the computation cell's result case: `program`, whose last step is the case's, and
/// the computation it writes.
fn computation_result(program: &Setup, written: Result<Written, &'static str>) -> Plans {
    let written = match written {
        Ok(written) => written,
        Err(reason) => return Plans::skip(SkipKind::Value, reason),
    };
    let plan = K7::Run(Run {
        program: program.text(),
        variables: Vec::new(),
        depth: program.steps,
        steps: program.steps,
        cells: vec![("k".to_owned(), written.value.clone())],
        status: status(&written.value),
    });
    Plans {
        k7: plan,
        counter: Err(BUILT),
    }
}

/// A value checks the value, unless it holds a term the generator does not state.
fn status(value: &Ground) -> Status {
    if holds_any(value) {
        Status::Liveness
    } else {
        Status::Value
    }
}

fn holds_any(term: &Ground) -> bool {
    match term {
        Ground::Any => true,
        Ground::Ctor { fields: terms, .. }
        | Ground::Unevaluated {
            arguments: terms, ..
        }
        | Ground::List(terms)
        | Ground::Set(terms)
        | Ground::Seq(terms) => terms.iter().any(holds_any),
        Ground::Map(entries) => entries
            .iter()
            .any(|(key, value)| holds_any(key) || holds_any(value)),
        _ => false,
    }
}

/// What a readable spelling matches in the computation cell.
fn readable_computation(spelling: &str) -> Result<Computation, &'static str> {
    match spelling {
        "[..]" => Ok(Computation {
            witness: go(),
            counter: Err(REST),
        }),
        "[]" => Ok(Computation {
            witness: skip(),
            counter: Ok(go()),
        }),
        "[x, ..]" => Ok(Computation {
            witness: go(),
            counter: Ok(skip()),
        }),
        "[Job { payload: x, .. }, ..]" | "[.., Job { payload: 0, .. }]" => Err(CELL_ITEM),
        _ => Err(NOTATION),
    }
}

/// What a `cells!` spelling matches in the computation cell.
fn cells_computation(spelling: &str) -> Result<Computation, &'static str> {
    match spelling {
        "k::configuration::KCell(x, ..)" => Ok(Computation {
            witness: go(),
            counter: Ok(skip()),
        }),
        "k::configuration::KCell()" => Ok(Computation {
            witness: skip(),
            counter: Ok(go()),
        }),
        _ => Err(NOTATION),
    }
}

/// What a readable subject spelling matches in `kind`'s cell.
fn readable_matched(kind: CellKind, spelling: &str) -> Result<Matched, &'static str> {
    use CellKind::{Collection, Group, Leaf, List, Map, Optional, SetCollection};
    Ok(match (kind, spelling) {
        (Leaf | List | Map | Group, "x") => Matched::every(BINDER),
        (Leaf | List | Map | Group, "_") => Matched::every(WILDCARD),
        (Leaf, "0") => Matched::between(set_pc(0), set_pc(1)),
        (List, "[..]") => Matched {
            witness: Some(set_stack(&[0])),
            counter: Err(REST),
        },
        (List, "[]") => Matched::between(set_stack(&[]), set_stack(&[0])),
        (List, "[x, ..]") => Matched::between(set_stack(&[0]), set_stack(&[])),
        (List, "[Job { payload: x, .. }, ..]" | "[.., Job { payload: 0, .. }]") => {
            return Err(CELL_ITEM);
        }
        (Map, "{ .. }") => Matched {
            witness: Some(set_env(&[(1, 0)])),
            counter: Err(REST),
        },
        (Map, "{ y -> x, .. }") => Matched::between(set_env(&[(1, 0)]), set_env(&[])),
        (Group, "Frame { ret: x }") => Matched::every(RECORD),
        (Optional, "Some(x)") => Matched::between(set_counter(0), absent()),
        (Optional, "None") => Matched::between(absent(), set_counter(0)),
        (Collection, "[..]") => Matched {
            witness: Some(add_job(0)),
            counter: Err(REST),
        },
        // The collection starts with no instance.
        (Collection, "[]") => Matched {
            witness: None,
            counter: Ok(Some(add_job(0))),
        },
        (Collection, "[Job { payload: x, .. }, ..]") => Matched {
            witness: Some(add_job(0)),
            counter: Ok(None),
        },
        (Collection, "[.., Job { payload: 0, .. }]") => Matched::between(add_job(0), add_job(1)),
        (SetCollection, _) => return bag_matched(spelling),
        _ => return Err(NOTATION),
    })
}

/// What a `cells!` subject spelling matches in `kind`'s cell.
fn cells_matched(kind: CellKind, spelling: &str) -> Result<Matched, &'static str> {
    use CellKind::{Collection, Group, Leaf, List, Map, Optional, SetCollection};
    Ok(match (kind, spelling) {
        (Leaf | List | Map, "k::configuration::Cell(x)") | (Group, "x") => Matched::every(BINDER),
        (Leaf | List | Map, "k::configuration::Cell(_)") | (Group, "_") => Matched::every(WILDCARD),
        (Leaf, "k::configuration::Cell(0)") => Matched::between(set_pc(0), set_pc(1)),
        (List, "k::configuration::Cell([x, ..])") => {
            Matched::between(set_stack(&[0]), set_stack(&[]))
        }
        (Map, "k::configuration::Cell(k::map![y -> x, ..])") => {
            Matched::between(set_env(&[(1, 0)]), set_env(&[]))
        }
        (Group, "k::fragment![crate::Frame { ret: x }]") => Matched::every(RECORD),
        (Optional, "Some(k::configuration::Cell(x))") => Matched::between(set_counter(0), absent()),
        (Optional, "None") => Matched::between(absent(), set_counter(0)),
        // The collection starts with no instance.
        (Collection, "[k::fragment![crate::Job { payload: x, .. }], instances0 @ ..]") => Matched {
            witness: Some(add_job(0)),
            counter: Ok(None),
        },
        (SetCollection, _) => return bag_matched(spelling),
        _ => return Err(NOTATION),
    })
}

/// What a Set collection's subject spelling matches, in either family: an instance written whole
/// is looked up, so its witness is the object it denotes, and an object whose map has one more
/// entry, or another key or value, is no witness; an instance whose map writes `..` selects the
/// objects whose map holds the written entry, so one with another entry beside it is a witness.
fn bag_matched(spelling: &str) -> Result<Matched, &'static str> {
    let exact = add_obj(1, &[(1, 2)]);
    Ok(match spelling {
        // An exact map is part of the instance's value, its key computed or not: a map with another
        // entry beside it is another value.
        "{ Obj { key: 1, m: map![1 -> 2] }, .. }"
        | "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> 2] }], instances0 @ .. }"
        | "{ Obj { key: 1, m: map![k::builtin::int::add(0, 1) -> 2] }, .. }"
        | "{ k::fragment![crate::Obj { key: 1, m: k::map![k::builtin::int::add(0, 1) -> 2] }], instances0 @ .. }" => {
            Matched::between(exact, add_obj(1, &[(1, 2), (3, 4)]))
        }
        "{ Obj { key: k::builtin::int::add(0, 1), m: map![1 -> 2] }, .. }"
        | "{ k::fragment![crate::Obj { key: k::builtin::int::add(0, 1), m: k::map![1 -> 2] }], instances0 @ .. }" => {
            Matched::between(exact, add_obj(2, &[(1, 2)]))
        }
        "{ Obj { key: 1, m: map![1 -> k::builtin::int::add(1, 1)] }, .. }"
        | "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> k::builtin::int::add(1, 1)] }], instances0 @ .. }" => {
            Matched::between(exact, add_obj(1, &[(1, 3)]))
        }
        "{ Obj { key: 1, m: { 1 -> 2, .. } }, .. }"
        | "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> 2, ..] }], instances0 @ .. }" => {
            Matched::between(add_obj(1, &[(1, 2), (3, 4)]), add_obj(1, &[(1, 3)]))
        }
        // In a readable record, `map![..]` is a literal.
        "{ Obj { key: 1, m: map![1 -> 2, ..] }, .. }" => return Err(ANONYMOUS_REST),
        _ => return Err(NOTATION),
    })
}

/// What a readable result spelling writes into `kind`'s cell, with `x` = 1 and `y` = 2.
fn readable_written(kind: CellKind, spelling: &str) -> Result<Written, &'static str> {
    use CellKind::{Collection, Group, KSequence, Leaf, List, Map, Optional, SetCollection};
    let rest = || go().program;
    Ok(Written::value(match (kind, spelling) {
        (_, "_") => return Err(WILDCARD_RESULT),
        // After `then(cNAME(1, 2), go)`: `..` is the rest, `go`.
        (KSequence, "[..]") => Ground::Seq(vec![rest()]),
        (KSequence, "[]") => Ground::Seq(Vec::new()),
        (KSequence, "[x, ..]") => Ground::Seq(vec![int(1), rest()]),
        // A `Job` cell as an item, which the generator states no ground form of.
        (KSequence, "[Job { payload: x, .. }, ..]") => Ground::Seq(vec![Ground::Any, rest()]),
        (KSequence, "[.., Job { payload: 0, .. }]") => Ground::Seq(vec![rest(), Ground::Any]),
        (Leaf, "x") | (Group, "Frame { ret: x }") | (Optional, "Some(x)") => int(1),
        (Leaf, "0") => int(0),
        (List | Map | Group, "x") => return Err(BINDER_SORT),
        (List | Collection, "[]") => Ground::List(Vec::new()),
        (
            List,
            "[..]" | "[x, ..]" | "[Job { payload: x, .. }, ..]" | "[.., Job { payload: 0, .. }]",
        )
        | (Map, "{ .. }" | "{ y -> x, .. }") => return Err(RESULT_REST),
        (Optional, "None") => Ground::Absent,
        // Over the subject's `[Job { payload: _, .. }, ..]`, the jobs 5 and 6: the front one is
        // written, the rest kept.
        (Collection, "[Job { payload: x, .. }, ..]") => Ground::List(vec![job(1), job(6)]),
        (Collection, "[..]") => Ground::List(vec![job(6)]),
        (Collection, "[.., Job { payload: 0, .. }]") => return Err(RESULT_LINE_UP),
        (SetCollection, _) => return bag_written(spelling),
        _ => return Err(NOTATION),
    }))
}

/// What a `cells!` result spelling writes into `kind`'s cell, with `x` = 1 and `y` = 2.
fn cells_written(kind: CellKind, spelling: &str) -> Result<Written, &'static str> {
    use CellKind::{Collection, Group, KSequence, Leaf, List, Map, Optional, SetCollection};
    Ok(match (kind, spelling) {
        (KSequence, "k::configuration::KCell(x)") => Written::value(Ground::Seq(vec![int(1)])),
        (KSequence, "k::configuration::KCell()") => Written::value(Ground::Seq(Vec::new())),
        (Leaf, "k::configuration::Cell(x)")
        | (Group, "k::fragment![crate::Frame { ret: x }]")
        | (Optional, "Some(k::configuration::Cell(x))") => Written::value(int(1)),
        (Leaf, "k::configuration::Cell(0)") => Written::value(int(0)),
        (List | Map, "k::configuration::Cell(x)") | (Group, "x") => return Err(BINDER_SORT),
        (List, "k::configuration::Cell([x, y])") => {
            Written::value(Ground::List(vec![int(1), int(2)]))
        }
        (Map, "k::configuration::Cell(k::map![x -> y])") => Written::value(map(&[(1, 2)])),
        // Two entries whose keys are equal at `x` = `y` = 1: the later one's value is the map's.
        (
            Map,
            "k::configuration::Cell(k::map![x -> 1, y -> 2])"
            | "k::configuration::Cell(k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), x, 1), y, 2))",
        ) => Written {
            value: map(&[(1, 2)]),
            y: 1,
        },
        (Optional, "None") => Written::value(Ground::Absent),
        // Over the subject's front job `old`, 5, beside 6: `..old` keeps its other cells and
        // `..instances0` the other jobs.
        (Collection, "[k::fragment![crate::Job { payload: x, ..old }], ..instances0]") => {
            Written::value(Ground::List(vec![job(1), job(6)]))
        }
        (SetCollection, _) => bag_written(spelling)?,
        _ => return Err(NOTATION),
    })
}

/// What a Set collection's result spelling writes, in either family: the object it denotes,
/// beside the subject's object 5.
fn bag_written(spelling: &str) -> Result<Written, &'static str> {
    let beside = |object: Ground| Written::value(Ground::set(vec![obj(5, &[(5, 5)]), object]));
    Ok(match spelling {
        "{ Obj { key: x, m: map![x -> y] }, .. }"
        | "{ k::fragment![crate::Obj { key: x, m: k::map![x -> y] }], ..instances0 }" => {
            beside(obj(1, &[(1, 2)]))
        }
        "{ Obj { key: k::builtin::int::add(x, 1), m: map![x -> y] }, .. }"
        | "{ k::fragment![crate::Obj { key: k::builtin::int::add(x, 1), m: k::map![x -> y] }], ..instances0 }" => {
            beside(obj(2, &[(1, 2)]))
        }
        "{ Obj { key: x, m: map![x -> k::builtin::int::add(y, 1)] }, .. }"
        | "{ k::fragment![crate::Obj { key: x, m: k::map![x -> k::builtin::int::add(y, 1)] }], ..instances0 }" => {
            beside(obj(1, &[(1, 3)]))
        }
        "{ Obj { key: x, m: map![k::builtin::int::add(x, 1) -> y] }, .. }"
        | "{ k::fragment![crate::Obj { key: x, m: k::map![k::builtin::int::add(x, 1) -> y] }], ..instances0 }" => {
            beside(obj(1, &[(2, 2)]))
        }
        "{ Obj { key: x, m: map![x -> y, ..] }, .. }"
        | "{ k::fragment![crate::Obj { key: x, m: k::map![x -> y, ..] }], ..instances0 }" => {
            return Err(ANONYMOUS_REST);
        }
        _ => return Err(NOTATION),
    })
}
