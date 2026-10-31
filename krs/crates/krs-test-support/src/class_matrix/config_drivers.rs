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
//!   collections start with no instance), it is the command alone. Each counter run writes a
//!   counter-witness and must stop before the command applies.
//! - **Exact and open:** a spelling that reads a collection whole (`[]`, an instance whose map is
//!   `map![1 -> 2]`) has, among its counter-witnesses, the collection with one item more; one whose
//!   `..` leaves items open (`[x, ..]`, `{ y -> x, .. }`, `Obj { key: 1, .. }`) has a witness with
//!   an item more than it writes. So a lowering that reads an exact collection as open, or an open
//!   one as exact, does not apply as stated. Each subject plan states the collections it reads
//!   ([`Reading`]), and `cargo test -p krs-test-support --test k7` checks the rule on the programs.
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
/// A cell record behind the computation's first item.
const BACK_ITEM: &str = "a cell record behind the computation's first item, which no driver command writes: a driver command acts at the front of the computation";
/// A cell record as a List cell's element.
const LIST_RECORD: &str = "a cell record as a List cell's element, which no driver command writes: a readable result reads `[Job { .. }, ..]` on a List cell as a collection's instances, which it refuses, and no other spelling builds a cell record";
/// A leaf, which holds one value.
const LEAF: &str = "a leaf holds one value, no collection";
/// An optional cell, which holds one value or none.
const OPTIONAL: &str = "an optional cell holds one value or none, no collection";
/// A group record of the machine base's one-child group.
const ONE_CHILD: &str = "the group has one child, which the record names: no child is left over";
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

/// What K7 runs a case on: its plan, and its counter runs or why it has none.
pub(super) struct Plans {
    pub(super) k7: K7,
    pub(super) counters: Result<Vec<Run>, &'static str>,
}

/// A collection a subject spelling reads, whose items a driver's program writes.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Part {
    /// The computation's items.
    Computation,
    /// A List cell's elements.
    List,
    /// A Map cell's entries.
    Map,
    /// The List collection `job`'s instances.
    Jobs,
    /// The Set collection `bag`'s instances.
    Objects,
    /// The entries of the map cell of the `bag` instance the spelling reads.
    ObjectMap,
}

/// How a spelling reads a collection: all of it, with the items it writes, or those items and,
/// by `..`, any others.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Extent {
    /// Exactly this many items.
    Exact(usize),
    /// This many items written, others left open.
    Open(usize),
}

/// A collection a subject case's spelling reads, and how many items its witness and each of its
/// counter-witnesses write there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reading {
    /// The collection.
    pub part: Part,
    /// How the spelling reads it.
    pub extent: Extent,
    /// The items the witness writes.
    pub witness: usize,
    /// The items each counter-witness writes.
    pub counters: Vec<usize>,
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

/// A `Job` cell record as the computation's first item, before what follows `pushjob(a)`.
fn push_job(payload: i64) -> Setup {
    Setup::command("PushJob", vec![int(payload)])
}

/// The object a Set collection's witness and counter-witnesses hold beside the one they read: key
/// 9 and an empty map, which no spelling reads, so `{ .., .. }`'s `..` has an instance to leave.
fn other_obj() -> Setup {
    add_obj(9, &[])
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
            counters: Err(NOT_RUN),
        }
    }
}

/// What a subject spelling matches in its cell.
struct Matched {
    /// The setup that writes a witness, or `None` where the start configuration holds one.
    witness: Option<Setup>,
    /// The setups that write counter-witnesses, `None` for the start configuration, or why no
    /// value of the cell is one.
    counters: Result<Vec<Option<Setup>>, &'static str>,
    /// The collections the spelling reads, or why it reads none.
    reads: Result<Vec<(Part, Extent)>, &'static str>,
}

impl Matched {
    /// A spelling that matches every value of its cell: the start configuration is a witness.
    const fn every(reason: &'static str) -> Self {
        Self {
            witness: None,
            counters: Err(reason),
            reads: Err(reason),
        }
    }

    /// A spelling that matches what `witness` writes and none of what `counters` write.
    fn between(witness: Setup, counters: Vec<Setup>) -> Self {
        Self {
            witness: Some(witness),
            counters: Ok(counters.into_iter().map(Some).collect()),
            reads: Ok(Vec::new()),
        }
    }

    /// The spelling, which reads `part` with `extent`.
    fn reading(self, part: Part, extent: Extent) -> Self {
        let mut reads = self.reads.unwrap_or_default();
        reads.push((part, extent));
        Self {
            reads: Ok(reads),
            ..self
        }
    }

    /// The spelling, which reads no collection, for `reason`.
    fn reading_none(self, reason: &'static str) -> Self {
        Self {
            reads: Err(reason),
            ..self
        }
    }
}

/// What a computation-cell spelling matches: the program that is a witness, those that are
/// counter-witnesses or why there is none, and how it reads the computation's items.
struct Computation {
    witness: Setup,
    counters: Result<Vec<Setup>, &'static str>,
    extent: Extent,
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

/// The collections a run family's subject case reads, each with the items its witness and its
/// counter-witnesses write there (as [`Reading`]s), or why it reads none; `None` for a result case,
/// whose plan checks the value its sentence writes, and for a case K7 does not run.
pub(super) fn readings(
    readable: bool,
    kind: CellKind,
    side: Side,
    spelling: &str,
) -> Option<Result<Vec<Reading>, &'static str>> {
    if side != Side::Subject {
        return None;
    }
    if kind == CellKind::KSequence {
        let computation = if readable {
            readable_computation(spelling)
        } else {
            cells_computation(spelling)
        }
        .ok()?;
        let counters = computation.counters.unwrap_or_default();
        return Some(Ok(vec![Reading {
            part: Part::Computation,
            extent: computation.extent,
            witness: items(Part::Computation, Some(&computation.witness)),
            counters: counters
                .iter()
                .map(|counter| items(Part::Computation, Some(counter)))
                .collect(),
        }]));
    }
    let matched = if readable {
        readable_matched(kind, spelling)
    } else {
        cells_matched(kind, spelling)
    }
    .ok()?;
    let counters = matched.counters.unwrap_or_default();
    Some(matched.reads.map(|reads| {
        reads
            .into_iter()
            .map(|(part, extent)| Reading {
                part,
                extent,
                witness: items(part, matched.witness.as_ref()),
                counters: counters
                    .iter()
                    .map(|counter| items(part, counter.as_ref()))
                    .collect(),
            })
            .collect()
    }))
}

/// The commands `program` runs, in order: a `then`'s parts, flattened.
fn commands(program: &Ground) -> Vec<&Ground> {
    match program {
        Ground::Ctor { path, fields } if path == "Cmd::Then" => {
            fields.iter().flat_map(commands).collect()
        }
        other => vec![other],
    }
}

/// How many items of `part` the configuration holds after `setup` (the start's, none, where it is
/// `None`): the computation's items it leaves, a list's elements or a map's entries it writes last,
/// the instances it adds, and the entries of the last object's map.
fn items(part: Part, setup: Option<&Setup>) -> usize {
    let mut count = 0;
    for command in setup
        .map(|setup| commands(&setup.program))
        .unwrap_or_default()
    {
        let Ground::Ctor { path, fields } = command else {
            continue;
        };
        let written = |index: usize| match fields.get(index) {
            Some(Ground::List(items)) => items.len(),
            Some(Ground::Map(entries)) => entries.len(),
            _ => 0,
        };
        match (part, path.trim_start_matches("Cmd::")) {
            (Part::Computation, "Skip") => {}
            (Part::Computation, _) | (Part::Jobs, "AddJob") | (Part::Objects, "AddObj") => {
                count += 1;
            }
            (Part::List, "SetStack") | (Part::Map, "SetEnv") => count = written(0),
            (Part::ObjectMap, "AddObj") => count = written(1),
            _ => {}
        }
    }
    count
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
        forward_only: Vec::new(),
    });
    let counters = matched.counters.map(|setups| {
        setups
            .into_iter()
            .map(|setup| {
                let counter = then_apply(setup);
                Run {
                    program: counter.text(),
                    variables: Vec::new(),
                    depth: counter.steps,
                    steps: counter.steps - 1,
                    cells: Vec::new(),
                    status: Status::Liveness,
                    forward_only: Vec::new(),
                }
            })
            .collect()
    });
    Plans { k7: plan, counters }
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
        forward_only: Vec::new(),
    });
    let counters = computation.counters.map(|counters| {
        counters
            .iter()
            .map(|counter| Run {
                program: counter.text(),
                variables: Vec::new(),
                depth: counter.steps + 1,
                steps: counter.steps,
                cells: Vec::new(),
                status: Status::Liveness,
                forward_only: Vec::new(),
            })
            .collect()
    });
    Plans { k7: plan, counters }
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
        forward_only: Vec::new(),
    });
    Plans {
        k7: plan,
        counters: Err(BUILT),
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
        forward_only: Vec::new(),
    });
    Plans {
        k7: plan,
        counters: Err(BUILT),
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

/// What a readable spelling matches in the computation cell: `[]` the empty one, not one with an
/// item; `[x, ..]` and `[Job { .. }, ..]` one whose first item `x` or the `Job` record is, the
/// witness holding an item more (`then(go, go)`, two items when `then` has stepped).
fn readable_computation(spelling: &str) -> Result<Computation, &'static str> {
    match spelling {
        "[..]" => Ok(Computation {
            witness: go(),
            counters: Err(REST),
            extent: Extent::Open(0),
        }),
        "[]" => Ok(Computation {
            witness: skip(),
            counters: Ok(vec![go()]),
            extent: Extent::Exact(0),
        }),
        "[x, ..]" => Ok(Computation {
            witness: go().then(go()),
            counters: Ok(vec![skip()]),
            extent: Extent::Open(1),
        }),
        "[Job { payload: x, .. }, ..]" => Ok(Computation {
            witness: push_job(0).then(go()),
            counters: Ok(vec![go()]),
            extent: Extent::Open(1),
        }),
        "[.., Job { payload: 0, .. }]" => Err(BACK_ITEM),
        _ => Err(NOTATION),
    }
}

/// What a `cells!` spelling matches in the computation cell, as [`readable_computation`].
fn cells_computation(spelling: &str) -> Result<Computation, &'static str> {
    match spelling {
        "k::configuration::KCell(x, ..)" => Ok(Computation {
            witness: go().then(go()),
            counters: Ok(vec![skip()]),
            extent: Extent::Open(1),
        }),
        "k::configuration::KCell()" => Ok(Computation {
            witness: skip(),
            counters: Ok(vec![go()]),
            extent: Extent::Exact(0),
        }),
        _ => Err(NOTATION),
    }
}

/// What a readable subject spelling matches in `kind`'s cell. An open list, map or instance list's
/// witness holds an item more than the spelling writes; an exact one's counter-witnesses include
/// one with an item more.
fn readable_matched(kind: CellKind, spelling: &str) -> Result<Matched, &'static str> {
    use CellKind::{Collection, Group, Leaf, List, Map, Optional, SetCollection};
    use Extent::{Exact, Open};
    Ok(match (kind, spelling) {
        (Leaf | List | Map | Group, "x") => Matched::every(BINDER),
        (Leaf | List | Map | Group, "_") => Matched::every(WILDCARD),
        (Leaf, "0") => Matched::between(set_pc(0), vec![set_pc(1)]).reading_none(LEAF),
        (List, "[..]") => Matched {
            witness: Some(set_stack(&[0])),
            counters: Err(REST),
            reads: Ok(vec![(Part::List, Open(0))]),
        },
        (List, "[]") => {
            Matched::between(set_stack(&[]), vec![set_stack(&[0])]).reading(Part::List, Exact(0))
        }
        (List, "[x, ..]") => {
            Matched::between(set_stack(&[0, 0]), vec![set_stack(&[])]).reading(Part::List, Open(1))
        }
        (List, "[Job { payload: x, .. }, ..]" | "[.., Job { payload: 0, .. }]") => {
            return Err(LIST_RECORD);
        }
        (Map, "{ .. }") => Matched {
            witness: Some(set_env(&[(1, 0)])),
            counters: Err(REST),
            reads: Ok(vec![(Part::Map, Open(0))]),
        },
        (Map, "{ y -> x, .. }") => Matched::between(set_env(&[(1, 0), (2, 0)]), vec![set_env(&[])])
            .reading(Part::Map, Open(1)),
        (Group, "Frame { ret: x }") => Matched::every(RECORD).reading_none(ONE_CHILD),
        (Optional, "Some(x)") => {
            Matched::between(set_counter(0), vec![absent()]).reading_none(OPTIONAL)
        }
        (Optional, "None") => {
            Matched::between(absent(), vec![set_counter(0)]).reading_none(OPTIONAL)
        }
        (Collection, "[..]") => Matched {
            witness: Some(add_job(0)),
            counters: Err(REST),
            reads: Ok(vec![(Part::Jobs, Open(0))]),
        },
        // The collection starts with no instance.
        (Collection, "[]") => Matched {
            witness: None,
            counters: Ok(vec![Some(add_job(0))]),
            reads: Ok(vec![(Part::Jobs, Exact(0))]),
        },
        // Two jobs, 0 at the front; the counter-witness is the start, with none.
        (Collection, "[Job { payload: x, .. }, ..]") => Matched {
            witness: Some(add_job(1).then(add_job(0))),
            counters: Ok(vec![None]),
            reads: Ok(vec![(Part::Jobs, Open(1))]),
        },
        // Two jobs, 0 at the back; not one job whose payload is 1.
        (Collection, "[.., Job { payload: 0, .. }]") => {
            Matched::between(add_job(0).then(add_job(7)), vec![add_job(1)])
                .reading(Part::Jobs, Open(1))
        }
        (SetCollection, _) => return bag_matched(spelling),
        _ => return Err(NOTATION),
    })
}

/// What a `cells!` subject spelling matches in `kind`'s cell, as [`readable_matched`].
fn cells_matched(kind: CellKind, spelling: &str) -> Result<Matched, &'static str> {
    use CellKind::{Collection, Group, Leaf, List, Map, Optional, SetCollection};
    use Extent::Open;
    Ok(match (kind, spelling) {
        (Leaf | List | Map, "k::configuration::Cell(x)") | (Group, "x") => Matched::every(BINDER),
        (Leaf | List | Map, "k::configuration::Cell(_)") | (Group, "_") => Matched::every(WILDCARD),
        (Leaf, "k::configuration::Cell(0)") => {
            Matched::between(set_pc(0), vec![set_pc(1)]).reading_none(LEAF)
        }
        (List, "k::configuration::Cell([x, ..])") => {
            Matched::between(set_stack(&[0, 0]), vec![set_stack(&[])]).reading(Part::List, Open(1))
        }
        (Map, "k::configuration::Cell(k::map![y -> x, ..])") => {
            Matched::between(set_env(&[(1, 0), (2, 0)]), vec![set_env(&[])])
                .reading(Part::Map, Open(1))
        }
        (Group, "k::fragment![crate::Frame { ret: x }]") => {
            Matched::every(RECORD).reading_none(ONE_CHILD)
        }
        (Optional, "Some(k::configuration::Cell(x))") => {
            Matched::between(set_counter(0), vec![absent()]).reading_none(OPTIONAL)
        }
        (Optional, "None") => {
            Matched::between(absent(), vec![set_counter(0)]).reading_none(OPTIONAL)
        }
        (Collection, "[k::fragment![crate::Job { payload: x, .. }], instances0 @ ..]") => Matched {
            witness: Some(add_job(1).then(add_job(0))),
            counters: Ok(vec![None]),
            reads: Ok(vec![(Part::Jobs, Open(1))]),
        },
        (SetCollection, _) => return bag_matched(spelling),
        _ => return Err(NOTATION),
    })
}

/// What a Set collection's subject spelling matches, in either family. The collection's `..`
/// leaves the other object (key 9) open, so every witness and counter-witness holds it. An
/// instance written whole is looked up, so its witness is the object it denotes, and its
/// counter-witnesses are that object with another key or value where the spelling computes one,
/// and with an entry more in its exact map; an instance whose map writes `..` selects the objects
/// whose map holds the written entry, so its witness has another entry beside it; an instance
/// record with `..` (`Obj { key: 1, .. }`) leaves its map open, so its witness's map is not the
/// template's empty one.
fn bag_matched(spelling: &str) -> Result<Matched, &'static str> {
    use Extent::{Exact, Open};
    let beside = |key: i64, entries: &[(i64, i64)]| other_obj().then(add_obj(key, entries));
    let exact = || beside(1, &[(1, 2)]);
    let more = || beside(1, &[(1, 2), (3, 4)]);
    let instance = |matched: Matched, map: Extent| {
        matched
            .reading(Part::Objects, Open(1))
            .reading(Part::ObjectMap, map)
    };
    Ok(match spelling {
        "{ Obj { key: 1, m: map![1 -> 2] }, .. }"
        | "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> 2] }], instances0 @ .. }" => {
            instance(Matched::between(exact(), vec![more()]), Exact(1))
        }
        "{ Obj { key: k::builtin::int::add(0, 1), m: map![1 -> 2] }, .. }"
        | "{ k::fragment![crate::Obj { key: k::builtin::int::add(0, 1), m: k::map![1 -> 2] }], instances0 @ .. }" => {
            instance(
                Matched::between(exact(), vec![beside(2, &[(1, 2)]), more()]),
                Exact(1),
            )
        }
        "{ Obj { key: 1, m: map![1 -> k::builtin::int::add(1, 1)] }, .. }"
        | "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> k::builtin::int::add(1, 1)] }], instances0 @ .. }" => {
            instance(
                Matched::between(exact(), vec![beside(1, &[(1, 3)]), more()]),
                Exact(1),
            )
        }
        "{ Obj { key: 1, m: map![k::builtin::int::add(0, 1) -> 2] }, .. }"
        | "{ k::fragment![crate::Obj { key: 1, m: k::map![k::builtin::int::add(0, 1) -> 2] }], instances0 @ .. }" => {
            instance(
                Matched::between(exact(), vec![beside(1, &[(2, 2)]), more()]),
                Exact(1),
            )
        }
        "{ Obj { key: 1, m: { 1 -> 2, .. } }, .. }"
        | "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> 2, ..] }], instances0 @ .. }" => {
            instance(
                Matched::between(more(), vec![beside(1, &[(1, 3)])]),
                Open(1),
            )
        }
        "{ Obj { key: 1, .. }, .. }"
        | "{ k::fragment![crate::Obj { key: 1, .. }], instances0 @ .. }" => instance(
            Matched::between(exact(), vec![beside(2, &[(1, 2)])]),
            Open(0),
        ),
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
