#!/usr/bin/env python3
"""Configuration-cells feature gate: rules that leave `k` out (KF-015),
whole nested-cell variables (KF-016), optional cells and cell collections
(KF-023), and rules typed by a cell group that a library declares.

Each fixture package runs natively through k-rust and through Java K, and
the outcomes must agree:

- `framing`: `burn: { fuel: f, acc: a } => { .. }` names no computation
  cell, so it frames `k` like any omitted cell. Its emitted K rule has no
  `<k>` cell, and its `krs expand` reference form has no `KCell` entry and no
  `tail`. Starting from `-cFUEL=3 -cACC=0`, the program `done` (erased by a
  `for Stmt` rule) ends with an empty computation cell on both routes, and
  natively with fuel 0 and acc 6; `report` waits for the fuel to run out and
  writes acc to the computation cell, so both routes end with `6` there.
  `krs check` accepts the package: `done` and `burn` share no cell, so the
  overlap check does not report them (F2 amendment, clause 5);
- `groups`: `push: { .., frame: f } => { stack: list::concat(list::item(f), s) }`
  binds the whole nested cell `<frame>` to one variable of K's generated
  sort `FrameCell`, and `pop` restores it with `frame: f` on the result
  side. The emitted rules name `F:FrameCell` and write the group clause
  bare; `krs expand` writes the entry without a `Cell(..)` wrapper and types
  the binder by the nested `#[k::cell]` struct. `save`/`restore` name the
  leaves and rebuild the frame with `k::fragment!`, and `call`/`ret` are the
  reference spelling of `push`/`pop`, and `wrap`/`unwrap` save the frame
  inside `held(..)`, a user production with a `KItem` field, which the
  frame fills because K makes `FrameCell` a subsort of `KItem`. Starting
  from an empty stack, pc 0 and gas 13, each of the four programs ends with
  pc 3 and gas 10 natively, and `report` writes 310 (`100 * pc + gas`) to
  the computation cell on both routes. `jump` matches and rebuilds the
  frame with the readable record `Frame { pc: p, gas: g }`, which is the
  group term `k::fragment!` spells: `krs expand` writes it as a fragment,
  and `bump jump report` ends with pc 11 and gas 12 and writes 1112 on both
  routes;
- `optional`: an `Option<Int>` cell and an `Option<Mark>` nested cell,
  both `multiplicity = "?"` and absent at start. `enable` creates the
  counter (`None => Some(0)`), `inc`/`dec` update it, `read` reads it,
  `disable` removes it, and a second `enable` is stuck on both routes;
  `peek` matches the mark with the readable record `Some(Mark { seen: s })`
  and `stamp` builds it with `k::fragment!`, the same group term;
- `threads`: K's lesson 1.17-B with a `cell_type = "Map"` collection of
  threads, `initial` so the first thread exists at start. `spawn` creates a
  thread, `join` (written with `k::cells!`) removes one, and a search of the
  race reaches both `return 2;` and `return 3;` on both routes;
- `objects`: a `cell_type = "Set"` collection whose instances are created
  with template defaults, updated in place, removed, and matched exactly;
- `set-instances`: two `cell_type = "Set"` collections whose rules select an
  instance by values computed from their other bindings (`oid: n + 1`, an id
  read from an `env` entry, a whole set or map cell built from `n`), beside
  two equal instances, which a set never holds, and guards; each program ends
  with the same computation cell and the same `<objects>` and `<sacks>`
  contents on both routes (NT-10);
- `shared-memory`: cores in a Map collection keyed by `cid`, beside one
  memory outside every instance. `load` and `peek` are clauses for an
  instruction, steps of one core, that read the memory: each emitted rule
  writes the memory's clause at the top, after the core's `<core> .. ...
  </core>`, and `peek` passes the core's key to `cidPlus`, whose function
  context reads the core's id. `store` and `mark` write the memory from
  rules for the configuration over the cores' instance list. A stored value
  is loaded back, a spawned core 1 peeks 5 + 1 and core 0 joins it, and a
  search of two cores marking one address reaches every order of the marks,
  on both routes, each compiling the same `definition.kore`;
- `queue`: a `cell_type = "List"` collection where `enqueue` appends at
  the back and `dequeue` removes the front, so jobs leave first in first
  out; the emitted back rewrite names the leading instances `_Instances1:Bag`.
  A bracketed value whose front record names every child reads by the
  cell's declared type: `enqueue` matches `k: [Enqueue { value: v }, ..]`
  at the computation cell's head, and `retire`, which leaves the
  computation cell out, removes the front instance `[Job { payload: 0 }, ..]`
  of the List collection; a search of `enqueue 4 enqueue 0 drop front`
  reaches `front` (retired first) and `0` (read first) on both routes;
- `group-core`, `group-small` and `group-board`: rules for a cell group.
  `group-core` declares the group `Core { k, pc, acc }`, the program syntax
  and the rules typed by the group (`for Core`), and no configuration; its
  `load` and `store` leave the open items `busRead(addr)` and
  `busWrite(addr, value)` on the group's computation cell. `group-small`
  holds the group in `Small { core, mem }` and resolves both items from
  `mem`; `group-board` holds it in `Board { core, timer, mem }`, resolves
  them alike and advances `timer` in the same step. Each definition emits the
  library's modules with the same text apart from the configuration module
  the main one imports, and its configuration holds the group's cells
  beside its own: only `board`'s holds a `<timer>`. Both programs that
  store and load end with an empty computation cell and the same `pc`, `acc`
  and `mem` in both definitions on both routes, and `board`'s timer counts
  the bus accesses; a load of an address `mem` does not map is stuck at
  `busRead` in both;
- `group-harts`: rules for a cell group held in instances. The library
  `group-harts/hart` declares `Hart { id, k, pc, regs, reservation?, jobs }`,
  whose `jobs` holds a Map collection of jobs, and rules for it (`for Hart`)
  over leaf cells, the whole group `regs`, the optional `reservation` and
  the job instances, a context alias `hart_eval` and a `#[k::context]`.
  `smp` holds harts as a Map collection keyed by `id`, starts a hart with its
  `spawn` rule, removes a finished one with `join`, and answers the bus from
  one shared memory; `nested` holds a Map collection of harts inside each
  instance of a Map collection of clusters, with those rules for `Cluster`;
  `opt` holds one hart in an optional cell. Each definition emits the
  library's modules with the same text apart from the configuration module
  the main one imports: every clause of a rule for `Hart`, and every cell of
  the alias and the contexts, inside one `<hart> .. ... </hart>`; the
  context `guard_operand`'s condition reads the hart's register `a`. A
  program that uses every form ends with the same cells on both routes in
  each definition, and `opt` is stuck at `guard` once `a` is no longer 1.
  Both routes compile the same `definition.kore`, a context's freezer paired
  by the labels of its heating and cooling rules (`krs-gate kore-compare`).
  A search of two harts that each run every form reaches one final state on
  both routes, and a search of two harts storing at one address reaches both
  orders of the stores, a load reading `0` and `1`. `nested` declares
  `pcPlus`, whose function context typed by `Hart` reads the program counter
  of the hart it is evaluated in, and a rule `leap` for `Hart` that applies
  it: the function receives the hart's key and its cluster's, so two harts
  that leap each read their own counter, and every order of their steps
  reaches one final state on both routes. `krs expand` prints its rules for
  `Cluster` and for `Hart` as `cells!` rules typed by the group, as it prints
  every rule for a group, and the print emits the readable K;
- negative fixtures: a rule without the computation cell whose only pattern
  is an unguarded variable (`krs::analysis::always-enabled-rule`), one
  that writes its cell back unchanged (`krs::analysis::rule-changes-no-cell`),
  a rule that selects a nested cell and a cell inside it
  (`krs::analysis::group-and-descendant`), a cell declaration that is the
  content of two cell fields (`krs::analysis::ambiguous-cell-sort`), and
  `frame: 3` in a `cells!` entry each fail `krs check` with a pinned
  diagnostic, as do a cell bag, a collection without `cell_type`, a
  collection with sibling cells, a `?` cell on a plain field, an `Option`
  field without `multiplicity = "?"`, a `None` template, `..ghost` naming no
  labelled instance, braces on a List collection, one List rule changing
  both ends, a created Map instance without its key, a stream cell inside
  a `?` group, and a `?` template that reads a configuration variable
  written `k::absent!(..)`;
- `optional-config-var-initial`: the same `?` cell written `Some(start)` is
  accepted without a warning and starts present on both routes, holding
  `$START`: from `-cSTART=3`, `go 2` writes 5 to the computation cell
  (`initial=""` in K: an optional cell its initializer starts present).

Run it from the repository root; `--record` rewrites the measured pins after
every step passes, and `--refresh-reference` reruns Java K instead of
replaying the per-user reference cache.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry, krs_gate  # noqa: E402
from support.fixture_gate import Fixture, FixtureGate, Program, diagnostic_lines  # noqa: E402
from support.krs import build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import add_refresh_argument  # noqa: E402
from support.tools import target_environment, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
PINS = HERE / "pins.json"
FIXTURES = HERE / "fixtures"

FRAMING = Fixture(MANIFEST, "krs-configuration-cells-framing")
START = (("FUEL", "3"), ("ACC", "0"))
FRAMING_PROGRAMS = (
    Program("done", "done", "accepted", ".K", variables=START),
    Program("report", "report", "accepted", "6", variables=START),
)

BURN_K = (
    "  rule [burn]:\n"
    "    <fuel> F:Int => F:Int -Int 1 </fuel>\n"
    "    <acc> A:Int => A:Int +Int F:Int </acc>\n"
    "    requires F:Int >Int 0\n"
)
BURN_REFERENCE = (
    '#[k::rule(label = "burn")]\n'
    "#[k::requires(k::builtin::int::gt(f, 0))]\n"
    "pub fn burn(\n"
    "    f: k::Term<k::builtin::Int>,\n"
    "    a: k::Term<k::builtin::Int>,\n"
    "    k::cells! {\n"
    "        fuel : k::configuration::Cell(f), acc : k::configuration::Cell(a), state @ ..\n"
    "    }: crate::Machine,\n"
    ") -> crate::Machine {\n"
)

GROUPS = Fixture(MANIFEST, "krs-configuration-cells-groups")
GROUPS_START = (("STACK", ".List"), ("PC", "0"), ("GAS", "13"))
GROUPS_PROGRAMS = tuple(
    Program(name, f"bump bump {save} bump {restore} bump report", "accepted", "310", variables=GROUPS_START)
    for name, save, restore in (
        ("push-pop", "push", "pop"),
        ("save-restore", "save", "restore"),
        ("call-ret", "call", "ret"),
        ("wrap-unwrap", "wrap", "unwrap"),
    )
)

GROUPS_JUMP = Program("jump", "bump jump report", "accepted", "1112", variables=GROUPS_START)
JUMP_K = (
    "  rule [jump]:\n"
    "    <k> jump => .K ... </k>\n"
    "    (<frame> <pc> P:Int </pc> <gas> G:Int </gas> </frame> => "
    "<frame> <pc> P:Int +Int 10 </pc> <gas> G:Int </gas> </frame>)\n"
)
JUMP_REFERENCE = (
    "frame : k::fragment![crate ::Frame { pc : p, gas : g }]",
    "frame : k::fragment![crate ::Frame { pc : k::builtin::int::add(p, 10), gas : g }]",
)

PUSH_K = (
    "  rule [push]:\n"
    "    <k> push => .K ... </k>\n"
    "    <stack> S:List => ListItem(F:FrameCell) S:List </stack>\n"
    "    F:FrameCell\n"
)
POP_K = (
    "  rule [pop]:\n"
    "    <k> pop => .K ... </k>\n"
    "    <stack> ListItem(F:FrameCell) S:List => S:List </stack>\n"
    "    (_:FrameCell => F:FrameCell)\n"
)
WRAP_K = (
    "  rule [wrap]:\n"
    "    <k> wrap => .K ... </k>\n"
    "    <stack> S:List => ListItem(held ( F:FrameCell )) S:List </stack>\n"
    "    F:FrameCell\n"
)
PUSH_REFERENCE = (
    '#[k::rule(label = "push")]\n'
    "pub fn push(\n"
    "    s: k::Term<k::builtin::List>,\n"
    "    f: crate::Frame,\n"
    "    k::cells! {\n"
    "        k : k::configuration::KCell(crate ::Cmd::Push(), ..), stack :\n"
    "        k::configuration::Cell(s), frame : f, state @ ..\n"
    "    }: crate::Machine,\n"
    ") -> crate::Machine {\n"
)

OPTIONAL = Fixture(MANIFEST, "krs-configuration-cells-optional")
OPTIONAL_PROGRAMS = (
    Program("count", "enable inc inc dec read", "accepted", "1"),
    Program("stuck", "enable enable", "accepted", "enable"),
    Program("toggle", "enable inc disable enable read", "accepted", "0"),
    Program("mark", "enable inc inc stamp peek", "accepted", "2"),
)

OPTIONAL_K = (
    "    <counter multiplicity=\"?\"> 0 </counter>\n"
    "    <mark multiplicity=\"?\">\n",
    "  rule [enable]:\n"
    "    <k> enable => .K ... </k>\n"
    "    (.Bag => <counter> 0 </counter>)\n",
    "  rule [inc]:\n"
    "    <k> inc => .K ... </k>\n"
    "    <counter> N:Int => N:Int +Int 1 </counter>\n",
    "  rule [read]:\n"
    "    <k> read => N:Int ... </k>\n"
    "    <counter> N:Int </counter>\n",
    "  rule [disable]:\n"
    "    <k> disable => .K ... </k>\n"
    "    (<counter> _ </counter> => .Bag)\n",
    "    (.Bag => <mark> <seen> N:Int </seen> </mark>)\n",
)
OPTIONAL_REFERENCE = (
    "    pub counter: Option<k::configuration::Cell<Int>>,\n",
    "            counter: k::absent!(k::configuration::Cell::new(0)),\n",
    "        k : k::configuration::KCell(crate ::Cmd::Enable(), ..), counter : None, state @\n",
    "        k : k::configuration::KCell(..), counter : Some(k::configuration::Cell(0)),\n",
    "        k : k::configuration::KCell(..), mark : Some(k::fragment![crate ::Mark { seen : n\n",
)

THREADS = Fixture(MANIFEST, "krs-configuration-cells-threads")
# The sort rules `add` (`for Exp`) and `seq` (`for Stmt`) run at the main cell, a thread's `k`, so
# each is a step of one thread: `krs expand` prints them as `cells!` rules typed `crate::Thread`.
THREADS_PROGRAMS = (
    Program("spawn-join", "a = spawn {return 1 + 2;}; b = join a; return b;", "accepted", "return 3;"),
    Program(
        "race",
        "x = 1; a = spawn {x = 2; return 0;}; x = 3; c = join a; return x;",
        "accepted",
        None,
        search=("return 2;", "return 3;"),
    ),
)
THREADS_K = (
    "      <thread multiplicity=\"*\" type=\"Map\" initial=\"\">\n",
    "  rule [spawn]:\n"
    "    <thread>\n"
    "        <k> spawn { Body:Stmt } ~> Tail0:K => N:Int ~> Tail0:K </k>\n"
    "        ...\n"
    "    </thread>\n"
    "    (.Bag => <thread>\n"
    "        <id> N:Int </id>\n"
    "        <k> Body:Stmt </k>\n"
    "        ...\n"
    "    </thread>)\n",
    "    (<thread>\n"
    "        <id> T:Int </id>\n"
    "        <k> return I:Int ; ... </k>\n"
    "        ...\n"
    "    </thread> => .Bag)\n",
)
THREADS_REFERENCE = (
    "crate ::Threads::thread : { me @ k::fragment![crate ::Thread { k : k::k![crate "
    "::ExpSyntax::Spawn(body), tail0 @ ..], .. }], instances0 @ .. }",
    "crate ::Threads::thread : { k::fragment![crate ::Thread { k : k::k![n, ..tail0], "
    "..me }], k::fragment![crate ::Thread { id : n, k : k::k![body], .. }], ..instances0 }",
)

OBJECTS = Fixture(MANIFEST, "krs-configuration-cells-objects")
OBJECTS_PROGRAMS = (
    Program("count", "mk 1 mk 2 touch 2 touch 2 rm 1 count 2", "accepted", "2"),
    Program("default", "mk 3 count 3", "accepted", "0"),
    Program("single", "mk 5 single", "accepted", "5"),
    Program("single-stuck", "mk 5 mk 6 single", "accepted", "single"),
)
OBJECTS_K = (
    "      <obj multiplicity=\"*\" type=\"Set\">\n",
    "    (.Bag => <obj>\n"
    "        <oid> N:Int </oid>\n"
    "        ...\n"
    "    </obj>)\n",
    "    <obj>\n"
    "        <oid> N:Int </oid>\n"
    "        <hits> H:Int => H:Int +Int 1 </hits>\n"
    "    </obj>\n",
    "    <objects>\n"
    "        <obj>\n"
    "            <oid> N:Int </oid>\n"
    "            ...\n"
    "        </obj>\n"
    "    </objects>\n",
)

SET_INSTANCES = Fixture(MANIFEST, "krs-configuration-cells-set-instances")
# Each program's final computation cell and `<objects>` and `<sacks>` contents.
SET_INSTANCES_PROGRAMS = (
    Program(
        "probe-found", "mk 3 probe 2", "accepted", ".K",
        cells=(("objects", "<obj> <oid> 3 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "probe-touched", "mk 3 touch 3 probe 2", "accepted", "probe 2",
        cells=(("objects", "<obj> <oid> 3 </oid> <hits> 1 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "probe-empty", "probe 5", "accepted", "probe 5",
        cells=(("objects", ".ObjCellSet"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "probe-other-touched", "mk 4 mk 3 touch 4 probe 3", "accepted", "probe 3",
        cells=(("objects", "<obj> <oid> 3 </oid> <hits> 0 </hits> </obj> <obj> <oid> 4 </oid> <hits> 1 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "drop", "mk 3 drop 2 probe 2", "accepted", "probe 2",
        cells=(("objects", ".ObjCellSet"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "bump", "mk 3 bump 2 probe 2", "accepted", "probe 2",
        cells=(("objects", "<obj> <oid> 3 </oid> <hits> 1 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "next-equal-hits", "mk 3 mk 4 touch 3 touch 4 next 3", "accepted", ".K",
        cells=(("objects", "<obj> <oid> 3 </oid> <hits> 1 </hits> </obj> <obj> <oid> 4 </oid> <hits> 1 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "next-other-hits", "mk 3 mk 4 touch 3 next 3", "accepted", "next 3",
        cells=(("objects", "<obj> <oid> 3 </oid> <hits> 1 </hits> </obj> <obj> <oid> 4 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "via", "mk 5 via 1", "accepted", ".K",
        cells=(("objects", ".ObjCellSet"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "check-touched", "mk 4 touch 4 check 2", "accepted", ".K",
        cells=(("objects", "<obj> <oid> 4 </oid> <hits> 1 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "check-untouched", "mk 4 check 2", "accepted", "check 2",
        cells=(("objects", "<obj> <oid> 4 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "check-zero", "mk 0 check 0", "accepted", "check 0",
        cells=(("objects", "<obj> <oid> 0 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "find", "mk 3 find 2", "accepted", ".K",
        cells=(("objects", "<obj> <oid> 3 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "probe-among-four", "mk 1 mk 2 mk 3 mk 40 probe 39", "accepted", ".K",
        cells=(("objects", "<obj> <oid> 1 </oid> <hits> 0 </hits> </obj> <obj> <oid> 2 </oid> <hits> 0 </hits> </obj> <obj> <oid> 3 </oid> <hits> 0 </hits> </obj> <obj> <oid> 40 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "probe-among-four-reversed", "mk 40 mk 3 mk 2 mk 1 probe 39", "accepted", ".K",
        cells=(("objects", "<obj> <oid> 1 </oid> <hits> 0 </hits> </obj> <obj> <oid> 2 </oid> <hits> 0 </hits> </obj> <obj> <oid> 3 </oid> <hits> 0 </hits> </obj> <obj> <oid> 40 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "dup", "mk 1 mk 2 mk 3 dup 1", "accepted", "dup 1",
        cells=(("objects", "<obj> <oid> 1 </oid> <hits> 0 </hits> </obj> <obj> <oid> 2 </oid> <hits> 0 </hits> </obj> <obj> <oid> 3 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "dz-zero", "mk 1 dz 0", "accepted", "dz 0",
        cells=(("objects", "<obj> <oid> 1 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "dz-five", "mk 105 dz 5", "accepted", ".K",
        cells=(("objects", "<obj> <oid> 105 </oid> <hits> 0 </hits> </obj>"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "bags", "mkb 5 bags 5", "accepted", ".K",
        cells=(("objects", ".ObjCellSet"), ("sacks", "<bag> <key> 5 </key> <s> SetItem ( 5 ) SetItem ( 6 ) </s> <m> 5 |-> 6 </m> </bag>")),
    ),
    Program(
        "bags-other-key", "mkb 5 bags 4", "accepted", "bags 4",
        cells=(("objects", ".ObjCellSet"), ("sacks", "<bag> <key> 5 </key> <s> SetItem ( 5 ) SetItem ( 6 ) </s> <m> 5 |-> 6 </m> </bag>")),
    ),
    Program(
        "bagm", "mkb 5 bagm 6", "accepted", ".K",
        cells=(("objects", ".ObjCellSet"), ("sacks", "<bag> <key> 5 </key> <s> SetItem ( 5 ) SetItem ( 6 ) </s> <m> 5 |-> 6 </m> </bag>")),
    ),
    Program(
        "bagc", "mkb 5 bagc 4", "accepted", ".K",
        cells=(("objects", ".ObjCellSet"), ("sacks", ".BagCellSet")),
    ),
    Program(
        "bagc-other-key", "mkb 5 bagc 5", "accepted", "bagc 5",
        cells=(("objects", ".ObjCellSet"), ("sacks", "<bag> <key> 5 </key> <s> SetItem ( 5 ) SetItem ( 6 ) </s> <m> 5 |-> 6 </m> </bag>")),
    ),
)

SHARED_MEMORY = Fixture(MANIFEST, "krs-configuration-cells-shared-memory")
SHARED_MEMORY_PROGRAMS = (
    Program("store-load", "store ( 0 , 5 ) ; load ( 0 )", "accepted", "5", cells=(("mem", "0 |-> 5"),)),
    # Core 1 reads 5 and adds its own id; core 0 takes the 6 it ends with.
    Program(
        "peek", "store ( 0 , 5 ) ; spawn { peek ( 0 ) } ; join ( 1 )", "accepted", "6",
        search=("6",), cells=(("mem", "0 |-> 5"),),
    ),
    # Core 1 marks 1 and loads; core 0 marks 0 before core 1's mark, between it and the load,
    # or after the load: core 1 reads 1, 0 and 1.
    Program(
        "race", "spawn { mark ( 0 ) ; load ( 0 ) } ; mark ( 0 ) ; join ( 1 )", "accepted", None,
        search=("0", "1", "1"),
    ),
)
# A clause for an instruction that reads the memory: the computation's clause inside the core,
# the memory's at the top after the core's cell, and the core's key passed where `cidPlus` reads
# the core.
SHARED_MEMORY_K = (
    "  rule [load]:\n"
    "    <core>\n"
    "        <k> load ( Addr:Int ) => V:Int ... </k>\n"
    "        ...\n"
    "    </core>\n"
    "    <mem> Addr:Int |-> V:Int ... </mem>\n",
    "  rule [peek]:\n"
    "    <core>\n"
    "        <k> peek ( Addr:Int ) => cidPlus ( V:Int ) #instance ( Krs_KeyCore:Int ) ... </k>\n"
    "        <cid> Krs_KeyCore:Int </cid>\n"
    "        ...\n"
    "    </core>\n"
    "    <mem> Addr:Int |-> V:Int ... </mem>\n",
)

QUEUE = Fixture(MANIFEST, "krs-configuration-cells-queue")
QUEUE_PROGRAMS = (
    Program("dequeue", "enqueue 1 enqueue 2 enqueue 3 dequeue", "accepted", "1"),
    Program("fifo", "enqueue 1 enqueue 2 enqueue 3 drop drop dequeue", "accepted", "3"),
    Program("front", "enqueue 4 enqueue 5 front", "accepted", "4"),
    Program("pop", "enqueue 4 enqueue 5 enqueue 6 pop", "accepted", "6"),
    Program("retire", "enqueue 4 enqueue 0 drop front", "accepted", None, search=("0", "front")),
)
QUEUE_K = (
    "      <job multiplicity=\"*\" type=\"List\">\n",
    "    <queue>\n"
    "        (<job>\n"
    "            <payload> P:Int </payload>\n"
    "            ...\n"
    "        </job> => .Bag)\n"
    "        ...\n"
    "    </queue>\n",
    "    <queue>\n"
    "        _Instances1:Bag\n"
    "        (.Bag => <job>\n"
    "            <payload> V:Int </payload>\n"
    "            ...\n"
    "        </job>)\n"
    "    </queue>\n",
    "  rule [retire]:\n"
    "    <queue>\n"
    "        (<job>\n"
    "            <payload> 0 </payload>\n"
    "        </job> => .Bag)\n"
    "        ...\n"
    "    </queue>\n",
)

GROUP_CORE = "krs-configuration-cells-group-core"
GROUP_SMALL = Fixture(MANIFEST, "krs-configuration-cells-group-small", dependencies=(f"{GROUP_CORE}:main",))
GROUP_BOARD = Fixture(MANIFEST, "krs-configuration-cells-group-board", dependencies=(f"{GROUP_CORE}:main",))
GROUP_MODULE = "KRS-GROUP-CORE"
# Each program, the whole computation cell and the other cells it ends with in both
# definitions, and `board`'s timer: one tick per `load` and `store` the bus answers. Each load
# reads a value other than the accumulator it replaces, so a load that leaves the accumulator
# unchanged ends differently; `overwrite` reads the second of two stores at one address, and
# `unmapped` is stuck at the read of an address `mem` does not map, in both definitions.
GROUP_RUNS = (
    (
        "store-load", "inc ; inc ; store ( 7 ) ; inc ; load ( 7 ) ; done", ".K",
        (("pc", "5"), ("acc", "2"), ("mem", "7 |-> 2")), "2",
    ),
    (
        "overwrite", "inc ; store ( 1 ) ; inc ; store ( 1 ) ; inc ; load ( 1 ) ; done", ".K",
        (("pc", "6"), ("acc", "2"), ("mem", "1 |-> 2")), "3",
    ),
    (
        "unmapped", "inc ; load ( 3 ) ; done", "busRead ( 3 ) ~> done",
        (("pc", "2"), ("acc", "1"), ("mem", ".Map")), "0",
    ),
)
GROUP_SMALL_PROGRAMS = tuple(
    Program(name, text, "accepted", run, cells=cells, whole=True)
    for name, text, run, cells, _ in GROUP_RUNS
)
GROUP_BOARD_PROGRAMS = tuple(
    Program(name, text, "accepted", run, cells=(*cells, ("timer", timer)), whole=True)
    for name, text, run, cells, timer in GROUP_RUNS
)
# The cells of each definition's configuration, in order, and the group's own, the same text in
# both.
GROUP_CELLS = {
    "krs-configuration-cells-group-small": ("core", "k", "pc", "acc", "mem"),
    "krs-configuration-cells-group-board": ("core", "k", "pc", "acc", "timer", "mem"),
}
GROUP_CORE_CELLS = (
    "    <core>\n"
    "      <k> $PGM:Prog </k>\n"
    "      <pc> 0 </pc>\n"
    "      <acc> 0 </acc>\n"
    "    </core>\n"
)

GROUP_HARTS_LIBRARY = "krs-configuration-cells-group-harts-hart"
GROUP_HARTS_MODULE = "KRS-GROUP-HART"
GROUP_HARTS = tuple(
    (Fixture(MANIFEST, f"krs-configuration-cells-group-harts-{name}", dependencies=(f"{GROUP_HARTS_LIBRARY}:main",)),
     f"KRS-GROUP-HARTS-{name.upper()}-CONFIGURATION")
    for name in ("smp", "nested", "opt")
)
# Every form a rule for `Hart` holds inside the hart: from pc 0, `inc` counts 1, `reserve` and
# `release` add the reserved 1, `wait ( here )` and `hop ( here )` each double it to 8; `swap`
# exchanges the registers 1 and 2, `post` creates the job keyed 0 and `work` counts it once.
GROUP_HARTS_FORMS = "inc ; swap ; reserve ; release ; post ; work ; wait ( here ) ; hop ( here )"
GROUP_HARTS_CELLS = (("pc", "8"), ("a", "2"), ("b", "1"), ("payload", "1"))
# Two harts store their ids at address 0; after hart 1 is joined, hart 0 reads the later store.
GROUP_HARTS_RACE = Program(
    "race", "spawn { store ( 0 ) } ; store ( 0 ) ; join ( 1 ) ; load ( 0 )", "accepted", None,
    search=("0", "1"),
)
# Two harts run every form, interleaved: hart 1 from pc 0 ends with pc 8, `a` 2 and one job's
# payload 1, and reports `8 + 10 * 2 + 100 * 1` at address 1 before hart 0 joins it; hart 0 runs
# `guard ( here )` with `a` 1, so its operand is evaluated, and ends with pc 24 and two `work`s on
# its job. Every order of the two harts' steps reaches that one final state, on both routes.
GROUP_HARTS_PAIR = Program(
    "pair",
    "spawn { inc ; swap ; reserve ; release ; post ; work ; wait ( here ) ; hop ( here ) ; report ( 1 ) } ; "
    "inc ; guard ( here ) ; inc ; reserve ; release ; post ; work ; work ; wait ( here ) ; hop ( here ) ; "
    "join ( 1 ) ; load ( 1 )",
    "accepted", "128",
    search=("128",),
    cells=(("pc", "24"), ("a", "1"), ("b", "2"), ("payload", "2"), ("mem", "1 |-> 128")),
)
# Two harts each `leap` past their own program counter, which `pcPlus` reads through its function
# context: hart 1 from pc 1 leaps 10 and reports `11 + 10 * 1 + 100 * 0` at address 1, and hart 0
# from pc 0 leaps 100 before it joins hart 1 and loads the report. Every order of their steps reads
# each hart's own counter, so it reaches that one final state, on both routes.
GROUP_HARTS_LEAP = Program(
    "leap",
    "spawn { post ; inc ; leap ( 10 ) ; report ( 1 ) } ; leap ( 100 ) ; join ( 1 ) ; load ( 1 )",
    "accepted", "21",
    search=("21",),
    cells=(("pc", "100"), ("mem", "1 |-> 21")),
)
GROUP_HARTS_PROGRAMS = {
    "krs-configuration-cells-group-harts-smp": (
        Program("forms", f"{GROUP_HARTS_FORMS} ; store ( 0 ) ; load ( 0 )", "accepted", "0",
                cells=(*GROUP_HARTS_CELLS, ("mem", "0 |-> 0"))),
        GROUP_HARTS_RACE,
        GROUP_HARTS_PAIR,
    ),
    "krs-configuration-cells-group-harts-nested": (
        Program("forms", f"{GROUP_HARTS_FORMS} ; store ( 0 ) ; load ( 0 )", "accepted", "0",
                cells=(*GROUP_HARTS_CELLS, ("mem", "0 |-> 0"))),
        GROUP_HARTS_RACE,
        GROUP_HARTS_PAIR,
        GROUP_HARTS_LEAP,
    ),
    # `opt` answers no bus item, so the load stays open; after `swap` the register `a` is 2, so
    # `guard`'s operand is not evaluated and the hart is stuck at it.
    "krs-configuration-cells-group-harts-opt": (
        Program("forms", f"{GROUP_HARTS_FORMS} ; load ( 0 )", "accepted", "busRead ( 0 )",
                cells=GROUP_HARTS_CELLS),
        Program("guarded", "swap ; guard ( here )", "accepted", "guard ( here )"),
    ),
}
# Each form inside the hart, as the library's module states it in every definition.
GROUP_HARTS_K = (
    "  context alias [hartEval]:\n"
    "    <hart>\n"
    "        <k> HERE ~> Tail:K </k>\n"
    "        ...\n"
    "    </hart>\n",
    "  context [hop-operand]:\n"
    "    <hart>\n"
    "        <k> hop ( HOLE:Exp ) ... </k>\n"
    "        ...\n"
    "    </hart>\n",
    "  context [guard-operand]:\n"
    "    <hart>\n"
    "        <k> guard ( HOLE:Exp ) ... </k>\n"
    "        <a> One:Int </a>\n"
    "        ...\n"
    "    </hart>\n"
    "    requires One:Int ==Int 1\n",
    "  rule [swap]:\n"
    "    <hart>\n"
    "        <k> swap => .K ... </k>\n"
    "        (<regs> <a> A:Int </a> <b> B:Int </b> </regs> => <regs> <a> B:Int </a> <b> A:Int </b> </regs>)\n"
    "        ...\n"
    "    </hart>\n",
    "        (.Bag => <reservation> Pc:Int </reservation>)\n",
    "        (<reservation> R:Int </reservation> => .Bag)\n",
    "        (.Bag => <job>\n"
    "            <jid> Me:Int </jid>\n"
    "            <payload> 0 </payload>\n"
    "        </job>)\n",
    "  rule [work]:\n"
    "    <hart>\n"
    "        <k> work => .K ... </k>\n"
    "        <job>\n"
    "            <payload> P:Int => P:Int +Int 1 </payload>\n"
    "            ...\n"
    "        </job>\n"
    "        ...\n"
    "    </hart>\n",
)

NEGATIVE = (
    "unguarded-framed-rule",
    "identity-framed-rule",
    "group-and-leaf",
    "reused-cell-declaration",
    "group-literal",
    "cell-bag",
    "collection-without-type",
    "collection-siblings",
    "optional-plain-field",
    "optional-without-multiplicity",
    "optional-none-template",
    "unknown-instance-label",
    "list-braces",
    "list-both-ends",
    "map-created-without-key",
    "stream-in-optional",
    "optional-config-var",
)

# Accepted: a `?` cell that reads a configuration variable, written `Some(..)`.
PRESENT = "optional-config-var-initial"
PRESENT_PROGRAMS = (Program("go", "go 2", "accepted", "5", variables=(("START", "3"),)),)
PRESENT_K = "    <counter multiplicity=\"?\" initial=\"\">"


def materialize(name: str, workspace: Path) -> Path:
    """Copy one negative fixture into the workspace with the facade path filled in."""

    destination = workspace / "fixtures" / name
    shutil.copytree(FIXTURES / name, destination)
    facade = json.dumps(str((ROOT / "crates" / "krs").resolve()))
    for template in sorted(destination.rglob("Cargo.toml.in")):
        manifest = template.read_text(encoding="utf-8").replace("@KRS_CRATE_PATH@", facade)
        template.with_name("Cargo.toml").write_text(manifest, encoding="utf-8")
        template.unlink()
    return destination / "Cargo.toml"


def final_cells(harness: FixtureGate, emitted, program: Program, cells: dict[str, str]) -> None:
    """Require the native final state of `program` to hold the given cell texts."""

    with krs_gate.Session(harness.gate, environment=harness.environment) as session:
        session.load(emitted.definition_ir, emitted.main_module)
        pattern = session.configure({"PGM": program.text, **dict(program.variables)})["pattern"]
        session.execute(pattern, keep=program.name)
        for cell, text in cells.items():
            session.expect(program.name, cell, text=text)


def verify_framing(harness: FixtureGate) -> None:
    harness.check(FRAMING)
    expansion = harness.expand(FRAMING)
    if BURN_REFERENCE not in expansion:
        raise GateError("the reference form of `burn` gained a computation-cell entry or lost its guard")
    emitted = harness.emit(FRAMING)
    source = emitted.source.read_text(encoding="utf-8")
    if BURN_K not in source:
        raise GateError(f"emitted K changed the k-less `burn` rule:\n{source}")
    harness.compare(emitted, FRAMING_PROGRAMS, sort="Stmt")
    final_cells(harness, emitted, FRAMING_PROGRAMS[0], {"fuel": "0", "acc": "6"})


def verify_groups(harness: FixtureGate) -> None:
    harness.check(GROUPS)
    expansion = harness.expand(GROUPS)
    if PUSH_REFERENCE not in expansion:
        raise GateError("the reference form of `push` lost its unwrapped group entry or its `crate::Frame` binder")
    flat = " ".join(expansion.split())
    for text in JUMP_REFERENCE:
        if text not in flat:
            raise GateError(f"the readable group record of `jump` is not a fragment in the reference form:\n{text}")
    emitted = harness.emit(GROUPS)
    source = emitted.source.read_text(encoding="utf-8")
    for rule in (PUSH_K, POP_K, JUMP_K, WRAP_K):
        if rule not in source:
            raise GateError(f"emitted K changed a whole-cell rule:\n{source}")
    harness.compare(emitted, (*GROUPS_PROGRAMS, GROUPS_JUMP), sort="Stmt")
    for program in GROUPS_PROGRAMS:
        final_cells(harness, emitted, program, {"pc": "3", "gas": "10"})
    final_cells(harness, emitted, GROUPS_JUMP, {"pc": "11", "gas": "12"})


def verify_optional(harness: FixtureGate) -> None:
    harness.check(OPTIONAL)
    expansion = harness.expand(OPTIONAL)
    for text in OPTIONAL_REFERENCE:
        if text not in expansion:
            raise GateError(f"the reference form lost an optional-cell spelling:\n{text}")
    emitted = harness.emit(OPTIONAL)
    source = emitted.source.read_text(encoding="utf-8")
    for text in OPTIONAL_K:
        if text not in source:
            raise GateError(f"emitted K changed an optional-cell form:\n{text}\nin:\n{source}")
    harness.compare(emitted, OPTIONAL_PROGRAMS, sort="Stmt")


def verify_threads(harness: FixtureGate) -> None:
    harness.check(THREADS)
    expansion = harness.expand(THREADS)
    flat = " ".join(expansion.split())
    for text in THREADS_REFERENCE:
        if text not in flat:
            raise GateError(f"the reference form lost a collection spelling:\n{text}\nin:\n{expansion}")
    emitted = harness.emit(THREADS)
    source = emitted.source.read_text(encoding="utf-8")
    for text in THREADS_K:
        if text not in source:
            raise GateError(f"emitted K changed a collection form:\n{text}\nin:\n{source}")
    harness.compare(emitted, THREADS_PROGRAMS, sort="Stmt", search=True)


def verify_emitted(harness: FixtureGate, fixture: Fixture, texts: tuple[str, ...]):
    """Check, expand, and emit a fixture, and require the given emitted K forms."""

    harness.check(fixture)
    harness.expand(fixture)
    emitted = harness.emit(fixture)
    source = emitted.source.read_text(encoding="utf-8")
    for text in texts:
        if text not in source:
            raise GateError(f"emitted K changed a collection form:\n{text}\nin:\n{source}")
    return emitted


def modules(source: str) -> dict[str, str]:
    """The body of each module of an emitted definition, by name."""

    return {
        match.group(1): match.group(2)
        for match in re.finditer(r"^module (\S+)\n(.*?)^endmodule$", source, re.MULTILINE | re.DOTALL)
    }


def library_modules(source: str, configuration: str, module: str = GROUP_MODULE) -> dict[str, str]:
    """The emitted modules of the group's library `module`, without the main one's import of `configuration`'s module."""

    library = {
        name: body for name, body in modules(source).items()
        if name == module or name.startswith(f"{module}-")
    }
    if set(library) != {module, f"{module}-SYNTAX"}:
        raise GateError(f"the library's modules are {sorted(library)}, not {module} and its syntax:\n{source}")
    imported = f"  imports {configuration}\n"
    if imported not in library[module]:
        raise GateError(f"{module} does not import {configuration}:\n{library[module]}")
    library[module] = library[module].replace(imported, "", 1)
    return library


def configuration_text(source: str, configuration: str) -> str:
    """The `configuration` declaration of the module `configuration`."""

    body = modules(source).get(configuration, "")
    match = re.search(r"^  configuration\n(.*)", body, re.MULTILINE | re.DOTALL)
    if match is None:
        raise GateError(f"no configuration in module {configuration}:\n{source}")
    return match.group(1)


def verify_group(harness: FixtureGate) -> None:
    library = {}
    for fixture, configuration, programs in (
        (GROUP_SMALL, "KRS-GROUP-SMALL-CONFIGURATION", GROUP_SMALL_PROGRAMS),
        (GROUP_BOARD, "KRS-GROUP-BOARD-CONFIGURATION", GROUP_BOARD_PROGRAMS),
    ):
        harness.check(fixture)
        harness.expand(fixture)
        emitted = harness.emit(fixture)
        source = emitted.source.read_text(encoding="utf-8")
        library[fixture.package] = library_modules(source, configuration)
        cells = configuration_text(source, configuration)
        declared = tuple(re.findall(r"<([a-z][\w-]*)>", cells))
        if declared != GROUP_CELLS[fixture.package] or GROUP_CORE_CELLS not in cells:
            raise GateError(
                f"{fixture.package}: the configuration does not hold the cells {GROUP_CELLS[fixture.package]}, "
                f"the group's as declared:\n{cells}"
            )
        harness.compare(emitted, programs, sort="Prog")
    if library[GROUP_SMALL.package] != library[GROUP_BOARD.package]:
        raise GateError(
            "the group's modules differ between its definitions:\n"
            + json.dumps(library, indent=2)
        )


def verify_group_harts(harness: FixtureGate) -> None:
    """Each definition holding harts in an instance emits the library's rules inside `<hart>`,
    and runs them alike on both routes."""

    library = {}
    for fixture, configuration in GROUP_HARTS:
        harness.check(fixture)
        harness.expand(fixture)
        emitted = harness.emit(fixture)
        source = emitted.source.read_text(encoding="utf-8")
        library[fixture.package] = library_modules(source, configuration, GROUP_HARTS_MODULE)
        for text in GROUP_HARTS_K:
            if text not in library[fixture.package][GROUP_HARTS_MODULE]:
                raise GateError(f"{fixture.package}: emitted K changed a form inside the hart:\n{text}\nin:\n{source}")
        programs = GROUP_HARTS_PROGRAMS[fixture.package]
        harness.compare(
            emitted, programs, sort="Prog",
            search=any(program.search is not None for program in programs), kore=True,
        )
    texts = list(library.values())
    if any(text != texts[0] for text in texts):
        raise GateError(
            "the hart library's modules differ between its definitions:\n"
            + json.dumps(library, indent=2)
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 configuration-cells ledger")

    environment = {**z3_environment(), **target_environment(), "CARGO_TERM_COLOR": "never"}
    krs = build(environment)
    gate = krs_gate.configured_or_build()
    check_packages("configuration-cells", krs=krs, env=environment)

    with tempfile.TemporaryDirectory(prefix="krs-configuration-cells-") as temporary:
        workspace = Path(temporary)
        harness = FixtureGate(
            "configuration-cells", pins, workspace, krs, gate, environment,
            refresh=arguments.refresh_reference,
            divergences=pins.get("known_divergences", {}),
            check_prints=True,
        )

        verify_framing(harness)
        print("PASS framing: burn frames k on both routes, done ends with fuel 0 and acc 6, report writes 6")

        verify_groups(harness)
        print("PASS groups: push/pop, save/restore and call/ret each end with pc 3 and gas 10, report writes 310; jump rebuilds the frame from a readable record")

        verify_optional(harness)
        print("PASS optional: enable creates, inc/dec update, read reads, disable deletes; a second enable is stuck")

        verify_threads(harness)
        print("PASS threads: spawn creates and join removes Map instances; the race reaches return 2 and return 3 on both routes")

        harness.compare(verify_emitted(harness, OBJECTS, OBJECTS_K), OBJECTS_PROGRAMS, sort="Stmt")
        print("PASS objects: Set instances are created with defaults, updated, removed, and matched exactly")

        harness.check(SET_INSTANCES)
        harness.expand(SET_INSTANCES)
        harness.compare(harness.emit(SET_INSTANCES), SET_INSTANCES_PROGRAMS, sort="Stmt")
        print(
            "PASS set-instances: computed ids, hits, and set and map cells select the same Set instances "
            "on both routes"
        )

        harness.compare(
            verify_emitted(harness, SHARED_MEMORY, SHARED_MEMORY_K), SHARED_MEMORY_PROGRAMS,
            sort="Prog", search=True, kore=True,
        )
        print(
            "PASS shared-memory: a core's step reads the memory beside the cores, its clause at the top; "
            "peek passes the core's key; the race reaches every order of the marks on both routes"
        )

        harness.compare(verify_emitted(harness, QUEUE, QUEUE_K), QUEUE_PROGRAMS, sort="Stmt", search=True)
        print(
            "PASS queue: enqueue appends at the back and dequeue removes the front, first in first out; "
            "brackets read by the cell's declared type"
        )

        verify_group(harness)
        print(
            "PASS group: the library's rules for Core run in small and board alike, each resolving the bus "
            "with its own rules; only board's timer counts the bus accesses; an unmapped load is stuck at busRead"
        )

        verify_group_harts(harness)
        print(
            "PASS group-harts: the library's rules for Hart run inside one hart in a Map collection, a nested "
            "collection and an optional cell; both routes agree, and two harts' racing stores reach both orders"
        )

        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-configuration-cells-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

        present = Fixture(materialize(PRESENT, workspace), f"krs-configuration-cells-{PRESENT}")
        warnings = diagnostic_lines(harness.check(present).stderr)
        if warnings:
            raise GateError(f"{PRESENT}: krs check reported diagnostics:\n" + "\n".join(warnings))
        harness.expand(present)
        emitted = harness.emit(present)
        source = emitted.source.read_text(encoding="utf-8")
        if PRESENT_K not in source:
            raise GateError(f"{PRESENT}: the emitted counter is not `initial`:\n{source}")
        harness.compare(emitted, PRESENT_PROGRAMS, sort="Stmt")
        print(f"PASS {PRESENT}: the counter written `Some(start)` starts as $START on both routes, without a warning")

    pins.finish("configuration-cells")
    print("PASS configuration-cells")
    return 0


if __name__ == "__main__":
    entry("configuration-cells", main, errors=(OSError,))
