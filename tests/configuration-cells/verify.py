#!/usr/bin/env python3
"""Configuration-cells feature gate: rules that leave `k` out (KF-015),
whole nested-cell variables (KF-016), and optional cells and cell
collections (KF-023).

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
- `groups`: `push: { .., frame: f } => { stack: list::concat(list::item(f), s), frame: f }`
  binds the whole nested cell `<frame>` to one variable of K's generated
  sort `FrameCell`, and `pop` restores it with `frame: f` on the result
  side. The emitted rules name `F:FrameCell` and write the group clause
  bare; `krs expand` writes the entry without a `Cell(..)` wrapper and types
  the binder by the nested `#[k::cell]` struct. `save`/`restore` restate the
  leaves and rebuild the frame with `k::fragment!`, and `call`/`ret` are the
  reference spelling of `push`/`pop`. Starting from an empty stack, pc 0 and
  gas 13, each of the three programs ends with pc 3 and gas 10 natively, and
  `report` writes 310 (`100 * pc + gas`) to the computation cell on both
  routes;
- `optional`: an `Option<Int>` cell and an `Option<Mark>` nested cell,
  both `multiplicity = "?"` and absent at start. `enable` creates the
  counter (`None => Some(0)`), `inc`/`dec` update it, `read` reads it,
  `disable` removes it, and a second `enable` is stuck on both routes;
- `threads`: K's lesson 1.17-B with a `cell_type = "Map"` collection of
  threads, `initial` so the first thread exists at start. `spawn` creates a
  thread, `join` (written with `k::cells!`) removes one, and a search of the
  race reaches both `return 2;` and `return 3;` on both routes;
- `objects`: a `cell_type = "Set"` collection whose instances are created
  with template defaults, updated in place, removed, and matched exactly;
- `queue`: a `cell_type = "List"` collection where `enqueue` appends at
  the back and `dequeue` removes the front, so jobs leave first in first
  out; the emitted back rewrite names the leading instances `_Instances1:Bag`;
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
  both ends, and a created Map instance without its key. A `?` template that
  reads a configuration variable without `initial` is accepted with a
  pinned warning.

Run it from the repository root; `--record` rewrites the measured pins after
every step passes, and `--refresh-reference` reruns Java K instead of
replaying the per-user reference cache.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
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
from support.tools import checkout_scratch, z3_environment  # noqa: E402


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
    )
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
PUSH_REFERENCE = (
    '#[k::rule(label = "push")]\n'
    "pub fn push(\n"
    "    s: k::Term<k::builtin::List>,\n"
    "    f: crate::Frame,\n"
    "    k::cells! {\n"
    "        k : k::configuration::KCell(crate ::Cmd::Push(), tail @ ..), stack :\n"
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
    "            counter: Some(k::configuration::Cell::new(0)),\n",
    "        k : k::configuration::KCell(crate ::Cmd::Enable(), tail @ ..), counter : None,\n",
    "        k : k::configuration::KCell(..tail), counter : Some(k::configuration::Cell(0)),\n",
    "        k : k::configuration::KCell(..tail), mark : Some(k::fragment![crate ::Mark { seen\n",
)

THREADS = Fixture(MANIFEST, "krs-configuration-cells-threads")
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
    "        <k> spawn { Body:Stmt } => N:Int ... </k>\n"
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

QUEUE = Fixture(MANIFEST, "krs-configuration-cells-queue")
QUEUE_PROGRAMS = (
    Program("dequeue", "enqueue 1 enqueue 2 enqueue 3 dequeue", "accepted", "1"),
    Program("fifo", "enqueue 1 enqueue 2 enqueue 3 drop drop dequeue", "accepted", "3"),
    Program("front", "enqueue 4 enqueue 5 front", "accepted", "4"),
    Program("pop", "enqueue 4 enqueue 5 enqueue 6 pop", "accepted", "6"),
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
)

# Accepted, with a pinned warning: a `?` template that reads a configuration
# variable without `initial` starts present in K.
WARNING = "optional-config-var"
WARNING_CODE = "warning[krs::analysis::collection-config-var-without-initial]"


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
    emitted = harness.emit(GROUPS)
    source = emitted.source.read_text(encoding="utf-8")
    for rule in (PUSH_K, POP_K):
        if rule not in source:
            raise GateError(f"emitted K changed a whole-cell rule:\n{source}")
    harness.compare(emitted, GROUPS_PROGRAMS, sort="Stmt")
    for program in GROUPS_PROGRAMS:
        final_cells(harness, emitted, program, {"pc": "3", "gas": "10"})


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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 configuration-cells ledger")

    target = checkout_scratch() / "configuration-cells-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target), "CARGO_TERM_COLOR": "never"}
    krs = build(environment, target=target)
    gate = krs_gate.configured_or_build(target)
    check_packages("configuration-cells", krs=krs, env=environment, target_dir=target)

    with tempfile.TemporaryDirectory(prefix="krs-configuration-cells-") as temporary:
        workspace = Path(temporary)
        harness = FixtureGate(
            "configuration-cells", pins, workspace, krs, gate, environment,
            refresh=arguments.refresh_reference,
            divergences=pins.get("known_divergences", {}),
        )

        verify_framing(harness)
        print("PASS framing: burn frames k on both routes, done ends with fuel 0 and acc 6, report writes 6")

        verify_groups(harness)
        print("PASS groups: push/pop, save/restore and call/ret each end with pc 3 and gas 10, report writes 310")

        verify_optional(harness)
        print("PASS optional: enable creates, inc/dec update, read reads, disable deletes; a second enable is stuck")

        verify_threads(harness)
        print("PASS threads: spawn creates and join removes Map instances; the race reaches return 2 and return 3 on both routes")

        harness.compare(verify_emitted(harness, OBJECTS, OBJECTS_K), OBJECTS_PROGRAMS, sort="Stmt")
        print("PASS objects: Set instances are created with defaults, updated, removed, and matched exactly")

        harness.compare(verify_emitted(harness, QUEUE, QUEUE_K), QUEUE_PROGRAMS, sort="Stmt")
        print("PASS queue: enqueue appends at the back and dequeue removes the front, first in first out")

        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-configuration-cells-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

        manifest = materialize(WARNING, workspace)
        process = harness.check(Fixture(manifest, f"krs-configuration-cells-{WARNING}"))
        warnings = diagnostic_lines(process.stderr)
        if not any(line.startswith(WARNING_CODE) for line in warnings):
            raise GateError(f"{WARNING}: krs check did not warn {WARNING_CODE}:\n{process.stderr}")
        harness.pins.expect(("warnings", WARNING), warnings)
        print(f"PASS warning {WARNING}: {warnings[0]}")

    pins.finish("configuration-cells")
    print("PASS configuration-cells")
    return 0


if __name__ == "__main__":
    entry("configuration-cells", main, errors=(OSError,))
