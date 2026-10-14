#!/usr/bin/env python3
"""Sorts-and-algebra feature gate: sort-parametric productions (KF-027).

A K sort parameter is a Rust type parameter `S: ?Sized` of a production
struct, emitted as K's `syntax {S} S ::= ..`. Each fixture package runs
natively through k-rust and through Java K, and the outcomes must agree:

- `functions` (F1, F3): `Choose<S>` is K's
  `syntax {S} S ::= choose(Bool, S, S) [function, total]`, with one equation
  per instance at Int, Bool, and the user sort `Exp`, each fixing its instance
  with a turbofish that the emitted K writes as strict casts,
  `choose ( true , A::Int , _::Int ) => A:Int`. A machine rule calls `choose`
  without a turbofish, so `go(7, true)` sets `<n>` to `7` and `<bit>` to
  `false`, and `go(7, false)` sets them to `0` and `true`; a readable clause
  builds `Choose::<Exp> { .. }`, which `krs expand` renders with the marker
  `dyn crate::ExpSort`, so `pick(true, 1, 2)` is `1` and `pick(false, 1, 2)`
  is `2`. The programs agree natively and on Java K's Haskell backend from the
  emitted K, and in both routes' KORE (read through `krs-gate`) the
  equations apply `choose` at exactly the instances Int, Bool, and Exp.
  `krs build --backend llvm` refuses the definition with the pinned
  `krs::capability::unavailable` message: K's llvm-kompile crashes on
  parametric function equations, in Java K's KORE and in k-rust's alike
  (upstream k/llvm-kompile-parametric-function-segfault);
- `constructors` (F2): `Wrap<S>` is the value-building schema
  `syntax {S} S ::= wrap(S)`. `go(7)` builds `wrap(v(7))`, at `Val`, and a
  rule on `Wrap::<Val>` makes it `v(-8)`; `fin(7)` builds `wrap(done(7))`, at
  `Done`, and a rule on `Wrap::<Done>` unwraps it to `done(7)`. The programs
  agree natively and on Java K's LLVM backend; the sidecar records the
  `ParametricConstructorSchema` requirement, which Java K's Haskell backend
  lacks (upstream haskell-backend/parametric-constructor-rejected-at-validation);
- negative fixtures, each failing `krs check` with a pinned diagnostic: a
  lifetime, const, unbounded, otherwise bounded, defaulted, or unused sort
  parameter, a where clause, generics on an enum family, on a sort trait, and
  on an equation, a turbofish with a lifetime or the wrong arity, a parameter
  named like a sort, an alias marker on a parametric production, a parametric
  constructor instantiated at Int, an equation head without a turbofish or
  with one that disagrees with its declared sort, a non-variable head
  argument below the instance, a head binder declared above it, an
  undetermined instance, and (F4) a head whose binders all sit below the
  turbofish instance, which k-rust would solve differently
  (`krs::analysis::native-instance`).

Run it from the repository root; `--record` rewrites the measured pins after
every step passes, and `--refresh-reference` reruns Java K instead of
replaying the per-user reference cache.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry, krs_gate, lsp  # noqa: E402
from support.fixture_gate import (  # noqa: E402
    ACCEPTED, JAVA_TOOLS, Emitted, Fixture, FixtureGate, Program, diagnostic_lines, java_run_outcome,
    printed_cells,
)
from support.krs import build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import Key, Output, Pin, Snapshot, add_refresh_argument, repository_inputs  # noqa: E402
from support.tools import checkout_scratch, rust_analyzer, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
PINS = HERE / "pins.json"
FIXTURES = HERE / "fixtures"

FUNCTIONS = Fixture(MANIFEST, "krs-sorts-algebra-functions")
FUNCTIONS_PROGRAMS = (
    Program("go-true", "go(7, true)", "accepted", ".K", cells=(("n", "7"), ("bit", "false"))),
    Program("go-false", "go(7, false)", "accepted", ".K", cells=(("n", "0"), ("bit", "true"))),
    Program("pick-true", "pick(true, 1, 2)", "accepted", "1"),
    Program("pick-false", "pick(false, 1, 2)", "accepted", "2"),
)
# Each instance's equations: K's text solver and k-rust's both fix them.
CHOOSE_INSTANCES = "Bool\nExp\nInt\n"

CONSTRUCTORS = Fixture(MANIFEST, "krs-sorts-algebra-constructors")
CONSTRUCTORS_PROGRAMS = (
    Program("go", "go(7)", "accepted", "v(-8)"),
    Program("fin", "fin(7)", "accepted", "done(7)"),
)

# rust-analyzer navigates from a turbofish head to the parametric production
# and from the turbofish's sort marker to its sort declaration.
LSP_PROBES = (
    ("turbofish head", "k::term![Choose::<dyn ExpSort> {", "Choose", "pub struct Choose<S: ?Sized> {"),
    ("turbofish marker", "k::term![Choose::<dyn ExpSort> {", "ExpSort", "k::sorts! {"),
    ("readable turbofish marker", "pick: Pick(c, x, y) => crate::Choose::<Exp>", "Exp>", "    Exp;"),
)

NEGATIVE = (
    "lifetime-parameter",
    "const-parameter",
    "missing-unsized",
    "parameter-bound",
    "parameter-default",
    "where-clause",
    "unused-parameter",
    "enum-generics",
    "sort-generics",
    "generic-equation",
    "turbofish-lifetime",
    "turbofish-arity",
    "parameter-sort-name",
    "parametric-alias",
    "domain-instance",
    "missing-turbofish",
    "turbofish-disagrees",
    "head-argument-below",
    "head-binder-sort",
    "undetermined-instance",
    "native-instance",
    "turbofish-alias",
    "readable-turbofish-marker",
)


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


def emitted_fragments(emitted: Emitted, fragments: tuple[str, ...]) -> None:
    source = emitted.source.read_text(encoding="utf-8")
    for fragment in fragments:
        if fragment not in source:
            raise GateError(f"{emitted.fixture.package}: emitted K omits {fragment!r}")


def choose_instances(harness: FixtureGate, kore: Path) -> str:
    """The distinct instances at which a KORE definition applies `choose`, one per line."""

    instances = krs_gate.kore_instances(harness.gate, kore, ["choose"], environment=harness.environment)
    return "".join(
        f"{' '.join(instance)}\n" for instance in sorted({tuple(instance) for instance in instances.get("choose", [])})
    )


def instance_reducer(harness: FixtureGate, package: str):
    """Reduce Java K's kompiled `definition.kore` to its `choose` instances."""

    def reduce(text: str) -> str:
        kore = harness.workspace / "kore-instances" / f"{package}.java.kore"
        kore.write_text(text, encoding="utf-8")
        return choose_instances(harness, kore)

    return reduce


def java_haskell_outcomes(
    harness: FixtureGate, emitted: Emitted, programs: tuple[Program, ...],
) -> tuple[dict[str, dict[str, object]], str]:
    """Kompile the emitted K with Java K's Haskell backend, run `programs`, and return the
    outcomes with the `choose` instances of the kompiled `definition.kore`."""

    package = emitted.fixture.package
    directory = harness.workspace / "haskell-programs" / package
    directory.mkdir(parents=True, exist_ok=True)
    k = Snapshot(
        f"{harness.label}/{package}-haskell",
        Key(tools=JAVA_TOOLS, inputs=repository_inputs([])),
        workspace=harness.workspace, refresh=harness.refresh,
        pin=Pin(harness.pins, f"{package}-haskell"),
    )
    compiled = harness.workspace / "kompiled-haskell" / package
    instances = harness.workspace / "kore-instances" / f"{package}.java.txt"
    instances.parent.mkdir(parents=True, exist_ok=True)
    kompiled = k.run(
        "kompile/definition", "kompile",
        [
            emitted.source, "--main-module", emitted.main_module,
            "--syntax-module", emitted.syntax_module,
            "--backend", "haskell", "--output-definition", compiled,
        ],
        timeout=900,
        outputs=(Output(instances, instance_reducer(harness, package), lambda: compiled / "definition.kore"),),
    )
    if kompiled.returncode != 0:
        raise GateError(f"{package}: kompile --backend haskell rejected the emitted definition:\n{kompiled.stderr}")
    outcomes: dict[str, dict[str, object]] = {}
    for program in programs:
        path = directory / f"{program.name}.pgm"
        path.write_text(program.text + "\n", encoding="utf-8")
        executed = k.run(f"krun/{program.name}", "krun", ["--definition", compiled, path], timeout=300)
        outcomes[program.name] = {"parse": ACCEPTED, "run": java_run_outcome(executed)}
        if program.cells:
            outcomes[program.name]["cells"] = printed_cells(executed.stdout, program.cells)
    print(f"PASS sorts-algebra {package} Haskell reference snapshot: {k.finish()}")
    return outcomes, instances.read_text(encoding="utf-8")


def verify_functions(harness: FixtureGate) -> None:
    """Parametric functions run natively and on Java Haskell; LLVM refuses them."""

    harness.check(FUNCTIONS)
    expansion = "".join(harness.expand(FUNCTIONS).split())
    if "crate::Choose::<dyncrate::ExpSort>(" not in expansion:
        raise GateError(f"{FUNCTIONS.package}: krs expand does not render the readable turbofish as its marker")
    emitted = harness.emit(FUNCTIONS)
    emitted_fragments(emitted, (
        'syntax {S} S ::= "choose" "(" Bool "," S "," S ")" [symbol(choose), function, total]',
        "rule choose ( true , A::Int , _::Int ) => A:Int [label(",
        "rule choose ( false , _::Int , B::Int ) => B:Int [label(",
        "rule choose ( true , A::Bool , _::Bool ) => A:Bool [label(",
        "rule choose ( true , A::Exp , _::Exp ) => A:Exp [label(",
        "<n> _ => choose ( B:Bool , I:Int , 0 ) </n>",
        "<bit> _ => choose ( B:Bool , false , true ) </bit>",
        "<k> pick ( C:Bool , X:Exp , Y:Exp ) => choose ( C:Bool , X:Exp , Y:Exp ) ... </k>",
    ))
    native = harness._native_outcomes(emitted, FUNCTIONS_PROGRAMS)  # noqa: SLF001
    java, java_instances = java_haskell_outcomes(harness, emitted, FUNCTIONS_PROGRAMS)
    observed: dict[str, dict[str, object]] = {}
    for program in FUNCTIONS_PROGRAMS:
        expected: dict[str, object] = {"parse": program.parse, "run": program.run}
        if program.cells:
            expected["cells"] = dict(program.cells)
        routes = {"native": native[program.name], "java": java[program.name]}
        if routes["native"] != routes["java"] or routes["native"] != expected:
            raise GateError(f"{FUNCTIONS.package} {program.name}: observed {routes}, expected {expected}")
        observed[program.name] = routes["native"]
    harness.pins.expect(("outcomes", FUNCTIONS.package), observed)

    directory = harness.workspace / "native-haskell" / FUNCTIONS.package
    harness._krs(FUNCTIONS, "build", "--backend", "haskell", "--output", directory)  # noqa: SLF001
    native_instances = choose_instances(harness, directory / "definition.kore")
    for route, instances in (("native", native_instances), ("Java Haskell", java_instances)):
        if instances != CHOOSE_INSTANCES:
            raise GateError(f"{FUNCTIONS.package}: {route} KORE applies choose at {instances!r}, expected {CHOOSE_INSTANCES!r}")
    harness.pins.expect(("kore_instances", FUNCTIONS.package), native_instances)

    refused = harness._krs(  # noqa: SLF001
        FUNCTIONS, "build", "--backend", "llvm", "--output",
        harness.workspace / "native-llvm" / FUNCTIONS.package, check=False,
    )
    if refused.returncode == 0:
        raise GateError(f"{FUNCTIONS.package}: krs build --backend llvm accepted parametric function equations")
    lines = diagnostic_lines(refused.stderr)
    if not lines or "krs::capability::unavailable" not in lines[0]:
        raise GateError(f"{FUNCTIONS.package}: krs build --backend llvm failed without the capability refusal:\n{refused.stderr}")
    harness.pins.expect(("diagnostics", "functions-llvm"), lines)


def verify_constructors(harness: FixtureGate) -> None:
    """Parametric constructors run natively and on Java LLVM; the sidecar records the schema."""

    harness.check(CONSTRUCTORS)
    harness.expand(CONSTRUCTORS)
    emitted = harness.emit(CONSTRUCTORS)
    emitted_fragments(emitted, (
        'syntax {S} S ::= "wrap" "(" S ")" [symbol(wrap)]',
        "<k> go ( N:Int ) => wrap ( v ( N:Int ) ) ... </k>",
        "rule wrap ( v ( N:Int ) ) => v ( N:Int -Int 15 ) [label(unwrap-val)]",
        "rule wrap ( D::Done ) => D:Done [label(unwrap-done)]",
    ))
    harness.compare(emitted, CONSTRUCTORS_PROGRAMS, sort="Pgm")
    sidecar = json.loads((emitted.directory / "symbols.json").read_text(encoding="utf-8"))
    requirements = [
        requirement for requirement in sidecar.get("capability_requirements", [])
        if requirement.get("feature") == "ParametricConstructorSchema"
    ]
    if [requirement.get("symbol") for requirement in requirements] != ["wrap"]:
        raise GateError(f"{CONSTRUCTORS.package}: the sidecar records {requirements}, not the wrap schema")
    harness.pins.expect(("capability_requirements", CONSTRUCTORS.package), requirements)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 sorts-algebra ledger")

    target = checkout_scratch() / "sorts-algebra-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target), "CARGO_TERM_COLOR": "never"}
    krs = build(environment)
    gate = krs_gate.configured_or_build()
    check_packages("sorts-algebra", krs=krs, env=environment, target_dir=target)
    analyzer = rust_analyzer()
    lsp.probe(
        HERE / "packages" / "functions",
        LSP_PROBES,
        diagnostic_timeout=600,
        environment={
            **environment,
            "CARGO_TARGET_DIR": os.fspath(target / "lsp"),
            "PATH": os.pathsep.join([os.fspath(analyzer.parent), os.environ["PATH"]]),
        },
        timeout=900,
    )
    print("PASS sorts-algebra rust-analyzer: turbofish heads and markers navigate to their declarations")

    with tempfile.TemporaryDirectory(prefix="krs-sorts-algebra-") as temporary:
        workspace = Path(temporary)
        harness = FixtureGate(
            "sorts-algebra", pins, workspace, krs, gate, environment,
            refresh=arguments.refresh_reference,
        )

        verify_functions(harness)
        print("PASS functions: choose at Int, Bool, and Exp agrees natively and on Java Haskell, both KORE at each instance; LLVM refuses it")

        verify_constructors(harness)
        print("PASS constructors: wrap at Val and Done agrees natively and on Java LLVM; the sidecar records the schema")

        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-sorts-algebra-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("sorts-algebra")
    print("PASS sorts-algebra")
    return 0


if __name__ == "__main__":
    entry("sorts-algebra", main, errors=(OSError,))
