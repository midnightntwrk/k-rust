#!/usr/bin/env python3
"""Patterns-and-functions feature gate: `name @ pattern` (KF-029) and `A | B` (KF-030).

Each fixture package runs natively through k-rust and through Java K, and
the outcomes must agree:

- `aliases`: `name @ pattern` is K's `#as`. A readable clause
  `Dup(p @ Pair(a, b))` reuses the matched pair, so `dup(pair(1, 2))` is
  `pair(pair(1, 2), pair(2, 1))`; a `cells!` rule whose binder list declares
  the alias before the binders inside it turns `wrap(pair(1, 2))` into
  `pair(1, pair(1, 2))`; an equation that aliases the tail it returns makes
  `rest(cons(1, cons(2, nil)))` `cons(2, nil)`, and its `owise` fallback makes
  `rest(cons(1, nil))` `nil`. The emitted K writes each alias last and
  parenthesised, `( pair ( A:Exp , B:Exp ) #as P:Exp )`; `krs expand` is
  byte-pinned. The same programs run on Java K's LLVM backend from the
  hand-written `reference.k`, with the same outcomes;
- `alternatives`: `A | B` is K's `#Or`, always parenthesised and left to
  right. A readable clause `Color(Red() | Green() | Blue())` makes
  `color(green())` `1` and leaves `color(3)` stuck; a readable clause whose
  whole subject is `Red() | Green() | Blue()` makes `red()` `1`; an
  equation `code(( red() #Or green() #Or blue() ))` makes `code(blue())` `1`;
  and `Pick(Pair(x, Red()) | Pair(x, Green()))`, whose alternatives both bind
  `x`, makes `pick(pair(5, green()))` `5`. The programs agree natively, on
  Java K's LLVM backend from the emitted K and from `reference.k`, and on
  Java K's Haskell backend from the emitted K;
- negative fixtures: `ref` on an alias, an alias inside its own subpattern,
  an alias of a `..` remainder, `@` in a result, an alias of a whole rule
  subject, alternatives binding different names, alternatives that can bind
  differently (K's #Or would be ambiguous), `|` in a result, and `|` beside a
  `..` remainder, each fail `krs check` with a pinned diagnostic.

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
from support.fixture_gate import (  # noqa: E402
    ACCEPTED, JAVA_TOOLS, Emitted, Fixture, FixtureGate, Program, java_run_outcome,
)
from support.krs import build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import Key, Pin, Snapshot, add_refresh_argument, repository_inputs  # noqa: E402
from support.tools import checkout_scratch, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
PINS = HERE / "pins.json"
FIXTURES = HERE / "fixtures"
REFERENCE = HERE / "reference.k"

ALIASES = Fixture(MANIFEST, "krs-patterns-functions-aliases")
ALIASES_PROGRAMS = (
    Program("dup", "dup(pair(1, 2))", "accepted", "pair(pair(1, 2), pair(2, 1))"),
    Program("wrap", "wrap(pair(1, 2))", "accepted", "pair(1, pair(1, 2))"),
    Program("rest-long", "rest(cons(1, cons(2, nil)))", "accepted", "cons(2, nil)"),
    Program("rest-short", "rest(cons(1, nil))", "accepted", "nil"),
)
# The hand-written K definition the emitted one must behave like.
ALIASES_REFERENCE = Fixture(MANIFEST, "krs-patterns-functions-aliases-reference")

ALTERNATIVES = Fixture(MANIFEST, "krs-patterns-functions-alternatives")
ALTERNATIVES_PROGRAMS = (
    Program("rgb", "color(green())", "accepted", "1"),
    Program("rgb-stuck", "color(3)", "accepted", "color(3)"),
    Program("primary", "red()", "accepted", "1"),
    Program("code-rgb", "code(blue())", "accepted", "1"),
    Program("pick", "pick(pair(5, green()))", "accepted", "5"),
)
ALTERNATIVES_REFERENCE = Fixture(MANIFEST, "krs-patterns-functions-alternatives-reference")

NEGATIVE = (
    "alias-ref",
    "alias-inside-itself",
    "alias-remainder",
    "alias-in-result",
    "alias-whole-subject",
    "or-unequal-binders",
    "or-ambiguous",
    "or-in-result",
    "or-remainder",
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


def unspaced(outcome: dict[str, object]) -> dict[str, object]:
    return {
        key: "".join(value.split()) if isinstance(value, str) else value
        for key, value in outcome.items()
    }


def agree_with_reference(
    harness: FixtureGate,
    workspace: Path,
    reference_fixture: Fixture,
    main_module: str,
    programs: tuple[Program, ...],
    observed: dict[str, dict[str, object]],
) -> None:
    """Run `programs` on Java LLVM from `reference.k` and require the observed outcomes."""

    reference_directory = workspace / "reference" / reference_fixture.package
    reference_directory.mkdir(parents=True)
    shutil.copyfile(REFERENCE, reference_directory / "definition.k")
    reference = Emitted(reference_fixture, reference_directory, main_module)
    java = harness._java_outcomes(reference, programs, sort="Exp")  # noqa: SLF001
    for program in programs:
        # reference.k declares no formats, so K prints its terms spaced out.
        if unspaced(java[program.name]) != unspaced(observed[program.name]):
            raise GateError(
                f"reference.k {program.name}: Java K observed {java[program.name]}, "
                f"the emitted definition {observed[program.name]}"
            )


def java_haskell_outcomes(
    harness: FixtureGate, emitted: Emitted, programs: tuple[Program, ...],
) -> dict[str, dict[str, object]]:
    """Kompile the emitted K with Java K's Haskell backend and run `programs` on it."""

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
    kompiled = k.run(
        "kompile/definition", "kompile",
        [
            emitted.source, "--main-module", emitted.main_module,
            "--syntax-module", emitted.syntax_module,
            "--backend", "haskell", "--output-definition", compiled,
        ],
        timeout=900,
    )
    if kompiled.returncode != 0:
        raise GateError(f"{package}: kompile --backend haskell rejected the emitted definition:\n{kompiled.stderr}")
    outcomes: dict[str, dict[str, object]] = {}
    for program in programs:
        path = directory / f"{program.name}.pgm"
        path.write_text(program.text + "\n", encoding="utf-8")
        executed = k.run(f"krun/{program.name}", "krun", ["--definition", compiled, path], timeout=300)
        outcomes[program.name] = {"parse": ACCEPTED, "run": java_run_outcome(executed)}
    print(f"PASS patterns-functions {package} Haskell reference snapshot: {k.finish()}")
    return outcomes


def verify_alternatives(harness: FixtureGate, workspace: Path) -> None:
    """Or-patterns run natively, on Java LLVM from the emitted K and from `reference.k`, and on Java Haskell."""

    harness.check(ALTERNATIVES)
    harness.expand(ALTERNATIVES)
    emitted = harness.emit(ALTERNATIVES)
    emitted_fragments(emitted, (
        "<k> color ( ( red ( ) #Or green ( ) #Or blue ( ) ) ) => 1 ... </k>",
        "<k> ( red ( ) #Or green ( ) #Or blue ( ) ) => 1 ... </k>",
        "<k> pick ( ( pair ( X:Exp , red ( ) ) #Or pair ( X:Exp , green ( ) ) ) ) => X:Exp ... </k>",
        "rule code ( ( red ( ) #Or green ( ) #Or blue ( ) ) ) => 1 [label(",
    ))
    observed = harness.compare(emitted, ALTERNATIVES_PROGRAMS, sort="Exp")
    agree_with_reference(
        harness, workspace, ALTERNATIVES_REFERENCE, "ALTERNATIVES-REFERENCE",
        ALTERNATIVES_PROGRAMS, observed,
    )
    haskell = java_haskell_outcomes(harness, emitted, ALTERNATIVES_PROGRAMS)
    for program in ALTERNATIVES_PROGRAMS:
        if haskell[program.name] != observed[program.name]:
            raise GateError(
                f"{ALTERNATIVES.package} {program.name}: Java K Haskell observed "
                f"{haskell[program.name]}, the native and LLVM routes {observed[program.name]}"
            )


def verify_aliases(harness: FixtureGate, workspace: Path) -> None:
    """Aliases run natively, on Java LLVM from the emitted K, and from `reference.k`."""

    harness.check(ALIASES)
    harness.expand(ALIASES)
    emitted = harness.emit(ALIASES)
    emitted_fragments(emitted, (
        "<k> dup ( ( pair ( A:Exp , B:Exp ) #as P:Exp ) ) => pair ( P:Exp , pair ( B:Exp , A:Exp ) ) ... </k>",
        "<k> wrap ( ( pair ( A:Exp , _ ) #as P:Exp ) ) ~> Tail:K => pair ( A:Exp , P:Exp ) ~> Tail:K </k>",
        "rule rest ( cons ( _ , ( cons ( _ , _ ) #as More:Seq ) ) ) => More:Seq [label(",
    ))
    observed = harness.compare(emitted, ALIASES_PROGRAMS, sort="Exp")
    agree_with_reference(
        harness, workspace, ALIASES_REFERENCE, "ALIASES-REFERENCE", ALIASES_PROGRAMS, observed,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 patterns-functions ledger")

    target = checkout_scratch() / "patterns-functions-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target), "CARGO_TERM_COLOR": "never"}
    krs = build(environment, target=target)
    gate = krs_gate.configured_or_build(target)
    check_packages("patterns-functions", krs=krs, env=environment, target_dir=target)

    with tempfile.TemporaryDirectory(prefix="krs-patterns-functions-") as temporary:
        workspace = Path(temporary)
        harness = FixtureGate(
            "patterns-functions", pins, workspace, krs, gate, environment,
            refresh=arguments.refresh_reference,
            divergences=pins.get("known_divergences", {}),
        )

        verify_aliases(harness, workspace)
        print("PASS aliases: dup, wrap, and rest agree natively, on Java LLVM, and with reference.k")

        verify_alternatives(harness, workspace)
        print("PASS alternatives: rgb, primary, code-rgb, and pick agree natively, on Java LLVM, with reference.k, and on Java Haskell")

        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-patterns-functions-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("patterns-functions")
    print("PASS patterns-functions")
    return 0


if __name__ == "__main__":
    entry("patterns-functions", main, errors=(OSError,))
