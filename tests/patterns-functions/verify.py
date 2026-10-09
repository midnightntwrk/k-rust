#!/usr/bin/env python3
"""Patterns-and-functions feature gate: `name @ pattern` (KF-029), `A | B` (KF-030), `k::matches!` (KF-031), and `let` blocks (KF-032).

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
- `matches`: `k::matches!(t, P)` is K's `( P :=K T )`, a Bool, with the
  pattern first and always parenthesised. Two readable clauses guarded by
  `k::matches!(e, Pair(_, _))` and its `bool::not` make `isPair(pair(1, 2))`
  `true` and `isPair(3)` `false`; guards `Pair(p @ Pair(_, _), p)` make
  `boxed(pair(pair(1, 2), pair(1, 2)))` `true` and
  `boxed(pair(pair(1, 2), pair(2, 1)))` `false`; the equation
  `twin(E) => ( pair ( X , X ) :=K E )`, whose local binder `x` occurs twice,
  makes `twin(pair(1, 1))` `true` and `twin(pair(1, 2))` `false`; and
  alternatives make `known(unit())` `true` and `known(3)` `false`. The
  programs agree natively, on Java K's LLVM backend from the emitted K and
  from `reference.k` (whose negations use `:/=K`), and on Java K's Haskell
  backend;
- `lets`: a block `{ let P = A; B }` is K's `( #let P = A #in B )`, always
  parenthesised, which K defines as `#fun(P => B)(A)`. A readable clause
  `Swap { e } => { let Pair(x, y) = e; Pair(y, x) }` makes `swap(pair(1, 2))`
  `pair(2, 1)`, and an equation whose body has a `let` statement makes
  `swapPair(pair(1, 2))` `pair(2, 1)`; two ascribed lets nest to the right,
  `( #let M:Int = E #in ( #let N:Int = M +Int 1 #in .. ) )`, so `scale(3)` is
  `12`; a `let` that shadows the rule's `e` takes a distinct name, so
  `shadow(1)` is `pair(pair(1, 1), 1)`; and a block as a condition makes
  `positive(5)` `1`. The defined programs agree natively, on Java K's LLVM
  backend from the emitted K and from `reference.k` (which writes
  `#fun(P => B)(A)`), and on Java K's Haskell backend. A refutable pattern
  that fails, `swap(3)` and `swapPair(3)`, and a failed ascription,
  `scale(pair(1, 2))`, make the term undefined on Java K's LLVM backend from
  both sources; natively the failed ascription leaves the generated lambda's
  application stuck (a pinned divergence), and the failed constructor
  patterns, on which the pinned native backend does not terminate, run on
  Java K only;
- negative fixtures: `ref` on an alias, an alias inside its own subpattern,
  an alias of a `..` remainder, `@` in a result, an alias of a whole rule
  subject, alternatives binding different names, alternatives that can bind
  differently (K's #Or would be ambiguous), `|` in a result, `|` beside a
  `..` remainder, a `k::matches!` name that shadows a rule binder, one read
  once, an `if` guard, std's bare `matches!`, `k::matches!` in a pattern, `@`
  in a `k::matches!` in a result, a pattern whose sort cannot meet its
  subject's, and `k::matches!` in a claim (the pinned native prover cannot
  resolve `:=K` there), a term block whose result ends in a semicolon, `|`
  and `@` in a `let` pattern, a block in a pattern, a let-bound name used
  outside its block, a `let` pattern whose sort cannot meet its value's, and
  a `let` in a claim, each fail `krs check` with a pinned diagnostic.

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
    ACCEPTED, JAVA_TOOLS, Emitted, Fixture, FixtureGate, Program, java_run_outcome, printed_cells,
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

MATCHES = Fixture(MANIFEST, "krs-patterns-functions-matches")
MATCHES_PROGRAMS = (
    Program("is-pair", "isPair(pair(1, 2))", "accepted", "true"),
    Program("not-pair", "isPair(3)", "accepted", "false"),
    Program("boxed", "boxed(pair(pair(1, 2), pair(1, 2)))", "accepted", "true"),
    Program("unboxed", "boxed(pair(pair(1, 2), pair(2, 1)))", "accepted", "false"),
    Program("twin", "twin(pair(1, 1))", "accepted", "true"),
    Program("not-twin", "twin(pair(1, 2))", "accepted", "false"),
    Program("known", "known(unit())", "accepted", "true"),
    Program("unknown", "known(3)", "accepted", "false"),
)
MATCHES_REFERENCE = Fixture(MANIFEST, "krs-patterns-functions-matches-reference")

LETS = Fixture(MANIFEST, "krs-patterns-functions-lets")
LETS_PROGRAMS = (
    Program("swap", "swap(pair(1, 2))", "accepted", "pair(2, 1)"),
    Program("swap-pair", "swapPair(pair(1, 2))", "accepted", "pair(2, 1)"),
    Program("scale", "scale(3)", "accepted", "12"),
    Program("shadow", "shadow(1)", "accepted", "pair(pair(1, 1), 1)"),
    Program("positive", "positive(5)", "accepted", "1"),
    Program("scale-refuted", "scale(pair(1, 2))", "accepted", "undefined"),
    Program("swap-refuted", "swap(3)", "accepted", "undefined"),
    Program("swap-pair-refuted", "swapPair(3)", "accepted", "undefined"),
)
# The pinned native backend does not terminate on a `#let` whose constructor
# pattern fails to match a concrete value (its execute request exceeds the
# session timeout), so these programs run on Java K only; the failed
# ascription `scale-refuted` is a pinned divergence (native leaves the
# generated lambda's application stuck).
LETS_JAVA_ONLY = ("swap-refuted", "swap-pair-refuted")
# Natively stuck programs, whose native outcome is the stuck computation.
LETS_STUCK = ("scale-refuted",)
# Java K's Haskell backend prints an undefined term rather than aborting, so
# only the defined programs run there.
LETS_HASKELL_PROGRAMS = tuple(program for program in LETS_PROGRAMS if program.run != "undefined")
LETS_REFERENCE = Fixture(MANIFEST, "krs-patterns-functions-lets-reference")

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
    "matches-shadow",
    "matches-unread",
    "matches-guard",
    "matches-std",
    "matches-lhs",
    "matches-alias-result",
    "matches-sort",
    "matches-claim",
    "let-shape",
    "let-or",
    "let-alias",
    "let-pattern",
    "let-scope",
    "let-sort",
    "let-claim",
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


def verify_matches(harness: FixtureGate, workspace: Path) -> None:
    """Shape tests run natively, on Java LLVM from the emitted K and from `reference.k`, and on Java Haskell."""

    harness.check(MATCHES)
    harness.expand(MATCHES)
    emitted = harness.emit(MATCHES)
    emitted_fragments(emitted, (
        "requires ( pair ( _ , _ ) :=K E:Exp )",
        "requires notBool ( pair ( _ , _ ) :=K E:Exp )",
        "requires ( pair ( ( pair ( _ , _ ) #as P:Exp ) , P:Exp ) :=K E:Exp )",
        "rule twin ( E:Exp ) => ( pair ( X:Exp , X:Exp ) :=K E:Exp ) [label(",
        "rule known ( E:Exp ) => ( ( pair ( _ , _ ) #Or unit ( ) ) :=K E:Exp ) [label(",
    ))
    observed = harness.compare(emitted, MATCHES_PROGRAMS, sort="Exp")
    agree_with_reference(
        harness, workspace, MATCHES_REFERENCE, "MATCHES-REFERENCE", MATCHES_PROGRAMS, observed,
    )
    haskell = java_haskell_outcomes(harness, emitted, MATCHES_PROGRAMS)
    for program in MATCHES_PROGRAMS:
        if haskell[program.name] != observed[program.name]:
            raise GateError(
                f"{MATCHES.package} {program.name}: Java K Haskell observed "
                f"{haskell[program.name]}, the native and LLVM routes {observed[program.name]}"
            )


def compare_lets(harness: FixtureGate, emitted: Emitted) -> dict[str, dict[str, object]]:
    """Run the let programs on Java K, and those that terminate natively also natively.

    This is `FixtureGate.compare` with the programs of `LETS_JAVA_ONLY` kept
    off the native route; each program's outcome is the agreed one, or its
    pinned divergence, or (Java only) the expected one.
    """

    native_programs = tuple(
        program for program in LETS_PROGRAMS if program.name not in LETS_JAVA_ONLY + LETS_STUCK
    )
    native = harness._native_outcomes(emitted, native_programs)  # noqa: SLF001
    with krs_gate.Session(harness.gate, environment=harness.environment) as session:
        session.load(emitted.definition_ir, emitted.main_module)
        for program in LETS_PROGRAMS:
            if program.name in LETS_STUCK:
                printed = session.exec_run(program=program.text, print_style="pretty")["printed"]["text"]
                native[program.name] = {
                    "parse": ACCEPTED,
                    "run": f"stuck: {printed_cells(printed, (('k', ''),))['k']}",
                }
    java = harness._java_outcomes(emitted, LETS_PROGRAMS, sort="Exp")  # noqa: SLF001
    known = harness.divergences.get(LETS.package, {})
    observed: dict[str, dict[str, object]] = {}
    for program in LETS_PROGRAMS:
        expected = {"parse": program.parse, "run": program.run}
        if program.name in LETS_JAVA_ONLY:
            if java[program.name] != expected:
                raise GateError(f"{LETS.package} {program.name}: Java K observed {java[program.name]}, expected {expected}")
            observed[program.name] = java[program.name]
            continue
        routes = {"native": native[program.name], "java": java[program.name]}
        divergence = known.get(program.name)
        if divergence is not None:
            if routes != divergence:
                raise GateError(
                    f"{LETS.package} {program.name}: pinned divergence changed: expected {divergence}, observed {routes}"
                )
            observed[program.name] = java[program.name]
            continue
        if routes["native"] != routes["java"] or routes["native"] != expected:
            raise GateError(f"{LETS.package} {program.name}: observed {routes}, expected {expected}")
        observed[program.name] = routes["native"]
    harness.pins.expect(("outcomes", LETS.package), observed)
    return observed


def verify_lets(harness: FixtureGate, workspace: Path) -> None:
    """Let blocks run natively, on Java LLVM from the emitted K and from `reference.k`, and on Java Haskell."""

    harness.check(LETS)
    harness.expand(LETS)
    emitted = harness.emit(LETS)
    emitted_fragments(emitted, (
        "<k> swap ( E:Exp ) => ( #let pair ( X:Exp , Y:Exp ) = E:Exp #in pair ( Y:Exp , X:Exp ) ) ... </k>",
        "rule swapPair ( P:Exp ) => ( #let pair ( X:Exp , Y:Exp ) = P:Exp #in pair ( Y:Exp , X:Exp ) ) [label(",
        "rule scale ( E:Exp ) => ( #let M:Int = E:Exp #in ( #let N:Int = M:Int +Int 1 #in N:Int *Int M:Int ) ) [label(",
        "<k> shadow ( E:Exp ) => pair ( ( #let E_2:Exp = pair ( E:Exp , E:Exp ) #in E_2:Exp ) , E:Exp ) ... </k>",
        "requires ( #let M:Int = E:Exp #in M:Int >Int 0 )",
    ))
    observed = compare_lets(harness, emitted)
    agree_with_reference(
        harness, workspace, LETS_REFERENCE, "LETS-REFERENCE", LETS_PROGRAMS, observed,
    )
    haskell = java_haskell_outcomes(harness, emitted, LETS_HASKELL_PROGRAMS)
    for program in LETS_HASKELL_PROGRAMS:
        if haskell[program.name] != observed[program.name]:
            raise GateError(
                f"{LETS.package} {program.name}: Java K Haskell observed "
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

        verify_matches(harness, workspace)
        print("PASS matches: isPair, boxed, twin, and known agree natively, on Java LLVM, with reference.k, and on Java Haskell")

        verify_lets(harness, workspace)
        print("PASS lets: swap, swapPair, scale, shadow, and positive agree natively, on Java LLVM, with reference.k, and on Java Haskell; the refuted lets are undefined on Java LLVM")

        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-patterns-functions-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("patterns-functions")
    print("PASS patterns-functions")
    return 0


if __name__ == "__main__":
    entry("patterns-functions", main, errors=(OSError,))
