#!/usr/bin/env python3
"""Patterns-and-functions feature gate: `name @ pattern` (KF-029).

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
- negative fixtures: `ref` on an alias, an alias inside its own subpattern,
  an alias of a `..` remainder, `@` in a result, and an alias of a whole rule
  subject, each fail `krs check` with a pinned diagnostic.

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
from support.fixture_gate import Emitted, Fixture, FixtureGate, Program  # noqa: E402
from support.krs import build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import add_refresh_argument  # noqa: E402
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

NEGATIVE = (
    "alias-ref",
    "alias-inside-itself",
    "alias-remainder",
    "alias-in-result",
    "alias-whole-subject",
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

    reference_directory = workspace / "reference" / ALIASES_REFERENCE.package
    reference_directory.mkdir(parents=True)
    shutil.copyfile(REFERENCE, reference_directory / "definition.k")
    reference = Emitted(ALIASES_REFERENCE, reference_directory, "ALIASES-REFERENCE")
    java = harness._java_outcomes(reference, ALIASES_PROGRAMS, sort="Exp")  # noqa: SLF001
    for program in ALIASES_PROGRAMS:
        # reference.k declares no formats, so K prints its terms spaced out.
        if unspaced(java[program.name]) != unspaced(observed[program.name]):
            raise GateError(
                f"reference.k {program.name}: Java K observed {java[program.name]}, "
                f"the emitted definition {observed[program.name]}"
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

        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-patterns-functions-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("patterns-functions")
    print("PASS patterns-functions")
    return 0


if __name__ == "__main__":
    entry("patterns-functions", main, errors=(OSError,))
