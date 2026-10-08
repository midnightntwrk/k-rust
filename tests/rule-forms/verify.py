#!/usr/bin/env python3
"""Rule-forms feature gate: priority (KF-010), nondet (KF-012), and anywhere rules (KF-026).

Each fixture package runs natively through k-rust and through Java K, and
the outcomes must agree:

- `priority`: `#[k::rule(priority = 40)]` beats a default-priority rule on
  the same head, so execution ends in `heads` and native search and
  `krun --search` both reach that one final state; a transition at priority
  250 loses to an `owise` one (priority 200) on both routes; guarded
  equations at priorities 50 to 54, and the same function with an
  `#[k::equation(owise)]` fallback, grade 95/85/75/65/10 identically;
- `nondet`: `#[k::rule(nondet = toss)]` groups two overlapping rules, and
  native search and `krun --search` both reach `heads` and `tails`; bare
  `#[k::strict]` reaches counters 3 and 4 on both routes; two `#[k::rule]`
  fns with complementary guards need no group; the key emits nothing;
- `anywhere`: `#[k::rule(anywhere)]` drops a leading `a` from `seq` at the
  top, inside `wrap(..)`, and repeatedly on both routes; reassociating
  `seq(seq(b, c), d)` is a pinned divergence (k-rust leaves the left-hand
  side, which nests the anywhere-headed `seq`, unreduced with a residual
  `#Ceil`; Java LLVM reassociates); each emitted rule carries `anywhere` and a
  `// krs-capability: AnywhereRule` comment, `symbols.json` records the
  requirement, and the Java Haskell reference route refuses the definition
  with `krs::capability::unavailable` before anything is kompiled;
- negative fixtures: `owise` with `priority`, priority 255, the retired
  `#[k::priority(N)]`, `owise` on a simplification, `priority` on an alias
  clause, an unannotated overlap of reference `#[k::rule]` fns, a group with
  one rule, a stale group member, a group mixing priorities, `nondet` on an
  equation, and `anywhere` on a readable clause, on a `cells!` rule, or with
  `priority` each fail `krs check` with a pinned diagnostic.

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
from support.fixture_gate import Fixture, FixtureGate, Program  # noqa: E402
from support.krs import build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import add_refresh_argument  # noqa: E402
from support.tools import checkout_scratch, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
PINS = HERE / "pins.json"
FIXTURES = HERE / "fixtures"

PRIORITY = Fixture(MANIFEST, "krs-rule-forms-priority")
PRIORITY_PROGRAMS = (
    Program("toss", "toss", "accepted", "heads", search=("heads",)),
    Program("flip", "flip", "accepted", "high", search=("high",)),
    *(
        Program(f"grade-{percentile}", f"grade({percentile})", "accepted", letter)
        for percentile, letter in (
            (95, "letterA"), (85, "letterB"), (75, "letterC"), (65, "letterD"), (10, "letterF"),
        )
    ),
    *(
        Program(f"grade-owise-{percentile}", f"gradeOwise({percentile})", "accepted", letter)
        for percentile, letter in (
            (95, "letterA"), (85, "letterB"), (75, "letterC"), (65, "letterD"), (10, "letterF"),
        )
    ),
)

NONDET = Fixture(MANIFEST, "krs-rule-forms-nondet")
ANYWHERE = Fixture(MANIFEST, "krs-rule-forms-anywhere")
ANYWHERE_PROGRAMS = (
    Program("drop", "seq(a, b)", "accepted", "b"),
    Program("drop-nested", "wrap(seq(a, b))", "accepted", "wrap(b)"),
    Program("drop-repeated", "seq(a, seq(a, c))", "accepted", "c"),
    # A pinned divergence: k-rust leaves `seq(seq(b, c), d)` unreduced with a
    # residual `#Ceil(seq(b, c))`, because the left-hand side nests the
    # anywhere-headed `seq`; Java LLVM reassociates.
    Program("reassociate", "seq(seq(b, c), d)", "accepted", "seq(b, seq(c, d))"),
    Program("reassociate-nested", "wrap(seq(seq(b, c), d))", "accepted", "wrap(seq(b, seq(c, d)))"),
)
ANYWHERE_REFUSAL = (
    "error[krs::capability::unavailable]: definition contains anywhere rules [drop-a, reassociate]; "
    "K 7.1.337's Haskell backend rejects them (and --allow-anywhere-haskell would drop them); "
    "run this on the LLVM or k-rust route"
)

COUNTER = (("COUNTER", "1"),)
NONDET_PROGRAMS = (
    Program("toss", "toss", "accepted", None, search=("heads", "tails"), variables=COUNTER),
    Program("strict-order", "add(inc, dbl)", "accepted", None, search=("3", "4"), variables=COUNTER),
    Program("div", "div(6, 3)", "accepted", "2", variables=COUNTER),
    Program("div-zero", "div(1, 0)", "accepted", "divByZero", variables=COUNTER),
)

NEGATIVE = (
    "owise-with-priority",
    "priority-out-of-range",
    "retired-priority",
    "owise-simplification",
    "priority-alias",
    "unannotated-overlap",
    "single-member-group",
    "stale-member",
    "mixed-priorities",
    "nondet-equation",
    "anywhere-readable",
    "anywhere-cells",
    "anywhere-priority",
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


def emitted_attributes(emitted, fragments: tuple[str, ...]) -> None:
    source = emitted.source.read_text(encoding="utf-8")
    for fragment in fragments:
        if fragment not in source:
            raise GateError(f"{emitted.fixture.package}: emitted K omits {fragment!r}")


def verify_anywhere(harness: FixtureGate, pins: Ledger) -> None:
    """Anywhere rules run natively and on Java LLVM; the Java Haskell route refuses them."""

    harness.check(ANYWHERE)
    harness.expand(ANYWHERE)
    emitted = harness.emit(ANYWHERE)
    emitted_attributes(emitted, (
        "  // krs-capability: AnywhereRule reassociate\n  rule seq ( seq (",
        "[anywhere, label(reassociate)]",
        "  // krs-capability: AnywhereRule drop-a\n  rule seq ( a , S:Stmt ) => S:Stmt [anywhere, label(drop-a)]",
    ))
    symbols = json.loads((emitted.directory / "symbols.json").read_text(encoding="utf-8"))
    requirements = symbols.get("capability_requirements")
    if sorted((row["feature"], row["symbol"]) for row in requirements or ()) != [
        ("AnywhereRule", "drop-a"), ("AnywhereRule", "reassociate"),
    ]:
        raise GateError(f"symbols.json records {requirements!r} as the capability requirements")
    harness.compare(emitted, ANYWHERE_PROGRAMS, sort="Stmt")
    for route in ("native-rust", "native-llvm", "java-llvm-reference"):
        krs_gate.require_route(harness.gate, emitted.directory, route, environment=harness.environment)
    # The Java Haskell reference step stops at the capability check, before kompile.
    try:
        krs_gate.require_route(
            harness.gate, emitted.directory, "java-haskell-reference", environment=harness.environment,
        )
    except GateError as refusal:
        message = str(refusal)
    else:
        raise GateError("the java-haskell-reference route accepted a definition with anywhere rules")
    if message != ANYWHERE_REFUSAL:
        raise GateError(f"java-haskell-reference refusal changed:\n{message}")
    pins.expect(("capability_refusals", "java-haskell-reference"), message)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 rule-forms ledger")

    target = checkout_scratch() / "rule-forms-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target), "CARGO_TERM_COLOR": "never"}
    krs = build(environment, target=target)
    gate = krs_gate.configured_or_build(target)
    check_packages("rule-forms", krs=krs, env=environment, target_dir=target)

    with tempfile.TemporaryDirectory(prefix="krs-rule-forms-") as temporary:
        workspace = Path(temporary)
        harness = FixtureGate(
            "rule-forms", pins, workspace, krs, gate, environment,
            refresh=arguments.refresh_reference,
            divergences=pins.get("known_divergences", {}),
        )

        harness.check(PRIORITY)
        harness.expand(PRIORITY)
        priority = harness.emit(PRIORITY)
        emitted_attributes(priority, (
            "rule toss => heads [priority(40), label(",
            "rule [flip-low]:",
            "[priority(250)]",
            "[priority(200)]",
            "rule gradeOwise ( _ ) => letterF [priority(200), label(",
            "rule grade ( _ ) => letterF [priority(54), label(",
        ))
        harness.compare(priority, PRIORITY_PROGRAMS, sort="Pgm", search=True)
        print("PASS priority: priority 40 wins, owise (200) beats priority 250, equation priorities and owise grade alike")

        harness.check(NONDET)
        harness.expand(NONDET)
        nondet = harness.emit(NONDET)
        if "nondet" in nondet.source.read_text(encoding="utf-8"):
            raise GateError("the check-only nondet key reached the emitted K")
        harness.compare(nondet, NONDET_PROGRAMS, sort="Exp", search=True)
        print("PASS nondet: toss reaches heads and tails, strictness order reaches 3 and 4, guards separate div")

        verify_anywhere(harness, pins)
        print("PASS anywhere: drop-a at any depth on both routes, reassociation a pinned k-rust divergence, Java Haskell refused before kompile")

        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-rule-forms-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("rule-forms")
    print("PASS rule-forms")
    return 0


if __name__ == "__main__":
    entry("rule-forms", main, errors=(OSError,))
