#!/usr/bin/env python3
"""Rule-forms feature gate: rule and equation priority (KF-010).

Each fixture package runs natively through k-rust and through Java K, and
the outcomes must agree:

- `priority`: `#[k::rule(priority = 40)]` beats a default-priority rule on
  the same head, so execution ends in `heads` and native search and
  `krun --search` both reach that one final state; a transition at priority
  250 loses to an `owise` one (priority 200) on both routes; guarded
  equations at priorities 50 to 54, and the same function with an
  `#[k::equation(owise)]` fallback, grade 95/85/75/65/10 identically;
- negative fixtures: `owise` with `priority`, priority 255, the retired
  `#[k::priority(N)]`, `owise` on a simplification, and `priority` on an
  alias clause each fail `krs check` with a pinned diagnostic.

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

NEGATIVE = (
    "owise-with-priority",
    "priority-out-of-range",
    "retired-priority",
    "owise-simplification",
    "priority-alias",
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

        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-rule-forms-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("rule-forms")
    print("PASS rule-forms")
    return 0


if __name__ == "__main__":
    entry("rule-forms", main, errors=(OSError,))
