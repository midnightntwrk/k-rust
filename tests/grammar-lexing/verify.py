#!/usr/bin/env python3
"""Grammar and lexing feature gate: program-syntax partition (KF-005).

Each package emits `<NS>-SYNTAX`, the grammar programs may use, and `<NS>`,
which imports it and adds what only rules may use. This gate checks the
partition end to end on both routes:

- `partition`: `pub` productions are program syntax, the `internal` family is
  not, builtin operations such as `andBool` and `+Int` never are, and
  `int-literals = "unsigned"` makes a program's `-1` the term `Neg(1)`;
- `kevm-case`: KEVM's `LogRecord::Entry` and `BlockHashLookup` take a `List`,
  and K has no LIST-SYNTAX module, so both are placed in `KRS-EVM`; the
  `krs check --partition` text is pinned and programs cannot contain them;
- `program-warning`: the same production marked `program` gives the pinned
  `krs::partition::not-program-syntax` warning;
- negative fixtures: the removed `root`/`syntax-root` keys, an invalid
  `int-literals`, `internal` on a non-pub item, a group that mixes `internal`
  and program syntax, and an unsigned package importing signed program syntax.

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

PARTITION = Fixture(MANIFEST, "krs-grammar-partition")
KEVM_CASE = Fixture(MANIFEST, "krs-grammar-kevm-case")
PROGRAM_WARNING = Fixture(MANIFEST, "krs-grammar-program-warning")

PARTITION_PROGRAMS = (
    Program("and", "true && false", "accepted", "false"),
    Program("and-bool-operator", "true andBool false", "rejected"),
    Program("internal-inc", "#inc(1)", "rejected"),
    Program("int-operator", "1 +Int 2", "rejected"),
    Program("unsigned-literal", "-1", "accepted", "0", kast='neg(#token("1","Int"))'),
    Program("spaced-negation", "- 1", "accepted", "0"),
)
KEVM_PROGRAMS = (
    Program("emit", "emit(1)", "accepted", "done"),
    Program("log-entry", "logEntry(1, .List, .Bytes)", "rejected"),
    Program("block-hash", "#kevmBlockHash(.List, 1)", "rejected"),
)
NEGATIVE = (
    ("removed-root", "removed-root", "krs-grammar-removed-root", ()),
    ("removed-syntax-root", "removed-syntax-root", "krs-grammar-removed-syntax-root", ()),
    ("invalid-int-literals", "invalid-int-literals", "krs-grammar-invalid-int-literals", ()),
    ("internal-not-pub", "internal-not-pub", "krs-grammar-internal-not-pub", ()),
    ("mixed-group", "mixed-group", "krs-grammar-mixed-group", ()),
    (
        "signed-leak", "signed-leak", "krs-grammar-unsigned-root",
        ("krs-grammar-signed-base:main",),
    ),
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


def require_imports(emitted, expected: dict[str, list[str]], gate: Path, environment) -> None:
    modules = krs_gate.ir_query(gate, emitted.directory, {"kind": "modules"}, environment=environment)
    rows = {row["name"]: row["imports"] for row in modules["rows"]}
    for module, imports in expected.items():
        if rows.get(module) != imports:
            raise GateError(f"{module} imports {rows.get(module)}, expected {imports}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 grammar-lexing ledger")

    target = checkout_scratch() / "grammar-lexing-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target), "CARGO_TERM_COLOR": "never"}
    krs = build(environment, target=target)
    gate = krs_gate.configured_or_build(target)
    check_packages("grammar-lexing", krs=krs, env=environment, target_dir=target)

    with tempfile.TemporaryDirectory(prefix="krs-grammar-lexing-") as temporary:
        workspace = Path(temporary)
        harness = FixtureGate(
            "grammar-lexing", pins, workspace, krs, gate, environment,
            refresh=arguments.refresh_reference,
            divergences=pins.get("known_divergences", {}),
        )

        harness.check(PARTITION)
        harness.expand(PARTITION)
        partition = harness.emit(PARTITION)
        require_imports(partition, {
            "KRS-PART-SYNTAX": ["BOOL-SYNTAX", "KRS-FRAMEWORK", "UNSIGNED-INT-SYNTAX"],
            "KRS-PART": ["BOOL", "INT", "KRS-FRAMEWORK", "KRS-PART-SYNTAX"],
        }, gate, environment)
        harness.partition(PARTITION)
        harness.compare(partition, PARTITION_PROGRAMS, sort="Exp")
        print("PASS partition: pub is program syntax; internal, andBool, and +Int are not; -1 is Neg(1)")

        partition_text, _ = harness.partition(KEVM_CASE)
        for production in ("LogRecord::Entry", "BlockHashLookup"):
            line = f"  production {production}: argument `"
            if line not in partition_text or "K has no LIST-SYNTAX module" not in partition_text:
                raise GateError(f"krs check --partition does not place {production} in KRS-EVM:\n{partition_text}")
        kevm = harness.emit(KEVM_CASE)
        harness.compare(kevm, KEVM_PROGRAMS, sort="Command")
        print("PASS kevm-case: LogRecord::Entry and BlockHashLookup placed in KRS-EVM; programs cannot contain them")

        _, warnings = harness.partition(PROGRAM_WARNING)
        if not any("krs::partition::not-program-syntax" in line for line in warnings):
            raise GateError(f"program-warning: no not-program-syntax warning: {warnings}")
        print("PASS program-warning: pinned krs::partition::not-program-syntax warning")

        for name, directory, package, dependencies in NEGATIVE:
            manifest = materialize(directory, workspace)
            message = harness.diagnostic(name, Fixture(manifest, package, dependencies=dependencies))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("grammar-lexing")
    print("PASS grammar-lexing")
    return 0


if __name__ == "__main__":
    entry("grammar-lexing", main, errors=(OSError,))
