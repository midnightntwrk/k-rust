#!/usr/bin/env python3
"""Grammar and lexing feature gate: program-syntax partition (KF-005), formats
(KF-018), and production keys (KF-002, KF-038, KF-045).

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
- `prefer`: `prefer` on `IfThen` resolves the dangling else, so
  `if true then if false then first else second` parses as
  `ifThen(true, ifThenElse(false, first, second))` on both routes and runs to
  `second`, and an unambiguous program is unaffected; `prefer` is a parser
  attribute that K 7.1.337 does not write to KORE, and the native
  `syntaxDefinition.kore` agrees (pinned);
- `overload`: `LValSyntax::LvalDot` overloads `ExpSyntax::Dot`, so `a.b`
  parses as `lvalDot(a, b)` on both routes and the rule written on the `LVal`
  production fires, while `1.b` stays a `dot`; both KOREs carry the one
  `symbol-overload` axiom of the family. `overload-ambiguous`, the same
  grammar without the key, makes `a.b` ambiguous on both routes and has no
  axiom;
- `visibility`: the non-`pub` `Helper::Wrap` is emitted `private`; `inc 1`
  runs to `2` through it on both routes, a program `helper(1)` is rejected on
  both, and a module importing the definition cannot use `helper(..)` in a
  rule: Java `kompile` and k-rust's outer loader both reject
  `fixtures/visibility-induced/induced.k`;
- `format`: `color`, `colors`, `%c`, and `%r`, with terminals printed by
  position; Java K accepts the emitted `.k`, the native and Java
  `syntaxDefinition.kore` agree on every `format` and `colors` attribute, and
  `krun --color on` output is pinned through the reference cache, and
  `krs run --color always` must print it byte for byte (KF-017);
- negative fixtures: the removed `root`/`syntax-root` keys, an invalid
  `int-literals`, `internal` on a non-pub item, a group that mixes `internal`
  and program syntax, an unsigned package importing signed program syntax, a
  `colors` list that does not match the printed terminals, `prefer` with
  `avoid`, an overload with another arity, one whose sort is not a subsort of
  its target's, two productions that overload each other, a dependent that
  names a private production (E0603), and a claim that names one.

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
from support.fixture_gate import Fixture, FixtureGate, Program, kore_attribute_lines  # noqa: E402
from support.krs import build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import Key, Output, Pin, Snapshot, add_refresh_argument, repository_inputs  # noqa: E402
from support.tools import checkout_scratch, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
PINS = HERE / "pins.json"
FIXTURES = HERE / "fixtures"

PARTITION = Fixture(MANIFEST, "krs-grammar-partition")
KEVM_CASE = Fixture(MANIFEST, "krs-grammar-kevm-case")
PROGRAM_WARNING = Fixture(MANIFEST, "krs-grammar-program-warning")
FORMAT = Fixture(MANIFEST, "krs-grammar-format")
PREFER = Fixture(MANIFEST, "krs-grammar-prefer")
OVERLOAD = Fixture(MANIFEST, "krs-grammar-overload")
OVERLOAD_AMBIGUOUS = Fixture(MANIFEST, "krs-grammar-overload-ambiguous")
VISIBILITY = Fixture(MANIFEST, "krs-grammar-visibility")
VISIBILITY_PROGRAMS = (
    Program("inc", "inc 1", "accepted", "2"),
    Program("helper", "helper(1)", "rejected"),
)
VISIBILITY_ATTRIBUTES = (("inc", "wrap"), ("private",))
INDUCED_MODULE = "KRS-VISIBILITY-INDUCED"
FORMAT_LABELS = ("while", "block", "assignX", "skip")
FORMAT_ATTRIBUTES = ("format", "color", "colors")
FORMAT_PROGRAM = "while (1) { x = 2; }"
FORMAT_SOURCE_FRAGMENTS = (
    "color(magenta), format(%1 %2%3%4 %5)",
    "colors(blue,blue), format(%1%i%n%2%d%n%3)",
    "colors(green,red,red,red), format(%c// assign%r%n%1 %2 %3%4)",
)

PARTITION_PROGRAMS = (
    Program("and", "true && false", "accepted", "false"),
    Program("and-bool-operator", "true andBool false", "rejected"),
    Program("internal-inc", "#inc(1)", "rejected"),
    Program("int-operator", "1 +Int 2", "rejected"),
    Program("unsigned-literal", "-1", "accepted", "0", kast='neg(#token("1","Int"))'),
    Program("spaced-negation", "- 1", "accepted", "0"),
)
PREFER_PROGRAMS = (
    Program(
        "dangling-else", "if true then if false then first else second", "accepted", "second",
        kast='ifThen(#token("true","Bool"),ifThenElse(#token("false","Bool"),first(.KList),second(.KList)))',
    ),
    Program(
        "if-then-else", "if true then first else second", "accepted", "first",
        kast='ifThenElse(#token("true","Bool"),first(.KList),second(.KList))',
    ),
    Program("if-then", "if false then first", "accepted", "skip"),
)
PREFER_ATTRIBUTES = (("ifThen", "ifThenElse"), ("prefer", "avoid"))
OVERLOAD_PROGRAMS = (
    Program(
        "lval-access", "a.b", "accepted", "lvalue",
        kast='lvalDot(#token("a","Id"),#token("b","Id"))',
    ),
    Program(
        "value-access", "1.b", "accepted", "value",
        kast='dot(#token("1","Int"),#token("b","Id"))',
    ),
)
OVERLOAD_AMBIGUOUS_PROGRAMS = (
    Program("lval-access", "a.b", "rejected"),
    Program("value-access", "1.b", "accepted", "value"),
)
OVERLOAD_ATTRIBUTES = (("dot", "lvalDot"), ("overload",))
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
    ("colors-mismatch", "colors-mismatch", "krs-grammar-colors-mismatch", ()),
    ("prefer-avoid", "prefer-avoid", "krs-grammar-prefer-avoid", ()),
    ("overload-arity", "overload-arity", "krs-grammar-overload-arity", ()),
    ("overload-not-subsort", "overload-not-subsort", "krs-grammar-overload-not-subsort", ()),
    ("overload-cycle", "overload-cycle", "krs-grammar-overload-cycle", ()),
    (
        "visibility-dependent", "visibility-dependent", "krs-grammar-visibility-dependent",
        ("krs-grammar-visibility-dependent-base:main",),
    ),
    ("visibility-claim", "visibility-claim", "krs-grammar-visibility-claim", ()),
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


def java_attribute_reducer(harness: FixtureGate, workspace: Path):
    """Reduce Java's `syntaxDefinition.kore` to the pinned symbol attributes through `krs-gate`."""

    def reduce(text: str) -> str:
        kore = workspace / "java-syntax-definition.kore"
        kore.write_text(text, encoding="utf-8")
        return kore_attribute_lines(
            harness.gate, kore, FORMAT_LABELS, FORMAT_ATTRIBUTES, environment=harness.environment,
        )

    return reduce


def verify_format(harness: FixtureGate, pins: Ledger, workspace: Path, refresh: bool) -> None:
    """Emitted formats, KORE colour attributes on both routes, and `krun --color on`."""

    harness.check(FORMAT)
    harness.expand(FORMAT)
    emitted = harness.emit(FORMAT)
    source = emitted.source.read_text(encoding="utf-8")
    for fragment in FORMAT_SOURCE_FRAGMENTS:
        if fragment not in source:
            raise GateError(f"emitted format omits {fragment!r}")
    native = harness.build(FORMAT) / "syntaxDefinition.kore"
    native_attributes = kore_attribute_lines(
        harness.gate, native, FORMAT_LABELS, FORMAT_ATTRIBUTES, environment=harness.environment,
    )
    program = workspace / "programs" / "format.pgm"
    program.parent.mkdir(parents=True, exist_ok=True)
    program.write_text(FORMAT_PROGRAM + "\n", encoding="utf-8")
    k = Snapshot(
        f"grammar-lexing/{FORMAT.package}",
        Key(tools=("kompile", "krun"), inputs=repository_inputs([])),
        workspace=workspace, refresh=refresh, pin=Pin(pins, FORMAT.package),
    )
    compiled = workspace / "kompiled" / FORMAT.package
    compile_process = k.run(
        "kompile/definition", "kompile",
        [
            emitted.source, "--main-module", emitted.main_module,
            "--syntax-module", emitted.syntax_module,
            "--backend", "llvm", "--output-definition", compiled,
        ],
        timeout=900,
        # The reduced evidence is written beside the kompiled directory, whose
        # own syntaxDefinition.kore krun still reads.
        outputs=(Output(
            workspace / "format-syntax-attributes.txt",
            java_attribute_reducer(harness, workspace),
            lambda: compiled / "syntaxDefinition.kore",
        ),),
    )
    if compile_process.returncode != 0:
        raise GateError(f"kompile rejected the emitted format definition:\n{compile_process.stderr}")
    java_attributes = (workspace / "format-syntax-attributes.txt").read_text(encoding="utf-8")
    if java_attributes != native_attributes:
        raise GateError(
            f"native and Java KORE format attributes differ:\nnative:\n{native_attributes}java:\n{java_attributes}"
        )
    colored = k.run(
        "krun/color", "krun", ["--definition", compiled, "--color", "on", program], timeout=120,
    )
    if colored.returncode != 0 or "\x1b[" not in colored.stdout:
        raise GateError(f"krun --color on printed no colours:\n{colored.stdout}{colored.stderr}")
    pins.expect(("format", "kore_attributes"), native_attributes)
    pins.expect(("format", "krun_color"), colored.stdout)
    # KF-017: `krs run --color always` prints the final state byte for byte as `krun --color on` does.
    native_colored = harness.run_command(FORMAT, "run", program, "--color", "always")
    if native_colored != colored.stdout:
        raise GateError(
            f"krs run --color always differs from krun --color on:\nkrs:\n{native_colored!r}\nkrun:\n{colored.stdout!r}"
        )
    # `kast --output program` formats with the authored format, so `%c` and `%r` print as letters.
    pins.expect(("format", "krs_parse_program"), harness.run_command(FORMAT, "parse", "--output", "program", program))
    print(f"PASS grammar-lexing {FORMAT.package} reference snapshot: {k.finish()}")


def verify_induced_visibility(harness: FixtureGate, pins: Ledger, emitted, workspace: Path, refresh: bool) -> None:
    """A module importing the emitted definition cannot use its private production on either route."""

    directory = workspace / "visibility-induced"
    directory.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(emitted.source, directory / "definition.k")
    induced = directory / "induced.k"
    shutil.copyfile(FIXTURES / "visibility-induced" / "induced.k", induced)
    k = Snapshot(
        "grammar-lexing/visibility-induced",
        Key(
            tools=("kompile",),
            inputs={
                **repository_inputs([FIXTURES / "visibility-induced" / "induced.k"]),
                f"emitted/{VISIBILITY.package}/definition.k": directory / "definition.k",
            },
        ),
        workspace=workspace, refresh=refresh, pin=Pin(pins, "visibility-induced"),
    )
    process = k.run(
        "kompile/induced", "kompile",
        [
            induced, "--main-module", INDUCED_MODULE, "--syntax-module", emitted.syntax_module,
            "--backend", "llvm", "--output-definition", workspace / "kompiled" / "visibility-induced",
        ],
        timeout=900,
    )
    if process.returncode == 0:
        raise GateError("Java kompile accepted a rule that uses a private production of an imported module")
    java = next((line for line in process.stderr.splitlines() if line.startswith("[Error]")), process.stderr)
    with krs_gate.Session(harness.gate, environment=harness.environment) as session:
        native = session.load_k(induced, INDUCED_MODULE)
    if native is None:
        raise GateError("k-rust loaded a rule that uses a private production of an imported module")
    pins.expect(("induced_rejections", "visibility"), {
        "java": java,
        "native": native.replace(os.fspath(directory), "{{work}}"),
    })
    print(f"PASS grammar-lexing visibility-induced reference snapshot: {k.finish()}")


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

        verify_format(harness, pins, workspace, arguments.refresh_reference)
        print(
            "PASS format: terminals by position; colours agree in native and Java KORE; "
            "krun --color on pinned and printed identically by krs run"
        )

        harness.check(PREFER)
        harness.expand(PREFER)
        prefer = harness.emit(PREFER)
        harness.compare(prefer, PREFER_PROGRAMS, sort="Stmt", attributes=PREFER_ATTRIBUTES)
        print("PASS prefer: the dangling else binds to the inner if on both routes; KORE attributes agree")

        for fixture, programs in (
            (OVERLOAD, OVERLOAD_PROGRAMS), (OVERLOAD_AMBIGUOUS, OVERLOAD_AMBIGUOUS_PROGRAMS),
        ):
            harness.check(fixture)
            harness.expand(fixture)
            emitted = harness.emit(fixture)
            harness.compare(emitted, programs, sort="Exp", attributes=OVERLOAD_ATTRIBUTES)
        axioms = {
            package: [line for line in harness.kore_attributes[package].splitlines() if line.startswith("overload ")]
            for package in (OVERLOAD.package, OVERLOAD_AMBIGUOUS.package)
        }
        if len(axioms[OVERLOAD.package]) != 1 or axioms[OVERLOAD_AMBIGUOUS.package]:
            raise GateError(f"expected one overload axiom with the key and none without it: {axioms}")
        print("PASS overload: a.b is lvalDot on both routes and the LVal rule fires; one overload axiom; ambiguous without the key")

        harness.check(VISIBILITY)
        harness.expand(VISIBILITY)
        visibility = harness.emit(VISIBILITY)
        harness.compare(visibility, VISIBILITY_PROGRAMS, sort="Exp", attributes=VISIBILITY_ATTRIBUTES)
        verify_induced_visibility(harness, pins, visibility, workspace, arguments.refresh_reference)
        print("PASS visibility: inc 1 runs through the private helper; helper(..) is invisible to programs and importers on both routes")

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
