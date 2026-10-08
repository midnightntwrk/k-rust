#!/usr/bin/env python3
r"""Builtin domains feature gate: the builtin operation catalog end to end.

Each package exercises one part of the catalog with one equation or rule per
operation, and a corpus of programs that apply them to concrete values:

- `int-sign`: negative Int literals (KF-006) in equation heads, readable
  patterns, results, and programs, and `int::div` on the four sign
  combinations; `int-sign-unsigned`: a rule literal `-1` in a package whose
  programs use unsigned literals and that uses no `int::` operation;

- `int-ops`, `bool-ops`, `bytes-ops`: one function and equation per INT, BOOL,
  and BYTES operation (KF-007), including the Euclidean and truncating
  divisions, `bitRangeInt`, and the `Endianness`/`Signedness` conversions;
- `set-ops`: SET operations and `list::contains`, with `Set2List`/`List2Set`
  from K's `COLLECTIONS` module;
- `map-ops`: MAP operations over a map held in a configuration cell, because K
  has no MAP-SYNTAX module and a program cannot contain a map;
- `k-equal`: `kequal::eq`, `ne`, and `ite` (KF-024) after K's tutorial
  `1_basic/18`, with every branch defined; the instances KRS infers for `ite`
  must be the ones in k-rust's KORE;
- `strings`: String literals (KF-008) in equations, readable patterns, results,
  and programs, including the Latin-1 code point `\xc1`, and the STRING
  operations with `bytes::from_string`/`to_string`;
- `floats`: Float literals and constants (KF-033) in equations and readable
  patterns, and every FLOAT operation: `0.1 + 0.2` in binary32 and binary64,
  NaN under `float::eq` and `kequal::eq`, signed zero, `sqrt`, `to_int` ties,
  and `max_value`. Programs supply every operand, so no application is ground,
  and every result is a Bool or an Int;
- `float-java-only`: a ground FLOAT application and a binary128 token, which
  KRS records as the `GroundFloatFolding` and `FloatPrecisionBeyondBinary64`
  requirements; the native and browser routes refuse the definition before
  compiling it, and its programs run on Java K's LLVM backend;
- `io`: console I/O through `stream` cells and the `exit` cell (KF-035). The
  program `read; read; print(sum); halt(sum)` with standard input `3\n4\n`
  (one token per line) prints `7` and exits with status 7, through `krs run`
  and through Java K's `krun --output none` on the LLVM backend; `krs search`
  on the definition gives the pinned refusal, and the browser route refuses
  it with the `ConsoleIO` requirement;
- `raw-k` and `raw-hook`: the raw K escapes (KF-037) in packages that set
  `allow-raw-k = true`. A `raw_k!` rule `double` runs natively and on Java K's
  LLVM backend; the quoted hook `KRYPTO.keccak256` runs natively and on Java
  K's Haskell backend, kompiled with `--hook-namespaces KRYPTO` because KRYPTO
  is outside K's default hook namespaces (its LLVM backend would need the
  blockchain plugin).
  Each `krs check` pins its `krs::semantic::raw-k` or `krs::expand::raw-hook`
  warning. `raw-denied` (no opt-in) and `raw-strict` (`profile = "strict"`)
  each fail with both errors, `krs check --profile strict` fails on `raw-k`,
  and `raw-parse-error`, a `raw_k!` rule K cannot parse, fails `krs build`
  closed with `krs::native::raw-k-parse` at the `raw_k!` text.

`known_divergences` in `pins.json` pins `ite-undefined-branch`, the k-equal
program `go()`, whose rule is `kequal::ite(true, 1, Undef())` with `Undef` a
function that has no equations: Java K's LLVM backend evaluates only the taken
branch and ends in `1`, while k-rust, strict in both branches, splits on whether
`Undef()` is defined and ends in two leaves. It also pins the `\xc1` programs
on which the routes disagree. k-rust stores a `\xHH` escape as the raw byte, so its `ordChar`,
`chrChar` (which yields UTF-8), and `String2Bytes` disagree with K's Latin-1
code points; and Java K's LLVM backend does not match the rule literal
`"\xc1"` against the same program literal, which k-rust does. The gate fails
when either route's pinned outcome changes.

Every program runs natively through k-rust and through Java K's LLVM backend;
the normalized final computation cells must agree with each other and with the
expected value written beside the program. The expansion and the emitted `.k`
of every package are pinned by digest.

Run it from the repository root; `--record` rewrites the measured pins after
every step passes, and `--refresh-reference` reruns Java K instead of
replaying the per-user reference cache.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry, krs_gate  # noqa: E402
from support.fixture_gate import (  # noqa: E402
    ACCEPTED, JAVA_TOOLS, Fixture, FixtureGate, Program, diagnostic_lines, java_run_outcome,
)
from support.krs import build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import Key, Pin, Snapshot, add_refresh_argument, repository_inputs  # noqa: E402
from support.tools import checkout_scratch, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
PINS = HERE / "pins.json"


def case(name: str, text: str, run: str) -> Program:
    return Program(name, text, "accepted", run)


INT_OPS = (
    case("add", "add(7, -3)", "4"),
    case("sub", "sub(7, 10)", "-3"),
    case("mul", "mul(-7, 3)", "-21"),
    case("div", "div(-7, 3)", "-2"),
    case("rem", "rem(-7, 3)", "-1"),
    case("div-euclid", "divEuclid(-7, 3)", "-3"),
    case("rem-euclid", "remEuclid(-7, 3)", "2"),
    case("pow", "pow(2, 10)", "1024"),
    case("pow-mod", "powMod(3, 4, 5)", "1"),
    case("shift-left", "shl(3, 4)", "48"),
    case("shift-right", "shr(-16, 2)", "-4"),
    case("bit-and", "bitAnd(12, 10)", "8"),
    case("bit-or", "bitOr(12, 10)", "14"),
    case("bit-xor", "bitXor(12, 10)", "6"),
    case("bit-not", "bitNot(5)", "-6"),
    case("min", "min(3, -4)", "-4"),
    case("max", "max(3, -4)", "3"),
    case("abs", "abs(-5)", "5"),
    case("log2", "log2(1024)", "10"),
    case("bit-range", "bitRange(4660, 4, 8)", "35"),
    case("sign-extend-bit-range", "signExtendBitRange(255, 0, 8)", "-1"),
    case("divides", "divides(3, 12)", "true"),
    case("not-divides", "divides(5, 12)", "false"),
    case("eq", "eq(2, 2)", "true"),
    case("ne", "ne(2, 2)", "false"),
    case("lt", "lt(-1, 0)", "true"),
    case("le", "le(1, 0)", "false"),
    case("gt", "gt(1, 0)", "true"),
    case("ge", "ge(0, 0)", "true"),
)

BOOL_OPS = (
    case("not", "not(true)", "false"),
    case("and", "and(true, false)", "false"),
    case("or", "or(true, false)", "true"),
    case("xor", "xor(true, true)", "false"),
    case("implies", "implies(true, false)", "false"),
    case("implies-vacuous", "implies(false, false)", "true"),
    case("and-then", "andThen(false, true)", "false"),
    case("or-else", "orElse(false, true)", "true"),
    case("eq", "eq(false, false)", "true"),
    case("ne", "ne(true, false)", "true"),
)

BYTES_OPS = (
    case("empty", "emptyLength()", "0"),
    case("length", r'length(b"\x01\x02\x03")', "3"),
    case("get", r'get(b"\x01\x02\x03", 1)', "2"),
    case("update", r'update(b"\x01\x02", 0, 255)', r'b"\xff\x02"'),
    case("substr", r'substr(b"\x01\x02\x03", 1, 3)', r'b"\x02\x03"'),
    case("pad-right", r'padRight(b"\x01", 3, 0)', r'b"\x01\x00\x00"'),
    case("pad-left", r'padLeft(b"\x01", 3, 0)', r'b"\x00\x00\x01"'),
    case("concat", r'concat(b"\x01", b"\x02\x03")', r'b"\x01\x02\x03"'),
    case("reverse", r'reverse(b"\x01\x02")', r'b"\x02\x01"'),
    case("replace-at", r'replaceAt(b"\x00\x00\x00", 1, b"\xff")', r'b"\x00\xff\x00"'),
    case("from-int", "fromIntBigEndian(4, 258)", r'b"\x00\x00\x01\x02"'),
    case("from-int-no-len", "fromIntSigned(-1)", r'b"\xff"'),
    case("to-int-unsigned", r'toIntUnsigned(b"\x01\x02")', "513"),
    case("to-int-signed", r'toIntSigned(b"\xff\xfe")', "-2"),
)

SET_OPS = (
    case("difference", "difference(1, 2)", "1"),
    case("intersect", "intersect(1, 2, 3)", "1"),
    case("union-size", "unionSize(1, 1)", "1"),
    case("is-subset", "isSubset(2, 1, 2)", "true"),
    case("not-subset", "isSubset(3, 1, 2)", "false"),
    case("contains", "setContains(2, 1, 2)", "true"),
    case("to-list", "toList(1, 2)", "2"),
    case("from-list", "fromList(1, 1)", "1"),
    case("list-contains", "listContains(3, 1, 2)", "false"),
)

MAP_OPS = (
    case("remove", "removeKey(2)", "2"),
    case("remove-absent", "removeKey(9)", "3"),
    case("remove-all", "removeKeys(1)", "1"),
    case("keys", "hasKey(2)", "true"),
    case("keys-absent", "hasKey(20)", "false"),
    case("keys-list", "keyCount()", "3"),
    case("values", "hasValue(20)", "true"),
    case("size", "entryCount()", "3"),
    case("update-all", "restore(1)", "10"),
    case("get-or-default", "lookup(2, 0)", "20"),
    case("get-or-default-absent", "lookup(9, 7)", "7"),
)

INT_SIGN = (
    case("quot-positive", "quot(7, 3)", "2"),
    case("quot-negative-dividend", "quot(-7, 3)", "-2"),
    case("quot-negative-divisor", "quot(7, -3)", "-2"),
    case("quot-negative-both", "quot(-7, -3)", "2"),
    case("sgn-minus-one", "sgn(-1)", "-1"),
    case("sgn-negative", "sgn(-5)", "-1"),
    case("sgn-zero", "sgn(0)", "0"),
    case("sgn-positive", "sgn(4)", "1"),
    case("div-by-minus-one", "7 / -1", "-7"),
    case("div-by-one", "-7 / 1", "-7"),
)

INT_SIGN_UNSIGNED = (
    case("rule-literal", "check(minusOne())", "true"),
    case("positive", "check(1)", "false"),
    Program("program-literal", "check(-1)", "rejected"),
)

STRINGS = (
    case("msg", 'msg("world")', r'"The string you provided: world\nHave a nice day!"'),
    case("length", 'length("hello")', "5"),
    case("length-latin-1", r'length("\xc1")', "1"),
    case("substr", 'substr("hello", 1, 3)', '"el"'),
    case("find", 'find("hello", "l", 0)', "2"),
    case("find-absent", 'find("hello", "z", 0)', "-1"),
    case("chr", "chr(65)", '"A"'),
    case("ord", 'ord("A")', "65"),
    case("ord-latin-1", r'ord("\xc1")', "193"),
    case("chr-latin-1", "chr(193)", r'"\xc1"'),
    case("from-string-latin-1", r'byteCount("\xc1")', "1"),
    case("from-int", "fromInt(-42)", '"-42"'),
    case("to-int", 'toInt("42")', "42"),
    case("from-bool", "fromBool(true)", '"true"'),
    case("to-bool", 'toBool("false")', "false"),
    case("eq", 'same("a", "a")', "true"),
    case("lt", 'before("abc", "abd")', "true"),
    case("not-lt", 'before("b", "a")', "false"),
    case("from-string", 'byteCount("hello")', "5"),
    case("to-string", 'roundTrip("hi")', '"hi"'),
    case("match-literal", 'greet("world")', '"hello, world"'),
    case("match-latin-1", r'greet("\xc1")', r'"\xc1!"'),
)

FLOATS = (
    case("sum-binary64", "sumIs(0.1, 0.2, 0.3)", "false"),
    case("sum-binary64-exact", "sumIs(0.1, 0.2, 0.30000000000000004)", "true"),
    case("sum-binary32", "sumIs(0.1f, 0.2f, 0.3f)", "true"),
    case("arithmetic", "arithmetic(1.5, 0.25)", "true"),
    case("nan-ieee-eq", "ieeeEq(NaN, NaN)", "false"),
    case("nan-ieee-ne", "ieeeNe(NaN, NaN)", "true"),
    case("nan-term-eq", "termEq(NaN, NaN)", "true"),
    case("nan", "nan(NaN)", "true"),
    case("not-nan", "nan(1.0)", "false"),
    case("signed-zero-ieee-eq", "ieeeEq(0.0, -0.0)", "true"),
    case("signed-zero-term-eq", "termEq(0.0, -0.0)", "false"),
    case("signed-zero-neg", "negativeSign(0.0)", "true"),
    case("infinite", "infinite(Infinity)", "true"),
    case("finite", "infinite(1.0e308)", "false"),
    case("ordered-nan", "ordered(NaN, 1.0)", "false"),
    case("ordered-infinity", "ordered(-Infinity, 0.0)", "true"),
    case("sqrt", "sqrtIs(2.25, 1.5)", "true"),
    case("rounding", "rounding(-2.5)", "true"),
    case("to-int-tie-down", "toInt(2.5)", "2"),
    case("to-int-tie-up", "toInt(3.5)", "4"),
    case("to-int-tie-negative", "toInt(-2.5)", "-2"),
    case("from-int", "fromIntIs(7, 53, 11, 7.0)", "true"),
    case("from-int-binary32", "fromIntIs(16777217, 24, 8, 16777216.0f)", "true"),
    case("round-binary32", "roundIs(0.1, 24, 8, 0.1f)", "true"),
    case("max-value", "maxValueIs(53, 11, 1.7976931348623157e308)", "true"),
    case("format-binary32", "format(0.1f)", "2408"),
    case("format-binary64", "format(1.5)", "5311"),
    case("format-binary64-suffix", "format(1.5d)", "5311"),
    case("match-literal", "classify(1.5)", "1"),
    case("match-binary32", "classify(0.1f)", "2"),
    case("match-infinity", "classify(Infinity)", "3"),
    case("match-negative-infinity", "classify(-Infinity)", "4"),
    case("match-negative-zero", "classify(-0.0)", "5"),
)

FLOAT_JAVA_ONLY = Fixture(MANIFEST, "krs-builtin-float-java-only")
FLOAT_JAVA_ONLY_PROGRAMS = (
    case("ground", "isHalf(0.5)", "true"),
    case("binary128", "belowOne(0.5p113x15)", "true"),
)

RAW_K = Fixture(MANIFEST, "krs-builtin-raw-k")
RAW_K_PROGRAMS = (case("double", "double(21)", "42"),)
RAW_HOOK = Fixture(MANIFEST, "krs-builtin-raw-hook")
RAW_HOOK_PROGRAMS = (
    case("keccak-abc", 'keccak(b"abc")', '"4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"'),
)
RAW_DENIED = Fixture(MANIFEST, "krs-builtin-raw-denied")
RAW_STRICT = Fixture(MANIFEST, "krs-builtin-raw-strict")
RAW_PARSE_ERROR = Fixture(MANIFEST, "krs-builtin-raw-parse-error")

IO = Fixture(MANIFEST, "krs-builtin-io")
IO_PROGRAM = "read; read; print(sum); halt(sum)"
IO_STDIN = "3\n4\n"
IO_EXPECTED = {"stdout": "7", "status": 7}

K_EQUAL = (
    case("if-true", "if (true) 1 else 2", "1"),
    case("if-false", "if (false) 1 else 2", "2"),
    case("if-nested", "if (true) if (false) 1 else 2 else 3", "2"),
    case("same-terms", "same(if (true) 1 else 2, if (true) 1 else 2)", "true"),
    case("same-values", "same(1, 2)", "false"),
    case("differ", "differ(if (true) 1 else 2, if (false) 1 else 2)", "true"),
    case("pick-true", "pick(true)", "1"),
    case("pick-false", "pick(false)", "2"),
    # The pinned known divergence (see pins.json and the module documentation).
    case("ite-undefined-branch", "go()", "1"),
)

CASES = (
    ("krs-builtin-int-ops", INT_OPS),
    ("krs-builtin-int-sign", INT_SIGN),
    ("krs-builtin-int-sign-unsigned", INT_SIGN_UNSIGNED),
    ("krs-builtin-k-equal", K_EQUAL),
    ("krs-builtin-bool-ops", BOOL_OPS),
    ("krs-builtin-bytes-ops", BYTES_OPS),
    ("krs-builtin-set-ops", SET_OPS),
    ("krs-builtin-map-ops", MAP_OPS),
    ("krs-builtin-strings", STRINGS),
    ("krs-builtin-floats", FLOATS),
)


def ite_instances(harness: FixtureGate, emitted) -> None:
    """Require KRS's `kequal::ite` instances to be the ones k-rust compiles.

    KRS infers each instance by k-rust's rule (the least sort of the branches
    below the position) and lowers `ite` with no sort parameter, so k-rust's
    solver picks the instance itself; `krs-gate` reads the instances its native
    definition applies `ite` at.
    """

    definition = json.loads(emitted.definition_ir.read_text(encoding="utf-8"))
    names: dict[str, str] = {}
    instances: list[dict[str, str]] = []

    def walk(node: Any) -> None:
        if isinstance(node, dict):
            if isinstance(node.get("id"), str) and isinstance(node.get("emitted_name"), str):
                names[node["id"]] = node["emitted_name"]
            if node.get("application") == {"application_source": "builtin", "application": "k_equal_ite"}:
                instances.append(node["sort"])
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for value in node:
                walk(value)

    walk(definition)
    krs = sorted(
        names[sort["sort"]] if sort["sort_source"] == "declared" else sort["sort"].capitalize()
        for sort in instances
    )
    if krs != ["Exp", "Int", "Int"]:
        raise GateError(f"KRS inferred kequal::ite instances {krs}, expected Exp, Int, and Int")
    native_definition = harness.build(emitted.fixture) / "definition.kore"
    native = krs_gate.kore_instances(harness.gate, native_definition, ["ite"], environment=harness.environment)
    if sorted({instance for (instance,) in native["ite"]} & set(krs)) != sorted(set(krs)):
        raise GateError(f"k-rust instantiates ite at {native['ite']}, not at KRS's {sorted(set(krs))}")


def java_only_floats(harness: FixtureGate) -> None:
    """Require the Float capability rows and pin each route's refusal (V8, KF-033)."""

    harness.check(FLOAT_JAVA_ONLY)
    harness.expand(FLOAT_JAVA_ONLY)
    emitted = harness.emit(FLOAT_JAVA_ONLY)
    symbols = json.loads((emitted.directory / "symbols.json").read_text(encoding="utf-8"))
    features = sorted(row["feature"] for row in symbols.get("capability_requirements") or ())
    if features != ["FloatPrecisionBeyondBinary64", "GroundFloatFolding"]:
        raise GateError(f"symbols.json records {features!r} as the capability requirements")
    source = emitted.source.read_text(encoding="utf-8")
    for feature in features:
        if f"  // krs-capability: {feature} " not in source:
            raise GateError(f"emitted K does not mark the sentence that needs {feature}")
    krs_gate.require_route(
        harness.gate, emitted.directory, "java-llvm-reference", environment=harness.environment,
    )
    java = harness._java_outcomes(emitted, FLOAT_JAVA_ONLY_PROGRAMS, sort="Exp")
    for program in FLOAT_JAVA_ONLY_PROGRAMS:
        expected = {"parse": program.parse, "run": program.run}
        if java[program.name] != expected:
            raise GateError(f"{FLOAT_JAVA_ONLY.package} {program.name}: Java K observed {java[program.name]}")
    harness.pins.expect(("outcomes", FLOAT_JAVA_ONLY.package), java)
    for route in ("native-rust", "native-llvm", "browser"):
        try:
            krs_gate.require_route(harness.gate, emitted.directory, route, environment=harness.environment)
        except GateError as refusal:
            harness.pins.expect(("capability_refusals", route), str(refusal))
        else:
            raise GateError(f"the {route} route accepted a ground Float application")
    print(
        "PASS krs-builtin-float-java-only: Java K runs it; the native and browser routes refuse it "
        "before compiling"
    )


def console_io(harness: FixtureGate) -> None:
    """Run the console program natively and on Java K and pin both refusals (KF-035)."""

    harness.check(IO)
    harness.expand(IO)
    emitted = harness.emit(IO)
    symbols = json.loads((emitted.directory / "symbols.json").read_text(encoding="utf-8"))
    requirements = sorted(
        (row["feature"], row["symbol"]) for row in symbols.get("capability_requirements") or ()
    )
    if requirements != [("ConsoleIO", "<input>"), ("ConsoleIO", "<output>")]:
        raise GateError(f"symbols.json records {requirements!r} as the capability requirements")
    source = emitted.source.read_text(encoding="utf-8")
    for line in (
        '<input stream="stdin"> .List </input>',
        '<output stream="stdout"> .List </output>',
        '<status exit=""> 1 </status>',
        "<input> ListItem(I:Int) => .List ... </input>",
        "// krs-capability: ConsoleIO <input>",
    ):
        if line not in source:
            raise GateError(f"emitted K lacks `{line}`")

    directory = harness.workspace / "console" / IO.package
    directory.mkdir(parents=True, exist_ok=True)
    program = directory / "sum.pgm"
    program.write_text(IO_PROGRAM + "\n", encoding="utf-8")
    stdin = directory / "stdin.txt"
    stdin.write_text(IO_STDIN, encoding="utf-8")

    native = subprocess.run(
        IO.invocation(harness.krs).argv("run", "--output", "none", program),
        cwd=ROOT, env={**os.environ, **harness.environment}, input=IO_STDIN,
        text=True, capture_output=True, timeout=900, check=False,
    )
    native_outcome = {"stdout": native.stdout, "status": native.returncode}

    k = Snapshot(
        f"{harness.label}/{IO.package}",
        Key(tools=JAVA_TOOLS, inputs=repository_inputs([])),
        workspace=harness.workspace, refresh=harness.refresh,
        pin=Pin(harness.pins, IO.package),
    )
    compiled = harness.workspace / "kompiled" / IO.package
    kompiled = k.run(
        "kompile/definition", "kompile",
        [
            emitted.source, "--main-module", emitted.main_module,
            "--syntax-module", emitted.syntax_module,
            "--backend", "llvm", "--output-definition", compiled,
        ],
        timeout=900,
    )
    if kompiled.returncode != 0:
        raise GateError(f"{IO.package}: kompile rejected the emitted definition:\n{kompiled.stderr}")
    executed = k.run(
        "krun/sum", "krun", ["--definition", compiled, "--output", "none", program],
        timeout=120, stdin=stdin,
    )
    print(f"PASS builtin-domains {IO.package} reference snapshot: {k.finish()}")
    java_outcome = {"stdout": executed.stdout, "status": executed.returncode}
    for route, outcome in (("native", native_outcome), ("Java K", java_outcome)):
        if outcome != IO_EXPECTED:
            detail = native.stderr if route == "native" else executed.stderr
            raise GateError(f"{IO.package}: {route} printed {outcome!r}, expected {IO_EXPECTED!r}:\n{detail}")
    harness.pins.expect(("console_io", IO.package), {"native": native_outcome, "java": java_outcome})

    searched = harness._krs(IO, "search", program, check=False)
    lines = diagnostic_lines(searched.stderr)
    if searched.returncode != 1 or not lines:
        raise GateError(f"{IO.package}: krs search exited {searched.returncode}:\n{searched.stderr}")
    harness.pins.expect(("diagnostics", "io-search"), lines)
    try:
        krs_gate.require_route(harness.gate, emitted.directory, "browser", environment=harness.environment)
    except GateError as refusal:
        harness.pins.expect(("capability_refusals", "browser-console-io"), str(refusal))
    else:
        raise GateError("the browser route accepted a definition with stream cells")
    print(
        f"PASS {IO.package}: stdout {IO_EXPECTED['stdout']!r} and status {IO_EXPECTED['status']} "
        "natively and on Java K; search and the browser route refuse it"
    )


def raw_warnings(harness: FixtureGate, fixture: Fixture, code: str) -> None:
    """Require `krs check` to pass with the raw K warning `code` and pin its warnings."""

    process = harness._krs(fixture, "check", check=False)
    lines = diagnostic_lines(process.stderr)
    if process.returncode != 0 or not any(line.startswith(f"warning[{code}]: ") for line in lines):
        raise GateError(f"{fixture.package}: krs check exited {process.returncode} without warning[{code}]:\n{process.stderr}")
    harness.pins.expect(("raw_warnings", fixture.package), lines)


def java_haskell_outcomes(harness: FixtureGate, emitted, programs) -> dict[str, dict[str, Any]]:
    """Run `programs` on Java K's Haskell backend, which evaluates the KRYPTO hooks."""

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
            "--backend", "haskell", "--hook-namespaces", "KRYPTO",
            "--output-definition", compiled,
        ],
        timeout=900,
    )
    if kompiled.returncode != 0:
        raise GateError(f"{package}: kompile --backend haskell rejected the emitted definition:\n{kompiled.stderr}")
    outcomes: dict[str, dict[str, Any]] = {}
    for program in programs:
        path = directory / f"{program.name}.pgm"
        path.write_text(program.text + "\n", encoding="utf-8")
        executed = k.run(f"krun/{program.name}", "krun", ["--definition", compiled, path], timeout=300)
        outcomes[program.name] = {"parse": ACCEPTED, "run": java_run_outcome(executed)}
    print(f"PASS builtin-domains {package} Haskell reference snapshot: {k.finish()}")
    return outcomes


def raw_k(harness: FixtureGate) -> None:
    """Run the raw K escapes on both routes and pin every refusal (KF-037)."""

    raw_warnings(harness, RAW_K, "krs::semantic::raw-k")
    harness.expand(RAW_K)
    emitted = harness.emit(RAW_K)
    source = emitted.source.read_text(encoding="utf-8")
    for line in (
        "  // raw_k! src/lib.rs:38:1 (opaque to KRS)\n"
        "  rule <k> double(I:Int) => I +Int I ... </k> [label(raw-double)]\n",
        "  imports INT\n",
    ):
        if line not in source:
            raise GateError(f"{RAW_K.package}: emitted K lacks {line!r}")
    harness.compare(emitted, RAW_K_PROGRAMS, sort="Exp")
    print(f"PASS {RAW_K.package}: the raw rule runs natively and on Java K's LLVM backend")

    raw_warnings(harness, RAW_HOOK, "krs::expand::raw-hook")
    harness.expand(RAW_HOOK)
    emitted = harness.emit(RAW_HOOK)
    if "[symbol(keccakHex), function, total, hook(KRYPTO.keccak256)]" not in emitted.source.read_text(encoding="utf-8"):
        raise GateError(f"{RAW_HOOK.package}: emitted K lacks hook(KRYPTO.keccak256)")
    native = harness._native_outcomes(emitted, RAW_HOOK_PROGRAMS)
    java = java_haskell_outcomes(harness, emitted, RAW_HOOK_PROGRAMS)
    for program in RAW_HOOK_PROGRAMS:
        expected = {"parse": program.parse, "run": program.run}
        for route, outcomes in (("native", native), ("Java K Haskell", java)):
            if outcomes[program.name] != expected:
                raise GateError(f"{RAW_HOOK.package} {program.name}: {route} observed {outcomes[program.name]}, expected {expected}")
    harness.pins.expect(("outcomes", RAW_HOOK.package), {program.name: native[program.name] for program in RAW_HOOK_PROGRAMS})
    print(f"PASS {RAW_HOOK.package}: the quoted hook runs natively and on Java K's Haskell backend")

    for name, fixture, extra in (
        ("raw-denied", RAW_DENIED, ()),
        ("raw-strict", RAW_STRICT, ()),
        ("raw-profile-strict", RAW_K, ("--profile", "strict")),
    ):
        harness.diagnostic(name, fixture, *extra)
    output = harness.workspace / "native" / RAW_PARSE_ERROR.package
    built = harness._krs(RAW_PARSE_ERROR, "build", "--output", output, check=False)
    lines = diagnostic_lines(built.stderr)
    if built.returncode == 0 or not any(line.startswith("error[krs::native::raw-k-parse]: ") for line in lines):
        raise GateError(f"{RAW_PARSE_ERROR.package}: krs build exited {built.returncode}:\n{built.stderr}")
    if "packages/raw-parse-error/src/lib.rs:35:11" not in built.stderr:
        raise GateError(f"{RAW_PARSE_ERROR.package}: the parse error does not name the raw_k! text:\n{built.stderr}")
    harness.pins.expect(("diagnostics", "raw-parse-error"), lines)
    print(
        "PASS raw K: without allow-raw-k and under the strict profile both escapes fail; "
        "a raw parse error fails the native build closed"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 builtin-domains ledger")

    target = checkout_scratch() / "builtin-domains-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target), "CARGO_TERM_COLOR": "never"}
    krs = build(environment, target=target)
    gate = krs_gate.configured_or_build(target)
    check_packages("builtin-domains", krs=krs, env=environment, target_dir=target)

    with tempfile.TemporaryDirectory(prefix="krs-builtin-domains-") as temporary:
        workspace = Path(temporary)
        harness = FixtureGate(
            "builtin-domains", pins, workspace, krs, gate, environment,
            refresh=arguments.refresh_reference,
            divergences=pins.get("known_divergences", {}),
        )
        for package, programs in CASES:
            fixture = Fixture(MANIFEST, package)
            harness.check(fixture)
            harness.expand(fixture)
            emitted = harness.emit(fixture)
            harness.compare(emitted, programs, sort="Exp")
            if package == "krs-builtin-k-equal":
                ite_instances(harness, emitted)
            pinned = len(harness.divergences.get(package, {}))
            print(
                f"PASS {package}: {len(programs) - pinned} programs agree natively and on Java K"
                + (f"; {pinned} pinned divergences unchanged" if pinned else "")
            )

        java_only_floats(harness)
        console_io(harness)
        raw_k(harness)

    pins.finish("builtin-domains")
    print("PASS builtin-domains")
    return 0


if __name__ == "__main__":
    entry("builtin-domains", main, errors=(OSError,))
