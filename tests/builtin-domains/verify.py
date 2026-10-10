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
  and `max_value`. Programs supply every operand, so no application is ground.
  `negate` leaves a Float in the computation cell, which both routes print as
  K's LLVM runtime does (`-0.15000000000000000e1`, `-0.100000001e0f`,
  `Infinity`, `NaNf`, `-0.00000000000000000e0`); every other result is a Bool
  or an Int. Those programs and two Float literals left as the result (`1.5`,
  `0.1f`) also run through `krs run` and `krs search` with `--output kast`,
  `kore`, and `json`, which must print each Float as `krun` and `krun --search`
  do (`#token("-0.15000000000000000e1","Float")`, not k-rust's
  `-1.5000000000000000e+00p53x11` or the literal's own text): the KAST text
  byte for byte, the KORE cells and the KAST JSON term as values;
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
- `io-hooks`: the direct console writes `io::write` and `io::putc` (K's
  `#write` and `#putc`). The programs `hello` and `bye` print `hi` and a
  newline, and `A`, through Java K's `krun --output none` on the LLVM backend;
  `both` writes and then continues with `bye` in one rule, because a `K`-sorted
  item splices into a `[..]` result as K's `~>` does, and prints both.
  KRS records the `ConsoleWriteHook` requirement, which the in-process k-rust
  backend lacks because it has no console state: `krs run` refuses the
  definition with the pinned `krs::capability::unavailable` message before
  compiling it, while `krs build --backend llvm` accepts it and writes the
  same `definition.kore` as Java K's LLVM kompile (`krs-gate kore-compare`);
- `io-log`: `io::log` (K's `#log`, hook `IO.logString`). The program `trace`
  logs the line `traced`, and `twice` logs `one` and continues with `trace` in
  one rule: `krs run` and `krs search` write the lines to standard
  error before their own status lines, and Java K's `krun` and `krun --search`
  on the LLVM backend (kompiled with `--enable-search`) write the same bytes
  to standard error. Like every `K-IO` operation it records the `ConsoleIO`
  requirement, which only the browser route lacks. The native
  `definition.kore` agrees with Java K's;
- `sort-tests`: K's generated sort predicates and projections (KF-013),
  `k::is!(S, t)` (`isS(T)`) and `k::project!(S, t)` (`{T}:>S`), in term rules
  and readable clauses, in results and guards: `chk(5)` is `true`,
  `chk(box(1))` is stuck because its guard fails, `prj(4)` is `5`, the user
  sort `Value` decides `isval`, a projected list lookup has one cast, and an
  equation `kind` computes with `k::is!` in its result. The
  failing projections `prj(true)` and `unbox(box(true))` are pinned
  divergences: Java K's LLVM backend aborts with `project:Int ( true ~> .K )`
  (`undefined`), while k-rust splits on whether the projection is defined and
  ends in a stuck leaf and a `#Bottom` (`trivial`) leaf, as for `go()` below. `sort-test-matched` (a sort test in a rule
  subject) and `sort-test-project-k` (a projection into `K`) pin their
  `krs::analysis::invalid-sort-test` errors, and `sort-test-trivial` pins the
  `krs::analysis::trivial-sort-test` warnings of an identity projection and of
  `k::is!(K, ..)`;
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

`known_divergences` in `pins.json` pins the two failing projections of
`sort-tests`, and `ite-undefined-branch`, the k-equal
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
import re
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


def float_case(name: str, text: str, printed: str) -> Program:
    """A program whose result is a Float: both routes must print it alike."""

    return Program(name, text, "accepted", printed, cells=(("k", f"{printed} ~> .K"),))


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
    float_case("negate-binary64", "negate(1.5)", "-0.15000000000000000e1"),
    float_case("negate-binary32", "negate(0.1f)", "-0.100000001e0f"),
    float_case("negate-infinity", "negate(-Infinity)", "Infinity"),
    float_case("negate-nan-binary32", "negate(NaNf)", "NaNf"),
    float_case("negate-zero", "negate(0.0)", "-0.00000000000000000e0"),
    float_case("negate-subnormal", "negate(2.5e-310)", "-0.25000000000000171e-309"),
)

FLOATS_PACKAGE = "krs-builtin-floats"
FLOAT_OUTPUTS = {
    **{program.name: program.text for program in FLOATS if program.name.startswith("negate-")},
    "literal-binary64": "1.5",
    "literal-binary32": "0.1f",
}
"""The `floats` programs whose result holds a Float, each printed by every `--output` format."""
FLOAT_KORE = re.compile(r'\\dv\{SortFloat\{\}\}\("([^"]*)"\)')

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

HOOKS = Fixture(MANIFEST, "krs-builtin-io-hooks")
HOOKS_EXPECTED = {
    "hello": {"stdout": "hi\n", "status": 0},
    "bye": {"stdout": "A", "status": 0},
    "both": {"stdout": "hi\nA", "status": 0},
}

LOG = Fixture(MANIFEST, "krs-builtin-io-log")
LOG_EXPECTED = {"trace": "traced\n", "twice": "one\ntraced\n"}
"""The standard error of each `io-log` program on Java K, which `krs run` and `krs search` must print first."""

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

SORT_TESTS = (
    case("chk-int", "chk(5)", "true"),
    case("chk-bool", "chk(true)", "true"),
    case("chk-guard-fails", "chk(box(1))", "chk(box(1))"),
    case("prj", "prj(4)", "5"),
    case("prj-undefined", "prj(true)", "undefined"),
    case("unbox", "unbox(box(1))", "2"),
    case("unbox-undefined", "unbox(box(true))", "undefined"),
    case("isval-value", "isval(3)", "1"),
    case("isval-not-value", "isval(box(3))", "0"),
    case("nth", "nth(1)", "20"),
    case("kind-int", "kind(7)", "1"),
    case("kind-box", "kind(box(7))", "0"),
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
    (FLOATS_PACKAGE, FLOATS),
    ("krs-builtin-sort-tests", SORT_TESTS),
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


def float_outputs(harness: FixtureGate, emitted) -> None:
    """Require `krs run` and `krs search` to print Floats as `krun` does in every output format.

    The LLVM runtime prints a Float in MPFR's form (`-0.15000000000000000e1`)
    in `--output kast`, `kore`, and `json` alike, while k-rust carries its own
    canonical token (`-1.5000000000000000e+00p53x11`) and a program literal
    keeps its text (`1.5`). `krs run --output kast` must print krun's bytes,
    `--output kore` the same cells (k-rust's KORE printer spaces its commas),
    and `--output json` the same KAST JSON term; `krs search --output kast`
    and `json` must print the configuration of `krun --search`'s one
    `#Equals` solution, and every KORE output the same Float tokens.
    """

    directory = harness.workspace / "float-outputs"
    directory.mkdir(parents=True, exist_ok=True)
    name = f"{FLOATS_PACKAGE}-outputs"
    k = Snapshot(
        f"{harness.label}/{name}",
        Key(tools=JAVA_TOOLS, inputs=repository_inputs([])),
        workspace=harness.workspace, refresh=harness.refresh,
        pin=Pin(harness.pins, name),
    )
    compiled = harness.workspace / "kompiled" / name
    kompiled = k.run(
        "kompile/definition", "kompile",
        [
            emitted.source, "--main-module", emitted.main_module,
            "--syntax-module", emitted.syntax_module,
            "--backend", "llvm", "--enable-search", "--output-definition", compiled,
        ],
        timeout=900,
    )
    if kompiled.returncode != 0:
        raise GateError(f"{name}: kompile rejected the emitted definition:\n{kompiled.stderr}")

    def krs(command: str, output: str, program: Path) -> str:
        native = harness._krs(emitted.fixture, command, "--output", output, program)  # noqa: SLF001
        return native.stdout

    def krun(label: str, program: Path, *arguments: str) -> str:
        java = k.run(label, "krun", ["--definition", compiled, *arguments, program], timeout=120)
        if java.returncode != 0:
            raise GateError(f"{name} {label}: krun exited {java.returncode}:\n{java.stderr}")
        return java.stdout

    def mismatch(program: str, what: str, native: Any, java: Any) -> GateError:
        return GateError(f"{name} {program}: {what} differs from krun's:\n  krs:  {native!r}\n  krun: {java!r}")

    observed: dict[str, dict[str, str]] = {}
    with krs_gate.Session(harness.gate, environment=harness.environment) as session:
        session.load(emitted.definition_ir, emitted.main_module)
        for program_name, text in FLOAT_OUTPUTS.items():
            program = directory / f"{program_name}.pgm"
            program.write_text(text + "\n", encoding="utf-8")
            run_kast = krs("run", "kast", program)
            java_kast = krun(f"krun-kast/{program_name}", program, "--output", "kast")
            if run_kast != java_kast:
                raise mismatch(program_name, "krs run --output kast", run_kast, java_kast)

            run_kore = krs("run", "kore", program)
            java_kore = krun(f"krun-kore/{program_name}", program, "--output", "kore")
            session.read(run_kore, f"{program_name}-native")
            session.read(java_kore, f"{program_name}-java")
            cells = ["k", "generatedCounter"]
            native_cells = session.observe(f"{program_name}-native", cells)
            java_cells = session.observe(f"{program_name}-java", cells)
            if native_cells != java_cells:
                raise mismatch(program_name, "krs run --output kore", native_cells, java_cells)
            floats = FLOAT_KORE.findall(java_kore)
            if not floats or FLOAT_KORE.findall(run_kore) != floats:
                raise mismatch(program_name, "the Floats of krs run --output kore", run_kore, java_kore)

            run_json = json.loads(krs("run", "json", program))["run"]["state"]
            java_json = json.loads(krun(f"krun-json/{program_name}", program, "--output", "json"))
            if run_json != java_json:
                raise mismatch(program_name, "krs run --output json", run_json, java_json)

            # `krun --search` prints its one solution as `#Equals(Result, configuration)`.
            search_kast = krs("search", "kast", program)
            java_search_kast = krun(f"krun-search-kast/{program_name}", program, "--search", "--output", "kast")
            if java_search_kast != f"#Equals{{GeneratedTopCell,GeneratedTopCell}}(Result,{search_kast.strip()})\n":
                raise mismatch(program_name, "krs search --output kast", search_kast, java_search_kast)
            [solution] = json.loads(krs("search", "json", program))["search"]["solutions"]
            java_search = json.loads(
                krun(f"krun-search-json/{program_name}", program, "--search", "--output", "json"),
            )
            equals = java_search["term"]
            if equals["label"]["name"] != "#Equals" or solution["state"]["term"] != equals["args"][1]:
                raise mismatch(program_name, "krs search --output json", solution["state"], java_search)
            search_kore = krs("search", "kore", program)
            if FLOAT_KORE.findall(search_kore) != floats:
                raise mismatch(program_name, "the Floats of krs search --output kore", search_kore, floats)
            observed[program_name] = {"kast": run_kast.strip(), "kore_floats": " ".join(floats)}
    print(f"PASS builtin-domains {name} reference snapshot: {k.finish()}")
    harness.pins.expect(("float_outputs", FLOATS_PACKAGE), observed)
    print(
        f"PASS {name}: krs run and krs search print {len(observed)} Float results as krun does "
        "in --output kast, kore, and json"
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


def console_hooks(harness: FixtureGate) -> None:
    """Run the direct console writes on Java K and pin the native refusal."""

    harness.check(HOOKS)
    harness.expand(HOOKS)
    emitted = harness.emit(HOOKS)
    symbols = json.loads((emitted.directory / "symbols.json").read_text(encoding="utf-8"))
    requirements = sorted(
        (row["feature"], row["symbol"]) for row in symbols.get("capability_requirements") or ()
    )
    if requirements != [
        ("ConsoleIO", "both"), ("ConsoleIO", "bye"), ("ConsoleIO", "hello"),
        ("ConsoleWriteHook", "both"), ("ConsoleWriteHook", "bye"), ("ConsoleWriteHook", "hello"),
    ]:
        raise GateError(f"{HOOKS.package}: symbols.json records {requirements!r} as the capability requirements")
    source = emitted.source.read_text(encoding="utf-8")
    for line in (
        "  // krs-capability: ConsoleWriteHook hello\n",
        '<k> hello => #write(1, "hi\\n") ... </k>',
        "<k> bye => #putc(1, 65) ... </k>",
        '<k> both => #write(1, "hi\\n") ~> bye ... </k>',
    ):
        if line not in source:
            raise GateError(f"{HOOKS.package}: emitted K lacks {line!r}")

    directory = harness.workspace / "console-hooks" / HOOKS.package
    directory.mkdir(parents=True, exist_ok=True)
    k = Snapshot(
        f"{harness.label}/{HOOKS.package}",
        Key(tools=JAVA_TOOLS, inputs=repository_inputs([])),
        workspace=harness.workspace, refresh=harness.refresh,
        pin=Pin(harness.pins, HOOKS.package),
    )
    compiled = harness.workspace / "kompiled" / HOOKS.package
    kompiled = k.run(
        "kompile/definition", "kompile",
        [
            emitted.source, "--main-module", emitted.main_module,
            "--syntax-module", emitted.syntax_module,
            "--backend", "llvm", "--output-definition", compiled,
        ],
        timeout=900,
        outputs=(harness.java_kore_output(emitted, compiled),),
    )
    if kompiled.returncode != 0:
        raise GateError(f"{HOOKS.package}: kompile rejected the emitted definition:\n{kompiled.stderr}")
    java: dict[str, dict[str, Any]] = {}
    for name in HOOKS_EXPECTED:
        program = directory / f"{name}.pgm"
        program.write_text(name + "\n", encoding="utf-8")
        executed = k.run(
            f"krun/{name}", "krun", ["--definition", compiled, "--output", "none", program], timeout=120,
        )
        java[name] = {"stdout": executed.stdout, "status": executed.returncode}
    print(f"PASS builtin-domains {HOOKS.package} reference snapshot: {k.finish()}")
    if java != HOOKS_EXPECTED:
        raise GateError(f"{HOOKS.package}: Java K printed {java!r}, expected {HOOKS_EXPECTED!r}")
    harness.pins.expect(("console_hooks", HOOKS.package), java)

    refused = harness._krs(HOOKS, "run", "--output", "none", directory / "hello.pgm", check=False)  # noqa: SLF001
    lines = diagnostic_lines(refused.stderr)
    if refused.returncode == 0 or not lines or not lines[0].startswith("error[krs::capability::unavailable]: "):
        raise GateError(f"{HOOKS.package}: krs run exited {refused.returncode} without the capability refusal:\n{refused.stderr}")
    if refused.stdout:
        raise GateError(f"{HOOKS.package}: krs run printed {refused.stdout!r} before refusing")
    harness.pins.expect(("diagnostics", "io-hooks-run"), lines)
    native_llvm = harness.workspace / "native-llvm" / HOOKS.package
    harness._krs(HOOKS, "build", "--backend", "llvm", "--output", native_llvm)  # noqa: SLF001
    krs_gate.require_route(harness.gate, emitted.directory, "java-llvm-reference", environment=harness.environment)
    harness.compare_kore(emitted, native=native_llvm)
    print(
        f"PASS {HOOKS.package}: Java K prints {HOOKS_EXPECTED['hello']['stdout']!r}, "
        f"{HOOKS_EXPECTED['bye']['stdout']!r}, and {HOOKS_EXPECTED['both']['stdout']!r}; krs run refuses the "
        "definition, and krs build --backend llvm accepts it with the same KORE as Java K"
    )


def log_prefix(stderr: str, command: str) -> str:
    """The standard error of a `krs run` or `krs search` before its own report lines."""

    lines = stderr.splitlines(keepends=True)
    for index, line in enumerate(lines):
        if line.startswith((f"krs {command}: ", "solution ")):
            return "".join(lines[:index])
    raise GateError(f"krs {command} printed no status line:\n{stderr}")


def console_log(harness: FixtureGate) -> None:
    """Require `krs run` and `krs search` to print `io::log` lines to standard error as krun does."""

    harness.check(LOG)
    harness.expand(LOG)
    emitted = harness.emit(LOG)
    symbols = json.loads((emitted.directory / "symbols.json").read_text(encoding="utf-8"))
    requirements = sorted(
        (row["feature"], row["symbol"]) for row in symbols.get("capability_requirements") or ()
    )
    if requirements != [("ConsoleIO", "trace"), ("ConsoleIO", "twice")]:
        raise GateError(f"{LOG.package}: symbols.json records {requirements!r} as the capability requirements")
    source = emitted.source.read_text(encoding="utf-8")
    for line in ('<k> trace => #log("traced") ... </k>', '<k> twice => #log("one") ~> trace ... </k>'):
        if line not in source:
            raise GateError(f"{LOG.package}: emitted K lacks {line!r}")

    directory = harness.workspace / "console-log" / LOG.package
    directory.mkdir(parents=True, exist_ok=True)
    k = Snapshot(
        f"{harness.label}/{LOG.package}",
        Key(tools=JAVA_TOOLS, inputs=repository_inputs([])),
        workspace=harness.workspace, refresh=harness.refresh,
        pin=Pin(harness.pins, LOG.package),
    )
    compiled = harness.workspace / "kompiled" / LOG.package
    kompiled = k.run(
        "kompile/definition", "kompile",
        [
            emitted.source, "--main-module", emitted.main_module,
            "--syntax-module", emitted.syntax_module,
            "--backend", "llvm", "--enable-search", "--output-definition", compiled,
        ],
        timeout=900,
        outputs=(harness.java_kore_output(emitted, compiled),),
    )
    if kompiled.returncode != 0:
        raise GateError(f"{LOG.package}: kompile rejected the emitted definition:\n{kompiled.stderr}")
    observed: dict[str, dict[str, Any]] = {}
    for name, expected in LOG_EXPECTED.items():
        program = directory / f"{name}.pgm"
        program.write_text(name + "\n", encoding="utf-8")
        java_run = k.run(
            f"krun/{name}", "krun", ["--definition", compiled, "--output", "none", program], timeout=120,
        )
        java_search = k.run(
            f"krun-search/{name}", "krun", ["--definition", compiled, "--search", program], timeout=120,
        )
        native_run = harness._krs(LOG, "run", "--output", "none", program, check=False)  # noqa: SLF001
        native_search = harness._krs(LOG, "search", program, check=False)  # noqa: SLF001
        outcomes = {
            "java-run": {"stderr": java_run.stderr, "status": java_run.returncode},
            "java-search": {"stderr": java_search.stderr, "status": java_search.returncode},
            "native-run": {"stderr": log_prefix(native_run.stderr, "run"), "status": native_run.returncode},
            "native-search": {
                "stderr": log_prefix(native_search.stderr, "search"), "status": native_search.returncode,
            },
        }
        for route, outcome in outcomes.items():
            if outcome != {"stderr": expected, "status": 0}:
                raise GateError(f"{LOG.package} {name}: {route} wrote {outcome!r}, expected {expected!r} on standard error")
        observed[name] = outcomes
    print(f"PASS builtin-domains {LOG.package} reference snapshot: {k.finish()}")
    harness.pins.expect(("console_log", LOG.package), observed)
    harness.compare_kore(emitted)
    print(
        f"PASS {LOG.package}: krs run, krs search, krun, and krun --search write the same "
        "io::log lines to standard error, and the native KORE agrees with Java K's"
    )


def raw_warnings(harness: FixtureGate, fixture: Fixture, code: str) -> None:
    """Require `krs check` to pass with the raw K warning `code` and pin its warnings."""

    process = harness._krs(fixture, "check", check=False)
    lines = diagnostic_lines(process.stderr)
    if process.returncode != 0 or not any(line.startswith(f"warning[{code}]: ") for line in lines):
        raise GateError(f"{fixture.package}: krs check exited {process.returncode} without warning[{code}]:\n{process.stderr}")
    harness.pins.expect(("raw_warnings", fixture.package), lines)


def sort_test_diagnostics(harness: FixtureGate) -> None:
    """Pin the sort-test errors and the trivial-sort-test warnings (KF-013)."""

    for name in ("sort-test-matched", "sort-test-project-k"):
        lines = harness.diagnostic(name, Fixture(MANIFEST, f"krs-builtin-{name}")).splitlines()
        if not lines[0].startswith("error[krs::analysis::invalid-sort-test]: "):
            raise GateError(f"{name}: expected krs::analysis::invalid-sort-test, got {lines[0]}")
    fixture = Fixture(MANIFEST, "krs-builtin-sort-test-trivial")
    process = harness._krs(fixture, "check", check=False)
    lines = diagnostic_lines(process.stderr)
    code = "krs::analysis::trivial-sort-test"
    if process.returncode != 0 or sum(line.startswith(f"warning[{code}]: ") for line in lines) != 2:
        raise GateError(f"{fixture.package}: krs check exited {process.returncode} without two warning[{code}]:\n{process.stderr}")
    harness.pins.expect(("sort_test_warnings", fixture.package), lines)
    print("PASS sort-test diagnostics: two invalid-sort-test errors and two trivial-sort-test warnings pinned")


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
            if package == FLOATS_PACKAGE:
                float_outputs(harness, emitted)

        sort_test_diagnostics(harness)
        java_only_floats(harness)
        console_io(harness)
        console_hooks(harness)
        console_log(harness)
        raw_k(harness)

    pins.finish("builtin-domains")
    print("PASS builtin-domains")
    return 0


if __name__ == "__main__":
    entry("builtin-domains", main, errors=(OSError,))
