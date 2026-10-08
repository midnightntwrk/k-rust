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
- `strings`: String literals (KF-008) in equations, readable patterns, results,
  and programs, including the Latin-1 code point `\xc1`, and the STRING
  operations with `bytes::from_string`/`to_string`.

`known_divergences` in `pins.json` pins the `\xc1` programs on which the routes
disagree. k-rust stores a `\xHH` escape as the raw byte, so its `ordChar`,
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
import os
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError, entry, krs_gate  # noqa: E402
from support.fixture_gate import Fixture, FixtureGate, Program  # noqa: E402
from support.krs import build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import add_refresh_argument  # noqa: E402
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

CASES = (
    ("krs-builtin-int-ops", INT_OPS),
    ("krs-builtin-int-sign", INT_SIGN),
    ("krs-builtin-int-sign-unsigned", INT_SIGN_UNSIGNED),
    ("krs-builtin-bool-ops", BOOL_OPS),
    ("krs-builtin-bytes-ops", BYTES_OPS),
    ("krs-builtin-set-ops", SET_OPS),
    ("krs-builtin-map-ops", MAP_OPS),
    ("krs-builtin-strings", STRINGS),
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
            pinned = len(harness.divergences.get(package, {}))
            print(
                f"PASS {package}: {len(programs) - pinned} programs agree natively and on Java K"
                + (f"; {pinned} pinned divergences unchanged" if pinned else "")
            )

    pins.finish("builtin-domains")
    print("PASS builtin-domains")
    return 0


if __name__ == "__main__":
    entry("builtin-domains", main, errors=(OSError,))
