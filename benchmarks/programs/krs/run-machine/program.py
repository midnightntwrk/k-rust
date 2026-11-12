#!/usr/bin/env python3
"""Writes the long-run `krs run` benchmark's program to standard output, as bytes.

The program is for the machine in krs/tests/perf/fixtures/run-machine.
It clears `--clear` bytes of memory from 0xC000 (default 4096), then polls an I/O register that
nothing writes, so it runs for any number of steps:

            liw r4, 0xC000
            liw r2, CLEAR
    clear:  st  [r4], r0
            inc r4
            dec r2
            jr  nz, clear
    poll:   ldh r0, [0x44]
            cmp r0, 0x90
            jr  nz, poll
            stop

The bytes depend on `--clear` alone.
`--check-map` checks instead that the opcode map below, which is the one `Decode` states
(cpu/src/decode.rs), gives every byte exactly one row.
"""

import argparse
import sys

# One row per `Decode` equation, in its order: (name, template or opcode, condition on the fields).
OPCODE_MAP = [
    ("nop", 0x00, None),
    ("stop", 0x08, None),
    ("ei", 0x10, None),
    ("jr", 0x18, None),
    ("jr_cc", "001cc000", None),
    ("li", "00rrr001", None),
    ("liw", "00rrr010", None),
    ("inc", "00rrr011", None),
    ("dec", "00rrr100", None),
    ("shl", 0x05, None),
    ("shr", 0x0D, None),
    ("rol", 0x15, None),
    ("ror", 0x1D, None),
    ("not", 0x25, None),
    ("neg", 0x2D, None),
    ("swap", 0x35, None),
    ("clr", 0x3D, None),
    ("ldh", "00rrr110", None),
    ("sth", "00rrr111", None),
    ("di", 0x76, None),
    ("test", "01dddsss", lambda f: f["d"] == f["s"] and f["d"] != 6),
    ("mov", "01dddsss", lambda f: f["d"] != f["s"] and f["d"] != 6 and f["s"] != 6),
    ("mov_from", "01ddd110", lambda f: f["d"] != 6),
    ("mov_to", "01110sss", lambda f: f["s"] != 6),
    ("alu", "10ooosss", lambda f: f["s"] != 6),
    ("alu_at", "10ooo110", None),
    ("alu_n", "11ooo000", None),
    ("load_at", "110aa001", None),
    ("store_at", "111aa001", None),
    ("jp_cc", "110cc010", None),
    ("jp", 0xE2, None),
    ("jp_link", 0xEA, None),
    ("illegal", 0xF2, None),
    ("clc", 0xFA, None),
    ("add_n", "11rrr011", None),
    ("sub_n", "11rrr100", None),
    ("cmp_n", "11rrr101", None),
    ("and_n", "11rrr110", None),
    ("xor_n", "11rrr111", None),
]


def fields(template, opcode):
    """The fields `template` reads of `opcode`, or None where its fixed bits differ."""
    values = {}
    for position, char in enumerate(template):
        bit = (opcode >> (7 - position)) & 1
        if char in "01":
            if bit != int(char):
                return None
        else:
            values[char] = values.get(char, 0) << 1 | bit
    return values


def rows(opcode):
    """The names of the rows that decode `opcode`."""
    names = []
    for name, pattern, condition in OPCODE_MAP:
        if isinstance(pattern, int):
            if pattern == opcode:
                names.append(name)
            continue
        values = fields(pattern, opcode)
        if values is not None and (condition is None or condition(values)):
            names.append(name)
    return names


def encode(name, **values):
    """The opcode of row `name` with the given field values."""
    for row, pattern, _ in OPCODE_MAP:
        if row != name:
            continue
        if isinstance(pattern, int):
            opcode = pattern
        else:
            opcode = 0
            remaining = {field: pattern.count(field) for field in values}
            for char in pattern:
                if char in "01":
                    bit = int(char)
                else:
                    remaining[char] -= 1
                    bit = (values[char] >> remaining[char]) & 1
                opcode = opcode << 1 | bit
        assert rows(opcode) == [name], (name, values, rows(opcode))
        return opcode
    raise KeyError(name)


def program(clear):
    code = bytearray()
    code += bytes([encode("liw", r=4), 0x00, 0xC0])
    code += bytes([encode("liw", r=2), clear & 0xFF, clear >> 8])
    clear_loop = len(code)
    code += bytes([encode("store_at", a=0)])
    code += bytes([encode("inc", r=4)])
    code += bytes([encode("dec", r=2)])
    code += bytes([encode("jr_cc", c=0), 0])
    code[-1] = (clear_loop - len(code)) & 0xFF
    poll_loop = len(code)
    code += bytes([encode("ldh", r=0), 0x44])
    code += bytes([encode("alu_n", o=7), 0x90])
    code += bytes([encode("jr_cc", c=0), 0])
    code[-1] = (poll_loop - len(code)) & 0xFF
    code += bytes([encode("stop")])
    return bytes(code)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--clear", type=int, default=4096, help="bytes the first loop clears")
    parser.add_argument("--check-map", action="store_true", help="check the opcode map")
    arguments = parser.parse_args()
    if arguments.check_map:
        wrong = {opcode: rows(opcode) for opcode in range(256) if len(rows(opcode)) != 1}
        if wrong:
            sys.exit(f"opcodes without exactly one row: {wrong}")
        print(f"{len(OPCODE_MAP)} rows give each of the 256 opcodes exactly one row")
        return
    if not 1 <= arguments.clear <= 0x2000:
        sys.exit("--clear must be between 1 and 8192, so that the cleared bytes stay below 0xE000")
    sys.stdout.buffer.write(program(arguments.clear))


if __name__ == "__main__":
    main()
