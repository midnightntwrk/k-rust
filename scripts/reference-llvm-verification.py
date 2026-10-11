#!/usr/bin/env python3
"""Verification copies: KORE in the declaration vocabulary of the KORE verifier (N38, N47)."""

from pathlib import Path
import re
import sys


TOKENS = re.compile(
    r'"(?:[^"\\]|\\.)*"|//[^\n]*|/\*[\s\S]*?\*/|\s+|[{}\[\](),:]|[^\s{}\[\](),:"]+'
)


def edit_symbol_declarations(source: str, addition) -> tuple[str, int]:
    """Append `addition(name, attributes)` to the attribute list of every symbol declaration for
    which it returns text, preserving every other byte; return the copy and the number changed.

    `attributes` lists each top-level attribute pattern of the declaration as its tokens.
    """
    tokens = []
    consumed = 0
    for match in TOKENS.finditer(source):
        if match.start() != consumed:
            raise ValueError("unrecognized KORE token")
        consumed = match.end()
        token = match.group()
        if not token.isspace() and not token.startswith(("//", "/*")):
            tokens.append((token, match.start()))
    if consumed != len(source):
        raise ValueError("unrecognized KORE token")

    edits = []
    index = 0
    while index < len(tokens):
        if tokens[index][0] not in ("symbol", "hooked-symbol"):
            index += 1
            continue
        # A declaration begins `symbol NAME{...}`; applications or variables
        # named symbol must not be mistaken for declaration keywords.
        if index + 2 >= len(tokens) or tokens[index + 2][0] != "{":
            index += 1
            continue
        name = tokens[index + 1][0]
        while index < len(tokens) and tokens[index][0] != "[":
            index += 1
        if index == len(tokens):
            raise ValueError(f"symbol {name} has no attribute list")
        index += 1
        patterns = []
        pattern = []
        depth = 0
        while index < len(tokens):
            token = tokens[index][0]
            if token == "]" and depth == 0:
                if pattern:
                    patterns.append(pattern)
                break
            if token == "," and depth == 0:
                patterns.append(pattern)
                pattern = []
            else:
                pattern.append(token)
                if token in ("{", "(", "["):
                    depth += 1
                elif token in ("}", ")", "]"):
                    depth -= 1
            index += 1
        if index == len(tokens):
            raise ValueError(f"symbol {name} has no closing attribute bracket")
        text = addition(name, patterns)
        if text is not None:
            edits.append((tokens[index][1], text))
        index += 1

    for position, text in reversed(edits):
        source = source[:position] + text + source[position:]
    return source, len(edits)


def normalize_llvm_value_productions(source: str) -> tuple[str, int]:
    """Add function only to marked symbol declarations, preserving every other byte.

    LLVM reads irreducible value applications as values without `function`.
    The verifier requires equation heads to carry `function` or `functional`;
    only its copy gains the former, which makes no totality claim.
    """

    def addition(name, patterns):
        if ["value-production", "{", "}", "(", ")"] not in patterns:
            return None
        if any(p and p[0] in ("function", "functional") for p in patterns):
            raise ValueError(
                f"LLVM value-production symbol {name} already carries function or functional"
            )
        return ", function{}()"

    return edit_symbol_declarations(source, addition)


def normalize_anywhere_injective(source: str) -> tuple[str, int]:
    """N47: add `injective` to every `anywhere` symbol declaration that lacks it, preserving
    every other byte.

    The verifier admits an application inside a function equation's argument only when its head
    is constructor-like or an injective `anywhere` symbol. `injective` is an axiom (equal
    applications have equal arguments) that an `anywhere` equation of the head may falsify, so
    the emitted definition withholds it, and whether the enclosing equation is consistent is
    decided by the compiler's own critical-pair check at that head instead. Only the
    verification copy gains the attribute, so the verifier checks every other sentence and
    every other argument; nothing compared or executed reads the copy.
    """

    def addition(name, patterns):
        if ["anywhere", "{", "}", "(", ")"] not in patterns:
            return None
        if any(p and p[0] == "injective" for p in patterns):
            return None
        return ", injective{}()"

    return edit_symbol_declarations(source, addition)


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: reference-llvm-verification.py INPUT OUTPUT", file=sys.stderr)
        return 2
    source, destination = map(Path, sys.argv[1:])
    if source.resolve() == destination.resolve():
        print("error: LLVM verification must use a separate copy", file=sys.stderr)
        return 1
    try:
        normalized, count = normalize_llvm_value_productions(source.read_bytes().decode())
        destination.write_bytes(normalized.encode())
    except (OSError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(f"N38 LLVM verification value-production declarations: {count}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
