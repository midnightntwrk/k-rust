"""Truncate a semantics port to a fraction of its rules and equations.

A real-port ladder rung keeps every declaration of the port (sorts,
constructor enums, functions, the configuration, claims, and plain Rust
items) and a deterministic, evenly spread fraction of its rewrite rules
(the statements of every `k::rules!` block) and of its equations (the
top-level `#[k::equation]` functions). Keeping every declaration is a
superset of "every declaration the kept rules reference", so the declaration
side of a rung is constant along the ladder and only rules and equations grow.

Selection is nested: the items kept at fraction `a/d` are a subset of those
kept at any larger fraction with the same denominator, so each rung adds work
to the previous one. Item `i` (counted separately for rules, over every
`k::rules!` block in source order, and for equations) is kept at `a/d` when
`floor((i + 1) a / d) > floor(i a / d)`.

The scanner here is a lexical approximation of Rust sufficient for the port
sources: it skips comments, string, raw-string, byte-string, and character
literals, distinguishes lifetimes, and tracks delimiter depth.
"""

from __future__ import annotations

from dataclasses import dataclass
import re


@dataclass(frozen=True)
class Token:
    kind: str
    """`ident`, `punct`, `open`, `close`, or `literal`."""
    text: str
    start: int
    end: int


_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_NUMBER = re.compile(r"[0-9][0-9A-Za-z_]*(\.[0-9][0-9A-Za-z_]*)?")
_RAW = re.compile(r'b?r(#*)"')


def tokenize(source: str) -> list[Token]:
    """Lex `source` into tokens with byte offsets; comments and whitespace are dropped."""

    tokens: list[Token] = []
    index = 0
    length = len(source)
    while index < length:
        char = source[index]
        if char.isspace():
            index += 1
            continue
        if source.startswith("//", index):
            newline = source.find("\n", index)
            index = length if newline < 0 else newline + 1
            continue
        if source.startswith("/*", index):
            depth, index = 1, index + 2
            while index < length and depth:
                if source.startswith("/*", index):
                    depth, index = depth + 1, index + 2
                elif source.startswith("*/", index):
                    depth, index = depth - 1, index + 2
                else:
                    index += 1
            continue
        raw = _RAW.match(source, index)
        if raw is not None:
            closing = '"' + raw.group(1)
            end = source.find(closing, raw.end())
            if end < 0:
                raise ValueError(f"unterminated raw string at offset {index}")
            tokens.append(Token("literal", source[index:end + len(closing)], index, end + len(closing)))
            index = end + len(closing)
            continue
        if char == '"' or (char == "b" and source.startswith('b"', index)):
            cursor = index + (2 if char == "b" else 1)
            while cursor < length and source[cursor] != '"':
                cursor += 2 if source[cursor] == "\\" else 1
            if cursor >= length:
                raise ValueError(f"unterminated string at offset {index}")
            tokens.append(Token("literal", source[index:cursor + 1], index, cursor + 1))
            index = cursor + 1
            continue
        if char == "'" or (char == "b" and source.startswith("b'", index)):
            quote = index + (1 if char == "b" else 0)
            if source.startswith("\\", quote + 1):
                cursor = quote + 2
                while cursor < length and source[cursor] != "'":
                    cursor += 1
                tokens.append(Token("literal", source[index:cursor + 1], index, cursor + 1))
                index = cursor + 1
                continue
            if quote + 2 < length and source[quote + 2] == "'":
                tokens.append(Token("literal", source[index:quote + 3], index, quote + 3))
                index = quote + 3
                continue
            # A lifetime or label: the quote and the identifier after it.
            tokens.append(Token("punct", "'", index, index + 1))
            index += 1
            continue
        identifier = _IDENT.match(source, index)
        if identifier is not None:
            tokens.append(Token("ident", identifier.group(0), index, identifier.end()))
            index = identifier.end()
            continue
        number = _NUMBER.match(source, index)
        if number is not None:
            tokens.append(Token("literal", number.group(0), index, number.end()))
            index = number.end()
            continue
        if char in "([{":
            tokens.append(Token("open", char, index, index + 1))
        elif char in ")]}":
            tokens.append(Token("close", char, index, index + 1))
        else:
            tokens.append(Token("punct", char, index, index + 1))
        index += 1
    return tokens


def matching(tokens: list[Token]) -> dict[int, int]:
    """Map every opening delimiter's token index to its closing token index."""

    pairs: dict[int, int] = {}
    stack: list[int] = []
    for position, token in enumerate(tokens):
        if token.kind == "open":
            stack.append(position)
        elif token.kind == "close":
            if not stack:
                raise ValueError(f"unbalanced {token.text!r} at offset {token.start}")
            opened = stack.pop()
            if "([{".index(tokens[opened].text) != ")]}".index(token.text):
                raise ValueError(f"mismatched {tokens[opened].text!r} and {token.text!r} at offset {token.start}")
            pairs[opened] = position
    if stack:
        raise ValueError(f"unclosed {tokens[stack[-1]].text!r} at offset {tokens[stack[-1]].start}")
    return pairs


@dataclass(frozen=True)
class Item:
    """One statement in a token range: `[first, last]` token indices, inclusive."""

    first: int
    last: int


def split_items(
    tokens: list[Token], pairs: dict[int, int], begin: int, end: int, *, braces_end: bool = True,
) -> list[Item]:
    """Split tokens `[begin, end)` into items at depth 0.

    An item ends at a `;`, or, with `braces_end` (Rust items), at a `}`
    closing a brace group opened at depth 0 (followed by an optional `;`).
    Attribute groups (`#[...]`, `#![...]`) never end an item; an inner
    attribute is an item of its own. Statements of a `k::rules!` block
    (`name: { .. } => { .. } where ..;`) end only at `;`.
    """

    items: list[Item] = []
    position = begin
    first = begin
    while position < end:
        token = tokens[position]
        if token.kind == "punct" and token.text == "#":
            bang = position + 1 < end and tokens[position + 1].text == "!"
            bracket = position + (2 if bang else 1)
            if bracket < end and tokens[bracket].text == "[":
                position = pairs[bracket] + 1
                if bang:
                    items.append(Item(first, position - 1))
                    first = position
                continue
        if token.kind == "open":
            closing = pairs[position]
            if token.text == "{" and braces_end:
                last = closing
                if last + 1 < end and tokens[last + 1].text == ";":
                    last += 1
                items.append(Item(first, last))
                position = first = last + 1
                continue
            position = closing + 1
            continue
        if token.kind == "punct" and token.text == ";":
            items.append(Item(first, position))
            first = position = position + 1
            continue
        position += 1
    if first < end:
        items.append(Item(first, end - 1))
    return items


def _attribute_paths(tokens: list[Token], pairs: dict[int, int], item: Item) -> tuple[list[str], int]:
    """The outer attribute paths of `item` (like `k::equation`) and the first token after them."""

    paths = []
    position = item.first
    while position <= item.last and tokens[position].text == "#" and tokens[position + 1].text == "[":
        closing = pairs[position + 1]
        path = []
        cursor = position + 2
        while cursor < closing and (tokens[cursor].kind == "ident" or tokens[cursor].text == ":"):
            path.append(tokens[cursor].text)
            cursor += 1
        paths.append("".join(path))
        position = closing + 1
    return paths, position


def keep(index: int, numerator: int, denominator: int) -> bool:
    """Whether item `index` is kept at fraction `numerator / denominator` (nested, evenly spread)."""

    return (index + 1) * numerator // denominator > index * numerator // denominator


@dataclass
class Truncation:
    source: str
    rules_total: int
    rules_kept: int
    equations_total: int
    equations_kept: int
    rule_blocks_dropped: int


def truncate(source: str, numerator: int, denominator: int) -> Truncation:
    """Keep `numerator / denominator` of the rules and equations of a port source."""

    if not 0 < numerator <= denominator:
        raise ValueError(f"fraction {numerator}/{denominator} is not in (0, 1]")
    tokens = tokenize(source)
    pairs = matching(tokens)
    removals: list[tuple[int, int]] = []
    """Byte ranges `[start, end)` to delete, in source order."""
    rules_total = rules_kept = equations_total = equations_kept = dropped_blocks = 0

    def span(items: list[Item], position: int, floor: int) -> tuple[int, int]:
        """An item's byte range, from the end of the previous item (or `floor`) through its last token."""

        start = tokens[items[position - 1].last].end if position else floor
        return start, tokens[items[position].last].end

    top = split_items(tokens, pairs, 0, len(tokens))
    for position, item in enumerate(top):
        paths, head = _attribute_paths(tokens, pairs, item)
        if "k::equation" in paths:
            if keep(equations_total, numerator, denominator):
                equations_kept += 1
            else:
                removals.append(span(top, position, 0))
            equations_total += 1
            continue
        texts = [token.text for token in tokens[head:head + 4]]
        if texts[:4] != ["k", ":", ":", "rules"] or tokens[head + 4].text != "!":
            continue
        brace = head + 5
        if tokens[brace].text != "{":
            raise ValueError(f"k::rules! at offset {tokens[head].start} is not brace-delimited")
        inner = split_items(tokens, pairs, brace + 1, pairs[brace], braces_end=False)
        block_removals = []
        block_kept = 0
        for inner_position, statement in enumerate(inner):
            _, statement_head = _attribute_paths(tokens, pairs, statement)
            if tokens[statement_head].text in ("for", "use"):
                continue
            if keep(rules_total, numerator, denominator):
                rules_kept += 1
                block_kept += 1
            else:
                block_removals.append(span(inner, inner_position, tokens[brace].end))
            rules_total += 1
        if block_kept == 0:
            dropped_blocks += 1
            removals.append(span(top, position, 0))
        else:
            removals.extend(block_removals)

    pieces = []
    cursor = 0
    for start, end in removals:
        pieces.append(source[cursor:start])
        cursor = end
    pieces.append(source[cursor:])
    return Truncation("".join(pieces), rules_total, rules_kept, equations_total, equations_kept, dropped_blocks)
