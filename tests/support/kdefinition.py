"""Helpers over the K definitions `krs emit-k` writes and the KORE K compiles."""

from __future__ import annotations

from dataclasses import dataclass, field
import os
from pathlib import Path
import re

from support import GateError
from support.hashing import sha256_bytes


EMITTED_ARTIFACTS = (
    ".krs-artifacts",
    "definition-ir.json",
    "definition.k",
    "descriptor-bundle.json",
    "semantic-ir.json",
    "sources.json",
    "symbols.json",
)
"""The exact file set one `krs emit-k` run writes."""

_SENTENCE_START = re.compile(
    r"^(?:endmodule\b|  (?:syntax\b|configuration\b|context alias\b|rule\b|claim \[))"
)
_CLAIM_HEADER = re.compile(r"^  claim \[([^]]+)\]")


def split_claims(source: str, expected: int) -> tuple[str, list[str], str]:
    """Split the top-level claims out of one emitted module.

    Returns the claim-free module with every other byte preserved, the claim
    labels in order, and the claim sentences. Exactly `expected` claims with
    distinct labels must be present.
    """

    lines = source.splitlines(keepends=True)
    kept: list[str] = []
    labels: list[str] = []
    claims: list[str] = []
    index = 0
    while index < len(lines):
        header = _CLAIM_HEADER.match(lines[index])
        if header is None:
            kept.append(lines[index])
            index += 1
            continue
        labels.append(header.group(1))
        start = index
        index += 1
        while index < len(lines) and _SENTENCE_START.match(lines[index]) is None:
            index += 1
        claims.extend(lines[start:index])
    if len(labels) != expected or len(set(labels)) != expected:
        raise GateError(f"expected {expected} emitted claims with distinct labels, found {labels!r}")
    value = "".join(kept)
    if "  claim [" in value:
        raise GateError("claim stripping left a top-level claim sentence")
    if not value.endswith("endmodule\n"):
        raise GateError("claim-free emitted definition lost its exact module terminator")
    return value, labels, "".join(claims)


_GENERATED_BINDER = re.compile(
    rb"(?P<prefix>\\exists\{R\} \()"
    rb"(?P<variable>Var'Unds'Gen[0-9]+)"
    rb"(?P<sort>:Sort[A-Za-z0-9']+\{\})"
    rb"(?P<body>,.*?)"
    rb"(?P=variable)(?P=sort)"
    rb"(?P<suffix>.*?\\bottom\{R\}\(\))",
    re.DOTALL,
)


_K_INCLUDE = re.compile(rb"Source\(/[^()\"]*?/include/kframework/")


def normalized_kore_sha256(path: Path, semantics: Path) -> str:
    """Digest a kompiled `definition.kore` independent of where things live.

    The recorded semantics source path becomes `semantics.k`; the recorded
    location of K's own builtin sources (the K installation prefix, which
    differs between two builds of the same K release) becomes `k`; and each
    generated sort-binder variable becomes one stable alpha name.
    """

    if not path.is_file():
        raise GateError(f"required file is missing: {path}")
    contents = path.read_bytes()
    temporary_source = os.fsencode(semantics.absolute())
    if temporary_source not in contents:
        raise GateError("definition.kore does not record its semantics source")
    normalized = contents.replace(temporary_source, b"semantics.k")
    normalized, include_count = _K_INCLUDE.subn(b"Source(k/include/kframework/", normalized)
    if include_count == 0:
        raise GateError("definition.kore does not record K's builtin sources")

    def alpha(match: re.Match[bytes]) -> bytes:
        variable = match.group("variable") + match.group("sort")
        if match.group(0).count(variable) != 2:
            raise GateError("definition.kore changed a generated binder shape")
        return match.group(0).replace(variable, b"Var'Unds'KrsAlpha" + match.group("sort"))

    normalized, binder_count = _GENERATED_BINDER.subn(alpha, normalized)
    if binder_count == 0:
        raise GateError("definition.kore has no generated sort binders")
    return sha256_bytes(normalized)


_KORE_TOKEN = re.compile(
    r"""(?:\s|/\*.*?\*/)*(?:(?P<string>"(?:[^"\\]|\\.)*")|(?P<ident>\\?[A-Za-z][A-Za-z0-9'-]*)|(?P<punct>[{}(),]))""",
    re.DOTALL,
)
_KORE_ESCAPES = {'"': '"', "\\": "\\", "n": "\n", "t": "\t", "r": "\r", "f": "\f"}


@dataclass
class _KoreFrame:
    kind: str
    name: str
    phase: str = "sort_item_or_close"
    sorts: list[dict[str, object]] = field(default_factory=list)
    args: list[dict[str, object]] = field(default_factory=list)


def _kore_string(literal: str) -> str:
    body = literal[1:-1]
    value: list[str] = []
    index = 0
    while index < len(body):
        character = body[index]
        if character != "\\":
            value.append(character)
            index += 1
            continue
        escape = body[index + 1 : index + 2]
        widths = {"x": 2, "u": 4, "U": 8}
        if escape in _KORE_ESCAPES:
            value.append(_KORE_ESCAPES[escape])
            index += 2
        elif escape in widths:
            digits = body[index + 2 : index + 2 + widths[escape]]
            if len(digits) != widths[escape]:
                raise GateError(f"truncated KORE string escape in {literal}")
            value.append(chr(int(digits, 16)))
            index += 2 + widths[escape]
        else:
            raise GateError(f"unsupported KORE string escape \\{escape} in {literal}")
    return "".join(value)


def parse_kore_pattern(text: str) -> dict[str, object]:
    """Parse one ground textual KORE pattern into the KORE JSON (v1) shape.

    Covers what a concrete final configuration contains: symbol applications
    and `\\dv` domain values, with sort applications; `/* ... */` comments, as
    `krun --output kore` prints before builtin collections and injections, are
    skipped. Any other connective or a variable is rejected, since a concrete
    result never contains one.
    """

    tokens: list[tuple[str, str]] = []
    position = 0
    text = text.rstrip()
    while position < len(text):
        match = _KORE_TOKEN.match(text, position)
        if match is None or match.end() == position:
            raise GateError(f"unexpected KORE text at offset {position}: {text[position:position + 40]!r}")
        kind = match.lastgroup
        assert kind is not None
        tokens.append((kind, match.group(kind)))
        position = match.end()
    cursor = 0

    def take(kind: str, value: str | None = None) -> str:
        nonlocal cursor
        if cursor >= len(tokens) or tokens[cursor][0] != kind or (value is not None and tokens[cursor][1] != value):
            found = tokens[cursor][1] if cursor < len(tokens) else "end of input"
            raise GateError(f"expected KORE {value or kind}, found {found!r}")
        cursor += 1
        return tokens[cursor - 1][1]

    def peek(value: str) -> bool:
        return cursor < len(tokens) and tokens[cursor] == ("punct", value)

    frames: list[_KoreFrame] = []
    result: dict[str, object] | None = None

    def start(kind: str) -> None:
        name = take("ident")
        take("punct", "{")
        frames.append(_KoreFrame(kind, name))

    def finish(node: dict[str, object]) -> None:
        nonlocal result
        frames.pop()
        if not frames:
            result = node
            return
        parent = frames[-1]
        if parent.phase == "sort_child":
            parent.sorts.append(node)
            parent.phase = "sort_separator_or_close"
        elif parent.phase == "arg_child":
            parent.args.append(node)
            parent.phase = "arg_separator_or_close"
        else:
            raise GateError("malformed KORE parser state")

    start("pattern")
    while frames:
        frame = frames[-1]
        if frame.phase in {"sort_item_or_close", "sort_item_required"}:
            if frame.phase == "sort_item_or_close" and peek("}"):
                take("punct", "}")
                if frame.kind == "sort":
                    finish({"tag": "SortApp", "name": frame.name, "args": frame.sorts})
                    continue
                take("punct", "(")
                if frame.name == "\\dv":
                    if len(frame.sorts) != 1:
                        raise GateError("a KORE domain value takes exactly one sort")
                    value = _kore_string(take("string"))
                    take("punct", ")")
                    finish({"tag": "DV", "sort": frame.sorts[0], "value": value})
                    continue
                if frame.name.startswith("\\"):
                    raise GateError(f"unsupported KORE connective {frame.name} in a concrete pattern")
                frame.phase = "arg_item_or_close"
            else:
                frame.phase = "sort_child"
                start("sort")
        elif frame.phase == "sort_separator_or_close":
            if peek(","):
                take("punct", ",")
                frame.phase = "sort_item_required"
            else:
                frame.phase = "sort_item_or_close"
                if not peek("}"):
                    take("punct", "}")
        elif frame.phase in {"arg_item_or_close", "arg_item_required"}:
            if frame.phase == "arg_item_or_close" and peek(")"):
                take("punct", ")")
                finish({"tag": "App", "name": frame.name, "sorts": frame.sorts, "args": frame.args})
            else:
                frame.phase = "arg_child"
                start("pattern")
        elif frame.phase == "arg_separator_or_close":
            if peek(","):
                take("punct", ",")
                frame.phase = "arg_item_required"
            else:
                frame.phase = "arg_item_or_close"
                if not peek(")"):
                    take("punct", ")")
        else:
            raise GateError("malformed KORE parser state")

    assert result is not None
    if cursor != len(tokens):
        raise GateError(f"trailing KORE text after the pattern: {tokens[cursor][1]!r}")
    return result
