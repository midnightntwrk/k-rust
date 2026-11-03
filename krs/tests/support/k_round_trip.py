"""The expansion round trip: a package's printed source must emit the K its authored source emits.

`krs expand` writes each readable form as its long form. The printed package means what the
authored one means only if, overlaid on a copy of the package, it checks and emits the same K.
That is the invariant a feature gate's `expand` step judges (`FixtureGate.expand`), and a port
gate's artifact layer for the crate it compiles from the expansion (`semantics.artifact_gate`).

The two emissions are compared sentence by sentence, after one normalization, defined here
and nowhere else. Each rule maps two K texts that mean the same thing to one text:

1. Variables are renamed by their first occurrence in each sentence (`V0`, `V1`, ..). A
   sentence's variables are bound in it, so a bijective renaming is the same sentence.
2. In a computation cell, a rewrite with a named continuation, `<c> A ~> T:K => B ~> T:K </c>`,
   where `T` occurs nowhere else in the sentence, is read as `<c> A => B ... </c>`. A
   computation cell is one whose content is a K sequence, as the configuration declares it:
   with K content (`<instrs> $PGM:K </instrs>`, `<todo> .K </todo>`), or as the main cell,
   whose content is the computation whatever its initializer's sort (`<instrs maincell="">`,
   and `<k>`, the main cell K's configurations have when none is marked:
   `<k> $PGM:Stmt </k>`). A definition that declares no configuration has K's default one,
   whose computation cell is `<k>`. The printed
   long form names the continuation the readable clause leaves anonymous; both rewrite the
   sequence's head and carry the same rest unchanged, which is what K's `...` at the end of a
   cell whose content is a K sequence means. A cell of another sort (a Map, a List) holds no
   `~>` rest, and rule 2 does not read it.
3. A variable that occurs once in its sentence, directly before a closing cell tag, in a cell
   whose content holds no rewrite, is read as `...` (with the `~>` before it, for a `K` rest).
   Such a variable is matched and never used, which is what K's anonymous `...` rest is. A
   rewrite in the cell is excluded, since `A => B R:Map` writes `R` on the right-hand side.
4. The comment the emitter writes before a raw K sentence, `// raw_k! FILE:LINE:COLUMN (opaque
   to KRS)`, is read without its line and column. K ignores a comment, and the printed file
   holds the same `raw_k!` text at another line.

Everything else must be equal, and a sentence one side has and the other has not is a
difference, at any position.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Iterable

_SENTENCE = re.compile(
    r"\n(?=\s*(?:rule|syntax|claim|context|configuration|module|endmodule|imports|requires)\b)"
)
_VARIABLE = re.compile(r"\b([A-Z][A-Za-z0-9_']*):(?=[A-Za-z#])")
_REST_SORTS = ("K", "Map", "Set", "List", "Bag")
_RAW_K_COMMENT = re.compile(r"(// raw_k! \S+?):\d+:\d+( \(opaque to KRS\))")
_LEAF_CELL = re.compile(r"<([A-Za-z][A-Za-z0-9-]*)((?:\s[^<>]*)?)>([^<>]*)</\1>")
_K_CONTENT = re.compile(r"\s*(?:\$[A-Za-z][A-Za-z0-9_]*:K|\.K)\s*")
_MAIN_CELL = re.compile(r"\smaincell=")
DEFAULT_COMPUTATION_CELLS = frozenset({"k"})
"""The computation cell of K's default configuration, `<k> $PGM:K </k>`, for a definition that
declares none."""


def sentences(text: str) -> list[str]:
    """The sentences of an emitted K text, each with its whitespace collapsed."""

    text = _RAW_K_COMMENT.sub(r"\1\2", text)
    return [" ".join(block.split()) for block in _SENTENCE.split(text) if block.split()]


def computation_cells(texts: Iterable[str]) -> frozenset[str]:
    """The leaf cells the configuration declarations in `texts` give K content or make the main
    cell (rule 2), or K's default configuration's when none is declared."""

    declarations = [
        sentence for text in texts for sentence in sentences(text) if sentence.startswith("configuration")
    ]
    if not declarations:
        return DEFAULT_COMPUTATION_CELLS
    return frozenset(
        cell
        for sentence in declarations
        for cell, attributes, content in _LEAF_CELL.findall(sentence)
        if _K_CONTENT.fullmatch(content) or _MAIN_CELL.search(attributes) or cell == "k"
    )


def _occurrences(words: list[str], name: str) -> int:
    return sum(1 for word in re.findall(r"[A-Za-z0-9_']+", " ".join(words)) if word == name)


def _continuation(words: list[str], cells: frozenset[str]) -> list[str]:
    """Rule 2, in the computation cells `cells`."""

    tails = [
        at for at in range(len(words) - 2)
        if words[at] == "~>" and words[at + 1].endswith(":K")
    ]
    if len(tails) != 2:
        return words
    left, right = tails
    tail = words[left + 1]
    closing = words[right + 2]
    cell = closing[2:-1] if closing.startswith("</") and closing.endswith(">") else None
    if words[right + 1] != tail or words[left + 2] != "=>" or cell not in cells:
        return words
    # Both tails are in that cell: the last tag opened before the first is the cell's own.
    opened = [word for word in words[:left] if re.fullmatch(r"<[A-Za-z][A-Za-z0-9-]*>", word)]
    if not opened or opened[-1] != f"<{cell}>":
        return words
    if _occurrences(words, tail.split(":")[0]) != 2:
        return words
    return words[:left] + words[left + 2:right] + ["...", closing] + words[right + 3:]


def _rests(words: list[str]) -> list[str]:
    """Rule 3."""

    at = 0
    while at < len(words) - 1:
        word, closing = words[at], words[at + 1]
        name, _, sort = word.partition(":")
        cell = closing[2:-1] if closing.startswith("</") and closing.endswith(">") else None
        if (
            cell is None or sort not in _REST_SORTS or not re.fullmatch(r"[A-Z][A-Za-z0-9_']*", name)
            or _occurrences(words, name) != 1
        ):
            at += 1
            continue
        opening = max((i for i in range(at) if words[i] == f"<{cell}>"), default=None)
        if opening is None or "=>" in words[opening + 1:at]:
            at += 1
            continue
        start = at - 1 if sort == "K" and at > opening + 1 and words[at - 1] == "~>" else at
        words = words[:start] + ["..."] + words[at + 1:]
        at = start + 1
    return words


def normalized(sentence: str, cells: frozenset[str] = DEFAULT_COMPUTATION_CELLS) -> str:
    """`sentence` under rules 1-3, with `cells` its definition's computation cells."""

    words = _rests(_continuation(sentence.split(), cells))
    names: dict[str, str] = {}

    def rename(match: re.Match[str]) -> str:
        names.setdefault(match.group(1), f"V{len(names)}")
        return names[match.group(1)] + ":"

    return _VARIABLE.sub(rename, " ".join(words))


def differences(authored: Path, printed: Path) -> list[str]:
    """Each difference between the `.k` artifacts of two emission directories, normalized."""

    found: list[str] = []
    cells = computation_cells(path.read_text(encoding="utf-8") for path in sorted(authored.glob("*.k")))
    names = sorted({path.name for directory in (authored, printed) for path in directory.glob("*.k")})
    for name in names:
        left, right = authored / name, printed / name
        if not left.is_file() or not right.is_file():
            found.append(f"{name}: emitted by one side only")
            continue
        a = [normalized(sentence, cells) for sentence in sentences(left.read_text(encoding="utf-8"))]
        b = [normalized(sentence, cells) for sentence in sentences(right.read_text(encoding="utf-8"))]
        if len(a) != len(b):
            found.append(f"{name}: {len(a)} authored sentences, {len(b)} printed")
        for index, (x, y) in enumerate(zip(a, b)):
            if x != y:
                found.append(f"{name} sentence {index}:\n  authored: {x}\n  printed:  {y}")
    return found
