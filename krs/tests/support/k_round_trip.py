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
4. Any other variable that occurs once in its sentence is read as K's anonymous variable of its
   sort: `X:Int` is `_:Int`. A variable that occurs once is matched and never used: no other
   occurrence equates it with another part of the term, and no right-hand side or condition
   reads it, so it constrains the match by its sort alone, which is what `_:Int` does; a claim's
   left-hand variable is quantified over its sort as `_` is. The emitted K holds no other
   once-used variable: an existential `?X`, a fresh `!X` and a configuration variable `$X` are
   none and are kept, as are a context's `HOLE` and an alias's `HERE`, which name the hole; a
   variable only on a rule's right-hand side is refused before K is emitted, a claim writes
   its unknowns `?X`, and a desugar clause lists its right-hand variable again in
   `unboundVariables(X)`, so it occurs twice. Occurrences are counted outside sort positions
   (after `:` or `:>`), so a variable named as its sort counts once per use. The printed long form names some matched-once items the readable clause
   leaves anonymous (a `for Sort` head `_` is the binder `_stmt`, emitted `_Stmt:Stmt`).
5. The comments the emitter writes to name the Rust source rather than the K are left out: the
   artifact's header (its unindented comment lines) and the `// KRS PACKAGE/FILE: ITEM` line
   above a sentence. K ignores a comment, and the printed source names some sentences by
   another item: `krs expand` prints a shorthand branch as the equation fn it stands for.

Everything else must be equal, and a sentence one side has and the other has not is a
difference, at any position.

The symbol table, `symbols.json`, is compared too: it names each module, symbol, label and
context alias the K writes by its identity, and the identity is what a source map, a proof
and a later emission refer to. A printed rule that emitted the same K under another identity
would be another rule to everything that reads the table (IMP's `while`, S5.6). Its entries
carry no variables, so they are compared exactly, as a set keyed by identity: an entry one
side has and the other has not is a difference, and so is one whose emitted name, kind or
source-map key differs.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Iterable

_SENTENCE = re.compile(
    r"\n(?=\s*(?:rule|syntax|claim|context|configuration|module|endmodule|imports|requires)\b)"
)
_VARIABLE = re.compile(r"\b([A-Z][A-Za-z0-9_']*):(?=[A-Za-z#])")
_REST_SORTS = ("K", "Map", "Set", "List", "Bag")
_ANY_VARIABLE = re.compile(r"(?<![\w?!$'])([A-Z_][A-Za-z0-9_']*):(?=[A-Za-z#])")
"""A variable as rule 4 reads it, its name capitalized or starting with `_`, not after `?`, `!`
or `$`."""
_RESERVED_VARIABLES = frozenset({"HOLE", "HERE"})
_HEADER = re.compile(r"\A(?://[^\n]*\n)+\n?")
"""The header of an emitted K artifact: the comment lines that open it and the blank line after
them."""
_SOURCE_LINE = re.compile(r"^[ \t]*// KRS [^\n]*\n", re.MULTILINE)
_LEAF_CELL = re.compile(r"<([A-Za-z][A-Za-z0-9-]*)((?:\s[^<>]*)?)>([^<>]*)</\1>")
_K_CONTENT = re.compile(r"\s*(?:\$[A-Za-z][A-Za-z0-9_]*:K|\.K)\s*")
_MAIN_CELL = re.compile(r"\smaincell=")
DEFAULT_COMPUTATION_CELLS = frozenset({"k"})
"""The computation cell of K's default configuration, `<k> $PGM:K </k>`, for a definition that
declares none."""


def sentences(text: str) -> list[str]:
    """The sentences of an emitted K text, each with its whitespace collapsed."""

    text = _SOURCE_LINE.sub("", _HEADER.sub("", text, count=1))
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


def _variable_occurrences(text: str, name: str) -> int:
    """The occurrences of the variable `name` in `text`: the words spelling it outside a sort
    position (after `:` or `:>`), where a sort of the same name is written, so that the count does
    not change when the variables are renamed."""

    return len(re.findall(rf"(?<![\w'])(?<!:)(?<!:>){re.escape(name)}(?![\w'])", text))


def _once_used(words: list[str]) -> str:
    """Rule 4."""

    text = " ".join(words)
    once = {
        name
        for name in _ANY_VARIABLE.findall(text)
        if name != "_" and name not in _RESERVED_VARIABLES and _variable_occurrences(text, name) == 1
    }
    return _ANY_VARIABLE.sub(lambda match: "_:" if match.group(1) in once else match.group(0), text)


def normalized(sentence: str, cells: frozenset[str] = DEFAULT_COMPUTATION_CELLS) -> str:
    """`sentence` under rules 1-4, with `cells` its definition's computation cells."""

    text = _once_used(_rests(_continuation(sentence.split(), cells)))
    names: dict[str, str] = {}

    def rename(match: re.Match[str]) -> str:
        names.setdefault(match.group(1), f"V{len(names)}")
        return names[match.group(1)] + ":"

    return _VARIABLE.sub(rename, text)


def differences(authored: Path, printed: Path) -> list[str]:
    """Each difference between the `.k` artifacts of two emission directories, normalized, and
    between their symbol tables."""

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
    return found + symbol_differences(authored, printed)


SYMBOLS = "symbols.json"
"""The symbol table an emission writes beside its `.k` artifacts."""


def _identity(entry: dict) -> str:
    return json.dumps(entry.get("identity"), sort_keys=True)


def symbol_differences(authored: Path, printed: Path) -> list[str]:
    """Each difference between the symbol tables of two emission directories."""

    left, right = authored / SYMBOLS, printed / SYMBOLS
    if not left.is_file() and not right.is_file():
        return []
    if not left.is_file() or not right.is_file():
        return [f"{SYMBOLS}: emitted by one side only"]
    tables = [json.loads(path.read_text(encoding="utf-8")) for path in (left, right)]
    found: list[str] = []
    versions = [table.get("schema_version") for table in tables]
    if versions[0] != versions[1]:
        found.append(f"{SYMBOLS}: schema version {versions[0]} authored, {versions[1]} printed")
    entries: list[dict[str, dict]] = []
    for side, table in zip(("authored", "printed"), tables):
        keyed: dict[str, dict] = {}
        for entry in table.get("entries", []):
            identity = _identity(entry)
            if identity in keyed:
                found.append(f"{SYMBOLS}: {side} names {identity} twice")
            keyed[identity] = entry
        entries.append(keyed)
    a, b = entries
    for identity in sorted(a.keys() | b.keys()):
        if identity not in b:
            found.append(f"{SYMBOLS}: {identity} ({a[identity].get('emitted_name')}) authored only")
        elif identity not in a:
            found.append(f"{SYMBOLS}: {identity} ({b[identity].get('emitted_name')}) printed only")
        elif a[identity] != b[identity]:
            found.append(
                f"{SYMBOLS}: {identity}:\n  authored: {json.dumps(a[identity], sort_keys=True)}"
                f"\n  printed:  {json.dumps(b[identity], sort_keys=True)}"
            )
    return found
