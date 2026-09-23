"""Helpers over the K definitions `krs emit-k` writes and the KORE K compiles."""

from __future__ import annotations

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


def normalized_kore_sha256(path: Path, semantics: Path) -> str:
    """Digest a kompiled `definition.kore` independent of its build location.

    The recorded semantics source path becomes `semantics.k`, and each
    generated sort-binder variable becomes one stable alpha name.
    """

    if not path.is_file():
        raise GateError(f"required file is missing: {path}")
    contents = path.read_bytes()
    temporary_source = os.fsencode(semantics.absolute())
    if temporary_source not in contents:
        raise GateError("definition.kore does not record its semantics source")
    normalized = contents.replace(temporary_source, b"semantics.k")

    def alpha(match: re.Match[bytes]) -> bytes:
        variable = match.group("variable") + match.group("sort")
        if match.group(0).count(variable) != 2:
            raise GateError("definition.kore changed a generated binder shape")
        return match.group(0).replace(variable, b"Var'Unds'KrsAlpha" + match.group("sort"))

    normalized, binder_count = _GENERATED_BINDER.subn(alpha, normalized)
    if binder_count == 0:
        raise GateError("definition.kore has no generated sort binders")
    return sha256_bytes(normalized)
