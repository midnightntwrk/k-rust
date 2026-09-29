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
"""The exact file set one `krs emit-k` run writes for a definition without claims."""

EMITTED_ARTIFACTS_WITH_SPEC = tuple(sorted((*EMITTED_ARTIFACTS, "spec.k")))
"""The exact file set one `krs emit-k` run writes when the definition has claims."""

_CLAIM_HEADER = re.compile(r"^  claim \[([^]]+)\]", re.MULTILINE)


def emitted_claims(directory: Path, module: str, expected: int) -> tuple[list[str], str]:
    """Read the claims `krs emit-k` wrote to `spec.k` beside `definition.k`.

    Checks the exact specification frame for main module `module` and returns
    the claim labels in order and the claim sentences between the frame's
    header and terminator. Exactly `expected` claims with distinct labels must
    be present.
    """

    path = directory / "spec.k"
    if not path.is_file():
        raise GateError(f"emit-k wrote no spec.k in {directory}")
    source = path.read_text(encoding="utf-8")
    header = f'requires "definition.k"\n\nmodule {module}-SPEC\n  imports {module}\n\n'
    footer = "endmodule\n"
    if not source.startswith(header) or not source.endswith(footer):
        raise GateError(f"spec.k does not have the exact {module}-SPEC frame")
    claims = source[len(header) : -len(footer)]
    labels = _CLAIM_HEADER.findall(claims)
    if len(labels) != expected or len(set(labels)) != expected:
        raise GateError(f"expected {expected} emitted claims with distinct labels, found {labels!r}")
    if not claims.startswith("  claim [") or "\nendmodule" in claims:
        raise GateError("spec.k holds more than its claim sentences")
    return labels, claims


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
