"""Helpers over the K definitions `krs emit-k` writes and the KORE K compiles."""

from __future__ import annotations

from pathlib import Path
import re

from support import GateError


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
