#!/usr/bin/env python3
"""Require findable KRS terminology and explicit Rust-analogy limits."""

from __future__ import annotations

from pathlib import Path


SITE = Path(__file__).resolve().parent.parent
PAGES = SITE / "src" / "pages"

REQUIRED = {
    "symbolic object-language": "start/what-krs-defines.mdx",
    "KResult": "imp/sorts-and-values.mdx",
    "KSequence": "imp/configuration-and-state.mdx",
    "constructor families": "imp/concrete-grammar.mdx",
    "strict evaluation": "imp/evaluation.mdx",
    "computation cell": "imp/configuration-and-state.mdx",
    "sequence tail": "imp/machine-rules.mdx",
    "object-language Boolean": "semantics/applicability-and-failure.mdx",
    "semantic bottom": "semantics/static-semantics.mdx",
    "reachability claim": "verification/reachability-claims.mdx",
    "stable public symbols": "advanced/composition.mdx",
    "backend-capability": "reference/workflow.mdx",
}


def main() -> None:
    missing: list[str] = []
    for term, relative in REQUIRED.items():
        source = (PAGES / relative).read_text(encoding="utf-8")
        if term.casefold() not in source.casefold():
            missing.append(f"{term!r} on {relative}")
    synthesis = (PAGES / "start" / "five-minute-theory.mdx").read_text(encoding="utf-8")
    for boundary in (
        "Rust analogy—and its limit",
        "do not execute Rust",
        "`foo_to_bar` does not call",
    ):
        if boundary not in synthesis:
            missing.append(f"five-minute Rust boundary {boundary!r}")
    static = (PAGES / "semantics" / "static-semantics.mdx").read_text(encoding="utf-8")
    if "not Rust `Option`" not in static:
        missing.append("partial-function Rust analogy limit")
    if missing:
        raise SystemExit(f"search/terminology audit is incomplete: {missing}")
    print(f"search audit passed: {len(REQUIRED)} canonical terms and 4 Rust limits")


if __name__ == "__main__":
    main()
