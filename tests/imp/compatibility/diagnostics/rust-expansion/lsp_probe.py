#!/usr/bin/env python3
"""Bounded rust-analyzer exact-range probe for the malformed IMP attribute."""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from support import GateError  # noqa: E402
from support.lsp import Session, token_range, version  # noqa: E402
from support.tools import checkout_scratch  # noqa: E402


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "src/lib.rs"
TEXT = SOURCE.read_text(encoding="utf-8")
TOKEN = "syntax"


def main() -> None:
    analyzer = version()
    target = Path(os.environ.get("KRS_IMP_PROBE_TARGET_ROOT", checkout_scratch())) / "rust-analyzer"
    capabilities = {
        "workspace": {"configuration": True},
        "window": {"workDoneProgress": True},
        "textDocument": {"diagnostic": {}},
    }
    with Session(
        ROOT, {SOURCE: TEXT}, capabilities=capabilities,
        environment={"CARGO_TARGET_DIR": os.fspath(target)},
    ) as session:
        diagnostics = session.diagnostics(SOURCE, timeout=90)
        matching = [
            diagnostic for diagnostic in diagnostics
            if "missing required argument `sort = ...`" in diagnostic.get("message", "")
        ]
        expected = token_range(TEXT, TOKEN, after="#[k::constructor")
        if len(matching) != 1 or matching[0].get("range") != expected:
            raise GateError(f"expected one exact authored `{TOKEN}` range {expected}, got {matching!r}")
        print(json.dumps({"rust_analyzer": analyzer, "range": expected, "token": TOKEN}, sort_keys=True))


if __name__ == "__main__":
    main()
