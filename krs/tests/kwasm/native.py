#!/usr/bin/env python3
"""Surface configuration and outcome reporting for the KWasm qualification corpus."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError, behavior  # noqa: E402
from support.hashing import canonical_json, json_sha256  # noqa: E402
from support.pins import load_toml  # noqa: E402


def configuration_variables(case: Mapping[str, Any]) -> dict[str, str]:
    """Return surface configuration text for native and Java execution."""

    return {"PGM": str(case["program"]), "STACK": ".ValStack"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("krs_gate", type=Path)
    parser.add_argument("definition", type=Path)
    parser.add_argument("module")
    parser.add_argument("--definition-kore-sha256", required=True)
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--outcomes", type=Path)
    arguments = parser.parse_args()
    corpus = load_toml(arguments.corpus)
    cases = corpus.get("behavior")
    if not isinstance(cases, list) or not cases:
        raise GateError("behavior corpus is empty")
    outcomes = behavior.native_corpus(
        arguments.krs_gate, arguments.definition, arguments.module, cases, configuration_variables, corpus,
        definition_kore_sha256=arguments.definition_kore_sha256,
    )
    digest = json_sha256(outcomes)
    if arguments.outcomes is not None:
        arguments.outcomes.write_text(canonical_json(outcomes) + "\n", encoding="utf-8")
    print(f"PASS native KWasm behavior: {len(outcomes)} executions; sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
