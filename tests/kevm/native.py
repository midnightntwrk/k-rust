#!/usr/bin/env python3
"""Surface configuration and outcome reporting for the KEVM qualification corpus."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import sys
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError, behavior  # noqa: E402
from support.hashing import canonical_json, json_sha256  # noqa: E402
from support.pins import load_toml  # noqa: E402


def configuration_variables(case: Mapping[str, Any]) -> dict[str, str]:
    """Return the surface configuration text shared with the Java route."""

    address = str(case.get("address", "0"))
    storage = str(case.get("storage", ".Map"))
    return {
        "PGM": "run",
        "PROGRAM": str(case["program"]),
        "JUMPDESTS": str(case.get("jump_dests", 'b""')),
        "ADDRESS": address,
        "ACCOUNTID": str(case.get("account_id", address)),
        "BALANCE": str(case.get("balance", "0")),
        "CODE": str(case.get("code", 'b""')),
        "NONCE": str(case.get("nonce", "0")),
        "ORIGIN": str(case.get("origin", "0")),
        "CALLER": str(case.get("caller", "0")),
        "CALLVALUE": str(case.get("call_value", "0")),
        "CALLDATA": str(case.get("call_data", 'b""')),
        "GASPRICE": str(case.get("gas_price", "0")),
        "RETURNDATA": str(case.get("return_data", 'b""')),
        "LOCALMEM": str(case.get("local_mem", 'b""')),
        "MEMORYUSED": str(case.get("memory_used", "0")),
        "CALLGAS": str(case.get("call_gas", "0")),
        "CALLDEPTH": str(case.get("call_depth", "0")),
        "CODEADDRESS": str(case.get("code_address", address)),
        "CALLSTACK": str(case.get("call_stack", ".List")),
        "INTERIMSTATES": str(case.get("interim_states", ".List")),
        "TOUCHEDACCOUNTS": str(case.get("touched_accounts", ".Set")),
        "STORAGE": storage,
        "ORIGSTORAGE": str(case.get("original_storage", storage)),
        "ACCESSEDSTORAGE": str(case.get("accessed_storage", ".Map")),
        "ACCESSEDACCOUNTS": str(case.get("accessed_accounts", ".Set")),
        "LOGS": str(case.get("logs", ".List")),
        "REFUND": str(case.get("refund", "0")),
        "SELFDESTRUCT": str(case.get("self_destruct", ".Set")),
        "CREATEDACCOUNTS": str(case.get("created_accounts", ".Set")),
        "STATIC": str(case.get("static", "false")),
        "BLOCKHASHES": str(case.get("block_hashes", ".List")),
        "COINBASE": str(case.get("coinbase", "0")),
        "TIMESTAMP": str(case.get("timestamp", "0")),
        "NUMBER": str(case.get("number", "0")),
        "PREVRANDAO": str(case.get("prev_randao", "0")),
        "GASLIMIT": str(case.get("gas_limit", "0")),
        "CHAINID": str(case.get("chain_id", "0")),
        "BASEFEE": str(case.get("base_fee", "0")),
        "STACK": str(case["stack"]),
        "PC": str(case["pc"]),
        "GAS": str(case["gas"]),
        "STATUS": ".StatusCode",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--jobs",
        type=int,
        default=int(os.environ.get("KRS_KEVM_JOBS", "1")),
        help="persistent K-Rust worker processes (default: %(default)s)",
    )
    parser.add_argument(
        "--case",
        action="append",
        default=[],
        dest="case_ids",
        help="execute only the named corpus case; may be repeated",
    )
    parser.add_argument("krs_gate", type=Path)
    parser.add_argument("definition", type=Path)
    parser.add_argument("module")
    parser.add_argument("--definition-kore-sha256", required=True)
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--outcomes", type=Path, help="write ordered behavior outcomes as JSON")
    arguments = parser.parse_args()
    corpus = load_toml(arguments.corpus)
    cases = corpus.get("behavior")
    if not isinstance(cases, list) or not cases:
        raise GateError("behavior corpus is empty")
    if arguments.case_ids:
        requested = set(arguments.case_ids)
        known = {str(case.get("id")) for case in cases}
        missing = sorted(requested - known)
        if missing:
            raise GateError(f"unknown behavior cases: {', '.join(missing)}")
        cases = [case for case in cases if case.get("id") in requested]
    outcomes = behavior.native_corpus(
        arguments.krs_gate,
        arguments.definition,
        arguments.module,
        cases,
        configuration_variables,
        corpus,
        definition_kore_sha256=arguments.definition_kore_sha256,
        jobs=arguments.jobs,
    )
    digest = json_sha256(outcomes)
    if arguments.outcomes is not None:
        arguments.outcomes.write_text(canonical_json(outcomes) + "\n", encoding="utf-8")
    print(f"PASS native KEVM behavior: {len(outcomes)} executions; sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
