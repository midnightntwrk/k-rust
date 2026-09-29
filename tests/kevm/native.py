#!/usr/bin/env python3
"""Persistent K-Rust execution support for the KEVM qualification corpus."""

from __future__ import annotations

import argparse
import ast
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import re
import sys
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError  # noqa: E402
from support import krs_gate  # noqa: E402
from support.hashing import canonical_json, json_sha256  # noqa: E402
from support.pins import load_toml  # noqa: E402


def concrete_mapping(value: Any, name: str) -> Mapping[str, Any]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise GateError(f"{name} is not a string-keyed table: {value}")
    return value


def concrete_logs(values: Any, name: str) -> list[Mapping[str, Any]]:
    if not isinstance(values, list):
        raise GateError(f"{name} is not an array: {values}")
    logs: list[Mapping[str, Any]] = []
    for index, value in enumerate(values):
        entry = concrete_mapping(value, f"{name}[{index}]")
        topics = entry.get("topics", [])
        if not isinstance(topics, list):
            raise GateError(f"{name}[{index}].topics is not an array: {topics}")
        logs.append(entry)
    return logs


def rendered_bytes(value: bytes) -> str:
    return 'b"' + "".join(f"\\x{byte:02x}" for byte in value) + '"'


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


def applications(value: Any, name: str) -> list[Mapping[str, Any]]:
    found: list[Mapping[str, Any]] = []
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            if current.get("tag") == "App" and current.get("name") == name:
                found.append(current)
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)
    return found


def cell(state: Mapping[str, Any], name: str) -> Mapping[str, Any]:
    matches = applications(state, f"Lbl'-LT-'{name}'-GT-'")
    if len(matches) != 1:
        raise GateError(f"native result contains {len(matches)} <{name}> cells")
    arguments = matches[0].get("args")
    if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
        raise GateError(f"native <{name}> cell is malformed")
    return arguments[0]


def domain_value(term: Mapping[str, Any], sort: str) -> str:
    observed_sort = term.get("sort")
    if (
        term.get("tag") != "DV"
        or not isinstance(observed_sort, dict)
        or observed_sort.get("tag") != "SortApp"
        or observed_sort.get("name") != f"Sort{sort}"
        or not isinstance(term.get("value"), str)
    ):
        raise GateError(f"expected concrete {sort} domain value: {term}")
    return str(term["value"])


def unwrap_injection(term: Mapping[str, Any]) -> Mapping[str, Any]:
    while term.get("tag") == "App" and term.get("name") == "inj":
        arguments = term.get("args")
        if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
            raise GateError(f"malformed sort injection: {term}")
        term = arguments[0]
    return term


def map_items(term: Mapping[str, Any]) -> list[tuple[Mapping[str, Any], Mapping[str, Any]]]:
    entries: list[tuple[Mapping[str, Any], Mapping[str, Any]]] = []
    pending = [term]
    while pending:
        current = pending.pop()
        name = current.get("name")
        arguments = current.get("args")
        if current.get("tag") == "App" and name == "Lbl'Stop'Map" and arguments == []:
            continue
        if current.get("tag") == "App" and name == "Lbl'Unds'Map'Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
            pending.extend((arguments[1], arguments[0]))
            continue
        if current.get("tag") == "App" and name == "Lbl'UndsPipe'-'-GT-Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
            entries.append((unwrap_injection(arguments[0]), unwrap_injection(arguments[1])))
            continue
        raise GateError(f"malformed concrete Map: {current}")
    return entries


def set_values(term: Mapping[str, Any]) -> list[str]:
    values: list[str] = []
    pending = [term]
    while pending:
        current = pending.pop()
        name = current.get("name")
        arguments = current.get("args")
        if current.get("tag") == "App" and name == "Lbl'Stop'Set" and arguments == []:
            continue
        if current.get("tag") == "App" and name == "Lbl'Unds'Set'Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
            pending.extend((arguments[1], arguments[0]))
            continue
        if current.get("tag") == "App" and name == "LblSetItem" and isinstance(arguments, list) and len(arguments) == 1 and isinstance(arguments[0], dict):
            values.append(domain_value(unwrap_injection(arguments[0]), "Int"))
            continue
        raise GateError(f"malformed concrete Set: {current}")
    return values


def list_values(term: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    values: list[Mapping[str, Any]] = []
    pending = [term]
    while pending:
        current = pending.pop()
        name = current.get("name")
        arguments = current.get("args")
        if current.get("tag") == "App" and name == "Lbl'Stop'List" and arguments == []:
            continue
        if current.get("tag") == "App" and name == "Lbl'Unds'List'Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
            pending.extend((arguments[1], arguments[0]))
            continue
        if current.get("tag") == "App" and name == "LblListItem" and isinstance(arguments, list) and len(arguments) == 1 and isinstance(arguments[0], dict):
            values.append(unwrap_injection(arguments[0]))
            continue
        raise GateError(f"malformed concrete List: {current}")
    return values


def rendered_int_map(term: Mapping[str, Any]) -> str:
    entries = sorted(
        ((domain_value(key, "Int"), domain_value(value, "Int")) for key, value in map_items(term)),
        key=lambda item: int(item[0]),
    )
    return ".Map" if not entries else ",".join(f"{key}:{value}" for key, value in entries)


def rendered_accessed_storage(term: Mapping[str, Any]) -> str:
    entries = sorted(
        (
            (domain_value(key, "Int"), sorted(set_values(value), key=int))
            for key, value in map_items(term)
        ),
        key=lambda item: int(item[0]),
    )
    return ".Map" if not entries else ",".join(f"{key}:[{','.join(values)}]" for key, values in entries)


def rendered_set(term: Mapping[str, Any]) -> str:
    values = sorted(set_values(term), key=int)
    return ".Set" if not values else ",".join(values)


def rendered_logs(term: Mapping[str, Any]) -> str:
    logs: list[dict[str, Any]] = []
    for entry in list_values(term):
        arguments = entry.get("args")
        if (
            entry.get("tag") != "App"
            or entry.get("name") != "Lblentry"
            or not isinstance(arguments, list)
            or len(arguments) != 3
            or not all(isinstance(item, dict) for item in arguments)
        ):
            raise GateError(f"malformed log entry: {entry}")
        data = domain_value(arguments[2], "Bytes")
        try:
            data_bytes = data.encode("latin-1")
        except UnicodeEncodeError as error:
            raise GateError("log entry returned a non-byte Bytes value") from error
        logs.append(
            {
                "address": domain_value(arguments[0], "Int"),
                "topics": [domain_value(topic, "Int") for topic in list_values(arguments[1])],
                "data": rendered_bytes(data_bytes),
            }
        )
    return canonical_json(logs)


def expected_logs(values: Any) -> str:
    logs = []
    for entry in concrete_logs(values, "expected logs"):
        data = ast.literal_eval(str(entry.get("data", 'b""')))
        if not isinstance(data, bytes):
            raise GateError(f"log data is not a Bytes literal: {entry.get('data')}")
        logs.append(
            {
                "address": str(entry.get("address", "0")),
                "topics": [str(topic) for topic in entry.get("topics", [])],
                "data": rendered_bytes(data),
            }
        )
    return canonical_json(logs)


def expected_int_map(values: Any) -> str:
    mapping = concrete_mapping(values, "expected storage Map")
    return ".Map" if not mapping else ",".join(
        f"{key}:{mapping[key]}" for key in sorted(mapping, key=int)
    )


def expected_accessed_storage(values: Any) -> str:
    mapping = concrete_mapping(values, "expected accessed_storage")
    return ".Map" if not mapping else ",".join(
        f"{key}:[{','.join(sorted((str(value) for value in mapping[key]), key=int))}]"
        for key in sorted(mapping, key=int)
    )


def word_stack(term: Mapping[str, Any]) -> str:
    values: list[str] = []
    while term.get("tag") == "App" and term.get("name") == "LblstackCons":
        arguments = term.get("args")
        if not isinstance(arguments, list) or len(arguments) != 2 or not all(isinstance(item, dict) for item in arguments):
            raise GateError(f"malformed stack constructor: {term}")
        values.append(domain_value(arguments[0], "Int"))
        term = arguments[1]
    if term.get("tag") != "App" or term.get("name") != "LblstackEmpty" or term.get("args") != []:
        raise GateError(f"malformed stack tail: {term}")
    return ":".join([*values, ".WordStack"])


def empty_list(term: Mapping[str, Any], name: str) -> str:
    if term.get("tag") != "App" or term.get("name") != "Lbl'Stop'List" or term.get("args") != []:
        raise GateError(f"expected empty {name}: {term}")
    return ".List"


STATUS_LABELS = {
    "Lblrunning": ".StatusCode",
    "LblbadJumpDestination": "EVMC_BAD_JUMP_DESTINATION",
    "LblinvalidMemoryAccess": "EVMC_INVALID_MEMORY_ACCESS",
    "LblinvalidInstruction": "EVMC_INVALID_INSTRUCTION",
    "LblstaticModeViolation": "EVMC_STATIC_MODE_VIOLATION",
    "LbloutOfGas": "EVMC_OUT_OF_GAS",
    "LblstackOverflow": "EVMC_STACK_OVERFLOW",
    "LblstackUnderflow": "EVMC_STACK_UNDERFLOW",
    "Lblsuccess": "EVMC_SUCCESS",
    "Lblreverted": "EVMC_REVERT",
}


def sole_state(result: Mapping[str, Any]) -> Mapping[str, Any]:
    leaves = result.get("leaves")
    if not isinstance(leaves, list) or len(leaves) != 1 or not isinstance(leaves[0], dict):
        raise GateError(f"native execution produced {0 if not isinstance(leaves, list) else len(leaves)} leaves")
    leaf = leaves[0]
    if leaf.get("reason") != "stuck":
        raise GateError(f"native execution halted with {leaf.get('reason')}: {leaf.get('detail')}")
    state = leaf.get("state")
    if not isinstance(state, dict) or state.get("format") != "KORE" or not isinstance(state.get("term"), dict):
        raise GateError("native execution returned malformed KORE JSON")
    return state["term"]


def observed(case: Mapping[str, Any], state: Mapping[str, Any]) -> dict[str, str]:
    k = cell(state, "k")
    expected_stuck_operation = case.get("expected_stuck_operation")
    if expected_stuck_operation is None:
        if k.get("tag") != "App" or k.get("name") != "dotk" or k.get("args") != []:
            raise GateError(f"{case['id']} did not halt with .K: {k}")
    else:
        arguments = k.get("args")
        if (
            k.get("tag") != "App"
            or k.get("name") != "kseq"
            or not isinstance(arguments, list)
            or len(arguments) != 2
            or not isinstance(arguments[0], dict)
            or not isinstance(arguments[1], dict)
            or arguments[1].get("name") != "dotk"
            or arguments[1].get("args") != []
        ):
            raise GateError(f"{case['id']} did not remain at the expected operation: {k}")
        operation = unwrap_injection(arguments[0])
        if operation.get("name") != f"Lbl{expected_stuck_operation}" or operation.get("args") != []:
            raise GateError(f"{case['id']} remained at the wrong operation: {operation}")
    program = domain_value(cell(state, "program"), "Bytes")
    output = domain_value(cell(state, "output"), "Bytes")
    local_mem = domain_value(cell(state, "localMem"), "Bytes")
    try:
        program_bytes = program.encode("latin-1")
        output_bytes = output.encode("latin-1")
        local_mem_bytes = local_mem.encode("latin-1")
    except UnicodeEncodeError as error:
        raise GateError(f"{case['id']} returned a non-byte Bytes value") from error
    status_term = cell(state, "statusCode")
    status = STATUS_LABELS.get(str(status_term.get("name")))
    if status is None or status_term.get("tag") != "App" or status_term.get("args") != []:
        raise GateError(f"{case['id']} returned an unknown status: {status_term}")
    outcome = {
        "id": str(case["id"]),
        "program": rendered_bytes(program_bytes),
        "stack": word_stack(cell(state, "wordStack")),
        "pc": domain_value(cell(state, "pc"), "Int"),
        "gas": domain_value(cell(state, "gas"), "Int"),
        "output": rendered_bytes(output_bytes),
        "local_mem": rendered_bytes(local_mem_bytes),
        "memory_used": domain_value(cell(state, "memoryUsed"), "Int"),
        "status": status,
    }
    if case.get("observe_storage", False):
        outcome.update({
            "storage": rendered_int_map(cell(state, "storage")),
            "accessed_storage": rendered_accessed_storage(cell(state, "accessedStorage")),
            "refund": domain_value(cell(state, "refund"), "Int"),
        })
    if case.get("observe_accounts", False):
        outcome["accessed_accounts"] = rendered_set(cell(state, "accessedAccounts"))
    if case.get("observe_logs", False):
        outcome["logs"] = rendered_logs(cell(state, "log"))
    if case.get("observe_state_stacks", False):
        outcome.update({
            "call_stack": empty_list(cell(state, "callStack"), "call stack"),
            "interim_states": empty_list(cell(state, "interimStates"), "world-state stack"),
        })
    return outcome


def expected(case: Mapping[str, Any]) -> dict[str, str]:
    outcome = {
        "id": str(case["id"]),
        "program": 'b"' + "".join(f"\\x{byte:02x}" for byte in ast.literal_eval(str(case["expected_program"]))) + '"',
        "stack": re.sub(r"\s*:\s*", ":", str(case["expected_stack"])),
        "pc": str(case["expected_pc"]),
        "gas": str(case["expected_gas"]),
        "output": rendered_bytes(
            ast.literal_eval(str(case.get("expected_output", case.get("return_data", 'b""'))))
        ),
        "local_mem": rendered_bytes(
            ast.literal_eval(str(case.get("expected_local_mem", case.get("local_mem", 'b""'))))
        ),
        "memory_used": str(case.get("expected_memory_used", case.get("memory_used", "0"))),
        "status": str(case["expected_status"]),
    }
    if case.get("observe_storage", False):
        outcome.update({
            "storage": expected_int_map(case.get("expected_storage", case.get("storage", {}))),
            "accessed_storage": expected_accessed_storage(
                case.get("expected_accessed_storage", case.get("accessed_storage", {}))
            ),
            "refund": str(case.get("expected_refund", case.get("refund", "0"))),
        })
    if case.get("observe_accounts", False):
        values = sorted(
            (
                str(value)
                for value in case.get(
                    "expected_accessed_accounts", case.get("accessed_accounts", [])
                )
            ),
            key=int,
        )
        outcome["accessed_accounts"] = ".Set" if not values else ",".join(values)
    if case.get("observe_logs", False):
        outcome["logs"] = expected_logs(case.get("expected_logs", case.get("logs", [])))
    if case.get("observe_state_stacks", False):
        outcome.update({
            "call_stack": ".List",
            "interim_states": ".List",
        })
    return outcome


def checked(case: Mapping[str, Any], outcome: dict[str, str]) -> dict[str, str]:
    wanted = expected(case)
    if outcome != wanted:
        raise GateError(f"{case['id']} differs: expected={wanted}, actual={outcome}")
    return outcome


def execute_batch(
    gate: Path,
    definition: Path,
    module: str,
    cases: list[tuple[int, Mapping[str, Any]]],
) -> list[tuple[int, dict[str, str]]]:
    outcomes: list[tuple[int, dict[str, str]]] = []
    with krs_gate.Session(gate) as session:
        session.load(definition, module)
        for index, case in cases:
            pattern = session.configure(configuration_variables(case))["pattern"]
            result = session.execute(pattern)
            if not isinstance(result, dict):
                raise GateError(f"native result shape differs: {result}")
            outcome = checked(case, observed(case, sole_state(result)))
            outcomes.append((index, outcome))
    return outcomes


def execute_corpus(
    gate: Path,
    definition: Path,
    module: str,
    cases: list[Mapping[str, Any]],
    jobs: int,
) -> list[dict[str, str]]:
    if jobs < 1:
        raise GateError("jobs must be at least one")
    indexed = list(enumerate(cases))
    chunks = [indexed[offset::jobs] for offset in range(min(jobs, len(indexed)))]
    with ThreadPoolExecutor(max_workers=len(chunks)) as pool:
        batches = pool.map(
            lambda chunk: execute_batch(gate, definition, module, chunk),
            chunks,
        )
    ordered = sorted((item for batch in batches for item in batch), key=lambda item: item[0])
    return [outcome for _, outcome in ordered]


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
    outcomes = execute_corpus(
        arguments.krs_gate,
        arguments.definition,
        arguments.module,
        cases,
        arguments.jobs,
    )
    digest = json_sha256(outcomes)
    if arguments.outcomes is not None:
        arguments.outcomes.write_text(canonical_json(outcomes) + "\n", encoding="utf-8")
    print(f"PASS native KEVM behavior: {len(outcomes)} executions; sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
