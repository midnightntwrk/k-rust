#!/usr/bin/env python3
"""Persistent K-Rust execution support for the KEVM qualification corpus."""

from __future__ import annotations

import argparse
import ast
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib
from typing import Any, Mapping


class NativeError(RuntimeError):
    """The native runner or its concrete result violated the gate protocol."""


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def kore_bytes(source: str) -> str:
    value = ast.literal_eval(source)
    if not isinstance(value, bytes):
        raise NativeError(f"program is not a Python Bytes literal: {source}")
    return '"' + "".join(f"\\x{byte:02x}" for byte in value) + '"'


def kore_int(value: str) -> str:
    try:
        parsed = int(value)
    except ValueError as error:
        raise NativeError(f"invalid concrete Int: {value}") from error
    return f'\\dv{{SortInt{{}}}}("{parsed}")'


def kore_bool(value: Any) -> str:
    if not isinstance(value, bool):
        raise NativeError(f"invalid concrete Bool: {value}")
    return f'\\dv{{SortBool{{}}}}("{str(value).lower()}")'


def concrete_mapping(value: Any, name: str) -> Mapping[str, Any]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise NativeError(f"{name} is not a string-keyed table: {value}")
    return value


def kore_set(values: Any) -> str:
    if not isinstance(values, list):
        raise NativeError(f"concrete Set is not an array: {values}")
    result = "Lbl'Stop'Set{}()"
    for value in sorted((str(value) for value in values), key=int):
        item = f"LblSetItem{{}}(inj{{SortInt{{}},SortKItem{{}}}}({kore_int(value)}))"
        result = f"Lbl'Unds'Set'Unds'{{}}({result},{item})"
    return result


def kore_int_map(values: Any) -> str:
    mapping = concrete_mapping(values, "concrete Int Map")
    result = "Lbl'Stop'Map{}()"
    for key in sorted(mapping, key=int):
        item = (
            "Lbl'UndsPipe'-'-GT-Unds'{}("
            f"inj{{SortInt{{}},SortKItem{{}}}}({kore_int(key)}),"
            f"inj{{SortInt{{}},SortKItem{{}}}}({kore_int(str(mapping[key]))}))"
        )
        result = f"Lbl'Unds'Map'Unds'{{}}({result},{item})"
    return result


def kore_accessed_storage(values: Any) -> str:
    mapping = concrete_mapping(values, "accessed_storage")
    result = "Lbl'Stop'Map{}()"
    for key in sorted(mapping, key=int):
        item = (
            "Lbl'UndsPipe'-'-GT-Unds'{}("
            f"inj{{SortInt{{}},SortKItem{{}}}}({kore_int(key)}),"
            f"inj{{SortSet{{}},SortKItem{{}}}}({kore_set(mapping[key])}))"
        )
        result = f"Lbl'Unds'Map'Unds'{{}}({result},{item})"
    return result


def kore_stack(source: str) -> str:
    values = source.split(" : ")
    if not values or values.pop() != ".WordStack":
        raise NativeError(f"unsupported concrete WordStack: {source}")
    result = "LblstackEmpty{}()"
    for value in reversed(values):
        result = f"LblstackCons{{}}({kore_int(value)},{result})"
    return result


def kore_list(values: Any) -> str:
    if not isinstance(values, list) or not all(isinstance(value, str) for value in values):
        raise NativeError(f"block_hashes is not a list of concrete Int strings: {values}")
    result = "Lbl'Stop'List{}()"
    for value in reversed(values):
        item = f"LblListItem{{}}(inj{{SortInt{{}},SortKItem{{}}}}({kore_int(value)}))"
        result = f"Lbl'Unds'List'Unds'{{}}({item},{result})"
    return result


def concrete_logs(values: Any, name: str) -> list[Mapping[str, Any]]:
    if not isinstance(values, list):
        raise NativeError(f"{name} is not an array: {values}")
    logs: list[Mapping[str, Any]] = []
    for index, value in enumerate(values):
        entry = concrete_mapping(value, f"{name}[{index}]")
        topics = entry.get("topics", [])
        if not isinstance(topics, list):
            raise NativeError(f"{name}[{index}].topics is not an array: {topics}")
        logs.append(entry)
    return logs


def kore_logs(values: Any) -> str:
    result = "Lbl'Stop'List{}()"
    for entry in concrete_logs(values, "logs"):
        address = kore_int(str(entry.get("address", "0")))
        topics = kore_list([str(topic) for topic in entry.get("topics", [])])
        data = f'\\dv{{SortBytes{{}}}}({kore_bytes(str(entry.get("data", "b\"\"")))})'
        log = f"Lblentry{{}}({address},{topics},{data})"
        item = f"LblListItem{{}}(inj{{SortLogEntry{{}},SortKItem{{}}}}({log}))"
        result = f"Lbl'Unds'List'Unds'{{}}({result},{item})"
    return result


def rendered_bytes(value: bytes) -> str:
    return 'b"' + "".join(f"\\x{byte:02x}" for byte in value) + '"'


def map_entry(name: str, sort: str, value: str) -> str:
    return (
        "Lbl'UndsPipe'-'-GT-Unds'{}("
        f'inj{{SortKConfigVar{{}},SortKItem{{}}}}(\\dv{{SortKConfigVar{{}}}}("${name}")),'
        f"inj{{Sort{sort}{{}},SortKItem{{}}}}({value}))"
    )


def initial_pattern(case: Mapping[str, Any]) -> str:
    call_data = kore_bytes(str(case.get("call_data", 'b""')))
    return_data = kore_bytes(str(case.get("return_data", 'b""')))
    local_mem = kore_bytes(str(case.get("local_mem", 'b""')))
    entries = (
        map_entry("PGM", "Command", "Lblrun{}()"),
        map_entry("PROGRAM", "Bytes", f"\\dv{{SortBytes{{}}}}({kore_bytes(str(case['program']))})"),
        map_entry(
            "JUMPDESTS",
            "Bytes",
            f"\\dv{{SortBytes{{}}}}({kore_bytes(str(case.get('jump_dests', 'b\"\"')))})",
        ),
        map_entry("ADDRESS", "Int", kore_int(str(case.get("address", "0")))),
        map_entry("ACCOUNTID", "Int", kore_int(str(case.get("account_id", case.get("address", "0"))))),
        map_entry("BALANCE", "Int", kore_int(str(case.get("balance", "0")))),
        map_entry(
            "CODE",
            "Bytes",
            f"\\dv{{SortBytes{{}}}}({kore_bytes(str(case.get('code', 'b\"\"')))})",
        ),
        map_entry("NONCE", "Int", kore_int(str(case.get("nonce", "0")))),
        map_entry("ORIGIN", "Int", kore_int(str(case.get("origin", "0")))),
        map_entry("CALLER", "Int", kore_int(str(case.get("caller", "0")))),
        map_entry("CALLVALUE", "Int", kore_int(str(case.get("call_value", "0")))),
        map_entry(
            "CALLDATA",
            "Bytes",
            f"\\dv{{SortBytes{{}}}}({call_data})",
        ),
        map_entry("GASPRICE", "Int", kore_int(str(case.get("gas_price", "0")))),
        map_entry(
            "RETURNDATA",
            "Bytes",
            f"\\dv{{SortBytes{{}}}}({return_data})",
        ),
        map_entry(
            "LOCALMEM",
            "Bytes",
            f"\\dv{{SortBytes{{}}}}({local_mem})",
        ),
        map_entry("MEMORYUSED", "Int", kore_int(str(case.get("memory_used", "0")))),
        map_entry("CALLGAS", "Int", kore_int(str(case.get("call_gas", "0")))),
        map_entry("CALLDEPTH", "Int", kore_int(str(case.get("call_depth", "0")))),
        map_entry(
            "CODEADDRESS",
            "Int",
            kore_int(str(case.get("code_address", case.get("address", "0")))),
        ),
        map_entry("CALLSTACK", "List", kore_list(case.get("call_stack", []))),
        map_entry("INTERIMSTATES", "List", kore_list(case.get("interim_states", []))),
        map_entry("TOUCHEDACCOUNTS", "Set", kore_set(case.get("touched_accounts", []))),
        map_entry("STORAGE", "Map", kore_int_map(case.get("storage", {}))),
        map_entry("ORIGSTORAGE", "Map", kore_int_map(case.get("original_storage", case.get("storage", {})))),
        map_entry("ACCESSEDSTORAGE", "Map", kore_accessed_storage(case.get("accessed_storage", {}))),
        map_entry("ACCESSEDACCOUNTS", "Set", kore_set(case.get("accessed_accounts", []))),
        map_entry("LOGS", "List", kore_logs(case.get("logs", []))),
        map_entry("REFUND", "Int", kore_int(str(case.get("refund", "0")))),
        map_entry("SELFDESTRUCT", "Set", kore_set(case.get("self_destruct", []))),
        map_entry("CREATEDACCOUNTS", "Set", kore_set(case.get("created_accounts", []))),
        map_entry("STATIC", "Bool", kore_bool(case.get("static", False))),
        map_entry("BLOCKHASHES", "List", kore_list(case.get("block_hashes", []))),
        map_entry("COINBASE", "Int", kore_int(str(case.get("coinbase", "0")))),
        map_entry("TIMESTAMP", "Int", kore_int(str(case.get("timestamp", "0")))),
        map_entry("NUMBER", "Int", kore_int(str(case.get("number", "0")))),
        map_entry("PREVRANDAO", "Int", kore_int(str(case.get("prev_randao", "0")))),
        map_entry("GASLIMIT", "Int", kore_int(str(case.get("gas_limit", "0")))),
        map_entry("CHAINID", "Int", kore_int(str(case.get("chain_id", "0")))),
        map_entry("BASEFEE", "Int", kore_int(str(case.get("base_fee", "0")))),
        map_entry("STACK", "WordStack", kore_stack(str(case["stack"]))),
        map_entry("PC", "Int", kore_int(str(case["pc"]))),
        map_entry("GAS", "Int", kore_int(str(case["gas"]))),
        map_entry("STATUS", "StatusCode", "Lblrunning{}()"),
    )
    configuration = "Lbl'Stop'Map{}()"
    for entry in entries:
        configuration = f"Lbl'Unds'Map'Unds'{{}}({configuration},{entry})"
    return f"LblinitGeneratedTopCell{{}}({configuration})"


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
        raise NativeError(f"native result contains {len(matches)} <{name}> cells")
    arguments = matches[0].get("args")
    if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
        raise NativeError(f"native <{name}> cell is malformed")
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
        raise NativeError(f"expected concrete {sort} domain value: {term}")
    return str(term["value"])


def unwrap_injection(term: Mapping[str, Any]) -> Mapping[str, Any]:
    while term.get("tag") == "App" and term.get("name") == "inj":
        arguments = term.get("args")
        if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
            raise NativeError(f"malformed sort injection: {term}")
        term = arguments[0]
    return term


def map_items(term: Mapping[str, Any]) -> list[tuple[Mapping[str, Any], Mapping[str, Any]]]:
    name = term.get("name")
    arguments = term.get("args")
    if term.get("tag") == "App" and name == "Lbl'Stop'Map" and arguments == []:
        return []
    if term.get("tag") == "App" and name == "Lbl'Unds'Map'Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
        return [*map_items(arguments[0]), *map_items(arguments[1])]
    if term.get("tag") == "App" and name == "Lbl'UndsPipe'-'-GT-Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
        return [(unwrap_injection(arguments[0]), unwrap_injection(arguments[1]))]
    raise NativeError(f"malformed concrete Map: {term}")


def set_values(term: Mapping[str, Any]) -> list[str]:
    name = term.get("name")
    arguments = term.get("args")
    if term.get("tag") == "App" and name == "Lbl'Stop'Set" and arguments == []:
        return []
    if term.get("tag") == "App" and name == "Lbl'Unds'Set'Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
        return [*set_values(arguments[0]), *set_values(arguments[1])]
    if term.get("tag") == "App" and name == "LblSetItem" and isinstance(arguments, list) and len(arguments) == 1 and isinstance(arguments[0], dict):
        return [domain_value(unwrap_injection(arguments[0]), "Int")]
    raise NativeError(f"malformed concrete Set: {term}")


def list_values(term: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    name = term.get("name")
    arguments = term.get("args")
    if term.get("tag") == "App" and name == "Lbl'Stop'List" and arguments == []:
        return []
    if term.get("tag") == "App" and name == "Lbl'Unds'List'Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
        return [*list_values(arguments[0]), *list_values(arguments[1])]
    if term.get("tag") == "App" and name == "LblListItem" and isinstance(arguments, list) and len(arguments) == 1 and isinstance(arguments[0], dict):
        return [unwrap_injection(arguments[0])]
    raise NativeError(f"malformed concrete List: {term}")


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
            raise NativeError(f"malformed log entry: {entry}")
        data = domain_value(arguments[2], "Bytes")
        try:
            data_bytes = data.encode("latin-1")
        except UnicodeEncodeError as error:
            raise NativeError("log entry returned a non-byte Bytes value") from error
        logs.append(
            {
                "address": domain_value(arguments[0], "Int"),
                "topics": [domain_value(topic, "Int") for topic in list_values(arguments[1])],
                "data": rendered_bytes(data_bytes),
            }
        )
    return canonical(logs)


def expected_logs(values: Any) -> str:
    logs = []
    for entry in concrete_logs(values, "expected logs"):
        data = ast.literal_eval(str(entry.get("data", 'b""')))
        if not isinstance(data, bytes):
            raise NativeError(f"log data is not a Bytes literal: {entry.get('data')}")
        logs.append(
            {
                "address": str(entry.get("address", "0")),
                "topics": [str(topic) for topic in entry.get("topics", [])],
                "data": rendered_bytes(data),
            }
        )
    return canonical(logs)


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
            raise NativeError(f"malformed stack constructor: {term}")
        values.append(domain_value(arguments[0], "Int"))
        term = arguments[1]
    if term.get("tag") != "App" or term.get("name") != "LblstackEmpty" or term.get("args") != []:
        raise NativeError(f"malformed stack tail: {term}")
    return ":".join([*values, ".WordStack"])


def empty_list(term: Mapping[str, Any], name: str) -> str:
    if term.get("tag") != "App" or term.get("name") != "Lbl'Stop'List" or term.get("args") != []:
        raise NativeError(f"expected empty {name}: {term}")
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


def observed(case: Mapping[str, Any], result: Mapping[str, Any]) -> dict[str, str]:
    leaves = result.get("leaves")
    if not isinstance(leaves, list) or len(leaves) != 1 or not isinstance(leaves[0], dict):
        raise NativeError(f"{case['id']} produced {0 if not isinstance(leaves, list) else len(leaves)} leaves")
    leaf = leaves[0]
    if leaf.get("reason") != "stuck":
        raise NativeError(f"{case['id']} halted with {leaf.get('reason')}: {leaf.get('detail')}")
    state = leaf.get("state")
    if not isinstance(state, dict) or state.get("format") != "KORE" or not isinstance(state.get("term"), dict):
        raise NativeError(f"{case['id']} returned malformed KORE JSON")
    state = state["term"]
    k = cell(state, "k")
    expected_stuck_operation = case.get("expected_stuck_operation")
    if expected_stuck_operation is None:
        if k.get("tag") != "App" or k.get("name") != "dotk" or k.get("args") != []:
            raise NativeError(f"{case['id']} did not halt with .K: {k}")
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
            raise NativeError(f"{case['id']} did not remain at the expected operation: {k}")
        operation = unwrap_injection(arguments[0])
        if operation.get("name") != f"Lbl{expected_stuck_operation}" or operation.get("args") != []:
            raise NativeError(f"{case['id']} remained at the wrong operation: {operation}")
    program = domain_value(cell(state, "program"), "Bytes")
    output = domain_value(cell(state, "output"), "Bytes")
    local_mem = domain_value(cell(state, "localMem"), "Bytes")
    try:
        program_bytes = program.encode("latin-1")
        output_bytes = output.encode("latin-1")
        local_mem_bytes = local_mem.encode("latin-1")
    except UnicodeEncodeError as error:
        raise NativeError(f"{case['id']} returned a non-byte Bytes value") from error
    status_term = cell(state, "statusCode")
    status = STATUS_LABELS.get(str(status_term.get("name")))
    if status is None or status_term.get("tag") != "App" or status_term.get("args") != []:
        raise NativeError(f"{case['id']} returned an unknown status: {status_term}")
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


def execute_batch(
    runner: Path,
    definition: Path,
    module: str,
    cases: list[tuple[int, Mapping[str, Any]]],
) -> list[tuple[int, dict[str, str]]]:
    requests = "".join(
        canonical({"id": str(case["id"]), "operation": "execute", "pattern": initial_pattern(case)}) + "\n"
        for _, case in cases
    )
    process = subprocess.run(
        [runner, definition, module],
        input=requests,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=600,
        check=False,
    )
    if process.returncode != 0:
        raise NativeError(f"native runner failed with {process.returncode}: {process.stderr.strip()}")
    lines = process.stdout.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    responses = [json.loads(line) for line in lines]
    if len(responses) != len(cases):
        raise NativeError(f"native runner returned {len(responses)} responses for {len(cases)} requests")
    outcomes: list[tuple[int, dict[str, str]]] = []
    for (index, case), response in zip(cases, responses, strict=True):
        if response.get("id") != case["id"] or not isinstance(response.get("result"), dict):
            raise NativeError(f"native response order or shape differs: {response}")
        outcome = observed(case, response["result"])
        wanted = expected(case)
        if outcome != wanted:
            raise NativeError(f"{case['id']} differs: expected={wanted}, actual={outcome}")
        outcomes.append((index, outcome))
    return outcomes


def execute_corpus(
    runner: Path,
    definition: Path,
    module: str,
    cases: list[Mapping[str, Any]],
    jobs: int,
) -> list[dict[str, str]]:
    if jobs < 1:
        raise NativeError("jobs must be at least one")
    indexed = list(enumerate(cases))
    chunks = [indexed[offset::jobs] for offset in range(min(jobs, len(indexed)))]
    with ThreadPoolExecutor(max_workers=len(chunks)) as pool:
        batches = pool.map(
            lambda chunk: execute_batch(runner, definition, module, chunk),
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
    parser.add_argument("runner", type=Path)
    parser.add_argument("definition", type=Path)
    parser.add_argument("module")
    parser.add_argument("corpus", type=Path)
    arguments = parser.parse_args()
    with arguments.corpus.open("rb") as stream:
        corpus = tomllib.load(stream)
    cases = corpus.get("behavior")
    if not isinstance(cases, list) or not cases:
        raise NativeError("behavior corpus is empty")
    if arguments.case_ids:
        requested = set(arguments.case_ids)
        known = {str(case.get("id")) for case in cases}
        missing = sorted(requested - known)
        if missing:
            raise NativeError(f"unknown behavior cases: {', '.join(missing)}")
        cases = [case for case in cases if case.get("id") in requested]
    outcomes = execute_corpus(
        arguments.runner,
        arguments.definition,
        arguments.module,
        cases,
        arguments.jobs,
    )
    digest = hashlib.sha256(canonical(outcomes).encode()).hexdigest()
    print(f"PASS native KEVM behavior: {len(outcomes)} executions; sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
