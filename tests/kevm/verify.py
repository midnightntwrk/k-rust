#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KEVM operational slice."""

from __future__ import annotations

import argparse
import ast
from pathlib import Path
import re
import sys
import tempfile
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, semantics  # noqa: E402
from support.hashing import json_sha256  # noqa: E402
from support.lock import descriptor_protocol, k_version  # noqa: E402
from support.pins import Ledger, load_toml  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool, scratch_root  # noqa: E402


PORT = semantics.Port(
    label="KEVM",
    key="kevm",
    checkout=ROOT.parent / "inspirations/runtimeverification/evm-semantics",
    descriptors=1104,
    clippy_allow=("clippy::too_many_arguments",),
)
CLAIM_COUNT = 8


def definition_checks(readable: str) -> None:
    """Require the emitted definition to use the builtin Bytes surface."""

    if "  imports BYTES\n" not in readable:
        raise GateError("emitted KEVM definition does not import pinned BYTES")
    if "lengthBytes(" not in readable:
        raise GateError("emitted KEVM definition omits functional lengthBytes syntax")
    if re.search(r"V[0-9A-F]+:Bytes \[ V[0-9A-F]+:Int \]", readable) is None:
        raise GateError("emitted KEVM definition omits builtin byte lookup syntax")
    if "EvmProgram" in readable:
        raise GateError("emitted KEVM definition retained the structured program adapter")


def normalize_term(value: str) -> str:
    def normalize_bytes(match: re.Match[str]) -> str:
        decoded = ast.literal_eval(match.group(0))
        if not isinstance(decoded, bytes):
            raise GateError(f"invalid Bytes token: {match.group(0)}")
        return 'b"' + "".join(f"\\x{byte:02x}" for byte in decoded) + '"'

    value = re.sub(r'b"(?:\\.|[^"\\])*"', normalize_bytes, value)
    value = re.sub(r"\s+", " ", value.strip())
    value = re.sub(r"\s*([(),;:])\s*", r"\1", value)
    value = re.sub(r"\.\s+", ".", value)
    return value


def observed_cell(result: str, name: str) -> str:
    match = re.search(rf"<{name}>\s*(.*?)\s*</{name}>", result, re.DOTALL)
    if match is None:
        raise GateError(f"native output omitted <{name}>: {result}")
    return normalize_term(match.group(1))


def block_hashes_term(values: Any) -> str:
    if not isinstance(values, list) or not all(isinstance(value, str) for value in values):
        raise GateError(f"block_hashes is not a list of concrete Int strings: {values}")
    if not values:
        return ".List"
    return " ".join(f"ListItem({value})" for value in values)


def int_map_term(values: Any) -> str:
    if not isinstance(values, dict) or not all(isinstance(key, str) for key in values):
        raise GateError(f"storage Map is not a string-keyed table: {values}")
    if not values:
        return ".Map"
    return " ".join(f"{key} |-> {values[key]}" for key in sorted(values, key=int))


def accessed_storage_term(values: Any) -> str:
    if not isinstance(values, dict) or not all(isinstance(key, str) for key in values):
        raise GateError(f"accessed_storage is not a string-keyed table: {values}")
    if not values:
        return ".Map"
    entries = []
    for key in sorted(values, key=int):
        slots = values[key]
        if not isinstance(slots, list):
            raise GateError(f"accessed_storage[{key}] is not an array: {slots}")
        value = ".Set" if not slots else " ".join(
            f"SetItem({slot})" for slot in sorted((str(slot) for slot in slots), key=int)
        )
        entries.append(f"{key} |-> ({value})")
    return " ".join(entries)


def int_set_term(values: Any) -> str:
    if not isinstance(values, list):
        raise GateError(f"concrete Set is not an array: {values}")
    items = [f"SetItem({value})" for value in sorted((str(value) for value in values), key=int)]
    return ".Set" if not items else " ".join(items)


def logs_term(values: Any) -> str:
    if not isinstance(values, list):
        raise GateError(f"concrete logs is not an array: {values}")
    items = []
    for index, value in enumerate(values):
        if not isinstance(value, dict):
            raise GateError(f"concrete logs[{index}] is not a table: {value}")
        topics = value.get("topics", [])
        if not isinstance(topics, list):
            raise GateError(f"concrete logs[{index}].topics is not an array: {topics}")
        topic_term = ".List" if not topics else " ".join(
            f"ListItem({topic})" for topic in topics
        )
        data = value.get("data", 'b""')
        items.append(
            f"ListItem(logEntry({value.get('address', '0')}, {topic_term}, {data}))"
        )
    return ".List" if not items else " ".join(items)


def observed_int_map(result: str, name: str) -> str:
    value = observed_cell(result, name)
    return ".Map" if value == ".Map" else ",".join(
        f"{key}:{entry}" for key, entry in re.findall(r"(-?\d+)\s*\|->\s*(-?\d+)", value)
    )


def observed_int_set(result: str, name: str) -> str:
    value = observed_cell(result, name)
    if value == ".Set":
        return ".Set"
    items = sorted(re.findall(r"SetItem\((-?\d+)\)", value), key=int)
    return ",".join(items)


def observed_accessed_storage(result: str) -> str:
    value = observed_cell(result, "accessedStorage")
    if value == ".Map":
        return value
    entries = []
    for key, body in re.findall(r"(-?\d+)\s*\|->\s*\((.*?)\)(?=\s+-?\d+\s*\|->|$)", value):
        slots = sorted(re.findall(r"SetItem\((-?\d+)\)", body), key=int)
        entries.append(f"{key}:[{','.join(slots)}]")
    return ",".join(entries)


def rendered_int_map(values: Any) -> str:
    if not isinstance(values, dict) or not all(isinstance(key, str) for key in values):
        raise GateError(f"expected storage Map is not a string-keyed table: {values}")
    return ".Map" if not values else ",".join(
        f"{key}:{values[key]}" for key in sorted(values, key=int)
    )


def rendered_accessed_storage(values: Any) -> str:
    if not isinstance(values, dict) or not all(isinstance(key, str) for key in values):
        raise GateError(f"expected accessed_storage is not a string-keyed table: {values}")
    return ".Map" if not values else ",".join(
        f"{key}:[{','.join(sorted((str(slot) for slot in values[key]), key=int))}]"
        for key in sorted(values, key=int)
    )


def java_reference_gate(
    workspace: Path,
    artifacts: Path,
    k: Mapping[str, str],
    pins: Ledger,
    corpus: Mapping[str, Any],
) -> tuple[int, int]:
    definition, source, claims = semantics.reference_definition(
        PORT, workspace, artifacts, k["kompile"], CLAIM_COUNT, pins
    )
    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    outcomes: list[dict[str, str]] = []
    for case in behavior:
        empty_bytes = 'b""'
        context = [
            f"-cADDRESS={case.get('address', '0')}",
            f"-cACCOUNTID={case.get('account_id', case.get('address', '0'))}",
            f"-cBALANCE={case.get('balance', '0')}",
            f"-cCODE={case.get('code', empty_bytes)}",
            f"-cNONCE={case.get('nonce', '0')}",
            f"-cORIGIN={case.get('origin', '0')}",
            f"-cCALLER={case.get('caller', '0')}",
            f"-cCALLVALUE={case.get('call_value', '0')}",
            f"-cCALLDATA={case.get('call_data', empty_bytes)}",
            f"-cGASPRICE={case.get('gas_price', '0')}",
            f"-cRETURNDATA={case.get('return_data', empty_bytes)}",
            f"-cLOCALMEM={case.get('local_mem', empty_bytes)}",
            f"-cMEMORYUSED={case.get('memory_used', '0')}",
            f"-cSTORAGE={int_map_term(case.get('storage', {}))}",
            f"-cORIGSTORAGE={int_map_term(case.get('original_storage', case.get('storage', {})))}",
            f"-cACCESSEDSTORAGE={accessed_storage_term(case.get('accessed_storage', {}))}",
            f"-cACCESSEDACCOUNTS={int_set_term(case.get('accessed_accounts', []))}",
            f"-cLOGS={logs_term(case.get('logs', []))}",
            f"-cREFUND={case.get('refund', '0')}",
            f"-cSTATIC={str(case.get('static', False)).lower()}",
            f"-cBLOCKHASHES={block_hashes_term(case.get('block_hashes', []))}",
            f"-cCOINBASE={case.get('coinbase', '0')}",
            f"-cTIMESTAMP={case.get('timestamp', '0')}",
            f"-cNUMBER={case.get('number', '0')}",
            f"-cPREVRANDAO={case.get('prev_randao', '0')}",
            f"-cGASLIMIT={case.get('gas_limit', '0')}",
            f"-cCHAINID={case.get('chain_id', '0')}",
            f"-cBASEFEE={case.get('base_fee', '0')}",
        ]
        result = run(
            [
                k["krun"], "--definition", definition,
                "-cPGM=run", f"-cPROGRAM={case['program']}", f"-cSTACK={case['stack']}",
                f"-cPC={case['pc']}", f"-cGAS={case['gas']}", "-cSTATUS=.StatusCode",
                *context, "--output", "pretty",
            ],
            timeout=120,
        ).stdout
        expected_k = "SLOAD" if case.get("expected_stuck_operation") == "storageLoad" else ".K"
        if observed_cell(result, "k") != expected_k:
            raise GateError(f"{case['id']} did not halt: {result}")
        observed = {
            "id": str(case["id"]),
            "program": observed_cell(result, "program"),
            "stack": observed_cell(result, "wordStack"),
            "pc": observed_cell(result, "pc"),
            "gas": observed_cell(result, "gas"),
            "output": observed_cell(result, "output"),
            "local_mem": observed_cell(result, "localMem"),
            "memory_used": observed_cell(result, "memoryUsed"),
            "status": observed_cell(result, "statusCode"),
        }
        expected = {
            "id": str(case["id"]),
            "program": normalize_term(str(case["expected_program"])),
            "stack": normalize_term(str(case["expected_stack"])),
            "pc": str(case["expected_pc"]),
            "gas": str(case["expected_gas"]),
            "output": normalize_term(
                str(case.get("expected_output", case.get("return_data", empty_bytes)))
            ),
            "local_mem": normalize_term(
                str(case.get("expected_local_mem", case.get("local_mem", empty_bytes)))
            ),
            "memory_used": str(case.get("expected_memory_used", case.get("memory_used", "0"))),
            "status": str(case["expected_status"]),
        }
        if case.get("observe_storage", False):
            observed.update({
                "storage": observed_int_map(result, "storage"),
                "accessed_storage": observed_accessed_storage(result),
                "refund": observed_cell(result, "refund"),
            })
            expected.update({
                "storage": rendered_int_map(
                    case.get("expected_storage", case.get("storage", {}))
                ),
                "accessed_storage": rendered_accessed_storage(
                    case.get("expected_accessed_storage", case.get("accessed_storage", {}))
                ),
                "refund": str(case.get("expected_refund", case.get("refund", "0"))),
            })
        if case.get("observe_accounts", False):
            observed["accessed_accounts"] = observed_int_set(result, "accessedAccounts")
            values = sorted(
                (
                    str(value)
                    for value in case.get(
                        "expected_accessed_accounts", case.get("accessed_accounts", [])
                    )
                ),
                key=int,
            )
            expected["accessed_accounts"] = ".Set" if not values else ",".join(values)
        if case.get("observe_logs", False):
            observed["logs"] = observed_cell(result, "log")
            expected["logs"] = normalize_term(
                logs_term(case.get("expected_logs", case.get("logs", [])))
            )
        if case.get("observe_state_stacks", False):
            observed.update({
                "call_stack": observed_cell(result, "callStack"),
                "interim_states": observed_cell(result, "interimStates"),
            })
            expected.update({
                "call_stack": ".List",
                "interim_states": ".List",
            })
        if observed != expected:
            raise GateError(f"{case['id']} differs: expected={expected}, actual={observed}")
        outcomes.append(observed)
    pins.expect("behavior_sha256", json_sha256(outcomes))

    semantics.reference_proof(PORT, workspace, definition, source, claims, k["kprove"])
    return len(outcomes), CLAIM_COUNT


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--java-reference",
        action="store_true",
        help="run the expensive pinned Java behavior and proof authority gate",
    )
    parser.add_argument(
        "--record",
        action="store_true",
        help="run the gate and rewrite the output pins it measured",
    )
    arguments = parser.parse_args()
    try:
        pins = Ledger(PORT.pins_path, record=arguments.record)
        corpus = load_toml(PORT.corpus_path)
        environment = semantics.preflight(PORT, pins, corpus)
        krs, compiler, runner = semantics.rust_gate(PORT, environment)
        with tempfile.TemporaryDirectory(prefix="krs-kevm-", dir=scratch_root()) as temporary:
            workspace = Path(temporary)
            artifacts = semantics.artifact_gate(PORT, workspace, krs, pins, environment)
            definition_checks((artifacts / "definition.k").read_text(encoding="utf-8"))
            if arguments.java_reference:
                k = {name: k_tool(name, k_version()) for name in ("kompile", "krun", "kprove")}
                executions, proofs = java_reference_gate(workspace, artifacts, k, pins, corpus)
                qualification = f"{executions} Java reference executions; {proofs} Java reference proofs"
            else:
                definition = semantics.native_definition(
                    workspace, artifacts, compiler, pins, environment
                )
                executions = semantics.native_behavior(
                    PORT, runner, definition, pins, corpus, environment
                )
                qualification = (
                    f"{executions} K-Rust executions; "
                    f"{CLAIM_COUNT} Java reference proofs deferred to --java-reference"
                )
        pins.finish("readable KEVM operational slice")
        print(
            f"PASS readable KEVM operational slice: {PORT.descriptors} descriptors; {qualification}; "
            f"protocol {descriptor_protocol()}; K {k_version()}"
        )
        return 0
    except (GateError, OSError) as error:
        print(f"FAIL readable KEVM operational slice: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
