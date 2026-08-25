#!/usr/bin/env python3
"""Compare rust-analyzer mappings for one, duplicated, and call-site spans."""

import json
import pathlib
import select
import subprocess
import time


ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE = ROOT / "crates" / "accepted" / "src" / "lib.rs"
TEXT = SOURCE.read_text()
LINES = TEXT.splitlines()
SERVER = subprocess.Popen(
    ["rust-analyzer"],
    cwd=ROOT,
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.DEVNULL,
)


def send(message):
    data = json.dumps(message, separators=(",", ":")).encode()
    SERVER.stdin.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
    SERVER.stdin.flush()


def receive(timeout):
    if not select.select([SERVER.stdout], [], [], timeout)[0]:
        return None
    headers = {}
    while True:
        line = SERVER.stdout.readline()
        if line == b"\r\n":
            break
        key, value = line.decode().split(":", 1)
        headers[key.lower()] = value.strip()
    return json.loads(SERVER.stdout.read(int(headers["content-length"])))


def handle_server_request(message):
    if not message or "method" not in message or "id" not in message:
        return
    if message["method"] == "workspace/configuration":
        count = len(message.get("params", {}).get("items", []))
        result = [{} for _ in range(count)]
    else:
        result = None
    send({"jsonrpc": "2.0", "id": message["id"], "result": result})


def wait_for(request_id, timeout=30):
    deadline = time.time() + timeout
    while time.time() < deadline:
        message = receive(deadline - time.time())
        if message is None:
            return None
        handle_server_request(message)
        if message.get("id") == request_id:
            return message
    return None


def position(fragment, needle):
    line = next(index for index, text in enumerate(LINES) if fragment in text)
    return {"line": line, "character": LINES[line].index(needle) + 1}


send(
    {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {
            "processId": None,
            "rootUri": ROOT.as_uri(),
            "capabilities": {
                "workspace": {"configuration": True},
                "window": {"workDoneProgress": True},
                "textDocument": {"definition": {}},
            },
        },
    }
)
assert wait_for(1), "rust-analyzer did not initialize"
send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

primed = False
deadline = time.time() + 30
while time.time() < deadline:
    message = receive(deadline - time.time())
    if message is None:
        break
    handle_server_request(message)
    if (
        message.get("method") == "$/progress"
        and message["params"].get("token") == "rustAnalyzer/cachePriming"
        and message["params"].get("value", {}).get("kind") == "end"
    ):
        primed = True
        break
assert primed, "rust-analyzer did not finish cache priming"

send(
    {
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": SOURCE.as_uri(),
                "languageId": "rust",
                "version": 1,
                "text": TEXT,
            }
        },
    }
)

diagnostics = None
deadline = time.time() + 15
while time.time() < deadline:
    message = receive(deadline - time.time())
    if message is None:
        break
    handle_server_request(message)
    if (
        message.get("method") == "textDocument/publishDiagnostics"
        and message.get("params", {}).get("uri") == SOURCE.as_uri()
    ):
        diagnostics = message["params"].get("diagnostics", [])
        break
assert diagnostics is not None, "document diagnostics did not arrive"
assert not diagnostics, f"unexpected diagnostics: {diagnostics}"

probes = [
    ("one authored expansion use", "single_path!(model::nested::Bar)"),
    ("two duplicated authored-span uses", "duplicated_source_path!(model::nested::Bar)"),
    ("one authored plus one call-site use", "callsite_duplicate_path!(model::nested::Bar)"),
]
outcomes = {}
for request_id, (name, fragment) in enumerate(probes, 10):
    send(
        {
            "jsonrpc": "2.0",
            "id": request_id,
            "method": "textDocument/definition",
            "params": {
                "textDocument": {"uri": SOURCE.as_uri()},
                "position": position(fragment, "Bar"),
            },
        }
    )
    response = wait_for(request_id)
    result = None if response is None else response.get("result")
    count = len(result) if isinstance(result, list) else int(bool(result))
    outcomes[name] = count
    print(f"{name}: {'RESOLVED' if count else 'MISS'} ({count} target(s))")

send({"jsonrpc": "2.0", "id": 99, "method": "shutdown", "params": None})
wait_for(99, 10)
send({"jsonrpc": "2.0", "method": "exit", "params": None})
SERVER.wait(timeout=10)

assert outcomes["one authored expansion use"] == 1
assert outcomes["one authored plus one call-site use"] == 1
# This is the behavior under measurement, rather than a universal RA API
# promise. Keep it pinned so a rust-analyzer upgrade forces review.
assert outcomes["two duplicated authored-span uses"] == 1
