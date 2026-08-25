#!/usr/bin/env python3
"""Reproducible rust-analyzer navigation probe for the Rust-hosted sample."""

import json
import pathlib
import select
import subprocess
import time


ROOT = pathlib.Path(__file__).resolve().parent.parent / "fixtures" / "tooling"
SOURCE = ROOT / "src" / "lib.rs"
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


def position(line_fragment, needle, occurrence=0):
    line = next(index for index, text in enumerate(LINES) if line_fragment in text)
    starts = []
    offset = 0
    while (found := LINES[line].find(needle, offset)) >= 0:
        starts.append(found)
        offset = found + 1
    return {"line": line, "character": starts[occurrence] + 1}


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
                "textDocument": {"definition": {}, "completion": {}},
            },
        },
    }
)
assert wait_for(1), "rust-analyzer did not initialize"
send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

primed = False
deadline = time.time() + 20
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

# didOpen invalidates expansion-derived maps. Wait for this document's first
# diagnostic publication while continuing to answer server requests.
opened_diagnostics = None
deadline = time.time() + 10
while time.time() < deadline:
    message = receive(deadline - time.time())
    if message is None:
        break
    handle_server_request(message)
    if (
        message.get("method") == "textDocument/publishDiagnostics"
        and message.get("params", {}).get("uri") == SOURCE.as_uri()
    ):
        opened_diagnostics = message["params"].get("diagnostics", [])
        break
assert opened_diagnostics is not None, "rust-analyzer did not finish opening the tooling fixture"
assert not opened_diagnostics, f"unexpected rust-analyzer diagnostics: {opened_diagnostics}"
print("authored-source diagnostics: PASS")

probes = [
    ("ordinary supertrait", "pub trait Expr", "KItem", 0),
    ("attribute argument", "constructor(sort = Expr", "Expr", 0),
    ("rule pattern", "pub fn step", "Foo", 0),
    ("rule parameter type", "pub fn step", "Expr", 0),
    ("rule body", "    Bar", "Bar", 0),
    ("term! payload", "term!(Foo)", "Foo", 0),
    ("cells! payload Foo", "term!(Foo)", "Foo", 1),
    ("cells! payload Bar", "term!(Foo)", "Bar", 0),
    ("ordinary reference", "    Foo", "Foo", 0),
]

passed = True
for request_id, (name, fragment, needle, occurrence) in enumerate(probes, 10):
    send(
        {
            "jsonrpc": "2.0",
            "id": request_id,
            "method": "textDocument/definition",
            "params": {
                "textDocument": {"uri": SOURCE.as_uri()},
                "position": position(fragment, needle, occurrence),
            },
        }
    )
    response = wait_for(request_id)
    result = None if response is None else response.get("result")
    success = bool(result)
    passed &= success
    print(f"{name}: {'PASS' if success else 'MISS'}")

send(
    {
        "jsonrpc": "2.0",
        "id": 50,
        "method": "textDocument/completion",
        "params": {
            "textDocument": {"uri": SOURCE.as_uri()},
            "position": {"line": 0, "character": 9},
        },
    }
)
response = wait_for(50)
result = None if response is None else response.get("result")
items = result.get("items", []) if isinstance(result, dict) else result or []
labels = {item.get("label") for item in items}
completion_passed = {"Term", "rule", "sort"} <= labels
passed &= completion_passed
print(f"ordinary completion: {'PASS' if completion_passed else 'MISS'}")

send({"jsonrpc": "2.0", "id": 99, "method": "shutdown", "params": None})
wait_for(99, 10)
send({"jsonrpc": "2.0", "method": "exit", "params": None})
SERVER.wait(timeout=10)
raise SystemExit(0 if passed else 1)
