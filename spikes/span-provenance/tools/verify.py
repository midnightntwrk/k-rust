#!/usr/bin/env python3
"""Run all stable-rustc span-provenance gates."""

import json
import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parent.parent


def run(command, cwd=ROOT, expect_success=True):
    print("+", " ".join(command))
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if (result.returncode == 0) != expect_success:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(f"unexpected exit status {result.returncode}")
    return result


version = run(["rustc", "--version"]).stdout.strip()
assert version.startswith("rustc 1.97.1 "), version
run(["cargo", "fmt", "--all", "--", "--check"])
run(["cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings"])
run(["cargo", "test", "--workspace"])

rejected = run(
    [
        "cargo",
        "check",
        "--manifest-path",
        "fixtures/rejected/Cargo.toml",
        "--message-format=json",
    ],
    expect_success=False,
)
diagnostics = [
    json.loads(line)["message"]
    for line in rejected.stdout.splitlines()
    if line.startswith("{") and json.loads(line).get("reason") == "compiler-message"
]
assert any(
    diagnostic["message"] == "expected identifier"
    and any(span["byte_start"] == 123 and span["byte_end"] == 140 for span in diagnostic["spans"])
    for diagnostic in diagnostics
), diagnostics
print("rejected invocation-local diagnostic: PASS")

unstable = run(
    [
        "cargo",
        "check",
        "--manifest-path",
        "fixtures/unstable-api/Cargo.toml",
        "--message-format=json",
    ],
    expect_success=False,
)
diagnostics = [
    json.loads(line)["message"]
    for line in unstable.stdout.splitlines()
    if line.startswith("{") and json.loads(line).get("reason") == "compiler-message"
]
unstable_methods = {
    span["text"][0]["text"].strip()
    for diagnostic in diagnostics
    if (diagnostic.get("code") or {}).get("code") == "E0658"
    for span in diagnostic["spans"]
    if span["is_primary"]
}
expected_methods = {
    "let _ = span.byte_range();",
    "let _ = span.join(span);",
    "let _ = span.parent();",
    "let _ = span.source();",
}
assert expected_methods <= unstable_methods, unstable_methods
print("stable API boundary: PASS")

lsp = run([sys.executable, "tools/lsp_probe.py"])
print(lsp.stdout, end="")
print("all span-provenance gates: PASS")
