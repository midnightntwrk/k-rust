#!/usr/bin/env python3
"""Regenerate the committed cancellation response with the pinned RPC server."""

import os
import socket
import subprocess
import sys
import time
from pathlib import Path


def required_executable(name: str) -> str:
    value = os.environ.get(name)
    if not value:
        raise SystemExit(f"set {name} to the pinned reference executable")
    return value


def main() -> None:
    kompile = required_executable("K_KOMPILE")
    rpc = required_executable("K_KORE_RPC")
    root = Path(__file__).resolve().parent
    subprocess.run(
        [
            kompile,
            "branching.k",
            "--backend",
            "haskell",
            "--main-module",
            "BR",
            "--syntax-module",
            "BR-SYNTAX",
            "--output-definition",
            "ref",
        ],
        cwd=root,
        check=True,
        stdout=subprocess.DEVNULL,
    )

    help_text = subprocess.run(
        [rpc, "--help"], check=True, capture_output=True, text=True
    ).stdout
    smt_args = ["--no-smt"] if "--no-smt" in help_text else ["--smt", "none"]
    bug_report_args = ["--no-bug-report"] if "--no-bug-report" in help_text else []
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        port = probe.getsockname()[1]

    server = subprocess.Popen(
        [
            rpc,
            "ref/definition.kore",
            "--module",
            "BR",
            *smt_args,
            "--server-port",
            str(port),
            *bug_report_args,
        ],
        cwd=root,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        connection = None
        for _ in range(300):
            if server.poll() is not None:
                stderr = server.stderr.read() if server.stderr else ""
                raise RuntimeError(f"RPC server exited early: {stderr}")
            try:
                connection = socket.create_connection(("127.0.0.1", port), timeout=1)
                break
            except ConnectionRefusedError:
                time.sleep(0.1)
        if connection is None:
            raise TimeoutError("RPC server did not listen within 30 seconds")
        with connection:
            request = (root / "cancel-request.json").read_bytes().rstrip(b"\n") + b"\n"
            connection.sendall(request)
            response = connection.makefile("rb").readline()
        if not response:
            raise RuntimeError("RPC server returned an empty response")
        (root / "cancel-response.json").write_bytes(response)
    finally:
        server.terminate()
        try:
            server.wait(timeout=5)
        except subprocess.TimeoutExpired:
            server.kill()
            server.wait()


if __name__ == "__main__":
    main()
