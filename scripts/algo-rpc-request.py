#!/usr/bin/env python3
"""Measure one raw-socket KORE JSON-RPC request against a local krust server."""

import argparse
import json
from pathlib import Path
import signal
import socket
import subprocess
import sys
import time


def peak_rss_kib(pid):
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmHWM:"):
                return int(line.split()[1])
    except FileNotFoundError:
        pass
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--krust", required=True)
    parser.add_argument("--definition", required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--request", required=True)
    parser.add_argument("--response", required=True)
    parser.add_argument("--metrics", required=True)
    parser.add_argument("--timings")
    parser.add_argument("--trace-aggregate")
    args = parser.parse_args()

    with socket.socket() as reservation:
        reservation.bind(("127.0.0.1", 0))
        port = reservation.getsockname()[1]
    command = [args.krust, "kore-rpc", args.definition, "--module", args.module,
               "--host", "127.0.0.1", "--server-port", str(port)]
    if args.timings:
        command += ["--timings", args.timings]
    if args.trace_aggregate:
        command += ["--trace-aggregate", args.trace_aggregate]
    server = subprocess.Popen(command, stdin=subprocess.DEVNULL, stderr=subprocess.PIPE,
                              stdout=subprocess.DEVNULL)
    try:
        deadline = time.monotonic() + 30
        while True:
            try:
                connection = socket.create_connection(("127.0.0.1", port), timeout=1)
                break
            except OSError:
                if server.poll() is not None:
                    raise RuntimeError(server.stderr.read().decode(errors="replace"))
                if time.monotonic() >= deadline:
                    raise TimeoutError("KORE JSON-RPC server did not start within 30 seconds")
                time.sleep(0.05)
        with connection:
            request = Path(args.request).read_bytes().rstrip(b"\r\n") + b"\n"
            started = time.monotonic()
            connection.sendall(request)
            with connection.makefile("rb") as reader:
                response = reader.readline()
            elapsed = time.monotonic() - started
        if not response:
            raise RuntimeError("KORE JSON-RPC server closed without a response")
        Path(args.response).write_bytes(response)
        sys.stdout.buffer.write(response)
        Path(args.metrics).write_text(json.dumps({
            "response_bytes": len(response),
            "request_wall_seconds": elapsed,
            "server_peak_rss_kib": peak_rss_kib(server.pid),
        }, indent=2) + "\n")
    finally:
        if server.poll() is None:
            server.send_signal(signal.SIGTERM)
            # The measured server's signal handler sets a flag; a connection releases accept.
            deadline = time.monotonic() + 15
            while server.poll() is None and time.monotonic() < deadline:
                try:
                    with socket.create_connection(("127.0.0.1", port), timeout=1):
                        pass
                except OSError:
                    pass
                time.sleep(0.05)
            try:
                server.wait(timeout=1)
            except subprocess.TimeoutExpired:
                server.kill()
                server.wait()
        stderr = server.stderr.read()
        if stderr:
            sys.stderr.buffer.write(stderr)
        if server.returncode:
            raise RuntimeError(f"KORE JSON-RPC server exited {server.returncode}")


if __name__ == "__main__":
    main()
