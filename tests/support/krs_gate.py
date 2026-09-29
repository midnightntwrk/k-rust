"""Client for the native gate's compile command and JSON session protocol.

This module owns the Python side of the protocol.
Callers supply opaque KORE text and consume the gate's JSON results.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any, Mapping

from support import GateError, ROOT
from support import process


SESSION_EXIT_TIMEOUT_SECONDS = 30


def compile(
    krs_gate: Path,
    definition_ir: Path,
    output: Path,
    *,
    environment: Mapping[str, str] | None,
    timings: Path | None = None,
) -> None:
    """Compile a Definition IR file to KORE with the one-shot gate command."""

    command = [os.fspath(krs_gate), "compile"]
    if timings is not None:
        command.extend(("--timings", os.fspath(timings)))
    command.extend((os.fspath(definition_ir), os.fspath(output)))
    process.run(command, environment=environment, timeout=900)


class Session:
    """Exchange one request and one response at a time with a gate session."""

    def __init__(self, krs_gate: Path, *, environment: Mapping[str, str] | None = None) -> None:
        self._krs_gate = krs_gate
        self._environment = environment
        self._process: subprocess.Popen[str] | None = None
        self._stderr: Any = None
        self._next_id = 1
        self._reported_exit = False

    def __enter__(self) -> Session:
        if self._process is not None:
            raise GateError("gate session is already open")
        self._stderr = tempfile.TemporaryFile(mode="w+t", encoding="utf-8")
        try:
            self._process = subprocess.Popen(
                [os.fspath(self._krs_gate), "session"],
                cwd=ROOT,
                env={**os.environ, **process.BASE_ENVIRONMENT, **(self._environment or {})},
                text=True,
                encoding="utf-8",
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=self._stderr,
                start_new_session=True,
            )
        except BaseException:
            self._stderr.close()
            self._stderr = None
            raise
        return self

    def __exit__(self, _type: Any, _value: Any, _traceback: Any) -> None:
        child = self._process
        if child is None:
            return
        try:
            assert child.stdin is not None
            child.stdin.close()
            child.stdin = None
            try:
                child.wait(timeout=SESSION_EXIT_TIMEOUT_SECONDS)
            except subprocess.TimeoutExpired as error:
                process.terminate_group(child)
                raise GateError("gate session did not exit after stdin closed; its process group was terminated") from error
            if child.returncode != 0 and _type is None and not self._reported_exit:
                raise GateError(f"gate session exited ({child.returncode}): {self._stderr_text()}")
        finally:
            if child.poll() is None:
                process.terminate_group(child)
            assert child.stdout is not None
            child.stdout.close()
            self._process = None
            self._stderr.close()
            self._stderr = None

    def _stderr_text(self) -> str:
        if self._stderr is None:
            return ""
        self._stderr.flush()
        self._stderr.seek(0)
        return self._stderr.read().strip()

    def request(self, operation: str, **fields: Any) -> Any:
        """Send one operation and return its result, or raise ``GateError``."""

        child = self._process
        if child is None or child.stdin is None or child.stdout is None:
            raise GateError("gate session is not open")
        request_id = str(self._next_id)
        self._next_id += 1
        request = {"id": request_id, "operation": operation, **fields}
        try:
            child.stdin.write(json.dumps(request, separators=(",", ":")) + "\n")
            child.stdin.flush()
        except BrokenPipeError as error:
            child.wait()
            self._reported_exit = True
            raise GateError(
                f"gate session exited before response to request {request_id}: {self._stderr_text()}"
            ) from error
        line = child.stdout.readline()
        if not line:
            child.wait()
            self._reported_exit = True
            raise GateError(
                f"gate session exited before response to request {request_id}: {self._stderr_text()}"
            )
        try:
            response = json.loads(line)
        except json.JSONDecodeError as error:
            raise GateError(f"invalid gate response for request {request_id}: {error}") from error
        if not isinstance(response, dict) or response.get("id") != request_id:
            raise GateError(f"gate response id differs from request {request_id}: {response!r}")
        if "error" in response:
            detail = response["error"]
            message = detail.get("message") if isinstance(detail, dict) else detail
            raise GateError(f"gate request {request_id} failed: {message}")
        if "result" not in response:
            raise GateError(f"gate response has no result for request {request_id}")
        return response["result"]

    def load(self, definition_ir: Path, module: str) -> dict[str, Any]:
        """Load emitted Definition IR and its main module."""

        return self.request("definition.load", definition_ir=os.fspath(definition_ir), module=module)

    def configure(self, variables: Mapping[str, str]) -> dict[str, Any]:
        """Parse surface configuration variables and return their KORE pattern."""

        return self.request("configure", variables=dict(variables))

    def execute(self, pattern: str, **options: Any) -> dict[str, Any]:
        """Execute an opaque KORE pattern and return the serialized result."""

        return self.request("execute", pattern=pattern, **options)

    def prove(self, claim: str) -> dict[str, Any]:
        """Prove an opaque KORE claim and return the serialized result."""

        return self.request("prove", claim=claim)
