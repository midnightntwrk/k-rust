"""Client for the native gate's compile command and JSON session protocol.

This module owns the Python side of the protocol.
Callers supply opaque KORE or KAST text and consume the gate's JSON results.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import threading
from typing import Any, Mapping, Sequence

from support import GateError, ROOT
from support import process
from support.tools import z3_environment


SESSION_EXIT_TIMEOUT_SECONDS = 30
REQUEST_TIMEOUT_SECONDS = 900


def build(target: Path, *, environment: Mapping[str, str] | None = None) -> Path:
    """Build the locked release gate in a caller-owned Cargo target directory."""

    binary = target / "release" / "krs-gate"
    process.run(
        ["cargo", "+stable", "build", "--locked", "--offline", "--release", "-p", "krs-gate", "--bins"],
        environment={
            **z3_environment(),
            **(environment or {}),
            "CARGO_NET_OFFLINE": "true",
            "CARGO_TARGET_DIR": os.fspath(target),
        },
        timeout=900,
    )
    if not binary.is_file():
        raise GateError(f"Cargo did not produce the gate binary at {binary}")
    return binary


def configured_or_build(default_target: Path) -> Path:
    """Use the gate binary named by ``KRS_GATE_BIN``, or build it in ``default_target``.

    A caller that already built the gate passes it on through ``KRS_GATE_BIN``,
    so a standalone run and a nested run share one release build.
    """

    configured = os.environ.get("KRS_GATE_BIN")
    if configured is None:
        return build(default_target)
    binary = Path(configured)
    if not binary.is_file():
        raise GateError(f"KRS_GATE_BIN names no gate binary: {binary}")
    return binary


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


def digest(
    krs_gate: Path, kore: Path, semantics: Path, *,
    environment: Mapping[str, str] | None = None,
) -> str:
    """Open one unloaded session and digest a kompiled KORE definition."""

    with Session(krs_gate, environment=environment) as session:
        return session.digest(kore, semantics)


def kore_attributes(
    krs_gate: Path, kore: Path, labels: Sequence[str], attributes: Sequence[str], *,
    environment: Mapping[str, str] | None = None,
) -> dict[str, dict[str, str]]:
    """Read symbol-declaration attributes of a KORE definition in one unloaded session."""

    return kore_symbols(krs_gate, kore, labels, attributes, environment=environment)[0]


def kore_symbols(
    krs_gate: Path, kore: Path, labels: Sequence[str], attributes: Sequence[str], *,
    environment: Mapping[str, str] | None = None,
) -> tuple[dict[str, dict[str, str]], list[list[str]]]:
    """Read symbol-declaration attributes and the sorted `symbol-overload` axiom
    pairs of a KORE definition in one unloaded session."""

    with Session(krs_gate, environment=environment) as session:
        response = session.request(
            "kore.attributes", kore=os.fspath(kore), labels=list(labels), attributes=list(attributes),
        )
    return response["symbols"], response["overloads"]


def kore_instances(
    krs_gate: Path, kore: Path, labels: Sequence[str], *,
    environment: Mapping[str, str] | None = None,
) -> dict[str, list[list[str]]]:
    """Read the sort instances of the named labels' symbol applications in one unloaded session."""

    with Session(krs_gate, environment=environment) as session:
        return session.kore_instances(kore, list(labels))


def ir_query(
    krs_gate: Path, artifacts: Path, query: Mapping[str, Any], *,
    environment: Mapping[str, str] | None = None,
) -> Any:
    """Query emitted artifacts in one unloaded session."""

    with Session(krs_gate, environment=environment) as session:
        return session.ir_query(artifacts, query)


def require_route(
    krs_gate: Path, artifacts: Path, route: str, *,
    environment: Mapping[str, str] | None = None,
) -> None:
    """Refuse emitted artifacts that need a capability `route` lacks (V8).

    The table is KRS's own (`krs_k_rust::ROUTE_CAPABILITIES`); a refusal is
    raised before anything is compiled for the route, and never weakened.
    """

    refusals = ir_query(
        krs_gate, artifacts, {"kind": "capabilities", "route": route}, environment=environment,
    )["refusals"]
    if refusals:
        raise GateError("\n".join(f"error[{refusal['code']}]: {refusal['message']}" for refusal in refusals))


def registration_table(
    krs_gate: Path, source: Path, display_file: str, crate_name: str, facade_alias: str, *,
    environment: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    """Expand authored crate-root registrations in one unloaded session."""

    with Session(krs_gate, environment=environment) as session:
        return session.registration_table(source, display_file, crate_name, facade_alias)


def ir_queries(
    krs_gate: Path, artifacts: Path, queries: list[Mapping[str, Any]], *,
    environment: Mapping[str, str] | None = None,
) -> list[Any]:
    """Query one artifact directory repeatedly in one unloaded session."""

    with Session(krs_gate, environment=environment) as session:
        return [session.ir_query(artifacts, query) for query in queries]


class Session:
    """Exchange requests with a gate session, serializing concurrent callers."""

    def __init__(self, krs_gate: Path, *, environment: Mapping[str, str] | None = None) -> None:
        self._krs_gate = krs_gate
        self._environment = environment
        self._process: subprocess.Popen[str] | None = None
        self._stderr: Any = None
        self._next_id = 1
        self._reported_exit = False
        self._request_lock = threading.Lock()

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

    def request(self, operation: str, *, timeout: float = REQUEST_TIMEOUT_SECONDS, **fields: Any) -> Any:
        """Send one operation and return its result, or raise ``GateError``.

        Concurrent callers hold one lock across the complete write and read.
        A request that has no response within ``timeout`` seconds kills the session's process group.
        """

        with self._request_lock:
            return self._request(operation, timeout=timeout, **fields)

    def _request(self, operation: str, *, timeout: float, **fields: Any) -> Any:
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
        expired = threading.Event()

        def expire() -> None:
            expired.set()
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

        timer = threading.Timer(timeout, expire)
        timer.start()
        try:
            line = child.stdout.readline()
        finally:
            timer.cancel()
        if expired.is_set():
            child.wait()
            self._reported_exit = True
            raise GateError(f"gate request {request_id} ({operation}) exceeded {timeout} seconds; the session was killed")
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

    def load(
        self, definition_ir: Path, module: str, *, definition_kore_sha256: str | None = None,
    ) -> dict[str, Any]:
        """Load emitted Definition IR and its main module.

        When ``definition_kore_sha256`` is given, the KORE the session compiled must have that digest.
        """

        loaded = self.request("definition.load", definition_ir=os.fspath(definition_ir), module=module)
        if definition_kore_sha256 is not None and loaded.get("definition_kore_sha256") != definition_kore_sha256:
            raise GateError(
                f"session definition KORE sha256 {loaded.get('definition_kore_sha256')} "
                f"differs from the compiled definition's {definition_kore_sha256}"
            )
        return loaded

    def ir_query(self, artifacts: Path, query: Mapping[str, Any]) -> Any:
        """Read a closed typed artifact projection without loading a definition."""

        return self.request("ir.query", artifacts=os.fspath(artifacts), query=dict(query))

    def registration_table(
        self, source: Path, display_file: str, crate_name: str, facade_alias: str,
    ) -> dict[str, Any]:
        """Return the product's registration table and cfg-carrying factory list."""

        return self.request(
            "registration.table", source=os.fspath(source), display_file=display_file,
            crate_name=crate_name, facade_alias=facade_alias,
        )

    def configure(self, variables: Mapping[str, str]) -> dict[str, Any]:
        """Parse surface configuration variables and return their KORE pattern."""

        return self.request("configure", variables=dict(variables))

    def execute(self, pattern: str, **options: Any) -> dict[str, Any]:
        """Execute an opaque KORE pattern and return the serialized result."""

        return self.request("execute", pattern=pattern, **options)

    def search(self, pattern: str, **options: Any) -> dict[str, Any]:
        """Search final states from an opaque KORE pattern and return the result."""

        return self.request("search", pattern=pattern, **options)

    def read(self, text: str, keep: str) -> dict[str, Any]:
        """Retain a Java KORE result under a session state name."""

        return self.request("kore.read", text=text, keep=keep)

    def digest(self, kore: Path, semantics: Path) -> str:
        """Digest a kompiled definition independently of source paths and generated names."""

        return self.request("kore.digest", kore=os.fspath(kore), semantics=os.fspath(semantics))["sha256"]

    def kore_attributes(self, kore: Path, labels: list[str], attributes: list[str]) -> dict[str, dict[str, str]]:
        """Read named string attributes of the named labels' KORE symbol declarations."""

        return self.request(
            "kore.attributes", kore=os.fspath(kore), labels=labels, attributes=attributes,
        )["symbols"]

    def kore_instances(self, kore: Path, labels: list[str]) -> dict[str, list[list[str]]]:
        """Read the sort instances at which a KORE definition's axioms apply each label's symbol."""

        return self.request("kore.instances", kore=os.fspath(kore), labels=labels)["instances"]

    def observe(self, state: str, cells: list[str]) -> dict[str, Any]:
        """Read canonical cell contents and collection sizes."""

        return self.request("observe", state=state, cells=cells)

    def expect(
        self, state: str, cell: str, *, text: str | None = None,
        size: int | None = None, head: str | None = None,
    ) -> dict[str, Any]:
        """Require a surface-text, size, or K-sequence-head expectation."""

        fields = {"text": text, "size": size, "head": head}
        selected = {name: value for name, value in fields.items() if value is not None}
        if len(selected) != 1:
            raise GateError("expect requires exactly one of text, size, or head")
        result = self.request("expect", state=state, cell=cell, **selected)
        if not result["met"]:
            raise GateError(
                f"gate expectation for <{cell}> failed: expected={result['expected']}, "
                f"actual={result['actual']}"
            )
        return result

    def prove(self, claim: str) -> dict[str, Any]:
        """Prove an opaque KORE claim and return the serialized result."""

        return self.request("prove", claim=claim)

    def exec_run(
        self, *, program: str | None = None, program_name: str | None = None,
        variables: Mapping[str, str] | None = None, depth: int | None = None, trace: bool = False,
        print_style: str | None = None,
    ) -> dict[str, Any]:
        """Run surface inputs through krs-exec, as `krs run` does, and return its `krs-exec/1` run report.

        With ``print_style="pretty"`` the report also carries ``printed``: the final state as `krs run`
        prints it (`krun --output pretty`), ``{"text": ..., "warnings": [...]}``.
        """

        fields: dict[str, Any] = {}
        if print_style is not None:
            fields["print"] = print_style
        return self.request(
            "exec.run", program=program, program_name=program_name,
            variables=dict(variables or {}), depth=depth, trace=trace, **fields,
        )

    def term_unparse(
        self, mode: str, *, program: str | None = None, program_name: str | None = None,
        sort: str | None = None, kore: str | None = None, color: bool = False,
    ) -> dict[str, Any]:
        """Print through the loaded definition's grammar (krs-unparse).

        ``mode="program"`` parses ``program`` at ``sort`` and prints it as `krs parse --output program`
        (`kast --output program`) does; ``mode="pretty"`` prints the KORE pattern ``kore`` as
        `krun --output pretty` does. Returns ``{"text": ..., "warnings": [...]}``.
        """

        fields = {
            key: value for key, value in {
                "program": program, "program_name": program_name, "sort": sort, "kore": kore,
            }.items() if value is not None
        }
        return self.request("term.unparse", mode=mode, color=color, **fields)

    def exec_search(
        self, *, program: str | None = None, program_name: str | None = None,
        variables: Mapping[str, str] | None = None, mode: str = "final",
        depth: int | None = None, max_solutions: int | None = None,
    ) -> dict[str, Any]:
        """Search surface inputs through krs-exec, as `krs search` does, and return its search report."""

        return self.request(
            "exec.search", program=program, program_name=program_name,
            variables=dict(variables or {}), mode=mode, depth=depth, max_solutions=max_solutions,
        )

    def exec_prove(self, claims: list[str] | None = None, *, depth: int | None = None) -> list[dict[str, Any]]:
        """Prove claims by label through krs-exec, as `krs prove` does, and return its proof reports."""

        return self.request("exec.prove", claims=list(claims or []), depth=depth)

    @staticmethod
    def _kast_input(value: Any = None, *, text: str | None = None, path: Path | None = None) -> dict[str, Any]:
        fields = {"value": value, "text": text, "path": os.fspath(path) if path is not None else None}
        selected = {key: child for key, child in fields.items() if child is not None}
        if len(selected) != 1:
            raise GateError("KAST input requires exactly one of value, text, or path")
        return selected

    def kast_normalize(
        self, variant: str, value: Any = None, *, text: str | None = None, path: Path | None = None,
        policy: Mapping[str, Any] | None = None, label: str | None = None, allow_prefix: bool = False,
    ) -> Any:
        """Normalize opaque evidence under an explicit Rust policy variant."""

        options: dict[str, Any] = {}
        if label is not None:
            options["label"] = label
        if allow_prefix:
            options["allow_prefix"] = True
        return self.request(
            "kast.normalize", variant=variant, policy=dict(policy or {}),
            **self._kast_input(value, text=text, path=path), **options,
        )

    def kast_project(
        self, reference: Mapping[str, Any], actual: Mapping[str, Any],
        reference_policy: Mapping[str, Any], actual_policy: Mapping[str, Any], *,
        compatible_sentence_pairs: list[Mapping[str, Any]] | None = None,
    ) -> dict[str, Any]:
        """Compare definition descriptors under the pin's two projection policies."""

        return self.request(
            "kast.project", reference=dict(reference), actual=dict(actual),
            reference_policy=dict(reference_policy), actual_policy=dict(actual_policy),
            compatible_sentence_pairs=compatible_sentence_pairs or [],
        )

    def kast_frontier(
        self, action: str, value: Any, *,
        returncode: int | None = None, stderr: str | None = None,
        constraint_labels: list[str] | tuple[str, ...] | None = None,
    ) -> Any:
        """Return proof classification and frontier, or a normalized search set."""

        fields = {
            key: child for key, child in {
                "returncode": returncode, "stderr": stderr, "constraint_labels": constraint_labels,
            }.items() if child is not None
        }
        return self.request("kast.frontier", action=action, value=value, **fields)

    def kast_inspect(
        self, action: str, value: Any = None, *, text: str | None = None, path: Path | None = None,
        policy: Mapping[str, Any] | None = None, label_map: Mapping[str, str] | None = None,
        name: str | None = None, if_complete: bool = False, head: str | None = None,
        allow_prefix: bool = False,
    ) -> Any:
        """Return generic term observations or facts for one definition module."""

        options = {
            key: child for key, child in {
                "policy": policy, "label_map": label_map, "name": name, "head": head,
            }.items() if child is not None
        }
        if if_complete:
            options["if_complete"] = True
        if allow_prefix:
            options["allow_prefix"] = True
        return self.request(
            "kast.inspect", action=action, **self._kast_input(value, text=text, path=path), **options,
        )
