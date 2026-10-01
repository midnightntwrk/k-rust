"""Extract typed KRS and Cargo diagnostics from mixed JSON line streams.

KRS invocations whose stderr is parsed here must pass `--message-format=json`.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import json
from pathlib import Path
import re

from support import GateError


def envelopes(stderr: str | bytes) -> list[dict]:
    """Return each line that parses as a JSON object, in stream order."""

    found: list[dict] = []
    for line in stderr.splitlines():
        try:
            value = json.loads(line)
        except (json.JSONDecodeError, UnicodeDecodeError):
            continue
        if isinstance(value, dict):
            found.append(value)
    return found


@dataclass(frozen=True)
class AuthoredRange:
    cargo_name: str
    package_relative_path: str
    content_sha256: str
    start_byte: int
    end_byte: int

    def __post_init__(self) -> None:
        if not all(isinstance(value, str) for value in (
            self.cargo_name, self.package_relative_path, self.content_sha256
        )):
            raise GateError("authored range identity must contain strings")
        if not self.cargo_name:
            raise GateError("authored range cargo_name must be nonempty")
        if re.fullmatch(r"[0-9a-f]{64}", self.content_sha256) is None:
            raise GateError("authored range content_sha256 must be lowercase SHA-256")
        parts = self.package_relative_path.split("/")
        if (not self.package_relative_path or self.package_relative_path.startswith("/")
                or any(part in ("", ".", "..") for part in parts)
                or "\\" in self.package_relative_path or ":" in parts[0]):
            raise GateError("authored range path must be package-relative and normalized")
        if not isinstance(self.start_byte, int) or isinstance(self.start_byte, bool):
            raise GateError("authored range start_byte must be an integer")
        if not isinstance(self.end_byte, int) or isinstance(self.end_byte, bool):
            raise GateError("authored range end_byte must be an integer")
        if not 0 <= self.start_byte <= self.end_byte:
            raise GateError("authored range byte offsets are invalid")

    def selected_bytes(self, package_root: Path) -> bytes:
        """Return the exact authored byte slice within the package source file."""

        data = (package_root / self.package_relative_path).read_bytes()
        if self.end_byte > len(data):
            raise GateError("authored range exceeds the source file length")
        return data[self.start_byte:self.end_byte]


@dataclass(frozen=True)
class GeneratedRange:
    artifact: str
    start_line: int
    start_column: int
    end_line: int
    end_column: int


@dataclass(frozen=True)
class KrsDiagnostic:
    schema_version: int
    stage: str
    code: str
    severity: str
    message: str
    authored_range: AuthoredRange | None
    generated_range: GeneratedRange | None = None
    notes: tuple[str, ...] = ()
    raw_json: str = field(default="", repr=False, compare=False)

    def selected_bytes(self, package_root: Path) -> bytes:
        """Return the authored byte slice, requiring an authored range."""

        if self.authored_range is None:
            raise GateError("KRS diagnostic has no authored range")
        return self.authored_range.selected_bytes(package_root)


def _object(value: object, label: str) -> dict:
    if not isinstance(value, dict):
        raise GateError(f"{label} must be a JSON object")
    return value


def _string(value: object, label: str) -> str:
    if not isinstance(value, str):
        raise GateError(f"{label} must be a string")
    return value


def _integer(value: object, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise GateError(f"{label} must be an integer")
    return value


def _required(value: dict, key: str, label: str) -> object:
    if key not in value:
        raise GateError(f"{label} is missing {key}")
    return value[key]


def _authored_range(value: object) -> AuthoredRange | None:
    if value is None:
        return None
    source_range = _object(value, "authored_range")
    file = _object(_required(source_range, "file", "authored_range"), "authored_range.file")
    package = _object(_required(file, "package", "authored_range.file"), "authored_range.file.package")
    for key in ("k_namespace", "cargo_version", "cargo_source"):
        component = _string(_required(package, key, "authored_range.file.package"), f"authored_range.file.package.{key}")
        if not component:
            raise GateError(f"authored_range.file.package.{key} must be nonempty")
    return AuthoredRange(
        _string(_required(package, "cargo_name", "authored_range.file.package"), "authored_range.file.package.cargo_name"),
        _string(_required(file, "package_relative_path", "authored_range.file"), "authored_range.file.package_relative_path"),
        _string(_required(file, "content_sha256", "authored_range.file"), "authored_range.file.content_sha256"),
        _integer(_required(source_range, "start_byte", "authored_range"), "authored_range.start_byte"),
        _integer(_required(source_range, "end_byte", "authored_range"), "authored_range.end_byte"),
    )


def _generated_range(value: object) -> GeneratedRange | None:
    if value is None:
        return None
    generated = _object(value, "generated_range")
    return GeneratedRange(
        _string(_required(generated, "artifact", "generated_range"), "generated_range.artifact"),
        *(_integer(_required(generated, key, "generated_range"), f"generated_range.{key}")
          for key in ("start_line", "start_column", "end_line", "end_column")),
    )


def krs_diagnostics(stderr: str | bytes) -> list[KrsDiagnostic]:
    """Parse KRS envelopes in stream order.

    A JSON object is KRS-shaped when it has either `schema_version` or `stage`.
    Cargo objects bearing `reason` are skipped. A partial KRS-shaped object is
    malformed and fails the gate.
    """

    found = []
    for value in envelopes(stderr):
        if "reason" in value or not ("schema_version" in value or "stage" in value):
            continue
        version = _integer(_required(value, "schema_version", "KRS diagnostic"), "schema_version")
        if version != 1:
            raise GateError(f"unsupported KRS diagnostic schema_version {version}")
        stage = _string(_required(value, "stage", "KRS diagnostic"), "stage")
        if stage not in ("rust-expansion", "analysis", "k-frontend", "native"):
            raise GateError(f"unknown KRS diagnostic stage {stage!r}")
        severity = _string(_required(value, "severity", "KRS diagnostic"), "severity")
        if severity not in ("error", "warning"):
            raise GateError(f"unknown KRS diagnostic severity {severity!r}")
        notes = value.get("notes", [])
        if not isinstance(notes, list) or any(not isinstance(note, str) for note in notes):
            raise GateError("KRS diagnostic notes must be a list of strings")
        found.append(KrsDiagnostic(
            version,
            stage,
            _string(_required(value, "code", "KRS diagnostic"), "code"),
            severity,
            _string(_required(value, "message", "KRS diagnostic"), "message"),
            _authored_range(_required(value, "authored_range", "KRS diagnostic")),
            _generated_range(value.get("generated_range")),
            tuple(notes),
            json.dumps(value, sort_keys=True),
        ))
    return found


@dataclass(frozen=True)
class CargoPrimarySpan:
    message: str
    file_name: str
    byte_start: int
    byte_end: int
    line_start: int
    column_start: int
    column_end: int


def cargo_primary_span(
    stream: str | bytes, level: str = "error", *, message_contains: str | None = None
) -> CargoPrimarySpan:
    """Return the sole primary span.

    Without a text filter, inspect the first Cargo diagnostic at `level`.
    With a filter, gather primary spans across all matching diagnostics.
    """

    matching: list[tuple[str, dict]] = []
    for envelope in envelopes(stream):
        if envelope.get("reason") != "compiler-message":
            continue
        diagnostic = _object(_required(envelope, "message", "Cargo compiler-message"), "Cargo message")
        if diagnostic.get("level") != level:
            continue
        message = _string(_required(diagnostic, "message", "Cargo diagnostic"), "Cargo diagnostic message")
        if message_contains is None or message_contains in message:
            matching.append((message, diagnostic))
            if message_contains is None:
                break
    spans: list[CargoPrimarySpan] = []
    for message, diagnostic in matching:
        raw_spans = _required(diagnostic, "spans", "Cargo diagnostic")
        if not isinstance(raw_spans, list):
            raise GateError("Cargo diagnostic spans must be a list")
        for raw_span in raw_spans:
            span = _object(raw_span, "Cargo span")
            if span.get("is_primary") is not True:
                continue
            spans.append(CargoPrimarySpan(
                message,
                _string(_required(span, "file_name", "Cargo span"), "Cargo span file_name"),
                *(_integer(_required(span, key, "Cargo span"), f"Cargo span {key}")
                  for key in ("byte_start", "byte_end", "line_start", "column_start", "column_end")),
            ))
    if len(spans) != 1:
        raise GateError(f"expected one primary Cargo {level} span, got {len(spans)}")
    return spans[0]
