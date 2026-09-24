"""The pin ledgers a gate compares its observations against, and `--record`.

A gate pins two kinds of values:

- inputs it does not control: external checkout revisions and file digests,
  and its corpus. It reads them with `Ledger.get` or `Ledger.table` and
  compares them itself; `--record` never rewrites them;
- outputs KRS produces: artifact, KORE, and behavior digests. It compares them
  through `Ledger.expect`. In check mode a difference fails the gate. In record
  mode the observation is kept, and `Ledger.finish` rewrites exactly the
  output pins that were observed, after the whole gate has passed.

Toolchain and schema versions are not repeated in a gate ledger; they come from
`Krs.lock` through `support.lock`. KRS source is never pinned: a source change
that leaves every output identical passes without a pin edit, and an intended
output change is re-recorded by running the gate with `--record`.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
import re
from typing import Any, Mapping, Sequence

from support import GateError


def load_json(path: Path) -> dict[str, Any]:
    """Load a file that must hold exactly one JSON object."""

    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise GateError(f"cannot load {path}: {error}") from error
    if not isinstance(value, dict):
        raise GateError(f"{path} must contain one JSON object")
    return value


def load_toml(path: Path) -> dict[str, Any]:
    # Imported here so the package stays importable by the Python 3.10
    # interpreter of the pinned pyk environment, which M4 uses for its oracles.
    import tomllib

    try:
        with path.open("rb") as stream:
            return tomllib.load(stream)
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise GateError(f"cannot load {path}: {error}") from error


def table(value: Any, name: str) -> Mapping[str, Any]:
    """Require one ledger entry to be a table (a JSON object or TOML table)."""

    if not isinstance(value, dict):
        raise GateError(f"{name} must be a table")
    return value


_BARE_KEY = re.compile(r"^[A-Za-z0-9_-]+$")


def _toml_key(key: str) -> str:
    return key if _BARE_KEY.match(key) else json.dumps(key, ensure_ascii=False)


def _toml_value(value: Any, name: str) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    if isinstance(value, list) and all(
        isinstance(item, (bool, int, str)) for item in value
    ):
        return "[" + ", ".join(_toml_value(item, name) for item in value) + "]"
    raise GateError(f"{name} holds a value the pin writer cannot spell: {value!r}")


def dump_toml(data: Mapping[str, Any]) -> str:
    """Spell a ledger of scalars, scalar lists, and nested tables as TOML."""

    sections: list[str] = []

    def emit(prefix: tuple[str, ...], current: Mapping[str, Any]) -> None:
        lines = [
            f"{_toml_key(key)} = {_toml_value(value, '.'.join((*prefix, key)))}"
            for key, value in current.items()
            if not isinstance(value, dict)
        ]
        if prefix:
            lines.insert(0, "[" + ".".join(_toml_key(part) for part in prefix) + "]")
        if lines:
            sections.append("\n".join(lines) + "\n")
        for key, value in current.items():
            if isinstance(value, dict):
                emit((*prefix, key), value)

    emit((), data)
    return "\n".join(sections)


def dump_json(data: Mapping[str, Any]) -> str:
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


_MISSING = object()


class Ledger:
    """One gate's pin file, opened in check mode or in record mode."""

    def __init__(self, path: Path, *, record: bool = False, artifacts_only: bool = False) -> None:
        """Open `path`; `artifacts_only` marks a run that skips the comparison layers.

        Such a run vouches only for artifacts identical to their pins, so it
        cannot record, and a difference directs the author to the full gate.
        """

        if record and artifacts_only:
            raise GateError("--record needs every layer and cannot be combined with --artifacts-only")
        self.path = path
        self.record = record
        self.artifacts_only = artifacts_only
        if path.suffix == ".toml":
            self.data = load_toml(path)
        elif path.suffix == ".json":
            self.data = load_json(path)
        else:
            raise GateError(f"unsupported pin ledger format: {path}")
        self._observed: dict[tuple[str, ...], Any] = {}

    def get(self, key: str, default: Any = None) -> Any:
        return self.data.get(key, default)

    def __getitem__(self, key: str) -> Any:
        return self.data[key]

    def table(self, key: str) -> Mapping[str, Any]:
        return table(self.data.get(key), f"{self.path.name} {key}")

    def _lookup(self, path: tuple[str, ...]) -> Any:
        current: Any = self.data
        for part in path:
            if not isinstance(current, dict) or part not in current:
                return _MISSING
            current = current[part]
        return current

    def expect(self, key: str | Sequence[str], observed: Any) -> None:
        """Compare one measured output with its pin, or keep it in record mode.

        The same output observed twice in one run (for example the behavior
        digest of two execution routes) must agree in both modes.
        """

        path = (key,) if isinstance(key, str) else tuple(key)
        name = ".".join(path)
        if path in self._observed:
            if self._observed[path] != observed:
                raise GateError(
                    f"{self.path.name} {name} was observed twice with different values: "
                    f"{json.dumps(self._observed[path], sort_keys=True)} and "
                    f"{json.dumps(observed, sort_keys=True)}"
                )
            return
        self._observed[path] = copy.deepcopy(observed)
        if self.record:
            return
        expected = self._lookup(path)
        if self.artifacts_only:
            advice = (
                "--artifacts-only vouches only for unchanged artifacts; "
                "run the full gate, and --record if the change is intended"
            )
        else:
            advice = "if the change is intended, run the gate with --record"
        if expected is _MISSING:
            missing = advice if self.artifacts_only else "run the gate with --record"
            raise GateError(f"{self.path.name} has no pin {name}; {missing}")
        if expected != observed:
            raise GateError(
                f"{self.path.name} {name} differs from its pin: "
                f"observed={json.dumps(observed, sort_keys=True)}; {advice}"
            )

    def write(self) -> list[str]:
        """Rewrite the observed output pins; return the names that changed."""

        if not self.record:
            raise GateError("only a record-mode ledger can be written")
        data = copy.deepcopy(self.data)
        changed: list[str] = []
        for path, value in self._observed.items():
            current = data
            for part in path[:-1]:
                current = current.setdefault(part, {})
                if not isinstance(current, dict):
                    raise GateError(f"{self.path.name} {'.'.join(path)} is not under a table")
            if current.get(path[-1], _MISSING) != value:
                current[path[-1]] = copy.deepcopy(value)
                changed.append(".".join(path))
        if changed:
            text = dump_toml(data) if self.path.suffix == ".toml" else dump_json(data)
            self.path.write_text(text, encoding="utf-8")
            self.data = data
        return changed

    def finish(self, label: str) -> None:
        """Write a record-mode ledger and report what changed; no-op in check mode.

        A gate calls this only after every step passed, so a failing run never
        leaves a partial record behind.
        """

        if not self.record:
            return
        changed = self.write()
        if changed:
            print(f"RECORDED {label}: {self.path.name} {', '.join(sorted(changed))}")
        else:
            print(f"RECORDED {label}: {self.path.name} already matched every observed output")
