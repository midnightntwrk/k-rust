"""Loading the JSON and TOML ledgers a gate compares its observations against."""

from __future__ import annotations

import json
from pathlib import Path
import tomllib
from typing import Any, Mapping

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
