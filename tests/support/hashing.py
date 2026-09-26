"""Digests the gates pin: files, text, canonical JSON, and artifact sets."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Sequence

from support import GateError


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(value: str) -> str:
    """SHA-256 of the UTF-8 encoding of `value`."""

    return sha256_bytes(value.encode("utf-8"))


def sha256_file(path: Path) -> str:
    if not path.is_file():
        raise GateError(f"required file is missing: {path}")
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_json(value: Any) -> str:
    """The one canonical JSON spelling every pinned JSON digest is taken over."""

    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def json_sha256(value: Any) -> str:
    return sha256_text(canonical_json(value))


def exact_directory(first: Path, second: Path, names: Sequence[str]) -> dict[str, str]:
    """Require two emissions to hold exactly `names`, byte for byte; return their digests."""

    expected = sorted(names)
    first_names = sorted(path.name for path in first.iterdir() if path.is_file())
    second_names = sorted(path.name for path in second.iterdir() if path.is_file())
    if first_names != expected or second_names != expected:
        raise GateError(
            f"artifact set differs: expected={expected}, first={first_names}, second={second_names}"
        )
    hashes = {name: sha256_file(first / name) for name in names}
    for name, digest in hashes.items():
        if sha256_file(second / name) != digest:
            raise GateError(f"repeated emission differs byte-for-byte: {name}")
    return hashes
