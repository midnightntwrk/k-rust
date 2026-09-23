"""Digests the gates pin: files, text, canonical JSON, trees, and artifact sets."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Iterable, Sequence

from support import GateError
from support.process import run


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(value: str) -> str:
    """SHA-256 of the UTF-8 encoding of `value`."""

    return sha256_bytes(value.encode("utf-8"))


def sha256_file(path: Path) -> str:
    if not path.is_file():
        raise GateError(f"required file is missing: {path}")
    return sha256_bytes(path.read_bytes())


def canonical_json(value: Any) -> str:
    """The one canonical JSON spelling every pinned JSON digest is taken over."""

    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def json_sha256(value: Any) -> str:
    return sha256_text(canonical_json(value))


def relevant_untracked(paths: Iterable[str]) -> list[str]:
    """Drop interpreter-generated Python cache entries from an untracked listing."""

    return sorted(
        relative
        for relative in paths
        if "__pycache__" not in Path(relative).parts and Path(relative).suffix != ".pyc"
    )


def tracked_tree_sha256(checkout: Path, prefix: str, *, reject_untracked: bool = False) -> str:
    """Digest every Git-tracked file under `prefix` by path and content.

    With `reject_untracked`, an untracked file other than Python cache output
    fails the digest, because it could change a build of the tree.
    """

    listing = run(["git", "-C", checkout, "ls-files", prefix], timeout=60)
    paths = sorted(line for line in listing.stdout.splitlines() if line)
    if not paths:
        raise GateError(f"tracked tree is empty: {checkout}/{prefix}")
    if reject_untracked:
        others = run(["git", "-C", checkout, "ls-files", "--others", prefix], timeout=60)
        untracked = relevant_untracked(others.stdout.splitlines())
        if untracked:
            raise GateError(
                f"untracked files can affect pinned source tree {checkout}/{prefix}: {untracked}"
            )
    digest = hashlib.sha256()
    for relative in paths:
        digest.update(relative.encode())
        digest.update(b"\0")
        digest.update(sha256_file(checkout / relative).encode())
        digest.update(b"\n")
    return digest.hexdigest()


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
