"""Verification of the pinned external checkouts under `../inspirations/`."""

from __future__ import annotations

from pathlib import Path

from support import GateError
from support.process import run


def git_revision(path: Path) -> str:
    return run(["git", "-C", path, "rev-parse", "HEAD"], timeout=30).stdout.strip()


def verify_checkout(path: Path, revision: str, *, label: str, clean: bool = True) -> None:
    """Require `path` to be checked out at `revision` and, with `clean`, unmodified."""

    observed = git_revision(path)
    if observed != revision:
        raise GateError(f"{label} checkout revision differs: expected={revision}, observed={observed}")
    if clean and run(["git", "-C", path, "status", "--porcelain"], timeout=30).stdout:
        raise GateError(f"{label} checkout is dirty: {path}")
