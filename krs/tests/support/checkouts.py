"""Verification of the pinned external checkouts under `../inspirations/`."""

from __future__ import annotations

from pathlib import Path

from support import GateError
from support.process import run


def git(checkout: Path, *arguments: str) -> str:
    """Run one Git command in `checkout` and return its stripped stdout."""

    return run(["git", "-C", checkout, *arguments], timeout=60).stdout.strip()


def git_revision(path: Path) -> str:
    return git(path, "rev-parse", "HEAD")


def verify_checkout(path: Path, revision: str, *, label: str, clean: bool = True) -> None:
    """Require `path` to be checked out at `revision` and, with `clean`, unmodified."""

    observed = git_revision(path)
    if observed != revision:
        raise GateError(f"{label} checkout revision differs: expected={revision}, observed={observed}")
    if clean and git(path, "status", "--porcelain"):
        raise GateError(f"{label} checkout is dirty: {path}")
