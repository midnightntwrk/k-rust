"""Consistent status lines and failure tracking for Python gates."""

from __future__ import annotations


STATUSES = frozenset({"PASS", "FAIL", "SKIP", "UNAVAILABLE", "MATCH", "MISMATCH", "RECORDED"})
PASSING = frozenset({"PASS", "MATCH"})


class Results:
    """Print gate checks and retain whether a required check failed."""

    def __init__(self, *, width: int = 12) -> None:
        self.width = width
        self._failed = False

    @property
    def failed(self) -> bool:
        """Whether any required check has a non-passing status."""
        return self._failed

    def add(self, name: str, status: str, detail: str, *, required: bool = True) -> None:
        """Print one status line and record failure for required checks."""
        if status not in STATUSES:
            raise ValueError(f"unknown gate result status {status!r}")
        print(f"{status:{self.width}} {name}: {detail}")
        if required and status not in PASSING:
            self._failed = True
