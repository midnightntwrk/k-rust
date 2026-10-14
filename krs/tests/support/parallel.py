"""Bounded, order-preserving concurrency for independent gate commands."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import os
from typing import Callable, Generic, Iterable, Optional, TypeVar

from support import GateError


T = TypeVar("T")
R = TypeVar("R")

MAX_WORKERS = 32
"""The largest accepted worker count; one per core on the reference host."""


def worker_count(variable: str, default: int) -> int:
    """Read a worker count from `variable`, falling back to `default`.

    The value must be an integer from 1 to `MAX_WORKERS`; 1 runs every job
    serially on the calling thread.
    """

    raw = os.environ.get(variable)
    if raw is None:
        return default
    try:
        value = int(raw)
    except ValueError as error:
        raise GateError(f"{variable} must be an integer") from error
    if not 1 <= value <= MAX_WORKERS:
        raise GateError(f"{variable} must be between 1 and {MAX_WORKERS}")
    return value


def ordered_map(function: Callable[[T], R], values: Iterable[T], workers: int) -> list[R]:
    """Apply `function` to every value with at most `workers` concurrent calls.

    Results keep the order of `values`. When calls fail, the exception of the
    earliest failing value in that order is raised, whatever order the calls
    finished in, and jobs that have not started are cancelled.
    """

    values = list(values)
    if workers <= 1 or len(values) <= 1:
        return [function(value) for value in values]
    with ThreadPoolExecutor(max_workers=min(workers, len(values))) as executor:
        futures = [executor.submit(function, value) for value in values]
        try:
            return [future.result() for future in futures]
        except BaseException:
            executor.shutdown(wait=True, cancel_futures=True)
            raise


@dataclass(frozen=True)
class Outcome(Generic[R]):
    """The value a call returned, or the exception it raised."""

    value: Optional[R] = None
    error: Optional[Exception] = None

    def get(self) -> R:
        """Return the value, or raise the call's exception."""

        if self.error is not None:
            raise self.error
        return self.value  # type: ignore[return-value]


def settle(call: Callable[[], R]) -> Outcome[R]:
    """Run `call`, keeping an ordinary exception as its outcome instead of raising it."""

    try:
        return Outcome(value=call())
    except Exception as error:  # noqa: BLE001 - re-raised by Outcome.get
        return Outcome(error=error)


def settle_all(calls: Iterable[Callable[[], R]], workers: int) -> list[Outcome[R]]:
    """Run every call to completion with at most `workers` concurrent calls.

    Outcomes keep the order of `calls`. A caller that inspects them in that
    order reports the same first failure however the calls were scheduled.
    """

    return ordered_map(settle, calls, workers)
