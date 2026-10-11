"""The verdict of a conformance case, from the verdicts of its steps.

The driver (`run.py`) records a case's verdict and the ratchet (`ratchet.py`) ranks the case after
deleting the steps its exclusions name; both compute it here, so a case ranked without some of its
steps is ranked exactly as the driver would have ranked it had those steps not been run.
"""

from __future__ import annotations


# Outcomes from worst to best. `reference-error` is below every Rust outcome but is not evidence
# about Rust: the ratchet reports a change to or from it as an oracle change, never a regression.
RANK = {
    "reference-error": -1,
    "krust-error": 0,
    "mismatch": 1,
    "krust-unsupported": 2,
    "skipped-with-reason": 2,
    "match": 3,
}

# The verdict of a step recorded without one: the driver records every compared step's verdict,
# so a step without one was not compared.
UNRECORDED = "skipped-with-reason"


def step_verdict(step: dict) -> str:
    return step.get("verdict", UNRECORDED)


def case_verdict(steps: list[dict]) -> str | None:
    """The worst verdict among `steps` (the first of equal rank), or None when there is no step.

    A case passes only as far as every one of its steps does, so its verdict is the worst step
    verdict. With no step there is nothing to rank; the caller decides what that means.
    """
    verdicts = [step_verdict(step) for step in steps]
    return min(verdicts, key=RANK.__getitem__) if verdicts else None
