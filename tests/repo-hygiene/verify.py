#!/usr/bin/env python3
"""Fail when the tracked tree depends on local-only notes.

`draft/` holds untracked, machine-local working notes, and the former root
tracking ledgers now live there. A tracked file must not reference either,
because a fresh clone contains neither. The check reads the Git index, so it
covers staged additions and ignores untracked files.

    PYTHONDONTWRITEBYTECODE=1 python3 tests/repo-hygiene/verify.py
"""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SELF = Path(__file__).resolve().relative_to(ROOT).as_posix()

# A `draft/` path segment (not, for example, the npm scope `@open-draft/`),
# or a quoted "draft" component joined into a path in code.
DRAFT_PATH = re.compile(r"""(?:^|[^A-Za-z0-9_@-])draft/|["']draft["']\s*[/,)]""")
REMOVED_LEDGERS = re.compile(
    r"K_RUST_HANDOFF|K_RUST_UPSTREAM|K_RUST_MORE_SEMANTICS_REQUESTS|"
    r"MIR_SEMANTICS_UPSTREAM|RECOVERY_AUDIT|LAST_KNOWN_PROMPT|RECOVERY_PROVENANCE"
)
# Paths inside the browser-lessons spikes and review evidence, which also live in draft/.
SPIKE_PATH = re.compile(r"spikes/(?:BL|IR)-[0-9]")


def tracked_files() -> list[str]:
    output = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "-z"],
        check=True,
        capture_output=True,
    ).stdout
    return [name for name in output.decode("utf-8").split("\0") if name]


def main() -> int:
    problems: list[str] = []
    for relative in tracked_files():
        if relative == "draft" or relative.startswith("draft/"):
            problems.append(f"{relative}: tracked file under draft/")
            continue
        if relative == SELF:
            continue
        path = ROOT / relative
        if not path.is_file():
            continue
        data = path.read_bytes()
        if b"\0" in data:
            continue
        text = data.decode("utf-8", errors="replace")
        for number, line in enumerate(text.splitlines(), start=1):
            for pattern, what in (
                (DRAFT_PATH, "references draft/"),
                (REMOVED_LEDGERS, "references a removed root ledger"),
                (SPIKE_PATH, "references a local-only spike path"),
            ):
                match = pattern.search(line)
                if match:
                    problems.append(f"{relative}:{number}: {what}: {line.strip()[:160]}")
    if problems:
        for problem in problems:
            print(problem, file=sys.stderr)
        print(f"FAIL repository hygiene: {len(problems)} finding(s)", file=sys.stderr)
        return 1
    print("PASS repository hygiene: no tracked file depends on draft/, a removed root ledger, or a spike path")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
