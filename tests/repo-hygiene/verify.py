#!/usr/bin/env python3
"""Fail when the tracked tree depends on local-only notes or has a dead gate.

`draft/` holds untracked, machine-local working notes, and the former root
tracking ledgers now live there. A tracked file must not reference either,
because a fresh clone contains neither. For the same reason a tracked file
must not cite a local ticket id (`IR-nn`, `BL-nnn`, `CQ-nnn`); it states the
fact the ticket stood for instead. The check reads the Git index, so it covers
staged additions and ignores untracked files.

Every `tests/<gate>/` directory must also have an entry point: a `verify.py`,
or a `README.md` that states the command that runs it. A directory with
neither is a gate nobody can run, so its rot goes unnoticed.

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
# A path under a spikes directory: the tracked one was removed (git history is its
# archive) and the browser-lessons spikes live in draft/. The bracket keeps this
# pattern itself out of a plain text search for the path.
SPIKE_PATH = re.compile(r"\bspikes[/]")
# A local ticket id. The bracket keeps this pattern out of its own search.
LOCAL_TICKET_ID = re.compile(r"\b(?:IR|BL|CQ)[-][0-9]{2,3}\b")
# A shell command that runs a gate, as a gate README must state one.
RUN_COMMAND = re.compile(r"\b(?:python3|cargo|bun|node)\s+\S")


def tracked_files() -> list[str]:
    output = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "-z"],
        check=True,
        capture_output=True,
    ).stdout
    return [name for name in output.decode("utf-8").split("\0") if name]


def gate_entry_problems(files: list[str]) -> list[str]:
    tracked = set(files)
    gates = sorted(
        {
            parts[1]
            for parts in (name.split("/") for name in files)
            if parts[0] == "tests" and len(parts) > 2
        }
    )
    problems: list[str] = []
    for gate in gates:
        if f"tests/{gate}/verify.py" in tracked:
            continue
        readme = f"tests/{gate}/README.md"
        if readme in tracked and RUN_COMMAND.search((ROOT / readme).read_text(encoding="utf-8")):
            continue
        problems.append(
            f"tests/{gate}/: gate has neither a verify.py nor a README.md stating the command that runs it"
        )
    return problems


def main() -> int:
    files = tracked_files()
    problems = gate_entry_problems(files)
    for relative in files:
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
                (LOCAL_TICKET_ID, "cites a local ticket id"),
            ):
                match = pattern.search(line)
                if match:
                    problems.append(f"{relative}:{number}: {what}: {line.strip()[:160]}")
    if problems:
        for problem in problems:
            print(problem, file=sys.stderr)
        print(f"FAIL repository hygiene: {len(problems)} finding(s)", file=sys.stderr)
        return 1
    print(
        "PASS repository hygiene: no tracked file depends on draft/, a removed root ledger, "
        "a spike path, or a local ticket id, and every tests/ gate has an entry point"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
