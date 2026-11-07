#!/usr/bin/env python3
"""Fail when the tracked tree holds or cites a local scratchpad.

The `draft` and `draft-personal` directories (at the root and under `krs`) are
untracked scratchpads: a clone does not have them, and what they hold is work in
progress, not a decision the repository makes. So no tracked file lies in a
directory of either name, and no tracked text names a path inside one, as
authority, as provenance, or as a place a tool reads or writes. Committed text
states in words what such a note established instead.

The check reads the Git index, so it covers staged additions and ignores
untracked files. A line that must name a scratchpad path is listed in
`ALLOWED` with the reason it has to; an entry that no longer matches a line is
itself a finding, so the list cannot outlive what it excuses. `EXEMPT` lists
the check's own files, which spell what they look for.

    scripts/repo_hygiene.py
"""
import re
import subprocess
import sys
from pathlib import Path

WORKSPACE = Path(__file__).resolve().parent.parent

# The directory names that hold scratchpads.
SCRATCHPADS = ("draft", "draft-personal")
# A path segment naming a scratchpad: after a start of line or a separator that cannot be part
# of a longer name (so the npm scope `@open-draft` and a name such as `ajv-draft-04` do not
# match), or a quoted scratchpad name joined into a path in code.
SCRATCHPAD_PATH = re.compile(
    r"(?:^|[^A-Za-z0-9_.@-])draft(?:-personal)?[/]|[\"']draft(?:-personal)?[\"']\s*[/,)]"
)

# (path, the exact line with surrounding whitespace removed) -> why that line names a scratchpad.
IGNORE_RULE = "the ignore rule must name the directory it keeps out of the index"
ALLOWED = {
    (".gitignore", "/draft/"): IGNORE_RULE,
    (".gitignore", "/draft-personal/"): IGNORE_RULE,
    (".gitignore", "/krs/draft/"): IGNORE_RULE,
}
# Files exempt from the reference rule as a whole: the check and its tests spell the names and
# the ignore rules they look for. A tracked path in a scratchpad directory is refused even here.
EXEMPT = {
    "scripts/repo_hygiene.py": "spells the scratchpad names, the pattern and the allowed lines",
    "scripts/test_repo_hygiene.py": "seeds the references the check must refuse",
}


def tracked_files(root=WORKSPACE):
    output = subprocess.run(["git", "-C", str(root), "ls-files", "-z"], check=True,
                            capture_output=True).stdout
    return [name for name in output.decode("utf-8").split("\0") if name]


def path_problem(relative):
    """The finding for a tracked path inside a scratchpad directory, or None."""
    directories = relative.split("/")[:-1]
    for name in SCRATCHPADS:
        if name in directories:
            return f"{relative}: tracked file under a {name} directory, a local scratchpad"
    return None


def text_problems(relative, text, allowed, used):
    """The findings for the lines of `text` that name a scratchpad path and are not allowed;
    every allowed (path, line) key met is added to `used`."""
    problems = []
    for number, line in enumerate(text.splitlines(), start=1):
        if not SCRATCHPAD_PATH.search(line):
            continue
        key = (relative, line.strip())
        if key in allowed:
            used.add(key)
            continue
        problems.append(f"{relative}:{number}: names a scratchpad path: {line.strip()[:160]}")
    return problems


def problems(files, root=WORKSPACE, allowed=ALLOWED, exempt=EXEMPT):
    found, used = [], set()
    for relative in files:
        problem = path_problem(relative)
        if problem:
            found.append(problem)
            continue
        if relative in exempt:
            continue
        path = root / relative
        if not path.is_file() or path.is_symlink():
            continue
        data = path.read_bytes()
        if b"\0" in data:
            continue
        found.extend(text_problems(relative, data.decode("utf-8", errors="replace"), allowed, used))
    for key in sorted(set(allowed) - used):
        found.append(f"{key[0]}: allowed line {key[1]!r} no longer occurs; "
                     "remove its ALLOWED entry")
    for relative in sorted(set(exempt) - set(files)):
        found.append(f"{relative}: exempt file is not tracked; remove its EXEMPT entry")
    return found


def main():
    found = problems(tracked_files())
    if found:
        for problem in found:
            print(problem, file=sys.stderr)
        print(f"FAIL repository hygiene: {len(found)} finding(s); state in words what the "
              "scratchpad note established, or drop the reference", file=sys.stderr)
        return 1
    print("PASS repository hygiene: no tracked file lies in or names a local scratchpad")
    return 0


if __name__ == "__main__":
    sys.exit(main())
