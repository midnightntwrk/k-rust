#!/usr/bin/env python3
"""Check the hypothesis table of lean/README.md against the theorems and the Rust tests it names.

Usage: scripts/lean-hypotheses.py WORKSPACE THEOREMS_FILE

The table is the one ```toml fence under the heading "## Hypotheses and their Rust tests" of
WORKSPACE/lean/README.md; THEOREMS_FILE is the theorem list `krust-audit --theorems` wrote. Every
[[hypothesis]] entry must have the keys `theorem`, `hypothesis` and `meaning`, exactly one of
`rust_test` and `owed_by`, and optionally `note`; no other key. The check fails when

  * `theorem` is not in THEOREMS_FILE;
  * `rust_test` is not `<path> <test>`, where <path> is a relative path, without `..`, to a file of
    the workspace and the last `::` segment of <test> is declared as `fn <name>` in that file;
  * `owed_by` is not a ticket id such as `LT-05` (a test not yet written, owed by that ticket).

Exit status: 0 when every entry passes, 1 when one fails, 2 on a usage or format error.
"""

import re
import sys
import tomllib
from pathlib import Path, PurePosixPath

HEADING = "## Hypotheses and their Rust tests"
REQUIRED = {"theorem", "hypothesis", "meaning"}
OPTIONAL = {"rust_test", "owed_by", "note"}
TICKET = re.compile(r"[A-Z]+-[0-9]+")
TEST_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def hypothesis_table(readme: str) -> str:
    """The body of the first ```toml fence after HEADING, before the next heading."""
    _, found, rest = readme.partition("\n" + HEADING + "\n")
    if not found:
        raise ValueError(f"lean/README.md has no heading {HEADING!r}")
    section = re.split(r"\n#{1,2} ", rest, maxsplit=1)[0]
    fence = re.search(r"^```toml\n(.*?)^```$", section, re.MULTILINE | re.DOTALL)
    if fence is None:
        raise ValueError(f"lean/README.md has no ```toml fence under {HEADING!r}")
    return fence.group(1)


def check_rust_test(workspace: Path, value: str) -> str | None:
    """None when `value` names an existing test, else the reason it does not."""
    parts = value.split()
    if len(parts) != 2:
        return f"rust_test {value!r} is not '<path> <test>'"
    path, test = parts
    relative = PurePosixPath(path)
    if relative.is_absolute() or any(part in ("", ".", "..") for part in relative.parts):
        return f"rust_test path {path!r} is not a relative path inside the workspace"
    file = workspace / relative
    if not file.is_file():
        return f"rust_test file {path} does not exist"
    name = test.rsplit("::", 1)[-1]
    if not TEST_NAME.fullmatch(name):
        return f"rust_test {test!r} does not end in a function name"
    if not re.search(rf"\bfn\s+{re.escape(name)}\s*[(<]", file.read_text(encoding="utf-8")):
        return f"rust_test {test}: {path} declares no fn {name}"
    return None


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print(__doc__.strip().splitlines()[2], file=sys.stderr)
        return 2
    workspace = Path(argv[1])
    theorems = set(Path(argv[2]).read_text(encoding="utf-8").split())
    try:
        table = tomllib.loads(hypothesis_table((workspace / "lean/README.md").read_text("utf-8")))
    except (ValueError, tomllib.TOMLDecodeError) as error:
        print(f"lean-check: {error}", file=sys.stderr)
        return 2
    entries = table.get("hypothesis")
    if set(table) != {"hypothesis"} or not isinstance(entries, list) or not entries:
        print("lean-check: the hypothesis table must hold only [[hypothesis]] entries", file=sys.stderr)
        return 2

    failures = []
    for number, entry in enumerate(entries, start=1):
        label = f"lean/README.md hypothesis {number} ({entry.get('theorem', '?')}: {entry.get('hypothesis', '?')})"
        keys = set(entry)
        for key in sorted(REQUIRED - keys):
            failures.append(f"{label}: missing key {key}")
        for key in sorted(keys - REQUIRED - OPTIONAL):
            failures.append(f"{label}: unknown key {key}")
        if not all(isinstance(entry[key], str) for key in keys):
            failures.append(f"{label}: every value must be a string")
            continue
        if "theorem" in entry and entry["theorem"] not in theorems:
            failures.append(f"{label}: theorem {entry['theorem']} is not in lean/theorems.txt")
        match ("rust_test" in entry, "owed_by" in entry):
            case (True, True):
                failures.append(f"{label}: both rust_test and owed_by; a written test is not owed")
            case (False, False):
                failures.append(f"{label}: neither rust_test nor owed_by")
            case (True, False):
                reason = check_rust_test(workspace, entry["rust_test"])
                if reason is not None:
                    failures.append(f"{label}: {reason}")
            case (False, True):
                if not TICKET.fullmatch(entry["owed_by"]):
                    failures.append(f"{label}: owed_by {entry['owed_by']!r} is not a ticket id such as LT-05")

    for failure in failures:
        print(f"lean-check: {failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
