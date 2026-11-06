#!/usr/bin/env python3
"""Record the krs command outputs that pages show, and check that they are current.

`recorded-outputs.toml` lists each recorded command. `--write` runs every entry
from its fixture directory and writes `src/snippets/outputs/<id>.txt` and the
lock of input and output digests. With no option, the script recomputes the
digests without running krs and fails when a fixture, a manifest entry, or an
output changed since the last `--write`. `--verify` runs every entry again and
compares the outputs byte for byte.

An entry with `show = "PATH"` (relative to its fixture) also records the file the
command wrote there, after a `$ cat PATH` line, so a page can show a generated
artifact such as the `definition.k` that `krs emit-k --output DIRECTORY` writes.

An entry with `select = "MEMBER"` records only that member of the one JSON object
the command prints on stdout, indented by two spaces, after a command line that
names it (`# the document's "MEMBER"`); stderr and the exit status follow as for
any entry. It is for a document whose other members are not functions of the
fixture, such as `krs kink check`'s, whose `k_rust_revision` names k-rust's build:
the recording fails when stdout is not such an object, or when the member's text
holds the repository's absolute path. A member may be a dotted path into nested
objects (`template.last_run.mutation`), and `select` may list several: the
recording then shows one object holding each listed path's value under the path,
in the listed order, after a command line that names them all.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys
import tomllib

SITE = Path(__file__).resolve().parents[1]
REPOSITORY = SITE.parent
MANIFEST = SITE / "recorded-outputs.toml"
OUTPUTS = SITE / "src" / "snippets" / "outputs"
LOCK = OUTPUTS / "outputs.lock.json"

sys.path.insert(0, str(REPOSITORY / "krs" / "tests"))
from support import GateError  # noqa: E402
from support.krs import build  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import z3_environment  # noqa: E402


def entries() -> list[dict]:
    outputs = tomllib.loads(MANIFEST.read_text(encoding="utf-8")).get("output", [])
    ids = [entry["id"] for entry in outputs]
    if len(set(ids)) != len(ids):
        raise GateError(f"{MANIFEST.name}: duplicate output ids")
    return outputs


def arguments(entry: dict) -> list[str]:
    command, *extra = entry["args"]
    return [command, "--package", entry["package"], "--definition", entry["definition"], *extra]


def fixture_files(directory: Path) -> list[Path]:
    """The fixture's tracked and untracked files that Git does not ignore."""

    listed = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", directory],
        cwd=REPOSITORY, check=True, capture_output=True,
    ).stdout.split(b"\0")
    return sorted(REPOSITORY / name.decode() for name in listed if name and (REPOSITORY / name.decode()).is_file())


def input_digest(entry: dict) -> str:
    digest = hashlib.sha256(json.dumps(entry, sort_keys=True).encode())
    directory = SITE / entry["fixture"]
    for path in fixture_files(directory):
        digest.update(path.relative_to(REPOSITORY).as_posix().encode() + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    return digest.hexdigest()


def record(binary: Path, entry: dict) -> str:
    executed = run(
        [binary, *arguments(entry)],
        cwd=SITE / entry["fixture"],
        environment={**z3_environment(), "NO_COLOR": "1"},
        check=False,
    )
    command = "$ " + shlex.join(["krs", *arguments(entry)])
    if "select" in entry:
        members = entry["select"] if isinstance(entry["select"], list) else [entry["select"]]
        named = ", ".join(json.dumps(member) for member in members)
        text = command + f"  # the document's {named}\n" + selected(entry, executed.stdout) + executed.stderr
    else:
        text = command + "\n" + executed.stdout + executed.stderr
    if executed.returncode != 0:
        text += f"exit status {executed.returncode}\n"
    elif "show" in entry:
        shown = SITE / entry["fixture"] / entry["show"]
        text += "$ " + shlex.join(["cat", entry["show"]]) + "\n" + shown.read_text(encoding="utf-8")
    return text


def member_value(entry: dict, document: object, member: str) -> object:
    """The value at the dotted path `member` of `document`."""

    value = document
    for key in member.split("."):
        if not isinstance(value, dict) or key not in value:
            raise GateError(f"output {entry['id']}: stdout is not a JSON object with the member {member!r}")
        value = value[key]
    return value


def selected(entry: dict, stdout: str) -> str:
    """The `select` member (or members) of the one JSON object `stdout` holds, as the recording
    shows it."""

    try:
        document = json.loads(stdout)
    except json.JSONDecodeError as error:
        raise GateError(f"output {entry['id']}: stdout is not one JSON document ({error}), so `select` cannot apply") from None
    if isinstance(entry["select"], list):
        shown = {member: member_value(entry, document, member) for member in entry["select"]}
    else:
        shown = member_value(entry, document, entry["select"])
    text = json.dumps(shown, indent=2, ensure_ascii=False) + "\n"
    if str(REPOSITORY) in text:
        raise GateError(f"output {entry['id']}: the selection {entry['select']!r} holds the checkout path {REPOSITORY}, "
                        "which is not a function of the fixture")
    return text


def output_path(entry: dict) -> Path:
    return OUTPUTS / f"{entry['id']}.txt"


def main() -> int:
    mode = sys.argv[1] if len(sys.argv) > 1 else "--check"
    if mode not in ("--check", "--write", "--verify"):
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} [--check | --write | --verify]")
    outputs = entries()
    lock = json.loads(LOCK.read_text(encoding="utf-8")) if LOCK.is_file() else {}
    if mode == "--check":
        stale = []
        for entry in outputs:
            path = output_path(entry)
            recorded = lock.get(entry["id"], {})
            if (
                not path.is_file()
                or recorded.get("inputs") != input_digest(entry)
                or recorded.get("output") != hashlib.sha256(path.read_bytes()).hexdigest()
            ):
                stale.append(entry["id"])
        if stale or set(lock) != {entry["id"] for entry in outputs}:
            names = ", ".join(stale) or "the lock lists other ids than the manifest"
            raise SystemExit(f"recorded outputs are stale: {names}; run python3 scripts/record-outputs.py --write")
        print(f"PASS recorded outputs: {len(outputs)} current")
        return 0
    binary = build()
    if mode == "--verify":
        differing = [entry["id"] for entry in outputs if record(binary, entry).encode() != output_path(entry).read_bytes()]
        if differing:
            raise SystemExit(f"recorded outputs differ from krs: {', '.join(differing)}; run python3 scripts/record-outputs.py --write")
        print(f"PASS recorded outputs: {len(outputs)} reproduced by krs")
        return 0
    OUTPUTS.mkdir(parents=True, exist_ok=True)
    lock = {}
    for entry in outputs:
        path = output_path(entry)
        path.write_text(record(binary, entry), encoding="utf-8")
        lock[entry["id"]] = {"inputs": input_digest(entry), "output": hashlib.sha256(path.read_bytes()).hexdigest()}
        print(f"updated {path.relative_to(SITE)}")
    LOCK.write_text(json.dumps(lock, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
