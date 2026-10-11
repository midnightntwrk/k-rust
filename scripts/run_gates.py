#!/usr/bin/env python3
"""The gate registry (scripts/gates.toml) and its runner; scripts/run-gates.sh is the entry point.

A gate is an executable entry, and asking for one is naming it: an unknown name fails before
anything runs. Entries are selected by name, by kind (--run), or by the paths a change touches
(--changed BASE..HEAD, --touched PATH), and each selected entry's command runs from the workspace
root under scripts/conformance/measure.py, which records its exit status, wall time and peak RSS.
The header of scripts/gates.toml defines the keys and kinds.
"""
import argparse
import getpass
import os
import re
import shlex
import subprocess
import sys
import time
import tomllib
from pathlib import Path

WORKSPACE = Path(__file__).resolve().parent.parent
REGISTRY = WORKSPACE / "scripts" / "gates.toml"
REGISTRY_PATH = "scripts/gates.toml"
MEASURE = WORKSPACE / "scripts" / "conformance" / "measure.py"

KINDS = ("certification", "heavy", "ci", "weekly", "on-demand")
# Kinds a change owes, and so must name the paths that owe them.
OWED_KINDS = ("certification", "heavy")
# Kinds selected by something other than a change: a schedule or a request.
UNOWED_KINDS = ("weekly", "on-demand")
HOSTS = ("human-uid",)
KEYS = {"name", "run", "command", "paths", "host"}
NAME = re.compile(r"[a-z0-9]+(-[a-z0-9]+)*")
SANDBOX_USER = re.compile(r"agent-[0-9]+")


class RegistryError(Exception):
    """The registry is malformed; the message lists every problem found."""


class Gate:
    def __init__(self, table, patterns):
        self.table = table
        self.name = table["name"]
        self.run = table["run"]
        self.command = table["command"]
        self.host = table.get("host")
        self.patterns = patterns

    def owed_by(self, paths):
        """The first of `paths` that one of this entry's patterns matches, or None."""
        for path in paths:
            if any(pattern.search(path) for pattern in self.patterns):
                return path
        return None


def parse(text):
    """The entries of a registry text, in order; raises RegistryError on any malformed part."""
    try:
        data = tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:
        raise RegistryError(f"not TOML: {error}") from None
    problems = []
    unknown = set(data) - {"path-set", "gate"}
    if unknown:
        problems.append(f"unknown top-level keys {sorted(unknown)}")
    sets = data.get("path-set", {})
    for set_name, patterns in sets.items():
        if not isinstance(patterns, list) or not all(isinstance(p, str) for p in patterns):
            problems.append(f"path-set {set_name} is not a list of strings")
    gates, names = [], set()
    for index, table in enumerate(data.get("gate", [])):
        name = table.get("name")
        label = name if isinstance(name, str) else f"#{index + 1}"
        if not isinstance(name, str) or not NAME.fullmatch(name):
            problems.append(f"gate {label}: name must be lowercase words joined by '-'")
        elif name in names:
            problems.append(f"gate {name}: name is not unique")
        names.add(name)
        if set(table) - KEYS:
            problems.append(f"gate {label}: unknown keys {sorted(set(table) - KEYS)}")
        for key in ("run", "command"):
            if not isinstance(table.get(key), str) or not table[key].strip():
                problems.append(f"gate {label}: `{key}` must be a non-empty string")
        run = table.get("run")
        if isinstance(run, str) and run not in KINDS:
            problems.append(f"gate {label}: run `{run}` is not one of {', '.join(KINDS)}")
        host = table.get("host")
        if host is not None and host not in HOSTS:
            problems.append(f"gate {label}: host `{host}` is not one of {', '.join(HOSTS)}")
        raw = table.get("paths")
        if raw is not None and (not isinstance(raw, list) or not all(isinstance(p, str) for p in raw)):
            problems.append(f"gate {label}: `paths` must be a list of strings")
            raw = None
        if run in OWED_KINDS and not raw:
            problems.append(f"gate {label}: a {run} entry needs `paths`, the changes that owe it")
        if run in UNOWED_KINDS and raw is not None:
            problems.append(f"gate {label}: a {run} entry is not owed by a change, so it has no `paths`")
        patterns = []
        for item in raw or []:
            expanded = [item]
            if item.startswith("@"):
                expanded = sets.get(item[1:])
                if not isinstance(expanded, list):
                    problems.append(f"gate {label}: no path-set `{item[1:]}`")
                    continue
            for pattern in expanded:
                try:
                    patterns.append(re.compile(pattern))
                except re.error as error:
                    problems.append(f"gate {label}: pattern {pattern!r}: {error}")
        gates.append(Gate(table, patterns))
    if problems:
        raise RegistryError("\n".join(problems))
    return gates


def load(path):
    return parse(Path(path).read_text())


def git(*args):
    return subprocess.run(["git", "-C", str(WORKSPACE), *args], check=True, text=True,
                          capture_output=True).stdout


def changed_paths(base, head):
    """Every path a commit after the merge base of BASE and HEAD added, edited or deleted (a
    rename counts as both its paths), and the names of the registry entries whose own table
    differs between the merge base and HEAD."""
    merge_base = git("merge-base", base, head).strip()
    paths = git("diff", "--name-only", "--no-renames", merge_base, head).splitlines()
    changed_entries = set()
    if REGISTRY_PATH in paths:
        try:
            before = {gate.name: gate.table for gate in parse(git("show", f"{merge_base}:{REGISTRY_PATH}"))}
        except (subprocess.CalledProcessError, RegistryError):
            before = {}
        after = parse(git("show", f"{head}:{REGISTRY_PATH}"))
        changed_entries = {gate.name for gate in after if before.get(gate.name) != gate.table}
    return paths, changed_entries


def select(gates, names=(), kinds=(), touched=None, changed_entries=()):
    """The selected entries in registry order, each with why it was selected.

    Named entries are always selected. Without `touched`, `kinds` selects every entry of those
    kinds. With `touched` (the paths a change touched), an entry is selected when one of its
    patterns matches a touched path or its own table changed, restricted to `kinds` when given.
    """
    by_name = {gate.name: gate for gate in gates}
    unknown = [name for name in names if name not in by_name]
    if unknown:
        raise KeyError(unknown)
    selected = []
    for gate in gates:
        if gate.name in names:
            selected.append((gate, "named"))
        elif touched is None:
            if gate.run in kinds:
                selected.append((gate, f"run = {gate.run}"))
        elif not kinds or gate.run in kinds:
            if gate.name in changed_entries:
                selected.append((gate, "its registry entry changed"))
            elif (path := gate.owed_by(touched)) is not None:
                selected.append((gate, f"touches {path}"))
    return selected


def check(gates):
    """Problems a valid registry still has against the workspace: a pattern that matches no
    tracked file (it owes its entry nothing), and a command whose program is not a tracked
    workspace file."""
    tracked = git("ls-files").splitlines()
    tracked_set = set(tracked)
    problems = []
    for gate in gates:
        for pattern in gate.patterns:
            if not any(pattern.search(path) for path in tracked):
                problems.append(f"gate {gate.name}: pattern {pattern.pattern!r} matches no tracked file")
        words = shlex.split(gate.command)
        program = next((w for w in words if not re.fullmatch(r"[A-Z_][A-Z0-9_]*=.*", w)), "")
        if program not in tracked_set:
            problems.append(f"gate {gate.name}: runs `{program}`, which is not a tracked workspace file")
    return problems


def describe(gate):
    host = f" host={gate.host}" if gate.host else ""
    return f"{gate.name}  run={gate.run}{host}\n    {gate.command}"


def in_sandbox():
    try:
        return SANDBOX_USER.fullmatch(getpass.getuser()) is not None
    except (KeyError, OSError):
        return False


def read_meta(path):
    try:
        return tomllib.loads(Path(path).read_text())
    except (OSError, tomllib.TOMLDecodeError):
        return {}


def tail(path, lines):
    try:
        return Path(path).read_text(errors="replace").splitlines()[-lines:]
    except OSError:
        return []


def toml_string(value):
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def run(selected, log_dir, extra_args, sandbox):
    log_dir.mkdir(parents=True, exist_ok=True)
    rows = []
    for gate, reason in selected:
        prefix = log_dir / gate.name
        if gate.host == "human-uid" and sandbox:
            print(f"[gates] {gate.name}: not run: needs a host-UID run ({reason})", flush=True)
            rows.append({"name": gate.name, "run": gate.run, "command": gate.command,
                         "status": "not-run", "reason": "needs a host-UID run"})
            continue
        print(f"[gates] {gate.name}: {gate.command} ({reason})", flush=True)
        command = gate.command + "".join(" " + shlex.quote(arg) for arg in extra_args)
        status = subprocess.run(
            [sys.executable, str(MEASURE), "--log", str(prefix), "--", "bash", "-c", command],
            cwd=WORKSPACE, stdin=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode
        meta = read_meta(f"{prefix}.meta.toml")
        wall, rss = meta.get("wall_seconds"), meta.get("peak_rss_mib")
        passed = status == 0
        for line in tail(f"{prefix}.stdout", 40 if passed else 80):
            print(f"    {line}")
        if not passed:
            for line in tail(f"{prefix}.stderr", 40):
                print(f"    stderr: {line}")
        print(f"[gates] {gate.name}: {'pass' if passed else f'FAIL (exit {status})'}, "
              f"wall {wall} s, peak RSS {rss} MiB; logs {prefix}.*", flush=True)
        rows.append({"name": gate.name, "run": gate.run, "command": command,
                     "status": "pass" if passed else "fail", "exit_code": status,
                     "wall_seconds": wall, "peak_rss_mib": rss})
    with open(log_dir / "summary.toml", "w") as summary:
        for row in rows:
            summary.write("[[entry]]\n")
            for key, value in row.items():
                if value is None:
                    continue
                summary.write(f"{key} = {toml_string(value) if isinstance(value, str) else value}\n")
            summary.write("\n")
    print(f"[gates] summary: {log_dir / 'summary.toml'}")
    for row in rows:
        measured = (f", wall {row['wall_seconds']} s, peak RSS {row['peak_rss_mib']} MiB"
                    if row["status"] != "not-run" else f" ({row['reason']})")
        print(f"  {row['name']}: {row['status']}{measured}")
    if any(row["status"] == "fail" for row in rows):
        return 1
    return 3 if any(row["status"] == "not-run" for row in rows) else 0


USAGE = """\
usage: scripts/run-gates.sh [--run KIND]... [--changed BASE..HEAD] [--touched PATH]...
                            [--list] [--log-dir DIR] [NAME...] [-- ARG...]
       scripts/run-gates.sh --check

Run the entries of scripts/gates.toml that are named, of a --run KIND (certification, heavy, ci,
weekly, on-demand), or owed by a change: --changed selects every entry with a pattern that
matches a path the commits after the merge base of BASE and HEAD touched, or whose own registry
table they changed; --touched PATH does the same for one path. With --changed or --touched,
--run restricts that selection to the given kinds. Named entries are always selected.
ARGs after `--` are appended to the command of the one selected entry.

Each entry runs from the workspace root under scripts/conformance/measure.py; its stdout, stderr
and meta.toml (exit code, wall time, peak RSS) go to --log-dir (default
target/gate-runs/<UTC time>), with a summary.toml of every entry. A host = "human-uid" entry is
not run as an agent-N user, and is listed as not run.

--list prints the selection (every entry when nothing is selected) without running it.
--check validates the registry against the workspace: every pattern matches a tracked file and
every command runs a tracked program.

Exit status: 0 when every selected entry passed (or nothing was owed), 1 when one failed, 3 when
none failed but one was not run for its host, 2 on a usage error, an unknown name or a
malformed registry."""


def main(argv):
    extra_args = []
    if "--" in argv:
        split = argv.index("--")
        argv, extra_args = argv[:split], argv[split + 1:]
    parser = argparse.ArgumentParser(add_help=False, usage=argparse.SUPPRESS)
    parser.add_argument("--run", action="append", default=[])
    parser.add_argument("--changed")
    parser.add_argument("--touched", action="append", default=[])
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--log-dir")
    parser.add_argument("--registry", default=str(REGISTRY))
    parser.add_argument("-h", "--help", action="store_true")
    parser.add_argument("names", nargs="*")
    try:
        args = parser.parse_args(argv)
    except SystemExit:
        print(USAGE, file=sys.stderr)
        return 2
    if args.help:
        print(USAGE)
        return 0
    try:
        gates = load(args.registry)
    except (OSError, RegistryError) as error:
        print(f"error: {args.registry}:\n{error}", file=sys.stderr)
        return 2
    if args.check:
        problems = check(gates)
        for problem in problems:
            print(f"error: {problem}", file=sys.stderr)
        if not problems:
            print(f"{len(gates)} entries; every pattern matches a tracked file and every command "
                  "runs a tracked program")
        return 1 if problems else 0
    bad_kinds = [kind for kind in args.run if kind not in KINDS]
    if bad_kinds:
        print(f"error: unknown --run kind {bad_kinds}; kinds: {', '.join(KINDS)}", file=sys.stderr)
        return 2
    touched, changed_entries = None, set()
    if args.changed is not None:
        base, dots, head = args.changed.partition("..")
        if not dots or not base or not head or head.startswith("."):
            print("error: --changed takes BASE..HEAD", file=sys.stderr)
            return 2
        try:
            touched, changed_entries = changed_paths(base, head)
        except subprocess.CalledProcessError as error:
            print(f"error: git: {error.stderr.strip()}", file=sys.stderr)
            return 2
    if args.touched:
        touched = (touched or []) + args.touched
    try:
        selected = select(gates, args.names, args.run, touched, changed_entries)
    except KeyError as error:
        print(f"error: unknown gate {', '.join(error.args[0])}; scripts/run-gates.sh --list "
              "names every entry", file=sys.stderr)
        return 2
    nothing_asked = not args.names and not args.run and touched is None
    if args.list:
        for gate, reason in ([(gate, "") for gate in gates] if nothing_asked else selected):
            print(describe(gate) + (f"\n    selected: {reason}" if reason else ""))
        return 0
    if nothing_asked:
        print("error: nothing selected: name an entry, or give --run, --changed or --touched\n",
              file=sys.stderr)
        print(USAGE, file=sys.stderr)
        return 2
    if extra_args and len(selected) != 1:
        print("error: arguments after `--` need exactly one selected entry", file=sys.stderr)
        return 2
    if not selected:
        print("[gates] no entry is selected: nothing is owed")
        return 0
    log_dir = Path(args.log_dir) if args.log_dir else (
        WORKSPACE / "target" / "gate-runs" / time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()))
    return run(selected, log_dir, extra_args, in_sandbox())


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
