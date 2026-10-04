#!/usr/bin/env python3
"""Line-deletion reducer for one generative compile case.

Usage: reduce.py [--exe PATH] [--fresh] [--keep TEXT] INPUT.k OUTCOME [MESSAGE_SUBSTRING]

Greedily deletes lines of INPUT.k (never `module MAIN`, `endmodule`, or a line containing TEXT)
while `generative-compile case` still reports an outcome starting with OUTCOME whose message
contains MESSAGE_SUBSTRING, then prints the reduced definition. A run that prints no result line
counts as the outcome `crash`, one that exceeds 60 seconds as `timeout`. `--fresh` reloads the
prelude for every candidate, as `generative-compile case --fresh` does. The harness defaults to
the release example in the workspace's Cargo target directory, which scripts/generative-compile.sh
builds.
"""
import json
import os
import subprocess
import sys
import tempfile

WORKSPACE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def usage():
    print(__doc__.strip().splitlines()[2], file=sys.stderr)
    sys.exit(2)


def default_exe():
    metadata = subprocess.run(
        ["cargo", "metadata", "--no-deps", "--format-version", "1"],
        cwd=WORKSPACE, capture_output=True, text=True, check=True).stdout
    target = json.loads(metadata)["target_directory"]
    return os.path.join(target, "release", "examples", "generative-compile")


def main():
    args = sys.argv[1:]
    exe, fresh, keep = None, False, None
    positional = []
    while args:
        arg = args.pop(0)
        if arg == "--exe" and args:
            exe = args.pop(0)
        elif arg == "--keep" and args:
            keep = args.pop(0)
        elif arg == "--fresh":
            fresh = True
        elif arg.startswith("--"):
            usage()
        else:
            positional.append(arg)
    if len(positional) not in (2, 3):
        usage()
    path, want = positional[0], positional[1]
    needle = positional[2] if len(positional) == 3 else ""
    exe = exe or default_exe()

    def outcome(text):
        with tempfile.NamedTemporaryFile("w", suffix=".k", delete=False) as fh:
            fh.write(text)
            name = fh.name
        try:
            command = [exe, "case", name] + (["--fresh"] if fresh else [])
            out = subprocess.run(command, capture_output=True, text=True, timeout=60).stdout
        except subprocess.TimeoutExpired:
            return "timeout", ""
        finally:
            os.unlink(name)
        for line in out.splitlines():
            if line.startswith("RESULT\t"):
                fields = line.split("\t", 4)
                return fields[1], fields[4] if len(fields) > 4 else ""
        return "crash", ""

    def interesting(lines):
        cls, msg = outcome("\n".join(lines) + "\n")
        return cls.startswith(want) and needle in msg

    with open(path) as fh:
        lines = [line for line in fh.read().splitlines() if not line.startswith("//")]
    if not interesting(lines):
        sys.exit(f"{path} does not reproduce {want} {needle!r}: {outcome(chr(10).join(lines))}")
    changed = True
    while changed:
        changed = False
        i = 0
        while i < len(lines):
            fixed = lines[i].strip() in ("module MAIN", "endmodule")
            if fixed or (keep and keep in lines[i]):
                i += 1
                continue
            candidate = lines[:i] + lines[i + 1:]
            if interesting(candidate):
                lines = candidate
                changed = True
            else:
                i += 1
    print("\n".join(lines))


if __name__ == "__main__":
    main()
