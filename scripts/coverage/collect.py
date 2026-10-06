"""Merge and export the raw profiles of scripts/coverage.sh runs.

usage: collect.py WORK SUITE [--per-test]

Reads WORK/list-SUITE.json (`cargo nextest list --message-format json`), the copied
WORK/bins/krust-SUITE, and the profiles below WORK/profiles/SUITE/BINARY/TEST that
scripts/coverage/runner.sh laid out. Writes WORK/export/SUITE.pickle:

- `binaries`: for each test binary of the suite, and the suite's krust, its path, package,
  kind and test count;
- `lines`: for each binary, {workspace-relative file: {line: execution count}} over the
  production lines of its llvm-cov export, unexecuted lines included (all of them for a
  binary that wrote no profile);
- `tests` (with --per-test): for each (binary id, test name), the production lines that the
  test's processes executed, as (file, sorted line array) pairs;
- `problems`: profiles whose binary is unknown and merges or exports that failed.

Profiles are grouped by the binary ID that each one records, because one test directory holds
the profiles of the test binary and of every krust it started.
"""

import array
import collections
import glob
import json
import multiprocessing
import os
import pickle
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from source import Workspace  # noqa: E402

IGNORE = r"--ignore-filename-regex=(/\.cargo/|/rustc/|/nix/store/|/rustlib/|^/usr/)"
LLVM = os.environ["COVERAGE_LLVM_TOOLS"]
ROOT = os.environ["COVERAGE_WORKSPACE"]
JOBS = int(os.environ.get("COVERAGE_JOBS", "8"))
WORKSPACE = Workspace(ROOT)


def build_id(path):
    out = subprocess.run(["readelf", "-n", path], capture_output=True, text=True).stdout
    match = re.search(r"Build ID: ([0-9a-f]+)", out)
    return match.group(1) if match else None


def profile_binary_id(path):
    out = subprocess.run(
        [f"{LLVM}/llvm-profdata", "show", "--binary-ids", path], capture_output=True, text=True
    ).stdout
    ids = out.split("Binary IDs:")[-1].split()
    return path, (ids[0] if ids else None)


def production_lines(lcov_text, hits_only):
    """{rel: {line: count}} (or {rel: set of lines} when hits_only) over production lines."""
    out = {}
    current = None
    mask = None
    prefix = ROOT.rstrip("/") + "/"
    for line in lcov_text.splitlines():
        if line.startswith("SF:"):
            path = line[3:]
            rel = path[len(prefix) :] if path.startswith(prefix) else None
            mask = WORKSPACE.test_mask(rel) if rel and rel.startswith("crates/") else None
            if mask is None:
                current = None
            else:
                current = out.setdefault(rel, set() if hits_only else {})
        elif current is not None and line.startswith("DA:"):
            number, count = line[3:].split(",")[:2]
            number = int(number)
            if number in mask:
                continue
            count = int(count)
            if hits_only:
                if count > 0:
                    current.add(number)
            else:
                current[number] = current.get(number, 0) + count
    return out


def export(profdata, objects, hits_only):
    command = [f"{LLVM}/llvm-cov", "export", "-format=lcov", "-skip-functions", f"-instr-profile={profdata}"]
    command += [objects[0]] + [f"-object={o}" for o in objects[1:]] + [IGNORE]
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode:
        return None, result.stderr.strip()[:400]
    return production_lines(result.stdout, hits_only), None


def merge(inputs, output):
    listing = output + ".inputs"
    with open(listing, "w") as handle:
        handle.write("\n".join(inputs) + "\n")
    result = subprocess.run(
        [f"{LLVM}/llvm-profdata", "merge", "-sparse", f"--input-files={listing}", "-o", output],
        capture_output=True,
        text=True,
    )
    os.remove(listing)
    return None if result.returncode == 0 else result.stderr.strip()[:400]


def empty_profile(directory):
    """Profile data with no records, against which a binary exports with every count zero."""
    text = os.path.join(directory, "empty.proftext")
    with open(text, "w") as handle:
        handle.write(":ir\n")
    profdata = os.path.join(directory, "empty.profdata")
    subprocess.run([f"{LLVM}/llvm-profdata", "merge", "-sparse", text, "-o", profdata], check=True)
    return profdata


def binary_work(task):
    key, path, inputs, directory = task
    if inputs:
        profdata = os.path.join(directory, f"{key}.profdata")
        error = merge(inputs, profdata)
        if error:
            return key, None, f"merge of {key} failed: {error}"
    else:
        profdata = os.path.join(directory, "empty.profdata")
    lines, error = export(profdata, [path], hits_only=False)
    if error and not inputs and "no coverage data found" in error:
        # A test binary whose tests are all compiled out, as `#![cfg(feature = "cli")]` files
        # are in the portable build, has no instrumented code of its own.
        return key, {}, None
    return key, lines, (f"export of {key} failed: {error}" if error else None)


def test_work(task):
    key, objects, inputs, directory = task
    profdata = os.path.join(directory, f"{os.getpid()}.profdata")
    error = merge(inputs, profdata)
    if error:
        return key, None, f"merge for {key} failed: {error}"
    lines, error = export(profdata, objects, hits_only=True)
    os.remove(profdata)
    if error:
        return key, None, f"export for {key} failed: {error}"
    return key, [(rel, array.array("i", sorted(found))) for rel, found in lines.items() if found], None


def main():
    work, suite = sys.argv[1], sys.argv[2]
    per_test = "--per-test" in sys.argv[3:]
    with open(os.path.join(work, f"list-{suite}.json")) as handle:
        listing = json.load(handle)

    binaries = {}  # build id -> description
    by_basename = {}
    for entry in listing["rust-suites"].values():
        path = entry["binary-path"]
        description = {
            "path": path,
            "binary_id": entry["binary-id"],
            "package": entry["package-name"],
            "kind": entry["kind"],
            "tests": len(entry.get("testcases", {})),
        }
        by_basename[os.path.basename(path)] = description
        identity = build_id(path)
        if identity:
            binaries[identity] = description
    krust = os.path.join(work, "bins", f"krust-{suite}")
    if os.path.exists(krust):
        binaries[build_id(krust)] = {"path": krust, "binary_id": "krust", "package": "k-rust", "kind": "krust", "tests": 0}

    profiles = [
        path
        for path in glob.glob(os.path.join(work, "profiles", suite, "*", "*", "*.profraw"))
        if os.path.basename(os.path.dirname(os.path.dirname(path))) != "_other"
    ]
    problems = []
    with multiprocessing.get_context("fork").Pool(JOBS) as pool:
        identity_of = dict(pool.imap_unordered(profile_binary_id, profiles, chunksize=16))

        groups = collections.defaultdict(list)
        for path, identity in identity_of.items():
            if identity in binaries:
                groups[identity].append(path)
            else:
                problems.append(f"profile from an unknown binary ({identity}): {path}")
        directory = os.path.join(work, "export", suite)
        os.makedirs(directory, exist_ok=True)
        # A binary that ran no test, such as a test harness without tests, still counts its
        # lines as unexecuted.
        empty_profile(directory)
        tasks = [(identity, d["path"], groups.get(identity, []), directory) for identity, d in binaries.items()]
        lines = {}
        for identity, found, error in pool.imap_unordered(binary_work, tasks):
            if error:
                problems.append(error)
            if found is not None:
                lines[binaries[identity]["binary_id"]] = found
        print(f"{suite}: {len(profiles)} profiles from {len(groups)} of {len(binaries)} binaries", flush=True)

        tests = {}
        if per_test:
            by_test = collections.defaultdict(list)
            for path, identity in identity_of.items():
                if identity in binaries:
                    test_directory = os.path.dirname(path)
                    by_test[test_directory].append((path, identity))
            tasks = []
            for test_directory, files in by_test.items():
                basename = os.path.basename(os.path.dirname(test_directory))
                owner = by_basename.get(basename)
                if owner is None:
                    problems.append(f"profiles of an unlisted test binary: {test_directory}")
                    continue
                key = (owner["binary_id"], os.path.basename(test_directory))
                objects = sorted({binaries[identity]["path"] for _, identity in files})
                objects.sort(key=lambda path: path != owner["path"])
                tasks.append((key, objects, [path for path, _ in files], directory))
            for done, (key, found, error) in enumerate(pool.imap_unordered(test_work, tasks, chunksize=4), 1):
                if error:
                    problems.append(error)
                if found is not None:
                    tests[key] = found
                if done % 500 == 0:
                    print(f"{suite}: {done}/{len(tasks)} tests exported", flush=True)

    described = {d["binary_id"]: d for d in binaries.values() if d["binary_id"] in lines}
    with open(os.path.join(work, "export", f"{suite}.pickle"), "wb") as handle:
        pickle.dump({"binaries": described, "lines": lines, "tests": tests, "problems": problems}, handle)
    for problem in problems[:20]:
        print(f"{suite}: {problem}", file=sys.stderr)
    if len(problems) > 20:
        print(f"{suite}: {len(problems) - 20} more problems", file=sys.stderr)


if __name__ == "__main__":
    main()
