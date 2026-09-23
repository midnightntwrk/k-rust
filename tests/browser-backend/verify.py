#!/usr/bin/env python3
"""Browser backend compatibility suite (IR-16).

Every case under cases/<id>/ is compiled by the wasip1-hosted fork compiler
(rustc.wasm of the IR-14 pack) and run, in Node WASI, headless Chromium, and
headless Firefox; each host's outcome must equal the case's recorded
expectation.

Expectations (cases/<id>/expected.json) are kept per fork revision. Each
comes from the native twin of that revision (x86_64 host, LLVM) with the
pack's rlibs, run under Node WASI; the fork commit is replaced by a
placeholder in compared text. Stock `rustc +stable` is a second, informative
reference; where it differs, both are recorded and the twin is authoritative.
A case whose status for the revision (case.toml expected_status, overridden
by fork_status) is `known-gap` or `limitation` also records the fork's
outcome: the host must reproduce it, and an outcome equal to the twin's
(`gap-closed`) fails until the expectation is changed on purpose.

  PYTHONDONTWRITEBYTECODE=1 python3 tests/browser-backend/verify.py --host {node,chromium,firefox,all}
      [--pack PACK_ROOT --fork-build FORK_BUILD] [--references] [--record]
      [--only B01-...,B06-...] [--out DIR] [--evidence DIR]

--pack selects the compiler under test (rustc.wasm, sysroot bundle, and
rlibs of one IR-14 pack); --fork-build supplies the twin of the same commit.
--host none with --references rebuilds only the reference records;
--record rewrites this revision's entry of every expected.json from a fresh
twin (and stable) run and, for gap cases, from the Node host's fork outcome.
"""

from __future__ import annotations

import argparse
import base64
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time
import tomllib
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CASES = HERE / "cases"
RUNNER = HERE / "runner"
DEFAULT_PACK = Path("/var/tmp/krs-ir14-pack-a/pack")
DEFAULT_FORK_BUILD = Path("/var/tmp/krs-browser-fork/R-k")
DEFAULT_FORK_SOURCE = ROOT.parent / "inspirations" / "AngelOnFira" / "rust-krs"
LOAD_MAX = 40.0
STEP_TIMEOUT_MS = 600_000
STABLE_DEPS = {"itoa": "=1.0.18", "serde": "=1.0.229", "serde_json": "=1.0.151", "sha2": "=0.10.9"}
HOSTS = ("node", "chromium", "firefox")


def log(message: str) -> None:
    print(f"[browser-backend] {message}", file=sys.stderr, flush=True)


def wait_for_load() -> str:
    while True:
        load = os.getloadavg()
        if load[0] <= LOAD_MAX:
            return " ".join(f"{value:.2f}" for value in load)
        log(f"1-minute load {load[0]:.1f} > {LOAD_MAX}; waiting")
        time.sleep(30)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(command: list[str], **kwargs: Any) -> None:
    log("$ " + " ".join(str(part) for part in command))
    subprocess.run(["nice", "-n", "10", *command], check=True, **kwargs)


# ---------------------------------------------------------------- suite.json

def blob(data: bytes) -> dict[str, str]:
    try:
        return {"utf8": data.decode("utf-8")}
    except UnicodeDecodeError:
        return {"base64": base64.b64encode(data).decode("ascii")}


def load_cases(only: list[str]) -> list[dict[str, Any]]:
    cases = []
    for directory in sorted(CASES.iterdir()):
        if not (directory / "case.toml").is_file():
            continue
        case = tomllib.loads((directory / "case.toml").read_text())
        if case["id"] != directory.name:
            raise SystemExit(f"{directory}: id {case['id']} differs from the directory name")
        if case.get("expected_status") not in ("pass", "known-gap", "limitation"):
            raise SystemExit(f"{directory}: expected_status must be pass, known-gap, or limitation")
        if only and case["id"] not in only:
            continue
        case["_dir"] = directory
        cases.append(case)
    return cases


def pack_section(pack_root: Path) -> dict[str, Any]:
    manifest = tomllib.loads((pack_root / "pack-manifest.toml").read_text())
    artifacts = [{"path": a["path"], "sha256": a["sha256"], "bytes": a["bytes"]} for a in manifest["artifact"]]
    by_path = {a["path"]: a for a in artifacts}
    direct = manifest["direct_rustc"]
    fork_flags = ["--sysroot", direct["sysroot"], *direct["extra_flags"]]
    for directory in direct["dependency_search_paths"]:
        fork_flags += ["-L", f"dependency=/pack/{directory}"]
    externs = {a["crate_name"]: a["path"] for a in manifest["artifact"] if a["role"] == "target-rlib"}
    return {
        "pack_id": manifest["pack_id"],
        "root": str(pack_root),
        "rustc_wasm": by_path[manifest["compiler"]["rustc_wasm"]],
        "sysroot_bundle": by_path[manifest["sysroot"]["bundle"]],
        "artifacts": artifacts,
        "sysroot_mount": manifest["sysroot"]["mount"],
        "fork_flags": fork_flags,
        # the BL-003 browser-rustc harness and browser/worker/src/pack-ir14.ts
        "fork_env": ["CLIF2WASM_OBJECT=1", "RIWL_TIMINGS=1"],
        "externs": externs,
        "_manifest": manifest,
    }


def suite_file(cases: list[dict[str, Any]], pack: dict[str, Any]) -> dict[str, Any]:
    out_cases = []
    for case in cases:
        directory: Path = case["_dir"]
        sources = {}
        for path in sorted(directory.glob("*.rs")):
            sources[f"/case/{path.name}"] = path.read_text()
        crates = []
        for crate in case.get("crate", []):
            if f"/case/{crate['src']}" not in sources:
                raise SystemExit(f"{case['id']}: missing source {crate['src']}")
            crates.append({
                "name": crate["name"],
                "src": f"/case/{crate['src']}",
                "type": crate["type"],
                "externs": crate.get("externs", []),
                "pack": crate.get("pack", []),
                "flags": crate.get("flags", []),
                "inspect": crate.get("inspect"),
            })
        runs = []
        for entry in case.get("run", []):
            vfs = {}
            if "vfs" in entry:
                root = directory / entry["vfs"]
                for path in sorted(p for p in root.rglob("*") if p.is_file()):
                    vfs["/" + path.relative_to(root).as_posix()] = blob(path.read_bytes())
            runs.append({
                "name": entry["name"],
                "bin": entry["bin"],
                "args": entry.get("args", []),
                "env": entry.get("env", []),
                "vfs": vfs,
                "timeout_ms": entry.get("timeout_ms", 0),
                "cancel": entry.get("cancel", False),
                "recompile_after": entry.get("recompile_after", False),
            })
        out_cases.append({
            "id": case["id"],
            "sources": sources,
            "opt_levels": case.get("opt_levels", [0, 2]),
            "crates": crates,
            "runs": runs,
            "last": case.get("last", False),
        })
    public_pack = {k: v for k, v in pack.items() if not k.startswith("_")}
    return {
        "schema": 1,
        "suite": "krs-browser-backend",
        "generated_by": "tests/browser-backend/verify.py",
        "pack": public_pack,
        "step_timeout_ms": STEP_TIMEOUT_MS,
        "cases": out_cases,
    }


# ---------------------------------------------------------------- normalization

COMMIT_PLACEHOLDER = "<fork-commit>"


def scrub(text: str, commit: str) -> str:
    """Replaces the fork commit (full and 9-character forms, as in /rustc/<commit>/ paths and -vV) with a placeholder."""
    return text.replace(commit, COMMIT_PLACEHOLDER).replace(commit[:9], COMMIT_PLACEHOLDER) if commit else text


def scrub_blob(value: dict[str, str], commit: str) -> dict[str, str]:
    return {"utf8": scrub(value["utf8"], commit)} if "utf8" in value else value


def normalize_variant(variant: dict[str, Any], commit: str) -> dict[str, Any]:
    """The compared form of one opt-level variant: no timings, trap texts, or artifact hashes."""
    compile_records = []
    for record in variant["compile"]:
        entry: dict[str, Any] = {"crate": record["crate"], "outcome": record["outcome"]}
        if record["outcome"] != "ok":
            # Error-exit behaviour (IR-26): an exit status with rustc's summary line, or a trap.
            entry["exit"] = "trap" if record["trap"] is not None else record["exitCode"]
            entry["summary"] = record.get("summary", False)
        if record["errors"]:
            entry["errors"] = [{"code": e["code"], "message": scrub(e["message"].split("\n")[0], commit)} for e in record["errors"]]
        if record["initFuncs"] is not None:
            entry["init_funcs"] = record["initFuncs"]
        compile_records.append(entry)
    runs = {}
    for record in variant["runs"]:
        entry = {"status": record["status"]}
        if record["status"] == "exit":
            entry["exit_code"] = record["exitCode"]
        if record["status"] in ("exit", "trap"):
            entry["stdout"] = scrub_blob(record["stdout"], commit)
            entry["stderr"] = scrub_blob(record["stderr"], commit)
        runs[record["run"]] = entry
    return {"compile": compile_records, "runs": runs}


def normalize_case(record: dict[str, Any], commit: str) -> dict[str, Any]:
    return {f"O{v['opt_level']}": normalize_variant(v, commit) for v in record["variants"]}


def case_status(case: dict[str, Any], revision: str) -> str:
    """expected_status, overridden per fork revision by case.toml fork_status (a full commit hash)."""
    return case.get("fork_status", {}).get(revision, case["expected_status"])


def digest(value: Any) -> str:
    return sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def differences(expected: Any, actual: Any, path: str = "") -> list[str]:
    if isinstance(expected, dict) and isinstance(actual, dict):
        out = []
        for key in sorted(set(expected) | set(actual)):
            if key not in actual:
                out.append(f"{path}/{key}: missing")
            elif key not in expected:
                out.append(f"{path}/{key}: unexpected")
            else:
                out += differences(expected[key], actual[key], f"{path}/{key}")
        return out
    if isinstance(expected, list) and isinstance(actual, list) and len(expected) == len(actual):
        out = []
        for index, (a, b) in enumerate(zip(expected, actual)):
            out += differences(a, b, f"{path}[{index}]")
        return out
    if expected != actual:
        text = lambda v: json.dumps(v)[:300]
        return [f"{path}: expected {text(expected)}, got {text(actual)}"]
    return []


# ---------------------------------------------------------------- hosts

def twin_rustc(args: argparse.Namespace) -> Path:
    return args.twin or args.fork_build / "build/x86_64-unknown-linux-gnu/stage1/bin/rustc"


def node_host(suite_path: Path, out: Path, compiler: str, only: list[str], args: argparse.Namespace, stable_deps: Path | None = None) -> dict[str, Any]:
    command = ["node", "--disable-warning=ExperimentalWarning", str(RUNNER / "node.ts"), "--suite", str(suite_path), "--out", str(out), "--compiler", compiler, "--scratch", str(args.scratch / "node")]
    if only:
        command += ["--only", ",".join(only)]
    if compiler == "twin":
        command += ["--twin", str(twin_rustc(args)), "--wasm-ld", str(args.fork_source / "wasi-sdk-32.0-x86_64-linux/bin/wasm-ld")]
    if compiler == "stable":
        command += ["--stable-deps", str(stable_deps)]
    wait_for_load()
    run(command)
    return json.loads(out.read_text())


def browser_host(browser: str, suite_path: Path, out: Path, only: list[str], args: argparse.Namespace) -> dict[str, Any]:
    site = args.scratch / f"site-{browser}"
    run(["bun", str(RUNNER / "build-site.ts"), "--out", str(site), "--suite", str(suite_path), "--pack", str(args.pack)])
    command = ["bun", str(RUNNER / "browser.ts"), "--browser", browser, "--site", str(site), "--out", str(out)]
    if only:
        command += ["--only", ",".join(only)]
    wait_for_load()
    run(command)
    return json.loads(out.read_text())


def stable_deps(args: argparse.Namespace) -> Path:
    project = args.scratch / "stable-deps"
    project.mkdir(parents=True, exist_ok=True)
    (project / "src").mkdir(exist_ok=True)
    (project / "src" / "lib.rs").write_text("")
    dependencies = "\n".join(f'{name} = "{version}"' for name, version in STABLE_DEPS.items())
    (project / "Cargo.toml").write_text(
        "[package]\nname = \"krs-ir16-stable-deps\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n"
        f"[dependencies]\n{dependencies}\n\n[workspace]\n\n[profile.release]\npanic = \"abort\"\n"
    )
    wait_for_load()
    run(["cargo", "+stable", "build", "--offline", "--release", "--target", "wasm32-wasip1", "-j", "4", "--manifest-path", str(project / "Cargo.toml")],
        env={**os.environ, "CARGO_TARGET_DIR": str(project / "target")})
    return project / "target" / "wasm32-wasip1" / "release" / "deps"


# ---------------------------------------------------------------- comparison

def classify(status: str, entry: dict[str, Any], actual: dict[str, Any]) -> tuple[bool, str, list[str]]:
    """Returns (match, verdict, problems) for one host's normalized case against one revision's expectation."""
    twin = entry["twin"]
    if status == "pass":
        problems = differences(twin, actual)
        return (not problems, "pass" if not problems else "mismatch", problems)
    fork = entry.get("fork")
    if fork is None:
        return (False, "unrecorded", [f"{status} case has no recorded fork outcome for this revision; run --record"])
    problems = differences(fork, actual)
    if not problems:
        return (True, status, [])
    if not differences(twin, actual):
        return (False, "gap-closed", ["the fork now matches the twin; record the flip as an intentional expectation change"])
    return (False, "mismatch", problems)


def b13_checks(record: dict[str, Any]) -> list[str]:
    problems = []
    for variant in record["variants"]:
        runs = {r["run"]: r for r in variant["runs"]}
        before, spin, after = runs.get("before"), runs.get("spin"), runs.get("after")
        if not (before and spin and after):
            return ["B13 runs missing"]
        if spin["status"] != "cancelled":
            problems.append(f"spin run status {spin['status']}, expected cancelled")
        if after["generation"] != before["generation"] + 1:
            problems.append(f"executor generations before {before['generation']} after {after['generation']}: expected exactly one replacement")
        if (after["stdout"], after["stderr"], after["status"]) != (before["stdout"], before["stderr"], before["status"]):
            problems.append("the run after cancellation differs from the run before")
        recompiled = [c for c in variant["compile"] if c["crate"].endswith("@recompile")]
        if not recompiled or any(c["outcome"] != "ok" for c in recompiled):
            problems.append("recompile after cancellation did not succeed")
    return problems


def run_summary(variant: dict[str, Any]) -> str:
    parts = []
    for record in variant["runs"]:
        text = record["status"] if record["status"] != "exit" else f"exit {record['exitCode']}"
        parts.append(f"{record['run']}={text}")
    return ", ".join(parts) if parts else "no runs"


def compile_summary(variant: dict[str, Any]) -> str:
    parts = []
    for record in variant["compile"]:
        text = record["outcome"]
        if record["errors"]:
            text += "(" + ",".join(e["code"] or "-" for e in record["errors"]) + ")"
        if record["outcome"] != "ok":
            text += "[trap]" if record["trap"] else f"[exit {record['exitCode']}]"
        if record["initFuncs"] is not None:
            text += f"[init_funcs={record['initFuncs']}]"
        parts.append(f"{record['crate']}={text}")
    return ", ".join(parts)


def toml_value(value: Any) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return str(value)
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    if isinstance(value, list):
        return "[" + ", ".join(toml_value(v) for v in value) + "]"
    raise TypeError(value)


def write_toml_rows(path: Path, comment: list[str], header: dict[str, Any], table: str, rows: list[dict[str, Any]]) -> None:
    lines = [*(f"# {line}" for line in comment), ""]
    lines += [f"{key} = {toml_value(value)}" for key, value in header.items()]
    for row in rows:
        lines += ["", f"[[{table}]]"]
        lines += [f"{key} = {toml_value(value)}" for key, value in row.items()]
    path.write_text("\n".join(lines) + "\n")


def native_commit(rustc: Path) -> str:
    output = subprocess.run([str(rustc), "-vV"], capture_output=True, text=True, check=True).stdout
    return re.search(r"^commit-hash: (\S+)$", output, re.M).group(1)


# ---------------------------------------------------------------- main

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--host", default="node", help="node, chromium, firefox, all, none, or a comma-separated list")
    parser.add_argument("--references", action="store_true", help="rebuild the twin and stable references and compare them with expected.json")
    parser.add_argument("--record", action="store_true", help="rewrite this fork revision's entry of every expected.json (implies --references and the node host)")
    parser.add_argument("--only", default="", help="comma-separated case ids")
    parser.add_argument("--pack", type=Path, default=DEFAULT_PACK, help="IR-14 pack root (holds pack-manifest.toml); its rustc.wasm, bundle, and rlibs are used together")
    parser.add_argument("--fork-build", type=Path, default=DEFAULT_FORK_BUILD, help="fork build root of the same commit as the pack (its stage1 twin is the reference)")
    parser.add_argument("--twin", type=Path, default=None, help="native twin rustc (default: FORK_BUILD/build/x86_64-unknown-linux-gnu/stage1/bin/rustc)")
    parser.add_argument("--fork-source", type=Path, default=DEFAULT_FORK_SOURCE, help="only its wasi-sdk wasm-ld is used (twin links)")
    parser.add_argument("--scratch", type=Path, default=Path("/var/tmp/krs-ir16-scratch"))
    parser.add_argument("--out", type=Path, default=Path("/var/tmp/krs-ir16-run"))
    parser.add_argument("--evidence", type=Path, default=None, help="also copy host records, matrix.toml, and expectations.toml here")
    args = parser.parse_args()

    hosts = list(HOSTS) if args.host == "all" else [] if args.host == "none" else [h for h in args.host.split(",") if h]
    for host in hosts:
        if host not in HOSTS:
            parser.error(f"unknown host {host}")
    if args.record:
        args.references = True
        if "node" not in hosts:
            hosts.insert(0, "node")
    only = [c for c in args.only.split(",") if c]
    load_at_start = wait_for_load()
    args.out.mkdir(parents=True, exist_ok=True)
    args.scratch.mkdir(parents=True, exist_ok=True)

    cases = load_cases(only)
    pack = pack_section(args.pack)
    manifest = pack["_manifest"]
    revision = manifest["compiler"]["fork_revision"]
    suite = suite_file(cases, pack)
    suite["pack"]["fork_revision"] = revision
    suite_path = args.out / "suite.json"
    suite_path.write_text(json.dumps(suite, indent=1) + "\n")
    log(f"{len(cases)} cases; pack {pack['pack_id']}; fork {revision}; load {load_at_start}")

    failures: list[str] = []
    references: dict[str, dict[str, Any]] = {}
    if args.references:
        twin_commit = native_commit(twin_rustc(args))
        if twin_commit != revision:
            raise SystemExit(f"twin {twin_rustc(args)} is at {twin_commit}, the pack at {revision}")
        references["twin"] = node_host(suite_path, args.out / "twin-reference.json", "twin", only, args)
        references["stable"] = node_host(suite_path, args.out / "stable-reference.json", "stable", only, args, stable_deps(args))

    records: dict[str, dict[str, Any]] = {}
    for host in hosts:
        out = args.out / f"{host}.json"
        records[host] = node_host(suite_path, out, "fork", only, args) if host == "node" else browser_host(host, suite_path, out, only, args)

    by_id = lambda record: {c["id"]: c for c in record["cases"]}
    expectation_rows = []

    for case in cases:
        path = case["_dir"] / "expected.json"
        document = json.loads(path.read_text()) if path.is_file() else {"schema": 2, "case": case["id"], "revisions": {}}
        status = case_status(case, revision)
        entry = document["revisions"].get(revision)
        if args.references:
            twin = normalize_case(by_id(references["twin"])[case["id"]], revision)
            stable = normalize_case(by_id(references["stable"])[case["id"]], revision)
            if args.record:
                entry = {
                    "status": status,
                    "reference": {
                        "twin": references["twin"]["environment"]["native_rustc_vv"],
                        "stable": references["stable"]["environment"]["native_rustc_vv"],
                        "pack_id": pack["pack_id"],
                        "run_host": "node:wasi " + references["twin"]["environment"]["node"],
                        "recorded": datetime.date.today().isoformat(),
                    },
                    "twin": twin,
                    "stable": stable,
                    "stable_differs": differences(twin, stable),
                }
                if status != "pass":
                    entry["fork"] = normalize_case(by_id(records["node"])[case["id"]], revision)
                    entry["gap"] = case.get("gap", {})
                document["revisions"][revision] = entry
                document["revisions"] = dict(sorted(document["revisions"].items()))
                path.write_text(json.dumps(document, indent=1, ensure_ascii=False) + "\n")
            elif entry is not None:
                drift = differences(entry["twin"], twin)
                if drift:
                    failures.append(f"{case['id']}: twin reference drifted from expected.json: {drift[:3]}")
                if differences(entry["stable"], stable):
                    log(f"{case['id']}: stable reference differs from the recorded one (informative)")
        if entry is None:
            failures.append(f"{case['id']}: expected.json has no entry for fork {revision} (run --record with this pack)")
            continue
        if entry["status"] != status:
            failures.append(f"{case['id']}: case.toml status {status} differs from the recorded {entry['status']} (run --record)")
        case["_entry"] = entry
        case["_status"] = status
        oracle = case.get("oracle")
        if oracle:
            oracle_bytes = (case["_dir"] / oracle["file"]).read_bytes()
            for variant_name, variant in entry["twin"].items():
                for run_name in oracle["runs"]:
                    stdout = variant["runs"][run_name]["stdout"]
                    got = stdout["utf8"].encode() if "utf8" in stdout else base64.b64decode(stdout["base64"])
                    if got.rstrip(b"\n") != oracle_bytes.rstrip(b"\n"):
                        failures.append(f"{case['id']} {variant_name} {run_name}: twin output differs from {oracle['file']}")
        for other, other_entry in document["revisions"].items():
            expectation_rows.append({
                "case": case["id"],
                "fork_revision": other,
                "status": other_entry["status"],
                "twin_sha256": digest(other_entry["twin"]),
                "stable_sha256": digest(other_entry["stable"]),
                "twin_equals_stable": not other_entry["stable_differs"],
                "stable_differs": other_entry["stable_differs"][:8],
                "fork_sha256": digest(other_entry["fork"]) if "fork" in other_entry else "",
                "twin_equals_current_revision_twin": digest(other_entry["twin"]) == digest(entry["twin"]),
            })

    rows = []
    for host, record in records.items():
        verified = record["verified"]
        if verified["rustc_wasm_sha256"] != manifest["compiler"]["rustc_wasm_sha256"]:
            failures.append(f"{host}: rustc.wasm {verified['rustc_wasm_sha256']} is not the manifest's")
        if verified["sysroot_bundle_sha256"] != manifest["sysroot"]["bundle_sha256"]:
            failures.append(f"{host}: sysroot bundle {verified['sysroot_bundle_sha256']} is not the manifest's")
        if verified["pack_id_recomputed"] != manifest["pack_id"]:
            failures.append(f"{host}: recomputed pack_id {verified['pack_id_recomputed']} is not the manifest's")
        host_cases = by_id(record)
        for case in cases:
            if "_entry" not in case:
                continue
            actual_record = host_cases.get(case["id"])
            if actual_record is None:
                failures.append(f"{host} {case['id']}: not run")
                continue
            actual = normalize_case(actual_record, revision)
            match, verdict, problems = classify(case["_status"], case["_entry"], actual)
            if case["id"] == "B13-recovery":
                extra = b13_checks(actual_record)
                problems += extra
                match = match and not extra
                verdict = verdict if not extra else "mismatch"
            if not match:
                failures.append(f"{host} {case['id']}: {verdict}: {problems[:4]}")
            expected_variants = case["_entry"]["twin"] if case["_status"] == "pass" else case["_entry"].get("fork", {})
            for variant in actual_record["variants"]:
                name = f"O{variant['opt_level']}"
                rows.append({
                    "case": case["id"],
                    "opt_level": variant["opt_level"],
                    "host": host,
                    "expected_status": case["_status"],
                    "compile": compile_summary(variant),
                    "run": run_summary(variant),
                    "output_sha256": digest(actual[name]),
                    "expected_sha256": digest(expected_variants.get(name)),
                    "match": match,
                    "verdict": verdict,
                    "problems": problems[:6],
                    "compile_ms": round(sum(c["ms"] for c in variant["compile"])),
                    "run_ms": round(sum(r["ms"] for r in variant["runs"])),
                })

    header = {
        "date": datetime.date.today().isoformat(),
        "krs_revision": subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip(),
        "pack": str(args.pack),
        "pack_id": pack["pack_id"],
        "fork_revision": revision,
        "rustc_wasm_sha256": manifest["compiler"]["rustc_wasm_sha256"],
        "sysroot_bundle_sha256": manifest["sysroot"]["bundle_sha256"],
        "hosts": list(records),
        "os": f"{platform.system()} {platform.release()} {platform.machine()}",
        "load_at_start": load_at_start,
        "pass": not failures,
        "failures": failures,
    }
    if records:
        write_toml_rows(args.out / "matrix.toml", ["IR-16 browser backend compatibility matrix (tests/browser-backend/verify.py).", "One row per case, opt level, and host."], header, "row", rows)
    write_toml_rows(args.out / "expectations.toml", ["IR-16 expectation hashes: sha256 of the normalized per-case JSON in cases/<id>/expected.json, per fork revision."],
                    {"current_fork_revision": revision}, "case", expectation_rows)
    if args.evidence:
        args.evidence.mkdir(parents=True, exist_ok=True)
        for name in ["matrix.toml", "expectations.toml", *[f"{h}.json" for h in records], *[f"{r}-reference.json" for r in references]]:
            if (args.out / name).is_file():
                shutil.copy(args.out / name, args.evidence / name)

    for failure in failures:
        log(f"FAIL {failure}")
    log(f"{'PASS' if not failures else 'FAIL'}: {len(cases)} cases, fork {revision[:9]}, hosts {', '.join(records) or 'none'}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
