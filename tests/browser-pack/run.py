#!/usr/bin/env python3
"""Top-level browser-lesson regression runner (IR-21): every browser gate, in order, against one pack.

Local mode (a pack and the fork build that produced it; this machine):

  PYTHONDONTWRITEBYTECODE=1 python3 tests/browser-pack/run.py \\
      --pack /var/tmp/krs-ir18-pack-r26/pack \\
      --fork-build /var/tmp/krs-browser-fork/R-26 \\
      --fork-source ../inspirations/AngelOnFira/rust-fix \\
      [--out /var/tmp/krs-ir21-run] [--rebuild] [--record-backend] [--steps a,b,...] [--keep-going]

Hosted mode (a published release fetched by content address; no fork build, so the steps that need
the native twin are skipped):

  PYTHONDONTWRITEBYTECODE=1 python3 tests/browser-pack/run.py \\
      --base-url https://<host>/<path>/ --release <release sha256> [--out DIR]

Steps (local mode, in order; --steps selects a subset, dependencies are the caller's concern):
  expectations        fail first, with the file to edit, when the pack's fork revision has no recorded
                      expectation: IR-15 scenarios with expectByFork (browser/worker/test/scenarios.ts) and
                      every IR-16 case (tests/browser-backend/cases/*/expected.json; --record-backend records them)
  modules             krs-lesson-policy and krs-expand-wasm, each in its own cargo invocation (IR-15 finding 3)
  stage               browser/worker/scripts/stage-assets.ts over --pack and the two modules
  oracle              browser/worker/test/parity/regenerate-oracle.sh (IR-17 native oracle for this crates/ tree)
  licenses            browser/release/release.py licenses (fails closed; needs --fork-source and --fork-build)
  release             browser/release/release.py assemble into OUT/publish (content-addressed layout)
  fetch               serve OUT/publish under hosting.toml, fetch the release by its SHA-256 with header checks,
                      and require the fetched directory to equal the staged one; later steps use the fetched copy
  check               tests/browser-pack/verify.py --check (pack, pack.json, licenses, oracle, release) and --falsify
  pipeline            IR-15 scenarios through the pipeline stage functions under Bun (test/run-pipeline.ts)
  tour-minimal        IR-17 bundle parity, headless Chromium and Firefox
  native-diagnostics  IR-18 native baseline and twin controls (needs the twin of the pack's fork)
  diagnostics         IR-18 diagnostic parity, headless Chromium and Firefox
  backend             IR-16 backend suite: --host all --references (twin; --record-backend adds --record for a new fork commit)
  cache               IR-21 cache and corruption tests, headless Chromium and Firefox
  rebuild             (only with --rebuild) tests/browser-pack/verify.py --rebuild: two clean pack builds compared byte for byte
Hosted mode runs: fetch, expectations, oracle, check, pipeline, tour-minimal, backend (hosts against expected.json, no references), cache.

Resource rules: the runner waits while the 1-minute load exceeds LOAD_MAX (default 40) before each step;
cargo runs at nice -n 19 with -j JOBS (default 4); pack builds take the heavy-build flock (build.sh).
Every step's output goes to OUT/logs/<step>.log; OUT/run.toml records the steps, exit codes, and wall times.
Environment: KRS_Z3_LIB (default: the Nix store Z3 4.12.5), CARGO_TARGET_ROOT (default /var/tmp/krs-ir21-target).
"""

from __future__ import annotations

import argparse
import datetime
import glob
import json
import os
import shutil
import signal
import subprocess
import sys
import time
import tomllib
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WORKER = ROOT / "browser/worker"
RELEASE = ROOT / "browser/release/release.py"
LOAD_MAX = float(os.environ.get("LOAD_MAX", "40"))
JOBS = os.environ.get("JOBS", "4")
LOCAL_STEPS = ["expectations", "modules", "stage", "oracle", "licenses", "release", "fetch", "check", "pipeline", "tour-minimal", "native-diagnostics", "diagnostics", "backend", "cache"]
HOSTED_STEPS = ["fetch", "expectations", "oracle", "check", "pipeline", "tour-minimal", "backend", "cache"]


def log(message: str) -> None:
    print(f"[run] {message}", file=sys.stderr, flush=True)


def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(ROOT), *args], check=True, capture_output=True, text=True).stdout.strip()


def z3_lib() -> str:
    if os.environ.get("KRS_Z3_LIB"):
        return os.environ["KRS_Z3_LIB"]
    hits = sorted(glob.glob("/nix/store/*-z3-4.12.5-lib/lib"))
    return hits[0] if hits else ""


def wait_for_load() -> float:
    while os.getloadavg()[0] > LOAD_MAX:
        log(f"1-minute load {os.getloadavg()[0]:.1f} > {LOAD_MAX}; waiting 60 s")
        time.sleep(60)
    return os.getloadavg()[0]


class Runner:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.out: Path = args.out.resolve()
        self.logs = self.out / "logs"
        self.logs.mkdir(parents=True, exist_ok=True)
        self.results: list[dict[str, Any]] = []
        self.target_root = Path(os.environ.get("CARGO_TARGET_ROOT", "/var/tmp/krs-ir21-target"))
        self.cli_target = self.target_root / "cli"
        self.krs_bin = self.cli_target / "debug/krs"
        z3 = z3_lib()
        self.env = {**os.environ, "KRS_Z3_LIB": z3, "LOAD_MAX": str(int(LOAD_MAX)), "PYTHONDONTWRITEBYTECODE": "1",
                    "LIBRARY_PATH": ":".join(p for p in (z3, os.environ.get("LIBRARY_PATH", "")) if p),
                    "LD_LIBRARY_PATH": ":".join(p for p in (z3, os.environ.get("LD_LIBRARY_PATH", "")) if p)}
        self.staged = self.out / "staged"
        self.fetched = self.out / "fetched"
        self.publish = self.out / "publish"
        self.oracle_dir = self.out / "oracle"
        self.release_sha: str | None = args.release

    @property
    def assets(self) -> Path:
        """The asset directory the gates read: the content-addressed copy once fetched."""
        return self.fetched if (self.fetched / "pack.json").is_file() else self.staged

    def step(self, name: str, command: list[str], cwd: Path = ROOT, env: dict[str, str] | None = None) -> bool:
        load = wait_for_load()
        log(f"== {name}: {' '.join(str(c) for c in command)}")
        started = time.monotonic()
        with open(self.logs / f"{name}.log", "w") as f:
            rc = subprocess.run([str(c) for c in command], cwd=cwd, env={**self.env, **(env or {})}, stdout=f, stderr=subprocess.STDOUT).returncode
        wall = round(time.monotonic() - started, 1)
        self.results.append({"step": name, "exit": rc, "wall_s": wall, "load_at_start": round(load, 2), "log": str(self.logs / f"{name}.log")})
        log(f"== {name}: {'PASS' if rc == 0 else f'FAIL ({rc})'} in {wall} s")
        return rc == 0

    # ---------------------------------------------------------------- steps

    def modules(self) -> bool:
        ok = True
        for pkg in ("krs-lesson-policy", "krs-expand-wasm"):
            ok = ok and self.step(f"modules-{pkg}", ["nice", "-n", "19", "cargo", "+stable", "build", "--locked", "--offline", "-j", JOBS,
                                                    "-p", pkg, "--target", "wasm32-unknown-unknown", "--release"],
                                  env={"CARGO_TARGET_DIR": str(self.target_root / pkg)})
        return ok

    def module_path(self, pkg: str) -> Path:
        return self.target_root / pkg / "wasm32-unknown-unknown/release" / f"{pkg.replace('-', '_')}.wasm"

    def stage(self) -> bool:
        return self.step("stage", ["bun", "scripts/stage-assets.ts", "--out", self.staged, "--pack", self.args.pack.resolve(), "--krs-rev", git("rev-parse", "HEAD")],
                         cwd=WORKER, env={"KRS_IR15_POLICY": str(self.module_path("krs-lesson-policy")),
                                          "KRS_IR15_EXPANDER": str(self.module_path("krs-expand-wasm")), "KRS_IR15_REPO": str(ROOT)})

    def oracle(self) -> bool:
        return self.step("oracle", ["bash", "browser/worker/test/parity/regenerate-oracle.sh", self.oracle_dir],
                         env={"CLI_TARGET": str(self.cli_target), "KRS_BIN": str(self.krs_bin)})

    def licenses(self) -> bool:
        return self.step("licenses", ["python3", RELEASE, "licenses", "--staged", self.staged, "--fork-source", self.args.fork_source.resolve(),
                                      "--fork-build", self.args.fork_build.resolve()])

    def release(self) -> bool:
        shutil.rmtree(self.publish, ignore_errors=True)
        ok = self.step("release", ["python3", RELEASE, "assemble", "--staged", self.staged, "--publish", self.publish,
                                   "--oracle", self.oracle_dir / "oracle.toml", "--activate"])
        if ok:
            self.release_sha = json.loads((self.publish / "index.json").read_text())["active"]["sha256"]
        return ok

    def fetch(self) -> bool:
        shutil.rmtree(self.fetched, ignore_errors=True)
        if self.args.base_url:
            return self.step("fetch", ["python3", RELEASE, "fetch", "--base-url", self.args.base_url, "--release", self.release_sha,
                                       "--out", self.fetched, "--check-headers"])
        port = str(self.args.serve_port)
        server = subprocess.Popen(["python3", RELEASE, "serve", self.publish, "--port", port], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            time.sleep(1)
            ok = self.step("fetch", ["python3", RELEASE, "fetch", "--base-url", f"http://127.0.0.1:{port}/", "--release", self.release_sha,
                                     "--out", self.fetched, "--check-headers", "--expect-cors"])
        finally:
            server.send_signal(signal.SIGINT)
            server.wait(timeout=10)
        if ok:
            ok = self.step("fetch-equals-staged", ["diff", "-r", "--exclude=.release.json", self.staged, self.fetched])
        return ok

    def fork_revision(self) -> str:
        manifest = (self.args.pack / "pack-manifest.toml") if self.args.pack else (self.assets / "pack/pack-manifest.toml")
        return tomllib.loads(manifest.read_text())["compiler"]["fork_revision"]

    def expectations(self) -> bool:
        fork = self.fork_revision()
        script = ("import { scenariosMissingFork } from './test/scenarios.ts';"
                  f"const missing = scenariosMissingFork('{fork}');"
                  "if (missing.length) { console.error(`IR-15 scenarios without an expectation for fork " + fork + " (add expectByFork entries in browser/worker/test/scenarios.ts): ${missing.join(', ')}`); process.exit(1); }"
                  "console.log('IR-15 scenarios: every fork-dependent scenario has an expectation for " + fork + "');")
        ok = self.step("expectations-ir15", ["bun", "-e", script], cwd=WORKER)
        missing = sorted(p.parent.name for p in (ROOT / "tests/browser-backend/cases").glob("*/expected.json")
                         if fork not in json.loads(p.read_text()).get("revisions", {}))
        if missing and not self.args.record_backend:
            message = (f"IR-16 cases without an expected.json entry for fork {fork}: {', '.join(missing)}; "
                       "record them with --record-backend (tests/browser-backend/verify.py --record) and review the diff")
            return self.step("expectations-ir16", ["sh", "-c", f"echo '{message}' >&2; exit 1"]) and False
        return self.step("expectations-ir16", ["sh", "-c", f"echo 'IR-16: {'recording ' + str(len(missing)) + ' cases' if missing else 'every case has an entry'} for fork {fork}'"]) and ok

    def pipeline(self) -> bool:
        return self.step("pipeline", ["bun", "test/run-pipeline.ts", "--assets", self.assets, "--out", self.out / "ir15-pipeline-bun.json"], cwd=WORKER)

    def check(self) -> bool:
        command = ["python3", HERE / "verify.py", "--check", "--staged", self.assets, "--out", self.out / "check.json"]
        if self.publish.is_dir():
            command += ["--publish", self.publish]
        if (self.oracle_dir / "oracle.toml").is_file():
            command += ["--oracle", self.oracle_dir / "oracle.toml"]
        ok = self.step("check", command)
        return self.step("falsify", ["python3", HERE / "verify.py", "--falsify", "--staged", self.assets, "--out", self.out / "falsify.json"]) and ok

    def tour_minimal(self) -> bool:
        return self.step("tour-minimal", ["bun", "test/parity/tour-minimal.ts", "--oracle-dir", self.oracle_dir, "--assets", self.assets,
                                          "--out", self.out / "ir17", "--bundles", self.out / "ir17-bundles", "--site", self.out / "site-ir17"], cwd=WORKER)

    def twin(self) -> Path:
        return self.args.fork_build.resolve() / "build/x86_64-unknown-linux-gnu/stage1/bin/rustc"

    def native_diagnostics(self) -> bool:
        return self.step("native-diagnostics", ["bash", "test/parity/native-diagnostics.sh", self.out / "ir18-native"], cwd=WORKER,
                         env={"ORACLE_DIR": str(self.oracle_dir), "ASSETS": str(self.assets), "TWIN": str(self.twin()), "KRS_BIN": str(self.krs_bin), "REPO": str(ROOT)})

    def diagnostics(self) -> bool:
        return self.step("diagnostics", ["bun", "test/parity/diagnostics.ts", "--native", self.out / "ir18-native", "--assets", self.assets,
                                         "--site", self.out / "site-ir18", "--out", self.out / "ir18", "--scratch", self.out / "ir18-scratch",
                                         "--krs-bin", self.krs_bin], cwd=WORKER)

    def backend(self) -> bool:
        command = ["python3", "tests/browser-backend/verify.py", "--pack", self.assets / "pack", "--host", "all",
                   "--scratch", self.out / "ir16-scratch", "--out", self.out / "ir16"]
        if self.args.fork_build:
            command += ["--fork-build", self.args.fork_build.resolve(), "--fork-source", self.args.fork_source.resolve(), "--references"]
            if self.args.record_backend:
                command.append("--record")
        return self.step("backend", command)

    def cache(self) -> bool:
        return self.step("cache", ["bun", "test/cache/run.ts", "--staged", self.assets, "--oracle", self.oracle_dir / "oracle.toml",
                                   "--out", self.out / "cache", "--work", self.out / "cache-work"], cwd=WORKER)

    def rebuild(self) -> bool:
        command = ["python3", HERE / "verify.py", "--rebuild", "--fork-build", self.args.fork_build.resolve(), "--scratch", self.out / "rebuild",
                   "--evidence", self.out / "rebuild-evidence", "--out", self.out / "rebuild.json"]
        if self.args.fork_source:
            command += ["--fork-source", self.args.fork_source.resolve()]
        if self.args.pack:
            command += ["--against", self.args.pack.resolve()]
        return self.step("rebuild", command)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--pack", type=Path, help="IR-14 pack root (local mode)")
    parser.add_argument("--fork-build", type=Path, help="fork build root of the pack's fork commit (twin, rustc.wasm, COPYRIGHT files)")
    parser.add_argument("--fork-source", type=Path, help="fork source checkout at the pack's fork commit (licenses, wasi-sdk wasm-ld)")
    parser.add_argument("--base-url", help="hosted mode: publication base URL")
    parser.add_argument("--release", help="hosted mode: release manifest sha256")
    parser.add_argument("--out", type=Path, default=Path("/var/tmp/krs-ir21-run"))
    parser.add_argument("--steps", default="", help="comma-separated subset")
    parser.add_argument("--rebuild", action="store_true", help="also run the heavy two-build reproducibility gate")
    parser.add_argument("--record-backend", action="store_true", help="IR-16 --record: new fork commit; review the expected.json diff by hand")
    parser.add_argument("--keep-going", action="store_true")
    parser.add_argument("--serve-port", type=int, default=8741)
    args = parser.parse_args()
    hosted = bool(args.base_url)
    if hosted and not args.release:
        parser.error("hosted mode needs --release (a content address, not the mutable index)")
    if not hosted and not (args.pack and args.fork_build and args.fork_source):
        parser.error("local mode needs --pack, --fork-build, and --fork-source")
    if args.pack:
        manifest = tomllib.loads((args.pack / "pack-manifest.toml").read_text())
        fork_rev = manifest["compiler"]["fork_revision"]
        twin_vv = subprocess.run([str(args.fork_build / "build/x86_64-unknown-linux-gnu/stage1/bin/rustc"), "-vV"], capture_output=True, text=True).stdout
        if f"commit-hash: {fork_rev}" not in twin_vv:
            parser.error(f"--fork-build twin is not at the pack's fork revision {fork_rev}")
        if git_rev(args.fork_source) != fork_rev:
            parser.error(f"--fork-source HEAD is not the pack's fork revision {fork_rev}")
        crates = next(i["git_tree"] for i in manifest["input"] if i["name"] == "KRS crates/ tree")
        if crates != git("rev-parse", "HEAD:crates"):
            parser.error(f"the pack was built from crates tree {crates}; this checkout has {git('rev-parse', 'HEAD:crates')} (rebuild the pack with browser/pack/build.sh)")
    steps = HOSTED_STEPS if hosted else LOCAL_STEPS + (["rebuild"] if args.rebuild else [])
    if args.steps:
        wanted = args.steps.split(",")
        unknown = [s for s in wanted if s not in LOCAL_STEPS + ["rebuild"]]
        if unknown:
            parser.error(f"unknown steps {unknown}")
        steps = [s for s in steps if s in wanted] + [s for s in wanted if s == "rebuild" and s not in steps]
    runner = Runner(args)
    if runner.release_sha is None and (runner.publish / "index.json").is_file():
        runner.release_sha = json.loads((runner.publish / "index.json").read_text())["active"]["sha256"]
    started = time.monotonic()
    header = {"date": datetime.datetime.now().isoformat(timespec="seconds"), "krs_revision": git("rev-parse", "HEAD"),
              "crates_tree": git("rev-parse", "HEAD:crates"), "mode": "hosted" if hosted else "local",
              "pack": str(args.pack) if args.pack else None, "fork_build": str(args.fork_build) if args.fork_build else None,
              "fork_source": str(args.fork_source) if args.fork_source else None, "base_url": args.base_url,
              "uptime": subprocess.run(["uptime"], capture_output=True, text=True).stdout.strip(), "steps": steps}
    log(json.dumps(header))
    failed = []
    for name in steps:
        ok = getattr(runner, name.replace("-", "_"))()
        if not ok:
            failed.append(name)
            if not args.keep_going:
                break
    header["release_sha256"] = runner.release_sha
    header["wall_s"] = round(time.monotonic() - started, 1)
    header["pass"] = not failed and bool(runner.results)
    header["failed"] = failed
    lines = ["# IR-21 browser-lesson regression run (tests/browser-pack/run.py)."]
    for k, v in header.items():
        if v is not None:
            lines.append(f"{k} = {json.dumps(v)}")
    for r in runner.results:
        lines.append("\n[[step]]")
        lines += [f"{k} = {json.dumps(v)}" for k, v in r.items()]
    (runner.out / "run.toml").write_text("\n".join(lines) + "\n")
    tomllib.loads((runner.out / "run.toml").read_text())
    log(f"{'PASS' if header['pass'] else 'FAIL'}: {len(runner.results)} steps in {header['wall_s']} s; failed: {failed or 'none'}; {runner.out / 'run.toml'}")
    return 0 if header["pass"] else 1


def git_rev(path: Path) -> str:
    return subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()


if __name__ == "__main__":
    sys.exit(main())
