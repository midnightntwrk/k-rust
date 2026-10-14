#!/usr/bin/env python3
"""Local end-to-end site: the docs site with the browser lesson, served against a local release.

  python3 browser/release/serve-local.py [--fork-build DIR] [--fork-source DIR] [--pack DIR]
      [--site-port 8740] [--pack-port 8741] [--pack-base URL] [--state DIR] [--cargo-target-root DIR]
      [--rebuild-release] [--rebuild-site] [--prepare-only]

This is the local deployment of docs-site/README.md ("Local deployment") as one command:

  1. pack      reuse --pack when its crates/ and browser/pack/ trees are the checkout's and its fork revision is the
               fork build's; otherwise build one with browser/pack/build.sh into STATE/pack-<crates>-<pack>-<fork>/
               (heavy-build flock, nice, -j 4) or reuse that directory when a previous launch built it.
  2. release   tests/browser-pack/run.py --steps modules,stage,oracle,licenses,release into STATE/run/, skipped when
               STATE/run/serve-local.json records the same inputs (pack, fork build, and the checkout's crates/,
               browser/, tests/tour-minimal/, Cargo.toml, Cargo.lock, including uncommitted changes).
               The release gates (expectations, fetch, check, browsers) are not run; run.py without --steps runs them.
  3. site      bun run build:lesson-worker and vocs build in docs-site/ with VITE_KRS_BROWSER_PACK_BASE set, skipped
               when docs-site/dist/.serve-local.json records the same pack base and the same docs-site/ and
               browser/worker/ inputs. The docs `check` step of `bun run build` is not run.
  4. serve     browser/release/release.py serve STATE/run/publish on 127.0.0.1:PACK_PORT and the built site
               (node dist/serve-node.js) on 127.0.0.1:SITE_PORT, in the foreground until Ctrl-C, which stops both.

CARGO_TARGET_ROOT is private to the checkout (default /var/tmp/krs-local-target-<checkout name>-<path hash>): the
oracle step's krs binary locates the framework through its compile-time CARGO_MANIFEST_DIR, so a binary built in
another worktree fails with a Cargo package collision.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import signal
import subprocess
import sys
import time
import tomllib
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SITE = ROOT.parent / "docs-site"
# The directory holding the reference checkouts, as tests/support locates it.
EXTERNAL_ROOT = Path(os.environ["KRS_EXTERNAL_ROOT"]) if os.environ.get("KRS_EXTERNAL_ROOT") else next(
    (directory for directory in ROOT.parents if (directory / "inspirations" / "runtimeverification").is_dir()),
    ROOT.parents[1],
)
RELEASE_INPUTS = ["crates", "browser", "tests/tour-minimal", "../Cargo.toml", "../Cargo.lock"]
SITE_INPUTS = ["../docs-site", "browser/worker", "tests/tour-minimal"]
NICE = ["nice", "-n", "19", "ionice", "-c3"]


def log(message: str) -> None:
    print(f"[serve-local] {message}", file=sys.stderr, flush=True)


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.run(["git", "-C", str(cwd), *args], check=True, capture_output=True, text=True).stdout.strip()


def inputs_key(paths: list[str]) -> dict[str, str]:
    """The committed trees of PATHS plus a digest of their uncommitted changes (tracked diff and untracked files)."""
    trees = {p: git("rev-parse", f"HEAD:./{p}") for p in paths}
    h = hashlib.sha256()
    h.update(subprocess.run(["git", "-C", str(ROOT), "diff", "HEAD", "--binary", "--", *paths], check=True, capture_output=True).stdout)
    for name in sorted(filter(None, git("ls-files", "--others", "--exclude-standard", "-z", "--", *paths).split("\0"))):
        h.update(name.encode() + b"\0")
        h.update(hashlib.sha256((ROOT / name).read_bytes()).digest())
    return {**trees, "uncommitted": h.hexdigest()}


def run(command: list[object], cwd: Path = ROOT, env: dict[str, str] | None = None) -> None:
    log("$ " + " ".join(str(c) for c in command))
    rc = subprocess.run([str(c) for c in command], cwd=cwd, env={**os.environ, **(env or {})}).returncode
    if rc != 0:
        sys.exit(f"serve-local: command failed ({rc}): {' '.join(str(c) for c in command)}")


def read_json(path: Path) -> dict | None:
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return None


def twin_revision(fork_build: Path) -> str:
    out = subprocess.run([str(fork_build / "build/x86_64-unknown-linux-gnu/stage1/bin/rustc"), "-vV"], capture_output=True, text=True).stdout
    return next((line.split(": ", 1)[1] for line in out.splitlines() if line.startswith("commit-hash: ")), "")


def pack_mismatch(pack: Path, fork_rev: str) -> str | None:
    """Why PACK cannot serve this checkout and fork build, or None when it can."""
    try:
        manifest = tomllib.loads((pack / "pack-manifest.toml").read_text())
    except OSError:
        return f"{pack}/pack-manifest.toml is missing"
    trees = {i["name"]: i.get("git_tree") for i in manifest.get("input", [])}
    want = {"KRS crates/ tree": git("rev-parse", "HEAD:./crates"), "KRS browser/pack/ tree": git("rev-parse", "HEAD:./browser/pack")}
    for name, tree in want.items():
        if trees.get(name) != tree:
            return f"{name} is {trees.get(name)}, the checkout has {tree}"
    if manifest["compiler"]["fork_revision"] != fork_rev:
        return f"fork revision is {manifest['compiler']['fork_revision']}, the fork build is {fork_rev}"
    return None


def wait_http(url: str, proc: subprocess.Popen, what: str) -> None:
    for _ in range(600):
        if proc.poll() is not None:
            sys.exit(f"serve-local: {what} exited with {proc.returncode}")
        try:
            with urllib.request.urlopen(url, timeout=2) as response:
                if response.status < 500:
                    return
        except Exception:
            pass
        time.sleep(0.2)
    sys.exit(f"serve-local: {what} did not answer {url}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--fork-build", type=Path, default=Path("/var/tmp/krs-browser-fork/R-22"))
    parser.add_argument("--fork-source", type=Path, default=EXTERNAL_ROOT / "inspirations/AngelOnFira/rust-22")
    parser.add_argument("--pack", type=Path, default=Path("/var/tmp/krs-browser-release/packbuild/pack"), help="pack to reuse when it matches")
    parser.add_argument("--state", type=Path, default=None, help="default /var/tmp/krs-local-site-<checkout name>")
    parser.add_argument("--cargo-target-root", type=Path, default=None)
    parser.add_argument("--site-port", type=int, default=8740)
    parser.add_argument("--pack-port", type=int, default=8741)
    parser.add_argument("--pack-base", default=None, help="pack base URL baked into the site (default http://127.0.0.1:PACK_PORT/)")
    parser.add_argument("--rebuild-release", action="store_true")
    parser.add_argument("--rebuild-site", action="store_true")
    parser.add_argument("--prepare-only", action="store_true", help="stop after the site build")
    args = parser.parse_args()

    path_hash = hashlib.sha256(str(ROOT).encode()).hexdigest()[:8]
    state = (args.state or Path(f"/var/tmp/krs-local-site-{ROOT.name}")).resolve()
    target_root = (args.cargo_target_root or Path(f"/var/tmp/krs-local-target-{ROOT.name}-{path_hash}")).resolve()
    pack_base = args.pack_base or f"http://127.0.0.1:{args.pack_port}/"
    fork_build, fork_source = args.fork_build.resolve(), args.fork_source.resolve()
    state.mkdir(parents=True, exist_ok=True)

    fork_rev = twin_revision(fork_build)
    if not fork_rev:
        sys.exit(f"serve-local: {fork_build} has no native twin (build/x86_64-unknown-linux-gnu/stage1/bin/rustc)")
    if git("rev-parse", "HEAD", cwd=fork_source) != fork_rev:
        sys.exit(f"serve-local: {fork_source} HEAD is not the fork build's revision {fork_rev}")

    # ---- 1. pack
    pack = args.pack.resolve()
    reason = pack_mismatch(pack, fork_rev)
    if reason:
        built = state / f"pack-{git('rev-parse', 'HEAD:./crates')[:8]}-{git('rev-parse', 'HEAD:./browser/pack')[:8]}-{fork_rev[:9]}"
        if pack_mismatch(built / "pack", fork_rev) is None:
            log(f"{pack} does not match ({reason}); reusing {built / 'pack'}")
        else:
            log(f"{pack} does not match ({reason}); building a pack into {built}")
            if built.exists() and any(built.iterdir()):
                sys.exit(f"serve-local: {built} holds an incomplete pack build; remove it and retry")
            if git("status", "--porcelain", "--", "crates", "browser/pack", "../Cargo.lock"):
                sys.exit("serve-local: crates/, browser/pack, or Cargo.lock has uncommitted changes; the pack is built from HEAD")
            run(NICE + ["bash", ROOT / "browser/pack/build.sh", fork_build, built], env={"FORK_SOURCE": str(fork_source)})
        pack = built / "pack"
    pack_id = tomllib.loads((pack / "pack-manifest.toml").read_text())["pack_id"]
    log(f"pack {pack} ({pack_id})")

    # ---- 2. release
    run_dir = state / "run"
    publish = run_dir / "publish"
    release_key = {"pack": str(pack), "pack_id": pack_id, "fork_build": str(fork_build), "fork_revision": fork_rev,
                   "cargo_target_root": str(target_root), "inputs": inputs_key(RELEASE_INPUTS)}
    stamp = run_dir / "serve-local.json"
    if args.rebuild_release or read_json(stamp) != release_key or not (publish / "index.json").is_file():
        stamp.unlink(missing_ok=True)
        run(NICE + ["python3", ROOT / "tests/browser-pack/run.py", "--pack", pack, "--fork-build", fork_build, "--fork-source", fork_source,
                    "--out", run_dir, "--steps", "modules,stage,oracle,licenses,release"],
            env={"CARGO_TARGET_ROOT": str(target_root), "PYTHONDONTWRITEBYTECODE": "1"})
        stamp.write_text(json.dumps(release_key, indent=1) + "\n")
    else:
        log(f"release in {publish} is current")
    release_sha = json.loads((publish / "index.json").read_text())["active"]["sha256"]

    # ---- 3. site
    site_stamp = SITE / "dist/.serve-local.json"
    site_key = {"pack_base": pack_base, "inputs": inputs_key(SITE_INPUTS)}
    if args.rebuild_site or read_json(site_stamp) != site_key or not (SITE / "dist/serve-node.js").is_file():
        env = {"VITE_KRS_BROWSER_PACK_BASE": pack_base}
        run(NICE + ["bun", "run", "build:lesson-worker"], cwd=SITE, env=env)
        run(NICE + ["bun", "x", "vocs", "build"], cwd=SITE, env=env)
        site_stamp.write_text(json.dumps(site_key, indent=1) + "\n")
    else:
        log(f"site build in {SITE / 'dist'} is current (pack base {pack_base})")
    if args.prepare_only:
        log(f"prepared: release {release_sha} in {publish}; site built for {pack_base}")
        return 0

    # ---- 4. serve
    procs: list[subprocess.Popen] = []

    def stop(*_: object) -> None:
        for p in procs:
            if p.poll() is None:
                os.killpg(p.pid, signal.SIGTERM)
        for p in procs:
            try:
                p.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()

    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    try:
        procs.append(subprocess.Popen(["python3", HERE / "release.py", "serve", publish, "--bind", "127.0.0.1", "--port", str(args.pack_port)],
                                      env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}, stdout=subprocess.DEVNULL, start_new_session=True))
        procs.append(subprocess.Popen(["node", "dist/serve-node.js"], cwd=SITE, env={**os.environ, "HOST": "127.0.0.1", "PORT": str(args.site_port)},
                                      stdout=subprocess.DEVNULL, start_new_session=True))
        wait_http(f"http://127.0.0.1:{args.pack_port}/index.json", procs[0], "release.py serve")
        wait_http(f"http://127.0.0.1:{args.site_port}/", procs[1], "the docs site")
        print(f"\n  lesson:  http://127.0.0.1:{args.site_port}/lessons/tour-minimal\n"
              f"  site:    http://127.0.0.1:{args.site_port}/\n"
              f"  release: {release_sha} at http://127.0.0.1:{args.pack_port}/ (site built for {pack_base})\n"
              "  Ctrl-C stops both servers.\n", flush=True)
        while all(p.poll() is None for p in procs):
            time.sleep(0.5)
        dead = next(p for p in procs if p.poll() is not None)
        log(f"{' '.join(str(a) for a in dead.args)} exited with {dead.returncode}; stopping")
        return 1
    except KeyboardInterrupt:
        log("stopping")
        return 0
    finally:
        stop()


if __name__ == "__main__":
    sys.exit(main())
