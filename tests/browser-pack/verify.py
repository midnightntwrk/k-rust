#!/usr/bin/env python3
"""Browser pack reproducibility and release gate.

  PYTHONDONTWRITEBYTECODE=1 python3 tests/browser-pack/verify.py --check --staged DIR
      [--publish DIR] [--oracle ORACLE_TOML] [--no-checkout] [--out FILE]
  PYTHONDONTWRITEBYTECODE=1 python3 tests/browser-pack/verify.py --falsify --staged DIR [--out FILE]
  PYTHONDONTWRITEBYTECODE=1 python3 tests/browser-pack/verify.py --rebuild --fork-build DIR
      [--fork-source DIR] [--scratch DIR] [--against PACK] [--evidence DIR]

--check (light; needs no fork build) verifies a staged asset directory
(browser/worker/scripts/stage-assets.ts output, or `release.py fetch` output):
  * pack/: every [[artifact]] byte count and SHA-256, no extra file, pack_id (browser/pack/manifest.py verify);
  * pack.json: pack_id, every PackAsset's bytes and SHA-256, the recomputed pack_id, and one crates/
    tree for pack, modules, and (unless --no-checkout) the checkout's HEAD:crates;
  * licenses/licenses.toml: covers exactly the release assets with their current hashes, every component has an
    SPDX expression, every notice file exists with its hash and no notice file is unreferenced, and status
    agrees with the recorded gaps;
  * with --oracle: oracle.toml is for the checkout's crates/ tree and its bundle files have the recorded hashes;
  * with --publish: index.json, the release manifest named by its SHA-256, every blob named by the SHA-256 of its
    bytes, the release's asset table equal to the staged directory, the oracle hash equal to oracle.toml's, and
    _headers equal to the rendering of browser/release/hosting.toml.
--falsify runs --check on two corrupted hard-link copies of the staged directory (one flipped byte in an rlib,
one [[asset]] entry removed from licenses.toml) and fails unless both are rejected.
--rebuild (heavy) runs browser/pack/build.sh twice into fresh directories and compares every pack file byte for
byte; it waits for the 1-minute load average, and build.sh itself takes the heavy-build flock and runs at
nice -n 19 ionice -c3 with -j JOBS (default 4).
"""

from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import time
import tomllib
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, entry  # noqa: E402
from support.checkouts import git, git_revision  # noqa: E402
from support.hashing import sha256_bytes, sha256_file, sha256_text  # noqa: E402
from support.process import BASE_ENVIRONMENT, run  # noqa: E402
from support.tools import scratch_root  # noqa: E402

HERE = Path(__file__).resolve().parent
LOAD_MAX = float(os.environ.get("LOAD_MAX", "40"))


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


manifest_py = load_module("krs_pack_manifest", ROOT / "browser/pack/manifest.py")
release_py = load_module("krs_release", ROOT / "browser/release/release.py")


def log(message: str) -> None:
    print(f"[browser-pack] {message}", file=sys.stderr, flush=True)


# ------------------------------------------------------------------ --check

class Check:
    def __init__(self) -> None:
        self.problems: list[str] = []
        self.passed: list[str] = []

    def section(self, name: str, problems: list[str]) -> None:
        if problems:
            self.problems += [f"{name}: {p}" for p in problems]
        else:
            self.passed.append(name)


def check_pack(staged: Path) -> list[str]:
    import contextlib
    import io
    err = io.StringIO()
    with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
        rc = manifest_py.verify(argparse.Namespace(pack=str(staged / "pack")))
    return [] if rc == 0 else [line.removeprefix("verify: ") for line in err.getvalue().splitlines()] or ["manifest.py verify failed"]


def check_pack_json(staged: Path, manifest: dict[str, Any], require_checkout: bool) -> list[str]:
    problems = []
    pack = json.loads((staged / "pack.json").read_text())
    if pack["pack_id"] != manifest["pack_id"]:
        problems.append(f"pack.json pack_id {pack['pack_id']} differs from pack-manifest.toml {manifest['pack_id']}")
    assets = [pack["compiler"]["rustc"], pack["compiler"]["sysroot_bundle"], pack["modules"]["policy"], pack["modules"]["expander"],
              *pack["artifacts"], *pack["framework_sources"]]
    for a in assets:
        path = staged / a["path"]
        if not path.is_file():
            problems.append(f"{a['path']} is missing")
        elif path.stat().st_size != a["bytes"] or sha256_file(path) != a["sha256"]:
            problems.append(f"{a['path']}: bytes or sha256 differ from pack.json")
    root = pack["integrity"]["root"] + "/"
    lines = sorted(f"{a['sha256']}  {a['path'][len(root):]}\n" for a in assets if a["path"].startswith(root))
    recomputed = "sha256:" + sha256_text("".join(lines))
    if recomputed != pack["pack_id"]:
        problems.append(f"pack.json assets recompute to {recomputed}, not {pack['pack_id']}")
    trees = {i["name"]: i.get("git_tree") for i in manifest["input"] if i["kind"] == "git-tree"}
    crates = {"pack-manifest.toml": trees.get("KRS crates/ tree"), "pack.json": pack["crates_tree"], "modules": pack["modules"]["crates_tree"]}
    if require_checkout:
        crates["checkout HEAD"] = git(ROOT, "rev-parse", "HEAD:crates")
        if git(ROOT, "status", "--porcelain", "--", "crates", "Cargo.lock"):
            problems.append("crates/ or Cargo.lock has uncommitted changes")
    if len(set(crates.values())) != 1:
        problems.append("crates/ trees differ: " + ", ".join(f"{k} {v}" for k, v in crates.items()))
    if pack["fork_revision"] != manifest["compiler"]["fork_revision"]:
        problems.append("pack.json fork_revision differs from the pack manifest")
    return problems


def check_licenses(staged: Path, manifest: dict[str, Any]) -> tuple[list[str], dict[str, Any]]:
    problems: list[str] = []
    path = staged / "licenses/licenses.toml"
    if not path.is_file():
        return ["licenses/licenses.toml is missing"], {}
    lic = tomllib.loads(path.read_text())
    if lic.get("kind") != release_py.LICENSES_KIND or lic.get("schema_version") != 1:
        problems.append("wrong kind or schema_version")
    if lic.get("pack_id") != manifest["pack_id"]:
        problems.append(f"pack_id {lic.get('pack_id')} is not the pack's")
    if lic.get("publication_review") != "required":
        problems.append("publication_review must be \"required\"")
    assets = release_py.staged_assets(staged, exclude_licenses=True)
    listed = {a["id"]: a for a in lic.get("asset", [])}
    for missing in sorted(set(assets) - set(listed)):
        problems.append(f"asset {missing} has no license entry")
    for extra in sorted(set(listed) - set(assets)):
        problems.append(f"license entry for {extra}, which is not a release asset")
    comps = {c["id"]: c for c in lic.get("component", [])}
    for aid, a in listed.items():
        if aid in assets and sha256_file(assets[aid]) != a["sha256"]:
            problems.append(f"{aid}: sha256 differs from the license inventory (stale licenses.toml)")
        if not a["components"]:
            problems.append(f"{aid}: no component")
        for cid in a["components"]:
            if cid not in comps:
                problems.append(f"{aid}: unknown component {cid}")
            elif aid not in comps[cid]["assets"]:
                problems.append(f"{aid}: component {cid} does not list it")
    referenced = set()
    for c in comps.values():
        if not c.get("spdx"):
            problems.append(f"{c['id']}: no SPDX expression")
        notices = c.get("notice", [])
        if (c.get("notice_status") == "present") != bool(notices):
            problems.append(f"{c['id']}: notice_status {c.get('notice_status')} with {len(notices)} notice files")
        for n in notices:
            f = staged / "licenses" / n["path"]
            referenced.add(n["path"])
            if not f.is_file():
                problems.append(f"{c['id']}: notice {n['path']} is missing")
            elif sha256_file(f) != n["sha256"]:
                problems.append(f"{c['id']}: notice {n['path']} has another sha256")
        needs_gap = c.get("license_status") != "declared" or (c.get("notice_status") == "missing" and c.get("assets"))
        if needs_gap and not c.get("gap"):
            problems.append(f"{c['id']}: {c.get('license_status')} license / {c.get('notice_status')} notice without a recorded gap")
    on_disk = {p.relative_to(staged / "licenses").as_posix() for p in (staged / "licenses/notices").rglob("*") if p.is_file()} if (staged / "licenses/notices").is_dir() else set()
    for stray in sorted(on_disk - referenced):
        problems.append(f"unreferenced notice file {stray}")
    gaps = sorted(cid for cid, c in comps.items() if c.get("gap"))
    if (lic.get("status") == "complete") != (not gaps):
        problems.append(f"status {lic.get('status')} with {len(gaps)} components with gaps")
    summary = {"status": lic.get("status"), "components": len(comps), "components_with_gaps": gaps,
               "notice_missing": lic.get("summary", {}).get("notice_missing", []),
               "license_inferred": lic.get("summary", {}).get("license_inferred", [])}
    return problems, summary


def check_oracle(oracle_path: Path, require_checkout: bool) -> tuple[list[str], dict[str, Any]]:
    problems = []
    oracle = tomllib.loads(oracle_path.read_text())
    if require_checkout and oracle["validity"]["crates_tree"] != git(ROOT, "rev-parse", "HEAD:crates"):
        problems.append(f"oracle.toml is for crates tree {oracle['validity']['crates_tree']}, the checkout has {git(ROOT, 'rev-parse', 'HEAD:crates')}")
    for key in ("oracle", "oracle_e1"):
        rec = oracle[key]
        f = Path(rec["bundle"])
        if not f.is_file() or sha256_file(f) != rec["bundle_sha256"]:
            problems.append(f"{rec['bundle']} does not have the recorded sha256")
    return problems, oracle


def check_publish(publish: Path, staged: Path, oracle: dict[str, Any] | None, require_checkout: bool) -> tuple[list[str], dict[str, Any]]:
    problems = []
    index = json.loads((publish / "index.json").read_text())
    if index.get("kind") != release_py.INDEX_KIND:
        problems.append("index.json has the wrong kind")
    rpath = publish / index["active"]["release"]
    raw = rpath.read_bytes()
    rsha = sha256_bytes(raw)
    if rpath.name != f"{rsha}.json" or index["active"]["sha256"] != rsha:
        problems.append(f"release {rpath.name} hashes to {rsha}")
    release = json.loads(raw)
    if release.get("kind") != release_py.RELEASE_KIND or release.get("schema") != 1:
        problems.append("release manifest has the wrong kind or schema")
    if index["active"]["pack_id"] != release["pack_id"]:
        problems.append("index.json pack_id differs from the release")
    hosting = release_py.hosting_rules()
    staged_ids = release_py.staged_assets(staged)
    rel_ids = {a["id"]: a for a in release["assets"]}
    for missing in sorted(set(staged_ids) - set(rel_ids)):
        problems.append(f"staged asset {missing} is not in the release")
    for extra in sorted(set(rel_ids) - set(staged_ids)):
        problems.append(f"release asset {extra} is not in the staged directory")
    for aid, a in rel_ids.items():
        for field in ("id", "role", "url", "required_media_type", "decoded_bytes", "decoded_sha256", "cache_policy"):
            if field not in a:
                problems.append(f"{aid}: missing required field {field}")
        blob = publish / a["url"]
        if not a["url"].startswith(f"blobs/{a['decoded_sha256']}"):
            problems.append(f"{aid}: url {a['url']} does not carry its sha256")
        if not blob.is_file() or blob.stat().st_size != a["decoded_bytes"] or sha256_file(blob) != a["decoded_sha256"]:
            problems.append(f"{aid}: blob {a['url']} is missing or has other bytes")
        if aid in staged_ids and sha256_file(staged_ids[aid]) != a["decoded_sha256"]:
            problems.append(f"{aid}: staged bytes differ from the release")
        rules = release_py.matching_rules(a["url"], hosting)
        if len(rules) != 1:
            problems.append(f"{aid}: {a['url']} matches {len(rules)} hosting.toml rules {rules} (must be exactly one)")
        want = release_py.headers_for(a["url"], hosting)
        if want is None or want["Content-Type"].split(";")[0] != a["required_media_type"]:
            problems.append(f"{aid}: required_media_type {a['required_media_type']} differs from hosting.toml")
        if a["role"] == "compiler" and a["required_media_type"] != "application/wasm":
            problems.append("rustc.wasm must be served as application/wasm")
    for role, entry in release["roles"].items():
        if entry.get("status") == "present" and not entry.get("assets"):
            problems.append(f"role {role} is present without assets")
    if require_checkout and release["krs"]["crates_tree"] != git(ROOT, "rev-parse", "HEAD:crates"):
        problems.append("release crates_tree differs from the checkout")
    if oracle is not None and (release["oracle"]["bundle_sha256"] != oracle["oracle"]["bundle_sha256"]
                               or release["oracle"]["e1_bundle_sha256"] != oracle["oracle_e1"]["bundle_sha256"]):
        problems.append("release oracle hashes differ from oracle.toml")
    headers = publish / "_headers"
    if not headers.is_file() or headers.read_text() != release_py.render_headers_file(hosting):
        problems.append("_headers is missing or differs from hosting.toml")
    return problems, {"release": f"releases/{rsha}.json", "release_sha256": rsha, "pack_id": release["pack_id"],
                      "assets": len(release["assets"]), "blob_bytes": sum(a["decoded_bytes"] for a in release["assets"])}


def run_check(staged: Path, publish: Path | None, oracle_path: Path | None, require_checkout: bool) -> dict[str, Any]:
    c = Check()
    staged = staged.resolve()
    manifest = tomllib.loads((staged / "pack/pack-manifest.toml").read_text())
    c.section("pack", check_pack(staged))
    c.section("pack.json", check_pack_json(staged, manifest, require_checkout))
    lic_problems, lic_summary = check_licenses(staged, manifest)
    c.section("licenses", lic_problems)
    oracle = None
    if oracle_path:
        o_problems, oracle = check_oracle(oracle_path, require_checkout)
        c.section("oracle", o_problems)
    rel_summary = None
    if publish:
        r_problems, rel_summary = check_publish(publish.resolve(), staged, oracle, require_checkout)
        c.section("release", r_problems)
    return {"mode": "check", "staged": str(staged), "pack_id": manifest["pack_id"], "fork_revision": manifest["compiler"]["fork_revision"],
            "pass": not c.problems, "passed": c.passed, "problems": c.problems, "licenses": lic_summary, "release": rel_summary}


# ------------------------------------------------------------------ --falsify

def link_copy(src: Path, dst: Path) -> None:
    if dst.exists():
        shutil.rmtree(dst)
    for rel, path in release_py.staged_assets(src).items():
        target = dst / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        os.link(path.resolve(), target)


def replace_file(path: Path, data: bytes) -> None:
    path.unlink()
    path.write_bytes(data)


def run_falsify(staged: Path, scratch: Path) -> dict[str, Any]:
    results = []
    manifest = tomllib.loads((staged / "pack/pack-manifest.toml").read_text())
    rlib = next(a["path"] for a in manifest["artifact"] if a["role"] == "target-rlib")
    # 1. one flipped byte in an rlib (length unchanged)
    case = scratch / "flipped-byte"
    link_copy(staged, case)
    target = case / "pack" / rlib
    data = bytearray(target.read_bytes())
    data[len(data) // 2] ^= 0x01
    replace_file(target, bytes(data))
    r = run_check(case, None, None, False)
    results.append({"case": "flipped-byte", "file": f"pack/{rlib}", "rejected": not r["pass"], "problems": r["problems"][:6]})
    # 2. a missing license entry
    case = scratch / "missing-license-entry"
    link_copy(staged, case)
    lic = case / "licenses/licenses.toml"
    text = lic.read_text()
    start = text.index("\n[[asset]]\nid = \"pack/" + rlib + "\"")
    end = text.find("\n[[asset]]", start + 1)
    replace_file(lic, (text[:start] + (text[end:] if end != -1 else "\n")).encode())
    r = run_check(case, None, None, False)
    results.append({"case": "missing-license-entry", "file": f"pack/{rlib}", "rejected": not r["pass"], "problems": r["problems"][:6]})
    shutil.rmtree(scratch)
    return {"mode": "falsify", "pass": all(x["rejected"] for x in results), "cases": results}


# ------------------------------------------------------------------ --rebuild

def wait_for_load() -> str:
    uptime = run(["uptime"], check=False).stdout.strip()
    log(f"uptime: {uptime}")
    while os.getloadavg()[0] > LOAD_MAX:
        log(f"1-minute load {os.getloadavg()[0]:.1f} > {LOAD_MAX}; waiting 60 s")
        time.sleep(60)
    return uptime


def du_bytes(path: Path) -> int:
    return int(run(["du", "-sb", path]).stdout.split()[0])


def pack_files(pack: Path) -> dict[str, str]:
    return {p.relative_to(pack).as_posix(): sha256_file(p) for p in sorted(pack.rglob("*")) if p.is_file()}


def run_rebuild(args: argparse.Namespace) -> dict[str, Any]:
    scratch = args.scratch.resolve()
    scratch.mkdir(parents=True, exist_ok=True)
    runs = []
    for label in ("a", "b"):
        out = scratch / f"rebuild-{label}"
        if out.exists():
            shutil.rmtree(out)
        uptime = wait_for_load()
        env = {**os.environ, **BASE_ENVIRONMENT, "JOBS": str(args.jobs), "LOAD_MAX": str(int(LOAD_MAX))}
        if args.fork_source:
            env["FORK_SOURCE"] = str(args.fork_source.resolve())
        log(f"rebuild {label}: browser/pack/build.sh {args.fork_build} {out}")
        t0 = time.monotonic()
        rc = subprocess.run(["bash", str(ROOT / "browser/pack/build.sh"), str(args.fork_build.resolve()), str(out)], env=env).returncode
        wall = time.monotonic() - t0
        if rc != 0:
            return {"mode": "rebuild", "pass": False, "problems": [f"build {label} failed with {rc}"]}
        stats = tomllib.loads((out / "build/build-stats.toml").read_text())
        runs.append({"label": label, "out": str(out), "wall_s_total": round(wall, 1), "cargo_wall_s": stats["wall_s"],
                     "memory_peak_bytes": stats["memory_peak_bytes"], "jobs": stats["jobs"], "load_at_start": stats["load_at_start"],
                     "uptime_before": uptime, "disk_bytes": du_bytes(out), "pack_bytes": du_bytes(out / "pack"),
                     "pack_id": tomllib.loads((out / "pack/pack-manifest.toml").read_text())["pack_id"]})
    a, b = (pack_files(scratch / f"rebuild-{x}/pack") for x in ("a", "b"))
    problems = [f"{p}: only in {'a' if p in a else 'b'}" for p in sorted(set(a) ^ set(b))]
    problems += [f"{p}: differs" for p in sorted(set(a) & set(b)) if a[p] != b[p]]
    against = None
    if args.against:
        c = pack_files(args.against.resolve())
        ca = {p: h for p, h in c.items() if p != "pack-manifest.toml"}
        aa = {p: h for p, h in a.items() if p != "pack-manifest.toml"}
        diff = sorted(p for p in set(ca) | set(aa) if ca.get(p) != aa.get(p))
        against = {"pack": str(args.against), "artifacts_equal": not diff, "differing": diff[:20],
                   "pack_id_equal": runs[0]["pack_id"] == tomllib.loads((args.against / "pack-manifest.toml").read_text())["pack_id"]}
    if args.evidence:
        args.evidence.mkdir(parents=True, exist_ok=True)
        for label, files in (("a", a), ("b", b)):
            (args.evidence / f"rebuild-{label}.sha256").write_text("".join(f"{h}  {p}\n" for p, h in files.items()))
    return {"mode": "rebuild", "pass": not problems, "files": len(a), "problems": problems, "runs": runs, "against": against,
            "date": datetime.date.today().isoformat(), "krs_revision": git_revision(ROOT)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--falsify", action="store_true")
    mode.add_argument("--rebuild", action="store_true")
    parser.add_argument("--staged", type=Path)
    parser.add_argument("--publish", type=Path)
    parser.add_argument("--oracle", type=Path)
    parser.add_argument("--no-checkout", action="store_true", help="do not compare with the checkout's crates/ tree")
    parser.add_argument("--fork-build", type=Path)
    parser.add_argument("--fork-source", type=Path)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--scratch", type=Path, default=scratch_root() / "krs-browser-pack-verify",
                        help="--rebuild and --falsify workspace (--falsify uses and removes SCRATCH/falsify; hard links need the staged directory's filesystem)")
    parser.add_argument("--against", type=Path, help="--rebuild: also compare build A's artifacts with this pack")
    parser.add_argument("--evidence", type=Path, help="--rebuild: write rebuild-a.sha256 and rebuild-b.sha256 here")
    parser.add_argument("--out", type=Path, help="write the JSON result here")
    args = parser.parse_args()
    if args.check:
        if not args.staged:
            parser.error("--check needs --staged")
        result = run_check(args.staged, args.publish, args.oracle, not args.no_checkout)
    elif args.falsify:
        if not args.staged:
            parser.error("--falsify needs --staged")
        result = run_falsify(args.staged.resolve(), args.scratch.resolve() / "falsify")
    else:
        if not args.fork_build:
            parser.error("--rebuild needs --fork-build")
        result = run_rebuild(args)
    text = json.dumps(result, indent=1) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text)
    for p in result.get("problems", []):
        log(f"FAIL {p}")
    log(f"{result['mode']}: {'PASS' if result['pass'] else 'FAIL'}")
    print(text, end="")
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    entry("browser-pack", main)
