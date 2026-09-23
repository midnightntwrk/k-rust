#!/usr/bin/env python3
"""KRS browser-lesson release: license inventory, content-addressed publication, fetch, and local hosting (IR-21).

Python 3 standard library only (plus `cargo +stable` for the license walk).
Formats: release-format.toml (release manifest and index), hosting.toml (HTTP headers),
licenses-manual.toml (hand-maintained license input).

A *staged asset directory* is what browser/worker/scripts/stage-assets.ts writes:
  pack/                      the IR-14 pack (pack-manifest.toml and its artifacts)
  modules/                   krs_lesson_policy.wasm, krs_expand_wasm.wasm
  pack.json                  the worker's PackManifest
  lessons/<lesson>/...       lesson manifests and sources
`licenses` adds licenses/ to it; `assemble` publishes it content-addressed; `fetch`
reconstructs it from a host. An asset id is a path relative to the staged directory.

Usage:
  release.py licenses --staged DIR --fork-source DIR --fork-build DIR [--repo DIR] [--manual FILE]
  release.py assemble --staged DIR --publish DIR --oracle ORACLE_TOML [--repo DIR] [--activate]
  release.py fetch --base-url URL (--release SHA256 | --index) --out DIR [--check-headers] [--expect-cors]
  release.py serve DIR [--port 8741] [--bind 127.0.0.1]
  release.py derive-generation --staged DIR --out DIR     (test-only: a second, valid pack generation)
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import http.server
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tomllib
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
DEFAULT_REPO = HERE.parents[1]
MANUAL = HERE / "licenses-manual.toml"
HOSTING = HERE / "hosting.toml"
RELEASE_KIND = "krs-browser-lesson-release"
INDEX_KIND = "krs-browser-lesson-index"
LICENSES_KIND = "krs-browser-lesson-licenses"
NOTICE_RE = re.compile(r"^(LICEN[CS]E|COPYING|COPYRIGHT|NOTICE|UNLICENSE)([-._].*)?$", re.I)
KNOWN_EXT = (".wasm", ".json", ".toml", ".txt", ".rs", ".rlib", ".rmeta", ".bundle")
IMMUTABLE = "public, max-age=31536000, immutable"
DROP_LICENSE: set[str] = set()  # test-only: crate ids whose license field is treated as absent


def die(message: str) -> None:
    print(f"release.py: {message}", file=sys.stderr)
    sys.exit(1)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True, text=True).stdout.strip()


def staged_assets(staged: Path, exclude_licenses: bool = False) -> dict[str, Path]:
    out = {}
    for path in sorted(staged.rglob("*")):
        if path.is_file() or (path.is_symlink() and path.resolve().is_file()):
            rel = path.relative_to(staged).as_posix()
            if rel.startswith("."):
                continue  # fetch bookkeeping (.release.json), not an asset
            if exclude_licenses and rel.startswith("licenses/"):
                continue
            out[rel] = path
    return out


# ------------------------------------------------------------------ TOML writer (the subset licenses.toml uses)

def toml_value(v: Any) -> str:
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return json.dumps(v, ensure_ascii=False)
    if isinstance(v, list):
        if not v:
            return "[]"
        if all(not isinstance(x, (dict, list)) for x in v) and sum(len(toml_value(x)) for x in v) < 80:
            return "[" + ", ".join(toml_value(x) for x in v) + "]"
        return "[\n" + "".join(f"  {toml_value(x)},\n" for x in v) + "]"
    if isinstance(v, dict):
        return "{ " + ", ".join(f"{toml_key(k)} = {toml_value(x)}" for k, x in v.items()) + " }"
    raise TypeError(type(v))


def toml_key(k: str) -> str:
    return k if re.fullmatch(r"[A-Za-z0-9_-]+", k) else json.dumps(k)


def toml_table(out: list[str], header: str | None, table: dict[str, Any]) -> None:
    if header:
        out.append(f"\n{header}")
    for k, v in table.items():
        if v is None:
            continue
        out.append(f"{toml_key(k)} = {toml_value(v)}")


# ------------------------------------------------------------------ licenses

class Inventory:
    def __init__(self, out: Path, placeholders: dict[str, Path]):
        self.out = out
        self.placeholders = placeholders
        self.components: dict[str, dict[str, Any]] = {}
        self.errors: list[str] = []

    def expand(self, text: str) -> Path:
        for key, value in self.placeholders.items():
            text = text.replace(f"<{key}>", str(value))
        return Path(text)

    def component(self, cid: str, **fields: Any) -> dict[str, Any]:
        c = self.components.get(cid)
        if c is None:
            c = {"id": cid, "sections": [], "assets": [], "notices": [], **fields}
            self.components[cid] = c
        else:
            for k, v in fields.items():
                if k in ("sections", "assets", "notices"):
                    continue
                if k not in c or c[k] in (None, ""):
                    c[k] = v
        return c

    def ship(self, cid: str, section: str, assets: list[str]) -> None:
        c = self.components[cid]
        if section not in c["sections"]:
            c["sections"].append(section)
        for a in assets:
            if a not in c["assets"]:
                c["assets"].append(a)

    def add_notice(self, cid: str, source: Path, label: str) -> None:
        c = self.components[cid]
        slug = re.sub(r"[^A-Za-z0-9._+-]", "-", cid)
        name = source.name
        rel = f"notices/{slug}/{name}"
        if any(n["path"] == rel for n in c["notices"]):
            return
        target = self.out / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        c["notices"].append({"path": rel, "sha256": sha256_file(target), "source": label})

    def notices_from_dir(self, cid: str, directory: Path, label: str) -> None:
        for f in sorted(directory.iterdir()):
            if f.is_file() and NOTICE_RE.match(f.name):
                self.add_notice(cid, f, f"{label}/{f.name}")


def cargo(args: list[str], cwd: Path) -> bytes:
    result = subprocess.run(["cargo", "+stable", *args], cwd=cwd, capture_output=True)
    if result.returncode != 0:
        die(f"cargo {' '.join(args)} failed:\n{result.stderr.decode(errors='replace')}")
    return result.stdout


def crate_id(name: str, version: str) -> str:
    return f"crate:{name}@{version}"


def pkg_component(inv: Inventory, pkg: dict[str, Any], overrides: dict[str, dict[str, Any]], repo: Path) -> str:
    """Component for a cargo metadata package; KRS path packages become krs:<name>."""
    source = pkg.get("source")
    if source is None:
        manifest_dir = Path(pkg["manifest_path"]).parent
        try:
            rel = manifest_dir.resolve().relative_to(repo.resolve())
        except ValueError:
            die(f"path package {pkg['name']} outside the KRS checkout: {manifest_dir}")
        cid = f"krs:{pkg['name']}"
        origin, basis = "krs", f"cargo metadata license field ({rel.as_posix()}/Cargo.toml, workspace.package)"
    elif source.startswith("registry+https://github.com/rust-lang/crates.io-index"):
        cid = crate_id(pkg["name"], pkg["version"])
        origin, basis = "crates.io", "cargo metadata license field"
    else:
        die(f"unsupported package source {source} for {pkg['name']}")
    spdx = pkg.get("license")
    status = "declared"
    if not spdx:
        o = overrides.get(cid)
        if o is None:
            inv.errors.append(f"{cid} has no license field (license_file = {pkg.get('license_file')!r}); add a [[crate_override]] to licenses-manual.toml")
            spdx, status, basis = "", "unknown", "no license field"
        else:
            spdx, basis = o["spdx"], f"manual override: {o['basis']}"
    if cid in DROP_LICENSE:
        spdx = ""  # test-only fault (--test-drop-license)
        if cid not in overrides:
            inv.errors.append(f"{cid} has no license field (test-only --test-drop-license); add a [[crate_override]] to licenses-manual.toml")
            status, basis = "unknown", "no license field"
    new = cid not in inv.components
    inv.component(cid, name=pkg["name"], version=pkg["version"], origin=origin, spdx=spdx, license_status=status, basis=basis)
    if new and source is not None:
        inv.notices_from_dir(cid, Path(pkg["manifest_path"]).parent, f"crates.io package {pkg['name']} {pkg['version']}")
    return cid


def walk_pack_metadata(meta: dict[str, Any]) -> tuple[set[str], set[str], set[str]]:
    """(shipped target packages, proc-macro packages, build-time packages) walked from krs and krs-compiler."""
    pkgs = {p["id"]: p for p in meta["packages"]}
    nodes = {n["id"]: n for n in meta["resolve"]["nodes"]}
    is_pm = lambda pid: any("proc-macro" in t["kind"] for t in pkgs[pid]["targets"])
    root = next(p["id"] for p in meta["packages"] if p["name"] == "krs-browser-pack")
    starts = [d["pkg"] for d in nodes[root]["deps"] if pkgs[d["pkg"]]["name"] in ("krs", "krs-compiler")]
    if len(starts) != 2:
        die("pack metadata: krs-browser-pack does not depend on both krs and krs-compiler")
    shipped, proc_macros, build_roots = set(), set(), set()
    stack = list(starts)
    while stack:
        pid = stack.pop()
        if pid in shipped:
            continue
        shipped.add(pid)
        for d in nodes[pid]["deps"]:
            kinds = {k["kind"] for k in d["dep_kinds"]}
            if None in kinds:
                if is_pm(d["pkg"]):
                    proc_macros.add(d["pkg"])
                else:
                    stack.append(d["pkg"])
            if "build" in kinds:
                build_roots.add(d["pkg"])
    build_time, stack = set(), list(proc_macros | build_roots)
    while stack:
        pid = stack.pop()
        if pid in build_time:
            continue
        build_time.add(pid)
        for d in nodes[pid]["deps"]:
            if {k["kind"] for k in d["dep_kinds"]} & {None, "build"}:
                stack.append(d["pkg"])
    return shipped, proc_macros, build_time


def artifact_key(package_id: str) -> str:
    """Match key between Cargo package ids of the build namespace (/krs) and of this checkout."""
    if package_id.startswith("registry+"):
        return package_id.split("#", 1)[1]
    m = re.match(r"path\+file://(.*?)/crates/([^#]+)#(?:[^@]+@)?(.+)$", package_id)
    if m:
        return f"crates/{m.group(2)}@{m.group(3)}"
    raise ValueError(package_id)


def tree_closure(repo: Path, package: str, target: str, edges: str) -> tuple[list[tuple[str, str]], bytes]:
    raw = cargo(["tree", "--offline", "--locked", "-p", package, "--target", target, "-e", edges,
                 "--prefix", "none", "-f", "{p}", "--no-dedupe"], repo)
    out = set()
    for line in raw.decode().splitlines():
        m = re.match(r"^(\S+) v(\S+)", line.strip())
        if m:
            out.add((m.group(1), m.group(2)))
    return sorted(out), raw


def bundle_crates(bundle: Path) -> list[str]:
    with open(bundle, "rb") as f:
        head = f.read(10)
        if head[:6] != b"RIWB1\n":
            die(f"{bundle}: not a RIWB1 bundle")
        (n,) = struct.unpack_from("<I", head, 6)
        index = json.loads(f.read(n))
    names = set()
    for entry in index["files"]:
        m = re.match(r"lib/rustlib/wasm32-wasip1/lib/lib(.+)-[0-9a-f]+\.(rlib|rmeta)$", entry["p"])
        if m:
            names.add(m.group(1))
    return sorted(names)


def licenses(args: argparse.Namespace) -> int:
    staged = args.staged.resolve()
    repo = args.repo.resolve()
    out = (args.out or staged / "licenses").resolve()
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    manual = tomllib.loads(args.manual.read_text())
    fork_source, fork_build = args.fork_source.resolve(), args.fork_build.resolve()
    inv = Inventory(out, {"fork-source": fork_source, "fork-build": fork_build, "repo": repo})
    assets = staged_assets(staged, exclude_licenses=True)
    manifest = tomllib.loads((staged / "pack" / "pack-manifest.toml").read_text())
    pack_json = json.loads((staged / "pack.json").read_text())
    overrides = {o["id"]: o for o in manual.get("crate_override", [])}
    inputs: list[dict[str, Any]] = []

    # --- identity: the checkout and the fork are the ones the pack was built from
    tree = {i["name"]: i.get("git_tree") for i in manifest["input"] if i["kind"] == "git-tree"}
    head_crates, head_pack = git(repo, "rev-parse", "HEAD:crates"), git(repo, "rev-parse", "HEAD:browser/pack")
    if tree.get("KRS crates/ tree") != head_crates or tree.get("KRS browser/pack/ tree") != head_pack:
        die(f"the checkout (crates {head_crates}, browser/pack {head_pack}) is not the pack's source "
            f"(crates {tree.get('KRS crates/ tree')}, browser/pack {tree.get('KRS browser/pack/ tree')})")
    if git(repo, "status", "--porcelain", "--", "crates", "browser/pack", "Cargo.lock"):
        die("crates/, browser/pack, or Cargo.lock has uncommitted changes")
    if pack_json["modules"]["crates_tree"] != head_crates:
        die(f"staged modules were built from crates tree {pack_json['modules']['crates_tree']}, not {head_crates}")
    fork_revision = manifest["compiler"]["fork_revision"]
    if git(fork_source, "rev-parse", "HEAD") != fork_revision:
        die(f"{fork_source} is not at the pack's fork revision {fork_revision}")
    twin_vv = subprocess.run([str(fork_build / "build/x86_64-unknown-linux-gnu/stage1/bin/rustc"), "-vV"],
                             check=True, capture_output=True, text=True).stdout
    if f"commit-hash: {fork_revision}" not in twin_vv:
        die(f"{fork_build} twin is not at {fork_revision}")

    # --- pack: cargo metadata walked from krs and krs-compiler (ticket command), checked against the artifacts
    meta_raw = cargo(["metadata", "--offline", "--locked", "--format-version", "1", "--filter-platform", "wasm32-wasip1",
                      "--manifest-path", str(repo / "browser/pack/Cargo.toml")], repo)
    inputs.append({"name": "pack cargo metadata", "command": "cargo +stable metadata --offline --locked --format-version 1 --filter-platform wasm32-wasip1 --manifest-path browser/pack/Cargo.toml", "stdout_sha256": sha256_bytes(meta_raw)})
    meta = json.loads(meta_raw)
    pkgs = {p["id"]: p for p in meta["packages"]}
    shipped, proc_macros, build_time = walk_pack_metadata(meta)

    def key_of(pid: str) -> str:
        p = pkgs[pid]
        if p.get("source"):
            return f"{p['name']}@{p['version']}"
        rel = Path(p["manifest_path"]).parent.resolve().relative_to(repo)
        return f"{rel.as_posix()}@{p['version']}"

    by_key = {key_of(pid): pid for pid in pkgs}
    art_by_key: dict[str, list[dict[str, Any]]] = {}
    for a in manifest["artifact"]:
        if a["role"] in ("target-rlib", "proc-macro-metadata"):
            art_by_key.setdefault(artifact_key(a["package_id"]), []).append(a)
    walked_target = {key_of(p) for p in shipped}
    walked_pm = {key_of(p) for p in proc_macros}
    art_target = {k for k, v in art_by_key.items() if any(a["role"] == "target-rlib" for a in v)}
    art_pm = {k for k, v in art_by_key.items() if any(a["role"] == "proc-macro-metadata" for a in v)}
    if walked_target != art_target:
        die(f"metadata walk and pack target rlibs differ: walk-only {sorted(walked_target - art_target)}, pack-only {sorted(art_target - walked_target)}")
    if walked_pm != art_pm:
        die(f"metadata walk and pack proc-macro metadata differ: {sorted(walked_pm)} vs {sorted(art_pm)}")
    for key in sorted(art_by_key):
        pid = by_key[key]
        cid = pkg_component(inv, pkgs[pid], overrides, repo)
        for a in art_by_key[key]:
            section = "pack-target-rlib" if a["role"] == "target-rlib" else "pack-proc-macro-metadata-only"
            inv.ship(cid, section, [f"pack/{a['path']}"])
    for pid in sorted(build_time, key=key_of):
        cid = pkg_component(inv, pkgs[pid], overrides, repo)
        inv.ship(cid, "pack-build-time", [])
    for a in manifest["artifact"]:
        if a["role"] == "framework-source":
            inv.ship(pkg_component(inv, pkgs[by_key["crates/krs@0.1.0"]], overrides, repo), "pack-framework-source", [f"pack/{a['path']}"])

    # --- modules: per-invocation closures (cargo tree -p, the feature set of each separate build)
    ws_raw = cargo(["metadata", "--offline", "--locked", "--format-version", "1", "--filter-platform", "wasm32-unknown-unknown"], repo)
    inputs.append({"name": "workspace cargo metadata", "command": "cargo +stable metadata --offline --locked --format-version 1 --filter-platform wasm32-unknown-unknown", "stdout_sha256": sha256_bytes(ws_raw)})
    ws = json.loads(ws_raw)
    ws_by_nv: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for p in ws["packages"]:
        ws_by_nv.setdefault((p["name"], p["version"]), []).append(p)
    modules = {"krs-lesson-policy": pack_json["modules"]["policy"]["path"], "krs-expand-wasm": pack_json["modules"]["expander"]["path"]}
    for package, asset in modules.items():
        linked, raw_linked = tree_closure(repo, package, "wasm32-unknown-unknown", "normal,no-proc-macro")
        every, raw_every = tree_closure(repo, package, "wasm32-unknown-unknown", "normal,build")
        inputs.append({"name": f"{package} linked closure", "command": f"cargo +stable tree --offline --locked -p {package} --target wasm32-unknown-unknown -e normal,no-proc-macro --prefix none -f {{p}} --no-dedupe", "stdout_sha256": sha256_bytes(raw_linked)})
        inputs.append({"name": f"{package} build closure", "command": f"cargo +stable tree --offline --locked -p {package} --target wasm32-unknown-unknown -e normal,build --prefix none -f {{p}} --no-dedupe", "stdout_sha256": sha256_bytes(raw_every)})
        for nv in every:
            candidates = ws_by_nv.get(nv, [])
            if len(candidates) != 1:
                die(f"{package}: {nv} matches {len(candidates)} workspace packages")
            cid = pkg_component(inv, candidates[0], overrides, repo)
            if nv in linked:
                inv.ship(cid, "module-linked", [asset])
            else:
                inv.ship(cid, "module-build-time", [])
        for bad in ("z3", "z3-sys"):
            if any(n == bad for n, _ in linked):
                die(f"{package} links {bad}; the Wasm feature set must not reach z3")

    # --- fork library: sysroot bundle crates and the sysroot supplement
    fl = manual["fork_library"]
    lock = tomllib.loads((fork_source / "library/Cargo.lock").read_text())
    vendor = fork_build / "build/tmp/generate-copyright-vendor"
    if not vendor.is_dir():
        die(f"{vendor} is missing (the fork build's generate-copyright step)")
    bundle_asset = "pack/" + manifest["sysroot"]["bundle"]
    library_crates = [(c, [bundle_asset]) for c in bundle_crates(staged / bundle_asset)]
    for a in manifest["artifact"]:
        if a["role"] == "sysroot-supplement":
            library_crates.append((a["crate_name"], [f"pack/{a['path']}"]))
    library_dirs: dict[str, Path] = {}
    for m in sorted((fork_source / "library").glob("**/Cargo.toml")):
        name = tomllib.loads(m.read_text()).get("package", {}).get("name")
        if isinstance(name, str):
            library_dirs.setdefault(name, m.parent)
    for crate, crate_assets in library_crates:
        candidates = [p for p in lock["package"] if p["name"].replace("-", "_") == crate]
        if len(candidates) > 1:
            pin = fl["pins"].get(candidates[0]["name"])
            candidates = [p for p in candidates if p["version"] == pin]
        if len(candidates) != 1:
            die(f"library crate {crate}: {len(candidates)} candidates in library/Cargo.lock (add a [fork_library] pin)")
        p = candidates[0]
        if p.get("source"):
            vdir = vendor / f"{p['name']}-{p['version']}"
            vmeta = tomllib.loads((vdir / "Cargo.toml").read_text())["package"]
            cid = crate_id(p["name"], p["version"])
            spdx = vmeta.get("license") or ""
            if not spdx:
                inv.errors.append(f"{cid} (fork library) has no license field")
            new = cid not in inv.components
            inv.component(cid, name=p["name"], version=p["version"], origin="crates.io", spdx=spdx, license_status="declared",
                          basis="license field of the fork build's vendored copy (generate-copyright-vendor)")
            if new:
                inv.notices_from_dir(cid, vdir, f"<fork-build>/build/tmp/generate-copyright-vendor/{vdir.name}")
            inv.ship(cid, "fork-sysroot", crate_assets)
        else:
            path = library_dirs.get(p["name"])
            if path is None:
                die(f"in-tree library crate {p['name']} not found under {fork_source}/library")
            spdx_field = tomllib.loads((path / "Cargo.toml").read_text()).get("package", {}).get("license")
            rel = path.relative_to(fork_source).as_posix()
            cid = f"fork-library:{p['name']}"
            if isinstance(spdx_field, str) and spdx_field:
                spdx, basis = spdx_field, f"<fork-source>/{rel}/Cargo.toml license field"
            else:
                spdx, basis = fl["default_spdx"], fl["default_basis"]
            new = cid not in inv.components
            inv.component(cid, name=p["name"], version=p["version"], origin="fork", spdx=spdx, license_status="declared", basis=basis)
            if new:
                for n in fl["in_tree_notices"]:
                    inv.add_notice(cid, inv.expand(n), n)
            inv.ship(cid, "fork-sysroot", crate_assets)

    # --- compiler: crates the ticket names, from the fork build's vendor directory
    compiler_asset = "pack/" + manifest["compiler"]["rustc_wasm"]
    for spec in manual["compiler"]["named_vendored_crates"]:
        name, version = spec.split("@")
        vdir = vendor / f"{name}-{version}"
        vmeta = tomllib.loads((vdir / "Cargo.toml").read_text())["package"]
        cid = crate_id(name, version)
        spdx = vmeta.get("license") or ""
        if not spdx:
            inv.errors.append(f"{cid} (compiler) has no license field")
        new = cid not in inv.components
        inv.component(cid, name=name, version=version, origin="crates.io", spdx=spdx, license_status="declared",
                      basis="license field of the fork build's vendored copy (generate-copyright-vendor)")
        if new:
            inv.notices_from_dir(cid, vdir, f"<fork-build>/build/tmp/generate-copyright-vendor/{vdir.name}")
        inv.ship(cid, "fork-compiler", [compiler_asset])

    # --- manual components
    for m in manual.get("component", []):
        fields = {k: v for k, v in m.items() if k not in ("id", "notices", "assets")}
        inv.component(m["id"], **fields)
        for n in m.get("notices", []):
            path = inv.expand(n)
            if not path.is_file():
                die(f"{m['id']}: notice {path} does not exist")
            inv.add_notice(m["id"], path, n)
        matched = []
        for pattern in m.get("assets", []):
            if pattern.startswith("site:"):
                matched.append(pattern)
                continue
            hits = [a for a in assets if fnmatch.fnmatch(a, pattern)]
            if not hits:
                die(f"{m['id']}: asset pattern {pattern} matches no staged asset")
            matched += hits
        for a in matched:
            section = ("site" if a.startswith("site:") else "fork-compiler" if a == compiler_asset
                       else "fork-sysroot" if a == bundle_asset else "release")
            inv.ship(m["id"], section, [a])

    # --- statuses, gaps, coverage
    gaps = manual.get("acknowledged_gap", [])
    acknowledged = lambda cid, kind: any(fnmatch.fnmatch(cid, g["component"]) and g["kind"] == kind for g in gaps)
    used_gaps: set[int] = set()
    for c in inv.components.values():
        c["notice_status"] = "present" if c["notices"] else "missing"
        c.setdefault("license_status", "declared")
        problems = []
        if not c.get("spdx"):
            problems.append("license-unknown")
        elif c["license_status"] == "inferred":
            problems.append("license-inferred")
        if c["notice_status"] == "missing" and c["assets"]:
            problems.append("notice-missing")
        c["gaps"] = []
        for kind in problems:
            if kind == "license-unknown":
                inv.errors.append(f"{c['id']}: no license expression")
                continue
            if not acknowledged(c["id"], kind):
                inv.errors.append(f"{c['id']}: {kind} and not in licenses-manual.toml [[acknowledged_gap]]")
            else:
                for i, g in enumerate(gaps):
                    if fnmatch.fnmatch(c["id"], g["component"]) and g["kind"] == kind:
                        used_gaps.add(i)
                        c["gaps"].append({"kind": kind, "reason": g["reason"]})
    for i, g in enumerate(gaps):
        if i not in used_gaps:
            inv.errors.append(f"acknowledged gap {g['component']} {g['kind']} matches no open gap (remove it)")
    coverage = {a: sorted(c["id"] for c in inv.components.values() if a in c["assets"]) for a in assets}
    for a, cids in coverage.items():
        if not cids:
            inv.errors.append(f"staged asset {a} is covered by no component")
    if inv.errors:
        inv.errors = list(dict.fromkeys(inv.errors))
        for e in inv.errors:
            print(f"licenses: {e}", file=sys.stderr)
        print(f"licenses: FAIL ({len(inv.errors)} problems); {out / 'licenses.toml'} not written", file=sys.stderr)
        return 1

    # --- write
    comps = sorted(inv.components.values(), key=lambda c: c["id"])
    gap_components = sorted({c["id"] for c in comps if c["gaps"]})
    doc: list[str] = ["# KRS browser-lesson license inventory (generated by browser/release/release.py licenses; format: browser/release/release-format.toml [licenses]).",
                      "# A record of obligations, not a licensing conclusion. Publication requires Sebastien's review."]
    toml_table(doc, None, {"schema_version": 1, "kind": LICENSES_KIND, "pack_id": manifest["pack_id"],
                           "status": "incomplete" if gap_components else "complete", "publication_review": "required"})
    toml_table(doc, "[generator]", {
        "command": "browser/release/release.py licenses",
        "krs_crates_tree": head_crates,
        "krs_pack_tree": head_pack,
        "fork_revision": fork_revision,
        "manual_sha256": sha256_file(args.manual),
        "cargo_version": subprocess.run(["cargo", "+stable", "-V"], capture_output=True, text=True).stdout.strip(),
    })
    for i in inputs:
        toml_table(doc, "[[generator.input]]", i)
    toml_table(doc, "[summary]", {
        "components": len(comps),
        "release_assets": len(assets),
        "components_with_gaps": gap_components,
        "license_inferred": sorted(c["id"] for c in comps if any(g["kind"] == "license-inferred" for g in c["gaps"])),
        "notice_missing": sorted(c["id"] for c in comps if any(g["kind"] == "notice-missing" for g in c["gaps"])),
    })
    for c in comps:
        row = {k: c.get(k) for k in ("id", "name", "version", "origin", "spdx", "license_status", "basis", "notice_status")}
        row["sections"] = sorted(c["sections"])
        row["assets"] = sorted(c["assets"])
        if c.get("note"):
            row["note"] = c["note"]
        toml_table(doc, "[[component]]", row)
        for n in c["notices"]:
            toml_table(doc, "[[component.notice]]", n)
        for g in c["gaps"]:
            toml_table(doc, "[[component.gap]]", g)
    for a in sorted(coverage):
        toml_table(doc, "[[asset]]", {"id": a, "sha256": sha256_file(assets[a]), "components": coverage[a]})
    text = "\n".join(doc) + "\n"
    tomllib.loads(text)
    (out / "licenses.toml").write_text(text)
    print(json.dumps({"licenses": str(out / "licenses.toml"), "components": len(comps), "status": "incomplete" if gap_components else "complete",
                      "gaps": gap_components}, indent=1))
    return 0


# ------------------------------------------------------------------ release assembly

def blob_name(asset_id: str, sha: str, role: str) -> str:
    """blobs/<sha256>.<ext>. Every blob has an extension, so exactly one hosting.toml rule matches it
    (header files of static hosts merge every matching rule). Notice texts are always .txt (served as
    text/plain, never as HTML from the asset origin)."""
    ext = os.path.splitext(asset_id)[1]
    if role == "notice":
        ext = ".txt"
    elif ext not in KNOWN_EXT:
        ext = ".bin"
    return f"blobs/{sha}{ext}"


def matching_rules(path: str, hosting: dict[str, Any]) -> list[str]:
    return [r["pattern"] for r in hosting["rule"] if fnmatch.fnmatch(path, r["pattern"])]


def hosting_rules() -> dict[str, Any]:
    return tomllib.loads(HOSTING.read_text())


def headers_for(path: str, hosting: dict[str, Any]) -> dict[str, str] | None:
    for rule in hosting["rule"]:
        if fnmatch.fnmatch(path, rule["pattern"]):
            headers = {"Content-Type": rule["content_type"], "Cache-Control": rule["cache_control"],
                       "X-Content-Type-Options": hosting["common"]["x_content_type_options"]}
            cors = hosting.get("cors")
            if cors:
                headers["Access-Control-Allow-Origin"] = cors["allow_origin"]
                headers["Access-Control-Expose-Headers"] = ", ".join(cors["expose_headers"])
            return headers
    return None


def render_headers_file(hosting: dict[str, Any]) -> str:
    """Netlify / Cloudflare Pages `_headers`: one block per path pattern, most specific first."""
    lines = ["# Generated by browser/release/release.py assemble from browser/release/hosting.toml; do not edit."]
    for rule in hosting["rule"]:
        lines.append(f"/{rule['pattern']}")
        for k, v in headers_for(rule["pattern"].replace("*", "x"), hosting).items():
            lines.append(f"  {k}: {v}")
    return "\n".join(lines) + "\n"


def role_of(asset_id: str, manifest: dict[str, Any]) -> str:
    if asset_id.startswith("pack/"):
        rel = asset_id[5:]
        if rel == "pack-manifest.toml":
            return "pack-manifest"
        for a in manifest["artifact"]:
            if a["path"] == rel:
                return a["role"]
        die(f"{asset_id} is not a pack artifact")
    if asset_id == "pack.json":
        return "worker-pack-manifest"
    if asset_id == "modules/krs_expand_wasm.wasm":
        return "krs-expander"
    if asset_id == "modules/krs_lesson_policy.wasm":
        return "lesson-policy"
    if asset_id.startswith("lessons/"):
        return "lesson"
    if asset_id == "licenses/licenses.toml":
        return "license-inventory"
    if asset_id.startswith("licenses/notices/"):
        return "notice"
    die(f"no role for staged asset {asset_id}")
    return ""


def assemble(args: argparse.Namespace) -> int:
    staged, publish, repo = args.staged.resolve(), args.publish.resolve(), args.repo.resolve()
    assets = staged_assets(staged)
    if "licenses/licenses.toml" not in assets:
        die("the staged directory has no licenses/licenses.toml (run `release.py licenses` first)")
    manifest = tomllib.loads((staged / "pack/pack-manifest.toml").read_text())
    pack_json = json.loads((staged / "pack.json").read_text())
    lic = tomllib.loads((staged / "licenses/licenses.toml").read_text())
    oracle = tomllib.loads(args.oracle.read_text())
    krs_lock = tomllib.loads((repo / "Krs.lock").read_text())
    head_crates = git(repo, "rev-parse", "HEAD:crates")
    for label, value in (("pack.json crates_tree", pack_json["crates_tree"]), ("modules crates_tree", pack_json["modules"]["crates_tree"]),
                         ("oracle validity.crates_tree", oracle["validity"]["crates_tree"])):
        if value != head_crates:
            die(f"{label} {value} is not the checkout's crates tree {head_crates}")
    if lic["pack_id"] != manifest["pack_id"] or pack_json["pack_id"] != manifest["pack_id"]:
        die("licenses.toml, pack.json, and pack-manifest.toml name different pack_ids")
    (publish / "blobs").mkdir(parents=True, exist_ok=True)
    (publish / "releases").mkdir(parents=True, exist_ok=True)
    entries = []
    for asset_id, path in assets.items():
        data_sha, size = sha256_file(path), path.stat().st_size
        role = role_of(asset_id, manifest)
        url = blob_name(asset_id, data_sha, role)
        target = publish / url
        if target.exists():
            if sha256_file(target) != data_sha:
                die(f"{target} exists with other bytes")
        else:
            tmp = target.with_suffix(target.suffix + ".partial")
            shutil.copyfile(path, tmp)
            os.replace(tmp, target)
        hdr = headers_for(url, hosting_rules())
        entry = {"id": asset_id, "role": role, "url": url, "required_media_type": hdr["Content-Type"].split(";")[0],
                 "decoded_bytes": size, "decoded_sha256": data_sha, "cache_policy": "immutable-content-addressed"}
        if role == "framework-source":
            entry["virtual_path"] = next(a["virtual_path"] for a in manifest["artifact"] if f"pack/{a['path']}" == asset_id)
        if role == "sysroot-bundle":
            entry["mount_path"] = manifest["sysroot"]["mount"]
        if role == "compiler":
            entry["load_mode"] = "WebAssembly.compile after digest verification"
        entries.append(entry)
    ids = lambda *roles: sorted(e["id"] for e in entries if e["role"] in roles)
    policy_versions = sorted({json.loads(path.read_text())["policy"]["version"]
                              for asset_id, path in assets.items() if asset_id.startswith("lessons/") and asset_id.endswith("/lesson.json")})
    if len(policy_versions) != 1:
        die(f"the staged lessons select policy versions {policy_versions}; a release records exactly one")
    collector_template = repo / "browser/worker/src/collector-template.ts"
    release = {
        "schema": 1,
        "kind": RELEASE_KIND,
        "pack_id": manifest["pack_id"],
        "krs": {
            "revision": git(repo, "rev-parse", "HEAD"),
            "crates_tree": head_crates,
            "pack_producer_revision": manifest["producer"]["krs_revision"],
            "krs_lock_k_rust_commit": krs_lock["k_rust"]["commit"],
            "descriptor_protocol_version": oracle["oracle"]["protocol_version"],
        },
        "oracle": {
            "recipe": "browser/worker/test/parity/regenerate-oracle.sh",
            "krs_revision": oracle["krs_revision"],
            "bundle_sha256": oracle["oracle"]["bundle_sha256"],
            "bundle_bytes": oracle["oracle"]["bundle_bytes"],
            "e1_bundle_sha256": oracle["oracle_e1"]["bundle_sha256"],
        },
        "compiler": {k: manifest["compiler"][k] for k in ("fork_repository", "fork_revision", "fork_commits", "cfg_version", "native_twin_rustc_vv", "wasip1_host_rustc_vv", "target_codegen_backend")},
        "roles": {
            "krs-target-dependencies": {"status": "present", "assets": ids("target-rlib", "sysroot-supplement", "proc-macro-metadata")},
            "krs-expander": {"status": "present", "path": "C (G1)", "assets": ids("krs-expander"), "protocol": "krs-expand-wasm JSON protocol schema 1 (crates/krs-expand-wasm/src/protocol.rs)"},
            "lesson-policy": {"status": "present", "assets": ids("lesson-policy"), "version": policy_versions[0]},
            "collector-template": {"status": "in-worker-bundle", "source": "browser/worker/src/collector-template.ts",
                                   "source_git_blob": git(repo, "rev-parse", "HEAD:browser/worker/src/collector-template.ts") if collector_template.is_file() else None},
            "direct-rustc-arguments": {"status": "present", "assets": ["pack/pack-manifest.toml", "pack.json"], "table": "[direct_rustc] of pack-manifest.toml; direct_rustc of pack.json"},
            "runtime-wasm": {"status": "absent", "reason": "IR-19 (krs-lower-wasm and k-rust for Wasm) has not produced a module; lowering runs natively"},
            "source-map-protocol": {"status": "present", "assets": ids("krs-expander"), "protocol": "IR-10 source map inside the expander response; krs_expand_lookup ABI"},
            "compiler": {"status": "present", "assets": ids("compiler")},
            "sysroot": {"status": "present", "assets": ids("sysroot-bundle"), "mount": manifest["sysroot"]["mount"]},
        },
        "licenses": {"asset": "licenses/licenses.toml", "status": lic["status"], "publication_review": lic["publication_review"],
                     "components_with_gaps": lic["summary"]["components_with_gaps"]},
        "worker_pack_asset": "pack.json",
        "delivery": {
            "url_rule": "every asset url is blobs/<decoded sha256>[.ext], relative to the publication base URL",
            "index": "index.json (mutable, no-cache)",
            "immutable_cache_control": IMMUTABLE,
            "headers": "browser/release/hosting.toml",
        },
        "application_cache": {
            "namespace": "krs-pack-" + manifest["pack_id"].removeprefix("sha256:"),
            "key": "absolute content-addressed URL",
            "write_rule": "write only after decoded length and digest verification",
            "activation_rule": "switch the active pointer only after every asset of the release is verified",
            "cleanup_rule": "delete an inactive namespace only when no page or worker holds its Web Locks lease",
            "corruption_rule": "evict the mismatched entry, refetch once from the same immutable URL, then report pack-integrity",
            "offline_rule": "start offline only when the active release and every asset are present and verified",
            "implementation": "browser/worker/src/pack-cache.ts",
        },
        "assets": sorted(entries, key=lambda e: e["id"]),
    }
    text = json.dumps(release, indent=1, sort_keys=False) + "\n"
    rsha = sha256_bytes(text.encode())
    rpath = publish / "releases" / f"{rsha}.json"
    rpath.write_text(text)
    (publish / "_headers").write_text(render_headers_file(hosting_rules()))
    if args.activate or not (publish / "index.json").exists():
        index = {"schema": 1, "kind": INDEX_KIND, "active": {"release": f"releases/{rsha}.json", "sha256": rsha, "pack_id": manifest["pack_id"]}}
        tmp = publish / "index.json.partial"
        tmp.write_text(json.dumps(index, indent=1) + "\n")
        os.replace(tmp, publish / "index.json")
    print(json.dumps({"release": f"releases/{rsha}.json", "sha256": rsha, "pack_id": manifest["pack_id"], "assets": len(entries),
                      "blobs_bytes": sum(e["decoded_bytes"] for e in entries)}, indent=1))
    return 0


# ------------------------------------------------------------------ fetch (content-addressed download and header check)

class Fetcher:
    def __init__(self, base: str, check_headers: bool, expect_cors: bool):
        self.base = base.rstrip("/") + "/"
        self.check_headers = check_headers
        self.expect_cors = expect_cors
        self.hosting = hosting_rules()
        self.problems: list[str] = []
        self.requests = 0

    def get(self, rel: str) -> bytes:
        self.requests += 1
        request = urllib.request.Request(self.base + rel, headers={"Accept-Encoding": "identity", "Origin": "https://krs-fetch.invalid"} if self.expect_cors else {"Accept-Encoding": "identity"})
        try:
            with urllib.request.urlopen(request, timeout=300) as response:
                data = response.read()
                headers = response.headers
        except urllib.error.URLError as error:
            die(f"GET {self.base + rel}: {error}")
        if self.check_headers:
            want = headers_for(rel, self.hosting)
            if want is None:
                self.problems.append(f"{rel}: no hosting.toml rule")
            else:
                for k in ("Content-Type", "Cache-Control", "X-Content-Type-Options") + (("Access-Control-Allow-Origin",) if self.expect_cors else ()):
                    if (headers.get(k) or "").lower() != want[k].lower():
                        self.problems.append(f"{rel}: {k} is {headers.get(k)!r}, hosting.toml requires {want[k]!r}")
            enc = headers.get("Content-Encoding")
            if enc not in (None, "identity"):
                self.problems.append(f"{rel}: Content-Encoding {enc} returned for Accept-Encoding: identity")
        return data


def fetch(args: argparse.Namespace) -> int:
    f = Fetcher(args.base_url, args.check_headers, args.expect_cors)
    if args.index:
        index = json.loads(f.get("index.json"))
        if index.get("kind") != INDEX_KIND:
            die("index.json has the wrong kind")
        rsha = index["active"]["sha256"]
    else:
        rsha = args.release
    raw = f.get(f"releases/{rsha}.json")
    if sha256_bytes(raw) != rsha:
        die(f"release {rsha}: downloaded bytes hash to {sha256_bytes(raw)}")
    release = json.loads(raw)
    if release.get("kind") != RELEASE_KIND or release.get("schema") != 1:
        die("not a schema-1 release manifest")
    out = args.out.resolve()
    if out.exists() and any(out.iterdir()):
        die(f"{out} is not empty")
    out.mkdir(parents=True, exist_ok=True)
    for a in release["assets"]:
        if not re.fullmatch(rf"blobs/{a['decoded_sha256']}(\.[a-z]+)?", a["url"]):
            die(f"{a['id']}: url {a['url']} does not carry its decoded sha256")
        data = f.get(a["url"])
        if len(data) != a["decoded_bytes"] or sha256_bytes(data) != a["decoded_sha256"]:
            die(f"{a['id']}: {len(data)} bytes, sha256 {sha256_bytes(data)}; release says {a['decoded_bytes']}, {a['decoded_sha256']}")
        target = out / a["id"]
        if ".." in Path(a["id"]).parts or Path(a["id"]).is_absolute():
            die(f"unsafe asset id {a['id']}")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    (out / ".release.json").write_bytes(raw)
    for p in f.problems:
        print(f"fetch: {p}", file=sys.stderr)
    print(json.dumps({"release": rsha, "pack_id": release["pack_id"], "assets": len(release["assets"]), "requests": f.requests,
                      "header_problems": len(f.problems), "out": str(out)}, indent=1))
    return 1 if f.problems else 0


# ------------------------------------------------------------------ serve (hosting.toml applied to a local directory)

def serve(args: argparse.Namespace) -> int:
    root = args.dir.resolve()
    hosting = hosting_rules()

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self) -> None:  # noqa: N802
            self.respond(True)

        def do_HEAD(self) -> None:  # noqa: N802
            self.respond(False)

        def respond(self, body: bool) -> None:
            rel = self.path.split("?", 1)[0].lstrip("/")
            target = (root / rel).resolve()
            hdr = headers_for(rel, hosting)
            if hdr is None or not target.is_file() or root not in target.parents:
                self.send_response(404)
                self.end_headers()
                return
            data = target.read_bytes()
            self.send_response(200)
            for k, v in hdr.items():
                self.send_header(k, v)
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            if body:
                self.wfile.write(data)

        def log_message(self, fmt: str, *a: Any) -> None:
            if args.verbose:
                super().log_message(fmt, *a)

    server = http.server.ThreadingHTTPServer((args.bind, args.port), Handler)
    print(f"serving {root} at http://{args.bind}:{server.server_address[1]}/", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


# ------------------------------------------------------------------ test-only second generation

def derive_generation(args: argparse.Namespace) -> int:
    """A second, valid pack generation for the cache tests: hard links of every staged file, except that the
    framework source crates/krs/Cargo.toml gains a trailing comment line, which changes its artifact hash and so
    pack_id, pack-manifest.toml, and pack.json. Nothing else changes; the collector ignores the comment."""
    staged, out = args.staged.resolve(), args.out.resolve()
    if out.exists():
        shutil.rmtree(out)
    for rel, path in staged_assets(staged).items():
        target = out / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        os.link(path.resolve(), target)
    rel = "krs/crates/krs/Cargo.toml"
    target = out / "pack" / rel
    data = target.read_bytes() + b"# second generation (IR-21 cache tests; test-only)\n"
    target.unlink()
    target.write_bytes(data)
    old_sha, new_sha, new_bytes = sha256_file(staged / "pack" / rel), sha256_bytes(data), len(data)
    mpath = out / "pack/pack-manifest.toml"
    text = mpath.read_text()
    block = re.search(r'\[\[artifact\]\]\npath = "' + re.escape(rel) + r'"\n(?:(?!\n\[).)*', text, re.S)
    if block is None or text.count(old_sha) != 1:
        die("cannot locate the framework-source artifact in pack-manifest.toml")
    new_block = re.sub(r"bytes = \d+", f"bytes = {new_bytes}", block.group(0)).replace(old_sha, new_sha)
    text = text[:block.start()] + new_block + text[block.end():]
    manifest = tomllib.loads(text)
    lines = sorted(f"{a['sha256']}  {a['path']}\n" for a in manifest["artifact"])
    new_id = "sha256:" + sha256_bytes("".join(lines).encode())
    text = text.replace(manifest["pack_id"], new_id)
    mpath.unlink()
    mpath.write_text(text)
    pack = json.loads((out / "pack.json").read_text())
    old_id = pack["pack_id"]
    pack["pack_id"] = new_id
    for s in pack["framework_sources"]:
        if s["path"] == f"pack/{rel}":
            s["sha256"], s["bytes"] = new_sha, new_bytes
    pack["source"]["sha256"] = sha256_bytes(text.encode())
    (out / "pack.json").unlink()
    (out / "pack.json").write_text(json.dumps(pack, indent=1) + "\n")
    for lesson in (out / "lessons").glob("*/lesson.json"):
        doc = json.loads(lesson.read_text())
        doc["pack_id"] = new_id
        lesson.unlink()
        lesson.write_text(json.dumps(doc, indent=1) + "\n")
    lic = out / "licenses/licenses.toml"
    if lic.exists():
        ltext = lic.read_text().replace(old_id, new_id)
        # Asset hashes of the changed files: pack.json, pack-manifest.toml, the framework source, lesson.json.
        ldoc = tomllib.loads(ltext)
        for a in ldoc["asset"]:
            p = out / a["id"]
            ltext = ltext.replace(f'id = "{a["id"]}"\nsha256 = "{a["sha256"]}"', f'id = "{a["id"]}"\nsha256 = "{sha256_file(p)}"')
        lic.unlink()
        lic.write_text(ltext)
    print(json.dumps({"out": str(out), "pack_id": new_id, "previous_pack_id": old_id}, indent=1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("licenses")
    p.add_argument("--staged", type=Path, required=True)
    p.add_argument("--fork-source", type=Path, required=True)
    p.add_argument("--fork-build", type=Path, required=True)
    p.add_argument("--repo", type=Path, default=DEFAULT_REPO)
    p.add_argument("--manual", type=Path, default=MANUAL)
    p.add_argument("--out", type=Path, default=None, help="default STAGED/licenses")
    p.add_argument("--test-drop-license", action="append", default=[], help=argparse.SUPPRESS)
    p = sub.add_parser("assemble")
    p.add_argument("--staged", type=Path, required=True)
    p.add_argument("--publish", type=Path, required=True)
    p.add_argument("--oracle", type=Path, required=True, help="oracle.toml from regenerate-oracle.sh at this crates/ tree")
    p.add_argument("--repo", type=Path, default=DEFAULT_REPO)
    p.add_argument("--activate", action="store_true", help="point index.json at this release (always done for a new publication)")
    p = sub.add_parser("fetch")
    p.add_argument("--base-url", required=True)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--release", help="release manifest sha256 (content address)")
    g.add_argument("--index", action="store_true", help="follow index.json (mutable; for smoke tests only)")
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--check-headers", action="store_true")
    p.add_argument("--expect-cors", action="store_true")
    p = sub.add_parser("serve")
    p.add_argument("dir", type=Path)
    p.add_argument("--port", type=int, default=8741)
    p.add_argument("--bind", default="127.0.0.1")
    p.add_argument("--verbose", action="store_true")
    p = sub.add_parser("derive-generation")
    p.add_argument("--staged", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    DROP_LICENSE.update(getattr(args, "test_drop_license", []))
    return {"licenses": licenses, "assemble": assemble, "fetch": fetch, "serve": serve, "derive-generation": derive_generation}[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
