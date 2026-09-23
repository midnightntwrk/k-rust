#!/usr/bin/env python3
"""KRS browser dependency pack: assembly, manifest, verification, and path scan.

Python 3 standard library only, plus `objcopy` (proc-macro metadata) and `strings` (path scan).
The manifest format is specified in manifest-format.toml next to this file.

Usage:
  manifest.py assemble --build DIR --pack DIR --stage1 DIR --rustc-wasm FILE --bundle FILE
                       --cargo-home DIR --rustflags ENCODED [--rustflag-sep SEP] --cargo-args ARGS
                       [--set KEY=VALUE ...] [--fork-commit "SHA SUBJECT" ...]
  manifest.py verify PACK       every [[artifact]] matches its file; no other file; no .so; pack_id
  manifest.py scan PACK         strings(1) path scan; exit 1 on any undeclared path
  manifest.py id PACK           print pack_id

`assemble` is called by build.sh after Cargo ran inside the build namespace. Every artifact is
derived from Cargo's JSON messages in BUILD/build.jsonl, not from a directory listing:

- each wasm32-wasip1 `.rlib` of a library target      -> deps/, role target-rlib
- each proc-macro target's host `.so`                 -> proc-macro-meta/lib<name>-<hash>.rmeta, role
  proc-macro-metadata: the payload of the library's `.rustc` section after the 8-byte
  METADATA_HEADER and the u64 length (an --emit=metadata rerun would have another crate hash)
- the twin's wasm32-wasip1 libproc_macro and librustc_literal_escaper (.rlib and .rmeta)
                                                      -> deps/, role sysroot-supplement (the
  sysroot bundle omits them, and proc-macro2's target rlib needs them)
- crates/krs/Cargo.toml and crates/krs/src/lib.rs of the export -> krs/..., role framework-source
- the sysroot bundle and rustc.wasm                   -> sysroot/, compiler/
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import tomllib

SCHEMA_VERSION = 2
MANIFEST_KIND = "krs-browser-lesson-pack"
MANIFEST_NAME = "pack-manifest.toml"
METADATA_HEADER = b"rust\0\0\0\x0a"  # rustc_metadata METADATA_HEADER (METADATA_VERSION 10)
TARGET = "wasm32-wasip1"
VIRTUAL_ROOT = "/krs"
NS_TARGET = os.environ.get("KRS_PACK_NS_TARGET", "/pack-target")  # build.sh PACK_TARGET (diagnostic override)
FRAMEWORK_SOURCES = ["crates/krs/Cargo.toml", "crates/krs/src/lib.rs"]
SYSROOT_SUPPLEMENT = ("libproc_macro-", "librustc_literal_escaper-")
PROC_MACRO_FLAG = "-Zproc-macro-metadata-only"
ROLES = ["compiler", "framework-source", "proc-macro-metadata", "sysroot-bundle", "sysroot-supplement", "target-rlib"]


# ------------------------------------------------------------------ helpers

def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def tree_digest(root):
    """sha256 over sorted "<sha256>  <relative path>\\n" lines of every regular file under root."""
    lines = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames.sort()
        for name in filenames:
            full = os.path.join(dirpath, name)
            if os.path.isfile(full) and not os.path.islink(full):
                lines.append(f"{sha256_file(full)}  {os.path.relpath(full, root)}\n")
    lines.sort()
    return hashlib.sha256("".join(lines).encode()).hexdigest(), len(lines)


def toml_value(v):
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


def toml_key(k):
    return k if re.fullmatch(r"[A-Za-z0-9_-]+", k) else json.dumps(k)


def write_table(out, header, table):
    if header:
        out.append(f"\n{header}")
    for k, v in table.items():
        out.append(f"{toml_key(k)} = {toml_value(v)}")


def ls_crate(twin, path, mode):
    return subprocess.run([twin, f"-Zls={mode}", path], check=True, capture_output=True, text=True).stdout


def crate_root_info(twin, path):
    out = ls_crate(twin, path, "root")
    name = re.search(r"^name (\S+)$", out, re.M).group(1)
    svh = re.search(r"^hash ([0-9a-f]+) ", out, re.M).group(1)
    triple = re.search(r"^triple (\S+)$", out, re.M).group(1)
    proc_macro = re.search(r"^proc_macro (\w+)$", out, re.M).group(1) == "true"
    return {"name": name, "svh": svh, "triple": triple, "proc_macro": proc_macro}


DEP_RE = re.compile(r"^\d+ (\S+) hash ([0-9a-f]+) host_hash \S+ kind (\S+)", re.M)


def crate_deps(twin, path):
    """External crates recorded in a crate's metadata: [(name-disambiguator, svh, kind)]."""
    return DEP_RE.findall(ls_crate(twin, path, "all"))


def extract_rustc_section(so_path, out_path):
    with tempfile.TemporaryDirectory() as tmp:
        section = os.path.join(tmp, "rustc.section")
        subprocess.run(["objcopy", "--dump-section", f".rustc={section}", so_path, os.path.join(tmp, "discard")],
                       check=True)
        buf = open(section, "rb").read()
    if buf[:8] != METADATA_HEADER:
        raise SystemExit(f"{so_path}: unexpected .rustc header {buf[:8]!r}")
    (length,) = struct.unpack_from("<Q", buf, 8)
    if 16 + length > len(buf):
        raise SystemExit(f"{so_path}: .rustc length {length} exceeds section size {len(buf)}")
    with open(out_path, "wb") as f:
        f.write(buf[16:16 + length])
    return {"section": ".rustc", "section_bytes": len(buf), "payload_offset": 16, "payload_bytes": length}


def read_bundle_index(path):
    with open(path, "rb") as f:
        head = f.read(10)
        if head[:6] != b"RIWB1\n":
            raise SystemExit(f"{path}: not a RIWB1 bundle")
        (n,) = struct.unpack_from("<I", head, 6)
        index = json.loads(f.read(n))
        data = f.read()
    return index["files"], data


def pack_id(artifacts):
    lines = sorted(f"{a['sha256']}  {a['path']}\n" for a in artifacts)
    return "sha256:" + hashlib.sha256("".join(lines).encode()).hexdigest()


# ------------------------------------------------------------------ assemble

def assemble(args):
    build, pack = os.path.realpath(args.build), os.path.realpath(args.pack)
    src, target = os.path.join(build, "src"), os.path.join(build, "target")
    twin = os.path.join(args.stage1, "bin", "rustc")
    twin_wasip1_lib = os.path.join(args.stage1, "lib", "rustlib", TARGET, "lib")
    sets = dict(item.partition("=")[::2] for item in args.set)

    def host(path):
        if path == NS_TARGET or path.startswith(NS_TARGET + "/"):
            return target + path[len(NS_TARGET):]
        raise SystemExit(f"artifact outside {NS_TARGET}: {path}")

    for sub in ("deps", "proc-macro-meta", "krs", "sysroot", "compiler"):
        if os.path.exists(os.path.join(pack, sub)):
            raise SystemExit(f"{pack}/{sub} exists; assemble needs an empty pack directory")
    os.makedirs(os.path.join(pack, "deps"))
    os.makedirs(os.path.join(pack, "proc-macro-meta"))

    with open(os.path.join(build, "build.jsonl")) as f:
        messages = [json.loads(line) for line in f if line.startswith("{")]
    root_pkg = [m for m in messages if m.get("reason") == "compiler-artifact"
                and m["package_id"].startswith("path+") and "#krs-browser-pack@" in m["package_id"]]
    if len(root_pkg) != 1:
        raise SystemExit(f"expected one krs-browser-pack artifact, found {len(root_pkg)}")

    artifacts, proc_macros, build_scripts = [], [], []
    for m in messages:
        reason = m.get("reason")
        if reason == "build-script-executed":
            out_dir = m["out_dir"]
            digest, count = tree_digest(host(out_dir))
            build_scripts.append({"package_id": m["package_id"], "out_dir": out_dir,
                                  "files": count, "out_dir_sha256": digest})
            continue
        if reason != "compiler-artifact" or m in root_pkg:
            continue
        kinds = m["target"]["kind"]
        crate = m["target"]["name"].replace("-", "_")
        for path in m["filenames"]:
            if "proc-macro" in kinds and path.endswith(".so"):
                base = os.path.basename(path)[:-3] + ".rmeta"
                rel = f"proc-macro-meta/{base}"
                provenance = extract_rustc_section(host(path), os.path.join(pack, rel))
                provenance = {"source_library": path, "source_library_sha256": sha256_file(host(path)),
                              **provenance}
                proc_macros.append((rel, crate))
                artifacts.append({"path": rel, "role": "proc-macro-metadata", "crate_name": crate,
                                  "package_id": m["package_id"], "features": m.get("features", []),
                                  "provenance": provenance})
            elif f"/{TARGET}/" in path and path.endswith(".rlib"):
                base = os.path.basename(path)
                if "-" not in base:
                    # Cargo names the uplifted copy (release/libfoo.rlib) for root units; the pack uses the
                    # byte-identical hashed file in deps/, which is what -L dependency= resolution finds.
                    ddir = os.path.join(os.path.dirname(path), "deps")
                    data = open(host(path), "rb").read()
                    same = [f for f in sorted(os.listdir(host(ddir)))
                            if f.startswith(base[:-5] + "-") and f.endswith(".rlib")
                            and open(os.path.join(host(ddir), f), "rb").read() == data]
                    if len(same) != 1:
                        raise SystemExit(f"no unique hashed copy of {path}: {same}")
                    path, base = f"{ddir}/{same[0]}", same[0]
                rel = f"deps/{base}"
                shutil.copyfile(host(path), os.path.join(pack, rel))
                artifacts.append({"path": rel, "role": "target-rlib", "crate_name": crate,
                                  "package_id": m["package_id"], "features": m.get("features", []),
                                  "source": path})

    for fname in sorted(os.listdir(twin_wasip1_lib)):
        if fname.startswith(SYSROOT_SUPPLEMENT) and fname.endswith((".rlib", ".rmeta")):
            rel = f"deps/{fname}"
            shutil.copyfile(os.path.join(twin_wasip1_lib, fname), os.path.join(pack, rel))
            artifacts.append({"path": rel, "role": "sysroot-supplement",
                              "crate_name": fname[3:].split("-")[0], "package_id": f"twin sysroot {TARGET}",
                              "features": [], "source": f"<stage1>/lib/rustlib/{TARGET}/lib/{fname}"})

    for relsrc in FRAMEWORK_SOURCES:
        rel = f"krs/{relsrc}"
        os.makedirs(os.path.dirname(os.path.join(pack, rel)), exist_ok=True)
        shutil.copyfile(os.path.join(src, relsrc), os.path.join(pack, rel))
        artifacts.append({"path": rel, "role": "framework-source", "virtual_path": f"{VIRTUAL_ROOT}/{relsrc}"})

    os.makedirs(os.path.join(pack, "sysroot"))
    shutil.copyfile(args.bundle, os.path.join(pack, "sysroot", "sysroot-wasip1.bundle"))
    artifacts.append({"path": "sysroot/sysroot-wasip1.bundle", "role": "sysroot-bundle", "format": "RIWB1",
                      "mount": "/sysroot"})
    os.makedirs(os.path.join(pack, "compiler"))
    shutil.copyfile(args.rustc_wasm, os.path.join(pack, "compiler", "rustc.wasm"))
    artifacts.append({"path": "compiler/rustc.wasm", "role": "compiler", "host": TARGET})

    for a in artifacts:
        full = os.path.join(pack, a["path"])
        a["bytes"] = os.path.getsize(full)
        a["sha256"] = sha256_file(full)
    artifacts.sort(key=lambda a: a["path"])
    if len({a["path"] for a in artifacts}) != len(artifacts):
        raise SystemExit("duplicate artifact path")

    # Crate hashes: each proc-macro .rmeta's own hash must be the one every pack rlib recorded for it.
    rlibs = [a for a in artifacts if a["role"] == "target-rlib"]
    recorded = {}
    for a in rlibs:
        info = crate_root_info(twin, os.path.join(pack, a["path"]))
        a["svh"] = info["svh"]
        for dep, svh, kind in crate_deps(twin, os.path.join(pack, a["path"])):
            recorded.setdefault(dep, set()).add(svh)
            if kind == "MacrosOnly":
                recorded.setdefault(("macros-only-user", dep), set()).add(a["crate_name"])
    for a in artifacts:
        if a["role"] != "proc-macro-metadata":
            continue
        info = crate_root_info(twin, os.path.join(pack, a["path"]))
        if not info["proc_macro"]:
            raise SystemExit(f"{a['path']} is not proc-macro metadata")
        seen = recorded.get(info["name"], set())
        if seen != {info["svh"]}:
            raise SystemExit(f"{a['path']}: own crate hash {info['svh']}, recorded by dependents {sorted(seen)}")
        a["svh"] = info["svh"]
        a["provenance"]["host_triple"] = info["triple"]
        a["provenance"]["recorded_by"] = sorted(recorded.get(("macros-only-user", info["name"]), set()))

    krs = [a for a in rlibs if a["crate_name"] == "krs"]
    if len(krs) != 1:
        raise SystemExit("expected one krs rlib")
    krs_deps = {d.rsplit("-", 1)[0] for d, _, _ in crate_deps(twin, os.path.join(pack, krs[0]["path"]))}
    for banned in ("inventory", "rustversion"):
        if banned in krs_deps:
            raise SystemExit(f"krs target metadata depends on {banned} (explicit descriptor registration expected)")
    compiler_art = next(a for a in artifacts if a["role"] == "compiler")
    so_files = [a["path"] for a in artifacts if a["path"].endswith(".so")]
    if so_files:
        raise SystemExit(f".so in pack: {so_files}")

    # Sysroot identity: every bundle file, and whether the twin's sysroot holds the same bytes.
    files, data = read_bundle_index(args.bundle)
    sysroot_files = []
    for f in files:
        if f["p"] == "manifest.json":
            continue
        blob = data[f["o"]:f["o"] + f["l"]]
        twin_file = os.path.join(args.stage1, f["p"])
        entry = {"path": f["p"], "bytes": f["l"], "sha256": hashlib.sha256(blob).hexdigest()}
        entry["twin"] = ("identical" if os.path.isfile(twin_file) and open(twin_file, "rb").read() == blob
                         else "differs" if os.path.isfile(twin_file) else "absent")
        sysroot_files.append(entry)
    if any(e["twin"] == "differs" for e in sysroot_files):
        raise SystemExit("sysroot bundle file differs from the twin's; the pack would not match rustc.wasm")
    sysroot_files.sort(key=lambda e: e["path"])

    # Inputs.
    twin_vv = open(os.path.join(build, "twin-vV.txt")).read().splitlines()
    wasm_vv = open(os.path.join(build, "rustc-wasm-vV.txt")).read().splitlines()
    vv = dict(line.split(": ", 1) for line in twin_vv[1:] if ": " in line)
    driver = sorted(f for f in os.listdir(os.path.join(args.stage1, "lib")) if f.startswith("librustc_driver-"))
    inputs = [
        {"name": "native-twin rustc", "kind": "file", "path": "<stage1>/bin/rustc", "sha256": sha256_file(twin)},
    ]
    for d in driver:
        inputs.append({"name": "native-twin compiler library", "kind": "file", "path": f"<stage1>/lib/{d}",
                       "sha256": sha256_file(os.path.join(args.stage1, "lib", d))})
    for triple in ("x86_64-unknown-linux-gnu", TARGET):
        digest, count = tree_digest(os.path.join(args.stage1, "lib", "rustlib", triple, "lib"))
        inputs.append({"name": f"native-twin {triple} standard library", "kind": "tree",
                       "path": f"<stage1>/lib/rustlib/{triple}/lib", "files": count, "sha256": digest})
    inputs.append({"name": "rustc.wasm", "kind": "file", "path": "<fork>/out/rustc/rustc.wasm",
                   "sha256": compiler_art["sha256"]})
    inputs.append({"name": "sysroot bundle", "kind": "file",
                   "path": "<fork>/out/wasip1/stage/rustc/sysroot-wasip1.bundle",
                   "sha256": sha256_file(args.bundle)})
    for rel in ("browser/pack/Cargo.toml", "browser/pack/Cargo.lock", "browser/pack/lib.rs"):
        inputs.append({"name": rel, "kind": "file", "path": f"{VIRTUAL_ROOT}/{rel}",
                       "sha256": sha256_file(os.path.join(src, rel))})
    inputs.append({"name": "KRS crates/ tree", "kind": "git-tree", "path": f"{VIRTUAL_ROOT}/crates",
                   "git_tree": sets["krs_crates_tree"]})
    inputs.append({"name": "KRS browser/pack/ tree", "kind": "git-tree", "path": f"{VIRTUAL_ROOT}/browser/pack",
                   "git_tree": sets["krs_pack_tree"]})
    lock = tomllib.load(open(os.path.join(src, "browser", "pack", "Cargo.lock"), "rb"))
    cache = os.path.join(args.cargo_home, "registry", "cache", sets["registry_index"])
    for p in sorted(lock["package"], key=lambda p: (p["name"], p["version"])):
        if "checksum" not in p:
            continue
        crate_file = os.path.join(cache, f"{p['name']}-{p['version']}.crate")
        if sha256_file(crate_file) != p["checksum"]:
            raise SystemExit(f"{crate_file} does not match its Cargo.lock checksum")
        inputs.append({"name": f"{p['name']} {p['version']}", "kind": "crate", "source": p["source"],
                       "sha256": p["checksum"]})

    sep = args.rustflag_sep
    rustflags = args.rustflags.split(sep) if args.rustflags else []
    by_crate = {a["crate_name"]: a["path"] for a in rlibs}

    doc = []
    doc.append("# KRS browser dependency pack manifest (browser/pack/manifest.py; format: browser/pack/manifest-format.toml).")
    doc.append("# Generated; every path is relative to the pack root unless it is a virtual (namespace) path.")
    write_table(doc, None, {"schema_version": SCHEMA_VERSION, "manifest_kind": MANIFEST_KIND,
                            "pack_id": pack_id(artifacts)})
    write_table(doc, "[producer]", {
        "builder": "browser/pack/build.sh",
        "krs_revision": sets["krs_revision"],
        "krs_source": f"git archive {sets['krs_revision']} mounted read-only at {VIRTUAL_ROOT}",
        "krs_worktree_clean": True,
        "virtual_root": VIRTUAL_ROOT,
        "cargo_version": sets["cargo_version"],
        "cargo_args": args.cargo_args.split(" "),
        "cargo_env": {"CARGO_HOME": "/cargo", "CARGO_TARGET_DIR": NS_TARGET, "CARGO_INCREMENTAL": "0",
                      "SOURCE_DATE_EPOCH": "0", "RUSTC": "/fork/stage1/bin/rustc"},
        "rustflags": rustflags,
        "host_rustflags": [],
        "cargo_lock_sha256": sha256_file(os.path.join(src, "browser", "pack", "Cargo.lock")),
        "registry_index": sets["registry_index"],
    })
    write_table(doc, "[compiler]", {
        "fork_repository": sets["fork_repository"],
        "fork_revision": vv["commit-hash"],
        "fork_commits": args.fork_commit,
        "cfg_version": twin_vv[0].removeprefix("rustc "),
        "native_twin_rustc_vv": twin_vv,
        "wasip1_host_rustc_vv": wasm_vv,
        "target": TARGET,
        "target_codegen_backend": "llvm",
        "rustc_wasm": "compiler/rustc.wasm",
        "rustc_wasm_sha256": compiler_art["sha256"],
    })
    write_table(doc, "[sysroot]", {
        "bundle": "sysroot/sysroot-wasip1.bundle",
        "bundle_sha256": sha256_file(args.bundle),
        "mount": "/sysroot",
        "files": len(sysroot_files),
        "twin_identical": sum(1 for e in sysroot_files if e["twin"] == "identical"),
    })
    for e in sysroot_files:
        write_table(doc, "[[sysroot.file]]", e)
    write_table(doc, "[direct_rustc]", {
        "path_base": "pack root",
        "edition": "2024",
        "target": TARGET,
        "sysroot": "/sysroot",
        "panic": "abort",
        "dependency_search_paths": ["deps", "proc-macro-meta"],
        "extra_flags": [PROC_MACRO_FLAG],
        "rustc_bootstrap_required": False,
        "collector_flags": ["-C", "opt-level=2"],
        "framework_sources": [f"{VIRTUAL_ROOT}/{r}" for r in FRAMEWORK_SOURCES],
    })
    write_table(doc, "[direct_rustc.externs]", {
        "k": by_crate["krs"],
        "__krs_host_runtime": by_crate["krs"],
        "__krs_compiler_runtime": by_crate["krs_compiler"],
    })
    write_table(doc, "[checks]", {
        "so_files": 0,
        "inventory_in_lock": any(p["name"] == "inventory" for p in lock["package"]),
        "krs_depends_on_inventory": False,
        "krs_depends_on_rustversion": False,
        "proc_macro_hashes_match_dependents": True,
    })
    write_table(doc, "[counts]", {r: sum(1 for a in artifacts if a["role"] == r) for r in ROLES})
    write_table(doc, "[paths]", {
        "declared": [{"pattern": p, "class": c, "roles": r, "note": n}
                     for p, c, r, n in declared_paths(vv["commit-hash"])],
    })
    for a in artifacts:
        prov = a.pop("provenance", None)
        write_table(doc, "[[artifact]]", a)
        if prov:
            write_table(doc, "[artifact.provenance]", prov)
    for b in sorted(build_scripts, key=lambda b: (b["package_id"], b["out_dir"])):
        write_table(doc, "[[build_script]]", b)
    for i in inputs:
        write_table(doc, "[[input]]", i)
    with open(os.path.join(pack, MANIFEST_NAME), "w") as f:
        f.write("\n".join(doc) + "\n")
    tomllib.load(open(os.path.join(pack, MANIFEST_NAME), "rb"))
    print(json.dumps({r: sum(1 for a in artifacts if a["role"] == r) for r in ROLES}, sort_keys=True))


# ------------------------------------------------------------------ declared paths and scan

def declared_paths(fork_commit):
    """Absolute paths allowed in pack artifacts: (pattern, class, roles, note).

    `pattern` is a Python regular expression matched at the start of a scan match; `roles` limits the
    artifact roles in which the class may occur (empty: every role).
    """
    return [
        (re.escape(VIRTUAL_ROOT + "/"), "virtual-root", [],
         "virtual KRS root; never remapped (CARGO_MANIFEST_DIR, file!(), source file names)"),
        ("/registry/", "remapped-registry", [],
         "target units: --remap-path-prefix of /cargo/registry/src/<index>; also the fork's own vendored crates"),
        ("/target/", "remapped-target", ["target-rlib"],
         "target units: --remap-path-prefix of /pack-target (build-script OUT_DIR includes)"),
        (re.escape(f"/rustc/{fork_commit}"), "fork-std", [],
         "the fork's remapped standard-library and compiler source prefix (rust.remap-debuginfo)"),
        ("/cargo/registry/src/", "namespace-registry", ["proc-macro-metadata"],
         "host units get no RUSTFLAGS: the build namespace's Cargo home (fixed path, not a host path)"),
        (re.escape(NS_TARGET + "/"), "namespace-target", ["proc-macro-metadata"],
         "host units get no RUSTFLAGS: the build namespace's target directory (fixed path, not a host path)"),
        ("/usr/bin/env$", "string-literal", ["target-rlib"], "syn: the `#!/usr/bin/env` shebang literal"),
        ("/tmp/dep_graph\\.gv\\)$", "string-literal", ["compiler"], "rustc: -Zdump-dep-graph default file name"),
        ("/(tmp|home|root)/[^\"`]*[\"`]", "string-literal", ["sysroot-bundle"],
         "std rustdoc examples kept in metadata (a quote or backtick ends the literal)"),
    ]


SCAN_TRIGGERS = ["/home/", "/var/tmp/", "/tmp/", "/nix/store", ".cargo/registry", "/srv/", "/root/", "/usr/",
                 "/krs/", "/registry/", "/target/", "/rustc/", "/cargo/", "/pack-target/", "/fork/",
                 "/workspace/", "/work/", "/sysroot/"] + ([NS_TARGET + "/"] if NS_TARGET != "/pack-target" else [])
# Fork products (rustc.wasm, the sysroot bundle, sysroot supplements) are copied verbatim from the fork
# build; they are scanned for the host-path triggers only, because their rustdoc text and
# string tables are full of relative links and literals under the virtual prefixes.
HOST_TRIGGERS = ["/home/", "/var/tmp/", "/tmp/", "/nix/store", ".cargo/registry", "/srv/", "/root/"]
FORK_PRODUCT_ROLES = ("compiler", "sysroot-bundle", "sysroot-supplement")


def trigger_re(triggers):
    return re.compile(r"(?:" + "|".join(re.escape(t) for t in triggers) + r")[\x21-\x7e]*")


PATH_RE = trigger_re(SCAN_TRIGGERS)
HOST_PATH_RE = trigger_re(HOST_TRIGGERS)
URL_TAIL_RE = re.compile(r"(?:[a-z]+://\S*|\.\.)$")  # a URL path or a relative ../ link, not a file path


def scan(args):
    pack = os.path.realpath(args.pack)
    manifest = tomllib.load(open(os.path.join(pack, MANIFEST_NAME), "rb"))
    declared = [(re.compile(d["pattern"]), d["class"], d["roles"]) for d in manifest["paths"]["declared"]]
    print("# pack path scan (browser/pack/manifest.py scan; strings -a)")
    print(f"# pack_id = {manifest['pack_id']}")
    print("# declared prefixes:")
    for p, c, roles in declared:
        print(f"#   {c}: {p.pattern}" + (f" (only in {', '.join(roles)})" if roles else ""))
    print("# A match is a maximal printable run starting at one of: " + " ".join(SCAN_TRIGGERS))
    print("# Fork products (" + ", ".join(FORK_PRODUCT_ROLES) + ") are scanned for: " + " ".join(HOST_TRIGGERS))
    print("# `crates/krs/...` (a relative display path) is not a /krs/ match.")
    undeclared = 0
    for a in manifest["artifact"]:
        out = subprocess.run(["strings", "-a", os.path.join(pack, a["path"])], check=True,
                             capture_output=True, text=True, errors="replace").stdout
        found = {}
        for line in out.splitlines():
            for m in (HOST_PATH_RE if a["role"] in FORK_PRODUCT_ROLES else PATH_RE).finditer(line):
                text = m.group(0)
                start = m.start()
                if text.startswith("/krs/") and line[max(0, start - 6):start] == "crates":
                    continue
                if URL_TAIL_RE.search(line[:start]):
                    continue
                cls = next((c for p, c, roles in declared
                            if p.match(text) and (not roles or a["role"] in roles)), "UNDECLARED")
                found.setdefault(cls, set()).add(text)
        print(f"\n[{a['role']}] {a['path']}")
        if not found:
            print("  no paths")
        for cls in sorted(found):
            items = sorted(found[cls])
            if cls == "UNDECLARED":
                undeclared += len(items)
            print(f"  {cls}: {len(items)} distinct")
            shown = items if cls in ("UNDECLARED", "virtual-root", "namespace-target", "namespace-registry", "string-literal", "fork-build-path") else items[:3]
            for item in shown[:40]:
                print(f"    {item[:200]}")
            if len(shown) > 40 or len(shown) < len(items):
                print(f"    ... {len(items) - min(len(shown), 40)} more")
    # Raw byte search for the build host's own paths (no strings(1) run boundaries involved).
    host_hits = 0
    if args.host_path:
        print("\n# raw host-path search (bytes, every artifact and the manifest); paths from build.sh:")
        files = [MANIFEST_NAME] + [a["path"] for a in manifest["artifact"]]
        for hp in args.host_path:
            needle = hp.encode()
            hits = []
            for rel in files:
                n = open(os.path.join(pack, rel), "rb").read().count(needle)
                if n:
                    hits.append(f"{rel} ({n})")
            host_hits += len(hits)
            print(f"host-path {hp!r}: {len(hits)} files" + (": " + ", ".join(hits) if hits else ""))
    print(f"\nundeclared_total = {undeclared}")
    print(f"host_path_files = {host_hits}")
    return 1 if undeclared or host_hits else 0


# ------------------------------------------------------------------ verify

def verify(args):
    pack = os.path.realpath(args.pack)
    manifest = tomllib.load(open(os.path.join(pack, MANIFEST_NAME), "rb"))
    errors = []
    if manifest.get("schema_version") != SCHEMA_VERSION or manifest.get("manifest_kind") != MANIFEST_KIND:
        errors.append("schema_version or manifest_kind mismatch")
    listed = set()
    for a in manifest["artifact"]:
        full = os.path.join(pack, a["path"])
        listed.add(a["path"])
        if a["role"] not in ROLES:
            errors.append(f"{a['path']}: unknown role {a['role']}")
        if not os.path.isfile(full):
            errors.append(f"{a['path']}: missing")
            continue
        if os.path.getsize(full) != a["bytes"] or sha256_file(full) != a["sha256"]:
            errors.append(f"{a['path']}: bytes or sha256 mismatch")
    present = set()
    for dirpath, _, filenames in os.walk(pack):
        for name in filenames:
            present.add(os.path.relpath(os.path.join(dirpath, name), pack))
    extra = sorted(present - listed - {MANIFEST_NAME})
    if extra:
        errors.append(f"files not in the manifest: {extra}")
    if any(p.endswith(".so") for p in present):
        errors.append(".so file in pack")
    if pack_id(manifest["artifact"]) != manifest["pack_id"]:
        errors.append("pack_id does not match the artifact table")
    if manifest["sysroot"]["bundle_sha256"] != next(
            a["sha256"] for a in manifest["artifact"] if a["role"] == "sysroot-bundle"):
        errors.append("sysroot.bundle_sha256 does not match the bundle artifact")
    for e in errors:
        print(f"verify: {e}", file=sys.stderr)
    if not errors:
        print(f"verify: ok, {len(listed)} artifacts, {manifest['pack_id']}")
    return 1 if errors else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    a = sub.add_parser("assemble")
    a.add_argument("--build", required=True)
    a.add_argument("--pack", required=True)
    a.add_argument("--stage1", required=True)
    a.add_argument("--rustc-wasm", required=True)
    a.add_argument("--bundle", required=True)
    a.add_argument("--cargo-home", required=True)
    a.add_argument("--rustflags", required=True)
    a.add_argument("--rustflag-sep", default="\x1f")
    a.add_argument("--cargo-args", required=True)
    a.add_argument("--set", action="append", default=[])
    a.add_argument("--fork-commit", action="append", default=[])
    for name in ("verify", "scan", "id"):
        sp = sub.add_parser(name)
        sp.add_argument("pack")
        if name == "scan":
            sp.add_argument("--host-path", action="append", default=[],
                            help="a build-host path that must not occur in any pack file (raw bytes)")
    args = parser.parse_args()
    if args.command == "assemble":
        return assemble(args)
    if args.command == "verify":
        return verify(args)
    if args.command == "scan":
        return scan(args)
    manifest = tomllib.load(open(os.path.join(args.pack, MANIFEST_NAME), "rb"))
    print(manifest["pack_id"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
