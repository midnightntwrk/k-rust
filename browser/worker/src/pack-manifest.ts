// Dependency-pack manifest (browser/pack/manifest-format.toml, schema_version 2)
// -> the worker's PackManifest, following the format's [consumer] contract:
//   - every [[artifact]] is verified (here: declared; the loader hashes the
//     bytes) and pack_id is recomputed (computePackId, also run by the loader);
//   - deps/ and proc-macro-meta/ are mounted under /pack, the bundle at
//     sysroot.mount, framework sources at their virtual_path;
//   - rustc arguments come from [direct_rustc]; lint flags and CARGO_* are
//     lesson properties and are not taken from the pack.
// The expander and policy modules are not pack artifacts; the
// caller passes them with the crates/ tree they were built from, which must
// equal the pack's "KRS crates/ tree" input, so the expander's output matches the krs-macros the pack's rlibs
// were built from.

import { computePackId } from "./pack.ts";
import type { MountedSource, PackArtifact, PackAsset, PackManifest } from "./protocol.ts";

export { computePackId };

export interface SourceArtifact {
  path: string;
  role: string;
  bytes: number;
  sha256: string;
  crate_name?: string;
  virtual_path?: string;
  mount?: string;
}

/** The parsed pack-manifest.toml (any TOML parser; the staging script uses Bun.TOML). */
export interface SourcePackManifest {
  schema_version: number;
  manifest_kind: string;
  pack_id: string;
  producer: { krs_revision: string };
  compiler: { fork_revision: string; cfg_version: string; wasip1_host_rustc_vv: string[]; rustc_wasm: string; rustc_wasm_sha256: string };
  sysroot: { bundle: string; bundle_sha256: string; mount: string };
  direct_rustc: {
    edition: string;
    target: string;
    sysroot: string;
    panic: string;
    dependency_search_paths: string[];
    extra_flags: string[];
    rustc_bootstrap_required: boolean;
    collector_flags: string[];
    framework_sources: string[];
    externs: { k: string; __krs_host_runtime: string; __krs_compiler_runtime: string };
  };
  input: Array<{ name: string; kind: string; git_tree?: string }>;
  artifact: SourceArtifact[];
}

export interface PackAdapterInputs {
  /** Where the pack root is staged, relative to the asset root (e.g. "pack"). */
  packDir: string;
  sourcePath: string;
  sourceSha256: string;
  policy: PackAsset;
  expander: PackAsset;
  modulesKrsRevision: string;
  modulesCratesTree: string;
  /** DescriptorBundle protocol of the pack's krs-ir (35 at 3501f86; STATUS.toml [[oracle]]). */
  protocolVersion: number;
  /** Mount point of the pack in the compiler VFS (default /pack). */
  mount?: string;
}

/** Throws with every contract violation found. */
export async function packFromManifest(source: SourcePackManifest, extra: PackAdapterInputs): Promise<PackManifest> {
  const problems: string[] = [];
  if (source.schema_version !== 2) problems.push(`schema_version ${source.schema_version} is not 2`);
  if (source.manifest_kind !== "krs-browser-lesson-pack") problems.push(`manifest_kind ${source.manifest_kind}`);
  const recomputed = await computePackId(source.artifact);
  if (recomputed !== source.pack_id) problems.push(`pack_id ${source.pack_id} does not match the artifacts (${recomputed})`);
  const mount = extra.mount ?? "/pack";
  const staged = (path: string) => `${extra.packDir}/${path}`;
  const byPath = new Map(source.artifact.map((a) => [a.path, a]));
  const asset = (path: string, sha256?: string): PackAsset => {
    const a = byPath.get(path);
    if (!a) {
      problems.push(`no artifact ${path}`);
      return { path: staged(path), sha256: "", bytes: 0 };
    }
    if (sha256 !== undefined && a.sha256 !== sha256) problems.push(`${path}: sha256 ${a.sha256}, manifest says ${sha256}`);
    return { path: staged(a.path), sha256: a.sha256, bytes: a.bytes };
  };
  const d = source.direct_rustc;
  if (d.rustc_bootstrap_required) problems.push("rustc_bootstrap_required = true is not supported");
  if (d.sysroot !== source.sysroot.mount) problems.push(`direct_rustc.sysroot ${d.sysroot} differs from sysroot.mount ${source.sysroot.mount}`);
  const cratesTree = source.input.find((i) => i.kind === "git-tree" && i.name === "KRS crates/ tree")?.git_tree ?? "";
  if (cratesTree === "") problems.push("the pack records no KRS crates/ git tree");
  else if (cratesTree !== extra.modulesCratesTree) {
    problems.push(`modules were built from crates/ tree ${extra.modulesCratesTree}, the pack from ${cratesTree}`);
  }

  const artifacts: PackArtifact[] = [];
  const frameworkSources: MountedSource[] = [];
  for (const a of source.artifact) {
    if (a.role === "target-rlib" || a.role === "sysroot-supplement" || a.role === "proc-macro-metadata") {
      artifacts.push({ path: staged(a.path), sha256: a.sha256, bytes: a.bytes, role: a.role, crate_name: a.crate_name ?? "", mount: `${mount}/${a.path}` });
    } else if (a.role === "framework-source") {
      if (!a.virtual_path?.startsWith("/krs/")) problems.push(`framework source ${a.path} has virtual_path ${a.virtual_path}`);
      frameworkSources.push({ path: staged(a.path), sha256: a.sha256, bytes: a.bytes, mount: a.virtual_path ?? "" });
    } else if (a.role !== "compiler" && a.role !== "sysroot-bundle") {
      problems.push(`unknown artifact role ${a.role} (${a.path})`);
    }
  }
  for (const path of d.framework_sources) {
    if (!frameworkSources.some((s) => s.mount === path)) problems.push(`framework source ${path} has no artifact`);
  }
  const extern = (path: string) => {
    if (!byPath.has(path)) problems.push(`extern ${path} is not an artifact`);
    return `${mount}/${path}`;
  };
  const manifest: PackManifest = {
    schema: 1,
    kind: "krs-browser-worker-pack",
    pack_id: source.pack_id,
    source: { format: "krs-pack-manifest-v2", sha256: extra.sourceSha256, path: extra.sourcePath },
    integrity: { rule: "sorted-artifact-lines", root: extra.packDir },
    krs_revision: source.producer.krs_revision,
    crates_tree: cratesTree,
    fork_revision: source.compiler.fork_revision,
    cfg_version: source.compiler.cfg_version,
    protocol_version: extra.protocolVersion,
    compiler: {
      rustc: asset(source.compiler.rustc_wasm, source.compiler.rustc_wasm_sha256),
      sysroot_bundle: asset(source.sysroot.bundle, source.sysroot.bundle_sha256),
      host_rustc_vv: source.compiler.wasip1_host_rustc_vv,
    },
    modules: { policy: extra.policy, expander: extra.expander, krs_revision: extra.modulesKrsRevision, crates_tree: extra.modulesCratesTree },
    artifacts,
    framework_sources: frameworkSources,
    externs: {
      facade: extern(d.externs.k),
      host_runtime: extern(d.externs.__krs_host_runtime),
      compiler_runtime: extern(d.externs.__krs_compiler_runtime),
    },
    direct_rustc: {
      edition: d.edition,
      target: d.target,
      sysroot: d.sysroot,
      common_flags: ["-C", `panic=${d.panic}`, ...d.extra_flags],
      collector_flags: d.collector_flags,
      // CLIF2WASM_OBJECT=1 selects the clif2wasm
      // object path inside rustc.wasm; RIWL_TIMINGS=1 prints the riwl timing line.
      env: ["CLIF2WASM_OBJECT=1", "RIWL_TIMINGS=1"],
      library_dirs: d.dependency_search_paths.map((p) => `${mount}/${p}`),
    },
  };
  if (problems.length > 0) throw new Error(`pack manifest rejected:\n  ${problems.join("\n  ")}`);
  return manifest;
}
