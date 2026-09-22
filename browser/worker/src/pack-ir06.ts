// Adapter: IR-06 cell-2 pack manifest (evidence/IR-06/cell2/pack-manifest.toml,
// written by evidence/IR-06/pack.py) -> the worker's PackManifest.
//
// The IR-06 manifest lists the pack's rlibs and metadata-only proc-macro
// artifacts and records the compiler hashes in [producer]; it does not name
// the rustc.wasm and sysroot files, the IR-11/IR-13 modules, or the IR-12
// framework sources, so the staging script passes those as `extra` and this
// adapter checks them against [producer]. IR-14 will get its own adapter to
// the same PackManifest once evidence/IR-14/manifest-format.toml exists.

import { sha256Hex } from "./pack.ts";
import type { MountedSource, PackArtifact, PackAsset, PackManifest } from "./protocol.ts";

/** The parsed TOML (any TOML parser; the staging script uses Bun.TOML). */
export interface Ir06PackManifest {
  schema_version: number;
  manifest_kind: string;
  producer: Record<string, string>;
  artifact: Array<{
    path: string;
    role: string;
    crate_name: string;
    bytes: number;
    sha256: string;
  }>;
}

export interface Ir06Extra {
  sourcePath: string;
  sourceSha256: string;
  rustc: PackAsset;
  sysrootBundle: PackAsset;
  policy: PackAsset;
  expander: PackAsset;
  frameworkSources: MountedSource[];
  /** DescriptorBundle protocol of the pack's krs-ir (35 at 3501f86; STATUS.toml [[oracle]]). */
  protocolVersion: number;
  /** Staging prefix under which the IR-06 `deps/…` files are placed (e.g. "pack"). */
  packDir: string;
}

// IR-06 result.toml [compilers] flags_common, minus the per-invocation parts
// (--edition, --target, --sysroot, -L) that the pipeline renders itself.
const IR06_COMMON_FLAGS = ["-C", "panic=abort", "-Zproc-macro-metadata-only"];
const IR06_COLLECTOR_FLAGS = ["-C", "opt-level=2"];
// spikes/BL-003/harness/run-browser-rustc.mjs: CLIF2WASM_OBJECT=1 selects the
// clif2wasm object path inside rustc.wasm; RIWL_TIMINGS=1 prints the riwl timing line.
const IR06_RUSTC_ENV = ["CLIF2WASM_OBJECT=1", "RIWL_TIMINGS=1"];

function mountFor(role: string, file: string): string {
  if (role === "proc-macro-metadata") return `/pack/proc-macro-meta/${file}`;
  if (role === "target-rlib" || role === "sysroot-supplement") return `/pack/deps/${file}`;
  throw new Error(`unknown IR-06 artifact role ${role}`);
}

function stagedPath(role: string, packDir: string, file: string): string {
  return role === "proc-macro-metadata" ? `${packDir}/proc-macro-meta/${file}` : `${packDir}/deps/${file}`;
}

export async function packFromIr06(source: Ir06PackManifest, extra: Ir06Extra): Promise<PackManifest> {
  if (source.schema_version !== 1 || !source.manifest_kind.startsWith("krs-browser-lesson-pack")) {
    throw new Error(`not an IR-06 pack manifest: ${source.manifest_kind} v${source.schema_version}`);
  }
  const producer = source.producer;
  if (producer.rustc_wasm_sha256 !== extra.rustc.sha256) {
    throw new Error(`rustc.wasm ${extra.rustc.sha256} is not the pack's ${producer.rustc_wasm_sha256}`);
  }
  if (producer.sysroot_bundle_sha256 !== extra.sysrootBundle.sha256) {
    throw new Error(`sysroot bundle ${extra.sysrootBundle.sha256} is not the pack's ${producer.sysroot_bundle_sha256}`);
  }
  const artifacts: PackArtifact[] = source.artifact.map((entry) => {
    const file = entry.path.split("/").pop()!;
    if (!entry.path.startsWith("deps/") || file.length === 0) throw new Error(`unexpected artifact path ${entry.path}`);
    return {
      path: stagedPath(entry.role, extra.packDir, file),
      sha256: entry.sha256,
      bytes: entry.bytes,
      role: entry.role as PackArtifact["role"],
      crate_name: entry.crate_name,
      mount: mountFor(entry.role, file),
    };
  });
  const one = (crate: string): string => {
    const found = artifacts.filter((a) => a.crate_name === crate && a.role === "target-rlib");
    if (found.length !== 1) throw new Error(`expected one ${crate} target rlib, found ${found.length}`);
    return found[0]!.mount;
  };
  const withoutId: Omit<PackManifest, "pack_id"> = {
    schema: 1,
    kind: "krs-browser-worker-pack",
    source: { format: "ir06-pack-manifest-v1", sha256: extra.sourceSha256, path: extra.sourcePath },
    krs_revision: producer.krs_revision ?? "",
    fork_revision: producer.fork_revision ?? "",
    protocol_version: extra.protocolVersion,
    compiler: {
      rustc: extra.rustc,
      sysroot_bundle: extra.sysrootBundle,
      host_rustc_vv: producer.wasip1_host_rustc_vV ?? "",
    },
    modules: { policy: extra.policy, expander: extra.expander },
    artifacts,
    framework_sources: extra.frameworkSources,
    externs: { facade: one("krs"), host_runtime: one("krs"), compiler_runtime: one("krs_compiler") },
    direct_rustc: {
      common_flags: IR06_COMMON_FLAGS,
      collector_flags: IR06_COLLECTOR_FLAGS,
      env: IR06_RUSTC_ENV,
      library_dirs: ["/pack/deps", "/pack/proc-macro-meta"],
    },
  };
  // The pack id is the digest of the normalized manifest, so it covers every
  // asset hash (compiler, sysroot, modules, rlibs, framework sources).
  const id = await sha256Hex(new TextEncoder().encode(JSON.stringify(withoutId)));
  return { pack_id: `krs-pack-${id}`, ...withoutId };
}
