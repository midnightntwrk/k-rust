// Pack verification and asset loading, shared by the page loader, the Node/Bun
// runner, and the worker's `assets` stage.

import type { PackAsset, PackManifest, VerifiedAssets } from "./protocol.ts";

export async function sha256Hex(bytes: Uint8Array): Promise<string> {
  const digest = await crypto.subtle.digest("SHA-256", bytes as Uint8Array<ArrayBuffer>);
  let out = "";
  for (const byte of new Uint8Array(digest)) out += byte.toString(16).padStart(2, "0");
  return out;
}

/** pack_id rule of the pack-manifest format: SHA-256 of the sorted "<sha256>  <path>\n" lines of every artifact. */
export async function ir14PackId(artifacts: Array<{ path: string; sha256: string }>): Promise<string> {
  const lines = artifacts.map((a) => `${a.sha256}  ${a.path}\n`).sort();
  return `sha256:${await sha256Hex(new TextEncoder().encode(lines.join("")))}`;
}

/** Recomputes pack_id from the pack's own assets (everything under integrity.root). */
export async function recomputePackId(pack: PackManifest): Promise<string> {
  const prefix = `${pack.integrity.root}/`;
  const own = packAssets(pack)
    .filter((a) => a.path.startsWith(prefix))
    .map((a) => ({ path: a.path.slice(prefix.length), sha256: a.sha256 }));
  return ir14PackId(own);
}

/** Every asset the worker needs, keyed by its pack-relative path. */
export function packAssets(pack: PackManifest): PackAsset[] {
  return [
    pack.compiler.rustc,
    pack.compiler.sysroot_bundle,
    pack.modules.policy,
    pack.modules.expander,
    ...pack.artifacts,
    ...pack.framework_sources,
  ];
}

export class PackIntegrityError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "PackIntegrityError";
  }
}

/**
 * Reads every asset through `read`, checks size and SHA-256 against the
 * manifest, recomputes the pack_id, and compiles the three Wasm modules
 * once. Any mismatch throws PackIntegrityError before a module is compiled.
 */
export async function loadVerifiedAssets(
  pack: PackManifest,
  read: (path: string) => Promise<Uint8Array>,
): Promise<VerifiedAssets> {
  const bytesByPath = new Map<string, Uint8Array>();
  const verified: Record<string, string> = {};
  await Promise.all(packAssets(pack).map(async (asset) => {
    const bytes = await read(asset.path);
    if (bytes.byteLength !== asset.bytes) {
      throw new PackIntegrityError(`${asset.path}: ${bytes.byteLength} bytes, manifest says ${asset.bytes}`);
    }
    const digest = await sha256Hex(bytes);
    if (digest !== asset.sha256) {
      throw new PackIntegrityError(`${asset.path}: sha256 ${digest}, manifest says ${asset.sha256}`);
    }
    bytesByPath.set(asset.path, bytes);
    verified[asset.path] = digest;
  }));
  const packId = await recomputePackId(pack);
  if (packId !== pack.pack_id) throw new PackIntegrityError(`pack_id ${pack.pack_id} does not match the verified artifacts (${packId})`);
  const take = (asset: PackAsset): Uint8Array => bytesByPath.get(asset.path)!;
  const compile = (asset: PackAsset) => WebAssembly.compile(take(asset) as Uint8Array<ArrayBuffer>);
  const [rustc, policy, expander] = await Promise.all([
    compile(pack.compiler.rustc),
    compile(pack.modules.policy),
    compile(pack.modules.expander),
  ]);
  const files: Record<string, Uint8Array> = {};
  for (const asset of [...pack.artifacts, ...pack.framework_sources]) files[asset.path] = take(asset);
  return {
    packId: pack.pack_id,
    modules: { rustc, policy, expander },
    sysrootBundle: take(pack.compiler.sysroot_bundle),
    files,
    verified,
  };
}

/**
 * The worker-side activation check: the assets belong to this pack and every
 * asset the pack names was verified with the manifest's digest.
 * Returns a list of problems (empty when the assets are usable).
 */
export function checkActivation(pack: PackManifest, assets: VerifiedAssets): string[] {
  const problems: string[] = [];
  if (assets.packId !== pack.pack_id) problems.push(`assets are for pack ${assets.packId}, not ${pack.pack_id}`);
  for (const asset of packAssets(pack)) {
    if (assets.verified[asset.path] !== asset.sha256) problems.push(`${asset.path} was not verified`);
  }
  for (const asset of [...pack.artifacts, ...pack.framework_sources]) {
    const bytes = assets.files[asset.path];
    if (!bytes) problems.push(`${asset.path} is missing`);
    else if (bytes.byteLength !== asset.bytes) problems.push(`${asset.path} has ${bytes.byteLength} bytes`);
  }
  if (assets.sysrootBundle.byteLength !== pack.compiler.sysroot_bundle.bytes) {
    problems.push("sysroot bundle size differs from the manifest");
  }
  return problems;
}
