// Worker-readable asset store over the Cache API (IR-20).
//
// The page calls storeVerifiedAssets once: every pack asset is taken from the
// pack's cache when a verified copy is there, otherwise downloaded from the
// asset base URL, checked for size and SHA-256, and written to the cache; the
// three Wasm modules are compiled as soon as their bytes are verified. The page
// keeps no asset bytes afterwards. Each worker calls readStoredAssets to read
// and verify the rest from the same cache, so starting a worker (and replacing
// one after cancel) clones only the compiled modules.
//
// One cache per pack_id; caches of other packs are deleted on activation. A
// cached entry that fails verification is replaced from the network on the
// page, and makes worker start-up fail (PackIntegrityError) in a worker.

import { packAssets, PackIntegrityError, recomputePackId, sha256Hex } from "./pack.ts";
import type { PackAsset, PackManifest, StoredAssets, VerifiedAssets } from "./protocol.ts";

export const CACHE_PREFIX = "krs-lesson-pack-";

/** The cache that holds the assets of one pack generation. */
export function cacheNameFor(packId: string): string {
  return `${CACHE_PREFIX}${packId.replace(/^sha256:/, "")}`;
}

/** The request URL of an asset: the base URL (with a trailing slash) joined with the pack-relative path. */
export function assetUrl(baseUrl: string, path: string): string {
  const base = baseUrl.endsWith("/") ? baseUrl : `${baseUrl}/`;
  return new URL(path, new URL(base, globalThis.location?.href)).href;
}

/** Total decoded size of every pack asset, as the manifest declares it. */
export function packBytes(pack: PackManifest): number {
  return packAssets(pack).reduce((sum, asset) => sum + asset.bytes, 0);
}

export interface StoreProgress {
  /** Bytes read so far from the cache or the network, over all assets. */
  loadedBytes: number;
  totalBytes: number;
  /** Assets verified so far, over all assets. */
  verifiedAssets: number;
  totalAssets: number;
  fromCache: number;
  fromNetwork: number;
}

export interface StoreOptions {
  /** Base URL the pack-relative asset paths resolve against. */
  baseUrl: string;
  cacheStorage?: CacheStorage;
  fetch?: typeof fetch;
  onProgress?: (progress: StoreProgress) => void;
  signal?: AbortSignal;
}

export interface StoreResult {
  stored: StoredAssets;
  fromCache: number;
  fromNetwork: number;
  /** Cached entries that failed verification and were replaced from the network. */
  replaced: string[];
}

/** Whether this host offers the Cache API (absent in some private browsing modes and in Bun/Node). */
export async function cacheStorageAvailable(cacheStorage: CacheStorage | undefined = globalThis.caches): Promise<boolean> {
  if (!cacheStorage) return false;
  try {
    await cacheStorage.keys();
    return true;
  } catch {
    return false;
  }
}

/** Number of this pack's assets already present in its cache (unverified; for the download prompt). */
export async function cachedAssetCount(pack: PackManifest, baseUrl: string, cacheStorage: CacheStorage = caches): Promise<number> {
  const name = cacheNameFor(pack.pack_id);
  if (!(await cacheStorage.has(name))) return 0;
  const cache = await cacheStorage.open(name);
  let count = 0;
  for (const asset of packAssets(pack)) if (await cache.match(assetUrl(baseUrl, asset.path))) count += 1;
  return count;
}

/** Deletes the caches of every other pack generation. */
export async function deleteOtherPackCaches(keep: string, cacheStorage: CacheStorage = caches): Promise<string[]> {
  const deleted: string[] = [];
  for (const name of await cacheStorage.keys()) {
    if (name.startsWith(CACHE_PREFIX) && name !== keep && (await cacheStorage.delete(name))) deleted.push(name);
  }
  return deleted;
}

async function readBody(response: Response, expected: number, onChunk: (bytes: number) => void, signal?: AbortSignal): Promise<Uint8Array> {
  if (!response.body) {
    const bytes = new Uint8Array(await response.arrayBuffer());
    onChunk(bytes.byteLength);
    return bytes;
  }
  const out = new Uint8Array(expected);
  let offset = 0;
  const reader = response.body.getReader();
  for (;;) {
    if (signal?.aborted) {
      await reader.cancel();
      throw signal.reason ?? new DOMException("aborted", "AbortError");
    }
    const { done, value } = await reader.read();
    if (done) break;
    if (offset + value.byteLength > expected) {
      await reader.cancel();
      throw new PackIntegrityError(`${response.url}: more than the ${expected} bytes the manifest declares`);
    }
    out.set(value, offset);
    offset += value.byteLength;
    onChunk(value.byteLength);
  }
  return offset === expected ? out : out.subarray(0, offset);
}

async function verify(asset: PackAsset, bytes: Uint8Array): Promise<string | null> {
  if (bytes.byteLength !== asset.bytes) return `${asset.path}: ${bytes.byteLength} bytes, manifest says ${asset.bytes}`;
  const digest = await sha256Hex(bytes);
  if (digest !== asset.sha256) return `${asset.path}: sha256 ${digest}, manifest says ${asset.sha256}`;
  return null;
}

/**
 * Page side. Fills the pack's cache with verified copies of every asset,
 * compiles the three modules, and returns the store description the workers
 * read. Throws PackIntegrityError when a downloaded asset or the pack_id does
 * not verify; network failures propagate as the fetch error.
 */
export async function storeVerifiedAssets(pack: PackManifest, options: StoreOptions): Promise<StoreResult> {
  const cacheStorage = options.cacheStorage ?? caches;
  const doFetch = options.fetch ?? fetch;
  const packId = await recomputePackId(pack);
  if (packId !== pack.pack_id) throw new PackIntegrityError(`pack_id ${pack.pack_id} does not match the manifest's artifacts (${packId})`);
  const cacheName = cacheNameFor(pack.pack_id);
  const cache = await cacheStorage.open(cacheName);
  const assets = packAssets(pack);
  const progress: StoreProgress = {
    loadedBytes: 0,
    totalBytes: assets.reduce((sum, a) => sum + a.bytes, 0),
    verifiedAssets: 0,
    totalAssets: assets.length,
    fromCache: 0,
    fromNetwork: 0,
  };
  const report = () => options.onProgress?.({ ...progress });
  const urls: Record<string, string> = {};
  const verified: Record<string, string> = {};
  const replaced: string[] = [];
  const moduleBytes = new Map<string, Promise<WebAssembly.Module>>();
  const modulePaths = new Set([pack.compiler.rustc.path, pack.modules.policy.path, pack.modules.expander.path]);

  await Promise.all(assets.map(async (asset) => {
    const url = assetUrl(options.baseUrl, asset.path);
    urls[asset.path] = url;
    let bytes: Uint8Array | null = null;
    const cached = await cache.match(url);
    if (cached) {
      let read = 0;
      const candidate = await readBody(cached, asset.bytes, (n) => {
        read += n;
        progress.loadedBytes += n;
        report();
      }, options.signal).catch(() => null);
      if (candidate && (await verify(asset, candidate)) === null) {
        bytes = candidate;
        progress.fromCache += 1;
      } else {
        progress.loadedBytes -= read;
        replaced.push(asset.path);
        await cache.delete(url);
      }
    }
    if (bytes === null) {
      const response = await doFetch(url, { signal: options.signal, credentials: "omit" });
      if (!response.ok) throw new Error(`${asset.path}: HTTP ${response.status} from ${url}`);
      const downloaded = await readBody(response, asset.bytes, (n) => {
        progress.loadedBytes += n;
        report();
      }, options.signal);
      const problem = await verify(asset, downloaded);
      if (problem !== null) throw new PackIntegrityError(problem);
      await cache.put(url, new Response(downloaded as Uint8Array<ArrayBuffer>, {
        headers: { "content-type": "application/octet-stream", "content-length": String(downloaded.byteLength) },
      }));
      bytes = downloaded;
      progress.fromNetwork += 1;
    }
    verified[asset.path] = asset.sha256;
    if (modulePaths.has(asset.path)) moduleBytes.set(asset.path, WebAssembly.compile(bytes as Uint8Array<ArrayBuffer>));
    progress.verifiedAssets += 1;
    report();
  }));

  const [rustc, policy, expander] = await Promise.all([
    moduleBytes.get(pack.compiler.rustc.path)!,
    moduleBytes.get(pack.modules.policy.path)!,
    moduleBytes.get(pack.modules.expander.path)!,
  ]);
  await deleteOtherPackCaches(cacheName, cacheStorage);
  const moduleVerified: Record<string, string> = {};
  for (const path of modulePaths) moduleVerified[path] = verified[path]!;
  return {
    stored: {
      packId: pack.pack_id,
      modules: { rustc, policy, expander },
      verified: moduleVerified,
      store: { kind: "cache-storage", cacheName, urls },
    },
    fromCache: progress.fromCache,
    fromNetwork: progress.fromNetwork,
    replaced,
  };
}

/**
 * Worker side. Reads the sysroot bundle, the pack artifacts, and the
 * framework sources from the store, verifies each against the manifest, and
 * returns VerifiedAssets for createPipelineContext. Any missing or mismatching
 * entry throws PackIntegrityError; the page then reloads the store.
 */
export async function readStoredAssets(pack: PackManifest, stored: StoredAssets, cacheStorage: CacheStorage = caches): Promise<VerifiedAssets> {
  if (stored.packId !== pack.pack_id) throw new PackIntegrityError(`stored assets are for pack ${stored.packId}, not ${pack.pack_id}`);
  const cache = await cacheStorage.open(stored.store.cacheName);
  const verified: Record<string, string> = { ...stored.verified };
  const files: Record<string, Uint8Array> = {};
  let sysrootBundle: Uint8Array | null = null;
  const needed = [pack.compiler.sysroot_bundle, ...pack.artifacts, ...pack.framework_sources];
  await Promise.all(needed.map(async (asset) => {
    const url = stored.store.urls[asset.path];
    const response = url === undefined ? undefined : await cache.match(url);
    if (!response) throw new PackIntegrityError(`${asset.path} is not in ${stored.store.cacheName}`);
    const bytes = new Uint8Array(await response.arrayBuffer());
    const problem = await verify(asset, bytes);
    if (problem !== null) throw new PackIntegrityError(`cached ${problem}`);
    verified[asset.path] = asset.sha256;
    if (asset.path === pack.compiler.sysroot_bundle.path) sysrootBundle = bytes;
    else files[asset.path] = bytes;
  }));
  return { packId: stored.packId, modules: stored.modules, sysrootBundle: sysrootBundle!, files, verified };
}
