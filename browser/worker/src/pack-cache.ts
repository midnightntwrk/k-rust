// Application cache for a published browser-lesson release (IR-21), implementing
// the BL-009 [application_cache] rules over the Cache API and Web Locks:
//
// - namespace: one Cache API cache per pack, "krs-pack-<pack_id hex>"; keys are
//   the absolute content-addressed asset URLs (browser/release/release-format.toml);
// - write rule: bytes are written only after their decoded length and SHA-256
//   match the release manifest; a truncated or corrupt response is never cached;
// - activation rule: the active pointer (cache "krs-pack-pointer") switches to a
//   release only after every required asset of that release is verified;
// - corruption rule: a cached entry whose bytes do not verify is evicted and
//   refetched once from the same URL; a second mismatch is a pack-integrity error;
// - offline rule: when index.json cannot be fetched, the page starts from the
//   active release only if it and every required asset are cached and verify;
// - cleanup rule: an inactive namespace is deleted only when no page or worker
//   holds its Web Locks lease "krs-pack-lease:<pack_id hex>" (a worker holds a
//   shared lease for its lifetime; see KrsCompilerOptions.lease);
// - no fallback: a failure never switches to another release, a mutable URL, or
//   another pack; the caller receives a PackCacheError.

import { PackIntegrityError, sha256Hex } from "./pack.ts";
import type { CompileEvent, PackAsset, PackManifest, StoredAssets, VerifiedAssets } from "./protocol.ts";

export interface ReleaseAsset {
  id: string;
  role: string;
  url: string;
  required_media_type: string;
  decoded_bytes: number;
  decoded_sha256: string;
  cache_policy: string;
}

export interface Release {
  schema: 1;
  kind: "krs-browser-lesson-release";
  pack_id: string;
  worker_pack_asset: string;
  assets: ReleaseAsset[];
  [key: string]: unknown;
}

export interface ReleaseRef {
  release: string;
  sha256: string;
  pack_id: string;
}

export interface ReleaseIndex {
  schema: 1;
  kind: "krs-browser-lesson-index";
  active: ReleaseRef;
}

export type CacheEvent =
  | { type: "index"; source: "network" | "offline-pointer"; release: string; packId: string }
  | { type: "verified"; id: string; from: "cache" | "network" }
  | { type: "fetch"; id: string; url: string; attempt: number }
  | { type: "cache-mismatch"; id: string; url: string; reason: string }
  | { type: "evict"; id: string; url: string }
  | { type: "reject"; id: string; url: string; reason: string }
  | { type: "activate"; packId: string; release: string }
  | { type: "cleanup"; namespace: string; result: "deleted" | "leased" | "active" };

export type PackCacheReason =
  | "digest-mismatch"
  | "length-mismatch"
  | "http-status"
  | "network"
  | "release-mismatch"
  | "offline-incomplete";

/**
 * The integrity error surface: code "pack-integrity" for bytes that do not
 * verify (the BL-009 corruption rule), "pack-unavailable" when the bytes cannot
 * be obtained (network, HTTP status, offline without a complete generation).
 */
export class PackCacheError extends PackIntegrityError {
  readonly code: "pack-integrity" | "pack-unavailable";
  readonly reason: PackCacheReason;
  readonly assetId: string | null;
  readonly url: string | null;
  /** Reads of this asset before the error: 1 = one network fetch, 2 = cached copy plus one refetch. */
  readonly attempts: number;
  constructor(reason: PackCacheReason, message: string, detail: { assetId?: string | null; url?: string | null; attempts?: number } = {}) {
    super(message);
    this.name = "PackCacheError";
    this.reason = reason;
    this.code = reason === "http-status" || reason === "network" || reason === "offline-incomplete" ? "pack-unavailable" : "pack-integrity";
    this.assetId = detail.assetId ?? null;
    this.url = detail.url ?? null;
    this.attempts = detail.attempts ?? 0;
  }

  toJSON() {
    return { name: this.name, code: this.code, reason: this.reason, assetId: this.assetId, url: this.url, attempts: this.attempts, message: this.message };
  }
}

/** The compile-event shape a UI receives for an asset failure (FailureCode pack-integrity, stage assets). */
export function packFailureEvent(error: PackCacheError, generation: number): CompileEvent {
  return { type: "failure", generation, stage: "assets", code: "pack-integrity", message: `${error.code} (${error.reason}): ${error.message}`, diagnostics: [] };
}

export const POINTER_CACHE = "krs-pack-pointer";
const NAMESPACE_PREFIX = "krs-pack-";
const hex = (packId: string) => packId.replace(/^sha256:/, "");
export const namespaceFor = (packId: string) => `${NAMESPACE_PREFIX}${hex(packId)}`;
export const leaseFor = (packId: string) => `krs-pack-lease:${hex(packId)}`;

/** Roles the worker does not need (license texts, the TOML pack manifest); fetched only on request. */
const OPTIONAL_ROLES = new Set(["license-inventory", "notice", "pack-manifest"]);

/** What a page shows before installing: the current release and how much of it is already cached. */
export interface ReleasePreview {
  ref: ReleaseRef;
  source: "network" | "offline-pointer";
  /** Required assets (the ones install() fetches) and their decoded size. */
  requiredAssets: number;
  requiredBytes: number;
  /** Decoded size of each required asset by id (for progress). */
  sizes: Record<string, number>;
  /** Required assets with an entry in the pack's namespace (not yet verified). */
  cachedAssets: number;
}

export interface PackCacheOptions {
  /** Base URL of the publication directory (index.json, releases/, blobs/). */
  baseUrl: string;
  caches?: CacheStorage;
  fetch?: typeof fetch;
  locks?: LockManager;
  onEvent?: (event: CacheEvent) => void;
}

/** A verified, activated release: every required asset is in memory and in its namespace. */
export class InstalledRelease {
  readonly release: Release;
  readonly ref: ReleaseRef;
  readonly namespace: string;
  private readonly bytes: Map<string, Uint8Array>;

  constructor(release: Release, ref: ReleaseRef, namespace: string, bytes: Map<string, Uint8Array>) {
    this.release = release;
    this.ref = ref;
    this.namespace = namespace;
    this.bytes = bytes;
  }

  get packId(): string {
    return this.release.pack_id;
  }

  get lease(): string {
    return leaseFor(this.release.pack_id);
  }

  /** Reader for loadVerifiedAssets: PackAsset paths are release asset ids. */
  read = async (id: string): Promise<Uint8Array> => {
    const bytes = this.bytes.get(id);
    if (!bytes) throw new PackCacheError("release-mismatch", `${id} is not a required asset of release ${this.ref.sha256}`, { assetId: id });
    return bytes;
  };

  text(id: string): string {
    const bytes = this.bytes.get(id);
    if (!bytes) throw new PackCacheError("release-mismatch", `${id} is not a required asset of release ${this.ref.sha256}`, { assetId: id });
    return new TextDecoder().decode(bytes);
  }

  workerPack(): PackManifest {
    return JSON.parse(this.text(this.release.worker_pack_asset)) as PackManifest;
  }
}

export class PackCache {
  private readonly base: string;
  private readonly caches: CacheStorage;
  private readonly fetchFn: typeof fetch;
  private readonly locks: LockManager | null;
  private readonly emit: (event: CacheEvent) => void;

  constructor(options: PackCacheOptions) {
    this.base = new URL(options.baseUrl, globalThis.location?.href).href.replace(/\/?$/, "/");
    this.caches = options.caches ?? globalThis.caches;
    this.fetchFn = options.fetch ?? globalThis.fetch.bind(globalThis);
    this.locks = options.locks ?? (globalThis.navigator as Navigator | undefined)?.locks ?? null;
    this.emit = options.onEvent ?? (() => {});
  }

  url(rel: string): string {
    return new URL(rel, this.base).href;
  }

  /** The pointer key: a synthetic URL under the base, never fetched. */
  private pointerKey(): string {
    return this.url("krs-pack-pointer/active");
  }

  private async get(url: string, id: string, attempt: number): Promise<Uint8Array> {
    this.emit({ type: "fetch", id, url, attempt });
    let response: Response;
    try {
      response = await this.fetchFn(url, { cache: "no-store", credentials: "omit" });
    } catch (error) {
      throw new PackCacheError("network", `${url}: ${String(error)}`, { assetId: id, url, attempts: attempt });
    }
    if (!response.ok) throw new PackCacheError("http-status", `${url}: HTTP ${response.status}`, { assetId: id, url, attempts: attempt });
    try {
      return new Uint8Array(await response.arrayBuffer());
    } catch (error) {
      throw new PackCacheError("network", `${url}: body not received completely (${String(error)})`, { assetId: id, url, attempts: attempt });
    }
  }

  private static async check(asset: ReleaseAsset, bytes: Uint8Array): Promise<PackCacheReason | null> {
    if (bytes.byteLength !== asset.decoded_bytes) return "length-mismatch";
    return (await sha256Hex(bytes)) === asset.decoded_sha256 ? null : "digest-mismatch";
  }

  /** Verified bytes of one asset: the cached copy if it verifies, otherwise one network fetch (BL-009 corruption rule). */
  private async ensure(cache: Cache, asset: ReleaseAsset): Promise<Uint8Array> {
    const url = this.url(asset.url);
    let attempts = 0;
    const cached = await cache.match(url);
    if (cached) {
      attempts += 1;
      const bytes = new Uint8Array(await cached.arrayBuffer());
      const bad = await PackCache.check(asset, bytes);
      if (bad === null) {
        this.emit({ type: "verified", id: asset.id, from: "cache" });
        return bytes;
      }
      this.emit({ type: "cache-mismatch", id: asset.id, url, reason: bad });
      await cache.delete(url);
      this.emit({ type: "evict", id: asset.id, url });
    }
    attempts += 1;
    const bytes = await this.get(url, asset.id, attempts);
    const bad = await PackCache.check(asset, bytes);
    if (bad !== null) {
      this.emit({ type: "reject", id: asset.id, url, reason: bad });
      throw new PackCacheError(bad, `${asset.id}: ${bytes.byteLength} bytes${bad === "digest-mismatch" ? " with another SHA-256" : ""} from ${url}; the release requires ${asset.decoded_bytes} bytes, sha256 ${asset.decoded_sha256}`, { assetId: asset.id, url, attempts });
    }
    await cache.put(url, new Response(bytes as Uint8Array<ArrayBuffer>, { headers: { "content-type": asset.required_media_type } }));
    this.emit({ type: "verified", id: asset.id, from: "network" });
    return bytes;
  }

  private async releaseBytes(ref: ReleaseRef, cache: Cache, allowNetwork: boolean): Promise<Release> {
    const url = this.url(ref.release);
    const asset: ReleaseAsset = { id: ref.release, role: "release", url: ref.release, required_media_type: "application/json", decoded_bytes: -1, decoded_sha256: ref.sha256, cache_policy: "immutable-content-addressed" };
    const cached = await cache.match(url);
    let bytes: Uint8Array | null = cached ? new Uint8Array(await cached.arrayBuffer()) : null;
    if (bytes && (await sha256Hex(bytes)) !== ref.sha256) {
      this.emit({ type: "cache-mismatch", id: ref.release, url, reason: "digest-mismatch" });
      await cache.delete(url);
      this.emit({ type: "evict", id: ref.release, url });
      bytes = null;
    }
    if (!bytes) {
      if (!allowNetwork) throw new PackCacheError("offline-incomplete", `release ${ref.sha256} is not cached`, { assetId: ref.release, url });
      bytes = await this.get(url, asset.id, 1);
      if ((await sha256Hex(bytes)) !== ref.sha256) {
        this.emit({ type: "reject", id: ref.release, url, reason: "digest-mismatch" });
        throw new PackCacheError("digest-mismatch", `release manifest at ${url} does not hash to ${ref.sha256}`, { assetId: ref.release, url, attempts: 1 });
      }
      await cache.put(url, new Response(bytes as Uint8Array<ArrayBuffer>, { headers: { "content-type": "application/json" } }));
    }
    const release = JSON.parse(new TextDecoder().decode(bytes)) as Release;
    if (release.kind !== "krs-browser-lesson-release" || release.schema !== 1) throw new PackCacheError("release-mismatch", `${url} is not a schema-1 release manifest`, { url });
    if (release.pack_id !== ref.pack_id) throw new PackCacheError("release-mismatch", `release ${ref.sha256} is pack ${release.pack_id}, the index says ${ref.pack_id}`, { url });
    return release;
  }

  /**
   * Verifies (fetching what is missing or corrupt) every required asset of
   * `ref`, then atomically makes it the active release. Nothing is activated
   * when any asset fails; the previous active release stays active.
   */
  async install(ref: ReleaseRef, options: { offline?: boolean } = {}): Promise<InstalledRelease> {
    const namespace = namespaceFor(ref.pack_id);
    const cache = await this.caches.open(namespace);
    const release = await this.releaseBytes(ref, cache, !options.offline);
    const required = release.assets.filter((a) => !OPTIONAL_ROLES.has(a.role));
    if (!required.some((a) => a.id === release.worker_pack_asset)) throw new PackCacheError("release-mismatch", "the release has no worker pack asset");
    const bytes = new Map<string, Uint8Array>();
    for (const asset of required) {
      try {
        bytes.set(asset.id, await this.ensure(cache, asset));
      } catch (error) {
        if (options.offline && error instanceof PackCacheError && error.code === "pack-unavailable") {
          throw new PackCacheError("offline-incomplete", `offline and ${asset.id} is not in the verified cache: ${error.message}`, { assetId: asset.id, url: error.url, attempts: error.attempts });
        }
        throw error;
      }
    }
    // The worker pack must describe exactly these bytes (pack.json is itself a verified asset).
    const pack = JSON.parse(new TextDecoder().decode(bytes.get(release.worker_pack_asset)!)) as PackManifest;
    if (pack.pack_id !== release.pack_id) throw new PackCacheError("release-mismatch", `pack.json is pack ${pack.pack_id}, the release ${release.pack_id}`);
    const pointer = await this.caches.open(POINTER_CACHE);
    await pointer.put(this.pointerKey(), new Response(JSON.stringify(ref), { headers: { "content-type": "application/json" } }));
    this.emit({ type: "activate", packId: release.pack_id, release: ref.release });
    return new InstalledRelease(release, ref, namespace, bytes);
  }

  /** The active pointer, or null. */
  async active(): Promise<ReleaseRef | null> {
    const pointer = await this.caches.open(POINTER_CACHE);
    const response = await pointer.match(this.pointerKey());
    return response ? ((await response.json()) as ReleaseRef) : null;
  }

  /**
   * Page start: follow index.json (no-cache) to the current release and install
   * it. Only when index.json itself cannot be fetched (network) does the page
   * start offline from the active release. Integrity errors never fall back.
   */
  async open(): Promise<InstalledRelease> {
    let index: ReleaseIndex;
    try {
      const bytes = await this.get(this.url("index.json"), "index.json", 1);
      index = JSON.parse(new TextDecoder().decode(bytes)) as ReleaseIndex;
    } catch (error) {
      if (!(error instanceof PackCacheError) || error.reason !== "network") throw error;
      const ref = await this.active();
      if (!ref) throw new PackCacheError("offline-incomplete", `index.json is unreachable and no release is active (${error.message})`, { url: error.url });
      this.emit({ type: "index", source: "offline-pointer", release: ref.release, packId: ref.pack_id });
      return this.install(ref, { offline: true });
    }
    if (index.kind !== "krs-browser-lesson-index" || index.schema !== 1) throw new PackCacheError("release-mismatch", "index.json is not a schema-1 index");
    this.emit({ type: "index", source: "network", release: index.active.release, packId: index.active.pack_id });
    return this.install(index.active);
  }

  /**
   * The current release without installing it: index.json (or, when it cannot
   * be fetched, the active pointer) and the content-addressed release manifest,
   * which is verified and cached. No asset is fetched.
   */
  async inspect(): Promise<ReleasePreview> {
    let ref: ReleaseRef;
    let source: ReleasePreview["source"] = "network";
    try {
      const index = JSON.parse(new TextDecoder().decode(await this.get(this.url("index.json"), "index.json", 1))) as ReleaseIndex;
      if (index.kind !== "krs-browser-lesson-index" || index.schema !== 1) throw new PackCacheError("release-mismatch", "index.json is not a schema-1 index");
      ref = index.active;
    } catch (error) {
      if (!(error instanceof PackCacheError) || error.reason !== "network") throw error;
      const active = await this.active();
      if (!active) throw new PackCacheError("offline-incomplete", `index.json is unreachable and no release is active (${error.message})`, { url: error.url });
      ref = active;
      source = "offline-pointer";
    }
    const cache = await this.caches.open(namespaceFor(ref.pack_id));
    const release = await this.releaseBytes(ref, cache, source === "network");
    const required = release.assets.filter((a) => !OPTIONAL_ROLES.has(a.role));
    let cachedAssets = 0;
    for (const asset of required) if (await cache.match(this.url(asset.url))) cachedAssets += 1;
    const sizes = Object.fromEntries(required.map((a) => [a.id, a.decoded_bytes]));
    return { ref, source, requiredAssets: required.length, requiredBytes: required.reduce((sum, a) => sum + a.decoded_bytes, 0), sizes, cachedAssets };
  }

  /**
   * IR-20: compiles the three modules from an installed release and describes
   * where each worker reads the other assets (the release's namespace, keyed by
   * content-addressed URL). The returned object holds no asset bytes; drop the
   * InstalledRelease afterwards so the page does not keep them either.
   */
  async storedAssets(installed: InstalledRelease, pack: PackManifest = installed.workerPack()): Promise<StoredAssets> {
    if (pack.pack_id !== installed.packId) throw new PackCacheError("release-mismatch", `pack.json is pack ${pack.pack_id}, the release ${installed.packId}`);
    const byId = new Map(installed.release.assets.map((a) => [a.id, a]));
    const urls: Record<string, string> = {};
    for (const asset of [pack.compiler.sysroot_bundle, ...pack.artifacts, ...pack.framework_sources]) {
      const entry = byId.get(asset.path);
      if (!entry || entry.decoded_sha256 !== asset.sha256 || entry.decoded_bytes !== asset.bytes) {
        throw new PackCacheError("release-mismatch", `${asset.path} is not a release asset with the pack's digest`, { assetId: asset.path });
      }
      urls[asset.path] = this.url(entry.url);
    }
    const modules = [pack.compiler.rustc, pack.modules.policy, pack.modules.expander];
    const verified: Record<string, string> = {};
    const compiled = await Promise.all(modules.map(async (asset) => {
      const bytes = await installed.read(asset.path);
      if (bytes.byteLength !== asset.bytes || (await sha256Hex(bytes)) !== asset.sha256) {
        throw new PackCacheError("digest-mismatch", `${asset.path} does not match pack.json`, { assetId: asset.path });
      }
      verified[asset.path] = asset.sha256;
      return WebAssembly.compile(bytes as Uint8Array<ArrayBuffer>);
    }));
    return {
      packId: pack.pack_id,
      modules: { rustc: compiled[0]!, policy: compiled[1]!, expander: compiled[2]! },
      verified,
      store: { kind: "cache-storage", cacheName: installed.namespace, urls },
    };
  }

  /** Deletes every inactive pack namespace whose lease nobody holds. */
  async cleanup(): Promise<Array<{ namespace: string; result: "deleted" | "leased" | "active" }>> {
    const active = await this.active();
    const activeNs = active ? namespaceFor(active.pack_id) : null;
    const results: Array<{ namespace: string; result: "deleted" | "leased" | "active" }> = [];
    for (const name of await this.caches.keys()) {
      if (!name.startsWith(NAMESPACE_PREFIX) || name === POINTER_CACHE) continue;
      let result: "deleted" | "leased" | "active";
      if (name === activeNs) {
        result = "active";
      } else if (this.locks) {
        const lease = `krs-pack-lease:${name.slice(NAMESPACE_PREFIX.length)}`;
        result = await this.locks.request(lease, { mode: "exclusive", ifAvailable: true }, async (lock) => {
          if (lock === null) return "leased" as const;
          await this.caches.delete(name);
          return "deleted" as const;
        });
      } else {
        result = "leased"; // without Web Locks, leases cannot be observed: never delete
      }
      this.emit({ type: "cleanup", namespace: name, result });
      results.push({ namespace: name, result });
    }
    return results;
  }
}

/**
 * Worker side of StoredAssets (IR-20): reads the sysroot bundle, the pack
 * artifacts, and the framework sources from the pack's namespace, verifies each
 * against the worker pack manifest, and returns VerifiedAssets for
 * createPipelineContext. A missing or mismatching entry is a PackCacheError
 * (pack-integrity); the page's next PackCache.install() evicts and refetches it.
 */
export async function readStoredAssets(pack: PackManifest, stored: StoredAssets, cacheStorage: CacheStorage = globalThis.caches): Promise<VerifiedAssets> {
  if (stored.packId !== pack.pack_id) throw new PackCacheError("release-mismatch", `stored assets are for pack ${stored.packId}, not ${pack.pack_id}`);
  const cache = await cacheStorage.open(stored.store.cacheName);
  const verified: Record<string, string> = { ...stored.verified };
  const files: Record<string, Uint8Array> = {};
  let sysrootBundle: Uint8Array | null = null;
  const needed: PackAsset[] = [pack.compiler.sysroot_bundle, ...pack.artifacts, ...pack.framework_sources];
  await Promise.all(needed.map(async (asset) => {
    const url = stored.store.urls[asset.path];
    const response = url === undefined ? undefined : await cache.match(url);
    if (!response) throw new PackCacheError("digest-mismatch", `${asset.path} is not in ${stored.store.cacheName}`, { assetId: asset.path, url: url ?? null });
    const bytes = new Uint8Array(await response.arrayBuffer());
    if (bytes.byteLength !== asset.bytes) {
      throw new PackCacheError("length-mismatch", `cached ${asset.path}: ${bytes.byteLength} bytes, pack.json says ${asset.bytes}`, { assetId: asset.path, url: url ?? null });
    }
    if ((await sha256Hex(bytes)) !== asset.sha256) {
      throw new PackCacheError("digest-mismatch", `cached ${asset.path} does not match its SHA-256 in pack.json`, { assetId: asset.path, url: url ?? null });
    }
    verified[asset.path] = asset.sha256;
    if (asset.path === pack.compiler.sysroot_bundle.path) sysrootBundle = bytes;
    else files[asset.path] = bytes;
  }));
  return { packId: stored.packId, modules: stored.modules, sysrootBundle: sysrootBundle!, files, verified };
}
