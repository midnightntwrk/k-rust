// Unit tests of the stored-assets path over PackCache: the page
// installs a release, compiles the modules, and hands workers a description of
// the namespace; readStoredAssets reads and verifies the rest. In-memory
// CacheStorage and fetch; no staged assets needed.

import { describe, expect, test } from "bun:test";
import { namespaceFor, PackCache, PackCacheError, readStoredAssets } from "../../src/pack-cache.ts";
import { checkActivation, sha256Hex } from "../../src/pack.ts";
import type { PackManifest } from "../../src/protocol.ts";

const EMPTY_WASM = new Uint8Array([0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);
const BASE = "https://pack.example/lesson/";
const text = (s: string) => new TextEncoder().encode(s);

class MemoryCache {
  entries = new Map<string, Uint8Array>();
  async match(url: string) {
    const bytes = this.entries.get(url);
    return bytes ? new Response(bytes.slice() as Uint8Array<ArrayBuffer>) : undefined;
  }
  async put(url: string, response: Response) {
    this.entries.set(url, new Uint8Array(await response.arrayBuffer()));
  }
  async delete(url: string) {
    return this.entries.delete(url);
  }
}

class MemoryCacheStorage {
  caches = new Map<string, MemoryCache>();
  async open(name: string) {
    if (!this.caches.has(name)) this.caches.set(name, new MemoryCache());
    return this.caches.get(name)!;
  }
  async has(name: string) {
    return this.caches.has(name);
  }
  async keys() {
    return [...this.caches.keys()];
  }
  async delete(name: string) {
    return this.caches.delete(name);
  }
}

async function fixture() {
  const files: Record<string, { bytes: Uint8Array; role: string }> = {
    "pack/compiler/rustc.wasm": { bytes: EMPTY_WASM, role: "compiler" },
    "pack/sysroot/sysroot.bundle": { bytes: text("sysroot bundle bytes"), role: "sysroot-bundle" },
    "pack/deps/libkrs.rlib": { bytes: text("an rlib"), role: "target-rlib" },
    "pack/krs/src/lib.rs": { bytes: text("// facade\n"), role: "framework-source" },
    "modules/krs_lesson_policy.wasm": { bytes: EMPTY_WASM, role: "lesson-policy" },
    "modules/krs_expand_wasm.wasm": { bytes: new Uint8Array([...EMPTY_WASM, 0x00, 0x04, 0x03, 0x61, 0x62, 0x63]), role: "krs-expander" },
    "licenses/licenses.toml": { bytes: text("licenses"), role: "license-inventory" },
  };
  const packAsset = async (path: string) => ({ path, bytes: files[path]!.bytes.byteLength, sha256: await sha256Hex(files[path]!.bytes) });
  const pack = {
    schema: 1,
    kind: "krs-browser-worker-pack",
    pack_id: "sha256:1111",
    integrity: { rule: "sorted-artifact-lines", root: "pack" },
    compiler: { rustc: await packAsset("pack/compiler/rustc.wasm"), sysroot_bundle: await packAsset("pack/sysroot/sysroot.bundle"), host_rustc_vv: [] },
    modules: { policy: await packAsset("modules/krs_lesson_policy.wasm"), expander: await packAsset("modules/krs_expand_wasm.wasm"), krs_revision: "t", crates_tree: "t" },
    artifacts: [{ ...(await packAsset("pack/deps/libkrs.rlib")), role: "target-rlib", crate_name: "krs", mount: "/pack/deps/libkrs.rlib" }],
    framework_sources: [{ ...(await packAsset("pack/krs/src/lib.rs")), mount: "/krs/crates/krs/src/lib.rs" }],
  } as unknown as PackManifest;
  files["pack.json"] = { bytes: text(JSON.stringify(pack)), role: "worker-pack-manifest" };
  const network: Record<string, Uint8Array> = {};
  const assets = [];
  for (const [id, { bytes, role }] of Object.entries(files)) {
    const sha = await sha256Hex(bytes);
    const url = `blobs/${sha}.bin`;
    network[`${BASE}${url}`] = bytes;
    assets.push({ id, role, url, required_media_type: "application/octet-stream", decoded_bytes: bytes.byteLength, decoded_sha256: sha, cache_policy: "immutable-content-addressed" });
  }
  const releaseBytes = text(JSON.stringify({ schema: 1, kind: "krs-browser-lesson-release", pack_id: pack.pack_id, worker_pack_asset: "pack.json", assets }));
  const releaseSha = await sha256Hex(releaseBytes);
  network[`${BASE}releases/${releaseSha}.json`] = releaseBytes;
  network[`${BASE}index.json`] = text(JSON.stringify({ schema: 1, kind: "krs-browser-lesson-index", active: { release: `releases/${releaseSha}.json`, sha256: releaseSha, pack_id: pack.pack_id } }));
  const requests: string[] = [];
  const fakeFetch = (async (input: string | URL | Request) => {
    const url = String(input);
    requests.push(url);
    const bytes = network[url];
    return bytes ? new Response(bytes.slice() as Uint8Array<ArrayBuffer>) : new Response("missing", { status: 404 });
  }) as unknown as typeof fetch;
  const storage = new MemoryCacheStorage();
  const cache = new PackCache({ baseUrl: BASE, caches: storage as unknown as CacheStorage, fetch: fakeFetch, locks: undefined });
  return { pack, files, requests, storage, cache };
}

describe("PackCache stored assets", () => {
  test("inspect reports the required size without fetching assets", async () => {
    const { cache, requests, files } = await fixture();
    const preview = await cache.inspect();
    const required = Object.entries(files).filter(([, f]) => f.role !== "license-inventory");
    expect(preview.requiredAssets).toBe(required.length);
    expect(preview.requiredBytes).toBe(required.reduce((s, [, f]) => s + f.bytes.byteLength, 0));
    expect(preview.cachedAssets).toBe(0);
    expect(requests.every((u) => u.endsWith("index.json") || u.includes("/releases/"))).toBe(true);
  });

  test("a worker reads verified assets from the installed namespace", async () => {
    const { cache, storage, pack, requests } = await fixture();
    const installed = await cache.open();
    const stored = await cache.storedAssets(installed);
    expect(stored.store.cacheName).toBe(namespaceFor(pack.pack_id));
    expect(Object.keys(stored.verified).sort()).toEqual(["modules/krs_expand_wasm.wasm", "modules/krs_lesson_policy.wasm", "pack/compiler/rustc.wasm"]);
    const assets = await readStoredAssets(pack, stored, storage as unknown as CacheStorage);
    expect(checkActivation(pack, assets)).toEqual([]);
    expect(new TextDecoder().decode(assets.files["pack/deps/libkrs.rlib"])).toBe("an rlib");
    expect(requests.some((u) => u.includes("licenses"))).toBe(false);
    expect((await cache.inspect()).cachedAssets).toBe((await cache.inspect()).requiredAssets);
  });

  test("a corrupted cache entry fails worker start-up and is replaced by the next install", async () => {
    const { cache, storage, pack, requests } = await fixture();
    const stored = await cache.storedAssets(await cache.open());
    const url = stored.store.urls["pack/deps/libkrs.rlib"]!;
    (await storage.open(stored.store.cacheName)).entries.set(url, text("an rlim"));
    const error = await readStoredAssets(pack, stored, storage as unknown as CacheStorage).catch((e: unknown) => e);
    expect(error).toBeInstanceOf(PackCacheError);
    expect((error as PackCacheError).code).toBe("pack-integrity");
    requests.length = 0;
    const again = await cache.storedAssets(await cache.open());
    expect(requests.filter((u) => u.includes("/blobs/"))).toEqual([url]);
    expect(checkActivation(pack, await readStoredAssets(pack, again, storage as unknown as CacheStorage))).toEqual([]);
  });
});
