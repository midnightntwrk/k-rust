// Unit tests of the Cache API asset store (IR-20) over an in-memory
// CacheStorage and fetch; no staged assets needed.

import { describe, expect, test } from "bun:test";
import { cacheNameFor, readStoredAssets, storeVerifiedAssets } from "../../src/asset-store.ts";
import { checkActivation, ir14PackId, PackIntegrityError, sha256Hex } from "../../src/pack.ts";
import type { PackAsset, PackManifest } from "../../src/protocol.ts";

const EMPTY_WASM = new Uint8Array([0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);
const BASE = "https://pack.example/base/";

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

async function asset(path: string, bytes: Uint8Array): Promise<PackAsset> {
  return { path, bytes: bytes.byteLength, sha256: await sha256Hex(bytes) };
}

async function fixturePack() {
  const text = (s: string) => new TextEncoder().encode(s);
  const files: Record<string, Uint8Array> = {
    "pack/compiler/rustc.wasm": EMPTY_WASM,
    "pack/sysroot/sysroot.bundle": text("sysroot bundle bytes"),
    "pack/deps/libkrs.rlib": text("an rlib"),
    "pack/krs/src/lib.rs": text("// facade\n"),
    "modules/policy.wasm": EMPTY_WASM,
    "modules/expander.wasm": EMPTY_WASM,
  };
  const rustc = await asset("pack/compiler/rustc.wasm", files["pack/compiler/rustc.wasm"]!);
  const bundle = await asset("pack/sysroot/sysroot.bundle", files["pack/sysroot/sysroot.bundle"]!);
  const rlib = await asset("pack/deps/libkrs.rlib", files["pack/deps/libkrs.rlib"]!);
  const source = await asset("pack/krs/src/lib.rs", files["pack/krs/src/lib.rs"]!);
  const packOwn = [rustc, bundle, rlib, source].map((a) => ({ path: a.path.slice("pack/".length), sha256: a.sha256 }));
  const pack = {
    schema: 1,
    kind: "krs-browser-worker-pack",
    pack_id: await ir14PackId(packOwn),
    integrity: { rule: "ir14-sorted-artifact-lines", root: "pack" },
    compiler: { rustc, sysroot_bundle: bundle, host_rustc_vv: [] },
    modules: {
      policy: await asset("modules/policy.wasm", EMPTY_WASM),
      expander: await asset("modules/expander.wasm", EMPTY_WASM),
      krs_revision: "test",
      crates_tree: "test",
    },
    artifacts: [{ ...rlib, role: "target-rlib", crate_name: "krs", mount: "/pack/deps/libkrs.rlib" }],
    framework_sources: [{ ...source, mount: "/krs/crates/krs/src/lib.rs" }],
  } as unknown as PackManifest;
  const requests: string[] = [];
  const network: Record<string, Uint8Array> = Object.fromEntries(Object.entries(files).map(([p, b]) => [`${BASE}${p}`, b]));
  const fakeFetch = (async (input: string | URL | Request) => {
    const url = String(input);
    requests.push(url);
    const bytes = network[url];
    return bytes ? new Response(bytes.slice() as Uint8Array<ArrayBuffer>) : new Response("missing", { status: 404 });
  }) as unknown as typeof fetch;
  return { pack, files, network, requests, fakeFetch };
}

describe("asset store", () => {
  test("cold store downloads and caches every asset; a worker reads them back verified", async () => {
    const { pack, requests, fakeFetch } = await fixturePack();
    const storage = new MemoryCacheStorage();
    const stale = await storage.open(`${cacheNameFor("sha256:old")}`);
    await stale.put("x", new Response("old"));
    const result = await storeVerifiedAssets(pack, { baseUrl: BASE, cacheStorage: storage as unknown as CacheStorage, fetch: fakeFetch });
    expect(result.fromNetwork).toBe(6);
    expect(result.fromCache).toBe(0);
    expect(requests.length).toBe(6);
    expect(await storage.keys()).toEqual([cacheNameFor(pack.pack_id)]);
    expect(Object.keys(result.stored.verified).sort()).toEqual(["modules/expander.wasm", "modules/policy.wasm", "pack/compiler/rustc.wasm"]);
    const assets = await readStoredAssets(pack, result.stored, storage as unknown as CacheStorage);
    expect(checkActivation(pack, assets)).toEqual([]);
    expect(new TextDecoder().decode(assets.files["pack/deps/libkrs.rlib"])).toBe("an rlib");
    expect(new TextDecoder().decode(assets.sysrootBundle)).toBe("sysroot bundle bytes");
  });

  test("a warm store makes no request", async () => {
    const { pack, requests, fakeFetch } = await fixturePack();
    const storage = new MemoryCacheStorage();
    await storeVerifiedAssets(pack, { baseUrl: BASE, cacheStorage: storage as unknown as CacheStorage, fetch: fakeFetch });
    requests.length = 0;
    const warm = await storeVerifiedAssets(pack, { baseUrl: BASE, cacheStorage: storage as unknown as CacheStorage, fetch: fakeFetch });
    expect(warm.fromCache).toBe(6);
    expect(requests).toEqual([]);
  });

  test("a corrupted cached asset is replaced on the page and rejected by a worker", async () => {
    const { pack, fakeFetch } = await fixturePack();
    const storage = new MemoryCacheStorage();
    const first = await storeVerifiedAssets(pack, { baseUrl: BASE, cacheStorage: storage as unknown as CacheStorage, fetch: fakeFetch });
    const cache = await storage.open(cacheNameFor(pack.pack_id));
    const url = `${BASE}pack/deps/libkrs.rlib`;
    cache.entries.set(url, new TextEncoder().encode("an rlim"));
    await expect(readStoredAssets(pack, first.stored, storage as unknown as CacheStorage)).rejects.toBeInstanceOf(PackIntegrityError);
    const again = await storeVerifiedAssets(pack, { baseUrl: BASE, cacheStorage: storage as unknown as CacheStorage, fetch: fakeFetch });
    expect(again.replaced).toEqual(["pack/deps/libkrs.rlib"]);
    expect(again.fromNetwork).toBe(1);
    expect(checkActivation(pack, await readStoredAssets(pack, again.stored, storage as unknown as CacheStorage))).toEqual([]);
  });

  test("a tampered download is rejected and not cached", async () => {
    const { pack, network, fakeFetch } = await fixturePack();
    network[`${BASE}pack/deps/libkrs.rlib`] = new TextEncoder().encode("an rlim");
    const storage = new MemoryCacheStorage();
    await expect(storeVerifiedAssets(pack, { baseUrl: BASE, cacheStorage: storage as unknown as CacheStorage, fetch: fakeFetch }))
      .rejects.toBeInstanceOf(PackIntegrityError);
    const cache = await storage.open(cacheNameFor(pack.pack_id));
    expect(cache.entries.has(`${BASE}pack/deps/libkrs.rlib`)).toBe(false);
  });

  test("a manifest whose pack_id does not match its artifacts is rejected before any request", async () => {
    const { pack, requests, fakeFetch } = await fixturePack();
    const forged = { ...pack, pack_id: "sha256:0000" };
    await expect(storeVerifiedAssets(forged, { baseUrl: BASE, cacheStorage: new MemoryCacheStorage() as unknown as CacheStorage, fetch: fakeFetch }))
      .rejects.toBeInstanceOf(PackIntegrityError);
    expect(requests).toEqual([]);
  });
});
