// Test page for the release cache and corruption tests: exposes window.ir21 over
// PackCache (src/pack-cache.ts) and the worker controller. The asset host is a
// separate origin (config.json `base`), so every asset request is a CORS fetch
// under the hosting.toml headers. run.ts drives the page and the asset host.

import { KrsCompiler, loadVerifiedAssets } from "../../src/controller.ts";
import { type CacheEvent, InstalledRelease, leaseFor, namespaceFor, PackCache, PackCacheError, packFailureEvent, POINTER_CACHE } from "../../src/pack-cache.ts";
import type { CompileEvent, LessonManifest } from "../../src/protocol.ts";

let base = "";
const installed = new Map<string, InstalledRelease>();
const compilers = new Map<string, KrsCompiler>();

function describeError(error: unknown) {
  if (error instanceof PackCacheError) return { ...error.toJSON(), failureEvent: packFailureEvent(error, 0), isPackIntegrityError: true };
  return { name: (error as Error)?.name ?? "Error", message: String((error as Error)?.message ?? error), isPackIntegrityError: false };
}

async function config() {
  base = ((await (await fetch("./config.json", { cache: "no-store" })).json()) as { base: string }).base;
  return { base, origin: location.origin, timeOrigin: performance.timeOrigin, userAgent: navigator.userAgent, locks: "locks" in navigator, caches: "caches" in globalThis };
}

/** PackCache.open() with a fresh event log. */
async function open() {
  const events: CacheEvent[] = [];
  const cache = new PackCache({ baseUrl: base, onEvent: (e) => events.push(e) });
  const started = performance.now();
  try {
    const release = await cache.open();
    installed.set(release.packId, release);
    return { ok: true, packId: release.packId, release: release.ref.release, namespace: release.namespace, ms: performance.now() - started, events };
  } catch (error) {
    return { ok: false, error: describeError(error), ms: performance.now() - started, events };
  }
}

async function cleanup() {
  const events: CacheEvent[] = [];
  const results = await new PackCache({ baseUrl: base, onEvent: (e) => events.push(e) }).cleanup();
  return { results, events };
}

function summary(events: CompileEvent[]) {
  const last = events.at(-1);
  if (!last) return { type: "none" };
  if (last.type === "success") return { type: "success", bundleSha256: last.bundleSha256, bytes: last.bundle.byteLength };
  if (last.type === "failure") return { type: "failure", stage: last.stage, code: last.code, message: last.message };
  return { type: last.type };
}

/** Builds a controller from an installed release (optionally holding its lease) and compiles the lesson. */
async function compile(packId: string, options: { lease?: boolean; keep?: boolean } = {}) {
  const release = installed.get(packId);
  if (!release) throw new Error(`pack ${packId} is not installed in this page`);
  const started = performance.now();
  let compiler = compilers.get(packId);
  if (!compiler) {
    const pack = release.workerPack();
    const assets = await loadVerifiedAssets(pack, release.read);
    compiler = await KrsCompiler.create(pack, assets, {
      createWorker: () => new Worker(new URL("./worker.js", location.href), { type: "module" }),
      ...(options.lease ? { lease: release.lease } : {}),
    });
    if (options.keep) compilers.set(packId, compiler);
  }
  const lesson = JSON.parse(release.text("lessons/tour-minimal/lesson.json")) as LessonManifest;
  const events: CompileEvent[] = [];
  for await (const event of compiler.compile({ lesson, files: { "src/lib.rs": release.text("lessons/tour-minimal/src/lib.rs") } })) events.push(event);
  if (!options.keep && !compilers.has(packId)) compiler.dispose();
  return { packId, ms: performance.now() - started, result: summary(events), resources: performance.getEntriesByType("resource").length };
}

function dispose(packId: string) {
  compilers.get(packId)?.dispose();
  compilers.delete(packId);
  installed.delete(packId);
  return true;
}

/** Test-only fault: replaces a cached entry with bytes of the same length and one flipped byte. */
async function corrupt(packId: string, assetId: string) {
  const release = installed.get(packId);
  if (!release) throw new Error(`pack ${packId} is not installed`);
  const asset = release.release.assets.find((a) => a.id === assetId);
  if (!asset) throw new Error(`no asset ${assetId}`);
  const url = new URL(asset.url, base).href;
  const cache = await caches.open(namespaceFor(packId));
  const response = await cache.match(url);
  if (!response) throw new Error(`${assetId} is not cached`);
  const bytes = new Uint8Array(await response.arrayBuffer());
  const middle = bytes.length >> 1;
  bytes[middle] = bytes[middle]! ^ 0x01;
  await cache.put(url, new Response(bytes, { headers: { "content-type": asset.required_media_type } }));
  return { url, bytes: bytes.byteLength };
}

async function hasEntry(packId: string, url: string) {
  return (await (await caches.open(namespaceFor(packId))).match(new URL(url, base).href)) !== undefined;
}

async function deleteNamespace(packId: string) {
  return caches.delete(namespaceFor(packId));
}

async function state() {
  const names = await caches.keys();
  const namespaces: Record<string, number> = {};
  for (const name of names) if (name !== POINTER_CACHE) namespaces[name] = (await (await caches.open(name)).keys()).length;
  const pointer = await new PackCache({ baseUrl: base }).active();
  const locks = navigator.locks ? await navigator.locks.query() : null;
  return {
    namespaces,
    pointer,
    heldLeases: (locks?.held ?? []).map((l) => ({ name: l.name, mode: l.mode })),
    pendingLeases: (locks?.pending ?? []).map((l) => ({ name: l.name, mode: l.mode })),
    storage: navigator.storage?.estimate ? await navigator.storage.estimate() : null,
  };
}

(globalThis as unknown as { ir21: unknown }).ir21 = { config, open, cleanup, compile, dispose, corrupt, hasEntry, deleteNamespace, state, leaseFor, namespaceFor };
(globalThis as unknown as { ir15Ready: boolean }).ir15Ready = true;
document.getElementById("status")!.textContent = "ready: window.ir21";
