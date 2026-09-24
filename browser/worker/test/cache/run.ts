// Browser cache and corruption tests of the release's application cache rules
// in headless Chromium and headless Firefox.
//
//   bun test/cache/run.ts --staged DIR --oracle ORACLE_TOML [--out DIR] [--work DIR]
//       [--browsers chromium,firefox] [--port 4371] [--asset-port 4391] [--load-max 40]
//
// Inputs: a staged asset directory with licenses/ (stage-assets.ts, then
// `release.py licenses`) and the tour-minimal oracle.toml of the same crates/ tree.
// The runner publishes two releases into WORK/publish with browser/release/release.py:
// A from --staged, and B from `release.py derive-generation` (a second, valid pack
// generation that differs in one framework-source byte string). A test asset host
// on its own origin serves the publication under browser/release/hosting.toml
// (CORS included) and injects faults per URL; the page (test/cache/cache-page.ts)
// drives src/pack-cache.ts and the worker controller. One fresh-profile session per
// browser runs every case in order; OUT/cache-tests-<browser>.json records each case's
// observations and verdict.

import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createServer, type Server } from "node:http";
import { join } from "node:path";
import { parseArgs } from "node:util";
import { openSite, type SiteSession } from "../harness/browsers.ts";
import { REPO, scratchPath, waitForLoad as waitForLoadAverage } from "../harness/environment.ts";
import { buildSite } from "../harness/site.ts";

const { values } = parseArgs({
  options: {
    staged: { type: "string" },
    oracle: { type: "string" },
    out: { type: "string", default: scratchPath("krs-browser-cache/evidence") },
    work: { type: "string", default: scratchPath("krs-browser-cache") },
    browsers: { type: "string", default: "chromium,firefox" },
    port: { type: "string", default: "4371" },
    "asset-port": { type: "string", default: "4391" },
    "load-max": { type: "string", default: "40" },
  },
});
if (!values.staged || !values.oracle) {
  console.error("usage: bun test/cache/run.ts --staged DIR --oracle ORACLE_TOML [--out DIR] [--browsers chromium,firefox]");
  process.exit(2);
}
const here = import.meta.dir;
const workerRoot = join(here, "../..");
const repo = REPO;
const releasePy = join(repo, "browser/release/release.py");
const work = values.work!;
const out = values.out!;
const publish = join(work, "publish");
const site = join(work, "site");
mkdirSync(out, { recursive: true });

function run(command: string[], cwd = repo): string {
  const result = Bun.spawnSync(command, { cwd, stderr: "pipe" });
  if (result.exitCode !== 0) throw new Error(`${command.join(" ")}: ${result.stderr.toString()}`);
  return result.stdout.toString();
}

const waitForLoad = () => waitForLoadAverage(Number(values["load-max"]));

// ---------------------------------------------------------------- releases A and B

rmSync(publish, { recursive: true, force: true });
const relA = JSON.parse(run(["python3", releasePy, "assemble", "--staged", values.staged!, "--publish", publish, "--oracle", values.oracle!, "--activate"]));
const stagedB = join(work, "staged-b");
run(["python3", releasePy, "derive-generation", "--staged", values.staged!, "--out", stagedB]);
const relB = JSON.parse(run(["python3", releasePy, "assemble", "--staged", stagedB, "--publish", publish, "--oracle", values.oracle!]));
if (relA.pack_id === relB.pack_id) throw new Error("derive-generation did not change pack_id");
interface Asset { id: string; role: string; url: string; decoded_bytes: number; decoded_sha256: string }
interface ReleaseDoc { pack_id: string; assets: Asset[] }
const releaseA = JSON.parse(readFileSync(join(publish, relA.release), "utf8")) as ReleaseDoc;
const releaseB = JSON.parse(readFileSync(join(publish, relB.release), "utf8")) as ReleaseDoc;
const refOf = (r: { release: string; sha256: string; pack_id: string }) => ({ release: r.release, sha256: r.sha256, pack_id: r.pack_id });
const optional = new Set(["license-inventory", "notice", "pack-manifest"]);
const requiredUrls = (r: ReleaseDoc) => new Set(r.assets.filter((a) => !optional.has(a.role)).map((a) => `/${a.url}`));
// Every URL a release may request: its manifest and its assets (index.json is allowed separately).
const urlsA = new Set([`/${relA.release}`, ...releaseA.assets.map((a) => `/${a.url}`)]);
const urlsB = new Set([`/${relB.release}`, ...releaseB.assets.map((a) => `/${a.url}`)]);
// A small target rlib (corruption target) and the one asset only B has (truncation target).
const rlibA = releaseA.assets.filter((a) => a.role === "target-rlib").sort((x, y) => x.decoded_bytes - y.decoded_bytes)[0]!;
const onlyB = releaseB.assets.find((a) => a.role === "framework-source" && !urlsA.has(`/${a.url}`))!;
const oracle = Bun.TOML.parse(readFileSync(values.oracle!, "utf8")) as { oracle: { bundle_sha256: string } };

// ---------------------------------------------------------------- test asset host

interface HostingRule { pattern: string; content_type: string; cache_control: string }
const hosting = Bun.TOML.parse(readFileSync(join(repo, "browser/release/hosting.toml"), "utf8")) as unknown as {
  rule: HostingRule[];
  cors: { allow_origin: string; expose_headers: string[] };
  common: { x_content_type_options: string };
};
const globRe = (pattern: string) => new RegExp(`^${pattern.replace(/[.+^${}()|[\]\\]/g, "\\$&").replace(/\*/g, "[^/]*").replace(/\?/g, "[^/]")}$`);
function headersFor(rel: string): Record<string, string> | null {
  const rule = hosting.rule.find((r) => globRe(r.pattern).test(rel));
  if (!rule) return null;
  return {
    "content-type": rule.content_type,
    "cache-control": rule.cache_control,
    "x-content-type-options": hosting.common.x_content_type_options,
    "access-control-allow-origin": hosting.cors.allow_origin,
    "access-control-expose-headers": hosting.cors.expose_headers.join(", "),
  };
}

type Fault = "corrupt" | "short" | "abort";
interface HostLogEntry { atMs: number; path: string; status: number; bytes: number; fault: Fault | null }
// node:http rather than Bun.serve: the "abort" fault must send a Content-Length header and then
// close the connection mid-body (a genuine truncated transfer), which Bun.serve does not allow.
const host = {
  server: null as Server | null,
  faults: new Map<string, Fault>(),
  active: "A" as "A" | "B",
  log: [] as HostLogEntry[],
  started: performance.now(),
  async start() {
    const server = createServer((request, response) => {
      const path = new URL(request.url ?? "/", "http://host").pathname;
      const rel = path.slice(1);
      const record = (status: number, bytes: number, fault: Fault | null) => this.log.push({ atMs: performance.now() - this.started, path, status, bytes, fault });
      const headers = headersFor(rel);
      let body: Uint8Array | null = null;
      if (headers !== null && rel === "index.json") {
        const r = this.active === "A" ? relA : relB;
        body = new TextEncoder().encode(`${JSON.stringify({ schema: 1, kind: "krs-browser-lesson-index", active: refOf(r) }, null, 1)}\n`);
      } else if (headers !== null && existsSync(join(publish, rel))) {
        body = new Uint8Array(readFileSync(join(publish, rel)));
      }
      if (headers === null || body === null) {
        record(404, 0, null);
        response.writeHead(404, { "access-control-allow-origin": "*" }).end("not found");
        return;
      }
      const fault = this.faults.get(path) ?? null;
      record(200, body.byteLength, fault);
      if (fault === "corrupt") {
        body = body.slice();
        body[body.length >> 1]! ^= 0x01;
      } else if (fault === "short") {
        body = body.slice(0, Math.max(0, body.length - Math.max(1, body.length >> 2)));
      } else if (fault === "abort") {
        response.writeHead(200, { ...headers, "content-length": String(body.length) });
        response.write(body.slice(0, body.length >> 1));
        setTimeout(() => response.socket?.destroy(), 50);
        return;
      }
      response.writeHead(200, { ...headers, "content-length": String(body.length) }).end(body);
    });
    await new Promise<void>((resolve) => server.listen(Number(values["asset-port"]), "127.0.0.1", resolve));
    this.server = server;
  },
  stop() {
    this.server?.closeAllConnections();
    this.server?.close();
    this.server = null;
  },
  mark() {
    return this.log.length;
  },
  since(mark: number) {
    return this.log.slice(mark);
  },
};

// ---------------------------------------------------------------- site

await buildSite({
  out: site,
  entrypoints: [join(workerRoot, "src/worker.ts"), join(here, "cache-page.ts")],
  copies: { "index.html": join(here, "index.html") },
});
writeFileSync(join(site, "config.json"), `${JSON.stringify({ base: `http://127.0.0.1:${values["asset-port"]}/` })}\n`);

// ---------------------------------------------------------------- cases

interface CaseResult { name: string; pass: boolean; checks: Record<string, boolean>; observed: Record<string, unknown> }

async function reload(session: SiteSession) {
  const before = (await session.evaluate("return performance.timeOrigin;")) as number;
  await session.evaluate("setTimeout(() => location.reload(), 50); return true;");
  for (let i = 0; i < 600; i += 1) {
    await Bun.sleep(100);
    try {
      const now = (await session.evaluate("return window.krsPageReady === true ? performance.timeOrigin : null;")) as number | null;
      if (now !== null && now !== before) return;
    } catch {
      // navigating
    }
  }
  throw new Error("page did not reload");
}

async function runBrowser(browser: "chromium" | "firefox") {
  const load = await waitForLoad();
  host.log = [];
  host.faults.clear();
  host.active = "A";
  await host.start();
  const session = await openSite({
    browser,
    site,
    port: Number(values.port) + (browser === "firefox" ? 10 : 0),
    profilePrefix: `${work}/`,
    chromiumArgs: ["--enable-precise-memory-info"],
  });
  const results: CaseResult[] = [];
  const ev = async (body: string) => (await session.evaluate(body)) as any;
  const record = (name: string, checks: Record<string, boolean>, observed: Record<string, unknown>) => {
    const pass = Object.values(checks).every(Boolean);
    results.push({ name, pass, checks, observed });
    process.stderr.write(`${browser} ${name}: ${pass ? "PASS" : `FAIL ${JSON.stringify(Object.entries(checks).filter(([, v]) => !v).map(([k]) => k))}`}\n`);
  };
  const notOutside = (log: HostLogEntry[], allowed: Set<string>) => log.every((e) => e.path === "/index.json" || allowed.has(e.path));
  const pathsOf = (log: HostLogEntry[]) => log.map((e) => e.path);
  const count = (log: HostLogEntry[], path: string) => log.filter((e) => e.path === path).length;
  let environment: unknown = null;
  try {
    environment = await ev("return await window.krsCache.config();");

    // C1 cold install and compile (release A)
    let m = host.mark();
    const c1 = await ev("return await window.krsCache.open();");
    const c1log = host.since(m);
    const c1compile = await ev(`return await window.krsCache.compile(${JSON.stringify(relA.pack_id)});`);
    record("cold-install", {
      opened: c1.ok === true && c1.packId === relA.pack_id,
      fetched_every_required_asset_once: [...requiredUrls(releaseA)].every((u) => count(c1log, u) === 1),
      no_optional_asset_fetched: c1log.every((e) => e.path === "/index.json" || e.path === `/${relA.release}` || requiredUrls(releaseA).has(e.path)),
      compile_matches_oracle: c1compile.result.type === "success" && c1compile.result.bundleSha256 === oracle.oracle.bundle_sha256,
      activated: c1.events.some((e: any) => e.type === "activate" && e.packId === relA.pack_id),
    }, { open: { ms: c1.ms, events: c1.events.length }, requests: c1log.length, compile: c1compile });

    // C2 corrupted cache entry (valid length, wrong bytes), origin intact: evict, refetch once, continue
    const corruptA = await ev(`return await window.krsCache.corrupt(${JSON.stringify(relA.pack_id)}, ${JSON.stringify(rlibA.id)});`);
    m = host.mark();
    const c2 = await ev("return await window.krsCache.open();");
    const c2log = host.since(m);
    const c2compile = await ev(`return await window.krsCache.compile(${JSON.stringify(relA.pack_id)});`);
    const c2seq = c2.events.filter((e: any) => e.id === rlibA.id).map((e: any) => e.type);
    record("corrupted-cache-entry-recovers", {
      opened: c2.ok === true,
      event_sequence: JSON.stringify(c2seq) === JSON.stringify(["cache-mismatch", "evict", "fetch", "verified"]),
      mismatch_reason_digest: c2.events.some((e: any) => e.type === "cache-mismatch" && e.id === rlibA.id && e.reason === "digest-mismatch"),
      refetched_once_same_url: count(c2log, `/${rlibA.url}`) === 1,
      nothing_else_fetched: c2log.every((e) => e.path === "/index.json" || e.path === `/${rlibA.url}`),
      compile_matches_oracle: c2compile.result.bundleSha256 === oracle.oracle.bundle_sha256,
    }, { corrupted: corruptA, asset: rlibA.id, events: c2seq, requests: pathsOf(c2log), compile: c2compile.result });

    // C3 corrupted cache entry and corrupted origin: one refetch, then pack-integrity; no fallback
    await ev(`return await window.krsCache.corrupt(${JSON.stringify(relA.pack_id)}, ${JSON.stringify(rlibA.id)});`);
    host.faults.set(`/${rlibA.url}`, "corrupt");
    m = host.mark();
    const c3 = await ev("return await window.krsCache.open();");
    const c3log = host.since(m);
    const c3state = await ev("return await window.krsCache.state();");
    const c3cached = await ev(`return await window.krsCache.hasEntry(${JSON.stringify(relA.pack_id)}, ${JSON.stringify(rlibA.url)});`);
    host.faults.clear();
    const c3seq = c3.events.filter((e: any) => e.id === rlibA.id).map((e: any) => e.type);
    record("corrupted-cache-and-origin-reports-integrity-error", {
      rejected: c3.ok === false,
      error_surface: c3.error?.isPackIntegrityError === true && c3.error?.name === "PackCacheError" && c3.error?.code === "pack-integrity" && c3.error?.reason === "digest-mismatch" && c3.error?.assetId === rlibA.id,
      failure_event: c3.error?.failureEvent?.type === "failure" && c3.error?.failureEvent?.code === "pack-integrity" && c3.error?.failureEvent?.stage === "assets",
      two_reads_one_refetch: c3.error?.attempts === 2 && count(c3log, `/${rlibA.url}`) === 1,
      event_sequence: JSON.stringify(c3seq) === JSON.stringify(["cache-mismatch", "evict", "fetch", "reject"]),
      corrupt_bytes_not_cached: c3cached === false,
      no_fallback_requests: notOutside(c3log, urlsA),
      pointer_unchanged: c3state.pointer?.pack_id === relA.pack_id,
    }, { error: c3.error, events: c3seq, requests: pathsOf(c3log), pointer: c3state.pointer });
    // Restore A (the origin is intact again).
    const c3restore = await ev("return await window.krsCache.open();");

    // C4 truncated response while installing B: rejected before activation
    host.active = "B";
    host.faults.set(`/${onlyB.url}`, "short");
    m = host.mark();
    const c4 = await ev("return await window.krsCache.open();");
    const c4log = host.since(m);
    const c4state = await ev("return await window.krsCache.state();");
    const c4cached = await ev(`return await window.krsCache.hasEntry(${JSON.stringify(relB.pack_id)}, ${JSON.stringify(onlyB.url)});`);
    host.faults.set(`/${onlyB.url}`, "abort");
    m = host.mark();
    const c4b = await ev("return await window.krsCache.open();");
    const c4blog = host.since(m);
    const c4bstate = await ev("return await window.krsCache.state();");
    const c4bcached = await ev(`return await window.krsCache.hasEntry(${JSON.stringify(relB.pack_id)}, ${JSON.stringify(onlyB.url)});`);
    host.faults.clear();
    record("truncated-response-rejected-before-activation", {
      short_rejected: c4.ok === false && c4.error?.code === "pack-integrity" && c4.error?.reason === "length-mismatch" && c4.error?.assetId === onlyB.id,
      short_not_cached: c4cached === false,
      short_pointer_still_a: c4state.pointer?.pack_id === relA.pack_id,
      short_no_fallback: notOutside(c4log, urlsB) && c4.packId === undefined,
      aborted_rejected: c4b.ok === false && c4b.error?.code === "pack-unavailable" && c4b.error?.reason === "network" && c4b.error?.assetId === onlyB.id,
      aborted_not_cached: c4bcached === false,
      aborted_pointer_still_a: c4bstate.pointer?.pack_id === relA.pack_id,
      aborted_no_fallback: notOutside(c4blog, urlsB),
    }, { short: c4.error, aborted: c4b.error, asset: onlyB.id, requests: { short: pathsOf(c4log).length, aborted: pathsOf(c4blog).length } });

    // C5 new generation while a worker holds the old one: cleanup keeps the leased namespace
    const c5holder = await ev(`return await window.krsCache.compile(${JSON.stringify(relA.pack_id)}, { lease: true, keep: true });`);
    const c5open = await ev("return await window.krsCache.open();"); // installs and activates B
    const c5stateBefore = await ev("return await window.krsCache.state();");
    const c5clean1 = await ev("return await window.krsCache.cleanup();");
    const c5stateLeased = await ev("return await window.krsCache.state();");
    const c5again = await ev(`return await window.krsCache.compile(${JSON.stringify(relA.pack_id)});`);
    await ev(`return window.krsCache.dispose(${JSON.stringify(relA.pack_id)});`);
    let c5stateReleased: any = null;
    for (let i = 0; i < 50; i += 1) {
      c5stateReleased = await ev("return await window.krsCache.state();");
      if (!c5stateReleased.heldLeases.some((l: any) => l.name.endsWith(relA.pack_id.slice(7)))) break;
      await Bun.sleep(100);
    }
    const c5clean2 = await ev("return await window.krsCache.cleanup();");
    const c5stateAfter = await ev("return await window.krsCache.state();");
    const nsA = `krs-pack-${relA.pack_id.slice(7)}`;
    const nsB = `krs-pack-${relB.pack_id.slice(7)}`;
    const c5compileB = await ev(`return await window.krsCache.compile(${JSON.stringify(relB.pack_id)});`);
    record("generation-lease-blocks-cleanup", {
      holder_compiled: c5holder.result.type === "success",
      b_activated: c5open.ok === true && c5open.packId === relB.pack_id && c5stateBefore.pointer?.pack_id === relB.pack_id,
      lease_held_by_worker: c5stateLeased.heldLeases.some((l: any) => l.name === `krs-pack-lease:${relA.pack_id.slice(7)}` && l.mode === "shared"),
      leased_namespace_kept: c5clean1.results.some((r: any) => r.namespace === nsA && r.result === "leased") && nsA in c5stateLeased.namespaces,
      old_generation_still_compiles: c5again.result.type === "success",
      deleted_after_lease_ends: c5clean2.results.some((r: any) => r.namespace === nsA && r.result === "deleted") && !(nsA in c5stateAfter.namespaces),
      active_kept: nsB in c5stateAfter.namespaces && c5clean2.results.some((r: any) => r.namespace === nsB && r.result === "active"),
      b_compiles: c5compileB.result.type === "success",
    }, { cleanupWhileLeased: c5clean1.results, cleanupAfter: c5clean2.results, leases: c5stateLeased.heldLeases, compileB: c5compileB.result, namespacesAfter: c5stateAfter.namespaces });

    // C6 evicted namespace (caches.delete between compiles): refetch and continue
    await ev(`return await window.krsCache.deleteNamespace(${JSON.stringify(relB.pack_id)});`);
    m = host.mark();
    const c6 = await ev("return await window.krsCache.open();");
    const c6log = host.since(m);
    const c6compile = await ev(`return await window.krsCache.compile(${JSON.stringify(relB.pack_id)});`);
    record("evicted-namespace-refetches", {
      opened: c6.ok === true && c6.packId === relB.pack_id,
      refetched_every_required_asset: [...requiredUrls(releaseB)].every((u) => count(c6log, u) === 1),
      same_urls_only: notOutside(c6log, urlsB),
      compiles: c6compile.result.type === "success" && c6compile.result.bundleSha256 === c5compileB.result.bundleSha256,
    }, { requests: c6log.length, compile: c6compile.result });

    // C7 offline reload after a complete verified load: compile succeeds from the cache alone
    host.stop();
    await reload(session);
    await ev("return await window.krsCache.config();");
    m = host.mark();
    const c7 = await ev("return await window.krsCache.open();");
    const c7compile = c7.ok ? await ev(`return await window.krsCache.compile(${JSON.stringify(relB.pack_id)});`) : null;
    const c7log = host.since(m);
    // C7b offline with the namespace gone: reported cleanly
    await ev(`return await window.krsCache.deleteNamespace(${JSON.stringify(relB.pack_id)});`);
    const c7b = await ev("return await window.krsCache.open();");
    record("offline-reload", {
      opened_offline: c7.ok === true && c7.packId === relB.pack_id && c7.events.some((e: any) => e.type === "index" && e.source === "offline-pointer"),
      all_from_cache: c7.ok === true && c7.events.filter((e: any) => e.type === "verified").every((e: any) => e.from === "cache"),
      compiles: c7compile?.result?.type === "success" && c7compile?.result?.bundleSha256 === c5compileB.result.bundleSha256,
      no_host_requests: c7log.length === 0,
      incomplete_offline_reported: c7b.ok === false && c7b.error?.code === "pack-unavailable" && c7b.error?.reason === "offline-incomplete",
    }, { open: c7.ok ? { ms: c7.ms, events: c7.events.length } : c7.error, compile: c7compile?.result, offlineIncomplete: c7b.error });
    await host.start();
    const final = await ev("return await window.krsCache.state();");
    void c3restore;
    await session.close();
    const record_ = {
      browser,
      details: session.details,
      environment,
      load_at_start: load,
      releases: { A: refOf(relA), B: refOf(relB) },
      targets: { corrupted: rlibA.id, truncated: onlyB.id },
      pass: results.every((r) => r.pass),
      cases: results,
      final_storage: final.storage,
    };
    writeFileSync(join(out, `cache-tests-${browser}.json`), `${JSON.stringify(record_, null, 1)}\n`);
    return record_;
  } catch (error) {
    await session.close().catch(() => {});
    writeFileSync(join(out, `cache-tests-${browser}.json`), `${JSON.stringify({ browser, pass: false, error: String((error as Error)?.stack ?? error), cases: results }, null, 1)}\n`);
    throw error;
  } finally {
    host.stop();
  }
}

const verdicts: Record<string, boolean> = {};
for (const browser of values.browsers!.split(",") as Array<"chromium" | "firefox">) {
  try {
    verdicts[browser] = (await runBrowser(browser)).pass;
  } catch (error) {
    process.stderr.write(`${browser}: ${String((error as Error)?.stack ?? error)}\n`);
    verdicts[browser] = false;
  }
}
const pass = Object.values(verdicts).every(Boolean);
writeFileSync(join(out, "cache-tests.json"), `${JSON.stringify({ pass, verdicts, releases: { A: refOf(relA), B: refOf(relB) } }, null, 1)}\n`);
process.stderr.write(`cache tests: ${pass ? "PASS" : "FAIL"} ${JSON.stringify(verdicts)}\n`);
process.exit(pass ? 0 : 1);
