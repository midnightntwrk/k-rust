// IR-20 docs-site lesson check: drives the built docs site's /lessons/tour-minimal
// page in headless Chromium and headless Firefox over WebDriver BiDi, through
// the page's own controls, and records bundles, diagnostics, cancel latency,
// cache behaviour, network requests, memory, and screenshots.
//
//   bun test/lesson/docs-lesson.ts --site DOCS_SITE_DIR --assets RELEASE_ROOT --out DIR \
//     [--oracle BUNDLE] [--oracle-e1 BUNDLE] [--browsers chromium,firefox] [--port N] [--expect configured|unconfigured]
//     [--pack-origin same|cross]
//
// DOCS_SITE_DIR is docs-site/ after `vocs build` (dist/serve-node.js runs the
// site). A Bun front server on --port proxies the site and serves RELEASE_ROOT
// (a browser/release/release.py publication: index.json, releases/, blobs/) at /krs-pack/, so the build must use
// VITE_KRS_BROWSER_PACK_BASE=/krs-pack/ (same origin). Every request that
// reaches the front server is logged, and BiDi network.beforeRequestSent
// events are recorded per browser. Fresh /var/tmp profiles; no visible window.
//
// --pack-origin cross checks the documented local deployment instead (docs-site/README.md): the pack is
// a second origin, http://127.0.0.1:<port + 70>/, so the build must use
// VITE_KRS_BROWSER_PACK_BASE=http://127.0.0.1:<port + 70>/. That origin is a logging pass-through to
// release.py serve that forwards the method and returns its status, headers (CORS included), and bytes
// unchanged; its requests are logged under /krs-pack/ so that every check applies unchanged.

import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { createHash, randomBytes } from "node:crypto";
import { join, resolve } from "node:path";
import { parseArgs } from "node:util";
import { TreeSampler } from "../browser/common.ts";

const { values } = parseArgs({
  args: Bun.argv.slice(2),
  options: {
    site: { type: "string" },
    assets: { type: "string", default: "/var/tmp/krs-ir21-run/publish" },
    out: { type: "string" },
    oracle: { type: "string", default: "/var/tmp/krs-ir17-oracle-final/native/descriptor-bundle.json" },
    "oracle-e1": { type: "string", default: "/var/tmp/krs-ir17-oracle-final/native-e1/descriptor-bundle.json" },
    browsers: { type: "string", default: "chromium,firefox" },
    port: { type: "string", default: "5310" },
    firefox: { type: "string", default: "/usr/lib/firefox/firefox" },
    expect: { type: "string", default: "configured" },
    "pack-origin": { type: "string", default: "same" },
  },
});
const SITE = resolve(values.site!);
const ASSETS = realpathSync(values.assets!);
const OUT = resolve(values.out!);
const PORT = Number(values.port);
const CROSS_ORIGIN = values["pack-origin"] === "cross";
if (!["same", "cross"].includes(values["pack-origin"]!)) throw new Error("--pack-origin is same or cross");
mkdirSync(OUT, { recursive: true });
const sha256 = (bytes: Uint8Array) => createHash("sha256").update(bytes).digest("hex");
const log = (text: string) => process.stderr.write(`${new Date().toISOString().slice(11, 19)} ${text}\n`);

async function waitForLoad(maximum: number) {
  for (;;) {
    const load = Number(readFileSync("/proc/loadavg", "utf8").split(" ")[0]);
    if (load <= maximum) return load;
    log(`1-minute load ${load} > ${maximum}; waiting`);
    await Bun.sleep(15_000);
  }
}

// ---------------------------------------------------------------- servers

interface ServerLogEntry {
  atMs: number;
  method: string;
  url: string;
  status: number;
  bytes: number;
  requestBodyBytes: number;
}

function startServers(browser: string) {
  const sitePort = PORT + 50;
  const site = Bun.spawn(["node", "dist/serve-node.js"], {
    cwd: SITE,
    env: { ...process.env, PORT: String(sitePort), HOST: "127.0.0.1" },
    stdout: "ignore",
    stderr: Bun.file(join(OUT, `${browser}-site-server.log`)),
  });
  const releasePort = PORT + 60;
  const releaseHost = Bun.spawn(["python3", join(import.meta.dir, "../../../release/release.py"), "serve", ASSETS, "--port", String(releasePort)], {
    env: { ...process.env, PYTHONDONTWRITEBYTECODE: "1" },
    stdout: "ignore",
    stderr: "ignore",
  });
  const entries: ServerLogEntry[] = [];
  const started = performance.now();
  const server = Bun.serve({
    hostname: "127.0.0.1",
    port: PORT,
    async fetch(request) {
      const url = new URL(request.url);
      const body = request.body ? new Uint8Array(await request.arrayBuffer()) : new Uint8Array();
      const entry: ServerLogEntry = { atMs: performance.now() - started, method: request.method, url: url.pathname + url.search, status: 404, bytes: 0, requestBodyBytes: body.byteLength };
      entries.push(entry);
      if (url.pathname.startsWith("/krs-pack/")) {
        // The release host: browser/release/release.py serve, which applies hosting.toml headers.
        const upstream = await fetch(`http://127.0.0.1:${releasePort}${url.pathname.slice("/krs-pack".length)}`);
        const bytes = new Uint8Array(await upstream.arrayBuffer());
        entry.status = upstream.status;
        entry.bytes = bytes.byteLength;
        return new Response(bytes, { status: upstream.status, headers: upstream.headers });
      }
      const upstream = await fetch(`http://127.0.0.1:${sitePort}${url.pathname}${url.search}`, {
        method: request.method,
        headers: request.headers,
        body: body.byteLength > 0 ? body : undefined,
        redirect: "manual",
      });
      const bytes = new Uint8Array(await upstream.arrayBuffer());
      entry.status = upstream.status;
      entry.bytes = bytes.byteLength;
      const headers = new Headers(upstream.headers);
      headers.delete("content-encoding");
      headers.delete("content-length");
      return new Response(bytes, { status: upstream.status, headers });
    },
  });
  const packPort = PORT + 70;
  const packServer = CROSS_ORIGIN
    ? Bun.serve({
        hostname: "127.0.0.1",
        port: packPort,
        async fetch(request) {
          const url = new URL(request.url);
          const entry: ServerLogEntry = { atMs: performance.now() - started, method: request.method, url: `/krs-pack${url.pathname}${url.search}`, status: 404, bytes: 0, requestBodyBytes: 0 };
          entries.push(entry);
          const upstream = await fetch(`http://127.0.0.1:${releasePort}${url.pathname}${url.search}`, { method: request.method, headers: request.headers });
          const bytes = new Uint8Array(await upstream.arrayBuffer());
          entry.status = upstream.status;
          entry.bytes = bytes.byteLength;
          return new Response(bytes, { status: upstream.status, headers: upstream.headers });
        },
      })
    : null;
  return {
    entries,
    origin: `http://127.0.0.1:${PORT}`,
    packOrigin: CROSS_ORIGIN ? `http://127.0.0.1:${packPort}` : null,
    async ready() {
      for (let i = 0; i < 200; i += 1) {
        try {
          const response = await fetch(`http://127.0.0.1:${sitePort}/`);
          if (response.status < 500) return;
        } catch {}
        await Bun.sleep(100);
      }
      throw new Error("docs site server did not start");
    },
    async releaseReady() {
      for (let i = 0; i < 200; i += 1) {
        try {
          if ((await fetch(`http://127.0.0.1:${releasePort}/index.json`)).ok) return;
        } catch {}
        await Bun.sleep(100);
      }
      throw new Error("release host did not start");
    },
    async stop() {
      server.stop(true);
      packServer?.stop(true);
      site.kill();
      releaseHost.kill();
      await site.exited;
      await releaseHost.exited;
    },
  };
}

// ---------------------------------------------------------------- BiDi

interface NetworkEvent {
  atMs: number;
  url: string;
  method: string;
  bodySize: number | null;
  headers: Array<{ name: string; value: string }>;
  destination: string | null;
  initiatorType: string | null;
}

class Bidi {
  private pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();
  private nextId = 0;
  network: NetworkEvent[] = [];
  private started = performance.now();
  constructor(private socket: WebSocket) {
    socket.onmessage = (event) => {
      const message = JSON.parse(String(event.data));
      if (message.type === "event") {
        if (message.method === "network.beforeRequestSent") {
          const r = message.params.request;
          this.network.push({
            atMs: performance.now() - this.started,
            url: r.url,
            method: r.method,
            bodySize: r.bodySize ?? null,
            headers: (r.headers ?? []).map((h: any) => ({ name: h.name, value: h.value?.value ?? "" })),
            destination: r.destination ?? null,
            initiatorType: r.initiatorType ?? message.params.initiator?.type ?? null,
          });
        }
        return;
      }
      const waiter = this.pending.get(message.id);
      if (!waiter) return;
      this.pending.delete(message.id);
      if (message.type === "success") waiter.resolve(message.result);
      else waiter.reject(new Error(JSON.stringify(message).slice(0, 2000)));
    };
  }
  static async connect(url: string): Promise<Bidi> {
    for (let i = 0; ; i += 1) {
      try {
        const socket = await new Promise<WebSocket>((ok, fail) => {
          const ws = new WebSocket(url);
          ws.onopen = () => ok(ws);
          ws.onerror = () => fail(new Error("connect"));
        });
        return new Bidi(socket);
      } catch {
        if (i > 300) throw new Error(`BiDi endpoint ${url} did not open`);
        await Bun.sleep(100);
      }
    }
  }
  command(method: string, params: Record<string, unknown> = {}): Promise<any> {
    return new Promise((ok, fail) => {
      const id = ++this.nextId;
      this.pending.set(id, { resolve: ok, reject: fail });
      this.socket.send(JSON.stringify({ id, method, params }));
    });
  }
  close() {
    this.socket.close();
  }
}

interface Session {
  browser: "chromium" | "firefox";
  bidi: Bidi;
  context: string;
  sampler: TreeSampler;
  version: string;
  close(): Promise<void>;
}

async function launch(browser: "chromium" | "firefox"): Promise<Session> {
  const profile = mkdtempSync(`/var/tmp/krs-ir20-${browser}-profile.`);
  const control = PORT + 1;
  let proc: ReturnType<typeof Bun.spawn>;
  let bidi: Bidi;
  let version = "";
  let deleteSession: () => Promise<void> = async () => {};
  if (browser === "chromium") {
    proc = Bun.spawn(["chromedriver", `--port=${control}`], { stdout: "ignore", stderr: "ignore" });
    const base = `http://127.0.0.1:${control}`;
    for (let i = 0; ; i += 1) {
      try {
        if ((await fetch(`${base}/status`)).ok) break;
      } catch {}
      if (i > 100) throw new Error("chromedriver did not start");
      await Bun.sleep(100);
    }
    const response = await fetch(`${base}/session`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        capabilities: {
          alwaysMatch: {
            browserName: "chrome",
            webSocketUrl: true,
            "goog:chromeOptions": { args: ["--headless=new", "--disable-dev-shm-usage", "--no-first-run", `--user-data-dir=${profile}`, "--window-size=1280,1400"] },
          },
        },
      }),
    });
    const payload = (await response.json()) as any;
    if (!response.ok) throw new Error(JSON.stringify(payload).slice(0, 2000));
    version = payload.value.capabilities.browserVersion;
    const sessionId = payload.value.sessionId;
    bidi = await Bidi.connect(payload.value.capabilities.webSocketUrl);
    deleteSession = async () => {
      await fetch(`${base}/session/${sessionId}`, { method: "DELETE" }).catch(() => {});
    };
  } else {
    proc = Bun.spawn(
      [values.firefox!, "--headless", "--new-instance", "--profile", profile, "--remote-debugging-port", String(control), "--remote-allow-hosts", "127.0.0.1,localhost", "about:blank"],
      { stdout: "ignore", stderr: "ignore", env: { ...process.env, MOZ_HEADLESS: "1", DISPLAY: "", WAYLAND_DISPLAY: "" } },
    );
    bidi = await Bidi.connect(`ws://127.0.0.1:${control}/session`);
    const session = await bidi.command("session.new", { capabilities: { alwaysMatch: { acceptInsecureCerts: false } } });
    version = session.capabilities.browserVersion;
    deleteSession = async () => {
      await bidi.command("session.end").catch(() => {});
    };
  }
  const sampler = new TreeSampler(() => proc.pid);
  sampler.start();
  await bidi.command("session.subscribe", { events: ["network.beforeRequestSent"] });
  const tree = await bidi.command("browsingContext.getTree", {});
  const context = tree.contexts[0].context as string;
  await bidi.command("browsingContext.setViewport", { context, viewport: { width: 1280, height: 1400 } });
  return {
    browser,
    bidi,
    context,
    sampler,
    version,
    async close() {
      await deleteSession();
      bidi.close();
      await Bun.sleep(300);
      sampler.stop();
      proc.kill();
      await proc.exited;
      rmSync(profile, { recursive: true, force: true });
    },
  };
}

// Helpers injected into every evaluation.
const PRELUDE = `
const $ = (s) => document.querySelector(s);
const $$ = (s) => [...document.querySelectorAll(s)];
const root = () => $('[data-lesson-phase]');
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const waitFor = async (predicate, timeoutMs, what) => {
  const t0 = performance.now();
  for (;;) {
    const value = predicate();
    if (value) return value;
    if (performance.now() - t0 > timeoutMs) throw new Error('timeout waiting for ' + what + ' (phase ' + root()?.dataset.lessonPhase + ', build ' + root()?.dataset.buildStatus + ')');
    await sleep(20);
  }
};
const setSource = (text) => {
  const ta = $('[data-lesson-editor]');
  Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, 'value').set.call(ta, text);
  ta.dispatchEvent(new Event('input', { bubbles: true }));
};
const source = () => $('[data-lesson-editor]').value;
const click = (action) => { const b = $('[data-action="' + action + '"]'); if (!b || b.disabled) throw new Error('button ' + action + ' is not enabled'); b.click(); };
const compileAndWait = async (timeoutMs = 300000) => {
  const before = Number(root().dataset.buildGeneration);
  const t0 = performance.now();
  await waitFor(() => !$('[data-action="compile"]').disabled, 10000, 'compile enabled');
  click('compile');
  await waitFor(() => Number(root().dataset.buildGeneration) > before && ['success', 'failure', 'cancelled'].includes(root().dataset.buildStatus), timeoutMs, 'build end');
  return { wallMs: performance.now() - t0, status: root().dataset.buildStatus };
};
const stageStates = () => Object.fromEntries($$('[data-stage]').map((e) => [e.dataset.stage, e.dataset.state]));
const bundleBytes = async () => {
  const sha = $('code[data-bundle-sha256]')?.dataset.bundleSha256;
  const a = await waitFor(() => $('a[download][data-bundle-sha256="' + sha + '"]'), 10000, 'bundle download link');
  const bytes = new Uint8Array(await (await fetch(a.href)).arrayBuffer());
  const digest = [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))].map((b) => b.toString(16).padStart(2, '0')).join('');
  let binary = '';
  for (let i = 0; i < bytes.length; i += 0x8000) binary += String.fromCharCode(...bytes.subarray(i, i + 0x8000));
  return { bytes: bytes.length, sha256: digest, base64: btoa(binary) };
};
const diagnostics = () => $$('[data-diagnostic-index]').map((li) => ({
  class: li.dataset.class,
  text: li.innerText,
  location: li.querySelector('[data-action="select-range"]')?.innerText ?? null,
}));
const marks = () => $$('mark[data-diagnostic]').map((m) => ({ diagnostic: Number(m.dataset.diagnostic), text: m.textContent, className: m.className }));
`;

async function evaluate(session: Session, body: string): Promise<any> {
  const expression = `(async () => { ${PRELUDE}\n${body} })().then((v) => JSON.stringify({ ok: v }), (e) => JSON.stringify({ error: String(e && e.stack || e) }))`;
  const result = await session.bidi.command("script.evaluate", { expression, target: { context: session.context }, awaitPromise: true, resultOwnership: "none" });
  if (result.type !== "success") throw new Error(`script exception: ${JSON.stringify(result).slice(0, 2000)}`);
  const parsed = JSON.parse(result.result.value as string) as { ok?: unknown; error?: string };
  if (parsed.error) throw new Error(parsed.error);
  return parsed.ok;
}

async function navigate(session: Session, url: string) {
  await session.bidi.command("browsingContext.navigate", { context: session.context, url, wait: "complete" });
}

async function screenshot(session: Session, name: string) {
  const result = await session.bidi.command("browsingContext.captureScreenshot", { context: session.context, origin: "viewport" });
  const file = join(OUT, "screenshots", `${session.browser}-${name}.png`);
  mkdirSync(join(OUT, "screenshots"), { recursive: true });
  writeFileSync(file, Buffer.from(result.data, "base64"));
  return file;
}

async function scrollTo(session: Session, selector: string) {
  await evaluate(session, `const e = $(${JSON.stringify(selector)}); if (e) e.scrollIntoView({ block: 'start' }); window.scrollBy(0, -80); await sleep(150); return true;`);
}

// ---------------------------------------------------------------- plan

interface Check {
  name: string;
  pass: boolean;
  detail: string;
}

// ASSETS is a release root (browser/release/release.py assemble): index.json -> releases/<sha>.json -> blobs/.
const releaseIndex = JSON.parse(readFileSync(join(ASSETS, "index.json"), "utf8"));
const release = JSON.parse(readFileSync(join(ASSETS, releaseIndex.active.release), "utf8"));
const OPTIONAL_ROLES = new Set(["license-inventory", "notice", "pack-manifest"]);
const requiredAssets: Array<{ id: string; url: string }> = release.assets.filter((a: any) => !OPTIONAL_ROLES.has(a.role));
const TOTAL_ASSETS = requiredAssets.length;
const MANIFEST_URLS = ["/krs-pack/index.json", `/krs-pack/${releaseIndex.active.release}`];
const CORRUPT_TARGET = requiredAssets.find((a) => a.id.startsWith("pack/deps/") && a.id.endsWith(".rlib"))!;
const NAMESPACE = `krs-pack-${String(releaseIndex.active.pack_id).replace(/^sha256:/, "")}`;
const seedSource = readFileSync(join(SITE, "src/snippets/tour-minimal.rs"), "utf8");
const oracle = new Uint8Array(readFileSync(values.oracle!));
const oracleE1 = new Uint8Array(readFileSync(values["oracle-e1"]!));
const e1Source = seedSource.replace("foo_to_bar: Foo() => Bar();", "foo_to_baz: Foo() => Bar();");
const x1Source = seedSource.replace("k: k::k![Object::Foo()],", "k: k::k![Object::Missing()],");
// Directly above the item, after the KRS attributes (policy v2 rejects a derive before a KRS attribute separately).
const policySource = seedSource.replace("pub enum Object {", "#[derive(serde::Serialize)]\npub enum Object {");
// Before policy v2 (IR-28) this reached rustc as E0428 in the generated registration table (generated-only);
// policy v2 rejects the reserved name at its authored range.
const reservedNameSource = `${seedSource}\npub static __KRS_REGISTRATIONS: u8 = 0;\n`;
const canary = `krs-canary-${randomBytes(16).toString("hex")}`;
const canarySource = `${seedSource}\n// ${canary}\n`;
for (const [name, text] of [["e1", e1Source], ["x1", x1Source], ["policy", policySource]] as const) {
  if (text === seedSource) throw new Error(`edit ${name} did not apply`);
}

async function runBrowser(browser: "chromium" | "firefox") {
  const servers = startServers(browser);
  await servers.ready();
  await servers.releaseReady();
  const checks: Check[] = [];
  const steps: Record<string, unknown> = {};
  const check = (name: string, pass: boolean, detail: unknown) => {
    checks.push({ name, pass, detail: typeof detail === "string" ? detail : JSON.stringify(detail) });
    log(`${browser} ${pass ? "PASS" : "FAIL"} ${name}`);
  };
  let session: Session | null = null;
  const pageUrl = `${servers.origin}/lessons/tour-minimal`;
  try {
    session = await launch(browser);
    const s = session;
    const step = async <T>(name: string, fn: () => Promise<T>): Promise<T | null> => {
      s.sampler.phase = name;
      const t0 = performance.now();
      try {
        const result = await fn();
        steps[name] = { ms: Math.round(performance.now() - t0), result };
        return result;
      } catch (error) {
        steps[name] = { ms: Math.round(performance.now() - t0), error: String(error instanceof Error ? error.stack ?? error.message : error) };
        check(`${name} ran`, false, String(error));
        return null;
      }
    };

    await step("open", async () => {
      await navigate(s, pageUrl);
      return evaluate(s, `await waitFor(() => ['idle', 'unconfigured', 'unavailable', 'unsupported'].includes(root()?.dataset.lessonPhase), 60000, 'hydration'); return { phase: root().dataset.lessonPhase, panel: $('[data-panel]').innerText };`);
    });
    const phase = (steps.open as any)?.result?.phase;
    if (values.expect === "unconfigured") {
      check("unconfigured build renders the unavailable state", phase === "unconfigured", phase);
      await screenshot(s, "unconfigured");
      const packRequests = servers.entries.filter((e) => e.url.startsWith("/krs-pack/"));
      check("an unconfigured page requests nothing from a pack base", packRequests.length === 0, packRequests);
      return { checks, steps, network: s.bidi.network, server: servers.entries, version: s.version, memory: s.sampler.summary() };
    }
    check("page hydrates to the download prompt", phase === "idle", phase);
    const beforeDownload = servers.entries.filter((e) => e.url.startsWith("/krs-pack/")).map((e) => e.url);
    check("only index.json and the release manifest load before the download button", JSON.stringify([...beforeDownload].sort()) === JSON.stringify([...MANIFEST_URLS].sort()), beforeDownload);
    await screenshot(s, "01-download-prompt");

    const cold = await step("download-cold", () =>
      evaluate(s, `click('download'); await waitFor(() => ['ready', 'load-failed'].includes(root().dataset.lessonPhase), 600000, 'ready'); const p = $('[data-panel]'); return { phase: root().dataset.lessonPhase, readyMs: Number(p.dataset.readyMs), fromNetwork: Number(p.dataset.fromNetwork), fromCache: Number(p.dataset.fromCache), release: p.dataset.release, text: p.innerText };`),
    );
    check("cold download verifies every asset into the cache", cold?.phase === "ready" && cold.release === releaseIndex.active.release && cold.fromNetwork === TOTAL_ASSETS, cold);

    const s0 = await step("S0-seed-cold", async () => {
      const r = await evaluate(s, `const r = await compileAndWait(); return { ...r, stages: stageStates(), sha: $('[data-bundle-sha256]')?.dataset.bundleSha256 ?? null, bundle: await bundleBytes() };`);
      return r;
    });
    const s0Bytes = s0?.bundle ? new Uint8Array(Buffer.from(s0.bundle.base64, "base64")) : new Uint8Array();
    check("S0 bundle equals the native oracle (cmp)", s0?.status === "success" && Buffer.compare(Buffer.from(s0Bytes), Buffer.from(oracle)) === 0 && s0.sha === sha256(oracle), { status: s0?.status, sha: s0?.sha, bytes: s0Bytes.byteLength });
    await evaluate(s, `$$('details').forEach((d) => { if (d.closest('[data-outcome="success"]')) d.open = true; }); return true;`);
    await scrollTo(s, "[data-lesson-editor]");
    await screenshot(s, "02-compiled-bundle");

    const s1 = await step("S1-seed-warm", () => evaluate(s, `const r = await compileAndWait(); return { ...r, sha: $('[data-bundle-sha256]')?.dataset.bundleSha256 ?? null };`));
    check("S1 warm bundle equals the oracle", s1?.sha === sha256(oracle), s1);

    const s2 = await step("S2-e1-edit", () => evaluate(s, `setSource(${JSON.stringify(e1Source)}); await sleep(50); const r = await compileAndWait(); return { ...r, sha: $('[data-bundle-sha256]')?.dataset.bundleSha256 ?? null, bundle: await bundleBytes() };`));
    const s2Bytes = s2?.bundle ? Buffer.from(s2.bundle.base64, "base64") : Buffer.alloc(0);
    check("S2 edit (foo_to_bar -> foo_to_baz) equals the E1 oracle (cmp)", Buffer.compare(s2Bytes, Buffer.from(oracleE1)) === 0, { sha: s2?.sha, wallMs: s2?.wallMs });

    const x1 = await step("X1-rustc-diagnostic", async () => {
      const r = await evaluate(s, `setSource(${JSON.stringify(x1Source)}); await sleep(50); const r = await compileAndWait();
        const summary = $('[data-failure-summary]')?.innerText ?? null;
        const outcome = $('[data-outcome]')?.dataset.outcome ?? null;
        const d = diagnostics(); const m = marks();
        click('select-range'); await sleep(50);
        const ta = $('[data-lesson-editor]');
        return { ...r, summary, outcome, diagnostics: d, marks: m, selection: [ta.selectionStart, ta.selectionEnd], stages: stageStates() };`);
      return r;
    });
    const missingAt = x1Source.indexOf("Object::Missing") + "Object::".length;
    check(
      "X1 edit shows rustc errors mapped to the authored `Missing`",
      x1?.status === "failure" && x1.outcome === "failure" && x1.summary === "rustc: 2 errors" &&
        x1.diagnostics.length === 2 && x1.diagnostics.every((d: any) => d.class === "exact-authored") &&
        x1.marks.length >= 1 && x1.marks.every((m: any) => m.text === "Missing") &&
        x1.selection[0] === missingAt && x1.selection[1] === missingAt + "Missing".length,
      { summary: x1?.summary, diagnostics: x1?.diagnostics, marks: x1?.marks, selection: x1?.selection, expected: [missingAt, missingAt + 7] },
    );
    await scrollTo(s, "[data-lesson-editor]");
    await screenshot(s, "03-rustc-level2-diagnostics");
    await evaluate(s, `$$('[data-outcome] details').forEach((d) => (d.open = true)); return true;`);
    await scrollTo(s, "[data-outcome]");
    await screenshot(s, "04-rustc-level3-raw");
    await evaluate(s, `$$('[data-outcome] details').forEach((d) => (d.open = false)); return true;`);
    await scrollTo(s, "[data-outcome]");
    await screenshot(s, "05-rustc-level1-summary");

    const policy = await step("policy-diagnostic", () =>
      evaluate(s, `setSource(${JSON.stringify(policySource)}); await sleep(50); const r = await compileAndWait(); return { ...r, summary: $('[data-failure-summary]')?.innerText ?? null, diagnostics: diagnostics(), marks: marks() };`),
    );
    check(
      "policy error (external derive) is reported before rustc with an authored highlight",
      policy?.status === "failure" && policy.summary === "Lesson policy: 1 error" && policy.diagnostics[0]?.class === "exact-authored" && policy.marks.length === 1 && policy.marks[0].text === "serde::Serialize",
      policy,
    );

    const reserved = await step("reserved-name-policy", () =>
      evaluate(s, `setSource(${JSON.stringify(reservedNameSource)}); await sleep(50); const r = await compileAndWait(); return { ...r, summary: $('[data-failure-summary]')?.innerText ?? null, diagnostics: diagnostics(), marks: marks() };`),
    );
    check(
      "an authored reserved name is a policy error at its authored range (no generated-only diagnostic)",
      reserved?.status === "failure" && reserved.summary === "Lesson policy: 1 error" && reserved.diagnostics.length === 1 && reserved.diagnostics[0].class === "exact-authored" &&
        reserved.marks.length === 1 && reserved.marks[0].text === "__KRS_REGISTRATIONS",
      reserved,
    );
    await evaluate(s, `$$('[data-outcome] details').forEach((d, i) => (d.open = i === 0)); return true;`);
    await scrollTo(s, "[data-outcome]");
    await screenshot(s, "06-reserved-name-policy");

    const cancel = await step("cancel-during-rustc", () =>
      evaluate(s, `click('reset'); await sleep(50);
        const before = Number(root().dataset.buildGeneration);
        click('compile');
        await waitFor(() => $('[data-stage="rustc-lesson"]')?.dataset.state === 'running', 60000, 'rustc-lesson running');
        await sleep(100);
        const t0 = performance.now();
        click('cancel');
        await waitFor(() => root().dataset.buildStatus === 'cancelled', 10000, 'cancelled');
        const observedMs = performance.now() - t0;
        const latency = Number($('[data-outcome="cancelled"]').dataset.cancelLatencyMs);
        const stages = stageStates();
        return { observedMs, latency, stages, sourceIsSeed: source() === ${JSON.stringify(seedSource)} };`),
    );
    check("cancel during rustc stops the build", cancel?.stages?.["rustc-lesson"] === "running" && cancel.sourceIsSeed === true && typeof cancel.latency === "number", cancel);
    await screenshot(s, "07-cancelled");
    const recovery = await step("after-cancel", () => evaluate(s, `const r = await compileAndWait(); return { ...r, sha: $('[data-bundle-sha256]')?.dataset.bundleSha256 ?? null };`));
    check("the compile after cancel equals the oracle", recovery?.sha === sha256(oracle), recovery);

    const serverBeforeCanary = servers.entries.length;
    const networkBeforeCanary = s.bidi.network.length;
    const canaryRun = await step("canary", () => evaluate(s, `setSource(${JSON.stringify(canarySource)}); await sleep(50); const r = await compileAndWait(); return { ...r, resources: performance.getEntriesByType('resource').map((e) => e.name) };`));
    check("canary compile succeeds", canaryRun?.status === "success", canaryRun?.status);
    const buildRequests = servers.entries.slice(serverBeforeCanary);
    const buildNetwork = s.bidi.network.slice(networkBeforeCanary).filter((e) => !e.url.startsWith("blob:"));
    check("a compile makes no network request (server log and BiDi)", buildRequests.length === 0 && buildNetwork.length === 0, { server: buildRequests, bidi: buildNetwork });

    const reload = await step("reload-from-cache", async () => {
      const before = servers.entries.length;
      await navigate(s, pageUrl);
      const r = await evaluate(s, `await waitFor(() => root()?.dataset.lessonPhase === 'idle', 60000, 'idle'); const prompt = $('[data-action="download"]').innerText; click('download'); await waitFor(() => ['ready', 'load-failed'].includes(root().dataset.lessonPhase), 600000, 'ready'); const p = $('[data-panel]'); const c = await compileAndWait(); return { prompt, phase: root().dataset.lessonPhase, readyMs: Number(p.dataset.readyMs), fromNetwork: Number(p.dataset.fromNetwork), fromCache: Number(p.dataset.fromCache), compile: c, sha: $('[data-bundle-sha256]')?.dataset.bundleSha256 ?? null };`);
      return { ...r, packRequests: servers.entries.slice(before).filter((e) => e.url.startsWith("/krs-pack/")).map((e) => e.url) };
    });
    check(
      "reload loads the compiler from Cache Storage (only the manifests are fetched) and compiles the oracle",
      reload?.phase === "ready" && reload.fromNetwork === 0 && reload.fromCache === TOTAL_ASSETS && reload.packRequests.every((u: string) => u === "/krs-pack/index.json") && reload.sha === sha256(oracle) && reload.prompt === "Load the compiler",
      reload,
    );

    const corrupt = await step("corrupted-cache-entry", async () => {
      const r1 = await evaluate(s, `const names = (await caches.keys()).filter((n) => n === ${JSON.stringify(NAMESPACE)}); const cache = await caches.open(names[0]);
        const key = (await cache.keys()).map((r) => r.url).find((u) => u.endsWith(${JSON.stringify("/" + CORRUPT_TARGET.url)}));
        const bytes = new Uint8Array(await (await cache.match(key)).arrayBuffer()); bytes[bytes.length >> 1] ^= 0xff;
        await cache.put(key, new Response(bytes));
        return { cache: names[0], key };`);
      // A worker started now reads the corrupted entry: the next compile must fail as an environment failure.
      const r2 = await evaluate(s, `const before = Number(root().dataset.buildGeneration); click('compile');
        await waitFor(() => Number(root().dataset.buildGeneration) > before && root().dataset.buildStatus === 'running', 60000, 'running');
        await waitFor(() => $('[data-stage="rustc-lesson"]')?.dataset.state === 'running', 60000, 'rustc-lesson running'); click('cancel');
        await waitFor(() => root().dataset.buildStatus === 'cancelled', 10000, 'cancelled');
        const r = await compileAndWait(60000);
        return { ...r, outcome: $('[data-outcome]')?.dataset.outcome ?? null, summary: $('[data-outcome] p')?.innerText ?? null };`);
      await scrollTo(s, "[data-outcome]");
      await screenshot(s, "08-environment-failure");
      const before = servers.entries.length;
      await navigate(s, pageUrl);
      const r3 = await evaluate(s, `await waitFor(() => root()?.dataset.lessonPhase === 'idle', 60000, 'idle'); click('download'); await waitFor(() => ['ready', 'load-failed'].includes(root().dataset.lessonPhase), 600000, 'ready'); const p = $('[data-panel]'); const c = await compileAndWait(); return { phase: root().dataset.lessonPhase, fromNetwork: Number(p.dataset.fromNetwork), replaced: p.dataset.replaced, compile: c, sha: $('[data-bundle-sha256]')?.dataset.bundleSha256 ?? null };`);
      return { corrupted: r1, workerSide: r2, pageSide: { ...r3, packRequests: servers.entries.slice(before).filter((e) => e.url.startsWith("/krs-pack/")).map((e) => e.url) } };
    });
    check(
      "a corrupted cached asset fails worker start-up as an environment failure",
      corrupt?.workerSide?.status === "failure" && corrupt.workerSide.outcome === "environment-failure",
      corrupt?.workerSide,
    );
    check(
      "on reload the page replaces exactly the corrupted entry from the network",
      corrupt?.pageSide?.phase === "ready" && corrupt.pageSide.fromNetwork === 1 && corrupt.pageSide.replaced === CORRUPT_TARGET.id && corrupt.pageSide.sha === sha256(oracle) &&
        JSON.stringify(corrupt.pageSide.packRequests.filter((u: string) => u !== "/krs-pack/index.json")) === JSON.stringify([`/krs-pack/${CORRUPT_TARGET.url}`]),
      corrupt?.pageSide,
    );

    // Network assertions over the whole session.
    const events = s.bidi.network.filter((e) => !e.url.startsWith("blob:") && !e.url.startsWith("data:"));
    const foreign = events.filter((e) => !e.url.startsWith(`${servers.origin}/`) && !(servers.packOrigin && e.url.startsWith(`${servers.packOrigin}/`)));
    const nonGet = events.filter((e) => e.method !== "GET").concat(servers.entries.filter((e) => e.method !== "GET") as any);
    const withBody = servers.entries.filter((e) => e.requestBodyBytes > 0);
    const canaryHits = [...events.map((e) => JSON.stringify(e)), ...servers.entries.map((e) => JSON.stringify(e))].filter((t) => t.includes(canary));
    const listed = new Set<string>([...MANIFEST_URLS, ...requiredAssets.map((a) => `/krs-pack/${a.url}`)]);
    const unlisted = servers.entries.filter((e) => e.url.startsWith("/krs-pack/") && !listed.has(e.url));
    check(CROSS_ORIGIN ? "every request is a GET to the page origin or the pack origin" : "every request is a GET to the page origin", foreign.length === 0 && nonGet.length === 0, { foreign, nonGet });
    check("no request carries a body", withBody.length === 0, withBody);
    check("every pack request is index.json, the active release, or one of its required assets", unlisted.length === 0, unlisted);
    check("the canary in the edited source appears in no request", canaryHits.length === 0, { canary, hits: canaryHits.length });
    return { checks, steps, canary, network: s.bidi.network, server: servers.entries, version: s.version, memory: s.sampler.summary() };
  } catch (error) {
    check("session", false, String(error instanceof Error ? error.stack : error));
    return { checks, steps, network: session?.bidi.network ?? [], server: servers.entries, version: session?.version ?? null, memory: session?.sampler.summary() ?? null };
  } finally {
    await session?.close();
    await servers.stop();
  }
}

const summary: Record<string, unknown> = {};
let allPass = true;
for (const browser of values.browsers!.split(",") as Array<"chromium" | "firefox">) {
  const load = await waitForLoad(40);
  log(`${browser}: start at 1-minute load ${load}`);
  const result = await runBrowser(browser);
  const pass = result.checks.every((c) => c.pass);
  allPass &&= pass;
  writeFileSync(join(OUT, `${browser}-network.jsonl`), result.network.map((e) => JSON.stringify(e)).join("\n") + "\n");
  writeFileSync(join(OUT, `${browser}-server.jsonl`), result.server.map((e) => JSON.stringify(e)).join("\n") + "\n");
  writeFileSync(join(OUT, `${browser}-record.json`), `${JSON.stringify({ browser, version: result.version, loadAtStart: load, pass, checks: result.checks, steps: result.steps, memory: result.memory }, null, 1)}\n`);
  summary[browser] = { version: result.version, pass, failed: result.checks.filter((c) => !c.pass).map((c) => c.name), checks: result.checks.length };
}
writeFileSync(join(OUT, `summary-${values.expect}.json`), `${JSON.stringify(summary, null, 1)}\n`);
console.log(JSON.stringify(summary, null, 1));
process.exit(allPass ? 0 : 1);
