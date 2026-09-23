// Headless browser host of the suite, run with Bun:
//
//   bun runner/browser.ts --browser chromium|firefox --site DIR --out FILE [--only ID,ID] [--port N]
//
// Chromium: WebDriver through a ChromeDriver this script starts (--headless=new).
// Firefox: WebDriver BiDi on /usr/lib/firefox/firefox --headless --new-instance.
// Both use a fresh /var/tmp profile and one page session for the whole suite, as
// the worker gate drivers do (browser/worker/test/browser/). No window is opened.

import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { parseArgs } from "node:util";
import { serveSite, TreeSampler } from "../../../browser/worker/test/browser/common.ts";
import type { HostRecord } from "./protocol.ts";

const { values } = parseArgs({
  options: {
    browser: { type: "string" },
    site: { type: "string" },
    out: { type: "string" },
    only: { type: "string", default: "" },
    port: { type: "string", default: "" },
    firefox: { type: "string", default: process.env.KRS_FIREFOX ?? "/usr/lib/firefox/firefox" },
  },
});
const browser = values.browser as "chromium" | "firefox";
if (!["chromium", "firefox"].includes(browser) || !values.site || !values.out) {
  throw new Error("usage: bun runner/browser.ts --browser chromium|firefox --site DIR --out FILE");
}
const port = Number(values.port || (browser === "chromium" ? 4616 : 4626));
const only = values.only ? values.only.split(",") : [];
const { server, log, origin } = serveSite(values.site, port);
const profile = mkdtempSync(`/var/tmp/krs-backend-${browser}-profile.`);
const started = performance.now();

interface Session {
  pid: number;
  evaluate(expression: string): Promise<unknown>;
  capabilities: Record<string, unknown>;
  close(): Promise<void>;
}

async function chromium(): Promise<Session> {
  const driverPort = port + 1;
  const driver = Bun.spawn(["chromedriver", `--port=${driverPort}`], { stdout: "ignore", stderr: "ignore" });
  const base = `http://127.0.0.1:${driverPort}`;
  const call = async (path: string, method = "GET", body?: unknown): Promise<any> => {
    const response = await fetch(`${base}${path}`, {
      method,
      headers: body === undefined ? {} : { "content-type": "application/json" },
      body: body === undefined ? undefined : JSON.stringify(body),
    });
    const payload = (await response.json()) as { value: any };
    if (!response.ok || payload.value?.error) throw new Error(`${method} ${path}: ${JSON.stringify(payload).slice(0, 2000)}`);
    return payload.value;
  };
  for (let i = 0; ; i += 1) {
    try {
      await call("/status");
      break;
    } catch {
      if (i > 100) throw new Error("chromedriver did not start");
      await Bun.sleep(100);
    }
  }
  const session = await call("/session", "POST", {
    capabilities: {
      alwaysMatch: {
        browserName: "chrome",
        "goog:chromeOptions": { args: ["--headless=new", "--disable-dev-shm-usage", "--no-first-run", `--user-data-dir=${profile}`] },
      },
    },
  });
  const id = session.sessionId as string;
  await call(`/session/${id}/timeouts`, "POST", { script: 3_600_000, pageLoad: 600_000, implicit: 0 });
  await call(`/session/${id}/url`, "POST", { url: `${origin}/` });
  return {
    pid: driver.pid,
    capabilities: session.capabilities,
    evaluate: async (expression) => {
      const text = await call(`/session/${id}/execute/async`, "POST", {
        script: `const done = arguments[arguments.length - 1];\nPromise.resolve().then(async () => (${expression})).then((v) => done(JSON.stringify({ ok: v })), (e) => done(JSON.stringify({ error: String(e && e.stack || e) })));`,
        args: [],
      });
      const parsed = JSON.parse(text as string) as { ok?: unknown; error?: string };
      if (parsed.error) throw new Error(parsed.error);
      return parsed.ok;
    },
    close: async () => {
      await call(`/session/${id}`, "DELETE").catch(() => {});
      driver.kill();
    },
  };
}

async function firefox(): Promise<Session> {
  const bidiPort = port + 1;
  const process_ = Bun.spawn(
    [values.firefox!, "--headless", "--new-instance", "--profile", profile, "--remote-debugging-port", String(bidiPort), "--remote-allow-hosts", "127.0.0.1,localhost", "about:blank"],
    { stdout: "ignore", stderr: "ignore", env: { ...process.env, MOZ_HEADLESS: "1", DISPLAY: "", WAYLAND_DISPLAY: "" } },
  );
  let socket: WebSocket | null = null;
  for (let i = 0; socket === null; i += 1) {
    try {
      socket = await new Promise<WebSocket>((resolve, reject) => {
        const ws = new WebSocket(`ws://127.0.0.1:${bidiPort}/session`);
        ws.onopen = () => resolve(ws);
        ws.onerror = () => reject(new Error("connect"));
      });
    } catch {
      if (i > 300) throw new Error("Firefox BiDi endpoint did not open");
      await Bun.sleep(100);
    }
  }
  const pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();
  let nextId = 0;
  socket.onmessage = (event) => {
    const message = JSON.parse(String(event.data));
    if (message.type === "event") return;
    const waiter = pending.get(message.id);
    if (!waiter) return;
    pending.delete(message.id);
    if (message.type === "success") waiter.resolve(message.result);
    else waiter.reject(new Error(JSON.stringify(message).slice(0, 2000)));
  };
  const command = (method: string, params: Record<string, unknown> = {}) =>
    new Promise<any>((resolve, reject) => {
      const id = ++nextId;
      pending.set(id, { resolve, reject });
      socket!.send(JSON.stringify({ id, method, params }));
    });
  const session = await command("session.new", { capabilities: { alwaysMatch: { acceptInsecureCerts: false } } });
  const tree = await command("browsingContext.getTree", {});
  const context = tree.contexts[0].context as string;
  await command("browsingContext.navigate", { context, url: `${origin}/`, wait: "complete" });
  return {
    pid: process_.pid,
    capabilities: session.capabilities,
    evaluate: async (expression) => {
      const result = await command("script.evaluate", {
        expression: `Promise.resolve().then(async () => (${expression})).then((v) => JSON.stringify({ ok: v }), (e) => JSON.stringify({ error: String(e && e.stack || e) }))`,
        target: { context },
        awaitPromise: true,
        resultOwnership: "none",
      });
      if (result.type !== "success") throw new Error(`script exception: ${JSON.stringify(result).slice(0, 2000)}`);
      const parsed = JSON.parse(result.result.value as string) as { ok?: unknown; error?: string };
      if (parsed.error) throw new Error(parsed.error);
      return parsed.ok;
    },
    close: async () => {
      await command("session.end").catch(() => {});
      socket!.close();
      process_.kill();
      await process_.exited;
    },
  };
}

let session: Session | null = null;
let sampler: TreeSampler | null = null;
let record: HostRecord | null = null;
let failure: string | null = null;
try {
  session = browser === "chromium" ? await chromium() : await firefox();
  sampler = new TreeSampler(() => session!.pid);
  sampler.start(250);
  for (let i = 0; ; i += 1) {
    const state = (await session.evaluate("window.krsBackendReady === true ? 'ready' : (window.krsBackendError ?? 'loading')")) as string;
    if (state === "ready") break;
    if (state !== "loading") throw new Error(`page failed: ${state}`);
    if (i > 1200) throw new Error("page did not become ready");
    await Bun.sleep(250);
  }
  sampler.phase = "suite";
  const text = (await session.evaluate(`window.krsBackend.run(${JSON.stringify(only)})`)) as string;
  record = JSON.parse(text) as HostRecord;
} catch (error) {
  failure = String(error instanceof Error ? error.stack : error);
} finally {
  await session?.close();
  await Bun.sleep(300);
  sampler?.stop();
  server.stop(true);
  rmSync(profile, { recursive: true, force: true });
}
if (!record) {
  process.stderr.write(`${browser}: FAIL ${failure}\n`);
  process.exit(1);
}
record.host = browser;
record.environment = {
  ...record.environment,
  browserName: session?.capabilities?.browserName ?? null,
  browserVersion: session?.capabilities?.browserVersion ?? null,
  driver: browser === "chromium" ? `chromedriver ${(session?.capabilities?.chrome as { chromedriverVersion?: string } | undefined)?.chromedriverVersion ?? ""}`.trim() : "WebDriver BiDi (no geckodriver)",
  headless: true,
  memory: sampler?.summary() ?? null,
  requests: log.length,
  driverWallMs: performance.now() - started,
};
writeFileSync(values.out, `${JSON.stringify(record, null, 1)}\n`);
process.stderr.write(`${browser}: wrote ${values.out} (${record.cases.length} cases, ${(record.wall_ms / 1000).toFixed(1)} s in the page)\n`);
