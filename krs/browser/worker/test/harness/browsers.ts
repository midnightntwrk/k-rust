// The one headless browser driver of the browser tests.
//
// Chromium runs under a ChromeDriver this module starts (WebDriver classic, and
// WebDriver BiDi over the session's webSocketUrl when `bidi` is requested).
// Firefox runs as `firefox --headless --new-instance` with its WebDriver BiDi
// endpoint (no geckodriver). Every session uses a fresh profile directory under
// the scratch root, samples the browser process tree, and removes the profile
// on close. No visible window is opened.

import { mkdtempSync, rmSync } from "node:fs";
import { firefoxBinary, scratchPath } from "./environment.ts";
import { TreeSampler } from "./memory.ts";
import { serveSite, type RequestLogEntry } from "./server.ts";

export type BrowserName = "chromium" | "firefox";

export interface NetworkEvent {
  atMs: number;
  url: string;
  method: string;
  bodySize: number | null;
  headers: Array<{ name: string; value: string }>;
  destination: string | null;
  initiatorType: string | null;
}

/** A WebDriver BiDi connection; records network.beforeRequestSent events once subscribed. */
export class Bidi {
  readonly network: NetworkEvent[] = [];
  private readonly pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();
  private nextId = 0;
  private readonly started = performance.now();

  private constructor(private readonly socket: WebSocket) {
    socket.onmessage = (event) => {
      const message = JSON.parse(String(event.data));
      if (message.type === "event") {
        if (message.method === "network.beforeRequestSent") this.recordRequest(message.params);
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
        const socket = await new Promise<WebSocket>((resolve, reject) => {
          const ws = new WebSocket(url);
          ws.onopen = () => resolve(ws);
          ws.onerror = () => reject(new Error("connect"));
        });
        return new Bidi(socket);
      } catch {
        if (i > 300) throw new Error(`BiDi endpoint ${url} did not open`);
        await Bun.sleep(100);
      }
    }
  }

  command(method: string, params: Record<string, unknown> = {}): Promise<any> {
    return new Promise((resolve, reject) => {
      const id = ++this.nextId;
      this.pending.set(id, { resolve, reject });
      this.socket.send(JSON.stringify({ id, method, params }));
    });
  }

  close() {
    this.socket.close();
  }

  private recordRequest(params: any) {
    const r = params.request;
    this.network.push({
      atMs: performance.now() - this.started,
      url: r.url,
      method: r.method,
      bodySize: r.bodySize ?? null,
      headers: (r.headers ?? []).map((h: any) => ({ name: h.name, value: h.value?.value ?? "" })),
      destination: r.destination ?? null,
      initiatorType: r.initiatorType ?? params.initiator?.type ?? null,
    });
  }
}

export interface LaunchOptions {
  browser: BrowserName;
  /** ChromeDriver port (Chromium) or BiDi port (Firefox). */
  controlPort: number;
  /** Prefix of the fresh profile directory (default: krs-browser-profile- under the scratch root). */
  profilePrefix?: string;
  /** Chromium: also open a WebDriver BiDi connection and drive the page through it (Firefox always does). */
  bidi?: boolean;
  /** Record network.beforeRequestSent events in `session.network` (implies `bidi`). */
  network?: boolean;
  /** Extra Chromium command-line arguments. */
  chromiumArgs?: string[];
  /** BiDi viewport of the page (implies `bidi`). */
  viewport?: { width: number; height: number };
  /** Chromium WebDriver classic script timeout (default 15 min). */
  scriptTimeoutMs?: number;
  /** Memory sampling interval (default 100 ms). */
  sampleIntervalMs?: number;
  /** Firefox binary (default: KRS_FIREFOX, else the system Firefox). */
  firefox?: string;
}

export interface BrowserSession {
  browser: BrowserName;
  profile: string;
  sampler: TreeSampler;
  /** The session's WebDriver capabilities. */
  capabilities: Record<string, any>;
  /** Browser and driver versions for evidence records. */
  details: Record<string, unknown>;
  /** The BiDi connection, when the session has one. */
  bidi: Bidi | null;
  /** BiDi requests seen by the page (empty unless `network` was requested). */
  network: NetworkEvent[];
  /** Runs an async function body in the page and returns its JSON-safe result. */
  evaluate(body: string): Promise<unknown>;
  navigate(url: string): Promise<void>;
  /** Polls a function body until it returns "ready"; "loading" keeps waiting, any other value fails. */
  waitReady(stateBody: string, timeoutMs: number, intervalMs?: number): Promise<void>;
  /** PNG screenshot of the viewport (BiDi sessions only). */
  screenshot(): Promise<Uint8Array>;
  close(): Promise<void>;
}

const wrapBody = (body: string) =>
  `(async () => { ${body} })().then((v) => JSON.stringify({ ok: v }), (e) => JSON.stringify({ error: String(e && e.stack || e) }))`;

function unwrap(text: string): unknown {
  const parsed = JSON.parse(text) as { ok?: unknown; error?: string };
  if (parsed.error) throw new Error(parsed.error);
  return parsed.ok;
}

async function webdriverClient(port: number) {
  const base = `http://127.0.0.1:${port}`;
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
      return call;
    } catch {
      if (i > 100) throw new Error("chromedriver did not start");
      await Bun.sleep(100);
    }
  }
}

export async function launch(options: LaunchOptions): Promise<BrowserSession> {
  const useBidi = options.browser === "firefox" || options.bidi === true || options.network === true || options.viewport !== undefined;
  const profile = mkdtempSync(`${options.profilePrefix ?? scratchPath("krs-browser-profile-")}${options.browser}-profile.`);
  const proc =
    options.browser === "chromium"
      ? Bun.spawn(["chromedriver", `--port=${options.controlPort}`], { stdout: "ignore", stderr: "ignore" })
      : Bun.spawn(
          [options.firefox ?? firefoxBinary(), "--headless", "--new-instance", "--profile", profile, "--remote-debugging-port", String(options.controlPort),
            "--remote-allow-hosts", "127.0.0.1,localhost", "about:blank"],
          { stdout: "ignore", stderr: "ignore", env: { ...process.env, MOZ_HEADLESS: "1", DISPLAY: "", WAYLAND_DISPLAY: "" } },
        );
  const sampler = new TreeSampler(() => proc.pid);
  sampler.start(options.sampleIntervalMs);
  let bidi: Bidi | null = null;
  let endSession: () => Promise<void> = async () => {};
  const close = async () => {
    await endSession().catch(() => {});
    bidi?.close();
    await Bun.sleep(300);
    sampler.stop();
    proc.kill();
    await proc.exited;
    rmSync(profile, { recursive: true, force: true });
  };
  try {
    let capabilities: Record<string, any>;
    let details: Record<string, unknown>;
    let classic: ((path: string, method?: string, body?: unknown) => Promise<any>) | null = null;
    let sessionPath = "";
    if (options.browser === "chromium") {
      const call = await webdriverClient(options.controlPort);
      const session = await call("/session", "POST", {
        capabilities: {
          alwaysMatch: {
            browserName: "chrome",
            ...(useBidi ? { webSocketUrl: true } : {}),
            "goog:chromeOptions": {
              args: ["--headless=new", "--disable-dev-shm-usage", "--no-first-run", `--user-data-dir=${profile}`, ...(options.chromiumArgs ?? [])],
            },
          },
        },
      });
      sessionPath = `/session/${session.sessionId as string}`;
      endSession = async () => {
        await call(sessionPath, "DELETE");
      };
      capabilities = session.capabilities;
      details = { browserVersion: capabilities?.browserVersion ?? null, chromedriverVersion: capabilities?.chrome?.chromedriverVersion ?? null };
      if (useBidi) {
        bidi = await Bidi.connect(capabilities.webSocketUrl as string);
      } else {
        classic = call;
        await call(`${sessionPath}/timeouts`, "POST", { script: options.scriptTimeoutMs ?? 900_000, pageLoad: 600_000, implicit: 0 });
      }
    } else {
      bidi = await Bidi.connect(`ws://127.0.0.1:${options.controlPort}/session`);
      const connection = bidi;
      const session = await connection.command("session.new", { capabilities: { alwaysMatch: { acceptInsecureCerts: false } } });
      endSession = async () => {
        await connection.command("session.end");
      };
      capabilities = session.capabilities;
      details = { browserVersion: capabilities?.browserVersion ?? null, userAgent: capabilities?.userAgent ?? null };
    }
    let context: string | null = null;
    if (bidi) {
      if (options.network) await bidi.command("session.subscribe", { events: ["network.beforeRequestSent"] });
      const tree = await bidi.command("browsingContext.getTree", {});
      context = tree.contexts[0].context as string;
      if (options.viewport) await bidi.command("browsingContext.setViewport", { context, viewport: options.viewport });
    }
    const connection = bidi;
    const evaluate = async (body: string): Promise<unknown> => {
      if (connection) {
        const result = await connection.command("script.evaluate", { expression: wrapBody(body), target: { context }, awaitPromise: true, resultOwnership: "none" });
        if (result.type !== "success") throw new Error(`script exception: ${JSON.stringify(result).slice(0, 2000)}`);
        return unwrap(result.result.value as string);
      }
      const text = await classic!(`${sessionPath}/execute/async`, "POST", {
        script: `const done = arguments[arguments.length - 1];\n${wrapBody(body)}.then(done);`,
        args: [],
      });
      return unwrap(text as string);
    };
    const navigate = async (url: string) => {
      if (connection) await connection.command("browsingContext.navigate", { context, url, wait: "complete" });
      else await classic!(`${sessionPath}/url`, "POST", { url });
    };
    const waitReady = async (stateBody: string, timeoutMs: number, intervalMs = 100) => {
      const deadline = performance.now() + timeoutMs;
      for (;;) {
        const state = await evaluate(stateBody);
        if (state === "ready") return;
        if (state !== "loading") throw new Error(`page failed: ${String(state)}`);
        if (performance.now() > deadline) throw new Error("page did not become ready");
        await Bun.sleep(intervalMs);
      }
    };
    const screenshot = async () => {
      if (!connection) throw new Error("screenshots need a BiDi session");
      const result = await connection.command("browsingContext.captureScreenshot", { context, origin: "viewport" });
      return new Uint8Array(Buffer.from(result.data as string, "base64"));
    };
    return {
      browser: options.browser,
      profile,
      sampler,
      capabilities,
      details,
      bidi,
      network: bidi?.network ?? [],
      evaluate,
      navigate,
      waitReady,
      screenshot,
      close,
    };
  } catch (error) {
    await close();
    throw error;
  }
}

/** Readiness of the worker test pages (test/page, test/cache): they set window.krsPageReady. */
export const PAGE_READY = `return window.krsPageReady === true ? "ready" : "loading";`;

export interface SiteOptions extends Omit<LaunchOptions, "controlPort"> {
  /** Directory served at http://127.0.0.1:<port>/; the driver uses port + 1. */
  site: string;
  port: number;
  /** Readiness function body (see waitReady); default PAGE_READY. */
  ready?: string;
  readyTimeoutMs?: number;
  readyIntervalMs?: number;
}

export interface SiteSession extends BrowserSession {
  origin: string;
  requestLog: RequestLogEntry[];
}

/** Serves `site`, launches a browser on it, and waits until the page is ready; close stops both. */
export async function openSite(options: SiteOptions): Promise<SiteSession> {
  const server = serveSite(options.site, options.port);
  let session: BrowserSession;
  try {
    session = await launch({ ...options, controlPort: options.port + 1 });
  } catch (error) {
    server.stop();
    throw error;
  }
  const siteSession: SiteSession = {
    ...session,
    origin: server.origin,
    requestLog: server.log,
    close: async () => {
      await session.close();
      server.stop();
    },
  };
  try {
    await session.navigate(`${server.origin}/`);
    await session.waitReady(options.ready ?? PAGE_READY, options.readyTimeoutMs ?? 30_000, options.readyIntervalMs ?? 100);
    return siteSession;
  } catch (error) {
    await siteSession.close();
    throw error;
  }
}
