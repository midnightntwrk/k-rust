// Headless browser sessions for the worker gates: Chromium over WebDriver
// (a ChromeDriver this module starts) and Firefox over WebDriver BiDi (no
// geckodriver; /usr/lib/firefox/firefox --headless --new-instance, as BL-001).
// Each session uses a fresh /var/tmp profile, serves the site from localhost,
// samples the browser process tree, and removes the profile on close. No
// visible window is opened.

import { mkdtempSync, rmSync } from "node:fs";
import { serveSite, TreeSampler, type Evaluate, type RequestLogEntry } from "./common.ts";

export interface BrowserSession {
  browser: "chromium" | "firefox";
  /** Runs an async function body in the page and returns its JSON-safe result. */
  evaluate: Evaluate;
  sampler: TreeSampler;
  requestLog: RequestLogEntry[];
  profile: string;
  details: Record<string, unknown>;
  close(): Promise<void>;
}

export interface LaunchOptions {
  site: string;
  port: number;
  /** Profile directory prefix under /var/tmp (a fresh directory is created per session). */
  profilePrefix: string;
  firefox?: string;
}

export async function launchChromium(options: LaunchOptions): Promise<BrowserSession> {
  const { server, log, origin } = serveSite(options.site, options.port);
  const profile = mkdtempSync(`${options.profilePrefix}chromium-profile.`);
  const driverPort = options.port + 1;
  const driver = Bun.spawn(["chromedriver", `--port=${driverPort}`], { stdout: "ignore", stderr: "ignore" });
  const driverBase = `http://127.0.0.1:${driverPort}`;
  const webdriver = async (path: string, method = "GET", body?: unknown): Promise<any> => {
    const response = await fetch(`${driverBase}${path}`, {
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
      await webdriver("/status");
      break;
    } catch {
      if (i > 100) throw new Error("chromedriver did not start");
      await Bun.sleep(100);
    }
  }
  const sampler = new TreeSampler(() => driver.pid);
  sampler.start();
  let sessionId: string | null = null;
  const close = async () => {
    if (sessionId) await webdriver(`/session/${sessionId}`, "DELETE").catch(() => {});
    await Bun.sleep(300);
    sampler.stop();
    driver.kill();
    await driver.exited;
    server.stop(true);
    rmSync(profile, { recursive: true, force: true });
  };
  try {
    const session = await webdriver("/session", "POST", {
      capabilities: {
        alwaysMatch: {
          browserName: "chrome",
          "goog:chromeOptions": {
            args: ["--headless=new", "--disable-dev-shm-usage", "--no-first-run", `--user-data-dir=${profile}`, "--enable-precise-memory-info"],
          },
        },
      },
    });
    sessionId = session.sessionId as string;
    await webdriver(`/session/${sessionId}/timeouts`, "POST", { script: 900_000, pageLoad: 600_000, implicit: 0 });
    await webdriver(`/session/${sessionId}/url`, "POST", { url: `${origin}/` });
    for (let i = 0; !(await webdriver(`/session/${sessionId}/execute/sync`, "POST", { script: "return window.ir15Ready === true;", args: [] })); i += 1) {
      if (i > 300) throw new Error("page did not become ready");
      await Bun.sleep(100);
    }
    const evaluate: Evaluate = async (body) => {
      const text = await webdriver(`/session/${sessionId}/execute/async`, "POST", {
        script: `const done = arguments[arguments.length - 1];\n(async () => { ${body} })().then((v) => done(JSON.stringify({ ok: v })), (e) => done(JSON.stringify({ error: String(e && e.stack || e) })));`,
        args: [],
      });
      const parsed = JSON.parse(text as string) as { ok?: unknown; error?: string };
      if (parsed.error) throw new Error(parsed.error);
      return parsed.ok;
    };
    return {
      browser: "chromium",
      evaluate,
      sampler,
      requestLog: log,
      profile,
      details: {
        browserVersion: session.capabilities?.browserVersion ?? null,
        chromedriverVersion: session.capabilities?.chrome?.chromedriverVersion ?? null,
      },
      close,
    };
  } catch (error) {
    await close();
    throw error;
  }
}

export async function launchFirefox(options: LaunchOptions): Promise<BrowserSession> {
  const { server, log, origin } = serveSite(options.site, options.port);
  const profile = mkdtempSync(`${options.profilePrefix}firefox-profile.`);
  const bidiPort = options.port + 1;
  const firefox = Bun.spawn(
    [options.firefox ?? "/usr/lib/firefox/firefox", "--headless", "--new-instance", "--profile", profile, "--remote-debugging-port", String(bidiPort), "--remote-allow-hosts", "127.0.0.1,localhost", "about:blank"],
    { stdout: "ignore", stderr: "ignore", env: { ...process.env, MOZ_HEADLESS: "1", DISPLAY: "", WAYLAND_DISPLAY: "" } },
  );
  const sampler = new TreeSampler(() => firefox.pid);
  sampler.start();
  let socket: WebSocket | null = null;
  const close = async () => {
    if (socket) {
      await command("session.end").catch(() => {});
      socket.close();
    }
    await Bun.sleep(300);
    sampler.stop();
    firefox.kill();
    await firefox.exited;
    server.stop(true);
    rmSync(profile, { recursive: true, force: true });
  };
  const pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();
  let nextId = 0;
  const command = (method: string, params: Record<string, unknown> = {}) =>
    new Promise<any>((resolve, reject) => {
      const id = ++nextId;
      pending.set(id, { resolve, reject });
      socket!.send(JSON.stringify({ id, method, params }));
    });
  try {
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
    socket.onmessage = (event) => {
      const message = JSON.parse(String(event.data));
      if (message.type === "event") return;
      const waiter = pending.get(message.id);
      if (!waiter) return;
      pending.delete(message.id);
      if (message.type === "success") waiter.resolve(message.result);
      else waiter.reject(new Error(JSON.stringify(message).slice(0, 2000)));
    };
    const session = await command("session.new", { capabilities: { alwaysMatch: { acceptInsecureCerts: false } } });
    const tree = await command("browsingContext.getTree", {});
    const context = tree.contexts[0].context as string;
    await command("browsingContext.navigate", { context, url: `${origin}/`, wait: "complete" });
    const evaluateRaw = async (expression: string) => {
      const result = await command("script.evaluate", { expression, target: { context }, awaitPromise: true, resultOwnership: "none" });
      if (result.type !== "success") throw new Error(`script exception: ${JSON.stringify(result).slice(0, 2000)}`);
      return result.result;
    };
    for (let i = 0; (await evaluateRaw("window.ir15Ready === true")).value !== true; i += 1) {
      if (i > 300) throw new Error("page did not become ready");
      await Bun.sleep(100);
    }
    const evaluate: Evaluate = async (body) => {
      const result = await evaluateRaw(`(async () => { ${body} })().then((v) => JSON.stringify({ ok: v }), (e) => JSON.stringify({ error: String(e && e.stack || e) }))`);
      const parsed = JSON.parse(result.value as string) as { ok?: unknown; error?: string };
      if (parsed.error) throw new Error(parsed.error);
      return parsed.ok;
    };
    return {
      browser: "firefox",
      evaluate,
      sampler,
      requestLog: log,
      profile,
      details: {
        browserVersion: session.capabilities?.browserVersion ?? null,
        userAgent: session.capabilities?.userAgent ?? null,
      },
      close,
    };
  } catch (error) {
    await close();
    throw error;
  }
}

export function launch(browser: "chromium" | "firefox", options: LaunchOptions): Promise<BrowserSession> {
  return browser === "chromium" ? launchChromium(options) : launchFirefox(options);
}
