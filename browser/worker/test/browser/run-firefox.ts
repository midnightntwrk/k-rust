// Headless Firefox driver over WebDriver BiDi (no geckodriver), as BL-001's
// run-firefox-evidence.mjs: /usr/lib/firefox/firefox --headless --new-instance
// with a fresh /var/tmp profile. No visible window is opened.
//
//   bun test/browser/run-firefox.ts [--site DIR] [--out DIR] [--port N]

import { mkdtempSync, rmSync } from "node:fs";
import { parseArgs } from "node:util";
import { SCENARIOS } from "../scenarios.ts";
import { runPlan, serveSite, TreeSampler, writeOutputs } from "./common.ts";

const { values } = parseArgs({
  options: {
    site: { type: "string", default: "/var/tmp/krs-ir15-site" },
    out: { type: "string", default: "/var/tmp/krs-ir15-run/evidence" },
    bundles: { type: "string", default: "/var/tmp/krs-ir15-run/firefox" },
    oracle: { type: "string", default: "/var/tmp/krs-ir11-parity/oracle/descriptor-bundle.json" },
    firefox: { type: "string", default: "/usr/lib/firefox/firefox" },
    port: { type: "string", default: "4325" },
  },
});
const port = Number(values.port);
const bidiPort = port + 1;
const { server, log, origin } = serveSite(values.site!, port);
const profile = mkdtempSync("/var/tmp/krs-ir15-firefox-profile.");
const firefox = Bun.spawn(
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

const sampler = new TreeSampler(() => firefox.pid);
sampler.start();
let session: any = null;
let records: Awaited<ReturnType<typeof runPlan>> = [];
let failure: string | null = null;
try {
  session = await command("session.new", { capabilities: { alwaysMatch: { acceptInsecureCerts: false } } });
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
  const evaluate = async (body: string) => {
    const result = await evaluateRaw(`(async () => { ${body} })().then((v) => JSON.stringify({ ok: v }), (e) => JSON.stringify({ error: String(e && e.stack || e) }))`);
    const parsed = JSON.parse(result.value as string) as { ok?: unknown; error?: string };
    if (parsed.error) throw new Error(parsed.error);
    return parsed.ok;
  };
  records = await runPlan(evaluate, sampler, SCENARIOS.map((s) => s.name));
} catch (error) {
  failure = String(error instanceof Error ? error.stack : error);
} finally {
  await command("session.end").catch(() => {});
  socket.close();
  await Bun.sleep(300);
  sampler.stop();
  firefox.kill();
  await firefox.exited;
  server.stop(true);
  rmSync(profile, { recursive: true, force: true });
}
const verdicts = writeOutputs("firefox", values.out!, values.bundles!, values.oracle!, records, {
  failure,
  browserVersion: session?.capabilities?.browserVersion ?? null,
  userAgent: session?.capabilities?.userAgent ?? null,
  memory: sampler.summary(),
  memorySamples: sampler.samples.map(({ top: _top, ...rest }) => rest),
  requestLog: log,
});
for (const c of verdicts.checks) process.stderr.write(`${c.pass ? "PASS" : "FAIL"} ${c.name}: ${c.detail.slice(0, 200)}\n`);
process.stderr.write(`firefox: ${verdicts.pass && !failure ? "PASS" : "FAIL"}${failure ? ` ${failure}` : ""}; peak PSS ${sampler.summary().peakPss?.pssKb} kB\n`);
process.exitCode = verdicts.pass && !failure ? 0 : 1;
