// Headless Chromium driver (WebDriver through a ChromeDriver this script
// starts), fresh profile, one page session running the whole plan.
//
//   bun test/browser/run-chromium.ts [--site DIR] [--out DIR] [--port N]

import { mkdtempSync, rmSync } from "node:fs";
import { parseArgs } from "node:util";
import { SCENARIOS } from "../scenarios.ts";
import { runPlan, serveSite, TreeSampler, writeOutputs } from "./common.ts";

const { values } = parseArgs({
  options: {
    site: { type: "string", default: "/var/tmp/krs-ir15-site" },
    out: { type: "string", default: "/var/tmp/krs-ir15-run/evidence" },
    bundles: { type: "string", default: "/var/tmp/krs-ir15-run/chromium" },
    oracle: { type: "string", default: "/var/tmp/krs-ir11-parity/oracle/descriptor-bundle.json" },
    port: { type: "string", default: "4315" },
  },
});
const port = Number(values.port);
const driverPort = port + 1;
const { server, log, origin } = serveSite(values.site!, port);
const profile = mkdtempSync("/var/tmp/krs-ir15-chromium-profile.");
const driver = Bun.spawn(["chromedriver", `--port=${driverPort}`], { stdout: "ignore", stderr: "ignore" });
const driverBase = `http://127.0.0.1:${driverPort}`;

async function webdriver(path: string, method = "GET", body?: unknown): Promise<any> {
  const response = await fetch(`${driverBase}${path}`, {
    method,
    headers: body === undefined ? {} : { "content-type": "application/json" },
    body: body === undefined ? undefined : JSON.stringify(body),
  });
  const payload = (await response.json()) as { value: any };
  if (!response.ok || payload.value?.error) throw new Error(`${method} ${path}: ${JSON.stringify(payload).slice(0, 2000)}`);
  return payload.value;
}

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
let session: any = null;
let records: Awaited<ReturnType<typeof runPlan>> = [];
let failure: string | null = null;
try {
  session = await webdriver("/session", "POST", {
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
  const evaluate = async (body: string) => {
    const text = await webdriver(`/session/${sessionId}/execute/async`, "POST", {
      script: `const done = arguments[arguments.length - 1];\n(async () => { ${body} })().then((v) => done(JSON.stringify({ ok: v })), (e) => done(JSON.stringify({ error: String(e && e.stack || e) })));`,
      args: [],
    });
    const parsed = JSON.parse(text as string) as { ok?: unknown; error?: string };
    if (parsed.error) throw new Error(parsed.error);
    return parsed.ok;
  };
  records = await runPlan(evaluate, sampler, SCENARIOS.map((s) => s.name));
} catch (error) {
  failure = String(error instanceof Error ? error.stack : error);
} finally {
  if (sessionId) await webdriver(`/session/${sessionId}`, "DELETE").catch(() => {});
  await Bun.sleep(300);
  sampler.stop();
  driver.kill();
  server.stop(true);
  rmSync(profile, { recursive: true, force: true });
}
const verdicts = writeOutputs("chromium", values.out!, values.bundles!, values.oracle!, records, {
  failure,
  browserVersion: session?.capabilities?.browserVersion ?? null,
  chromedriverVersion: session?.capabilities?.chrome?.chromedriverVersion ?? null,
  memory: sampler.summary(),
  memorySamples: sampler.samples.map(({ top: _top, ...rest }) => rest),
  requestLog: log,
});
for (const c of verdicts.checks) process.stderr.write(`${c.pass ? "PASS" : "FAIL"} ${c.name}: ${c.detail.slice(0, 200)}\n`);
process.stderr.write(`chromium: ${verdicts.pass && !failure ? "PASS" : "FAIL"}${failure ? ` ${failure}` : ""}; peak PSS ${sampler.summary().peakPss?.pssKb} kB\n`);
process.exitCode = verdicts.pass && !failure ? 0 : 1;
