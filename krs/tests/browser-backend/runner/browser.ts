// Headless browser host of the suite, run with Bun:
//
//   bun runner/browser.ts --browser chromium|firefox --site DIR --out FILE [--only ID,ID] [--port N]
//
// Drives the site through the shared browser driver
// (browser/worker/test/harness/browsers.ts): Chromium over WebDriver, Firefox
// over WebDriver BiDi, a fresh profile, and one page session for the whole suite.

import { writeFileSync } from "node:fs";
import { parseArgs } from "node:util";
import { openSite, type BrowserName, type SiteSession } from "../../../browser/worker/test/harness/browsers.ts";
import { firefoxBinary, scratchPath } from "../../../browser/worker/test/harness/environment.ts";
import type { HostRecord } from "./protocol.ts";

const { values } = parseArgs({
  options: {
    browser: { type: "string" },
    site: { type: "string" },
    out: { type: "string" },
    only: { type: "string", default: "" },
    port: { type: "string", default: "" },
    firefox: { type: "string", default: firefoxBinary() },
  },
});
const browser = values.browser as BrowserName;
if (!["chromium", "firefox"].includes(browser) || !values.site || !values.out) {
  throw new Error("usage: bun runner/browser.ts --browser chromium|firefox --site DIR --out FILE");
}
const port = Number(values.port || (browser === "chromium" ? 4616 : 4626));
const only = values.only ? values.only.split(",") : [];
const started = performance.now();

let session: SiteSession | null = null;
let record: HostRecord | null = null;
let failure: string | null = null;
try {
  session = await openSite({
    browser,
    site: values.site,
    port,
    profilePrefix: scratchPath("krs-backend-"),
    firefox: values.firefox!,
    scriptTimeoutMs: 3_600_000,
    sampleIntervalMs: 250,
    ready: "return window.krsBackendReady === true ? 'ready' : (window.krsBackendError ?? 'loading');",
    readyTimeoutMs: 300_000,
    readyIntervalMs: 250,
  });
  session.sampler.phase = "suite";
  const text = (await session.evaluate(`return await window.krsBackend.run(${JSON.stringify(only)});`)) as string;
  record = JSON.parse(text) as HostRecord;
} catch (error) {
  failure = String(error instanceof Error ? error.stack : error);
} finally {
  await session?.close();
}
if (!record) {
  process.stderr.write(`${browser}: FAIL ${failure}\n`);
  process.exit(1);
}
const capabilities = session?.capabilities ?? {};
record.host = browser;
record.environment = {
  ...record.environment,
  browserName: capabilities.browserName ?? null,
  browserVersion: capabilities.browserVersion ?? null,
  driver: browser === "chromium" ? `chromedriver ${capabilities.chrome?.chromedriverVersion ?? ""}`.trim() : "WebDriver BiDi (no geckodriver)",
  headless: true,
  memory: session?.sampler.summary() ?? null,
  requests: session?.requestLog.length ?? 0,
  driverWallMs: performance.now() - started,
};
writeFileSync(values.out, `${JSON.stringify(record, null, 1)}\n`);
process.stderr.write(`${browser}: wrote ${values.out} (${record.cases.length} cases, ${(record.wall_ms / 1000).toFixed(1)} s in the page)\n`);
