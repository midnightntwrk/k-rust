// Worker gate driver for one headless browser: fresh profile, one page session
// running the whole scenario plan (test/scenarios.ts) on the site that
// scripts/build-site.ts built.
//
//   bun test/browser/run-browser.ts --browser chromium|firefox [--site DIR] [--out DIR] [--bundles DIR] [--oracle FILE] [--port N]

import { join } from "node:path";
import { parseArgs } from "node:util";
import { openSite, type BrowserName, type SiteSession } from "../harness/browsers.ts";
import { firefoxBinary, scratchPath } from "../harness/environment.ts";
import { SCENARIOS } from "../scenarios.ts";
import { runPlan, writeOutputs } from "./plan.ts";

const { values } = parseArgs({
  options: {
    browser: { type: "string", default: "chromium" },
    site: { type: "string", default: scratchPath("krs-browser-site") },
    out: { type: "string", default: scratchPath("krs-browser-run/evidence") },
    bundles: { type: "string" },
    oracle: { type: "string", default: scratchPath("krs-browser-parity/oracle/native/collector-stdout.json") },
    firefox: { type: "string", default: firefoxBinary() },
    port: { type: "string" },
  },
});
const browser = values.browser as BrowserName;
if (browser !== "chromium" && browser !== "firefox") throw new Error("--browser is chromium or firefox");
const port = Number(values.port ?? (browser === "chromium" ? 4315 : 4325));
const bundles = values.bundles ?? join(values.out!, "..", browser);

let records: Awaited<ReturnType<typeof runPlan>> = [];
let failure: string | null = null;
let session: SiteSession | null = null;
try {
  session = await openSite({
    browser,
    site: values.site!,
    port,
    profilePrefix: scratchPath("krs-browser-profile-"),
    firefox: values.firefox!,
    chromiumArgs: ["--enable-precise-memory-info"],
  });
  records = await runPlan(session.evaluate, session.sampler, SCENARIOS.map((s) => s.name));
} catch (error) {
  failure = String(error instanceof Error ? error.stack : error);
} finally {
  await session?.close();
}
const memory = session?.sampler.summary() ?? null;
const verdicts = writeOutputs(browser, values.out!, bundles, values.oracle!, records, {
  failure,
  ...(session?.details ?? {}),
  memory,
  memorySamples: (session?.sampler.samples ?? []).map(({ top: _top, ...rest }) => rest),
  requestLog: session?.requestLog ?? [],
});
for (const c of verdicts.checks) process.stderr.write(`${c.pass ? "PASS" : "FAIL"} ${c.name}: ${c.detail.slice(0, 200)}\n`);
process.stderr.write(`${browser}: ${verdicts.pass && !failure ? "PASS" : "FAIL"}${failure ? ` ${failure}` : ""}; peak PSS ${memory?.peakPss?.pssKb} kB\n`);
process.exitCode = verdicts.pass && !failure ? 0 : 1;
