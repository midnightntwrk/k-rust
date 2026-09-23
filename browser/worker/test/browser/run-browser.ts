// Worker gate driver for one headless browser: fresh profile, one page session
// running the whole scenario plan (test/scenarios.ts).
//
//   bun test/browser/run-browser.ts --browser chromium|firefox [--site DIR] [--out DIR] [--port N]
//
// run-chromium.ts and run-firefox.ts are kept as entry points with the worker gate defaults.

import { parseArgs } from "node:util";
import { SCENARIOS } from "../scenarios.ts";
import { runPlan, writeOutputs } from "./common.ts";
import { launch } from "./drivers.ts";

export async function main(browser: "chromium" | "firefox", defaults: { port: string }) {
  const { values } = parseArgs({
    args: Bun.argv.slice(2),
    options: {
      browser: { type: "string", default: browser },
      site: { type: "string", default: "/var/tmp/krs-ir15-site" },
      out: { type: "string", default: "/var/tmp/krs-ir15-run/evidence" },
      bundles: { type: "string", default: `/var/tmp/krs-ir15-run/${browser}` },
      oracle: { type: "string", default: "/var/tmp/krs-ir11-parity/oracle/descriptor-bundle.json" },
      firefox: { type: "string", default: process.env.KRS_FIREFOX ?? "/usr/lib/firefox/firefox" },
      port: { type: "string", default: defaults.port },
    },
  });
  let records: Awaited<ReturnType<typeof runPlan>> = [];
  let failure: string | null = null;
  let session: Awaited<ReturnType<typeof launch>> | null = null;
  try {
    session = await launch(browser, { site: values.site!, port: Number(values.port), profilePrefix: "/var/tmp/krs-ir15-", firefox: values.firefox });
    records = await runPlan(session.evaluate, session.sampler, SCENARIOS.map((s) => s.name));
  } catch (error) {
    failure = String(error instanceof Error ? error.stack : error);
  } finally {
    await session?.close();
  }
  const memory = session?.sampler.summary() ?? null;
  const verdicts = writeOutputs(browser, values.out!, values.bundles!, values.oracle!, records, {
    failure,
    ...(session?.details ?? {}),
    memory,
    memorySamples: (session?.sampler.samples ?? []).map(({ top: _top, ...rest }) => rest),
    requestLog: session?.requestLog ?? [],
  });
  for (const c of verdicts.checks) process.stderr.write(`${c.pass ? "PASS" : "FAIL"} ${c.name}: ${c.detail.slice(0, 200)}\n`);
  process.stderr.write(`${browser}: ${verdicts.pass && !failure ? "PASS" : "FAIL"}${failure ? ` ${failure}` : ""}; peak PSS ${memory?.peakPss?.pssKb} kB\n`);
  process.exitCode = verdicts.pass && !failure ? 0 : 1;
}

if (import.meta.main) {
  const browser = (Bun.argv.includes("firefox") ? "firefox" : "chromium") as "chromium" | "firefox";
  await main(browser, { port: browser === "chromium" ? "4315" : "4325" });
}
