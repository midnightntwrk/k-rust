// Worker gate: unit tests, the pipeline under Bun and Node, the controller
// under Bun, and the worker in headless Chromium and (when installed)
// headless Firefox. Waits while the 1-minute load average exceeds --load-max.
//
//   bun test/verify.ts [--out DIR] [--oracle FILE] [--load-max 40] [--skip-firefox]
//
// Prerequisites (defaults under the scratch root, harness/environment.ts): a
// dependency pack (krs-browser-pack/pack) staged by bun scripts/stage-assets.ts
// with the policy and expander modules, and the native oracle bundle
// (krs-browser-parity/oracle/native/collector-stdout.json).

import { existsSync, mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseArgs } from "node:util";
import { firefoxBinary, scratchPath, waitForLoad } from "./harness/environment.ts";

const { values } = parseArgs({
  options: {
    out: { type: "string", default: scratchPath("krs-browser-run/evidence") },
    "load-max": { type: "string", default: "40" },
    "skip-firefox": { type: "boolean", default: false },
    assets: { type: "string", default: scratchPath("krs-browser-assets") },
    oracle: { type: "string", default: scratchPath("krs-browser-parity/oracle/native/collector-stdout.json") },
  },
});
const root = join(import.meta.dir, "..");
const out = values.out!;
if (!existsSync(values.oracle!)) throw new Error(`native oracle bundle ${values.oracle} is missing; run test/parity/regenerate-oracle.sh`);
mkdirSync(out, { recursive: true });
const loadMax = Number(values["load-max"]);

interface StepResult {
  name: string;
  command: string[];
  exitCode: number;
  wallMs: number;
  load: number;
}
const results: StepResult[] = [];

async function step(name: string, command: string[]) {
  const load = await waitForLoad(loadMax);
  const started = performance.now();
  process.stderr.write(`== ${name}: ${command.join(" ")}\n`);
  const child = Bun.spawn(["nice", "-n", "10", ...command], { cwd: root, stdout: "inherit", stderr: "inherit" });
  const exitCode = await child.exited;
  results.push({ name, command, exitCode, wallMs: performance.now() - started, load });
  process.stderr.write(`== ${name}: ${exitCode === 0 ? "PASS" : `FAIL (${exitCode})`}\n`);
}

if (!existsSync(join(values.assets!, "pack.json"))) await step("stage-assets", ["bun", "scripts/stage-assets.ts", "--out", values.assets!]);
await step("build-site", ["bun", "scripts/build-site.ts", "--assets", values.assets!]);
await step("unit", ["bun", "test", "test/unit"]);
await step("pipeline-bun", ["bun", "test/run-pipeline.ts", "--assets", values.assets!, "--oracle", values.oracle!, "--evidence", "--out", join(out, "pipeline-bun.json")]);
await step("pipeline-node", ["node", "test/run-pipeline.ts", "--assets", values.assets!, "--oracle", values.oracle!, "--evidence", "--out", join(out, "pipeline-node.json")]);
await step("controller-bun", ["bun", "test/run-controller.ts", "--assets", values.assets!, "--oracle", values.oracle!, "--out", join(out, "controller-bun.json")]);
await step("chromium", ["bun", "test/browser/run-browser.ts", "--browser", "chromium", "--oracle", values.oracle!, "--out", out]);
if (!values["skip-firefox"] && existsSync(firefoxBinary())) await step("firefox", ["bun", "test/browser/run-browser.ts", "--browser", "firefox", "--oracle", values.oracle!, "--out", out]);

const pass = results.every((r) => r.exitCode === 0);
writeFileSync(join(out, "verify.json"), `${JSON.stringify({ pass, results }, null, 1)}\n`);
for (const r of results) process.stderr.write(`${r.exitCode === 0 ? "PASS" : "FAIL"} ${r.name} (${(r.wallMs / 1000).toFixed(1)} s, load ${r.load})\n`);
process.exit(pass ? 0 : 1);
