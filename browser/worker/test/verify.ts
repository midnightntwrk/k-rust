// Worker gate: unit tests, the pipeline under Bun and Node, the controller
// under Bun, and the worker in headless Chromium and (when installed)
// headless Firefox. Waits while the 1-minute load average exceeds --load-max.
//
//   bun test/verify.ts [--out DIR] [--load-max 40] [--skip-firefox]
//
// Prerequisites: a dependency pack (default /var/tmp/krs-ir14-pack-a/pack) staged by
// bun scripts/stage-assets.ts with the policy and expander modules, and the
// native oracle bundle (default /var/tmp/krs-ir11-parity/oracle/descriptor-bundle.json).

import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseArgs } from "node:util";

const { values } = parseArgs({
  options: {
    out: { type: "string", default: "/var/tmp/krs-ir15-run/evidence" },
    "load-max": { type: "string", default: "40" },
    "skip-firefox": { type: "boolean", default: false },
    assets: { type: "string", default: "/var/tmp/krs-ir15-assets" },
  },
});
const root = join(import.meta.dir, "..");
const out = values.out!;
mkdirSync(out, { recursive: true });
const loadMax = Number(values["load-max"]);

async function waitForLoad() {
  for (;;) {
    const load = Number(readFileSync("/proc/loadavg", "utf8").split(" ")[0]);
    if (load <= loadMax) return load;
    process.stderr.write(`load ${load} > ${loadMax}, waiting 60 s\n`);
    await Bun.sleep(60_000);
  }
}

interface StepResult {
  name: string;
  command: string[];
  exitCode: number;
  wallMs: number;
  load: number;
}
const results: StepResult[] = [];

async function step(name: string, command: string[]) {
  const load = await waitForLoad();
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
await step("pipeline-bun", ["bun", "test/run-pipeline.ts", "--assets", values.assets!, "--evidence", "--out", join(out, "pipeline-bun.json")]);
await step("pipeline-node", ["node", "test/run-pipeline.ts", "--assets", values.assets!, "--evidence", "--out", join(out, "pipeline-node.json")]);
await step("controller-bun", ["bun", "test/run-controller.ts", "--assets", values.assets!, "--out", join(out, "controller-bun.json")]);
await step("chromium", ["bun", "test/browser/run-chromium.ts", "--out", out]);
if (!values["skip-firefox"] && existsSync("/usr/lib/firefox/firefox")) await step("firefox", ["bun", "test/browser/run-firefox.ts", "--out", out]);

const pass = results.every((r) => r.exitCode === 0);
writeFileSync(join(out, "verify.json"), `${JSON.stringify({ pass, results }, null, 1)}\n`);
for (const r of results) process.stderr.write(`${r.exitCode === 0 ? "PASS" : "FAIL"} ${r.name} (${(r.wallMs / 1000).toFixed(1)} s, load ${r.load})\n`);
process.exit(pass ? 0 : 1);
