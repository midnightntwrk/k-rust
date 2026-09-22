// Runs the pipeline stage functions directly (no worker) under Bun or Node
// (Node 24 strips the types), over the staged assets, and records events,
// timings, and memory.
//
//   bun test/run-pipeline.ts [--assets DIR] [--out FILE.json] [--only NAME,...] [--repeat N]
//   node test/run-pipeline.ts ...

import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import process from "node:process";
import { parseArgs } from "node:util";
import { loadVerifiedAssets } from "../src/pack.ts";
import { createPipelineContext, runBuild } from "../src/pipeline.ts";
import type { CompileEvent, LessonManifest, PackManifest } from "../src/protocol.ts";
import { check, SCENARIOS } from "./scenarios.ts";

const { values } = parseArgs({
  options: {
    assets: { type: "string", default: "/var/tmp/krs-ir15-assets" },
    out: { type: "string" },
    only: { type: "string" },
    repeat: { type: "string", default: "1" },
    evidence: { type: "boolean", default: false },
  },
});
const assetsDir = values.assets!;
const here = new URL(".", import.meta.url).pathname;
const host = typeof (globalThis as { Bun?: unknown }).Bun !== "undefined"
  ? `bun ${(globalThis as unknown as { Bun: { version: string } }).Bun.version}`
  : `node ${process.version}`;

// Peak RSS by sampling (process.memoryUsage) plus the kernel high-water mark.
let peakRss = 0;
const vmHwm = (): number | null => {
  try {
    const kb = /VmHWM:\s+(\d+) kB/.exec(readFileSync("/proc/self/status", "utf8"))?.[1];
    return kb ? Number(kb) * 1024 : null;
  } catch {
    return null;
  }
};
const memory = () => {
  const usage = process.memoryUsage();
  peakRss = Math.max(peakRss, usage.rss);
  return { rss: usage.rss, heapUsed: usage.heapUsed, external: usage.external, arrayBuffers: usage.arrayBuffers };
};
const sampler = setInterval(memory, 50);

const t0 = performance.now();
const pack = JSON.parse(readFileSync(join(assetsDir, "pack.json"), "utf8")) as PackManifest;
const lesson = JSON.parse(readFileSync(join(assetsDir, "lessons/tour-minimal/lesson.json"), "utf8")) as LessonManifest;
const assets = await loadVerifiedAssets(pack, async (path) => new Uint8Array(readFileSync(join(assetsDir, path))));
const loadMs = performance.now() - t0;
const t1 = performance.now();
const ctx = createPipelineContext(pack, assets);
const contextMs = performance.now() - t1;

const only = values.only ? new Set(values.only.split(",")) : null;
const records = [];
let generation = 0;
let failed = 0;
for (let round = 0; round < Number(values.repeat); round += 1) {
  for (const scenario of SCENARIOS) {
    if (only && !only.has(scenario.name)) continue;
    const source = readFileSync(join(here, "fixtures", scenario.fixture), "utf8");
    const events: CompileEvent[] = [];
    const started = performance.now();
    const result = await runBuild(
      ctx,
      { generation: ++generation, lesson, files: { "src/lib.rs": source }, debugEvidence: values.evidence },
      { emit: (event) => events.push(event), memory },
    );
    const wallMs = performance.now() - started;
    const verdict = check(scenario.expect, events);
    if (!verdict.ok) failed += 1;
    const terminal = events[events.length - 1]!;
    process.stderr.write(
      `${scenario.name}: ${verdict.ok ? "PASS" : "FAIL"} ${terminal.type}` +
        `${terminal.type === "success" ? ` ${terminal.bundleSha256} (${terminal.bundle.byteLength} bytes)` : ""}` +
        `${terminal.type === "failure" ? ` ${terminal.stage}/${terminal.code}: ${terminal.message.split("\n")[0]}` : ""}` +
        ` ${wallMs.toFixed(0)} ms${verdict.ok ? "" : `\n  ${verdict.problems.join("\n  ")}`}\n`,
    );
    records.push({
      scenario: scenario.name,
      round,
      wallMs,
      replaceWorker: result.replaceWorker,
      verdict,
      events: events.map((event) => {
        const slim = (e: typeof event) =>
          "evidence" in e && e.evidence ? { ...e, evidence: { ...e.evidence, expandedText: undefined, sourceMap: undefined } } : e;
        return event.type === "success" ? { ...slim(event), bundle: { bytes: event.bundle.byteLength } } : slim(event);
      }),
    });
  }
}
clearInterval(sampler);
memory();
const summary = {
  host,
  platform: `${process.platform} ${process.arch}`,
  assets: assetsDir,
  pack_id: pack.pack_id,
  loadAndVerifyMs: loadMs,
  contextMs,
  peakRssSampledBytes: peakRss,
  vmHwmBytes: vmHwm(),
  failed,
  records,
};
if (values.out) writeFileSync(values.out, `${JSON.stringify(summary, null, 1)}\n`);
process.stderr.write(`host ${host}; load+verify ${loadMs.toFixed(0)} ms; context ${contextMs.toFixed(0)} ms; peak RSS ${(peakRss / 2 ** 20).toFixed(0)} MiB; VmHWM ${((vmHwm() ?? 0) / 2 ** 20).toFixed(0)} MiB; failed ${failed}\n`);
process.exitCode = failed === 0 ? 0 : 1;
