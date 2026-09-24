// The worker gate's scenario plan, run in one page session per browser, and
// its outputs: bundles, events JSONL, the record, and the verdicts.

import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import type { TreeSampler } from "../harness/memory.ts";

// ---------------------------------------------------------------- plan

export type Evaluate = (body: string) => Promise<unknown>;

export interface StepRecord {
  step: string;
  wallMs: number;
  result: unknown;
  error: string | null;
}

/** Runs the scenario plan in one page session; `evaluate` runs an async function body in the page. */
export async function runPlan(evaluate: Evaluate, sampler: TreeSampler, scenarios: string[]): Promise<StepRecord[]> {
  const steps: Array<[string, string]> = [
    ["init", "return await window.krsWorker.init();"],
    ...scenarios.map((name): [string, string] => [name, `return await window.krsWorker.run(${JSON.stringify(name)});`]),
    ["cancel-during-rustc-lesson", "return await window.krsWorker.cancelDuringRustcLesson(100);"],
    ["supersede", "return await window.krsWorker.supersede();"],
    ["tour-minimal-final", `return await window.krsWorker.run("tour-minimal");`],
  ];
  const records: StepRecord[] = [];
  for (const [step, body] of steps) {
    sampler.phase = step;
    const started = performance.now();
    let result: unknown = null;
    let error: string | null = null;
    try {
      result = await evaluate(body);
    } catch (e) {
      error = String(e instanceof Error ? e.stack ?? e.message : e);
    }
    records.push({ step, wallMs: performance.now() - started, result, error });
    process.stderr.write(`${step}: ${error ? `ERROR ${error.split("\n")[0]}` : "done"} (${(performance.now() - started).toFixed(0)} ms)\n`);
  }
  sampler.phase = "teardown";
  return records;
}

// ---------------------------------------------------------------- output

export interface Verdicts {
  pass: boolean;
  checks: Array<{ name: string; pass: boolean; detail: string }>;
}

/** Writes bundles, events JSONL, and the record; compares bundles byte for byte with the oracle. */
export function writeOutputs(
  browser: string,
  outDir: string,
  bundleDir: string,
  oraclePath: string,
  records: StepRecord[],
  extra: Record<string, unknown>,
): Verdicts {
  mkdirSync(outDir, { recursive: true });
  mkdirSync(bundleDir, { recursive: true });
  const oracle = new Uint8Array(readFileSync(oraclePath));
  const checks: Verdicts["checks"] = [];
  const lines: string[] = [];
  const bundles: Record<string, string> = {};
  const scrub = (value: unknown): unknown => {
    // Drop base64 bundles from the retained record (they are written as files).
    if (Array.isArray(value)) return value.map(scrub);
    if (value && typeof value === "object") {
      const out: Record<string, unknown> = {};
      for (const [k, v] of Object.entries(value)) if (k !== "base64") out[k] = scrub(v);
      return out;
    }
    return value;
  };
  for (const record of records) {
    const result = record.result as Record<string, unknown> | null;
    if (record.error) checks.push({ name: record.step, pass: false, detail: record.error.split("\n")[0]! });
    const events = (result?.events ?? []) as Array<Record<string, unknown>>;
    for (const event of events) {
      const bundle = event.bundle as { base64?: string } | undefined;
      if (event.type === "success" && bundle?.base64) {
        const bytes = Uint8Array.from(atob(bundle.base64), (c) => c.charCodeAt(0));
        const file = join(bundleDir, `${record.step}.json`);
        writeFileSync(file, bytes);
        const same = bytes.length === oracle.length && bytes.every((b, i) => b === oracle[i]);
        bundles[record.step] = file;
        checks.push({ name: `${record.step}: bundle equals oracle byte for byte`, pass: same, detail: `${bytes.length} bytes ${event.bundleSha256}` });
      }
    }
    if (result && "verdict" in result) {
      const verdict = result.verdict as { ok: boolean; problems: string[] };
      checks.push({ name: `${record.step}: expected events`, pass: verdict.ok, detail: verdict.problems.join("; ") || "ok" });
      // Only a replacement worker's own script (a local static asset) may load during a build.
      const requests = (result.requestsDuringBuild ?? []) as string[];
      checks.push({
        name: `${record.step}: no network request during the build except local worker.js`,
        pass: requests.every((name) => /^http:\/\/127\.0\.0\.1:\d+\/worker\.js$/.test(name)),
        detail: requests.length === 0 ? "none" : requests.join(", "),
      });
    }
    if (record.step === "cancel-during-rustc-lesson" && result) {
      const recovery = result.recovery as { verdict: { ok: boolean }; events: Array<Record<string, unknown>> };
      const cancelled = (result.events as Array<Record<string, unknown>>);
      const sawRustcStart = cancelled.some((e) => e.type === "progress" && e.stage === "rustc-lesson" && e.state === "start");
      const sawRustcEnd = cancelled.some((e) => e.type === "progress" && e.stage === "rustc-lesson" && e.state === "end");
      checks.push({
        name: "cancel during rustc-lesson ends with cancelled, nothing after, replacement worker succeeds",
        pass: result.endedWithCancelled === true && result.eventsAfterCancelled === 0 && sawRustcStart && !sawRustcEnd &&
          recovery.verdict.ok && (result.workersAfter as number) === (result.workersBefore as number) + 1,
        detail: `cancel at ${Number(result.cancelIssuedAtMs).toFixed(0)} ms; workers ${result.workersBefore} -> ${result.workersAfter}; recovery ${recovery.verdict.ok}`,
      });
    }
    if (record.step === "supersede" && result) {
      const r = result as { first: { type: string }; second: { type: string; reason?: string }; third: { type: string } };
      checks.push({
        name: "a queued request superseded by a newer one ends cancelled/superseded; the others succeed",
        pass: r.first.type === "success" && r.second.type === "cancelled" && r.second.reason === "superseded" && r.third.type === "success",
        detail: JSON.stringify(result),
      });
    }
    lines.push(JSON.stringify({ browser, step: record.step, wallMs: record.wallMs, error: record.error, result: scrub(result) }));
  }
  writeFileSync(join(outDir, `${browser}-events.jsonl`), `${lines.join("\n")}\n`);
  const verdicts = { pass: checks.every((c) => c.pass), checks };
  writeFileSync(join(outDir, `${browser}-record.json`), `${JSON.stringify({ browser, verdicts, bundles, ...extra }, null, 1)}\n`);
  return verdicts;
}
