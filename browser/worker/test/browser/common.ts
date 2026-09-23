// Shared parts of the headless browser drivers: a static server with a
// request log, a /proc process-tree memory sampler, and
// the scenario plan every browser runs in one page session.

import { readdirSync, readFileSync, realpathSync, statSync, writeFileSync, mkdirSync } from "node:fs";
import { extname, join, resolve } from "node:path";

const TYPES: Record<string, string> = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".map": "application/json",
  ".json": "application/json",
  ".wasm": "application/wasm",
  ".rs": "text/plain; charset=utf-8",
  ".toml": "text/plain; charset=utf-8",
};

export interface RequestLogEntry {
  atMs: number;
  method: string;
  path: string;
  status: number;
  bytes: number;
}

export function serveSite(dir: string, port: number) {
  const root = realpathSync(dir);
  const log: RequestLogEntry[] = [];
  const started = performance.now();
  const server = Bun.serve({
    hostname: "127.0.0.1",
    port,
    fetch(request) {
      const url = new URL(request.url);
      let path = decodeURIComponent(url.pathname);
      if (path.endsWith("/")) path += "index.html";
      const target = resolve(root, `.${path}`);
      let status = 404;
      let response: Response;
      try {
        const real = realpathSync(target);
        // The assets link points outside the site root; allow the site and the staged assets only.
        if (!real.startsWith(`${root}/`) && !real.startsWith(`${realpathSync(join(root, "assets"))}/`)) throw new Error("outside");
        if (!statSync(real).isFile()) throw new Error("not a file");
        const body = Bun.file(real);
        status = 200;
        response = new Response(body, { headers: { "content-type": TYPES[extname(real)] ?? "application/octet-stream", "cache-control": "no-store" } });
        log.push({ atMs: performance.now() - started, method: request.method, path, status, bytes: body.size });
        return response;
      } catch {
        log.push({ atMs: performance.now() - started, method: request.method, path, status, bytes: 0 });
        return new Response("not found", { status });
      }
    },
  });
  return { server, log, origin: `http://127.0.0.1:${port}` };
}

// ---------------------------------------------------------------- memory

interface ProcStatus {
  pid: number;
  ppid: number;
  name: string | null;
  rssKb: number;
}

function procStatus(pid: number): ProcStatus | null {
  try {
    const text = readFileSync(`/proc/${pid}/status`, "utf8");
    const field = (name: string) => new RegExp(`^${name}:\\s+(.+)$`, "m").exec(text)?.[1] ?? null;
    return { pid, ppid: Number(field("PPid")), name: field("Name"), rssKb: Number(/^\d+/.exec(field("VmRSS") ?? "0")?.[0] ?? 0) };
  } catch {
    return null;
  }
}

function tree(rootPid: number): ProcStatus[] {
  const all = readdirSync("/proc").filter((n) => /^\d+$/.test(n)).map((n) => procStatus(Number(n))).filter((s): s is ProcStatus => s !== null);
  const selected = new Set([rootPid]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const s of all) if (!selected.has(s.pid) && selected.has(s.ppid)) { selected.add(s.pid); changed = true; }
  }
  return all.filter((s) => selected.has(s.pid));
}

function pssKb(pid: number): number {
  try {
    return Number(/^Pss:\s+(\d+) kB$/m.exec(readFileSync(`/proc/${pid}/smaps_rollup`, "utf8"))?.[1] ?? 0);
  } catch {
    return 0;
  }
}

export interface MemoryPoint {
  atMs: number;
  phase: string;
  processes: number;
  rssKb: number;
  pssKb: number;
  top: Array<{ pid: number; name: string | null; pssKb: number }>;
}

export class TreeSampler {
  phase = "setup";
  samples: MemoryPoint[] = [];
  private timer: ReturnType<typeof setInterval> | null = null;
  private readonly started = performance.now();
  constructor(private readonly rootPid: () => number | null) {}
  start(intervalMs = 100) {
    this.timer = setInterval(() => {
      const pid = this.rootPid();
      if (pid === null) return;
      const procs = tree(pid).map((p) => ({ ...p, pssKb: pssKb(p.pid) }));
      this.samples.push({
        atMs: performance.now() - this.started,
        phase: this.phase,
        processes: procs.length,
        rssKb: procs.reduce((s, p) => s + p.rssKb, 0),
        pssKb: procs.reduce((s, p) => s + p.pssKb, 0),
        top: procs.sort((a, b) => b.pssKb - a.pssKb).slice(0, 3).map(({ pid, name, pssKb }) => ({ pid, name, pssKb })),
      });
    }, intervalMs);
  }
  stop() {
    if (this.timer) clearInterval(this.timer);
  }
  summary() {
    const peak = (field: "pssKb" | "rssKb") => this.samples.reduce<MemoryPoint | null>((best, s) => (best === null || s[field] > best[field] ? s : best), null);
    const byPhase: Record<string, { peakPssKb: number; peakRssKb: number; samples: number }> = {};
    for (const s of this.samples) {
      const p = (byPhase[s.phase] ??= { peakPssKb: 0, peakRssKb: 0, samples: 0 });
      p.peakPssKb = Math.max(p.peakPssKb, s.pssKb);
      p.peakRssKb = Math.max(p.peakRssKb, s.rssKb);
      p.samples += 1;
    }
    return {
      method: "100 ms samples of /proc/<pid>/smaps_rollup Pss and VmRSS over the browser process tree; RSS double-counts shared pages",
      sampleCount: this.samples.length,
      peakPss: peak("pssKb"),
      peakRss: peak("rssKb"),
      byPhase,
    };
  }
}

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
