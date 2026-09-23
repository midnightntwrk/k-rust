// Test page for the compiler worker: loads the staged pack from ./assets/,
// verifies every hash, compiles the three modules once, and exposes
// window.ir15 for the WebDriver/BiDi drivers.

import { KrsCompiler, loadVerifiedAssets } from "../../src/controller.ts";
import type { CompileEvent, FaultInjection, LessonManifest, PackManifest } from "../../src/protocol.ts";
import { check, expectationFor, SCENARIOS } from "../scenarios.ts";

let compiler: KrsCompiler | null = null;
let lesson: LessonManifest | null = null;
let forkRevision = "";
const fixtures = new Map<string, string>();

function base64(bytes: Uint8Array): string {
  let binary = "";
  for (let i = 0; i < bytes.length; i += 0x8000) binary += String.fromCharCode(...bytes.subarray(i, i + 0x8000));
  return btoa(binary);
}

function heap(): Record<string, number> | null {
  const memory = (performance as unknown as { memory?: { usedJSHeapSize: number; totalJSHeapSize: number } }).memory;
  return memory ? { usedJSHeapSize: memory.usedJSHeapSize, totalJSHeapSize: memory.totalJSHeapSize } : null;
}

function resourceNames(): string[] {
  return performance.getEntriesByType("resource").map((entry) => entry.name);
}

/** JSON-safe copy of an event: bundle bytes become size + base64; bulky evidence text is dropped unless keepExpanded. */
function plain(event: CompileEvent, keepBundle: boolean, keepExpanded = false): unknown {
  const bulky = keepExpanded ? {} : { expandedText: undefined, sourceMap: undefined };
  if (event.type === "success") {
    const { bundle, evidence, ...rest } = event;
    return {
      ...rest,
      bundle: { bytes: bundle.byteLength, ...(keepBundle ? { base64: base64(bundle) } : {}) },
      ...(evidence ? { evidence: { ...evidence, ...bulky } } : {}),
    };
  }
  if (event.type === "failure" && event.evidence) {
    return { ...event, evidence: { ...event.evidence, ...bulky } };
  }
  return event;
}

function resourceEntries(from: number) {
  return performance.getEntriesByType("resource").slice(from).map((e) => {
    const r = e as PerformanceResourceTiming;
    return { name: r.name, startTime: r.startTime, durationMs: r.duration, transferSize: r.transferSize, decodedBodySize: r.decodedBodySize };
  });
}

async function collect(iterable: AsyncIterable<CompileEvent>, onEvent?: (event: CompileEvent) => void) {
  const events: Array<{ event: CompileEvent; atMs: number }> = [];
  const started = performance.now();
  for await (const event of iterable) {
    events.push({ event, atMs: performance.now() - started });
    onEvent?.(event);
  }
  return { events, wallMs: performance.now() - started };
}

async function init() {
  const t0 = performance.now();
  const pack = (await (await fetch("./assets/pack.json")).json()) as PackManifest;
  forkRevision = pack.fork_revision;
  lesson = (await (await fetch("./assets/lessons/tour-minimal/lesson.json")).json()) as LessonManifest;
  for (const scenario of SCENARIOS) {
    if (!fixtures.has(scenario.fixture)) fixtures.set(scenario.fixture, await (await fetch(`./fixtures/${scenario.fixture}`)).text());
  }
  const t1 = performance.now();
  const assets = await loadVerifiedAssets(pack, async (path) => {
    const response = await fetch(`./assets/${path}`);
    if (!response.ok) throw new Error(`fetch ${path}: ${response.status}`);
    return new Uint8Array(await response.arrayBuffer());
  });
  const t2 = performance.now();
  compiler = await KrsCompiler.create(pack, assets, {
    createWorker: () => new Worker(new URL("./worker.js", location.href), { type: "module" }),
  });
  const t3 = performance.now();
  return {
    userAgent: navigator.userAgent,
    hardwareConcurrency: navigator.hardwareConcurrency,
    packId: pack.pack_id,
    fetchManifestsMs: t1 - t0,
    loadVerifyCompileMs: t2 - t1,
    workerReadyMs: t3 - t2,
    heap: heap(),
    resources: performance.getEntriesByType("resource").map((e) => {
      const r = e as PerformanceResourceTiming;
      return { name: r.name, durationMs: r.duration, transferSize: r.transferSize, decodedBodySize: r.decodedBodySize };
    }),
  };
}

async function run(name: string, options: { debugEvidence?: boolean; keepBundle?: boolean } = {}) {
  const scenario = SCENARIOS.find((s) => s.name === name);
  if (!scenario || !compiler || !lesson) throw new Error(`unknown scenario ${name} or not initialized`);
  const resourcesBefore = resourceNames().length;
  const heapBefore = heap();
  const { events, wallMs } = await collect(
    compiler.compile({ lesson, files: { "src/lib.rs": fixtures.get(scenario.fixture)! }, debugEvidence: options.debugEvidence ?? true }),
  );
  const verdict = check(expectationFor(scenario, forkRevision), events.map((e) => e.event));
  return {
    scenario: name,
    wallMs,
    verdict,
    requestsDuringBuild: resourceNames().slice(resourcesBefore),
    heapBefore,
    heapAfter: heap(),
    workersStarted: compiler.workersStarted,
    events: events.map(({ event, atMs }) => ({ atMs, ...(plain(event, options.keepBundle ?? event.type === "success") as object) })),
  };
}

/**
 * Compiles caller-supplied source (the parity gate's edit round trip, the diagnostic cases) in the
 * current page session. `lesson` defaults to the staged tour-minimal manifest;
 * a caller may pass another manifest for the same pack (the diagnostic packages).
 */
async function runSource(options: {
  label: string;
  source: string;
  lesson?: LessonManifest;
  debugEvidence?: boolean;
  keepBundle?: boolean;
  keepExpanded?: boolean;
  faultInjection?: FaultInjection;
}) {
  const target = options.lesson ?? lesson;
  if (!compiler || !target) throw new Error("not initialized");
  const resourcesBefore = resourceNames().length;
  const heapBefore = heap();
  const { events, wallMs } = await collect(
    compiler.compile({
      lesson: target,
      files: { [target.display_file]: options.source },
      debugEvidence: options.debugEvidence ?? true,
      ...(options.faultInjection ? { faultInjection: options.faultInjection } : {}),
    }),
  );
  return {
    label: options.label,
    lesson: target.lesson,
    wallMs,
    requestsDuringBuild: resourceNames().slice(resourcesBefore),
    resourceTiming: resourceEntries(resourcesBefore),
    heapBefore,
    heapAfter: heap(),
    workersStarted: compiler.workersStarted,
    events: events.map(({ event, atMs }) => ({
      atMs,
      ...(plain(event, options.keepBundle ?? event.type === "success", options.keepExpanded ?? false) as object),
    })),
  };
}

/** The staged tour-minimal source and manifest (the parity gate applies edit E1 to this text). */
function lessonSource() {
  if (!lesson) throw new Error("not initialized");
  return { lesson, source: fixtures.get("tour-minimal.rs")! };
}

/** Cancel while rustc-lesson runs, then build again in the replacement worker. */
async function cancelDuringRustcLesson(delayMs = 100) {
  if (!compiler || !lesson) throw new Error("not initialized");
  const c = compiler;
  const workersBefore = c.workersStarted;
  let cancelIssuedAtMs: number | null = null;
  const started = performance.now();
  const { events } = await collect(c.compile({ lesson, files: { "src/lib.rs": fixtures.get("tour-minimal.rs")! } }), (event) => {
    if (event.type === "progress" && event.stage === "rustc-lesson" && event.state === "start") {
      setTimeout(() => {
        cancelIssuedAtMs = performance.now() - started;
        c.cancel();
      }, delayMs);
    }
  });
  // Give a terminated worker's in-flight messages time to (not) arrive.
  await new Promise((resolve) => setTimeout(resolve, 500));
  const lastEvent = events.at(-1)?.event;
  const recovery = await run("tour-minimal", { debugEvidence: false, keepBundle: false });
  return {
    cancelIssuedAtMs,
    events: events.map(({ event, atMs }) => ({ atMs, ...(plain(event, false) as object) })),
    endedWithCancelled: lastEvent?.type === "cancelled",
    eventsAfterCancelled: events.findIndex((e) => e.event.type === "cancelled") === events.length - 1 ? 0 : -1,
    workersBefore,
    workersAfter: c.workersStarted,
    recovery,
  };
}

/** Three compiles in quick succession: the second is superseded while queued. */
async function supersede() {
  if (!compiler || !lesson) throw new Error("not initialized");
  const files = { "src/lib.rs": fixtures.get("tour-minimal.rs")! };
  const [a, b, c] = await Promise.all([
    collect(compiler.compile({ lesson, files })),
    collect(compiler.compile({ lesson, files: { "src/lib.rs": fixtures.get("policy-d007.rs")! } })),
    collect(compiler.compile({ lesson, files })),
  ]);
  const terminal = (r: typeof a) => {
    const e = r.events.at(-1)?.event;
    return e ? { type: e.type, generation: e.generation, ...(e.type === "cancelled" ? { reason: e.reason } : {}), ...(e.type === "success" ? { bundleSha256: e.bundleSha256 } : {}) } : null;
  };
  return { first: terminal(a), second: terminal(b), third: terminal(c), secondEventCount: b.events.length };
}

(globalThis as unknown as { ir15: unknown }).ir15 = {
  init,
  run,
  runSource,
  lessonSource,
  cancelDuringRustcLesson,
  supersede,
  scenarios: SCENARIOS.map((s) => s.name),
};
(globalThis as unknown as { ir15Ready: boolean }).ir15Ready = true;
document.getElementById("status")!.textContent = "ready: call window.ir15.init()";
