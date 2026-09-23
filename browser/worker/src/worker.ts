// Dedicated module worker entry: receives the verified assets once (or reads
// them from the pack's Cache Storage namespace, pack-cache.ts), then runs
// one build at a time and posts its events. The controller owns generations,
// queueing, and cancellation (Worker.terminate()).

import { readStoredAssets } from "./pack-cache.ts";
import { createPipelineContext, type PipelineContext, runBuild } from "./pipeline.ts";
import { type FromWorker, type ToWorker, WORKER_PROTOCOL } from "./protocol.ts";

interface WorkerScope {
  onmessage: ((event: MessageEvent<ToWorker>) => void) | null;
  postMessage(message: FromWorker): void;
}
const scope = globalThis as unknown as WorkerScope;

let context: PipelineContext | null = null;
let busy = false;

/** Chromium exposes performance.memory in workers; other hosts return null. */
function memoryProbe(): Record<string, number> | null {
  const memory = (performance as unknown as { memory?: { usedJSHeapSize: number; totalJSHeapSize: number } }).memory;
  return memory ? { usedJSHeapSize: memory.usedJSHeapSize, totalJSHeapSize: memory.totalJSHeapSize } : null;
}

/**
 * Takes the pack lease (shared Web Lock, held until the worker is terminated)
 * when one is requested, then runs `start`. The lease is taken first so that
 * PackCache.cleanup() cannot delete a namespace the worker is about to read.
 */
function withLease(lease: string | undefined, start: () => Promise<void>): void {
  const fail = (error: unknown) =>
    scope.postMessage({ type: "init-error", message: String(error instanceof Error ? error.message : error) });
  const ready = () => scope.postMessage({ type: "ready", protocol: WORKER_PROTOCOL });
  if (lease === undefined) {
    start().then(ready, fail);
    return;
  }
  const locks = (globalThis.navigator as Navigator | undefined)?.locks;
  if (!locks) {
    fail(`lease ${lease} requested but Web Locks are unavailable`);
    return;
  }
  // Held until the worker is terminated; the browser releases a context's locks when it goes away.
  void locks.request(lease, { mode: "shared" }, () => {
    start().then(ready, fail);
    return new Promise<never>(() => {});
  });
}

scope.onmessage = (event) => {
  const message = event.data;
  if (message.type === "init" || message.type === "init-stored") {
    if (message.protocol !== WORKER_PROTOCOL) {
      scope.postMessage({ type: "init-error", message: `worker protocol ${WORKER_PROTOCOL}, controller ${message.protocol}` });
      return;
    }
    withLease(message.lease, async () => {
      const assets = message.type === "init" ? message.assets : await readStoredAssets(message.pack, message.stored);
      context = createPipelineContext(message.pack, assets);
    });
    return;
  }
  if (message.type === "compile") {
    const generation = message.request.generation;
    if (context === null || busy) {
      scope.postMessage({
        type: "event",
        event: {
          type: "failure",
          generation,
          stage: "assets",
          code: "protocol-mismatch",
          message: context === null ? "worker received a build before init" : "worker received a build while busy",
          diagnostics: [],
        },
      });
      scope.postMessage({ type: "done", generation, replaceWorker: context === null });
      return;
    }
    busy = true;
    void runBuild(context, message.request, {
      emit: (compileEvent) => scope.postMessage({ type: "event", event: compileEvent }),
      memory: memoryProbe,
    }).then(
      (result) => {
        busy = false;
        scope.postMessage({ type: "done", generation, replaceWorker: result.replaceWorker });
      },
      (error: unknown) => {
        busy = false;
        scope.postMessage({
          type: "event",
          event: { type: "failure", generation, stage: "assets", code: "compiler-trap", message: String(error), diagnostics: [] },
        });
        scope.postMessage({ type: "done", generation, replaceWorker: true });
      },
    );
  }
};
