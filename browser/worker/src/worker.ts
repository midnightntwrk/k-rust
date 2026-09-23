// Dedicated module worker entry: receives the verified assets once (or reads
// them from the page's asset store, asset-store.ts), then runs
// one build at a time and posts its events. The controller owns generations,
// queueing, and cancellation (Worker.terminate()).

import { readStoredAssets } from "./asset-store.ts";
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

scope.onmessage = (event) => {
  const message = event.data;
  if (message.type === "init") {
    if (message.protocol !== WORKER_PROTOCOL) {
      scope.postMessage({ type: "init-error", message: `worker protocol ${WORKER_PROTOCOL}, controller ${message.protocol}` });
      return;
    }
    try {
      context = createPipelineContext(message.pack, message.assets);
      scope.postMessage({ type: "ready", protocol: WORKER_PROTOCOL });
    } catch (error) {
      scope.postMessage({ type: "init-error", message: String(error instanceof Error ? error.message : error) });
    }
    return;
  }
  if (message.type === "init-stored") {
    if (message.protocol !== WORKER_PROTOCOL) {
      scope.postMessage({ type: "init-error", message: `worker protocol ${WORKER_PROTOCOL}, controller ${message.protocol}` });
      return;
    }
    readStoredAssets(message.pack, message.stored).then(
      (assets) => {
        context = createPipelineContext(message.pack, assets);
        scope.postMessage({ type: "ready", protocol: WORKER_PROTOCOL });
      },
      (error: unknown) => scope.postMessage({ type: "init-error", message: String(error instanceof Error ? error.message : error) }),
    );
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
