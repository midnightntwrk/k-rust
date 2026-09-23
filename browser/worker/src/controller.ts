// Page-side controller: owns the worker, generations, queueing, and
// cancellation. docs-site imports this module and protocol.ts only.
//
// - One build runs per worker. A compile() while one runs is queued; a newer
//   compile() supersedes the queued one, which ends with `cancelled`
//   (reason "superseded").
// - cancel() terminates the worker, ends the running and queued generations
//   with `cancelled` (reason "cancel"), and starts a fresh worker from the same
//   verified assets. Nothing is transferred from the terminated worker, and no
//   event of a cancelled generation is delivered after `cancelled`.
// - A build that ends with a genuine trap (compiler-trap, collector-trap,
//   out-of-memory) replaces the worker before the next build.

import {
  type CompileEvent,
  type CompileRequest,
  type FromWorker,
  type PackManifest,
  type StoredAssets,
  type ToWorker,
  type VerifiedAssets,
  WORKER_PROTOCOL,
} from "./protocol.ts";

/** The asset loader (hash verification + one module compile per page), re-exported for docs-site. */
export { loadVerifiedAssets, PackIntegrityError } from "./pack.ts";
/** The release cache (IR-21); PackCache.storedAssets lets workers read verified assets themselves (IR-20). */
export {
  type CacheEvent,
  InstalledRelease,
  PackCache,
  PackCacheError,
  packFailureEvent,
  type ReleasePreview,
} from "./pack-cache.ts";

export interface KrsCompilerOptions {
  /** Creates the module worker (the bundle location differs between hosts). */
  createWorker: () => Worker;
  /**
   * Web Locks lease each worker holds (shared) for its lifetime, e.g.
   * InstalledRelease.lease: PackCache.cleanup() never deletes the namespace of
   * a pack while a worker built from it is alive (IR-21).
   */
  lease?: string;
}

/** Push-based async iterable with an explicit end. */
class EventChannel implements AsyncIterable<CompileEvent> {
  private buffer: CompileEvent[] = [];
  private waiting: ((result: IteratorResult<CompileEvent>) => void) | null = null;
  closed = false;

  push(event: CompileEvent): void {
    if (this.closed) return;
    if (this.waiting) {
      const resolve = this.waiting;
      this.waiting = null;
      resolve({ value: event, done: false });
    } else {
      this.buffer.push(event);
    }
  }

  close(): void {
    if (this.closed) return;
    this.closed = true;
    if (this.waiting) {
      const resolve = this.waiting;
      this.waiting = null;
      resolve({ value: undefined, done: true });
    }
  }

  [Symbol.asyncIterator](): AsyncIterator<CompileEvent> {
    return {
      next: () => {
        const event = this.buffer.shift();
        if (event !== undefined) return Promise.resolve({ value: event, done: false });
        if (this.closed) return Promise.resolve({ value: undefined, done: true });
        return new Promise((resolve) => {
          this.waiting = resolve;
        });
      },
    };
  }
}

interface Job {
  request: CompileRequest;
  channel: EventChannel;
}

interface WorkerSlot {
  worker: Worker;
  ready: Promise<void>;
}

export class KrsCompiler {
  private readonly pack: PackManifest;
  private readonly assets: VerifiedAssets | StoredAssets;
  private readonly options: KrsCompilerOptions;
  private slot: WorkerSlot;
  private generation = 0;
  private running: Job | null = null;
  private queued: Job | null = null;
  private disposed = false;
  /** Number of workers started (1 + replacements); observable for tests. */
  workersStarted = 0;

  private constructor(pack: PackManifest, assets: VerifiedAssets | StoredAssets, options: KrsCompilerOptions) {
    this.pack = pack;
    this.assets = assets;
    this.options = options;
    this.slot = this.spawn();
  }

  /**
   * `assets` is either the verified bytes (cloned into every worker) or a
   * StoredAssets description (each worker reads and verifies the bytes from
   * the store; only the compiled modules are cloned).
   */
  static async create(pack: PackManifest, assets: VerifiedAssets | StoredAssets, options: KrsCompilerOptions): Promise<KrsCompiler> {
    const compiler = new KrsCompiler(pack, assets, options);
    await compiler.slot.ready;
    return compiler;
  }

  private spawn(): WorkerSlot {
    this.workersStarted += 1;
    const worker = this.options.createWorker();
    const ready = new Promise<void>((resolve, reject) => {
      worker.onmessage = (event: MessageEvent<FromWorker>) => {
        const message = event.data;
        if (message.type === "ready") resolve();
        else if (message.type === "init-error") reject(new Error(message.message));
        else if (this.slot?.worker === worker) this.onWorkerMessage(message);
      };
      worker.onerror = (event) => {
        const text = (event as ErrorEvent).message ?? "worker error";
        reject(new Error(text));
        if (this.slot?.worker === worker) this.onWorkerCrash(text);
      };
    });
    const lease = this.options.lease ? { lease: this.options.lease } : {};
    const init: ToWorker = "store" in this.assets
      ? { type: "init-stored", protocol: WORKER_PROTOCOL, pack: this.pack, stored: this.assets, ...lease }
      : { type: "init", protocol: WORKER_PROTOCOL, pack: this.pack, assets: this.assets, ...lease };
    worker.postMessage(init);
    return { worker, ready };
  }

  private replaceWorker(): void {
    this.slot.worker.terminate();
    this.slot = this.spawn();
  }

  private onWorkerMessage(message: FromWorker): void {
    const job = this.running;
    if (job === null) return;
    if (message.type === "event") {
      if (message.event.generation === job.request.generation) job.channel.push(message.event);
      return;
    }
    if (message.type === "done" && message.generation === job.request.generation) {
      job.channel.close();
      this.running = null;
      if (message.replaceWorker) this.replaceWorker();
      this.startNext();
    }
  }

  private onWorkerCrash(text: string): void {
    const job = this.running;
    if (job !== null) {
      job.channel.push({
        type: "failure",
        generation: job.request.generation,
        stage: "assets",
        code: "compiler-trap",
        message: `worker crashed: ${text}`,
        diagnostics: [],
      });
      job.channel.close();
      this.running = null;
    }
    this.replaceWorker();
    this.startNext();
  }

  private startNext(): void {
    if (this.running !== null || this.queued === null || this.disposed) return;
    const job = this.queued;
    this.queued = null;
    this.running = job;
    const slot = this.slot;
    slot.ready.then(
      () => {
        if (this.running === job && this.slot === slot) {
          const message: ToWorker = { type: "compile", request: job.request };
          slot.worker.postMessage(message);
        }
      },
      (error: unknown) => {
        if (this.running !== job) return;
        job.channel.push({
          type: "failure",
          generation: job.request.generation,
          stage: "assets",
          code: "pack-integrity",
          message: `worker did not initialize: ${String(error)}`,
          diagnostics: [],
        });
        job.channel.close();
        this.running = null;
      },
    );
  }

  compile(request: Omit<CompileRequest, "generation">): AsyncIterable<CompileEvent> {
    const channel = new EventChannel();
    const job: Job = { request: { ...request, generation: ++this.generation }, channel };
    if (this.disposed) {
      channel.push({ type: "cancelled", generation: job.request.generation, reason: "disposed" });
      channel.close();
      return channel;
    }
    if (this.queued !== null) {
      this.queued.channel.push({ type: "cancelled", generation: this.queued.request.generation, reason: "superseded" });
      this.queued.channel.close();
    }
    this.queued = job;
    this.startNext();
    return channel;
  }

  /** The generation most recently handed out. */
  get currentGeneration(): number {
    return this.generation;
  }

  private cancelAll(reason: "cancel" | "disposed"): void {
    for (const job of [this.running, this.queued]) {
      if (job === null) continue;
      job.channel.push({ type: "cancelled", generation: job.request.generation, reason });
      job.channel.close();
    }
    this.running = null;
    this.queued = null;
  }

  cancel(): void {
    if (this.disposed) return;
    const hadWork = this.running !== null || this.queued !== null;
    this.cancelAll("cancel");
    if (hadWork) this.replaceWorker();
  }

  dispose(): void {
    if (this.disposed) return;
    this.cancelAll("disposed");
    this.disposed = true;
    this.slot.worker.terminate();
  }
}
