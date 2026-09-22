// Controller side of an executor worker (browser Worker or Node worker_threads):
// one step at a time, a timeout per step, and replacement of the worker when a
// step is cancelled (the only way to stop a spinning Wasm instance).

import type { Compiler, Executor, RunRequest, RustcRequest, StepResult } from "./protocol.ts";

export interface Port {
  post(message: unknown): void;
  onMessage(listener: (message: WorkerReply) => void): void;
  onError(listener: (error: unknown) => void): void;
  terminate(): void;
}

export type WorkerRequest =
  | { type: "init"; init: unknown }
  | { type: "rustc"; id: number; request: RustcRequest }
  | { type: "run"; id: number; request: RunRequest };

export type WorkerReply =
  | { type: "ready" }
  | { type: "result"; id: number; result: StepResult }
  | { type: "error"; id: number | null; message: string };

export class WorkerClient implements Compiler, Executor {
  readonly kind = "fork" as const;
  private port: Port | null = null;
  private ready: Promise<void> | null = null;
  private nextId = 0;
  private waiting = new Map<number, { resolve: (r: StepResult) => void; reject: (e: Error) => void }>();
  private created = 0;

  private readonly spawn: () => Port;
  private readonly init: unknown;

  constructor(spawn: () => Port, init: unknown) {
    this.spawn = spawn;
    this.init = init;
  }

  generations(): number {
    return this.created;
  }

  private start(): Promise<void> {
    const port = this.spawn();
    this.created += 1;
    this.port = port;
    this.ready = new Promise<void>((resolve, reject) => {
      port.onMessage((message) => {
        if (message.type === "ready") return resolve();
        if (message.type === "error" && message.id === null) return reject(new Error(message.message));
        if (message.type === "result" || message.type === "error") {
          const waiter = this.waiting.get(message.id!);
          if (!waiter) return;
          this.waiting.delete(message.id!);
          if (message.type === "result") waiter.resolve(message.result);
          else waiter.reject(new Error(message.message));
        }
      });
      port.onError((error) => {
        const failure = new Error(`executor worker error: ${String(error instanceof Error ? error.message : error)}`);
        reject(failure);
        for (const waiter of this.waiting.values()) waiter.reject(failure);
        this.waiting.clear();
      });
    });
    port.post({ type: "init", init: this.init } satisfies WorkerRequest);
    return this.ready;
  }

  async reset(): Promise<void> {
    this.port?.terminate();
    for (const waiter of this.waiting.values()) waiter.reject(new Error("executor reset"));
    this.waiting.clear();
    this.port = null;
    await this.start();
  }

  private async step(type: "rustc" | "run", request: RustcRequest | RunRequest): Promise<StepResult> {
    if (this.port === null) await this.start();
    await this.ready;
    const id = ++this.nextId;
    const started = performance.now();
    let timer: ReturnType<typeof setTimeout> | null = null;
    const result = new Promise<StepResult>((resolve, reject) => this.waiting.set(id, { resolve, reject }));
    const timeout = new Promise<"timeout">((resolve) => {
      timer = setTimeout(() => resolve("timeout"), request.timeoutMs);
    });
    this.port!.post({ type, id, request } as WorkerRequest);
    const winner = await Promise.race([result, timeout]);
    if (timer !== null) clearTimeout(timer);
    if (winner !== "timeout") return winner;
    this.waiting.delete(id);
    const ms = performance.now() - started;
    await this.reset();
    return { status: "cancelled", exitCode: null, trap: null, trapName: null, stdout: new Uint8Array(0), stderr: new Uint8Array(0), outputs: {}, ms, memoryBytes: null };
  }

  rustc(request: RustcRequest): Promise<StepResult> {
    return this.step("rustc", request);
  }

  run(request: RunRequest): Promise<StepResult> {
    return this.step("run", request);
  }

  dispose(): void {
    this.port?.terminate();
    this.port = null;
  }
}
