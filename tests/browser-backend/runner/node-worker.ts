// Node executor worker: runs rustc.wasm and case modules under node:wasi
// (WASI Preview 1), the independent WASI implementation of the suite, with
// every guest directory materialized in a per-step scratch directory.
//
// rustc.wasm preopens: /sysroot (the unpacked bundle), /pack (the IR-14 pack
// root, read only by convention), /case, /out, /tmp. A case run sees one
// preopen "/" holding exactly the run's VFS files.

import { closeSync, mkdirSync, mkdtempSync, openSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { WASI } from "node:wasi";
import { parentPort } from "node:worker_threads";
import type { RunRequest, RustcRequest, StepResult } from "./protocol.ts";
import type { WorkerReply, WorkerRequest } from "./worker-client.ts";

interface NodeInit {
  rustc: WebAssembly.Module | null;
  sysrootDir: string | null;
  packRoot: string | null;
  sysrootMount: string;
  scratch: string;
}

let init: NodeInit | null = null;

function writeTree(root: string, files: Record<string, Uint8Array>, prefix: string): void {
  for (const [path, bytes] of Object.entries(files)) {
    if (!path.startsWith(prefix)) continue;
    const target = join(root, path.slice(prefix.length));
    mkdirSync(dirname(target), { recursive: true });
    writeFileSync(target, bytes);
  }
}

async function execute(module: WebAssembly.Module, args: string[], env: string[], preopens: Record<string, string>, dir: string) {
  const stdoutPath = join(dir, ".stdout");
  const stderrPath = join(dir, ".stderr");
  const stdout = openSync(stdoutPath, "w");
  const stderr = openSync(stderrPath, "w");
  const stdin = openSync("/dev/null", "r");
  const wasi = new WASI({
    version: "preview1",
    args,
    env: Object.fromEntries(env.map((entry) => {
      const at = entry.indexOf("=");
      return [entry.slice(0, at), entry.slice(at + 1)];
    })),
    preopens,
    returnOnExit: true,
    stdin,
    stdout,
    stderr,
  });
  const instance = await WebAssembly.instantiate(module, { wasi_snapshot_preview1: wasi.wasiImport } as WebAssembly.Imports);
  let exitCode: number | null = null;
  let trap: string | null = null;
  let trapName: string | null = null;
  const started = performance.now();
  try {
    exitCode = wasi.start(instance);
  } catch (error) {
    trapName = error instanceof Error ? error.name : typeof error;
    trap = error instanceof Error ? `${error.name}: ${error.message}` : String(error);
  }
  const ms = performance.now() - started;
  closeSync(stdout);
  closeSync(stderr);
  closeSync(stdin);
  let memoryBytes: number | null = null;
  try {
    memoryBytes = (instance.exports.memory as WebAssembly.Memory).buffer.byteLength;
  } catch {
    memoryBytes = null;
  }
  return {
    status: trap !== null ? ("trap" as const) : ("exit" as const),
    exitCode,
    trap,
    trapName,
    stdout: new Uint8Array(readFileSync(stdoutPath)),
    stderr: new Uint8Array(readFileSync(stderrPath)),
    ms,
    memoryBytes,
  };
}

async function rustc(request: RustcRequest): Promise<StepResult> {
  if (!init?.rustc || !init.sysrootDir || !init.packRoot) throw new Error("this executor has no rustc.wasm");
  const dir = mkdtempSync(join(init.scratch, "rustc-"));
  try {
    for (const name of ["case", "out", "tmp"]) mkdirSync(join(dir, name));
    writeTree(join(dir, "case"), request.files, "/case/");
    writeTree(join(dir, "out"), request.files, "/out/");
    const result = await execute(init.rustc, ["rustc", ...request.args], request.env, {
      [init.sysrootMount]: init.sysrootDir,
      "/pack": init.packRoot,
      "/case": join(dir, "case"),
      "/out": join(dir, "out"),
      "/tmp": join(dir, "tmp"),
    }, dir);
    const outputs: Record<string, Uint8Array> = {};
    for (const path of request.outputs) {
      try {
        outputs[path] = new Uint8Array(readFileSync(join(dir, "out", path.slice("/out/".length))));
      } catch {
        // absent output
      }
    }
    return { ...result, outputs };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

async function run(request: RunRequest): Promise<StepResult> {
  const dir = mkdtempSync(join(init!.scratch, "run-"));
  try {
    const root = join(dir, "root");
    mkdirSync(root);
    writeTree(root, request.files, "/");
    const module = await WebAssembly.compile(request.module as Uint8Array<ArrayBuffer>);
    const result = await execute(module, request.args, request.env, { "/": root }, dir);
    return { ...result, outputs: {} };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const port = parentPort!;
let queue: Promise<void> = Promise.resolve();
port.on("message", (message: WorkerRequest) => {
  queue = queue.then(async () => {
    const reply = (value: WorkerReply) => port.postMessage(value);
    try {
      if (message.type === "init") {
        init = message.init as NodeInit;
        mkdirSync(init.scratch, { recursive: true });
        reply({ type: "ready" });
      } else if (message.type === "rustc") {
        reply({ type: "result", id: message.id, result: await rustc(message.request) });
      } else {
        reply({ type: "result", id: message.id, result: await run(message.request) });
      }
    } catch (error) {
      reply({ type: "error", id: message.type === "init" ? null : message.id, message: String(error instanceof Error ? `${error.name}: ${error.message}` : error) });
    }
  });
});
