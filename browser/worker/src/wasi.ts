// Runs one wasm32-wasip1 command module under the vendored browser_wasi_shim,
// with byte-exact stdout/stderr capture and trap reporting.

import { Fd, File, OpenFile, type PreopenDirectory, WASI } from "../vendor/browser_wasi_shim/index.js";

class Capture extends Fd {
  chunks: Uint8Array[] = [];
  length = 0;
  override fd_write(data: Uint8Array) {
    this.chunks.push(data.slice());
    this.length += data.byteLength;
    return { ret: 0, nwritten: data.byteLength };
  }
  bytes(): Uint8Array {
    const out = new Uint8Array(this.length);
    let at = 0;
    for (const chunk of this.chunks) {
      out.set(chunk, at);
      at += chunk.byteLength;
    }
    return out;
  }
}

export interface CommandResult {
  /** Exit status, or null when the instance trapped. */
  exitCode: number | null;
  /** Trap message (RuntimeError, RangeError, ...), or null. */
  trap: string | null;
  trapName: string | null;
  stdout: Uint8Array;
  stderr: Uint8Array;
  instantiateMs: number;
  runMs: number;
  /** Linear memory size at exit (bytes), when readable. */
  memoryBytes: number | null;
}

export interface CommandOptions {
  module: WebAssembly.Module;
  args: string[];
  env: string[];
  preopens: PreopenDirectory[];
}

export async function runCommand(options: CommandOptions): Promise<CommandResult> {
  for (const text of [...options.args, ...options.env]) {
    // The shim sizes argv/environ buffers by UTF-16 length; non-ASCII would corrupt them.
    if (!/^[\x20-\x7e]*$/.test(text)) throw new Error(`non-ASCII WASI argument or variable: ${JSON.stringify(text)}`);
  }
  const stdout = new Capture();
  const stderr = new Capture();
  const stdin = new OpenFile(new File(new Uint8Array(0), { readonly: true }));
  const wasi = new WASI(options.args, options.env, [stdin, stdout, stderr, ...options.preopens], { debug: false });
  const instantiateStarted = performance.now();
  const instance = (await WebAssembly.instantiate(options.module, {
    wasi_snapshot_preview1: wasi.wasiImport as WebAssembly.ModuleImports,
  })) as WebAssembly.Instance;
  const instantiateMs = performance.now() - instantiateStarted;
  const exports = instance.exports as { memory: WebAssembly.Memory; _start: () => unknown };
  let exitCode: number | null = null;
  let trap: string | null = null;
  let trapName: string | null = null;
  const runStarted = performance.now();
  try {
    exitCode = wasi.start(instance as never);
  } catch (error) {
    trapName = error instanceof Error ? error.name : typeof error;
    trap = error instanceof Error ? `${error.name}: ${error.message}` : String(error);
  }
  const runMs = performance.now() - runStarted;
  let memoryBytes: number | null = null;
  try {
    memoryBytes = exports.memory.buffer.byteLength;
  } catch {
    memoryBytes = null;
  }
  return { exitCode, trap, trapName, stdout: stdout.bytes(), stderr: stderr.bytes(), instantiateMs, runMs, memoryBytes };
}
