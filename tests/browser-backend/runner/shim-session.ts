// Compile and run steps under the vendored, IR-12-patched browser_wasi_shim,
// reusing the IR-15 worker's runCommand (byte-exact capture, trap and memory
// reporting) and VFS helpers. Used inside the browser executor worker.
//
// rustc.wasm VFS (one preopen per layer, as IR-15):
//   /sysroot  immutable  sysroot bundle (RIWB1), at the pack's sysroot mount
//   /pack     immutable  every pack artifact at its pack-relative path
//   /case     per step   the case sources
//   /out      per step   earlier outputs of the case; new outputs are read back
//   /tmp      per step   empty
// A case run sees one preopen "/" holding exactly the run's VFS files.

import { Directory, File, PreopenDirectory } from "../../../browser/worker/vendor/browser_wasi_shim/index.js";
import { parseSysrootBundle, preopen, readFile, readOnlyTree, type Tree } from "../../../browser/worker/src/vfs.ts";
import { runCommand, type CommandResult } from "../../../browser/worker/src/wasi.ts";
import type { RunRequest, RustcRequest, StepResult } from "./protocol.ts";

function strip(path: string, root: string): string {
  if (!path.startsWith(`${root}/`)) throw new Error(`${path} is not under ${root}`);
  return path.slice(root.length + 1);
}

function toStep(run: CommandResult, outputs: Record<string, Uint8Array>): StepResult {
  return {
    status: run.trap !== null ? "trap" : "exit",
    exitCode: run.exitCode,
    trap: run.trap,
    trapName: run.trapName,
    stdout: run.stdout,
    stderr: run.stderr,
    outputs,
    ms: run.runMs,
    memoryBytes: run.memoryBytes,
  };
}

export class ShimSession {
  private readonly sysroot: Tree;
  private readonly pack: Tree;
  private readonly rustcModule: WebAssembly.Module;
  private readonly sysrootMount: string;

  constructor(rustcModule: WebAssembly.Module, bundle: Uint8Array, packFiles: Record<string, Uint8Array>, sysrootMount: string) {
    this.rustcModule = rustcModule;
    this.sysrootMount = sysrootMount;
    this.sysroot = readOnlyTree(parseSysrootBundle(bundle));
    this.pack = readOnlyTree(Object.entries(packFiles));
  }

  async rustc(request: RustcRequest): Promise<StepResult> {
    const caseFiles: Array<[string, Uint8Array]> = [];
    const out = new Directory([]);
    for (const [path, bytes] of Object.entries(request.files)) {
      if (path.startsWith("/case/")) caseFiles.push([strip(path, "/case"), bytes]);
      else if (path.startsWith("/out/")) {
        const name = strip(path, "/out");
        if (name.includes("/")) throw new Error(`nested /out path ${path}`);
        out.contents.set(name, new File(bytes, { readonly: true }));
      } else throw new Error(`unexpected compile input ${path}`);
    }
    const preopens = [
      preopen(this.sysrootMount, this.sysroot),
      preopen("/pack", this.pack),
      preopen("/case", readOnlyTree(caseFiles)),
      new PreopenDirectory("/out", out.contents),
      new PreopenDirectory("/tmp", []),
    ];
    const run = await runCommand({ module: this.rustcModule, args: ["rustc", ...request.args], env: request.env, preopens });
    const outDir = preopens[3]!.dir;
    const outputs: Record<string, Uint8Array> = {};
    for (const path of request.outputs) {
      const bytes = readFile(outDir, strip(path, "/out"));
      if (bytes !== null) outputs[path] = bytes.slice();
    }
    return toStep(run, outputs);
  }

  async run(request: RunRequest): Promise<StepResult> {
    const module = await WebAssembly.compile(request.module as Uint8Array<ArrayBuffer>);
    const root = preopen("/", readOnlyTree(Object.entries(request.files).map(([path, bytes]) => [strip(path, ""), bytes])));
    const run = await runCommand({ module, args: request.args, env: request.env, preopens: [root] });
    return toStep(run, {});
  }
}
