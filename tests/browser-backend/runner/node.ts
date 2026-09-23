// Node host of the suite (run with Node >= 24, type stripping):
//
//   node runner/node.ts --suite FILE --out FILE --compiler fork|twin|stable
//        [--only ID,ID] [--scratch DIR] [--twin RUSTC] [--wasm-ld PATH] [--stable-deps DIR]
//
// fork:   rustc.wasm from the dependency pack under node:wasi, in a worker thread
// twin:   the native twin (x86_64 host, same fork commit, LLVM) with the pack's rlibs
// stable: rustc +stable with rlibs built by cargo +stable (second reference)
// Every case module runs under node:wasi in a worker thread; a timed-out run
// terminates that worker and the next step starts a fresh one.

import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { parseArgs } from "node:util";
import { Worker } from "node:worker_threads";
import { computePackId, sha256Hex } from "../../../browser/worker/src/pack.ts";
import { parseSysrootBundle } from "../../../browser/worker/src/vfs.ts";
import type { Compiler, HostRecord, RustcRequest, StepResult, SuiteFile } from "./protocol.ts";
import { runSuite } from "./suite.ts";
import { WorkerClient, type Port, type WorkerReply } from "./worker-client.ts";

const { values } = parseArgs({
  options: {
    suite: { type: "string" },
    out: { type: "string" },
    compiler: { type: "string", default: "fork" },
    only: { type: "string", default: "" },
    scratch: { type: "string", default: "/var/tmp/krs-backend-node" },
    twin: { type: "string", default: "/var/tmp/krs-browser-fork/R-k/build/x86_64-unknown-linux-gnu/stage1/bin/rustc" },
    "wasm-ld": { type: "string", default: "" },
    "stable-deps": { type: "string", default: "" },
  },
});
if (!values.suite || !values.out) throw new Error("usage: node runner/node.ts --suite FILE --out FILE --compiler fork|twin|stable");
const kind = values.compiler as "fork" | "twin" | "stable";
if (!["fork", "twin", "stable"].includes(kind)) throw new Error(`unknown compiler ${kind}`);
const suite = JSON.parse(readFileSync(values.suite, "utf8")) as SuiteFile;
const scratch = resolve(values.scratch!);
mkdirSync(scratch, { recursive: true });
const started = performance.now();
const log = (line: string) => process.stderr.write(`[node ${kind}] ${line}\n`);

// ---------------------------------------------------------------- pack verification

const packRoot = suite.pack.root;
const readPack = (path: string) => new Uint8Array(readFileSync(join(packRoot, path)));
let verifiedArtifacts = 0;
for (const artifact of suite.pack.artifacts) {
  const bytes = readPack(artifact.path);
  const digest = await sha256Hex(bytes);
  if (bytes.byteLength !== artifact.bytes || digest !== artifact.sha256) throw new Error(`pack artifact ${artifact.path} does not match the manifest`);
  verifiedArtifacts += 1;
}
const packIdRecomputed = await computePackId(suite.pack.artifacts);
if (packIdRecomputed !== suite.pack.pack_id) throw new Error(`pack_id ${suite.pack.pack_id} != recomputed ${packIdRecomputed}`);

// ---------------------------------------------------------------- executor

function spawnNodeWorker(): Port {
  const worker = new Worker(new URL("./node-worker.ts", import.meta.url));
  return {
    post: (message) => worker.postMessage(message),
    onMessage: (listener) => worker.on("message", (message: WorkerReply) => listener(message)),
    onError: (listener) => worker.on("error", listener),
    terminate: () => void worker.terminate(),
  };
}

let rustcModule: WebAssembly.Module | null = null;
let sysrootDir: string | null = null;
let rustcSha256: string | null = null;
let bundleSha256: string | null = null;
if (kind === "fork") {
  const rustcBytes = readPack(suite.pack.rustc_wasm.path);
  rustcSha256 = await sha256Hex(rustcBytes);
  if (rustcSha256 !== suite.pack.rustc_wasm.sha256) throw new Error("rustc.wasm hash mismatch");
  const bundle = readPack(suite.pack.sysroot_bundle.path);
  bundleSha256 = await sha256Hex(bundle);
  if (bundleSha256 !== suite.pack.sysroot_bundle.sha256) throw new Error("sysroot bundle hash mismatch");
  sysrootDir = join(scratch, `sysroot-${bundleSha256.slice(0, 16)}`);
  if (!existsSync(join(sysrootDir, ".complete"))) {
    rmSync(sysrootDir, { recursive: true, force: true });
    for (const [path, bytes] of parseSysrootBundle(bundle)) {
      mkdirSync(dirname(join(sysrootDir, path)), { recursive: true });
      writeFileSync(join(sysrootDir, path), bytes);
    }
    writeFileSync(join(sysrootDir, ".complete"), `${bundleSha256}\n`);
  }
  rustcModule = await WebAssembly.compile(rustcBytes as Uint8Array<ArrayBuffer>);
}

const client = new WorkerClient(spawnNodeWorker, {
  rustc: rustcModule,
  sysrootDir,
  packRoot,
  sysrootMount: suite.pack.sysroot_mount,
  scratch: join(scratch, `steps-${process.pid}`),
});

// ---------------------------------------------------------------- native reference compilers

class NativeCompiler implements Compiler {
  private readonly stableDeps = new Map<string, string>();
  readonly kind: "twin" | "stable";
  constructor(kind: "twin" | "stable") {
    this.kind = kind;
    if (kind === "stable" && values["stable-deps"]) {
      for (const name of readdirSync(values["stable-deps"]!)) {
        const match = /^lib(.+)-[0-9a-f]+\.rlib$/.exec(name);
        if (match) this.stableDeps.set(match[1]!, join(values["stable-deps"]!, name));
      }
    }
  }

  async rustc(request: RustcRequest): Promise<StepResult> {
    const dir = mkdtempSync(join(scratch, `${this.kind}-`));
    try {
      for (const [path, bytes] of Object.entries(request.files)) {
        const target = join(dir, path);
        mkdirSync(dirname(target), { recursive: true });
        writeFileSync(target, bytes);
      }
      mkdirSync(join(dir, "out"), { recursive: true });
      const args = request.args.map((arg) => this.translate(arg, dir));
      const binary = args.includes("bin");
      const extra: string[] = [`--remap-path-prefix=${dir}/case=/case`, `--remap-path-prefix=${dir}/out=/out`];
      let command: string;
      if (this.kind === "twin") {
        command = values.twin!;
        extra.push("-Zproc-macro-metadata-only", "-L", `dependency=${packRoot}/deps`, "-L", `dependency=${packRoot}/proc-macro-meta`);
        if (binary) {
          if (!values["wasm-ld"]) throw new Error("--wasm-ld is required for the twin");
          extra.push("-C", `linker=${values["wasm-ld"]}`);
        }
      } else {
        command = "rustc";
        if (values["stable-deps"]) extra.push("-L", `dependency=${values["stable-deps"]}`);
      }
      const env: Record<string, string> = { LANG: "C" };
      for (const name of ["PATH", "HOME", "RUSTUP_HOME", "CARGO_HOME"]) if (process.env[name]) env[name] = process.env[name]!;
      const t0 = performance.now();
      const argv = this.kind === "stable" ? ["+stable", ...args, ...extra] : [...args, ...extra];
      const child = spawnSync(command, argv, { env, cwd: dir, timeout: request.timeoutMs, maxBuffer: 256 * 1024 * 1024 });
      const ms = performance.now() - t0;
      const outputs: Record<string, Uint8Array> = {};
      for (const path of request.outputs) {
        const file = join(dir, path);
        if (existsSync(file)) outputs[path] = new Uint8Array(readFileSync(file));
      }
      const cancelled = child.error !== undefined && /ETIMEDOUT/.test(String(child.error));
      return {
        status: cancelled ? "cancelled" : child.signal ? "trap" : "exit",
        exitCode: child.status,
        trap: child.signal ? `signal ${child.signal}` : null,
        trapName: child.signal,
        stdout: new Uint8Array(child.stdout ?? new Uint8Array(0)),
        stderr: new Uint8Array(child.stderr ?? new Uint8Array(0)),
        outputs,
        ms,
        memoryBytes: null,
      };
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }

  private translate(arg: string, dir: string): string {
    const pack = /^([A-Za-z0-9_]+)=\/pack\/(.+)$/.exec(arg);
    if (pack) {
      if (this.kind === "twin") return `${pack[1]}=${packRoot}/${pack[2]}`;
      const own = this.stableDeps.get(pack[1]!);
      if (!own) throw new Error(`stable reference has no rlib for ${pack[1]} (build it with cargo +stable; see verify.py)`);
      return `${pack[1]}=${own}`;
    }
    return arg
      .replace(/^\/case\//, `${dir}/case/`)
      .replace(/^([A-Za-z0-9_]+)=\/out\//, `$1=${dir}/out/`)
      .replace(/^dependency=\/out$/, `dependency=${dir}/out`)
      .replace(/^\/out\//, `${dir}/out/`);
  }
}

const compiler: Compiler = kind === "fork" ? client : new NativeCompiler(kind);
const nativeVersion = kind === "fork"
  ? null
  : spawnSync(kind === "twin" ? values.twin! : "rustc", kind === "twin" ? ["-vV"] : ["+stable", "-vV"], { encoding: "utf8" }).stdout.trim().split("\n");

let cases: HostRecord["cases"] = [];
try {
  cases = await runSuite(suite, compiler, client, { only: values.only ? values.only.split(",") : [], log });
} finally {
  client.dispose();
  rmSync(join(scratch, `steps-${process.pid}`), { recursive: true, force: true });
}

const record: HostRecord = {
  schema: 1,
  host: kind === "fork" ? "node" : `node-${kind}-reference`,
  compiler: kind,
  environment: {
    node: process.version,
    platform: `${process.platform} ${process.arch}`,
    wasi: "node:wasi preview1",
    native_rustc_vv: nativeVersion,
    wasm_ld: kind === "twin" ? values["wasm-ld"] : null,
    stable_deps: kind === "stable" ? values["stable-deps"] : null,
  },
  pack_id: suite.pack.pack_id,
  verified: { rustc_wasm_sha256: rustcSha256, sysroot_bundle_sha256: bundleSha256, pack_id_recomputed: packIdRecomputed, artifacts_verified: verifiedArtifacts },
  cases,
  executor_generations: client.generations(),
  wall_ms: performance.now() - started,
};
mkdirSync(dirname(resolve(values.out!)), { recursive: true });
writeFileSync(values.out!, `${JSON.stringify(record, null, 1)}\n`);
log(`wrote ${values.out} (${cases.length} cases, ${(record.wall_ms / 1000).toFixed(1)} s)`);
process.exit(0);
