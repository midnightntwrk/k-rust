// Backend suite page: loads suite.json and the dependency pack from local files,
// verifies every pack artifact and the pack_id, compiles rustc.wasm once, and
// runs the suite through an executor worker (browser_wasi_shim). A cancelled
// step terminates the worker; the next step starts a fresh one in the same page.
// The WebDriver/BiDi driver calls window.ir16.run(only) and reads the HostRecord.

import { ir14PackId, sha256Hex } from "../../../browser/worker/src/pack.ts";
import type { HostRecord, SuiteFile } from "../runner/protocol.ts";
import { runSuite } from "../runner/suite.ts";
import { WorkerClient, type Port, type WorkerReply } from "../runner/worker-client.ts";

declare global {
  interface Window {
    ir16Ready?: boolean;
    ir16Error?: string;
    ir16?: { run(only: string[]): Promise<string>; log: string[] };
  }
}

const status = document.getElementById("status")!;
const log: string[] = [];

async function fetchBytes(url: string): Promise<Uint8Array> {
  const response = await fetch(url);
  if (!response.ok) throw new Error(`${url}: HTTP ${response.status}`);
  return new Uint8Array(await response.arrayBuffer());
}

function spawnShimWorker(): Port {
  const worker = new Worker("./shim-worker.js", { type: "module" });
  return {
    post: (message) => worker.postMessage(message),
    onMessage: (listener) => worker.addEventListener("message", (event: MessageEvent<WorkerReply>) => listener(event.data)),
    onError: (listener) => worker.addEventListener("error", (event) => listener(event.message || event)),
    terminate: () => worker.terminate(),
  };
}

async function prepare() {
  const t0 = performance.now();
  const suite = (await (await fetch("./suite.json")).json()) as SuiteFile;
  const base = suite.pack.url_base ?? "assets/pack";
  const files: Record<string, Uint8Array> = {};
  let verified = 0;
  let rustcBytes: Uint8Array | null = null;
  let bundle: Uint8Array | null = null;
  await Promise.all(suite.pack.artifacts.map(async (artifact) => {
    const bytes = await fetchBytes(`./${base}/${artifact.path}`);
    if (bytes.byteLength !== artifact.bytes || (await sha256Hex(bytes)) !== artifact.sha256) {
      throw new Error(`pack artifact ${artifact.path} does not match the manifest`);
    }
    verified += 1;
    if (artifact.path === suite.pack.rustc_wasm.path) rustcBytes = bytes;
    else if (artifact.path === suite.pack.sysroot_bundle.path) bundle = bytes;
    else if (/^(deps|proc-macro-meta)\//.test(artifact.path)) files[artifact.path] = bytes;
  }));
  const packIdRecomputed = await ir14PackId(suite.pack.artifacts);
  if (packIdRecomputed !== suite.pack.pack_id) throw new Error(`pack_id ${suite.pack.pack_id} != ${packIdRecomputed}`);
  if (!rustcBytes || !bundle) throw new Error("the pack has no rustc.wasm or sysroot bundle");
  const compileStarted = performance.now();
  const rustc = await WebAssembly.compile(rustcBytes as Uint8Array<ArrayBuffer>);
  const rustcCompileMs = performance.now() - compileStarted;
  return {
    suite,
    rustc,
    bundle: bundle as Uint8Array,
    files,
    verified: {
      rustc_wasm_sha256: await sha256Hex(rustcBytes),
      sysroot_bundle_sha256: await sha256Hex(bundle),
      pack_id_recomputed: packIdRecomputed,
      artifacts_verified: verified,
    },
    timings: { prepareMs: performance.now() - t0, rustcCompileMs },
  };
}

const prepared = prepare();

window.ir16 = {
  log,
  async run(only: string[]): Promise<string> {
    const started = performance.now();
    const { suite, rustc, bundle, files, verified, timings } = await prepared;
    const client = new WorkerClient(spawnShimWorker, { rustc, bundle, pack: files, sysrootMount: suite.pack.sysroot_mount });
    let cases: HostRecord["cases"] = [];
    try {
      cases = await runSuite(suite, client, client, {
        only,
        log: (line) => {
          log.push(line);
          status.textContent = line;
        },
      });
    } finally {
      client.dispose();
    }
    const record: HostRecord = {
      schema: 1,
      host: "browser",
      compiler: "fork",
      environment: { userAgent: navigator.userAgent, hardwareConcurrency: navigator.hardwareConcurrency, wasi: "browser_wasi_shim (Weblings d0cd7a9f + path_readlink patch, browser/worker/vendor)", ...timings },
      pack_id: suite.pack.pack_id,
      verified,
      cases,
      executor_generations: client.generations(),
      wall_ms: performance.now() - started,
    };
    return JSON.stringify(record);
  },
};

prepared.then(
  () => {
    status.textContent = "ready";
    window.ir16Ready = true;
  },
  (error: unknown) => {
    window.ir16Error = String(error instanceof Error ? error.stack ?? error.message : error);
    status.textContent = `failed: ${window.ir16Error}`;
  },
);
