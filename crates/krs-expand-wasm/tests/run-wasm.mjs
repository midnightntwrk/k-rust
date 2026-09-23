// Runs the krs-expand-wasm module through its ABI, with no dependencies and
// no imports.
//
// usage: node run-wasm.mjs MODULE.wasm REQUEST.json [OUT.json] [REPEAT]
//
// Sends the request file's bytes unchanged to krs_expand_run (or, for a
// request with a "ranges" field, krs_expand_lookup) REPEAT times (default 1)
// on one instance, checks that every response is byte-identical,
// writes the response bytes unchanged to OUT.json (default: stdout), and
// prints timings and linear-memory sizes as JSON on stderr. The module must
// have no imports. Exits 0 when the response is well formed, whatever `ok`
// is.
import { readFile, writeFile } from "node:fs/promises";
import process from "node:process";

const [modulePath, requestPath, outPath, repeatText = "1"] = process.argv.slice(2);
if (!modulePath || !requestPath) {
  throw new Error("usage: node run-wasm.mjs MODULE.wasm REQUEST.json [OUT.json] [REPEAT]");
}
const repeat = Number.parseInt(repeatText, 10);
if (!(repeat >= 1)) {
  throw new Error(`REPEAT must be a positive integer, got ${repeatText}`);
}

const bytes = await readFile(modulePath);
const compileStarted = performance.now();
const module = await WebAssembly.compile(bytes);
const compileMs = performance.now() - compileStarted;
const imports = WebAssembly.Module.imports(module);
if (imports.length !== 0) {
  throw new Error(`module has imports: ${JSON.stringify(imports)}`);
}
const exports = WebAssembly.Module.exports(module).map((entry) => `${entry.kind}:${entry.name}`);
const instantiateStarted = performance.now();
const instance = await WebAssembly.instantiate(module, {});
const instantiateMs = performance.now() - instantiateStarted;
const api = instance.exports;

const request = await readFile(requestPath);
const entry = "ranges" in JSON.parse(new TextDecoder().decode(request))
  ? api.krs_expand_lookup
  : api.krs_expand_run;
const runOnce = () => {
  const started = performance.now();
  const requestPtr = api.krs_expand_alloc(request.length);
  new Uint8Array(api.memory.buffer, requestPtr, request.length).set(request);
  const packed = entry(requestPtr, request.length);
  const responsePtr = Number(packed & 0xffffffffn);
  const responseLen = Number(packed >> 32n);
  const response = new Uint8Array(api.memory.buffer, responsePtr, responseLen).slice();
  api.krs_expand_dealloc(requestPtr, request.length);
  api.krs_expand_dealloc(responsePtr, responseLen);
  return { response, ms: performance.now() - started };
};

const memoryBefore = api.memory.buffer.byteLength;
const runs = [];
let first;
for (let index = 0; index < repeat; index += 1) {
  const { response, ms } = runOnce();
  runs.push(ms);
  if (first === undefined) {
    first = response;
  } else if (Buffer.compare(Buffer.from(first), Buffer.from(response)) !== 0) {
    throw new Error(`run ${index} returned a different response`);
  }
}

const parsed = JSON.parse(new TextDecoder().decode(first));
if (parsed.schema !== 1 || typeof parsed.ok !== "boolean" || !Array.isArray(parsed.diagnostics)) {
  throw new Error("malformed response");
}
if (outPath) {
  await writeFile(outPath, first);
} else {
  process.stdout.write(first);
  process.stdout.write("\n");
}
const warm = runs.slice(1).sort((a, b) => a - b);
console.error(JSON.stringify({
  node: process.version,
  module_bytes: bytes.length,
  exports,
  imports: imports.length,
  compile_ms: compileMs,
  instantiate_ms: instantiateMs,
  first_run_ms: runs[0],
  warm_runs: warm.length,
  warm_median_ms: warm.length ? warm[Math.floor(warm.length / 2)] : null,
  warm_max_ms: warm.length ? warm[warm.length - 1] : null,
  memory_before: memoryBefore,
  memory_after: api.memory.buffer.byteLength,
  ok: parsed.ok,
  response_bytes: first.length,
}));
