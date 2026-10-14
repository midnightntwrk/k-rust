// Node host side of the krs-wasm-abi JSON-over-linear-memory ABI:
// `<prefix>_alloc(len) -> ptr`, `<prefix>_<entry>(ptr, len) -> u64`
// (response_len << 32 | response_ptr), `<prefix>_dealloc(ptr, len)`, and no
// imports. Used by `tests/browser-pack/wasm-parity.mjs`; the browser worker's
// copy is `browser/worker/src/modules.ts`.
import { readFile } from "node:fs/promises";

// Compiles and instantiates the module at `path`, which must have no imports.
export async function loadModule(path) {
  const bytes = await readFile(path);
  const module = await WebAssembly.compile(bytes);
  const imports = WebAssembly.Module.imports(module);
  if (imports.length !== 0) {
    throw new Error(`module has imports: ${JSON.stringify(imports)}`);
  }
  const instance = await WebAssembly.instantiate(module, {});
  return instance.exports;
}

// Sends the request bytes to `<prefix>_<entry>` and returns a copy of the
// response bytes; both buffers are released.
export function callBytes(exports, prefix, entry, request) {
  const alloc = exports[`${prefix}_alloc`];
  const run = exports[`${prefix}_${entry}`];
  const dealloc = exports[`${prefix}_dealloc`];
  if (typeof alloc !== "function" || typeof run !== "function" || typeof dealloc !== "function") {
    throw new Error(`module lacks the ${prefix}_{alloc,${entry},dealloc} ABI`);
  }
  const requestPtr = alloc(request.length);
  new Uint8Array(exports.memory.buffer, requestPtr, request.length).set(request);
  const packed = run(requestPtr, request.length);
  const responsePtr = Number(packed & 0xffffffffn);
  const responseLen = Number(packed >> 32n);
  const response = new Uint8Array(exports.memory.buffer, responsePtr, responseLen).slice();
  dealloc(requestPtr, request.length);
  dealloc(responsePtr, responseLen);
  return response;
}

// Parses a schema-1 response and checks the fields every module returns.
export function parseResponse(bytes) {
  const text = new TextDecoder().decode(bytes);
  const parsed = JSON.parse(text);
  if (parsed.schema !== 1 || typeof parsed.ok !== "boolean" || !Array.isArray(parsed.diagnostics)) {
    throw new Error(`malformed response: ${text}`);
  }
  return parsed;
}
