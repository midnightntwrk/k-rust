// Runs the krs-lesson-policy Wasm module through its ABI, with no
// dependencies and no imports.
//
// usage: node run-wasm.mjs MODULE.wasm FILE.rs [DISPLAY_FILE] [VERSION]
//
// Sends one schema-1 request whose only file is FILE.rs under DISPLAY_FILE
// (default src/lib.rs), with the tour-minimal policy at VERSION (default 1),
// and prints the JSON response. Exits 0 when the response is well formed,
// whatever `ok` is.
import { readFile } from "node:fs/promises";
import process from "node:process";

const [modulePath, sourcePath, displayFile = "src/lib.rs", version = "1"] = process.argv.slice(2);
if (!modulePath || !sourcePath) {
  throw new Error("usage: node run-wasm.mjs MODULE.wasm FILE.rs [DISPLAY_FILE]");
}

const module = await WebAssembly.compile(await readFile(modulePath));
const imports = WebAssembly.Module.imports(module);
if (imports.length !== 0) {
  throw new Error(`module has imports: ${JSON.stringify(imports)}`);
}
const { exports } = await WebAssembly.instantiate(module, {});

const request = new TextEncoder().encode(
  JSON.stringify({
    schema: 1,
    policy: { version: Number(version), editable_files: ["src/lib.rs"], facade_alias: "k" },
    files: { [displayFile]: await readFile(sourcePath, "utf8") },
  }),
);
const requestPtr = exports.krs_lesson_policy_alloc(request.length);
new Uint8Array(exports.memory.buffer, requestPtr, request.length).set(request);
const packed = exports.krs_lesson_policy_run(requestPtr, request.length);
const responsePtr = Number(packed & 0xffffffffn);
const responseLen = Number(packed >> 32n);
const response = new TextDecoder().decode(
  new Uint8Array(exports.memory.buffer, responsePtr, responseLen).slice(),
);
exports.krs_lesson_policy_dealloc(requestPtr, request.length);
exports.krs_lesson_policy_dealloc(responsePtr, responseLen);

const parsed = JSON.parse(response);
if (parsed.schema !== 1 || typeof parsed.ok !== "boolean" || !Array.isArray(parsed.diagnostics)) {
  throw new Error(`malformed response: ${response}`);
}
process.stdout.write(`${JSON.stringify(parsed)}\n`);
