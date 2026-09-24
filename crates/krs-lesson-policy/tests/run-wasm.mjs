// Runs the krs-lesson-policy Wasm module through its ABI
// (krs-wasm-abi/abi.mjs), with no dependencies and no imports.
//
// usage: node run-wasm.mjs MODULE.wasm FILE.rs [DISPLAY_FILE]
//
// Sends one schema-1 request whose only file is FILE.rs under DISPLAY_FILE
// (default src/lib.rs), with the tour-minimal policy, and prints the JSON
// response. Exits 0 when the response is well formed,
// whatever `ok` is.
import { readFile } from "node:fs/promises";
import process from "node:process";
import { callBytes, loadModule, parseResponse } from "../../krs-wasm-abi/abi.mjs";

const [modulePath, sourcePath, displayFile = "src/lib.rs"] = process.argv.slice(2);
if (!modulePath || !sourcePath) {
  throw new Error("usage: node run-wasm.mjs MODULE.wasm FILE.rs [DISPLAY_FILE]");
}

const { exports } = await loadModule(modulePath);
const request = new TextEncoder().encode(
  JSON.stringify({
    schema: 1,
    policy: { editable_files: ["src/lib.rs"], facade_alias: "k" },
    files: { [displayFile]: await readFile(sourcePath, "utf8") },
  }),
);
const parsed = parseResponse(callBytes(exports, "krs_lesson_policy", "run", request));
process.stdout.write(`${JSON.stringify(parsed)}\n`);
