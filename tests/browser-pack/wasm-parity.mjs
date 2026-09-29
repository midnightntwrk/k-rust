// Compare recorded native protocol responses with the same requests sent to Wasm.
// usage: node wasm-parity.mjs MODULE.wasm PREFIX DIR
import { readFile, readdir } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { callBytes, loadModule, parseResponse } from "../../crates/krs-wasm-abi/abi.mjs";

const [modulePath, prefix, directory] = process.argv.slice(2);
if (!modulePath || !prefix || !directory || process.argv.length !== 5) {
  throw new Error("usage: node wasm-parity.mjs MODULE.wasm PREFIX DIR");
}

const names = (await readdir(directory))
  .filter((name) => name.endsWith(".request.json"))
  .sort();
if (names.length === 0) {
  throw new Error(`no parity cases in ${directory}`);
}

const exports = await loadModule(modulePath);
const failures = [];
for (const name of names) {
  const match = /^(.+)\.(run|lookup)\.request\.json$/.exec(name);
  if (!match) {
    failures.push(`${name}: expected CASE.ENTRY.request.json`);
    continue;
  }
  const [, caseName, entry] = match;
  const caseId = `${caseName}.${entry}`;
  try {
    const request = await readFile(path.join(directory, name));
    const expected = await readFile(path.join(directory, `${caseId}.response.json`));
    const actual = callBytes(exports, prefix, entry, request);
    parseResponse(actual);
    if (!Buffer.from(actual).equals(expected)) {
      failures.push(`${caseId}: Wasm response differs from native response`);
    }
  } catch (error) {
    failures.push(`${caseId}: ${error.message}`);
  }
}

if (failures.length > 0) {
  throw new Error(`Wasm parity failed:\n${failures.join("\n")}`);
}
console.log(`Wasm parity: ${names.length} cases passed`);
