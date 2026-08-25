import { resolve } from "node:path";
import { captureManifest } from "./capture.js";
import { compareBundles } from "./compare.js";
import { writeJson } from "./io.js";
import { runSmokeSuite } from "./smoke.js";

function usage(): string {
  return `Usage:
  bun run oracle capture <manifest.json> --out <new-directory>
  bun run oracle compare <left-bundle-or-directory> <right-bundle-or-directory> [--only <boundary,...>] [--report <file>] [--expect equal|different]
  bun run oracle smoke <suite.json> --out <new-directory>

Boundaries use <run-id>:<artifact-id>, for example full:definition-kore.
Capture and smoke refuse to overwrite existing directories.`;
}

function option(args: readonly string[], name: string): string | undefined {
  const index = args.indexOf(name);
  if (index === -1) return undefined;
  const value = args[index + 1];
  if (value === undefined || value.startsWith("--")) throw new Error(`${name} requires a value`);
  return value;
}

function requireOption(args: readonly string[], name: string): string {
  const value = option(args, name);
  if (value === undefined) throw new Error(`Missing required option ${name}`);
  return value;
}

async function main(args: readonly string[]): Promise<void> {
  const command = args[0];
  if (command === undefined || command === "help" || command === "--help" || command === "-h") {
    console.log(usage());
    return;
  }
  if (command === "capture") {
    const manifest = args[1];
    if (manifest === undefined) throw new Error("capture requires a manifest path");
    const bundle = await captureManifest(resolve(manifest), resolve(requireOption(args, "--out")));
    console.log(bundle);
    return;
  }
  if (command === "compare") {
    const left = args[1];
    const right = args[2];
    if (left === undefined || right === undefined) throw new Error("compare requires two bundle paths or directories");
    const only = option(args, "--only");
    const selected = only === undefined ? undefined : new Set(only.split(",").filter((item) => item.length > 0));
    const comparison = await compareBundles(left, right, selected);
    const report = option(args, "--report");
    if (report === undefined) console.log(JSON.stringify(comparison, null, 2));
    else await writeJson(resolve(report), comparison);
    const expectation = option(args, "--expect");
    if (expectation !== undefined && expectation !== "equal" && expectation !== "different") {
      throw new Error("--expect must be equal or different");
    }
    if (expectation === "equal" && !comparison.equal) throw new Error("Bundles differ but equality was expected");
    if (expectation === "different" && comparison.equal) throw new Error("Bundles are equal but a difference was expected");
    if (expectation === undefined && !comparison.equal) process.exitCode = 1;
    return;
  }
  if (command === "smoke") {
    const suite = args[1];
    if (suite === undefined) throw new Error("smoke requires a suite path");
    const report = await runSmokeSuite(resolve(suite), resolve(requireOption(args, "--out")));
    console.log(report);
    return;
  }
  throw new Error(`Unknown command: ${command}\n\n${usage()}`);
}

if (import.meta.main) {
  try {
    await main(Bun.argv.slice(2));
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error));
    process.exitCode = 2;
  }
}
