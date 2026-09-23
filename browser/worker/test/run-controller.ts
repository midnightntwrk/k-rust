// Drives KrsCompiler (controller + module worker) under Bun: a build, a
// cancellation during rustc-lesson, and a build in the replacement worker.
//
//   bun test/run-controller.ts [--assets DIR] [--out FILE.json]

import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseArgs } from "node:util";
import { KrsCompiler } from "../src/controller.ts";
import { loadVerifiedAssets } from "../src/pack.ts";
import type { CompileEvent, LessonManifest, PackManifest } from "../src/protocol.ts";
import { check, SCENARIOS } from "./scenarios.ts";

const { values } = parseArgs({ options: { assets: { type: "string", default: "/var/tmp/krs-ir15-assets" }, out: { type: "string" } } });
const dir = values.assets!;
const pack = JSON.parse(readFileSync(join(dir, "pack.json"), "utf8")) as PackManifest;
const lesson = JSON.parse(readFileSync(join(dir, "lessons/tour-minimal/lesson.json"), "utf8")) as LessonManifest;
const assets = await loadVerifiedAssets(pack, async (path) => new Uint8Array(readFileSync(join(dir, path))));
const source = readFileSync(join(import.meta.dir, "fixtures/tour-minimal.rs"), "utf8");
const expect = SCENARIOS.find((s) => s.name === "tour-minimal")!.expect;

const compiler = await KrsCompiler.create(pack, assets, {
  createWorker: () => new Worker(new URL("../src/worker.ts", import.meta.url).href, { type: "module" }),
});

async function drain(iterable: AsyncIterable<CompileEvent>, onEvent?: (e: CompileEvent) => void) {
  const events: CompileEvent[] = [];
  for await (const event of iterable) {
    events.push(event);
    onEvent?.(event);
  }
  return events;
}

const first = await drain(compiler.compile({ lesson, files: { "src/lib.rs": source } }));
const workersBefore = compiler.workersStarted;
const cancelled = await drain(compiler.compile({ lesson, files: { "src/lib.rs": source } }), (event) => {
  if (event.type === "progress" && event.stage === "rustc-lesson" && event.state === "start") setTimeout(() => compiler.cancel(), 100);
});
await Bun.sleep(300);
const recovery = await drain(compiler.compile({ lesson, files: { "src/lib.rs": source } }));
compiler.dispose();

const result = {
  host: `bun ${Bun.version}`,
  first: check(expect, first),
  firstSha256: first.at(-1)?.type === "success" ? (first.at(-1) as { bundleSha256: string }).bundleSha256 : null,
  cancelled: {
    last: cancelled.at(-1),
    sawRustcEnd: cancelled.some((e) => e.type === "progress" && e.stage === "rustc-lesson" && e.state === "end"),
  },
  workers: [workersBefore, compiler.workersStarted],
  recovery: check(expect, recovery),
};
const pass = result.first.ok && result.cancelled.last?.type === "cancelled" && !result.cancelled.sawRustcEnd &&
  result.recovery.ok && result.workers[1] === result.workers[0]! + 1;
if (values.out) writeFileSync(values.out, `${JSON.stringify({ pass, ...result }, null, 1)}\n`);
console.error(JSON.stringify({ pass, ...result }));
process.exit(pass ? 0 : 1);
