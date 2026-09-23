// IR-18 twin control helper: the worker's expand stage and rustc span mapping,
// run under Bun over the same expander module, so that a native-twin compile of
// the expanded text can be classified exactly as the worker classifies the
// rustc.wasm compile.
//
//   bun test/parity/expand-case.ts expand --expander M.wasm --lesson L.json --source F.rs --out DIR
//       [--fault registration-table-missing-factory]
//     writes DIR/expanded.rs, DIR/response.json (expander response; text replaced by the faulted text)
//   bun test/parity/expand-case.ts map --expander M.wasm --dir DIR --source F.rs --stderr twin.stderr
//     prints the worker Diagnostic list for the twin's JSON stderr (generated file = DIR/expanded.rs)

import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseArgs } from "node:util";
import { fromRustc, lookupRanges } from "../../src/diagnostics.ts";
import { runExpander, runLookup, type ExpandResponse } from "../../src/modules.ts";
import { injectMissingFactory } from "../../src/pipeline.ts";
import type { LessonManifest } from "../../src/protocol.ts";
import { parseStderr, reportable } from "../../src/rustc.ts";

const [command, ...rest] = Bun.argv.slice(2);
const { values } = parseArgs({
  args: rest,
  options: {
    expander: { type: "string" },
    lesson: { type: "string" },
    source: { type: "string" },
    out: { type: "string" },
    dir: { type: "string" },
    stderr: { type: "string" },
    fault: { type: "string" },
  },
});
const module = await WebAssembly.compile(readFileSync(values.expander!));
const source = readFileSync(values.source!, "utf8");

if (command === "expand") {
  const lesson = JSON.parse(readFileSync(values.lesson!, "utf8")) as LessonManifest;
  const generatedFile = `/work/expanded/${lesson.lesson}/${lesson.display_file}`;
  const response = await runExpander(module, {
    schema: 1,
    mode: "whole-file",
    file: { virtual_path: `${lesson.package.manifest_dir}/${lesson.display_file}`, display_file: lesson.display_file, source },
    package: {
      cargo_name: lesson.package.cargo_name,
      cargo_version: lesson.package.cargo_version,
      manifest_dir: lesson.package.manifest_dir,
      crate_name: lesson.package.crate_name,
    },
    module_path: [lesson.package.crate_name],
    facade: lesson.facade,
    generated_file: generatedFile,
    policy: lesson.policy,
  });
  const out = values.out!;
  mkdirSync(out, { recursive: true });
  let fault: string | null = null;
  if (response.ok && response.expanded && values.fault === "registration-table-missing-factory") {
    const injected = injectMissingFactory(response.expanded.text, response);
    response.expanded.text = injected.text;
    fault = injected.detail;
  }
  if (response.expanded) writeFileSync(join(out, "expanded.rs"), response.expanded.text);
  writeFileSync(join(out, "response.json"), `${JSON.stringify({ ...response, fault }, null, 1)}\n`);
  console.log(JSON.stringify({ ok: response.ok, diagnostics: response.diagnostics, fault }));
} else if (command === "map") {
  const dir = values.dir!;
  const response = JSON.parse(readFileSync(join(dir, "response.json"), "utf8")) as ExpandResponse;
  const text = readFileSync(join(dir, "expanded.rs"), "utf8");
  const parsed = parseStderr(readFileSync(values.stderr!, "utf8"));
  const diagnostics = reportable(parsed.diagnostics);
  const generatedFile = join(dir, "expanded.rs");
  const ranges = lookupRanges(diagnostics, generatedFile).filter((r): r is [number, number] => r !== null);
  const lookup = ranges.length > 0
    ? await runLookup(module, { schema: 1, authored_source: source, text, source_map: response.source_map, ranges })
    : null;
  const mapped = fromRustc(diagnostics, generatedFile, "src/lib.rs", lookup?.ok ? lookup.mappings : null);
  console.log(JSON.stringify(mapped.map(({ rendered: _rendered, ...d }) => d), null, 1));
} else {
  throw new Error("usage: expand-case.ts expand|map ...");
}
