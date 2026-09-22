// Builds the static suite site: page.js and shim-worker.js bundles, the page,
// suite.json (with the pack's page-relative URL), and an `assets` link to the
// directory holding the pack (no copy of the 207 MB pack).
//
//   bun runner/build-site.ts --out DIR --suite SUITE_JSON --pack PACK_ROOT

import { cpSync, mkdirSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { basename, dirname, join } from "node:path";
import { parseArgs } from "node:util";

const { values } = parseArgs({
  options: {
    out: { type: "string" },
    suite: { type: "string" },
    pack: { type: "string" },
  },
});
if (!values.out || !values.suite || !values.pack) throw new Error("usage: bun runner/build-site.ts --out DIR --suite FILE --pack DIR");
const root = join(import.meta.dir, "..");
const out = values.out;
rmSync(out, { recursive: true, force: true });
mkdirSync(out, { recursive: true });
const result = await Bun.build({
  entrypoints: [join(root, "page/page.ts"), join(root, "runner/shim-worker.ts")],
  outdir: out,
  target: "browser",
  format: "esm",
  naming: "[name].js",
  minify: false,
  sourcemap: "linked",
});
if (!result.success) {
  for (const log of result.logs) console.error(log);
  process.exit(1);
}
cpSync(join(root, "page/index.html"), join(out, "index.html"));
const pack = realpathSync(values.pack);
symlinkSync(dirname(pack), join(out, "assets"));
const suite = JSON.parse(readFileSync(values.suite, "utf8"));
suite.pack.url_base = `assets/${basename(pack)}`;
writeFileSync(join(out, "suite.json"), JSON.stringify(suite));
console.log(JSON.stringify({ out, pack, outputs: result.outputs.map((o) => o.path) }));
