// Builds the static suite site: page.js and shim-worker.js bundles, the page,
// suite.json (with the pack's page-relative URL), and an `assets` link to the
// directory holding the pack (no copy of the 207 MB pack).
//
//   bun runner/build-site.ts --out DIR --suite SUITE_JSON --pack PACK_ROOT

import { readFileSync, realpathSync, writeFileSync } from "node:fs";
import { basename, dirname, join } from "node:path";
import { parseArgs } from "node:util";
import { buildSite } from "../../../browser/worker/test/harness/site.ts";

const { values } = parseArgs({
  options: {
    out: { type: "string" },
    suite: { type: "string" },
    pack: { type: "string" },
  },
});
if (!values.out || !values.suite || !values.pack) throw new Error("usage: bun runner/build-site.ts --out DIR --suite FILE --pack DIR");
const root = join(import.meta.dir, "..");
const pack = realpathSync(values.pack);
const outputs = await buildSite({
  out: values.out,
  entrypoints: [join(root, "page/page.ts"), join(root, "runner/shim-worker.ts")],
  copies: { "index.html": join(root, "page/index.html") },
  links: { assets: dirname(pack) },
});
const suite = JSON.parse(readFileSync(values.suite, "utf8"));
suite.pack.url_base = `assets/${basename(pack)}`;
writeFileSync(join(values.out, "suite.json"), JSON.stringify(suite));
console.log(JSON.stringify({ out: values.out, pack, outputs }));
