// Builds the static worker test site: worker.js and page.js bundles, the page,
// the scenario fixtures, and an `assets` link to the staged pack.
//
//   bun scripts/build-site.ts [--out DIR] [--assets DIR]

import { join } from "node:path";
import { parseArgs } from "node:util";
import { scratchPath } from "../test/harness/environment.ts";
import { buildSite } from "../test/harness/site.ts";

const { values } = parseArgs({
  options: {
    out: { type: "string", default: scratchPath("krs-browser-site") },
    assets: { type: "string", default: scratchPath("krs-browser-assets") },
  },
});
const root = join(import.meta.dir, "..");
const outputs = await buildSite({
  out: values.out!,
  entrypoints: [join(root, "src/worker.ts"), join(root, "test/page/page.ts")],
  copies: { "index.html": join(root, "test/page/index.html"), fixtures: join(root, "test/fixtures") },
  links: { assets: values.assets! },
});
console.log(JSON.stringify({ out: values.out, outputs }));
