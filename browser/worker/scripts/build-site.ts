// Builds the static test site: worker.js and page.js bundles, the page, the
// scenario fixtures, and an `assets` link to the staged pack.
//
//   bun scripts/build-site.ts [--out DIR] [--assets DIR]

import { cpSync, mkdirSync, rmSync, symlinkSync } from "node:fs";
import { join } from "node:path";
import { parseArgs } from "node:util";

const { values } = parseArgs({
  options: {
    out: { type: "string", default: "/var/tmp/krs-ir15-site" },
    assets: { type: "string", default: "/var/tmp/krs-ir15-assets" },
  },
});
const root = join(import.meta.dir, "..");
const out = values.out!;
rmSync(out, { recursive: true, force: true });
mkdirSync(out, { recursive: true });
const result = await Bun.build({
  entrypoints: [join(root, "src/worker.ts"), join(root, "test/page/page.ts")],
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
cpSync(join(root, "test/page/index.html"), join(out, "index.html"));
cpSync(join(root, "test/fixtures"), join(out, "fixtures"), { recursive: true });
symlinkSync(values.assets!, join(out, "assets"));
console.log(JSON.stringify({ out, outputs: result.outputs.map((o) => o.path) }));
