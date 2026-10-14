// Builds a static test site: ESM browser bundles of the entry points (named
// <entry>.js, with linked source maps), copied files, and links to directories
// that stay outside the site (the staged pack is never copied).

import { cpSync, mkdirSync, rmSync, symlinkSync } from "node:fs";
import { join } from "node:path";

export interface SiteSpec {
  out: string;
  entrypoints: string[];
  /** Site-relative path to the file or directory copied there. */
  copies?: Record<string, string>;
  /** Site-relative path to the directory linked there. */
  links?: Record<string, string>;
}

/** Rebuilds `spec.out` from scratch; returns the bundle paths. */
export async function buildSite(spec: SiteSpec): Promise<string[]> {
  rmSync(spec.out, { recursive: true, force: true });
  mkdirSync(spec.out, { recursive: true });
  const result = await Bun.build({
    entrypoints: spec.entrypoints,
    outdir: spec.out,
    target: "browser",
    format: "esm",
    naming: "[name].js",
    minify: false,
    sourcemap: "linked",
  });
  if (!result.success) {
    throw new AggregateError(result.logs, `site build of ${spec.out} failed:\n${result.logs.map(String).join("\n")}`);
  }
  for (const [path, source] of Object.entries(spec.copies ?? {})) cpSync(source, join(spec.out, path), { recursive: true });
  for (const [path, target] of Object.entries(spec.links ?? {})) symlinkSync(target, join(spec.out, path));
  return result.outputs.map((o) => o.path);
}
