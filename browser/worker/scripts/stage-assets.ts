// Assembles the worker's immutable assets into one directory (default
// krs-browser-assets under the scratch root) and writes the normalized pack.json and the
// tour-minimal lesson manifest. No file is downloaded; large binaries stay out
// of git.
//
//   bun scripts/stage-assets.ts [--out DIR] [--pack DIR] [--krs-rev REV (default HEAD)]
//
// Inputs:
//   --pack               a dependency pack root (holds pack-manifest.toml; default SCRATCH/krs-browser-pack/pack)
//   KRS_STAGE_POLICY     krs_lesson_policy.wasm built from the pack's crates/ tree
//   KRS_STAGE_EXPANDER   krs_expand_wasm.wasm built from the pack's crates/ tree
//   KRS_STAGE_REPO       KRS checkout holding --krs-rev (module revision and the tour-minimal lesson)
// SCRATCH is the scratch root (test/harness/environment.ts). Build each module in
// its own cargo invocation (a joint build unifies the policy crate's `abi`
// feature into the expander), as tests/browser-pack/run.py does:
//   CARGO_TARGET_DIR=SCRATCH/krs-browser-pack-target/<pkg> cargo +stable build -p <pkg> \
//     --target wasm32-unknown-unknown --release --offline

import { copyFileSync, mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import { parseArgs } from "node:util";
import { packFromManifest, type SourcePackManifest } from "../src/pack-manifest.ts";
import { sha256Hex } from "../src/pack.ts";
import type { LessonManifest, PackAsset } from "../src/protocol.ts";
import { scratchPath } from "../test/harness/environment.ts";
import { buildLessonManifest } from "./lesson-manifest.ts";

const { values } = parseArgs({
  options: {
    out: { type: "string", default: scratchPath("krs-browser-assets") },
    pack: { type: "string", default: scratchPath("krs-browser-pack/pack") },
    "krs-rev": { type: "string", default: "HEAD" },
  },
});
const OUT = values.out!;
const PACK = values.pack!;
const env = (name: string, fallback: string) => process.env[name] ?? fallback;
const inputs = {
  policy: env("KRS_STAGE_POLICY", scratchPath("krs-browser-pack-target/krs-lesson-policy/wasm32-unknown-unknown/release/krs_lesson_policy.wasm")),
  expander: env("KRS_STAGE_EXPANDER", scratchPath("krs-browser-pack-target/krs-expand-wasm/wasm32-unknown-unknown/release/krs_expand_wasm.wasm")),
  repo: env("KRS_STAGE_REPO", join(import.meta.dir, "../../..")),
};

function git(...args: string[]): Uint8Array {
  const result = Bun.spawnSync(["git", "-C", inputs.repo, ...args]);
  if (result.exitCode !== 0) throw new Error(`git ${args.join(" ")}: ${result.stderr.toString()}`);
  return new Uint8Array(result.stdout);
}
const text = (bytes: Uint8Array) => new TextDecoder().decode(bytes);
const KRS_REV = text(git("rev-parse", "--verify", `${values["krs-rev"]!}^{commit}`)).trim();
const gitShow = (path: string) => git("show", `${KRS_REV}:${path}`);
// The one KRS schema version (descriptor bundles and both IRs) pinned by Krs.lock at the staged revision.
function krsIrSchema(): number {
  const lock = Bun.TOML.parse(text(gitShow("Krs.lock"))) as { schemas?: { krs_ir?: unknown } };
  const schema = lock.schemas?.krs_ir;
  if (typeof schema !== "number") throw new Error(`Krs.lock at ${KRS_REV} has no [schemas] krs_ir`);
  return schema;
}

async function place(rel: string, bytes: Uint8Array): Promise<PackAsset> {
  const target = join(OUT, rel);
  mkdirSync(dirname(target), { recursive: true });
  writeFileSync(target, bytes);
  return { path: rel, sha256: await sha256Hex(bytes), bytes: bytes.byteLength };
}

async function placeFile(rel: string, source: string): Promise<PackAsset> {
  const target = join(OUT, rel);
  mkdirSync(dirname(target), { recursive: true });
  copyFileSync(source, target);
  const bytes = new Uint8Array(readFileSync(target));
  return { path: rel, sha256: await sha256Hex(bytes), bytes: bytes.byteLength };
}

function walk(dir: string): string[] {
  return readdirSync(dir).flatMap((name) => {
    const path = join(dir, name);
    return statSync(path).isDirectory() ? walk(path) : [path];
  });
}

rmSync(OUT, { recursive: true, force: true });
mkdirSync(OUT, { recursive: true });

// The dependency pack, copied as is under pack/ (the loader verifies every artifact and pack_id).
const manifestText = readFileSync(join(PACK, "pack-manifest.toml"), "utf8");
const source = Bun.TOML.parse(manifestText) as unknown as SourcePackManifest;
for (const file of walk(PACK)) await placeFile(`pack/${relative(PACK, file)}`, file);

const pack = await packFromManifest(source, {
  packDir: "pack",
  sourcePath: join(PACK, "pack-manifest.toml"),
  sourceSha256: await sha256Hex(new TextEncoder().encode(manifestText)),
  policy: await placeFile("modules/krs_lesson_policy.wasm", inputs.policy),
  expander: await placeFile("modules/krs_expand_wasm.wasm", inputs.expander),
  modulesKrsRevision: KRS_REV,
  modulesCratesTree: text(git("rev-parse", `${KRS_REV}:crates`)).trim(),
  protocolVersion: krsIrSchema(),
});
writeFileSync(join(OUT, "pack.json"), `${JSON.stringify(pack, null, 1)}\n`);

// tour-minimal lesson manifest, rendered from the fixture's Cargo.toml.
const cargo = buildLessonManifest(text(gitShow("tests/tour-minimal/Cargo.toml")), text(gitShow("Cargo.toml")));
const facadeAlias = cargo.facadeAlias;
const lintFlags = cargo.lintFlags;
const lesson: LessonManifest = {
  schema: 1,
  lesson: "tour-minimal",
  pack_id: pack.pack_id,
  expansion: "krs-expander",
  package: {
    cargo_name: cargo.name,
    cargo_version: cargo.version,
    crate_name: cargo.libName,
    manifest_dir: "/workspace/tour-minimal",
    edition: cargo.edition,
    k_namespace: cargo.namespace!,
    cargo_source: "workspace",
    cargo_toml: cargo.cargoToml,
  },
  facade: { alias: facadeAlias, path: `::${facadeAlias}` },
  display_file: "src/lib.rs",
  policy: { editable_files: ["src/lib.rs"], facade_alias: facadeAlias },
  rustc_lint_flags: lintFlags,
};
await place("lessons/tour-minimal/lesson.json", new TextEncoder().encode(`${JSON.stringify(lesson, null, 1)}\n`));
await place("lessons/tour-minimal/src/lib.rs", gitShow("tests/tour-minimal/src/lib.rs"));

console.log(JSON.stringify({
  out: OUT,
  pack_id: pack.pack_id,
  pack_krs_revision: pack.krs_revision,
  modules_krs_revision: pack.modules.krs_revision,
  crates_tree: pack.crates_tree,
  artifacts: pack.artifacts.length,
  lint_flags: lintFlags,
}, null, 1));
