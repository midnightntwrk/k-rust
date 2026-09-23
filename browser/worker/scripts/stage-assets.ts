// Assembles the worker's immutable assets into one directory (default
// /var/tmp/krs-browser-assets) and writes the normalized pack.json and the
// tour-minimal lesson manifest. No file is downloaded; large binaries stay out
// of git.
//
//   bun scripts/stage-assets.ts [--out DIR] [--pack DIR] [--krs-rev REV] [--policy-version N]
//
// Inputs:
//   --pack               a dependency pack root (holds pack-manifest.toml; default /var/tmp/krs-browser-pack/pack)
//   --policy-version     the lesson manifest's [policy] version (default 2; 1 reproduces the
//                        manifests from before policy version 2)
//   KRS_STAGE_POLICY     krs_lesson_policy.wasm built from the pack's crates/ tree
//   KRS_STAGE_EXPANDER   krs_expand_wasm.wasm built from the pack's crates/ tree
//   KRS_STAGE_REPO       KRS checkout holding --krs-rev (module revision and the tour-minimal lesson)
// Build each module in its own cargo invocation (a joint build unifies the
// policy crate's `abi` feature into the expander):
//   CARGO_TARGET_DIR=/var/tmp/krs-browser-modules-target/<pkg> cargo +stable build -p <pkg> \
//     --target wasm32-unknown-unknown --release --offline

import { copyFileSync, mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import { parseArgs } from "node:util";
import { packFromManifest, type SourcePackManifest } from "../src/pack-manifest.ts";
import { sha256Hex } from "../src/pack.ts";
import type { LessonManifest, PackAsset } from "../src/protocol.ts";

const { values } = parseArgs({
  options: {
    out: { type: "string", default: "/var/tmp/krs-browser-assets" },
    pack: { type: "string", default: "/var/tmp/krs-browser-pack/pack" },
    "krs-rev": { type: "string", default: "3501f86cf5c219c300107302ab76c1b2854464c4" },
    "policy-version": { type: "string", default: "2" },
  },
});
const OUT = values.out!;
const PACK = values.pack!;
const KRS_REV = values["krs-rev"]!;
const POLICY_VERSION = Number(values["policy-version"]);
if (!Number.isInteger(POLICY_VERSION) || POLICY_VERSION < 1) throw new Error(`--policy-version: ${values["policy-version"]}`);
const env = (name: string, fallback: string) => process.env[name] ?? fallback;
const inputs = {
  policy: env("KRS_STAGE_POLICY", "/var/tmp/krs-browser-modules-target/krs-lesson-policy/wasm32-unknown-unknown/release/krs_lesson_policy.wasm"),
  expander: env("KRS_STAGE_EXPANDER", "/var/tmp/krs-browser-modules-target/krs-expand-wasm/wasm32-unknown-unknown/release/krs_expand_wasm.wasm"),
  repo: env("KRS_STAGE_REPO", join(import.meta.dir, "../../..")),
};

function git(...args: string[]): Uint8Array {
  const result = Bun.spawnSync(["git", "-C", inputs.repo, ...args]);
  if (result.exitCode !== 0) throw new Error(`git ${args.join(" ")}: ${result.stderr.toString()}`);
  return new Uint8Array(result.stdout);
}
const gitShow = (path: string) => git("show", `${KRS_REV}:${path}`);
const text = (bytes: Uint8Array) => new TextDecoder().decode(bytes);

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
  protocolVersion: 35,
});
writeFileSync(join(OUT, "pack.json"), `${JSON.stringify(pack, null, 1)}\n`);

// tour-minimal lesson manifest, rendered from the fixture's Cargo.toml.
const cargoToml = text(gitShow("tests/tour-minimal/Cargo.toml"));
const cargo = Bun.TOML.parse(cargoToml) as {
  package: { name: string; version: string; edition: string; metadata: { krs: { "k-namespace": string } } };
  lib: { name: string };
  dependencies: Record<string, { package?: string }>;
  lints?: { rust?: Record<string, string | { level: string; priority?: number }> };
};
const levelFlag: Record<string, string> = { forbid: "-F", deny: "-D", warn: "-W", allow: "-A" };
const lintFlags = Object.entries(cargo.lints?.rust ?? {})
  .map(([name, value]) => (typeof value === "string" ? { name, level: value, priority: 0 } : { name, level: value.level, priority: value.priority ?? 0 }))
  .sort((a, b) => a.priority - b.priority || (a.name < b.name ? -1 : 1))
  .flatMap(({ name, level }) => [levelFlag[level]!, name]);
const facadeAlias = Object.entries(cargo.dependencies).find(([, dep]) => dep.package === "krs")![0];
const lesson: LessonManifest = {
  schema: 1,
  lesson: "tour-minimal",
  pack_id: pack.pack_id,
  expansion: "krs-expander",
  package: {
    cargo_name: cargo.package.name,
    cargo_version: cargo.package.version,
    crate_name: cargo.lib.name,
    manifest_dir: "/workspace/tour-minimal",
    edition: cargo.package.edition,
    k_namespace: cargo.package.metadata.krs["k-namespace"],
    cargo_source: "workspace",
    cargo_toml: cargoToml,
  },
  facade: { alias: facadeAlias, path: `::${facadeAlias}` },
  display_file: "src/lib.rs",
  policy: { version: POLICY_VERSION, editable_files: ["src/lib.rs"], facade_alias: facadeAlias },
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
  policy_version: POLICY_VERSION,
}, null, 1));
