// Assembles the worker's immutable assets into one directory (default
// /var/tmp/krs-ir15-assets) and writes the normalized pack.json and the
// tour-minimal lesson manifest. No file is downloaded; large binaries stay out
// of git.
//
//   bun scripts/stage-assets.ts [--out DIR] [--krs-rev REV]
//
// Inputs (overridable with environment variables):
//   KRS_IR15_PACK_MANIFEST  IR-06 cell-2 pack-manifest.toml (evidence/IR-06/cell2)
//   KRS_IR15_PACK_DEPS      the pack's flat deps directory (/var/tmp/krs-ir06-cell2/w/deps)
//   KRS_IR15_RUSTC          rustc.wasm of configuration K (fork 195111dff)
//   KRS_IR15_SYSROOT        sysroot-wasip1.bundle of configuration K
//   KRS_IR15_POLICY         krs_lesson_policy.wasm built at KRS_REV
//   KRS_IR15_EXPANDER       krs_expand_wasm.wasm built at KRS_REV
//   KRS_IR15_REPO           KRS checkout that holds KRS_REV (framework sources, lesson)
// If evidence/IR-14/manifest-format.toml exists, the script says so: an IR-14
// adapter replaces pack-ir06.ts at that point.

import { existsSync, mkdirSync, readFileSync, writeFileSync, copyFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { parseArgs } from "node:util";
import { packFromIr06, type Ir06PackManifest } from "../src/pack-ir06.ts";
import { sha256Hex } from "../src/pack.ts";
import type { LessonManifest, MountedSource, PackAsset } from "../src/protocol.ts";

const EVIDENCE = "/home/sebastiengllmt/git/workspaces/starstream-fv/krs/draft/browser-lessons/independent-review/evidence";
const { values } = parseArgs({
  options: {
    out: { type: "string", default: "/var/tmp/krs-ir15-assets" },
    "krs-rev": { type: "string", default: "3501f86cf5c219c300107302ab76c1b2854464c4" },
  },
});
const OUT = values.out!;
const KRS_REV = values["krs-rev"]!;
const env = (name: string, fallback: string) => process.env[name] ?? fallback;
const inputs = {
  packManifest: env("KRS_IR15_PACK_MANIFEST", `${EVIDENCE}/IR-06/cell2/pack-manifest.toml`),
  packDeps: env("KRS_IR15_PACK_DEPS", "/var/tmp/krs-ir06-cell2/w/deps"),
  rustc: env("KRS_IR15_RUSTC", "/var/tmp/krs-browser-fork/R-k/out/rustc/rustc.wasm"),
  sysroot: env("KRS_IR15_SYSROOT", "/var/tmp/krs-browser-fork/R-k/out/wasip1/stage/rustc/sysroot-wasip1.bundle"),
  policy: env("KRS_IR15_POLICY", "/var/tmp/krs-ir15-target/krs-lesson-policy/wasm32-unknown-unknown/release/krs_lesson_policy.wasm"),
  expander: env("KRS_IR15_EXPANDER", "/var/tmp/krs-ir15-target/krs-expand-wasm/wasm32-unknown-unknown/release/krs_expand_wasm.wasm"),
  repo: env("KRS_IR15_REPO", join(import.meta.dir, "../../..")),
};

if (existsSync(`${EVIDENCE}/IR-14/manifest-format.toml`)) {
  console.error("note: evidence/IR-14/manifest-format.toml exists; this script still stages the IR-06 cell-2 pack through pack-ir06.ts");
}

function gitShow(path: string): Uint8Array {
  const result = Bun.spawnSync(["git", "-C", inputs.repo, "show", `${KRS_REV}:${path}`]);
  if (result.exitCode !== 0) throw new Error(`git show ${KRS_REV}:${path}: ${result.stderr.toString()}`);
  return new Uint8Array(result.stdout);
}

async function place(relative: string, bytes: Uint8Array): Promise<PackAsset> {
  const target = join(OUT, relative);
  mkdirSync(dirname(target), { recursive: true });
  writeFileSync(target, bytes);
  return { path: relative, sha256: await sha256Hex(bytes), bytes: bytes.byteLength };
}

async function placeFile(relative: string, source: string): Promise<PackAsset> {
  const target = join(OUT, relative);
  mkdirSync(dirname(target), { recursive: true });
  copyFileSync(source, target);
  const bytes = new Uint8Array(readFileSync(target));
  return { path: relative, sha256: await sha256Hex(bytes), bytes: bytes.byteLength };
}

mkdirSync(OUT, { recursive: true });
const manifestText = readFileSync(inputs.packManifest, "utf8");
const ir06 = Bun.TOML.parse(manifestText) as unknown as Ir06PackManifest;

// Pack artifacts: copy from the flat deps directory and check against the IR-06 manifest.
for (const artifact of ir06.artifact) {
  const file = artifact.path.split("/").pop()!;
  const staged = artifact.role === "proc-macro-metadata" ? `pack/proc-macro-meta/${file}` : `pack/deps/${file}`;
  const placed = await placeFile(staged, join(inputs.packDeps, file));
  if (placed.sha256 !== artifact.sha256 || placed.bytes !== artifact.bytes) {
    throw new Error(`${file}: staged ${placed.sha256}/${placed.bytes}, manifest ${artifact.sha256}/${artifact.bytes}`);
  }
}

const frameworkSources: MountedSource[] = [];
for (const path of ["crates/krs/Cargo.toml", "crates/krs/src/lib.rs"]) {
  frameworkSources.push({ ...(await place(`krs/${path}`, gitShow(path))), mount: `/krs/${path}` });
}

const pack = await packFromIr06(ir06, {
  sourcePath: inputs.packManifest,
  sourceSha256: await sha256Hex(new TextEncoder().encode(manifestText)),
  rustc: await placeFile("rustc/rustc.wasm", inputs.rustc),
  sysrootBundle: await placeFile("rustc/sysroot-wasip1.bundle", inputs.sysroot),
  policy: await placeFile("modules/krs_lesson_policy.wasm", inputs.policy),
  expander: await placeFile("modules/krs_expand_wasm.wasm", inputs.expander),
  frameworkSources,
  protocolVersion: 35,
  packDir: "pack",
});
if (pack.krs_revision !== KRS_REV) throw new Error(`pack is KRS ${pack.krs_revision}, staging ${KRS_REV}`);
writeFileSync(join(OUT, "pack.json"), `${JSON.stringify(pack, null, 1)}\n`);

// tour-minimal lesson manifest, rendered from the fixture's Cargo.toml.
const cargoToml = new TextDecoder().decode(gitShow("tests/tour-minimal/Cargo.toml"));
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
  policy: { version: 1, editable_files: ["src/lib.rs"], facade_alias: facadeAlias },
  rustc_lint_flags: lintFlags,
};
await place("lessons/tour-minimal/lesson.json", new TextEncoder().encode(`${JSON.stringify(lesson, null, 1)}\n`));
await place("lessons/tour-minimal/src/lib.rs", gitShow("tests/tour-minimal/src/lib.rs"));

console.log(JSON.stringify({ out: OUT, pack_id: pack.pack_id, krs_revision: pack.krs_revision, artifacts: pack.artifacts.length, lint_flags: lintFlags }, null, 1));
