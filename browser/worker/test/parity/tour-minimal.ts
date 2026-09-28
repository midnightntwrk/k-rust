// tour-minimal bundle parity gate: real tour-minimal native/browser bundle parity.
//
//   bun test/parity/tour-minimal.ts [--regenerate-oracle] [--out DIR] [--repeats 2]
//       [--browsers chromium,firefox] [--oracle-dir DIR] [--assets DIR] [--site DIR]
//       [--bundles DIR] [--scratch DIR] [--load-max 40]
//
// Reads the editable lesson file tests/tour-minimal/src/lib.rs from the
// checkout (not a pre-expanded copy) and E1 = edit-e1.patch applied
// to it, and runs, in each browser, one page session per repeat with a fresh
// profile: S0 original (cold), S1 original (warm), S2 E1, S3 original again,
// all through the worker API with the dependency pack. Every bundle is
// compared byte for byte with the compact native `krs emit-k` oracle that
// regenerate-oracle.sh recorded in <oracle-dir>/oracle.toml.
//
// The gate refuses to compare (exit 3) when oracle.toml does not match the
// checkout (crates/ tree, tests/tour-minimal tree, Cargo.lock, source hashes,
// the hashes embedded in the oracle) or when the staged pack was built from
// another crates/ tree, and prints the regeneration command.

import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseArgs } from "node:util";
import { openSite, type SiteSession } from "../harness/browsers.ts";
import { REPO, scratchPath, waitForLoad as waitForLoadAverage } from "../harness/environment.ts";

const { values } = parseArgs({
  options: {
    "regenerate-oracle": { type: "boolean", default: false },
    "oracle-dir": { type: "string", default: scratchPath("krs-parity-oracle") },
    out: { type: "string", default: scratchPath("krs-parity-run/evidence") },
    bundles: { type: "string", default: scratchPath("krs-parity-run/bundles") },
    scratch: { type: "string", default: scratchPath("krs-parity-run/scratch") },
    assets: { type: "string", default: scratchPath("krs-browser-assets") },
    site: { type: "string", default: scratchPath("krs-parity-site") },
    repeats: { type: "string", default: "2" },
    browsers: { type: "string", default: "chromium,firefox" },
    "load-max": { type: "string", default: "40" },
    port: { type: "string", default: "4335" },
  },
});
const here = import.meta.dir;
const workerRoot = join(here, "../..");
const repo = REPO;
const oracleDir = values["oracle-dir"]!;
const oracleToml = join(oracleDir, "oracle.toml");
const regenerate = `browser/worker/test/parity/regenerate-oracle.sh ${oracleDir}`;
const out = values.out!;
mkdirSync(out, { recursive: true });

function sh(command: string[], cwd = repo): string {
  const result = Bun.spawnSync(command, { cwd, stderr: "pipe" });
  if (result.exitCode !== 0) throw new Error(`${command.join(" ")}: ${result.stderr.toString()}`);
  return result.stdout.toString();
}
const git = (...args: string[]) => sh(["git", ...args]).trim();
const sha256 = (bytes: Uint8Array | string) => new Bun.CryptoHasher("sha256").update(bytes).digest("hex");

const waitForLoad = () => waitForLoadAverage(Number(values["load-max"]));

if (values["regenerate-oracle"]) {
  await waitForLoad();
  const child = Bun.spawn(["bash", join(here, "regenerate-oracle.sh"), oracleDir], { cwd: repo, stdout: "inherit", stderr: "inherit" });
  if ((await child.exited) !== 0) process.exit(1);
}

// ---------------------------------------------------------------- oracle validity (fail closed)

interface OracleRecord {
  bundle: string;
  bundle_bytes: number;
  bundle_sha256: string;
  protocol_version: number;
  descriptors: number;
  lesson_source_sha256: string;
  descriptor_kinds: Record<string, number>;
}
interface OracleToml {
  krs_revision: string;
  validity: Record<string, string | number>;
  oracle: OracleRecord;
  oracle_e1: OracleRecord & { edit_patch_sha256: string };
}

function refuse(problems: string[]): never {
  process.stderr.write(`tour-minimal parity gate refuses to compare:\n${problems.map((p) => `  - ${p}`).join("\n")}\nregenerate with:\n  ${regenerate}\n`);
  writeFileSync(join(out, "gate.json"), `${JSON.stringify({ pass: false, refused: problems, regenerate }, null, 1)}\n`);
  process.exit(3);
}

if (!existsSync(oracleToml)) refuse([`${oracleToml} does not exist`]);
const oracle = Bun.TOML.parse(readFileSync(oracleToml, "utf8")) as unknown as OracleToml;
const lessonPath = join(repo, "tests/tour-minimal/src/lib.rs");
const lessonText = readFileSync(lessonPath, "utf8");
const current = {
  crates_tree: git("rev-parse", "HEAD:crates"),
  tour_minimal_tree: git("rev-parse", "HEAD:tests/tour-minimal"),
  cargo_lock_blob: git("rev-parse", "HEAD:Cargo.lock"),
  krs_lib_rs_sha256: sha256(readFileSync(join(repo, "crates/krs/src/lib.rs"))),
  lesson_source_sha256: sha256(lessonText),
};
const problems: string[] = [];
for (const [key, value] of Object.entries(current)) {
  if (oracle.validity[key] !== value) problems.push(`oracle.toml validity.${key} = ${String(oracle.validity[key])}, checkout has ${value}`);
}
if (git("status", "--porcelain", "--", "crates", "tests/tour-minimal", "Cargo.lock") !== "") problems.push("crates/, tests/tour-minimal, or Cargo.lock has uncommitted changes");
const patchPath = join(here, "edit-e1.patch");
if (sha256(readFileSync(patchPath)) !== oracle.oracle_e1.edit_patch_sha256) problems.push("edit-e1.patch differs from the one the E1 oracle was generated with");
const oracleBytes = { base: new Uint8Array(readFileSync(oracle.oracle.bundle)), e1: new Uint8Array(readFileSync(oracle.oracle_e1.bundle)) };
if (sha256(oracleBytes.base) !== oracle.oracle.bundle_sha256) problems.push(`${oracle.oracle.bundle} does not have the recorded sha256`);
if (sha256(oracleBytes.e1) !== oracle.oracle_e1.bundle_sha256) problems.push(`${oracle.oracle_e1.bundle} does not have the recorded sha256`);
if (oracleBytes.base.length !== oracle.oracle.bundle_bytes || oracleBytes.e1.length !== oracle.oracle_e1.bundle_bytes) problems.push("oracle bundle byte count differs from its record");
if (oracleBytes.base.at(-1) !== 10 || oracleBytes.e1.at(-1) !== 10) problems.push("oracle bundle lacks the collector stdout newline");
const embeddedHashes = (bytes: Uint8Array) =>
  [...new Set([...new TextDecoder().decode(bytes).matchAll(/"content_sha256":\s*"([0-9a-f]{64})"/g)].map((m) => m[1]!))].sort();
const wantEmbedded = [current.krs_lib_rs_sha256, current.lesson_source_sha256].sort();
if (JSON.stringify(embeddedHashes(oracleBytes.base)) !== JSON.stringify(wantEmbedded)) {
  problems.push(`the oracle embeds ${embeddedHashes(oracleBytes.base).join(", ")}, expected ${wantEmbedded.join(", ")}`);
}
const pack = JSON.parse(readFileSync(join(values.assets!, "pack.json"), "utf8")) as { pack_id: string; crates_tree: string; krs_revision: string; modules: { crates_tree: string } };
if (pack.crates_tree !== current.crates_tree) problems.push(`staged pack crates_tree ${pack.crates_tree} differs from the checkout's ${current.crates_tree} (rebuild the pack)`);
if (pack.modules.crates_tree !== current.crates_tree) problems.push(`staged modules crates_tree ${pack.modules.crates_tree} differs from the checkout's ${current.crates_tree}`);
if (problems.length > 0) refuse(problems);

// E1 source: the patch applied to a scratch copy of the lesson file.
const scratch = join(values.scratch!, "e1");
rmSync(scratch, { recursive: true, force: true });
mkdirSync(join(scratch, "tests/tour-minimal/src"), { recursive: true });
writeFileSync(join(scratch, "tests/tour-minimal/src/lib.rs"), lessonText);
sh(["patch", "-p1", "--quiet", "-i", patchPath], scratch);
const e1Text = readFileSync(join(scratch, "tests/tour-minimal/src/lib.rs"), "utf8");
if (sha256(e1Text) !== oracle.oracle_e1.lesson_source_sha256) refuse([`patched source ${sha256(e1Text)} differs from the E1 oracle's ${oracle.oracle_e1.lesson_source_sha256}`]);

// ---------------------------------------------------------------- site

await waitForLoad();
sh(["bun", "scripts/build-site.ts", "--out", values.site!, "--assets", values.assets!], workerRoot);

// ---------------------------------------------------------------- bundle checks

const decoder = new TextDecoder();
function kinds(bytes: Uint8Array): Record<string, number> {
  const counts: Record<string, number> = Object.create(null) as Record<string, number>;
  for (const d of (JSON.parse(decoder.decode(bytes)) as { descriptors: Array<{ payload: { descriptor_kind: string } }> }).descriptors) {
    const kind = d.payload.descriptor_kind;
    counts[kind] = (counts[kind] ?? 0) + 1;
  }
  return Object.fromEntries(Object.entries(counts).sort());
}
const sameBytes = (a: Uint8Array, b: Uint8Array) => a.length === b.length && a.every((x, i) => x === b[i]);

/** Every SourceFileId must be a package-relative path of a declared virtual file. */
function sourceFileIds(bytes: Uint8Array, lessonSha: string): { ok: boolean; ids: string[]; problems: string[] } {
  const declared = new Map([
    ["krs@0.1.0 (framework) src/lib.rs", current.krs_lib_rs_sha256], // /krs/crates/krs/src/lib.rs
    ["krs-tour-minimal@0.0.0 (workspace) src/lib.rs", lessonSha], // /workspace/tour-minimal/src/lib.rs
  ]);
  const ids = new Set<string>();
  const problems: string[] = [];
  const walk = (value: unknown) => {
    if (Array.isArray(value)) return value.forEach(walk);
    if (!value || typeof value !== "object") return;
    const record = value as Record<string, unknown>;
    if (typeof record.package_relative_path === "string") {
      const pkg = record.package as { cargo_name: string; cargo_version: string; cargo_source: string };
      const id = `${pkg.cargo_name}@${pkg.cargo_version} (${pkg.cargo_source}) ${record.package_relative_path}`;
      ids.add(id);
      if (!declared.has(id)) problems.push(`undeclared source file ${id}`);
      else if (declared.get(id) !== record.content_sha256) problems.push(`${id} hash ${String(record.content_sha256)}`);
    }
    Object.values(record).forEach(walk);
  };
  walk(JSON.parse(decoder.decode(bytes)));
  return { ok: problems.length === 0, ids: [...ids].sort(), problems };
}

// ---------------------------------------------------------------- plan

interface StepSpec {
  step: "S0" | "S1" | "S2" | "S3";
  source: string;
  expect: "base" | "e1";
  note: string;
}
const plan: StepSpec[] = [
  { step: "S0", source: lessonText, expect: "base", note: "original source, cold start" },
  { step: "S1", source: lessonText, expect: "base", note: "original source again, warm" },
  { step: "S2", source: e1Text, expect: "e1", note: "E1 (foo_to_bar -> foo_to_baz)" },
  { step: "S3", source: lessonText, expect: "base", note: "original source restored" },
];

interface Check {
  name: string;
  pass: boolean;
  detail: string;
}

async function runSession(browser: "chromium" | "firefox", repeat: number, port: number) {
  const checks: Check[] = [];
  const steps: unknown[] = [];
  let init: unknown = null;
  let failure: string | null = null;
  let session: SiteSession | null = null;
  const bundleDir = join(values.bundles!, `${browser}-r${repeat}`);
  mkdirSync(bundleDir, { recursive: true });
  const load = await waitForLoad();
  const started = performance.now();
  try {
    session = await openSite({ browser, site: values.site!, port, profilePrefix: scratchPath("krs-parity-profile-"), chromiumArgs: ["--enable-precise-memory-info"] });
    session.sampler.phase = "init";
    init = await session.evaluate("return await window.krsWorker.init();");
    for (const spec of plan) {
      session.sampler.phase = spec.step;
      const t0 = performance.now();
      const result = (await session.evaluate(
        `return await window.krsWorker.runSource(${JSON.stringify({ label: spec.step, source: spec.source, debugEvidence: true, keepBundle: true })});`,
      )) as { wallMs: number; events: Array<Record<string, any>>; requestsDuringBuild: string[]; resourceTiming: unknown[]; workersStarted: number; lesson: string };
      const driverMs = performance.now() - t0;
      const success = result.events.find((e) => e.type === "success");
      const failureEvent = result.events.find((e) => e.type === "failure");
      let bundleInfo: Record<string, unknown> = { outcome: success ? "success" : failureEvent ? `failure ${failureEvent.stage}/${failureEvent.code}: ${failureEvent.message}` : "none" };
      if (success) {
        const bytes = Uint8Array.from(atob(success.bundle.base64 as string), (c) => c.charCodeAt(0));
        const file = join(bundleDir, `${spec.step}.json`);
        writeFileSync(file, bytes);
        const want = spec.expect === "base" ? oracleBytes.base : oracleBytes.e1;
        const wantRecord = spec.expect === "base" ? oracle.oracle : oracle.oracle_e1;
        const cmp = Bun.spawnSync(["cmp", file, wantRecord.bundle]);
        const text = decoder.decode(bytes);
        const hostPaths = ["/home", "/var/tmp", "/srv"].filter((p) => text.includes(p));
        const ids = sourceFileIds(bytes, spec.expect === "base" ? oracle.oracle.lesson_source_sha256 : oracle.oracle_e1.lesson_source_sha256);
        const counts = kinds(bytes);
        bundleInfo = {
          outcome: "success",
          file,
          bytes: bytes.length,
          sha256: sha256(bytes),
          workerSha256: success.bundleSha256,
          cmpExit: cmp.exitCode,
          equalsExpectedOracle: sameBytes(bytes, want),
          equalsBaseOracle: sameBytes(bytes, oracleBytes.base),
          descriptorKinds: counts,
          hostPaths,
          sourceFileIds: ids.ids,
        };
        checks.push({ name: `${spec.step}: cmp with the ${spec.expect === "base" ? "original" : "E1"} oracle`, pass: cmp.exitCode === 0 && sameBytes(bytes, want), detail: `${bytes.length} bytes ${sha256(bytes)}` });
        checks.push({ name: `${spec.step}: worker-reported sha256 equals the bytes`, pass: success.bundleSha256 === sha256(bytes), detail: String(success.bundleSha256) });
        checks.push({ name: `${spec.step}: descriptor kinds equal the oracle's`, pass: JSON.stringify(counts) === JSON.stringify(wantRecord.descriptor_kinds), detail: JSON.stringify(counts) });
        checks.push({ name: `${spec.step}: no physical host path`, pass: hostPaths.length === 0, detail: hostPaths.join(", ") || "none" });
        checks.push({ name: `${spec.step}: SourceFileIds are the declared virtual files`, pass: ids.ok, detail: ids.problems.join("; ") || ids.ids.join("; ") });
        if (spec.expect === "e1") checks.push({ name: `${spec.step}: differs from the original oracle`, pass: !sameBytes(bytes, oracleBytes.base), detail: "E1 must change the bundle" });
      } else {
        checks.push({ name: `${spec.step}: success`, pass: false, detail: String(bundleInfo.outcome) });
      }
      checks.push({
        name: `${spec.step}: no network request during the build except local worker.js`,
        pass: result.requestsDuringBuild.every((name) => /^http:\/\/127\.0\.0\.1:\d+\/worker\.js$/.test(name)),
        detail: result.requestsDuringBuild.join(", ") || "none",
      });
      const evidence = success?.evidence ?? failureEvent?.evidence;
      steps.push({
        step: spec.step,
        note: spec.note,
        expected: spec.expect === "base" ? "original oracle" : "E1 oracle",
        sourceSha256: sha256(spec.source),
        wallMs: result.wallMs,
        driverMs,
        workersStarted: result.workersStarted,
        expansionPath: "C (lesson.expansion = krs-expander; krs-expand-wasm module)",
        bundle: bundleInfo,
        stageEvents: result.events.filter((e) => e.type === "progress").map((e) => ({ atMs: e.atMs, stage: e.stage, state: e.state, ms: e.ms })),
        stageMs: evidence?.stageMs ?? null,
        artifacts: evidence?.artifacts ?? null,
        expandedSha256: evidence?.expandedSha256 ?? null,
        rustcRunMs: evidence ? { lesson: evidence.rustc?.lesson?.runMs, collector: evidence.rustc?.collector?.runMs, riwl: evidence.rustc?.collector?.riwl } : null,
        collectorRunMs: evidence?.collector?.runMs ?? null,
        resourceTiming: result.resourceTiming,
        requestsDuringBuild: result.requestsDuringBuild,
      });
      process.stderr.write(`${browser} r${repeat} ${spec.step}: ${String(bundleInfo.outcome)} ${String(bundleInfo.sha256 ?? "")} (${result.wallMs.toFixed(0)} ms)\n`);
    }
  } catch (error) {
    failure = String(error instanceof Error ? error.stack ?? error.message : error);
    checks.push({ name: "session", pass: false, detail: failure.split("\n")[0]! });
  } finally {
    await session?.close();
  }
  const s = new Map((steps as Array<{ step: string; bundle: { sha256?: string } }>).map((x) => [x.step, x.bundle.sha256]));
  checks.push({ name: "S3 equals S0 (no state leaks from S2)", pass: s.get("S0") !== undefined && s.get("S0") === s.get("S3"), detail: `${s.get("S0")} / ${s.get("S3")}` });
  return {
    browser,
    repeat,
    load,
    wallMs: performance.now() - started,
    profile: session?.profile ?? null,
    freshProfile: `mkdtemp under ${scratchPath("krs-parity-profile-")}, removed after the session`,
    ...(session?.details ?? {}),
    init,
    steps,
    checks,
    pass: checks.every((c) => c.pass),
    failure,
    memory: session?.sampler.summary() ?? null,
    requestLog: session?.requestLog ?? [],
  };
}

const browsers = values.browsers!.split(",") as Array<"chromium" | "firefox">;
const repeats = Number(values.repeats);
const results: Record<string, unknown[]> = {};
let port = Number(values.port);
for (const browser of browsers) {
  results[browser] = [];
  for (let repeat = 1; repeat <= repeats; repeat += 1) {
    const session = await runSession(browser, repeat, port);
    port += 2;
    results[browser]!.push(session);
    for (const c of session.checks) process.stderr.write(`${c.pass ? "PASS" : "FAIL"} ${browser} r${repeat} ${c.name}: ${c.detail.slice(0, 160)}\n`);
  }
  const sessions = results[browser] as Array<{ steps: Array<{ step: string; bundle: { sha256?: string } }> }>;
  const perStep = plan.map((p) => new Set(sessions.map((s) => s.steps.find((x) => x.step === p.step)?.bundle.sha256)));
  const deterministic = perStep.every((set) => set.size === 1 && !set.has(undefined));
  writeFileSync(join(out, `${browser}-evidence.json`), `${JSON.stringify({
    browser,
    pack_id: pack.pack_id,
    pack_krs_revision: pack.krs_revision,
    crates_tree: pack.crates_tree,
    krs_revision: git("rev-parse", "HEAD"),
    oracle: { base: oracle.oracle.bundle_sha256, e1: oracle.oracle_e1.bundle_sha256, krs_revision: oracle.krs_revision },
    deterministicAcrossSessions: deterministic,
    sessions,
  }, null, 1)}\n`);
}

const all = Object.values(results).flat() as Array<{ browser: string; repeat: number; pass: boolean; checks: Check[] }>;
const pass = all.length === browsers.length * repeats && all.every((s) => s.pass);
writeFileSync(join(out, "gate.json"), `${JSON.stringify({
  pass,
  krs_revision: git("rev-parse", "HEAD"),
  oracle_toml: oracleToml,
  oracle_revision: oracle.krs_revision,
  validity: current,
  sessions: all.map((s) => ({ browser: s.browser, repeat: s.repeat, pass: s.pass, failed: s.checks.filter((c) => !c.pass).map((c) => c.name) })),
}, null, 1)}\n`);
process.stderr.write(`tour-minimal parity gate: ${pass ? "PASS" : "FAIL"}\n`);
process.exit(pass ? 0 : 1);
