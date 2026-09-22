// IR-18 gate: browser diagnostics against native diagnostics, per case.
//
//   bun test/parity/diagnostics.ts [--native DIR] [--assets DIR] [--site DIR] [--out DIR]
//       [--browsers chromium,firefox] [--load-max 40]
//
// Prerequisite: native-diagnostics.sh (the native baseline and twin controls) at
// this revision, over the same staged assets. Every case in cases.ts runs through
// the IR-15 worker API (runSource) in one fresh-profile page session per browser.
// For the lowering cases (D003, D008) the browser bundle is lowered natively by
// krs-cli (`krs check` with the cargo shim substituting the collector's stdout),
// because IR-19's Wasm lowering does not exist yet; these are labeled
// "native lowering of the browser bundle".
//
// Classification is mechanical on both sides: native rustc from the primary
// span (authored file and no expansion: exact-authored; an expansion:
// invocation-level; no span: unmappable), krs-cli from the DiagnosticEnvelope
// authored_range (unstructured text: unmappable), collector stderr unmappable;
// browser from the worker's Diagnostic.class (krs_expand_lookup over the IR-10
// map). Parity requires equal stage, code, message, and class, equal authored
// ranges when both sides carry one, the same number of diagnostics per compile,
// no authored range on generated-only or unmappable browser diagnostics, and
// identical classification in Chromium and Firefox. Labels, notes, and helps are
// compared and reported but do not gate.

import { cpSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseArgs } from "node:util";
import type { LessonManifest } from "../../src/protocol.ts";
import { parseStderr, reportable, type RustcDiagnostic } from "../../src/rustc.ts";
import { launch, type BrowserSession } from "../browser/drivers.ts";
import { FORK_IR04 } from "../scenarios.ts";
import { CASES, fixtureText, lessonManifest, resolveFault, type DiagnosticCase, type Stage } from "./cases.ts";

const { values } = parseArgs({
  options: {
    native: { type: "string", default: "/var/tmp/krs-ir18-native" },
    assets: { type: "string", default: "/var/tmp/krs-ir18-assets-r26" },
    site: { type: "string", default: "/var/tmp/krs-ir18-site" },
    out: { type: "string", default: "/var/tmp/krs-ir18-run/evidence" },
    scratch: { type: "string", default: "/var/tmp/krs-ir18-run/scratch" },
    browsers: { type: "string", default: "chromium,firefox" },
    "krs-bin": { type: "string", default: "/var/tmp/krs-ir17-cli-target/debug/krs" },
    "load-max": { type: "string", default: "40" },
    port: { type: "string", default: "4355" },
  },
});
const here = import.meta.dir;
const workerRoot = join(here, "../..");
const nativeDir = values.native!;
const out = values.out!;
const scratch = values.scratch!;
rmSync(out, { recursive: true, force: true });
mkdirSync(out, { recursive: true });
mkdirSync(scratch, { recursive: true });
const sha256 = (bytes: Uint8Array | string) => new Bun.CryptoHasher("sha256").update(bytes).digest("hex");
const repo = Bun.spawnSync(["git", "-C", here, "rev-parse", "--show-toplevel"]).stdout.toString().trim();
const head = Bun.spawnSync(["git", "-C", repo, "rev-parse", "HEAD"]).stdout.toString().trim();

async function waitForLoad(): Promise<number> {
  const max = Number(values["load-max"]);
  for (;;) {
    const load = Number(readFileSync("/proc/loadavg", "utf8").split(" ")[0]);
    if (load <= max) return load;
    process.stderr.write(`load ${load} > ${max}, waiting 60 s\n`);
    await Bun.sleep(60_000);
  }
}

// ---------------------------------------------------------------- normalized diagnostics

type MappingClass = "exact-authored" | "invocation-level" | "generated-only" | "unmappable";
interface Normalized {
  stage: Stage;
  code: string | null;
  level: string;
  /** null only for D007, whose native side is a successful compile. */
  message: string | null;
  class: MappingClass;
  authored: [number, number] | null;
  generated?: { file: string; range: [number, number] } | null;
  label?: string | null;
  children?: string[];
  /** rustc only: the primary span's macro-origin context (`expansion.macro_decl_name`) and file. */
  macroOrigin?: string | null;
  spanFile?: string | null;
  producer: string;
}

/** Native rustc JSON (cargo --message-format=json) -> reportable diagnostics. */
function cargoDiagnostics(path: string): RustcDiagnostic[] {
  const list: RustcDiagnostic[] = [];
  for (const line of readFileSync(path, "utf8").split("\n")) {
    if (!line.startsWith("{")) continue;
    const value = JSON.parse(line) as { reason?: string; message?: RustcDiagnostic };
    if (value.reason === "compiler-message" && value.message) list.push(value.message);
  }
  return reportable(list);
}

interface SpanWithExpansion {
  file_name: string;
  byte_start: number;
  byte_end: number;
  is_primary: boolean;
  label: string | null;
  expansion?: unknown;
}
const children = (d: RustcDiagnostic) => d.children.map((c) => `${c.level}: ${c.message}`);

function nativeRustc(d: RustcDiagnostic, stage: Stage, authoredFile: string): Normalized {
  const span = (d.spans as SpanWithExpansion[]).find((s) => s.is_primary) ?? null;
  let klass: MappingClass = "unmappable";
  if (span && span.file_name.endsWith(authoredFile)) klass = span.expansion ? "invocation-level" : "exact-authored";
  return {
    stage,
    code: d.code?.code ?? null,
    level: d.level,
    message: d.message,
    class: klass,
    authored: span && klass !== "unmappable" ? [span.byte_start, span.byte_end] : null,
    label: span?.label ?? null,
    children: children(d),
    macroOrigin: (span?.expansion as { macro_decl_name?: string } | undefined)?.macro_decl_name ?? null,
    spanFile: span?.file_name ?? null,
    producer: stage === "expander" ? "krs-macros compile_error! (rustc JSON)" : "rustc +stable (native proc macros)",
  };
}

/** krs-cli stderr: DiagnosticEnvelope JSON lines, or unstructured `krs: <error>`. */
function krsCli(stderr: string): Normalized[] {
  return stderr.split("\n").filter((l) => l.trim() !== "").map((line) => {
    if (line.startsWith("{")) {
      const e = JSON.parse(line) as { stage: string; code: string; severity: string; message: string; authored_range?: { start_byte: number; end_byte: number } | null; notes?: string[] };
      return {
        stage: "lowering" as Stage,
        code: e.code,
        level: e.severity,
        message: e.message,
        class: e.authored_range ? ("exact-authored" as MappingClass) : ("unmappable" as MappingClass),
        authored: e.authored_range ? ([e.authored_range.start_byte, e.authored_range.end_byte] as [number, number]) : null,
        children: e.notes ?? [],
        producer: `krs-cli DiagnosticEnvelope (stage ${e.stage})`,
      };
    }
    return { stage: "lowering" as Stage, code: null, level: "error", message: line.replace(/^krs: /, ""), class: "unmappable" as MappingClass, authored: null, children: [], producer: "krs-cli unstructured error" };
  });
}

function collectorStderr(stderr: string): Normalized[] {
  return stderr.split("\n").filter((l) => l.trim() !== "").map((line) => ({
    stage: "collector" as Stage,
    code: null,
    level: "error",
    message: line.replace(/^KRS collector failed: /, ""),
    class: "unmappable" as MappingClass,
    authored: null,
    producer: "native collector binary (krs emit-k build) stderr",
  }));
}

const read = (...parts: string[]) => readFileSync(join(nativeDir, "cases", ...parts), "utf8");

function nativeFor(c: DiagnosticCase): { diagnostics: Normalized[]; compile: Normalized[]; raw: Record<string, string>; note?: string } {
  switch (c.id) {
    case "D001":
    case "D002":
    case "D004": {
      const dir = c.id === "D001" ? "D001" : "D002-D004";
      const all = cargoDiagnostics(join(nativeDir, "cases", dir, "cargo.jsonl")).map((d) => nativeRustc(d, c.nativeStage, c.fixture.split("/").pop()!));
      return { diagnostics: c.nativeSelect ? c.nativeSelect.map((i) => all[i]!) : all, compile: all, raw: { "cargo.jsonl": read(dir, "cargo.jsonl") } };
    }
    case "X1":
    case "X2": {
      const all = cargoDiagnostics(join(nativeDir, "cases", c.id, "cargo.jsonl")).map((d) => nativeRustc(d, "rustc", "src/lib.rs"));
      return { diagnostics: all, compile: all, raw: { "cargo.jsonl": read(c.id, "cargo.jsonl") } };
    }
    case "D003":
    case "D008": {
      const all = krsCli(read(c.id, "stderr"));
      return { diagnostics: all, compile: all, raw: { stderr: read(c.id, "stderr"), exit: read(c.id, "exit") } };
    }
    case "D005":
    case "D006": {
      const all = collectorStderr(read(c.id, "collector.stderr"));
      return {
        diagnostics: all,
        compile: all,
        raw: { "collector.stderr": read(c.id, "collector.stderr"), "collector.exit": read(c.id, "collector.exit"), "bl006-probe.json": read(c.id, "bl006-probe.json") },
        note: `BL-006 anchor-probe at this revision: ${read(c.id, "bl006-probe.json").trim()}`,
      };
    }
    case "D007": {
      const exit = read("D007", "exit").trim();
      const target: Normalized = {
        stage: "policy",
        code: "krs::policy::non-krs-proc-macro",
        level: "error",
        // No native message exists (native cargo check succeeds); the message is reported, not compared.
        message: null,
        class: "exact-authored",
        authored: [9, 25],
        producer: `BL-006 contract target; native cargo check exit ${exit} with ${cargoDiagnostics(join(nativeDir, "cases/D007/cargo.jsonl")).length} diagnostics`,
      };
      return { diagnostics: [target], compile: [target], raw: { "cargo.jsonl": read("D007", "cargo.jsonl"), exit } };
    }
    case "D009": {
      // Native producer: the x86_64 twin of rustc.wasm (same fork commit) compiling the same faulted
      // expanded text against the pack; classified with the same map (twin control).
      const mapped = JSON.parse(read("D009", "twin", "twin-mapped.json")) as Array<{ code: string | null; severity: string; message: string; class: MappingClass; authored: { start: number; end: number } | null; generated: { file: string; start: number; end: number } | null }>;
      const all = mapped.map((d) => ({
        stage: "rustc" as Stage,
        code: d.code,
        level: d.severity,
        message: d.message,
        class: d.class,
        authored: d.authored ? ([d.authored.start, d.authored.end] as [number, number]) : null,
        generated: d.generated ? { file: d.generated.file, range: [d.generated.start, d.generated.end] as [number, number] } : null,
        producer: "native twin rustc (x86_64, same fork commit) on the same faulted expanded text, classified by the same map",
      }));
      return { diagnostics: all, compile: all, raw: { "twin.stderr": read("D009", "twin", "twin.stderr") } };
    }
  }
  throw new Error(`no native baseline for ${c.id}`);
}

// ---------------------------------------------------------------- browser side

interface BrowserDiagnostic {
  origin: "policy" | "expander" | "rustc" | "collector";
  code: string | null;
  severity: string;
  message: string;
  class: MappingClass;
  authored: { file: string; start: number; end: number } | null;
  generated: { file: string; start: number; end: number } | null;
  rendered?: string;
}

function browserNormalized(d: BrowserDiagnostic): Normalized {
  return {
    stage: d.origin,
    code: d.code,
    level: d.severity,
    message: d.message,
    class: d.class,
    authored: d.authored ? [d.authored.start, d.authored.end] : null,
    generated: d.generated ? { file: d.generated.file, range: [d.generated.start, d.generated.end] } : null,
    producer: `worker (${d.origin})`,
  };
}

/** Lowers a browser bundle natively: krs check with the cargo shim returning the bundle as the collector's stdout. */
function lowerNatively(c: DiagnosticCase, bundlePath: string): { stderr: string; exit: number } {
  const pkg = c.id === "D003" ? ["wrong-result", "bl006-wrong-result"] : ["overlap", "bl006-overlap"];
  const z3 = process.env.KRS_Z3_LIB ?? "/nix/store/bncr69nhmgvphbynb1a3g4a2jb9b8vj0-z3-4.12.5-lib/lib";
  const result = Bun.spawnSync(
    ["nice", "-n", "19", values["krs-bin"]!, "check", "--manifest-path", join(nativeDir, "workspace", pkg[0]!, "Cargo.toml"), "--package", pkg[1]!, "--definition", "main"],
    {
      env: { ...process.env, PATH: `${join(nativeDir, "lower-shim")}:${process.env.PATH}`, KRS_IR18_BUNDLE: bundlePath, LD_LIBRARY_PATH: z3, CARGO_TARGET_DIR: join(nativeDir, "target-krs") },
      stdout: "pipe",
      stderr: "pipe",
    },
  );
  return { stderr: result.stderr.toString(), exit: result.exitCode };
}

interface CaseRun {
  id: string;
  wallMs: number;
  terminal: Record<string, unknown> | null;
  diagnostics: Normalized[];
  rawDiagnostics: BrowserDiagnostic[];
  rustcRaw: { lesson: string | null; collector: string | null };
  bundle?: { path: string; sha256: string; bytes: number; equalsNative: boolean };
  lowering?: { stderr: string; exit: number; label: string };
  fault?: unknown;
}

async function runBrowser(browser: "chromium" | "firefox", port: number, tour: LessonManifest) {
  const runs: CaseRun[] = [];
  let session: BrowserSession | null = null;
  let failure: string | null = null;
  const rawDir = join(out, browser);
  mkdirSync(rawDir, { recursive: true });
  const load = await waitForLoad();
  try {
    session = await launch(browser, { site: values.site!, port, profilePrefix: "/var/tmp/krs-ir18-" });
    await session.evaluate("return await window.ir15.init();");
    for (const c of CASES) {
      session.sampler.phase = c.id;
      const lesson = lessonManifest(c.lesson, tour);
      const request = { label: c.id, source: fixtureText(c.fixture), lesson, debugEvidence: true, keepBundle: true, faultInjection: resolveFault(c.faultInjection) };
      const result = (await session.evaluate(`return await window.ir15.runSource(${JSON.stringify(request)});`)) as { wallMs: number; events: Array<Record<string, any>> };
      const terminal = result.events.find((e) => e.type === "success" || e.type === "failure" || e.type === "cancelled") ?? null;
      const rawDiagnostics = result.events.filter((e) => e.type === "diagnostics").flatMap((e) => e.entries as BrowserDiagnostic[]);
      const evidence = terminal?.evidence as { rustc?: { lesson?: { stderr: string }; collector?: { stderr: string } }; fault?: unknown } | undefined;
      const run: CaseRun = {
        id: c.id,
        wallMs: result.wallMs,
        terminal: terminal ? { type: terminal.type, stage: terminal.stage, code: terminal.code, message: terminal.message, bundleSha256: terminal.bundleSha256 } : null,
        diagnostics: rawDiagnostics.map(browserNormalized),
        rawDiagnostics,
        rustcRaw: { lesson: evidence?.rustc?.lesson?.stderr ?? null, collector: evidence?.rustc?.collector?.stderr ?? null },
        fault: evidence?.fault,
      };
      if (terminal?.type === "success" && c.nativeLoweringOfBrowserBundle) {
        const bytes = Uint8Array.from(atob(terminal.bundle.base64 as string), (ch) => ch.charCodeAt(0));
        const path = join(scratch, `${browser}-${c.id}-bundle.json`);
        writeFileSync(path, bytes);
        const nativeBundle = new Uint8Array(readFileSync(join(nativeDir, "cases", c.id, "native-bundle.json")));
        run.bundle = { path, sha256: sha256(bytes), bytes: bytes.length, equalsNative: bytes.length === nativeBundle.length && bytes.every((b, i) => b === nativeBundle[i]) };
        const lowered = lowerNatively(c, path);
        run.lowering = { ...lowered, label: "native lowering of the browser bundle (krs check, collector stdout replaced by the browser bundle); IR-19 has no Wasm lowering yet" };
        run.diagnostics = [...run.diagnostics, ...krsCli(lowered.stderr)];
      }
      // Raw worker events per case (bundle bytes dropped; kept in scratch).
      const scrub = (value: unknown): unknown => {
        if (Array.isArray(value)) return value.map(scrub);
        if (value && typeof value === "object") return Object.fromEntries(Object.entries(value).filter(([k]) => k !== "base64").map(([k, v]) => [k, scrub(v)]));
        return value;
      };
      writeFileSync(join(rawDir, `${c.id}.json`), `${JSON.stringify({ case: c.id, browser, request: { ...request, source: undefined, sourceSha256: sha256(request.source), lesson: lesson.lesson }, events: scrub(result.events), bundle: run.bundle ?? null, lowering: run.lowering ?? null }, null, 1)}\n`);
      if (run.rustcRaw.lesson) writeFileSync(join(rawDir, `${c.id}.rustc-lesson.unmapped.stderr`), run.rustcRaw.lesson);
      runs.push(run);
      process.stderr.write(`${browser} ${c.id}: ${String(run.terminal?.type)} ${String(run.terminal?.stage ?? "")}/${String(run.terminal?.code ?? "")} ${run.diagnostics.length} diagnostic(s) (${result.wallMs.toFixed(0)} ms)\n`);
    }
  } catch (error) {
    failure = String(error instanceof Error ? error.stack ?? error.message : error);
  } finally {
    await session?.close();
  }
  return { browser, load, runs, failure, details: session?.details ?? {}, memory: session?.sampler.summary() ?? null };
}

// ---------------------------------------------------------------- comparison

interface FieldResult {
  field: string;
  native: unknown;
  browser: unknown;
  equal: boolean;
  gating: boolean;
}

function compareOne(n: Normalized, b: Normalized | undefined): FieldResult[] {
  const f = (field: string, native: unknown, browser: unknown, gating = true): FieldResult => ({ field, native, browser, equal: JSON.stringify(native) === JSON.stringify(browser), gating });
  if (!b) return [f("present", true, false)];
  const rows = [f("stage", n.stage, b.stage), f("code", n.code, b.code), f("message", n.message, b.message, n.message !== null), f("class", n.class, b.class)];
  if (n.authored !== null || b.authored !== null) rows.push(f("authored", n.authored, b.authored));
  return rows;
}

function labelsAndNotes(c: DiagnosticCase, native: Normalized, browserRun: CaseRun, index: number): FieldResult[] {
  if (native.stage !== "rustc" && native.stage !== "expander") return [];
  const raw = browserRun.rustcRaw.lesson ? reportable(parseStderr(browserRun.rustcRaw.lesson).diagnostics) : [];
  const b = raw[index];
  if (!b || native.producer.startsWith("native twin")) return [];
  const span = (b.spans as SpanWithExpansion[]).find((s) => s.is_primary) ?? null;
  const browserOrigin = (span?.expansion as { macro_decl_name?: string } | undefined)?.macro_decl_name ?? null;
  return [
    { field: "label", native: native.label ?? null, browser: span?.label ?? null, equal: (native.label ?? null) === (span?.label ?? null), gating: false },
    { field: "children", native: native.children ?? [], browser: children(b), equal: JSON.stringify(native.children ?? []) === JSON.stringify(children(b)), gating: false },
    { field: "macro_origin", native: native.macroOrigin ?? null, browser: browserOrigin, equal: (native.macroOrigin ?? null) === browserOrigin, gating: false },
    // rustc's own span file (and so its `rendered` text): the authored file natively, the generated file in the browser.
    { field: "rustc_span_file", native: native.spanFile ?? null, browser: span?.file_name ?? null, equal: (native.spanFile ?? null) === (span?.file_name ?? null), gating: false },
  ];
}

// ---------------------------------------------------------------- main

const tour = JSON.parse(readFileSync(join(values.assets!, "lessons/tour-minimal/lesson.json"), "utf8")) as LessonManifest;
const pack = JSON.parse(readFileSync(join(values.assets!, "pack.json"), "utf8")) as { pack_id: string; fork_revision: string; krs_revision: string; crates_tree: string };
const nativeProvenance = readFileSync(join(nativeDir, "provenance.txt"), "utf8");
if (!nativeProvenance.includes(`crates_tree = ${pack.crates_tree}`)) {
  process.stderr.write(`native baseline ${nativeDir} is not for the pack's crates tree ${pack.crates_tree}; rerun native-diagnostics.sh\n`);
  process.exit(3);
}
for (const c of CASES) {
  if (c.bl006Sha256 && sha256(fixtureText(c.fixture)) !== c.bl006Sha256) throw new Error(`${c.fixture} differs from the BL-006 fixture`);
}
await waitForLoad();
const site = Bun.spawnSync(["bun", "scripts/build-site.ts", "--out", values.site!, "--assets", values.assets!], { cwd: workerRoot, stderr: "pipe" });
if (site.exitCode !== 0) throw new Error(site.stderr.toString());

const browsers = values.browsers!.split(",") as Array<"chromium" | "firefox">;
const sessions = [];
let port = Number(values.port);
for (const browser of browsers) {
  sessions.push(await runBrowser(browser, port, tour));
  port += 2;
}

const cases = CASES.map((c) => {
  const native = nativeFor(c);
  const perBrowser = sessions.map((s) => {
    const run = s.runs.find((r) => r.id === c.id);
    if (!run) return { browser: s.browser, ran: false, pass: false, fields: [], notes: [] as FieldResult[], problems: ["case did not run"], run: null };
    const problems: string[] = [];
    const selected = c.nativeSelect ? c.nativeSelect.map((i) => run.diagnostics[i]) : run.diagnostics;
    const fields = native.diagnostics.flatMap((n, i) => compareOne(n, selected[i]).map((r) => ({ ...r, index: i })));
    const notes = native.diagnostics.flatMap((n, i) => labelsAndNotes(c, n, run, c.nativeSelect ? c.nativeSelect[i]! : i));
    if (run.diagnostics.length !== native.compile.length) problems.push(`the compile reported ${run.diagnostics.length} diagnostic(s), native ${native.compile.length}`);
    for (const d of run.rawDiagnostics) {
      if ((d.class === "generated-only" || d.class === "unmappable") && d.authored !== null) problems.push(`${d.class} diagnostic carries an authored range`);
    }
    for (const r of fields) if (r.gating && !r.equal) problems.push(`${r.field}: native ${JSON.stringify(r.native)} browser ${JSON.stringify(r.browser)}`);
    if (c.nativeLoweringOfBrowserBundle && !run.bundle?.equalsNative) problems.push("browser bundle differs from the native collector bundle");
    return { browser: s.browser, ran: true, pass: problems.length === 0, fields, notes, problems, run };
  });
  const classes = perBrowser.map((p) => JSON.stringify(p.run?.rawDiagnostics.map((d) => [d.class, d.authored?.start, d.authored?.end]) ?? null));
  const crossBrowser = classes.every((x) => x === classes[0]);
  const pass = perBrowser.every((p) => p.pass) && crossBrowser;
  // IR-26 (fork 0ce51e933) fixed the rustc.wasm trap; the blocker applies only to the IR-04 fork.
  const blocked = c.blockedBy !== undefined && pack.fork_revision === FORK_IR04;
  return { case: c, native, perBrowser, crossBrowser, pass, blocked, status: pass ? "match" : blocked ? `blocked-by ${c.blockedBy!.ticket}` : "mismatch" };
});

// Raw native evidence per case.
const nativeOut = join(out, "native");
mkdirSync(nativeOut, { recursive: true });
for (const c of cases) for (const [name, text] of Object.entries(c.native.raw)) writeFileSync(join(nativeOut, `${c.case.id}.${name}`), text);
for (const extra of ["provenance.txt", "fixtures.sha256", "cases.sha256"]) if (existsSync(join(nativeDir, extra))) cpSync(join(nativeDir, extra), join(nativeOut, extra));
for (const id of ["D002-D004", "D009", "X1", "X2"]) {
  const dir = join(nativeDir, "cases", id, "twin");
  if (existsSync(dir)) for (const f of ["twin.stderr", "twin-mapped.json", "expand.json"]) if (existsSync(join(dir, f))) cpSync(join(dir, f), join(nativeOut, `${id}.twin.${f}`));
}

// ---------------------------------------------------------------- comparison-contract.toml

const q = (v: unknown) => JSON.stringify(v ?? "");
const range = (r: [number, number] | null | undefined) => (r ? `[${r[0]}, ${r[1]}]` : "[]");
const lines: string[] = [
  "# IR-18 comparison contract: BL-006 schema plus stage, path, and generated_* fields (browser side).",
  "# Generated by browser/worker/test/parity/diagnostics.ts; do not edit by hand.",
  "schema_version = 2",
  'ticket = "IR-18"',
  'classification_values = ["exact-authored", "invocation-level", "generated-only", "unmappable"]',
  'stage_values = ["expander", "policy", "rustc", "collector", "lowering"]',
  'path = "C"',
  `krs_revision = ${q(head)}`,
  `pack_id = ${q(pack.pack_id)}`,
  `fork_revision = ${q(pack.fork_revision)}`,
  `crates_tree = ${q(pack.crates_tree)}`,
  "",
];
for (const r of cases) {
  const c = r.case;
  lines.push("[[case]]", `id = ${q(c.id)}`, `title = ${q(c.title)}`, `fixture = ${q(`browser/worker/test/fixtures/${c.fixture}`)}`, `fixture_sha256 = ${q(sha256(fixtureText(c.fixture)))}`, `lesson = ${q(c.lesson)}`);
  if (c.faultInjection) lines.push(`fault_injection = ${q(c.faultInjection.kind)}`);
  lines.push(`native_stage = ${q(c.nativeStage)}`, `status = ${q(r.status)}`, `cross_browser_identical = ${r.crossBrowser}`);
  if (r.blocked) lines.push(`blocked_by = ${q(c.blockedBy!.ticket)}`, `blocked_reason = ${q(c.blockedBy!.reason)}`);
  else if (c.blockedBy) lines.push(`formerly_blocked_by = ${q(`${c.blockedBy.ticket} (fork ${FORK_IR04.slice(0, 9)}); fixed in the pack's fork`)}`);
  if (c.nativeLoweringOfBrowserBundle) lines.push('lowering = "native lowering of the browser bundle (IR-19 pending)"');
  lines.push(`note = ${q(c.note)}`);
  r.native.diagnostics.forEach((n, i) => {
    lines.push("[[case.native]]", `index = ${i}`, `producer = ${q(n.producer)}`, `stage = ${q(n.stage)}`, `code = ${q(n.code)}`, `level = ${q(n.level)}`, `message = ${q(n.message)}`, `class = ${q(n.class)}`, `authored = ${range(n.authored)}`);
    if (n.generated) lines.push(`generated_file = ${q(n.generated.file)}`, `generated = ${range(n.generated.range)}`);
    if (n.label !== undefined) lines.push(`label = ${q(n.label)}`);
    if (n.children) lines.push(`children = [${n.children.map(q).join(", ")}]`);
  });
  if (r.native.note) lines.push(`native_reference = ${q(r.native.note)}`);
  for (const p of r.perBrowser) {
    const run = p.run;
    lines.push("[[case.browser]]", `browser = ${q(p.browser)}`, `pass = ${p.pass}`, `terminal = ${q(run?.terminal ? `${String(run.terminal.type)} ${String(run.terminal.stage ?? "")}/${String(run.terminal.code ?? "")}` : "none")}`);
    if (run?.bundle) lines.push(`bundle_sha256 = ${q(run.bundle.sha256)}`, `bundle_equals_native = ${run.bundle.equalsNative}`);
    if (p.problems.length > 0) lines.push(`problems = [${p.problems.map(q).join(", ")}]`);
    const differing = p.notes.filter((n) => !n.equal);
    if (differing.length > 0) lines.push(`label_note_differences = [${differing.map((n) => q(`${n.field}: native ${JSON.stringify(n.native)} browser ${JSON.stringify(n.browser)}`)).join(", ")}]`);
    (run?.diagnostics ?? []).forEach((d, i) => {
      lines.push("[[case.browser.diagnostic]]", `index = ${i}`, `stage = ${q(d.stage)}`, `code = ${q(d.code)}`, `level = ${q(d.level)}`, `message = ${q(d.message)}`, `class = ${q(d.class)}`, `authored = ${range(d.authored)}`);
      if (d.generated) lines.push(`generated_file = ${q(d.generated.file)}`, `generated = ${range(d.generated.range)}`);
      else lines.push('generated_file = ""', "generated = []");
    });
  }
  lines.push("");
}
writeFileSync(join(out, "comparison-contract.toml"), `${lines.join("\n")}\n`);

const summary = {
  pass: cases.every((r) => r.pass || r.blocked),
  krs_revision: head,
  pack,
  sessions: sessions.map((s) => ({ browser: s.browser, load: s.load, failure: s.failure, details: s.details, peakPssMiB: s.memory?.peakPss ? Math.round(s.memory.peakPss.pssKb / 1024) : null })),
  cases: cases.map((r) => ({
    id: r.case.id,
    status: r.status,
    crossBrowser: r.crossBrowser,
    native: r.native.diagnostics.map((n) => ({ stage: n.stage, code: n.code, class: n.class, authored: n.authored, message: n.message })),
    browsers: r.perBrowser.map((p) => ({
      browser: p.browser,
      pass: p.pass,
      problems: p.problems,
      terminal: p.run?.terminal ?? null,
      diagnostics: p.run?.diagnostics.map((d) => ({ stage: d.stage, code: d.code, class: d.class, authored: d.authored, generated: d.generated ?? null })) ?? [],
      labelNoteDifferences: p.notes.filter((n) => !n.equal),
      wallMs: p.run?.wallMs ?? null,
      fault: p.run?.fault ?? null,
      lowering: p.run?.lowering ? { exit: p.run.lowering.exit, label: p.run.lowering.label } : null,
      bundle: p.run?.bundle ? { sha256: p.run.bundle.sha256, bytes: p.run.bundle.bytes, equalsNative: p.run.bundle.equalsNative } : null,
    })),
  })),
};
writeFileSync(join(out, "comparison.json"), `${JSON.stringify(summary, null, 1)}\n`);
for (const r of cases) process.stderr.write(`${r.case.id}: ${r.status}${r.perBrowser.some((p) => p.problems.length) ? ` (${r.perBrowser.map((p) => `${p.browser}: ${p.problems.join("; ")}`).join(" | ")})` : ""}\n`);
process.stderr.write(`IR-18 gate: ${summary.pass ? "PASS" : "FAIL"}\n`);
process.exit(summary.pass ? 0 : 1);
