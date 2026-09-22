// Stage functions of the browser compiler pipeline (IR-15), independent of the
// worker global so that tests and the Node/Bun runner call them directly.
//
//   assets -> policy (IR-13 module) -> expand (IR-11 module) -> rustc-lesson
//   -> rustc-collector (riwl links in-process) -> collect (WASI) -> bundle
//
// VFS for rustc.wasm (one preopen per layer):
//   /sysroot    immutable  sysroot bundle (RIWB1), at the pack's sysroot.mount
//   /pack       immutable  deps/ (target rlibs, sysroot supplement), proc-macro-meta/
//   /krs        immutable  framework sources (IR-12)
//   /workspace  per build  <lesson>/Cargo.toml, <lesson>/<display_file> (authored)
//   /work       per build  expanded/<lesson>/<display_file>, collector/main.rs, out/
//   /tmp        per run    empty
// The collector sees one preopen, "/", holding only /krs and /workspace (IR-12).

import { renderCollectorMain } from "./collector-template.ts";
import { fromCollector, fromExpander, fromPolicy, fromRustc, lookupRanges } from "./diagnostics.ts";
import { runExpander, runLookup, runPolicy, type ExpandResponse } from "./modules.ts";
import { checkActivation, sha256Hex } from "./pack.ts";
import type {
  CompileEvent,
  CompileRequest,
  Diagnostic,
  Evidence,
  FailureCode,
  LessonManifest,
  MemorySample,
  PackManifest,
  RustcRecord,
  Stage,
  VerifiedAssets,
  VfsEntry,
} from "./protocol.ts";
import {
  classifyRustc,
  collectorInvocation,
  COLLECTOR_MAIN,
  expandedPath,
  type Invocation,
  lessonInvocation,
  parseStderr,
  reportable,
} from "./rustc.ts";
import { Directory, File, PreopenDirectory } from "../vendor/browser_wasi_shim/index.js";
import { insert, listDirectory, merge, parseSysrootBundle, preopen, readFile, readOnlyTree, type Tree } from "./vfs.ts";
import { runCommand } from "./wasi.ts";

// ---------------------------------------------------------------- context

export interface PipelineContext {
  pack: PackManifest;
  modules: VerifiedAssets["modules"];
  /** Immutable layers, built once from verified bytes. */
  layers: { sysroot: Tree; pack: Tree; krs: Tree };
  activationProblems: string[];
}

function stripPrefix(path: string, prefix: string): string {
  if (!path.startsWith(`${prefix}/`)) throw new Error(`${path} is not under ${prefix}`);
  return path.slice(prefix.length + 1);
}

export function createPipelineContext(pack: PackManifest, assets: VerifiedAssets): PipelineContext {
  const activationProblems = checkActivation(pack, assets);
  const sysrootFiles = parseSysrootBundle(assets.sysrootBundle);
  const packEntries: Array<[string, Uint8Array]> = pack.artifacts.map((a) => [stripPrefix(a.mount, "/pack"), assets.files[a.path]!]);
  const krsEntries: Array<[string, Uint8Array]> = pack.framework_sources.map((s) => [stripPrefix(s.mount, "/krs"), assets.files[s.path]!]);
  return {
    pack,
    modules: assets.modules,
    layers: { sysroot: readOnlyTree(sysrootFiles), pack: readOnlyTree(packEntries), krs: readOnlyTree(krsEntries) },
    activationProblems,
  };
}

// ---------------------------------------------------------------- build state

export class StageFailure extends Error {
  readonly stage: Stage;
  readonly code: FailureCode;
  readonly diagnostics: Diagnostic[];
  /** A trapped instance may leave shim objects inconsistent (IR-15 assumption). */
  readonly replaceWorker: boolean;
  constructor(stage: Stage, code: FailureCode, message: string, diagnostics: Diagnostic[] = [], replaceWorker = false) {
    super(message);
    this.name = "StageFailure";
    this.stage = stage;
    this.code = code;
    this.diagnostics = diagnostics;
    this.replaceWorker = replaceWorker;
  }
}

export interface BuildHooks {
  emit(event: CompileEvent): void;
  /** Host memory probe (process.memoryUsage, performance.memory, ...). */
  memory?(): Record<string, number> | null;
}

export interface Build {
  ctx: PipelineContext;
  request: CompileRequest;
  lesson: LessonManifest;
  hooks: BuildHooks;
  /** Per-build trees and directories; dropped with the build. */
  workspace: Tree;
  work: Directory;
  evidence: Evidence;
  memory: MemorySample[];
  expansion?: { text: string; sourceMap: unknown; response: ExpandResponse };
  lessonRlib?: Uint8Array;
  collectorWasm?: Uint8Array;
  stdout?: Uint8Array;
}

export function createBuild(ctx: PipelineContext, request: CompileRequest, hooks: BuildHooks): Build {
  const lesson = request.lesson;
  const workspace: Tree = new Map();
  const encoder = new TextEncoder();
  const lessonDir = stripPrefix(lesson.package.manifest_dir, "/workspace");
  insert(workspace, `${lessonDir}/Cargo.toml`, new File(encoder.encode(lesson.package.cargo_toml), { readonly: true }));
  for (const [path, text] of Object.entries(request.files)) {
    if (lesson.policy.editable_files.includes(path)) insert(workspace, `${lessonDir}/${path}`, new File(encoder.encode(text), { readonly: true }));
  }
  const work = new Directory([
    ["expanded", new Directory([])],
    ["collector", new Directory([])],
    ["out", new Directory([])],
  ]);
  return {
    ctx,
    request,
    lesson,
    hooks,
    workspace,
    work,
    evidence: { stageMs: {}, rustc: {}, vfs: { rustc: [], collector: [] }, artifacts: {} },
    memory: [],
  };
}

function sample(build: Build, label: string, extra: Record<string, number> = {}): void {
  const values = { ...(build.hooks.memory?.() ?? {}), ...extra };
  if (Object.keys(values).length > 0) build.memory.push({ at: new Date().toISOString(), label, values });
}

function writeWork(build: Build, absolute: string, bytes: Uint8Array): void {
  const relative = stripPrefix(absolute, "/work").split("/");
  const name = relative.pop()!;
  let dir = build.work;
  for (const part of relative) {
    let next = dir.contents.get(part);
    if (next === undefined) {
      next = new Directory([]);
      dir.contents.set(part, next);
    }
    if (!(next instanceof Directory)) throw new Error(`/work path ${absolute} crosses a file`);
    dir = next;
  }
  dir.contents.set(name, new File(bytes));
}

function rustcPreopens(build: Build): PreopenDirectory[] {
  const { layers } = build.ctx;
  return [
    preopen(build.ctx.pack.direct_rustc.sysroot, layers.sysroot),
    preopen("/pack", layers.pack),
    preopen("/krs", layers.krs),
    preopen("/workspace", build.workspace),
    new PreopenDirectory("/work", build.work.contents),
    new PreopenDirectory("/tmp", []),
  ];
}

async function listPreopens(preopens: PreopenDirectory[]): Promise<VfsEntry[]> {
  const out: VfsEntry[] = [];
  for (const dir of preopens) out.push(...(await listDirectory(dir.prestat_name, dir.dir)));
  return out;
}

// ---------------------------------------------------------------- stages

export function stageAssets(build: Build): void {
  const { ctx, lesson } = build;
  if (ctx.activationProblems.length > 0) {
    throw new StageFailure("assets", "pack-integrity", `pack ${ctx.pack.pack_id} is not activated: ${ctx.activationProblems.join("; ")}`);
  }
  if (lesson.schema !== 1) throw new StageFailure("assets", "protocol-mismatch", `lesson manifest schema ${String(lesson.schema)} is not 1`);
  if (lesson.pack_id !== ctx.pack.pack_id) {
    throw new StageFailure("assets", "pack-integrity", `lesson ${lesson.lesson} requires pack ${lesson.pack_id}, the worker holds ${ctx.pack.pack_id}`);
  }
  if (lesson.package.edition !== ctx.pack.direct_rustc.edition) {
    throw new StageFailure("assets", "protocol-mismatch", `lesson edition ${lesson.package.edition} differs from the pack's ${ctx.pack.direct_rustc.edition}`);
  }
  if (lesson.expansion !== "krs-expander") {
    throw new StageFailure("assets", "protocol-mismatch", `expansion mode ${lesson.expansion} is not supported (G1 selected path C)`);
  }
}

export async function stagePolicy(build: Build): Promise<void> {
  const { lesson, request } = build;
  const diagnostics: Diagnostic[] = [];
  for (const path of Object.keys(request.files).sort()) {
    if (!lesson.policy.editable_files.includes(path)) {
      diagnostics.push({
        origin: "policy",
        code: "krs::policy::editable-file",
        severity: "error",
        message: `\`${path}\` is not an editable file of this lesson`,
        class: "unmappable",
        authored: null,
        generated: null,
      });
    }
  }
  if (!(lesson.display_file in request.files)) {
    diagnostics.push({
      origin: "policy",
      code: "krs::policy::editable-file",
      severity: "error",
      message: `the request does not contain \`${lesson.display_file}\``,
      class: "unmappable",
      authored: null,
      generated: null,
    });
  }
  if (diagnostics.length === 0) {
    const response = await runPolicy(build.ctx.modules.policy, { schema: 1, policy: lesson.policy, files: request.files });
    diagnostics.push(...response.diagnostics.map(fromPolicy));
    if (!response.ok && response.diagnostics.length === 0) {
      throw new StageFailure("policy", "policy", "policy module returned ok = false without a diagnostic");
    }
  }
  if (diagnostics.length > 0) {
    build.hooks.emit({ type: "diagnostics", generation: request.generation, origin: "policy", entries: diagnostics });
    throw new StageFailure("policy", "policy", `${diagnostics.length} policy violation(s)`, diagnostics);
  }
}

export async function stageExpand(build: Build): Promise<void> {
  const { lesson, request } = build;
  const source = request.files[lesson.display_file]!;
  const response = await runExpander(build.ctx.modules.expander, {
    schema: 1,
    mode: "whole-file",
    file: { virtual_path: `${lesson.package.manifest_dir}/${lesson.display_file}`, display_file: lesson.display_file, source },
    package: {
      cargo_name: lesson.package.cargo_name,
      cargo_version: lesson.package.cargo_version,
      manifest_dir: lesson.package.manifest_dir,
      crate_name: lesson.package.crate_name,
    },
    module_path: [lesson.package.crate_name],
    facade: lesson.facade,
    generated_file: expandedPath(lesson),
    policy: lesson.policy,
  });
  if (!response.ok || response.expanded === null || response.source_map === null) {
    const diagnostics = response.diagnostics.map(fromExpander);
    const origin = diagnostics.every((d) => d.origin === "policy") && diagnostics.length > 0 ? "policy" : "expander";
    build.hooks.emit({ type: "diagnostics", generation: request.generation, origin, entries: diagnostics });
    throw new StageFailure("expand", origin === "policy" ? "policy" : "expansion", `${diagnostics.length} expansion error(s)`, diagnostics);
  }
  if (response.expanded.generated_file !== expandedPath(lesson)) {
    throw new StageFailure("expand", "protocol-mismatch", `expander wrote ${response.expanded.generated_file}`);
  }
  build.expansion = { text: response.expanded.text, sourceMap: response.source_map, response };
  writeWork(build, expandedPath(lesson), new TextEncoder().encode(response.expanded.text));
  if (request.debugEvidence) {
    build.evidence.expandedText = response.expanded.text;
    build.evidence.expandedSha256 = await sha256Hex(new TextEncoder().encode(response.expanded.text));
    build.evidence.sourceMap = response.source_map;
    build.evidence.registrations = response.registrations;
  }
}

interface RustcRun {
  record: RustcRecord;
  output: Uint8Array | null;
  parsed: ReturnType<typeof parseStderr>;
  run: Awaited<ReturnType<typeof runCommand>>;
}

async function runRustc(build: Build, invocation: Invocation, label: string): Promise<RustcRun> {
  const preopens = rustcPreopens(build);
  if (build.request.debugEvidence && build.evidence.vfs.rustc.length === 0) build.evidence.vfs.rustc = await listPreopens(preopens);
  sample(build, `${label}:before`);
  const run = await runCommand({ module: build.ctx.modules.rustc, args: invocation.args, env: invocation.env, preopens });
  sample(build, `${label}:after`, run.memoryBytes === null ? {} : { rustcWasmMemoryBytes: run.memoryBytes });
  const stderr = new TextDecoder().decode(run.stderr);
  const parsed = parseStderr(stderr);
  const output = readFile(build.work, stripPrefix(invocation.output, "/work"));
  const record: RustcRecord = {
    args: invocation.args,
    env: invocation.env,
    preopens: preopens.map((p) => p.prestat_name),
    exitCode: run.exitCode,
    trap: run.trap,
    stderr,
    instantiateMs: run.instantiateMs,
    runMs: run.runMs,
    memoryBytes: run.memoryBytes,
    riwl: parsed.riwl,
  };
  return { record, output: output && output.byteLength > 0 ? output : null, parsed, run };
}

/** Maps rustc diagnostics of the lesson compile through krs_expand_lookup. */
export async function mapLessonDiagnostics(build: Build, diagnostics: ReturnType<typeof reportable>): Promise<Diagnostic[]> {
  const { lesson } = build;
  const generatedFile = expandedPath(lesson);
  const ranges = lookupRanges(diagnostics, generatedFile).filter((r): r is [number, number] => r !== null);
  let mappings = null;
  if (ranges.length > 0 && build.expansion) {
    const response = await runLookup(build.ctx.modules.expander, {
      schema: 1,
      authored_source: build.request.files[lesson.display_file]!,
      text: build.expansion.text,
      source_map: build.expansion.sourceMap,
      ranges,
    });
    mappings = response.ok ? response.mappings : null;
  }
  return fromRustc(diagnostics, generatedFile, lesson.display_file, mappings);
}

export async function stageRustcLesson(build: Build): Promise<void> {
  const { ctx, lesson, request } = build;
  const invocation = lessonInvocation(ctx.pack, lesson);
  const result = await runRustc(build, invocation, "rustc-lesson");
  build.evidence.rustc.lesson = result.record;
  const entries = await mapLessonDiagnostics(build, reportable(result.parsed.diagnostics));
  if (entries.length > 0) build.hooks.emit({ type: "diagnostics", generation: request.generation, origin: "rustc", entries });
  const outcome = classifyRustc("rustc-lesson", result.run, result.parsed, result.output !== null);
  if (!outcome.ok) {
    const genuineTrap = outcome.code === "compiler-trap" || outcome.code === "out-of-memory";
    throw new StageFailure("rustc-lesson", outcome.code!, outcome.message!, entries.filter((d) => d.severity === "error"), genuineTrap);
  }
  build.lessonRlib = result.output!;
  build.evidence.artifacts.lessonRlib = { bytes: result.output!.byteLength, sha256: await sha256Hex(result.output!) };
}

export async function stageRustcCollector(build: Build): Promise<void> {
  const { ctx, lesson, request } = build;
  writeWork(build, COLLECTOR_MAIN, new TextEncoder().encode(renderCollectorMain(lesson)));
  const invocation = collectorInvocation(ctx.pack, lesson);
  const result = await runRustc(build, invocation, "rustc-collector");
  build.evidence.rustc.collector = result.record;
  const entries = fromRustc(reportable(result.parsed.diagnostics), expandedPath(lesson), lesson.display_file, null);
  if (entries.length > 0) build.hooks.emit({ type: "diagnostics", generation: request.generation, origin: "rustc", entries });
  const outcome = classifyRustc("rustc-collector", result.run, result.parsed, result.output !== null);
  if (!outcome.ok) {
    const genuineTrap = outcome.code === "compiler-trap" || outcome.code === "out-of-memory";
    throw new StageFailure("rustc-collector", outcome.code!, outcome.message!, entries.filter((d) => d.severity === "error"), genuineTrap);
  }
  build.collectorWasm = result.output!;
  build.evidence.artifacts.collectorWasm = { bytes: result.output!.byteLength, sha256: await sha256Hex(result.output!) };
}

export async function stageCollect(build: Build): Promise<void> {
  const { ctx, request } = build;
  const bytes = build.collectorWasm!;
  const compileStarted = performance.now();
  let module: WebAssembly.Module;
  try {
    module = await WebAssembly.compile(bytes as Uint8Array<ArrayBuffer>);
  } catch (error) {
    throw new StageFailure("collect", "link-error", `collector.wasm does not compile: ${String(error)}`);
  }
  const compileMs = performance.now() - compileStarted;
  // One preopen "/" over a tree with only /krs and /workspace (IR-12).
  const root = preopen("/", merge(new Map([["krs", ctx.layers.krs]]), new Map([["workspace", build.workspace]])));
  if (request.debugEvidence) build.evidence.vfs.collector = await listDirectory("/", root.dir);
  const args = ["collector"];
  const run = await runCommand({ module, args, env: [], preopens: [root] });
  sample(build, "collect:after", run.memoryBytes === null ? {} : { collectorWasmMemoryBytes: run.memoryBytes });
  const stderr = new TextDecoder().decode(run.stderr);
  build.evidence.collector = {
    exitCode: run.exitCode,
    trap: run.trap,
    stderr,
    compileMs,
    instantiateMs: run.instantiateMs,
    runMs: run.runMs,
    memoryBytes: run.memoryBytes,
    args,
    env: [],
    preopens: [root.prestat_name],
  };
  if (run.trap !== null) {
    const diagnostics = fromCollector(stderr, run.trap);
    build.hooks.emit({ type: "diagnostics", generation: request.generation, origin: "collector", entries: diagnostics });
    throw new StageFailure("collect", run.trapName === "RangeError" ? "out-of-memory" : "collector-trap", run.trap, diagnostics, true);
  }
  if (run.exitCode !== 0) {
    const diagnostics = fromCollector(stderr, null);
    build.hooks.emit({ type: "diagnostics", generation: request.generation, origin: "collector", entries: diagnostics });
    throw new StageFailure("collect", "collector-error", `collector exited ${run.exitCode}`, diagnostics);
  }
  build.stdout = run.stdout;
}

export async function stageBundle(build: Build): Promise<{ bundle: Uint8Array; sha256: string }> {
  const bytes = build.stdout!;
  let parsed: { protocol_version?: unknown };
  try {
    parsed = JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes)) as { protocol_version?: unknown };
  } catch (error) {
    throw new StageFailure("bundle", "collector-error", `collector stdout is not a JSON bundle: ${String(error)}`);
  }
  if (parsed.protocol_version !== build.ctx.pack.protocol_version) {
    throw new StageFailure(
      "bundle",
      "protocol-mismatch",
      `bundle protocol ${String(parsed.protocol_version)} is not the pack's ${build.ctx.pack.protocol_version}`,
    );
  }
  return { bundle: bytes, sha256: await sha256Hex(bytes) };
}

// ---------------------------------------------------------------- orchestration

const INTERNAL_FAILURE: Record<Stage, FailureCode> = {
  assets: "pack-integrity",
  policy: "policy",
  expand: "expansion",
  "rustc-lesson": "compiler-trap",
  "rustc-collector": "compiler-trap",
  collect: "collector-trap",
  bundle: "collector-error",
};

export interface BuildResult {
  ok: boolean;
  /** The worker should be replaced before the next build (a genuine trap). */
  replaceWorker: boolean;
  build: Build;
}

/** Runs every stage in order and emits progress, diagnostics, and exactly one success or failure. */
export async function runBuild(ctx: PipelineContext, request: CompileRequest, hooks: BuildHooks): Promise<BuildResult> {
  const build = createBuild(ctx, request, hooks);
  const generation = request.generation;
  let stage: Stage = "assets";
  const timed = async <T>(name: Stage, work: () => T | Promise<T>): Promise<T> => {
    stage = name;
    hooks.emit({ type: "progress", generation, stage: name, state: "start" });
    const started = performance.now();
    const value = await work();
    const ms = performance.now() - started;
    build.evidence.stageMs[name] = ms;
    hooks.emit({ type: "progress", generation, stage: name, state: "end", ms });
    return value;
  };
  const withEvidence = () => (request.debugEvidence ? { evidence: { ...build.evidence, memory: build.memory } } : {});
  try {
    sample(build, "build:start");
    await timed("assets", () => stageAssets(build));
    await timed("policy", () => stagePolicy(build));
    await timed("expand", () => stageExpand(build));
    await timed("rustc-lesson", () => stageRustcLesson(build));
    await timed("rustc-collector", () => stageRustcCollector(build));
    await timed("collect", () => stageCollect(build));
    const { bundle, sha256 } = await timed("bundle", () => stageBundle(build));
    sample(build, "build:end");
    hooks.emit({ type: "success", generation, bundle, bundleSha256: sha256, ...withEvidence() });
    return { ok: true, replaceWorker: false, build };
  } catch (error) {
    sample(build, "build:failed");
    if (error instanceof StageFailure) {
      hooks.emit({
        type: "failure",
        generation,
        stage: error.stage,
        code: error.code,
        message: error.message,
        diagnostics: error.diagnostics,
        ...withEvidence(),
      });
      return { ok: false, replaceWorker: error.replaceWorker, build };
    }
    const oom = error instanceof RangeError;
    hooks.emit({
      type: "failure",
      generation,
      stage,
      code: oom ? "out-of-memory" : INTERNAL_FAILURE[stage],
      message: `internal error in stage ${stage}: ${error instanceof Error ? `${error.name}: ${error.message}` : String(error)}`,
      diagnostics: [],
      ...withEvidence(),
    });
    return { ok: false, replaceWorker: true, build };
  }
}

