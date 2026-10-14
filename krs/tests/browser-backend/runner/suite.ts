// Host-independent suite controller: compiles every crate of every case at
// every opt level with one Compiler, runs the case's executions with one
// Executor, and returns raw records. Comparison with expected.json is done by
// verify.py, so every host and both references go through this one code path.

import { sha256Hex } from "../../../browser/worker/src/pack.ts";
import { initFuncCount } from "./objinfo.ts";
import type {
  Blob,
  CaseRecord,
  CompileRecord,
  Compiler,
  DiagnosticSummary,
  Executor,
  RunRecord,
  StepResult,
  SuiteCase,
  SuiteCrate,
  SuiteFile,
  VariantRecord,
} from "./protocol.ts";

export const CASE_ROOT = "/case";
export const OUT_ROOT = "/out";

export function toBlob(bytes: Uint8Array): Blob {
  try {
    return { utf8: new TextDecoder("utf-8", { fatal: true }).decode(bytes) };
  } catch {
    let binary = "";
    for (let i = 0; i < bytes.length; i += 0x8000) binary += String.fromCharCode(...bytes.subarray(i, i + 0x8000));
    return { base64: btoa(binary) };
  }
}

export function fromBlob(blob: Blob): Uint8Array {
  if ("utf8" in blob) return new TextEncoder().encode(blob.utf8);
  return Uint8Array.from(atob(blob.base64), (c) => c.charCodeAt(0));
}

export function outputPath(crate: SuiteCrate): string {
  if (crate.type === "rlib") return `${OUT_ROOT}/lib${crate.name}.rlib`;
  if (crate.type === "bin") return `${OUT_ROOT}/${crate.name}.wasm`;
  return `${OUT_ROOT}/${crate.name}.o`;
}

/** Guest-form rustc arguments; each Compiler adds its own sysroot, search paths, and linker. */
export function crateArgs(suite: SuiteFile, crate: SuiteCrate, optLevel: number): string[] {
  const args = [
    crate.src,
    "--crate-name",
    crate.name,
    "--crate-type",
    crate.type === "obj" ? "rlib" : crate.type,
    "--edition",
    "2024",
    "--target",
    "wasm32-wasip1",
    "-C",
    "panic=abort",
    "-C",
    `opt-level=${optLevel}`,
    "--error-format=json",
    "-L",
    `dependency=${OUT_ROOT}`,
  ];
  if (crate.type === "obj") args.push("--emit", "obj", "-C", "codegen-units=1");
  for (const name of crate.externs) args.push("--extern", `${name}=${OUT_ROOT}/lib${name}.rlib`);
  for (const name of crate.pack) {
    const path = suite.pack.externs[name];
    if (path === undefined) throw new Error(`crate ${crate.name}: pack has no crate ${name}`);
    args.push("--extern", `${name}=/pack/${path}`);
  }
  args.push(...crate.flags, "-o", outputPath(crate));
  return args;
}

interface ParsedStderr {
  errors: DiagnosticSummary[];
  summary: boolean;
  residue: string[];
  linkErrors: string[];
}

export function parseRustcStderr(text: string): ParsedStderr {
  const errors: DiagnosticSummary[] = [];
  const residue: string[] = [];
  let summary = false;
  for (const line of text.split("\n")) {
    if (line.startsWith("{")) {
      try {
        const value = JSON.parse(line) as { $message_type?: string; level?: string; code?: { code: string } | null; message?: string };
        if (value.$message_type === "diagnostic") {
          if (/^aborting due to /.test(value.message ?? "")) summary = true;
          else if (value.level === "error") errors.push({ level: value.level, code: value.code?.code ?? null, message: value.message ?? "" });
          continue;
        }
      } catch {
        // kept as residue
      }
    }
    if (/^riwl-timing: /.test(line) || line.trim() === "") continue;
    residue.push(line);
  }
  return { errors, summary, residue, linkErrors: residue.filter((line) => /^riwl: error/.test(line)) };
}

function compileOutcome(step: StepResult, parsed: ParsedStderr, output: Uint8Array | undefined): CompileRecord["outcome"] {
  if (step.status === "cancelled") return "cancelled";
  if (parsed.errors.length > 0) return "error";
  if (parsed.linkErrors.length > 0 && step.exitCode !== 0) return "link-error";
  if (step.status === "trap" || step.exitCode !== 0 || output === undefined || output.byteLength === 0) return "compiler-trap";
  return "ok";
}

export interface SuiteOptions {
  only?: string[];
  log?: (line: string) => void;
}

async function compileCrates(
  suite: SuiteFile,
  kase: SuiteCase,
  optLevel: number,
  compiler: Compiler,
  sources: Record<string, Uint8Array>,
  label: string,
): Promise<{ records: CompileRecord[]; outputs: Record<string, Uint8Array>; ok: boolean }> {
  const outputs: Record<string, Uint8Array> = {};
  const records: CompileRecord[] = [];
  for (const crate of kase.crates) {
    const target = outputPath(crate);
    // rustc.wasm gets the pack's [direct_rustc] sysroot, -Z flags, and search paths;
    // the native references add their own (runner/node.ts NativeCompiler).
    const fork = compiler.kind === "fork";
    const step = await compiler.rustc({
      args: [...crateArgs(suite, crate, optLevel), ...(fork ? suite.pack.fork_flags : [])],
      env: fork ? suite.pack.fork_env : [],
      files: { ...sources, ...outputs },
      outputs: [target],
      timeoutMs: suite.step_timeout_ms,
    });
    const parsed = parseRustcStderr(new TextDecoder().decode(step.stderr));
    const output = step.outputs[target];
    const outcome = compileOutcome(step, parsed, output);
    if (outcome === "ok") outputs[target] = output!;
    records.push({
      crate: `${crate.name}${label}`,
      outcome,
      errors: outcome === "link-error" ? parsed.linkErrors.map((message) => ({ level: "error", code: null, message })) : parsed.errors,
      summary: parsed.summary,
      exitCode: step.exitCode,
      trap: step.trap,
      residue: parsed.residue.slice(-40),
      outputSha256: outcome === "ok" ? await sha256Hex(output!) : null,
      outputBytes: outcome === "ok" ? output!.byteLength : null,
      initFuncs: outcome === "ok" && crate.inspect === "init-funcs" ? initFuncCount(output!) : null,
      ms: step.ms,
      memoryBytes: step.memoryBytes,
    });
    if (outcome !== "ok") return { records, outputs, ok: false };
  }
  return { records, outputs, ok: true };
}

export async function runCase(suite: SuiteFile, kase: SuiteCase, compiler: Compiler, executor: Executor, log: (line: string) => void): Promise<CaseRecord> {
  const started = performance.now();
  const encoder = new TextEncoder();
  const sources: Record<string, Uint8Array> = {};
  for (const [path, text] of Object.entries(kase.sources)) sources[path] = encoder.encode(text);
  const variants: VariantRecord[] = [];
  for (const optLevel of kase.opt_levels) {
    let compiled = await compileCrates(suite, kase, optLevel, compiler, sources, "");
    const compile = [...compiled.records];
    const runs: RunRecord[] = [];
    for (const run of kase.runs) {
      const bin = kase.crates.find((c) => c.name === run.bin);
      const module = bin ? compiled.outputs[outputPath(bin)] : undefined;
      if (!compiled.ok || module === undefined) {
        runs.push({ run: run.name, status: "not-run", exitCode: null, trap: null, trapName: null, stdout: { utf8: "" }, stderr: { utf8: "" }, stdoutSha256: "", ms: 0, generation: executor.generations() });
        continue;
      }
      const files: Record<string, Uint8Array> = {};
      for (const [path, blob] of Object.entries(run.vfs)) files[path] = fromBlob(blob);
      const step = await executor.run({
        module,
        args: [run.bin, ...run.args],
        env: run.env,
        files,
        timeoutMs: run.timeout_ms > 0 ? run.timeout_ms : suite.step_timeout_ms,
      });
      runs.push({
        run: run.name,
        status: step.status,
        exitCode: step.exitCode,
        trap: step.trap,
        trapName: step.trapName,
        stdout: toBlob(step.stdout),
        stderr: toBlob(step.stderr),
        stdoutSha256: await sha256Hex(step.stdout),
        ms: step.ms,
        generation: executor.generations(),
      });
      log(`${kase.id} O${optLevel} run ${run.name}: ${step.status}${step.exitCode !== null ? ` ${step.exitCode}` : ""}${step.trap ? ` (${step.trap})` : ""} ${step.ms.toFixed(0)} ms`);
      if (run.recompile_after) {
        compiled = await compileCrates(suite, kase, optLevel, compiler, sources, "@recompile");
        compile.push(...compiled.records);
      }
    }
    for (const record of compile) {
      log(`${kase.id} O${optLevel} compile ${record.crate}: ${record.outcome}${record.errors.length ? ` ${record.errors.map((e) => e.code ?? e.message).join(",")}` : ""}${record.trap ? ` (${record.trap})` : ""} ${record.ms.toFixed(0)} ms`);
    }
    variants.push({ opt_level: optLevel, compile, runs });
  }
  return { id: kase.id, variants, ms: performance.now() - started };
}

/** Cases in id order, with `last` cases (B13 recovery) after all others. */
export function orderedCases(suite: SuiteFile, only?: string[]): SuiteCase[] {
  const selected = suite.cases.filter((c) => !only || only.length === 0 || only.includes(c.id));
  const byId = (a: SuiteCase, b: SuiteCase) => (a.id < b.id ? -1 : a.id > b.id ? 1 : 0);
  return [...selected.filter((c) => !c.last).sort(byId), ...selected.filter((c) => c.last).sort(byId)];
}

export async function runSuite(suite: SuiteFile, compiler: Compiler, executor: Executor, options: SuiteOptions = {}): Promise<CaseRecord[]> {
  const log = options.log ?? (() => {});
  const records: CaseRecord[] = [];
  for (const kase of orderedCases(suite, options.only)) records.push(await runCase(suite, kase, compiler, executor, log));
  return records;
}
