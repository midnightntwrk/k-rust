// rustc.wasm invocation shape and output interpretation.
//
// Cargo-free two-stage compile against a flat dependency directory:
// the lesson rlib first, then the collector binary linked in-process by riwl.

import type { FailureCode, LessonManifest, PackManifest } from "./protocol.ts";

export const OUT_DIR = "/work/out";
export const COLLECTOR_MAIN = "/work/collector/main.rs";
export const COLLECTOR_OUT = `${OUT_DIR}/collector.wasm`;
export const COLLECTOR_CRATE = "krs_lesson_collector";

/**
 * Lints rustc suppresses for proc-macro output (external-macro spans) but
 * reports on the same tokens in a pre-expanded file: generated
 * `__KrsEnumVariant_*` and `__krs_configuration_sort_*` names.
 */
export const GENERATED_TEXT_LINT_ALLOWANCES = ["-A", "non_camel_case_types", "-A", "non_snake_case"];

export function expandedPath(lesson: LessonManifest): string {
  return `/work/expanded/${lesson.lesson}/${lesson.display_file}`;
}

export function lessonRlibPath(lesson: LessonManifest): string {
  return `${OUT_DIR}/lib${lesson.package.crate_name}.rlib`;
}

function common(pack: PackManifest): string[] {
  const d = pack.direct_rustc;
  const args = ["--edition", d.edition, "--target", d.target, "--sysroot", d.sysroot, ...d.common_flags];
  for (const dir of pack.direct_rustc.library_dirs) args.push("-L", `dependency=${dir}`);
  return args;
}

export interface Invocation {
  args: string[];
  env: string[];
  output: string;
}

export function lessonInvocation(pack: PackManifest, lesson: LessonManifest): Invocation {
  const output = lessonRlibPath(lesson);
  return {
    args: [
      "rustc",
      expandedPath(lesson),
      "--crate-name",
      lesson.package.crate_name,
      "--crate-type",
      "rlib",
      ...common(pack),
      "--extern",
      `${lesson.facade.alias}=${pack.externs.facade}`,
      "--error-format=json",
      ...lesson.rustc_lint_flags,
      ...(lesson.expansion === "krs-expander" ? GENERATED_TEXT_LINT_ALLOWANCES : []),
      "-o",
      output,
    ],
    env: [
      ...pack.direct_rustc.env,
      `CARGO_PKG_NAME=${lesson.package.cargo_name}`,
      `CARGO_PKG_VERSION=${lesson.package.cargo_version}`,
      `CARGO_MANIFEST_DIR=${lesson.package.manifest_dir}`,
      `CARGO_CRATE_NAME=${lesson.package.crate_name}`,
    ],
    output,
  };
}

export function collectorInvocation(pack: PackManifest, lesson: LessonManifest): Invocation {
  return {
    args: [
      "rustc",
      COLLECTOR_MAIN,
      "--crate-name",
      COLLECTOR_CRATE,
      "--crate-type",
      "bin",
      ...common(pack),
      ...pack.direct_rustc.collector_flags,
      "--extern",
      `${lesson.package.crate_name}=${lessonRlibPath(lesson)}`,
      "--extern",
      `__krs_host_runtime=${pack.externs.host_runtime}`,
      "--extern",
      `__krs_collector_runtime=${pack.externs.collector_runtime}`,
      "--error-format=json",
      "-o",
      COLLECTOR_OUT,
    ],
    env: [...pack.direct_rustc.env],
    output: COLLECTOR_OUT,
  };
}

// ---------------------------------------------------------------- stderr

export interface RustcSpan {
  file_name: string;
  byte_start: number;
  byte_end: number;
  line_start: number;
  line_end: number;
  column_start: number;
  column_end: number;
  is_primary: boolean;
  label: string | null;
}

export interface RustcDiagnostic {
  $message_type: "diagnostic";
  message: string;
  code: { code: string; explanation: string | null } | null;
  level: string;
  spans: RustcSpan[];
  children: RustcDiagnostic[];
  rendered: string | null;
}

export interface ParsedStderr {
  diagnostics: RustcDiagnostic[];
  /** Raw JSON lines, in order, unmapped. */
  jsonLines: string[];
  riwl: Record<string, number> | null;
  /** Lines that are neither JSON diagnostics nor the riwl timing line (ICE text, panics). */
  residue: string[];
}

export function parseStderr(stderr: string): ParsedStderr {
  const diagnostics: RustcDiagnostic[] = [];
  const jsonLines: string[] = [];
  const residue: string[] = [];
  let riwl: Record<string, number> | null = null;
  for (const line of stderr.split("\n")) {
    if (line.startsWith("{")) {
      try {
        const value = JSON.parse(line) as RustcDiagnostic;
        if (value.$message_type === "diagnostic") {
          diagnostics.push(value);
          jsonLines.push(line);
          continue;
        }
      } catch {
        // not JSON; kept as residue
      }
    }
    const timing = /^riwl-timing: (.*)$/.exec(line);
    if (timing) {
      riwl = Object.fromEntries(
        timing[1]!.trim().split(/\s+/).map((pair) => {
          const [key, value] = pair.split("=");
          return [key!, Number(value)];
        }),
      );
      continue;
    }
    if (line.trim() !== "") residue.push(line);
  }
  return { diagnostics, jsonLines, riwl, residue };
}

/** Diagnostics a learner sees: drops rustc's summary lines ("aborting due to", --explain hints). */
export function reportable(diagnostics: RustcDiagnostic[]): RustcDiagnostic[] {
  return diagnostics.filter((d) => {
    if (d.level === "failure-note") return false;
    if (d.spans.length === 0 && /^aborting due to /.test(d.message)) return false;
    if (d.spans.length === 0 && /^\d+ warnings? emitted$/.test(d.message)) return false;
    return true;
  });
}

export interface RustcOutcome {
  ok: boolean;
  code?: FailureCode;
  message?: string;
}

/** Host OOM (RangeError from memory growth) or Rust's alloc-failure message before its abort. */
export const OOM = /out of memory|cannot allocate memory|could not allocate|memory allocation of \d+ bytes failed/i;

/**
 * Classifies one rustc.wasm run. rustc.wasm before fork 0ce51e933 traps
 * (RuntimeError: unreachable) after printing diagnostics on every error exit,
 * with no "aborting due to" line; later forks exit 1. A trap that follows an
 * emitted error is a failed compile, not a compiler crash.
 */
export function classifyRustc(
  stage: "rustc-lesson" | "rustc-collector",
  run: { exitCode: number | null; trap: string | null; trapName: string | null },
  parsed: ParsedStderr,
  outputPresent: boolean,
): RustcOutcome {
  const errors = parsed.diagnostics.filter((d) => d.level === "error" && !/^aborting due to /.test(d.message));
  const errorCode = (): FailureCode =>
    stage === "rustc-collector" && errors.some((d) => /\blink|riwl|undefined symbol|wasm-ld/i.test(d.message))
      ? "link-error"
      : "compile-error";
  if (run.trap !== null) {
    if (errors.length > 0) return { ok: false, code: errorCode(), message: `${errors.length} error(s); rustc.wasm then trapped (${run.trap})` };
    if (run.trapName === "RangeError" || OOM.test(run.trap) || parsed.residue.some((line) => OOM.test(line))) return { ok: false, code: "out-of-memory", message: run.trap };
    return { ok: false, code: "compiler-trap", message: [run.trap, ...parsed.residue.slice(-20)].join("\n") };
  }
  if (run.exitCode !== 0) {
    if (errors.length > 0) return { ok: false, code: errorCode(), message: `${errors.length} error(s); rustc exited ${run.exitCode}` };
    return { ok: false, code: "compiler-trap", message: [`rustc exited ${run.exitCode} without a diagnostic`, ...parsed.residue.slice(-20)].join("\n") };
  }
  if (!outputPresent) return { ok: false, code: "compiler-trap", message: "rustc exited 0 without writing its output" };
  return { ok: true };
}
