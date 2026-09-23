// Shapes shared by the suite controller, the executors, verify.py, and the page.
//
// verify.py renders every cases/<id>/case.toml and the IR-14 pack manifest into
// one suite.json (SuiteFile); every host runs the same suite.json and returns a
// HostRecord, which verify.py compares with each case's expected.json.

/** A file as JSON: UTF-8 text when it decodes, base64 otherwise. */
export type Blob = { utf8: string } | { base64: string };

export interface PackAssetRef {
  /** Path relative to the pack root. */
  path: string;
  sha256: string;
  bytes: number;
}

export interface SuitePack {
  pack_id: string;
  /** compiler.fork_revision of the pack manifest. */
  fork_revision: string;
  /** Host directory of the pack (Node hosts). */
  root: string;
  /** Page-relative URL of the pack root (browser hosts; set by build-site.ts). */
  url_base?: string;
  rustc_wasm: PackAssetRef;
  sysroot_bundle: PackAssetRef;
  /** Every [[artifact]] of the manifest (pack_id is recomputed over them). */
  artifacts: PackAssetRef[];
  /** Mount point of the sysroot bundle in the compiler VFS. */
  sysroot_mount: string;
  /** [direct_rustc] of the pack, rendered for the fork compiler (guest paths). */
  fork_flags: string[];
  /** WASI environment of rustc.wasm (CLIF2WASM_OBJECT=1, RIWL_TIMINGS=1). */
  fork_env: string[];
  /** crate name -> pack-relative rlib path (target-rlib role). */
  externs: Record<string, string>;
}

export type CrateType = "rlib" | "bin" | "obj";

export interface SuiteCrate {
  name: string;
  /** Guest path of the root source file (/case/<src>). */
  src: string;
  type: CrateType;
  /** Earlier crates of the same case. */
  externs: string[];
  /** Crates taken from the pack (resolved through SuitePack.externs). */
  pack: string[];
  flags: string[];
  /** "init-funcs": count WASM_INIT_FUNCS entries of the emitted object. */
  inspect: string | null;
}

export interface SuiteRun {
  name: string;
  bin: string;
  args: string[];
  env: string[];
  /** Guest path (absolute, under the single "/" preopen) -> bytes. */
  vfs: Record<string, Blob>;
  /** 0: no timeout beyond the step ceiling. */
  timeout_ms: number;
  /** The run is expected to be cancelled by its timeout (spin). */
  cancel: boolean;
  /** After this run, recompile every crate of the case (fresh executor if cancelled). */
  recompile_after: boolean;
}

export interface SuiteCase {
  id: string;
  /** Guest path -> source text, mounted under /case. */
  sources: Record<string, string>;
  opt_levels: number[];
  crates: SuiteCrate[];
  runs: SuiteRun[];
  /** Run after every other case (B13). */
  last: boolean;
}

export interface SuiteFile {
  schema: 1;
  suite: "krs-browser-backend";
  generated_by: string;
  pack: SuitePack;
  /** Ceiling for any single compile or run step. */
  step_timeout_ms: number;
  cases: SuiteCase[];
}

// ---------------------------------------------------------------- steps

export interface RustcRequest {
  args: string[];
  env: string[];
  /** Guest path -> bytes for /case and /out inputs. */
  files: Record<string, Uint8Array>;
  /** Guest paths to return when present after the run. */
  outputs: string[];
  timeoutMs: number;
}

export interface RunRequest {
  module: Uint8Array;
  args: string[];
  env: string[];
  /** Guest path -> bytes, all under the single "/" preopen. */
  files: Record<string, Uint8Array>;
  timeoutMs: number;
}

export interface StepResult {
  /** exit: exited with exitCode; trap: the instance threw; cancelled: the timeout fired and the executor was replaced. */
  status: "exit" | "trap" | "cancelled";
  exitCode: number | null;
  trap: string | null;
  trapName: string | null;
  stdout: Uint8Array;
  stderr: Uint8Array;
  outputs: Record<string, Uint8Array>;
  ms: number;
  memoryBytes: number | null;
}

export interface Compiler {
  readonly kind: "fork" | "twin" | "stable";
  rustc(request: RustcRequest): Promise<StepResult>;
}

export interface Executor {
  run(request: RunRequest): Promise<StepResult>;
  /** Replaces the execution context (worker); used after a cancelled step. */
  reset(): Promise<void>;
  /** Number of execution contexts created so far. */
  generations(): number;
}

// ---------------------------------------------------------------- records

export interface DiagnosticSummary {
  level: string;
  code: string | null;
  message: string;
}

export interface CompileRecord {
  crate: string;
  /**
   * ok | error (JSON error diagnostics, then an exit or a trap) | link-error (riwl
   * reported an error on plain stderr) | compiler-trap (no diagnostic) | cancelled
   */
  outcome: "ok" | "error" | "link-error" | "compiler-trap" | "cancelled";
  errors: DiagnosticSummary[];
  /** rustc's `aborting due to N previous error(s)` summary diagnostic was emitted. */
  summary: boolean;
  exitCode: number | null;
  trap: string | null;
  /** Everything on stderr that is not a JSON diagnostic (riwl timings excluded). */
  residue: string[];
  outputSha256: string | null;
  outputBytes: number | null;
  initFuncs: number | null;
  ms: number;
  memoryBytes: number | null;
}

export interface RunRecord {
  run: string;
  status: "exit" | "trap" | "cancelled" | "not-run";
  exitCode: number | null;
  /** Engine-specific trap text (not compared). */
  trap: string | null;
  trapName: string | null;
  stdout: Blob;
  stderr: Blob;
  stdoutSha256: string;
  ms: number;
  generation: number;
}

export interface VariantRecord {
  opt_level: number;
  compile: CompileRecord[];
  runs: RunRecord[];
}

export interface CaseRecord {
  id: string;
  variants: VariantRecord[];
  ms: number;
}

export interface HostRecord {
  schema: 1;
  host: string;
  compiler: "fork" | "twin" | "stable";
  environment: Record<string, unknown>;
  pack_id: string;
  verified: { rustc_wasm_sha256: string | null; sysroot_bundle_sha256: string | null; pack_id_recomputed: string | null; artifacts_verified: number };
  cases: CaseRecord[];
  executor_generations: number;
  wall_ms: number;
}
