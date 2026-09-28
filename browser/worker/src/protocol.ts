// Public types of the KRS browser compiler worker.
//
// docs-site imports this module and controller.ts only. Everything here is
// plain data: every value crosses the page/worker boundary by structured clone.

/** Pipeline stages, in execution order. */
export type Stage =
  | "assets"
  | "policy"
  | "expand"
  | "rustc-lesson"
  | "rustc-collector"
  | "collect"
  | "bundle";

export const STAGES: readonly Stage[] = [
  "assets",
  "policy",
  "expand",
  "rustc-lesson",
  "rustc-collector",
  "collect",
  "bundle",
];

/** The lesson manifest's `[policy]` table (LessonPolicy, schema 1). */
export interface LessonPolicy {
  editable_files: string[];
  facade_alias: string;
}

/** Versioned description of one lesson package (schema 1). */
export interface LessonManifest {
  schema: 1;
  /** Lesson id; also the directory name under /workspace. */
  lesson: string;
  /** The pack this lesson was authored against (PackManifest.pack_id). */
  pack_id: string;
  /** "krs-expander" on path C (krs-expand-wasm); "rustc" on path W. */
  expansion: "krs-expander" | "rustc";
  package: {
    cargo_name: string;
    cargo_version: string;
    crate_name: string;
    /** "/workspace/<lesson>" (stable virtual identity). */
    manifest_dir: string;
    edition: string;
    /** `[package.metadata.krs] k-namespace`. */
    k_namespace: string;
    /** Cargo source kind passed to PackageContext::new (krs-cli: "workspace"). */
    cargo_source: string;
    /** The self-contained Cargo.toml text mounted at <manifest_dir>/Cargo.toml; workspace inheritance is a protocol error. */
    cargo_toml: string;
  };
  /** The facade dependency: `alias` is the extern name, `path` its absolute path. */
  facade: { alias: string; path: string };
  /** The editable file that holds the definition (the policy allows src/lib.rs or src/main.rs). */
  display_file: string;
  policy: LessonPolicy;
  /** Lint flags rendered from the manifest's `[lints.rust]` table, e.g. ["-D", "warnings"]. */
  rustc_lint_flags: string[];
}

export interface CompileRequest {
  /** Monotonic per controller. */
  generation: number;
  lesson: LessonManifest;
  /** Package-relative path -> UTF-8 text; keys must be in lesson.policy.editable_files. */
  files: Record<string, string>;
  /** Attach expanded text, rustc arguments, VFS listings, and raw stderr to the result. */
  debugEvidence?: boolean;
  /** Test-only fault injection (diagnostic cases D005, D006, D009); the docs site never sets it. */
  faultInjection?: FaultInjection;
}

/**
 * Test-only faults that no authored input can produce without a defect, so the diagnostic parity gate can exercise those paths.
 *
 * - `registration-table-missing-factory`: after expansion, the first
 *   registration's factory reference inside the generated-only registration
 *   table is renamed to a same-length name that no item has, so rustc reports
 *   E0425 wholly inside generated text (D009). Byte offsets, and therefore the
 *   source map, are unchanged.
 * - `collector-source`: after both rustc stages, the collector's view of the
 *   named lesson files (package-relative) is replaced by the given text, or
 *   removed when the value is null; rustc still compiled the request's files
 *   (stale source D005, missing source D006).
 */
export type FaultInjection =
  | { kind: "registration-table-missing-factory" }
  | { kind: "collector-source"; files: Record<string, string | null> };

export type DiagnosticOrigin = "policy" | "expander" | "rustc" | "collector";

export type CompileEvent =
  | { type: "progress"; generation: number; stage: Stage; state: "start" | "end"; ms?: number }
  | { type: "diagnostics"; generation: number; origin: DiagnosticOrigin; entries: Diagnostic[] }
  | { type: "success"; generation: number; bundle: Uint8Array; bundleSha256: string; evidence?: Evidence }
  | {
      type: "failure";
      generation: number;
      stage: Stage;
      code: FailureCode;
      message: string;
      diagnostics: Diagnostic[];
      evidence?: Evidence;
    }
  | { type: "cancelled"; generation: number; reason: "cancel" | "superseded" | "disposed" };

export type FailureCode =
  | "pack-integrity"
  | "policy"
  | "expansion"
  | "compile-error"
  | "compiler-trap"
  | "out-of-memory"
  | "link-error"
  | "collector-error"
  | "collector-trap"
  | "protocol-mismatch";

export type MappingClass = "exact-authored" | "invocation-level" | "generated-only" | "unmappable";

export interface SourceRange {
  file: string;
  /** UTF-8 byte offsets, end exclusive. */
  start: number;
  end: number;
}

export interface Diagnostic {
  origin: DiagnosticOrigin;
  code: string | null;
  severity: "error" | "warning" | "note" | "help";
  message: string;
  class: MappingClass;
  /** Authored range in the editable file (package-relative path). */
  authored: SourceRange | null;
  /** Generated range (rustc coordinates); always retained when present. */
  generated: SourceRange | null;
  rendered?: string;
}

/** Debug evidence, attached only when CompileRequest.debugEvidence is set. */
export interface Evidence {
  stageMs: Partial<Record<Stage, number>>;
  /** The applied test-only fault, with what it changed. */
  fault?: { kind: FaultInjection["kind"]; detail: string };
  expandedText?: string;
  expandedSha256?: string;
  sourceMap?: unknown;
  registrations?: unknown;
  rustc: { lesson?: RustcRecord; collector?: RustcRecord };
  vfs: { rustc: VfsEntry[]; collector: VfsEntry[] };
  artifacts: { lessonRlib?: ArtifactDigest; collectorWasm?: ArtifactDigest };
  collector?: {
    exitCode: number | null;
    trap: string | null;
    stderr: string;
    compileMs: number;
    instantiateMs: number;
    runMs: number;
    memoryBytes: number | null;
    args: string[];
    env: string[];
    preopens: string[];
  };
  memory?: MemorySample[];
}

export interface RustcRecord {
  args: string[];
  env: string[];
  preopens: string[];
  exitCode: number | null;
  trap: string | null;
  stderr: string;
  instantiateMs: number;
  runMs: number;
  /** Linear memory of the rustc.wasm instance at exit. */
  memoryBytes: number | null;
  riwl: Record<string, number> | null;
}

export interface VfsEntry {
  path: string;
  bytes: number;
  sha256: string;
}

export interface ArtifactDigest {
  bytes: number;
  sha256: string;
}

export interface MemorySample {
  at: string;
  label: string;
  /** Whatever the host exposes: rss (Node/Bun), usedJSHeapSize (Chromium), or wasm memory bytes. */
  values: Record<string, number>;
}

// ---------------------------------------------------------------- pack

export interface PackAsset {
  /** Path relative to the pack root that the loader reads from. */
  path: string;
  sha256: string;
  bytes: number;
}

export interface PackArtifact extends PackAsset {
  role: "target-rlib" | "proc-macro-metadata" | "sysroot-supplement";
  crate_name: string;
  /** Absolute path in the rustc VFS, e.g. /pack/deps/libkrs-….rlib. */
  mount: string;
}

export interface MountedSource extends PackAsset {
  /** Absolute VFS path, e.g. /krs/crates/krs/src/lib.rs. */
  mount: string;
}

/**
 * Normalized pack manifest consumed by the worker (schema 1). pack-manifest.ts
 * derives it from a pack-manifest.toml (schema_version 2) plus the
 * expander and policy modules, which the pack does not carry.
 */
export interface PackManifest {
  schema: 1;
  kind: "krs-browser-worker-pack";
  /** The pack_id ("sha256:<hex>"), recomputed by the loader. */
  pack_id: string;
  source: { format: string; sha256: string; path: string };
  /** How the loader recomputes pack_id: the pack-manifest rule over every asset under `root`. */
  integrity: { rule: "sorted-artifact-lines"; root: string };
  krs_revision: string;
  /** git tree id of crates/ the pack was built from (pack-manifest [[input]] "KRS crates/ tree"). */
  crates_tree: string;
  fork_revision: string;
  cfg_version: string;
  /** Collector wire protocol version the pack's krs-ir writes. */
  protocol_version: number;
  compiler: { rustc: PackAsset; sysroot_bundle: PackAsset; host_rustc_vv: string[] };
  /** Policy and expander modules, built from the same crates/ tree. */
  modules: { policy: PackAsset; expander: PackAsset; krs_revision: string; crates_tree: string };
  artifacts: PackArtifact[];
  framework_sources: MountedSource[];
  /** Absolute VFS paths of the extern crates. */
  externs: { facade: string; host_runtime: string; compiler_runtime: string };
  direct_rustc: {
    edition: string;
    target: string;
    sysroot: string;
    /** Flags every rustc stage passes (panic strategy, -Zproc-macro-metadata-only, ...). */
    common_flags: string[];
    /** Additional flags for the collector binary (optimization level). */
    collector_flags: string[];
    /** WASI environment for every rustc.wasm run (CLIF2WASM_OBJECT=1, ...). */
    env: string[];
    /** Absolute VFS directories passed as -L dependency=<dir>. */
    library_dirs: string[];
  };
}

/**
 * Assets after the loader verified every hash against the pack manifest
 * (activation rule). Modules are compiled once per page and cloned.
 */
export interface VerifiedAssets {
  packId: string;
  modules: { rustc: WebAssembly.Module; policy: WebAssembly.Module; expander: WebAssembly.Module };
  sysrootBundle: Uint8Array;
  /** Pack-relative asset path -> bytes, for every artifact and framework source. */
  files: Record<string, Uint8Array>;
  /** Pack-relative asset path -> SHA-256 the loader computed. */
  verified: Record<string, string>;
}

/**
 * Verified pack assets that each worker reads from Cache Storage itself
 * The page installs a release through PackCache (pack-cache.ts),
 * compiles the three modules, and keeps no asset bytes; each worker reads the
 * rlibs, the sysroot bundle, and the framework sources from the release's
 * cache namespace and verifies them again (readStoredAssets). Starting or
 * replacing a worker then clones only the compiled modules, not about 120 MB
 * of bytes on the page thread, which dominated browser memory and delayed
 * the cancelled event of a replaced worker.
 */
export interface StoredAssets {
  packId: string;
  modules: VerifiedAssets["modules"];
  /** SHA-256 the page computed for the three module assets (their bytes are not stored for the worker). */
  verified: Record<string, string>;
  store: {
    kind: "cache-storage";
    /** Cache Storage name: the pack's PackCache namespace (namespaceFor). */
    cacheName: string;
    /** PackManifest asset path (= release asset id) -> absolute content-addressed URL of its cache entry. */
    urls: Record<string, string>;
  };
}

// ---------------------------------------------------------------- worker messages (internal)

export const WORKER_PROTOCOL = 1;

export type ToWorker =
  | {
      type: "init";
      protocol: number;
      pack: PackManifest;
      assets: VerifiedAssets;
      /** Web Locks name the worker holds in shared mode for its lifetime (pack-cache.ts cleanup lease). */
      lease?: string;
    }
  | {
      type: "init-stored";
      protocol: number;
      pack: PackManifest;
      stored: StoredAssets;
      /** As for init; taken before the worker reads the store, so cleanup cannot delete it mid-read. */
      lease?: string;
    }
  | { type: "compile"; request: CompileRequest };

export type FromWorker =
  | { type: "ready"; protocol: number }
  | { type: "init-error"; message: string }
  | { type: "event"; event: CompileEvent }
  | { type: "done"; generation: number; replaceWorker: boolean };
