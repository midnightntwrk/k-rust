// JSON-over-linear-memory ABI of the IR-13 policy module and the IR-11
// expander module: `<prefix>_alloc(len) -> ptr`, `<prefix>_<fn>(ptr, len) -> u64`
// (response_len << 32 | response_ptr), `<prefix>_dealloc(ptr, len)`.
// Both modules have no imports. Every call uses a fresh instance.

interface AbiExports {
  memory: WebAssembly.Memory;
  [name: string]: unknown;
}

async function callJson(module: WebAssembly.Module, prefix: string, fn: string, request: unknown): Promise<unknown> {
  const instance = (await WebAssembly.instantiate(module, {})) as WebAssembly.Instance;
  const exports = instance.exports as AbiExports;
  const alloc = exports[`${prefix}_alloc`] as (len: number) => number;
  const run = exports[`${prefix}_${fn}`] as (ptr: number, len: number) => bigint;
  const dealloc = exports[`${prefix}_dealloc`] as (ptr: number, len: number) => void;
  if (typeof alloc !== "function" || typeof run !== "function" || typeof dealloc !== "function") {
    throw new Error(`module lacks the ${prefix}_{alloc,${fn},dealloc} ABI`);
  }
  const bytes = new TextEncoder().encode(JSON.stringify(request));
  const requestPtr = alloc(bytes.byteLength);
  new Uint8Array(exports.memory.buffer, requestPtr, bytes.byteLength).set(bytes);
  const packed = run(requestPtr, bytes.byteLength);
  const responsePtr = Number(packed & 0xffffffffn);
  const responseLen = Number(packed >> 32n);
  const text = new TextDecoder().decode(new Uint8Array(exports.memory.buffer, responsePtr, responseLen).slice());
  dealloc(requestPtr, bytes.byteLength);
  dealloc(responsePtr, responseLen);
  return JSON.parse(text);
}

// ---------------------------------------------------------------- IR-13 policy

export interface PolicyRequest {
  schema: 1;
  policy: { version: number; editable_files: string[]; facade_alias: string };
  files: Record<string, string>;
}

export interface PolicyDiagnosticJson {
  code: string;
  message: string;
  file: string;
  authored: [number, number] | null;
  class: "exact-authored" | "unmappable";
}

export interface PolicyResponse {
  schema: 1;
  ok: boolean;
  policy_version: number | null;
  diagnostics: PolicyDiagnosticJson[];
}

export function runPolicy(module: WebAssembly.Module, request: PolicyRequest): Promise<PolicyResponse> {
  return callJson(module, "krs_lesson_policy", "run", request) as Promise<PolicyResponse>;
}

// ---------------------------------------------------------------- IR-11 expander

export interface ExpandRequest {
  schema: 1;
  mode: "whole-file";
  file: { virtual_path: string; display_file: string; source: string };
  package: { cargo_name: string; cargo_version: string; manifest_dir: string; crate_name: string };
  module_path: string[];
  facade: { alias: string; path: string };
  generated_file: string;
  policy: { version: number; editable_files: string[]; facade_alias: string };
}

export interface ExpandDiagnosticJson {
  origin: "policy" | "expander" | "protocol";
  code: string | null;
  severity: string;
  message: string;
  class: "exact-authored" | "invocation-level" | "generated-only" | "unmappable";
  file: string;
  authored: [number, number] | null;
  invocation: number | null;
  notes: string[];
}

export interface ExpandResponse {
  schema: 1;
  ok: boolean;
  expanded: { generated_file: string; text: string } | null;
  source_map: ({ authored_sha256: string } & Record<string, unknown>) | null;
  diagnostics: ExpandDiagnosticJson[];
  registrations: unknown[];
  requests_framework: boolean;
  evidence: Record<string, unknown>;
}

export function runExpander(module: WebAssembly.Module, request: ExpandRequest): Promise<ExpandResponse> {
  return callJson(module, "krs_expand", "run", request) as Promise<ExpandResponse>;
}

export interface LookupRequest {
  schema: 1;
  authored_source: string;
  text: string;
  source_map: unknown;
  ranges: Array<[number, number]>;
}

export interface LookupResponse {
  schema: 1;
  ok: boolean;
  mappings: Array<{
    class: "exact-authored" | "invocation-level" | "generated-only" | "unmappable";
    authored: [number, number] | null;
    invocation: number | null;
  }>;
  diagnostics: ExpandDiagnosticJson[];
}

export function runLookup(module: WebAssembly.Module, request: LookupRequest): Promise<LookupResponse> {
  return callJson(module, "krs_expand", "lookup", request) as Promise<LookupResponse>;
}
