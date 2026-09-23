// The execution seam of the browser lesson (IR-20 -> IR-19).
//
// The compiler worker ends at the canonical DescriptorBundle. Everything after
// it, the stages the native CLI runs after the collector's stdout is
// deserialized, belongs to IR-19's prebuilt module (proposed crate
// krs-lower-wasm, linking k-rust without Z3):
//
//   lower    serde DescriptorBundle -> lower_descriptor_bundle -> lower_semantic_theory -> emit_k
//   kore     krs_k_rust::compile_definition (structured loader, no emitted-K parsing)
//   execute  k-rust backend on the initial configuration
//
// The page consumes only the types below. `executionStatus()` is the single
// place that decides whether execution exists: until IR-19 lands it reports
// `available: false` and the page shows those stages as not yet available. It
// never produces a result, a final configuration, or a diagnostic of its own.
//
// IR-19 plugs in by returning `{ available: true, create }` here (or from a
// module the build selects), where `create` loads its module from the same
// asset base and returns a LessonExecutor.

import type { Diagnostic } from '../../../browser/worker/src/protocol.ts'

export type ExecutionStage = 'lower' | 'kore' | 'execute'

export const EXECUTION_STAGES: ReadonlyArray<{ id: ExecutionStage; label: string; detail: string }> = [
  { id: 'lower', label: 'Lower', detail: 'KRS lowering and K emission of the bundle' },
  { id: 'kore', label: 'Compile to KORE', detail: 'k-rust compiles the lowered definition' },
  { id: 'execute', label: 'Execute', detail: 'k-rust runs the initial configuration' },
]

/**
 * What the loaded module can do (IR-19 derives it from krs-k-rust's
 * FrontendCapabilities; operations the Z3-free k-rust lacks report false).
 */
export interface ExecutionCapabilities {
  execute: boolean
  search: boolean
  prove: boolean
  smt: boolean
}

export interface ExecutionRequest {
  generation: number
  /** The exact bytes the compiler worker returned (the collector's stdout). */
  bundle: Uint8Array
  bundleSha256: string
  packId: string
  signal: AbortSignal
}

export type ExecutionEvent =
  | { type: 'progress'; stage: ExecutionStage; state: 'start' | 'end'; ms?: number }
  /** Lowering diagnostics are the CLI's DiagnosticEnvelope mapped to the worker's Diagnostic shape. */
  | { type: 'diagnostics'; stage: ExecutionStage; entries: Diagnostic[] }
  | { type: 'result'; finalConfiguration: string; raw?: unknown }
  | { type: 'failure'; stage: ExecutionStage; code: string; message: string; diagnostics: Diagnostic[]; raw?: unknown }
  | { type: 'cancelled' }

export interface LessonExecutor {
  capabilities: ExecutionCapabilities
  run(request: ExecutionRequest): AsyncIterable<ExecutionEvent>
  dispose(): void
}

export type ExecutionStatus =
  | { available: false; reason: string }
  | { available: true; create: (options: { packBase: string; packId: string }) => Promise<LessonExecutor> }

/** Execution is not available in the browser yet: the k-rust handoff (IR-19) has not landed. */
export function executionStatus(): ExecutionStatus {
  return {
    available: false,
    reason:
      'Lowering, KORE compilation, and execution in the browser need the k-rust handoff, which is not built yet. ' +
      'The compiler stops at the DescriptorBundle.',
  }
}
