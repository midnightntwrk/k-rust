import {
  compileBackendNative,
  compileDefinitionNative,
  createBackendNative,
  formatKoreDefinitionNative,
  parseKastNative,
  parseKoreNative,
  parseProgramNative,
  printKastNative,
  printKoreNative,
  type NativeBackend,
  type NativeDiagnostic,
  type NativeCompileDefinitionOptions,
  type NativeParseProgramOptions,
} from '../native.js'

export interface KastSort {
  node: 'KSort'
  name: string
  params: KastSort[]
}

export interface KastLabel {
  node: 'KLabel'
  name: string
  params: KastSort[]
}

export type KastTerm =
  | { node: 'KToken'; sort: KastSort; token: string }
  | { node: 'KApply'; label: KastLabel; arity: number; args: KastTerm[] }
  | { node: 'KSequence'; arity: number; items: KastTerm[] }
  | { node: 'KVariable'; name: string; sort?: KastSort }
  | { node: 'KRewrite'; lhs: KastTerm; rhs: KastTerm }
  | { node: 'KAs'; pattern: KastTerm; alias: KastTerm }
  | { node: 'InjectedKLabel'; label: KastLabel }

export interface Kast {
  format: 'KAST'
  version: 4
  term: KastTerm
}

export type KoreSort =
  | { tag: 'SortVar'; name: string }
  | { tag: 'SortApp'; name: string; args: KoreSort[] }

export type KorePattern =
  | { tag: 'String'; value: string }
  | { tag: 'EVar' | 'SVar'; name: string; sort: KoreSort }
  | { tag: 'App'; name: string; sorts: KoreSort[]; args: KorePattern[] }
  | { tag: 'Top' | 'Bottom'; sort: KoreSort }
  | { tag: 'And' | 'Or'; sort: KoreSort; patterns: KorePattern[] }
  | { tag: 'Not'; sort: KoreSort; arg: KorePattern }
  | { tag: 'Next'; sort: KoreSort; dest: KorePattern }
  | { tag: 'Implies' | 'Iff'; sort: KoreSort; first: KorePattern; second: KorePattern }
  | { tag: 'Rewrites'; sort: KoreSort; source: KorePattern; dest: KorePattern }
  | {
      tag: 'Exists' | 'Forall'
      sort: KoreSort
      var: string
      varSort: KoreSort
      arg: KorePattern
    }
  | { tag: 'Mu' | 'Nu'; var: string; varSort: KoreSort; arg: KorePattern }
  | { tag: 'Ceil' | 'Floor'; argSort: KoreSort; sort: KoreSort; arg: KorePattern }
  | {
      tag: 'Equals' | 'In'
      argSort: KoreSort
      sort: KoreSort
      first: KorePattern
      second: KorePattern
    }
  | { tag: 'DV'; sort: KoreSort; value: string }
  | { tag: 'LeftAssoc' | 'RightAssoc'; symbol: string; sorts: KoreSort[]; argss: KorePattern[] }

export interface Kore {
  format: 'KORE'
  version: 1
  term: KorePattern
}

export interface Source {
  /** Stable virtual filename used for `requires` resolution and diagnostics. */
  name: string
  text: string
}

export interface ParseProgramOptions {
  definition: string
  moduleName: string
  sort: string
  program: string
  sourceName?: string
  /** Additional virtual files keyed by the names used in `requires`. */
  sources?: Readonly<Record<string, string>> | readonly Source[]
  markdownSelector?: string
  /** Load k-rust's embedded standard prelude. Defaults to true. */
  includePrelude?: boolean
}

export type CompilationBackend = 'rust' | 'llvm'

export interface CompileDefinitionOptions {
  definition: string
  moduleName: string
  backend?: CompilationBackend
  sourceName?: string
  /** Additional virtual files keyed by the names used in `requires`. */
  sources?: Readonly<Record<string, string>> | readonly Source[]
  markdownSelector?: string
  /** Load k-rust's embedded standard prelude. Defaults to true. */
  includePrelude?: boolean
  /** Pretty-printer line width. Defaults to 100. */
  koreWidth?: number
}

export interface Diagnostic extends NativeDiagnostic {
  severity: 'error' | 'warning'
}

export interface ParsedProgram {
  text: string
  kast: Kast
  diagnostics: Diagnostic[]
}

export interface CompiledDefinition {
  definitionKore: string
  syntaxDefinitionKore: string
  macrosKore: string
  diagnostics: Diagnostic[]
}

export interface SerializedKast {
  text: string
  kast: Kast
}

export interface SerializedKore {
  text: string
  kore: Kore
}

export interface BackendCapabilities {
  execution: boolean
  simplification: boolean
  implication: boolean
  modelGeneration: boolean
  proving: boolean
  moduleAddition: boolean
  smt: boolean
  stepTimeouts: boolean
  search: boolean
  observation: boolean
}

export interface CreateBackendOptions {
  definitionKore: string
  moduleName: string
  smtTimeoutMs?: number
  smtRetryLimit?: number
}

export type ExecutionStrategy = 'all' | 'any'

export interface ExecuteOptions {
  state: Kore
  moduleName?: string
  maxDepth?: number
  maxBreadth?: number
  maxSimplificationIterations?: number
  strategy?: ExecutionStrategy
  stopAtBranch?: boolean
  cutPointRules?: string[]
  terminalRules?: string[]
  stepTimeoutMs?: number
  movingAverageTimeout?: boolean
  assumeStateDefined?: boolean
  /**
   * `state-set` (default) merges structurally equal final configurations into one leaf;
   * `path-set` returns one leaf per explored path, each with its own trace, branch and
   * observations.
   */
  resultModality?: 'state-set' | 'path-set'
  schemaVersion?: number
}

export interface BackendTraceEntry {
  depth: number
  kind: 'simplification' | 'rewrite' | 'claim' | 'remainder'
  label?: string
  uniqueId: string
}

export interface ExecutionLeaf {
  state: Kore
  diagnostics?: BackendDiagnostic[]
  /** Present on branch and cut-point halts. */
  candidates?: ExecutionCandidate[]
  /** The branch's remaining path candidate, when one remains. */
  remainder?: ExecutionRemainder
  depth: number
  reason:
    | 'cancelled'
    | 'stuck'
    | 'trivial'
    | 'vacuous'
    | 'branch'
    | 'cut-point'
    | 'terminal'
    | 'depth-bound'
    | 'breadth-bound'
    | 'indeterminate'
    | 'unsupported-hook'
    | 'simplification-error'
    | 'timeout'
  /** Legacy human-readable context only; use candidates and remainder for halt evidence. */
  detail?: string
  trace: BackendTraceEntry[]
  branch?: TransitionId[]
  /** Ordered effects committed on this branch, independent of observation. */
  effects?: BackendEffect[]
  observations?: ObservationEvent[]
}

export interface ExecutionCandidate {
  state: Kore
  uniqueId: string
  label?: string
  diagnostics?: BackendDiagnostic[]
}

export interface ExecutionRemainder {
  state: Kore
  ruleIds: string[]
  diagnostics?: BackendDiagnostic[]
}

export interface ExecutionResult {
  /** The reading of `leaves` selected by `ExecuteOptions.resultModality`. */
  modality: 'state-set' | 'path-set'
  leaves: ExecutionLeaf[]
  /** Compatibility copy of effects when execution retains exactly one leaf. */
  effects: BackendEffect[]
  discarded?: UncommittedObservation[]
}

export interface TransitionId {
  rule: string
  /** Lowercase SHA-256 of canonical compact successor KORE. */
  target: string
}

export interface BackendBinding {
  variable: Kore
  value: Kore
}

export interface BackendTermPair {
  left: Kore
  right: Kore
}

export type BackendEffect = { kind: 'user-log'; message: string }

/** The kind of committed transition. */
export type TransitionClass = 'rewrite' | 'remainder' | 'claim'

/** The kind of rule applied while normalizing a branch state. */
export type EvaluationClass = 'function-equation' | 'simplification' | 'builtin'

/** A committed transition; `id` is an element of the branch it is reported on, in order. */
export interface TransitionObservation {
  kind: 'transition'
  id: TransitionId
  class: TransitionClass
  ruleLabel?: string
  bindings: BackendBinding[]
  introducedPredicates: Kore[]
  before: Kore
  after: Kore
  /** Attributes committed branch effects to this observed transition. */
  effects: BackendEffect[]
}

/**
 * An equation, simplification, or builtin application that normalized a state of the branch.
 * `anchor` is the number of branch entries preceding it: the normalized state is the one reached
 * by the first `anchor` transitions (the initial state when 0). Diagnostic only: presence,
 * multiplicity, and order depend on the simplifier's strategy.
 */
export interface EvaluationObservation {
  kind: 'evaluation'
  rule: string
  class: EvaluationClass
  ruleLabel?: string
  anchor: number
  before: Kore
  after: Kore
  effects: BackendEffect[]
}

export interface UncommittedObservation {
  kind: 'uncommitted'
  id: TransitionId
  ruleLabel?: string
  /** Effects attempted by a rolled-back transition; no leaf commits them. */
  effects: BackendEffect[]
  reason: 'rolled-back'
}

export type ObservationEvent =
  | TransitionObservation
  | EvaluationObservation
  | UncommittedObservation

export interface ObservationOptions {
  /** Exact executable rewrite, equation, simplification, or definedness ids. Omit to include builtins. */
  rules?: string[]
}

export type SearchType = 'final' | 'all' | 'one-step' | 'one-or-more-steps'

export interface SearchOptions {
  state: Kore
  moduleName?: string
  searchType?: SearchType
  maxDepth?: number
  maxBreadth?: number
  /**
   * Maximum materialized states, witnesses, or matches. Truncation is always reported by a
   * `result-bound` entry. Path searches can enumerate exponentially many acyclic witnesses, so
   * callers should set this bound when the definition can converge repeatedly.
   */
  maxResults?: number
  maxSimplificationIterations?: number
  schemaVersion?: number
}

export interface SearchPatternOptions extends SearchOptions {
  pattern: Kore
}

export interface SearchState {
  state: Kore
  depth: number
  trace: BackendTraceEntry[]
  branch?: TransitionId[]
  observations?: ObservationEvent[]
}

export interface PathWitness {
  id: TransitionId[]
  state: Kore
  depth: number
  trace: BackendTraceEntry[]
  observations?: ObservationEvent[]
}

export type BuiltinFailure =
  | { kind: 'wrong-arity'; hook: string; expected: number; actual: number }
  | { kind: 'unexpected-sort'; hook: string; expected: string; actual: string }
  | { kind: 'alternative-sorts-differ'; thenSort: string; elseSort: string }
  | { kind: 'incompatible-map-sorts'; left: string; right: string }
  | { kind: 'invalid-float-token'; hook: string; token: string }
  | { kind: 'unsupported-float-format'; hook: string; precision: number; exponentBits: number }
  | {
      kind: 'unsupported-float-format-parameters'
      hook: string
      precision: string
      exponentBits: string
    }
  | {
      kind: 'mismatched-float-formats'
      hook: string
      leftPrecision: number
      leftExponentBits: number
      rightPrecision: number
      rightExponentBits: number
    }

export type TranslationFailure =
  | { kind: 'non-boolean-and'; term: Kore }
  | { kind: 'placeholder-out-of-bounds'; placeholder: number; arguments: number }
  | { kind: 'unsupported-predicate'; predicate: string }
  | { kind: 'parametric-sort'; sort: string }
  | { kind: 'smt-lemma-surplus-mappings'; rule: string; terms: Kore[] }
  | { kind: 'smt-lemma-surplus-predicates'; rule: string; predicates: Kore[] }
  | { kind: 'missing-smt-lemma-variable'; rule: string; variable: Kore }

export type ConditionIndeterminacy =
  | { kind: 'no-solver' }
  | { kind: 'implication-indeterminate' }
  | { kind: 'smt-unknown'; reason: string }
  | { kind: 'inconsistent-path-condition' }
  | { kind: 'untranslatable'; error: TranslationFailure }
  | { kind: 'non-functional-binding' }

export type BackendDiagnostic =
  | { kind: 'undecided-condition'; ruleId: string; reason: ConditionIndeterminacy; predicates: Kore[] }
  | { kind: 'undecided-predicate'; predicate: Kore; reason: ConditionIndeterminacy }
  | { kind: 'simplification-budget-exhausted'; limit: number; subject: 'term' | 'predicates' }
  | { kind: 'rule-condition-unsimplified'; ruleId: string; limit: number }
  | { kind: 'unsupported-hook-unevaluated'; hook: string; reason: string }

export type SmtFailure =
  | { kind: 'translation'; error: TranslationFailure }
  | { kind: 'unavailable' }
  | { kind: 'inconsistent-prelude' }
  | { kind: 'unknown-prelude'; reason: string }
  | { kind: 'unknown'; reason: string }
  | { kind: 'inconsistent-ground-truth' }
  | { kind: 'missing-model' }
  | { kind: 'missing-model-value'; variable: Kore }
  | { kind: 'invalid-model-value'; variable: Kore; value: string }

export type SearchSatisfiability =
  | { kind: 'sat' }
  | { kind: 'unsat' }
  | { kind: 'unknown'; reason: string }
  | { kind: 'error'; error: SmtFailure }

export type SearchFailure =
  | { kind: 'stack-exhausted' }
  | { kind: 'builtin'; error: BuiltinFailure }
  | { kind: 'conflicting-results'; rules: string[] }
  | { kind: 'smt'; rule?: string; error: SmtFailure }
  | { kind: 'smt-predicate'; predicate: Kore; error: SmtFailure }
  | { kind: 'inconsistent-ground-truth'; rule?: string }
  | { kind: 'iteration-limit'; limit: number; term: Kore | null }
  | { kind: 'predicate-iteration-limit'; limit: number; predicate: Kore | null }
  | { kind: 'invalid-builtin-result-symbol'; hook: string; symbol: string }
  | { kind: 'match'; rule: string; bindings: BackendBinding[]; remainder: BackendTermPair[] }
  | { kind: 'requires'; rule: string; predicates: Kore[] }
  | { kind: 'concreteness'; rule: string; variable: Kore }
  | {
      kind: 'remainder'
      rules: string[]
      predicates: Kore[]
      satisfiability: SearchSatisfiability
    }

export type SearchIncomplete =
  | { kind: 'result-bound' }
  | { kind: 'depth-bound'; state: SearchState }
  | { kind: 'breadth-bound'; states: SearchState[] }
  | { kind: 'indeterminate'; state: SearchState; reason: SearchFailure }
  | { kind: 'cancelled'; state: SearchState }
  | { kind: 'simplification'; state: SearchState; error: SearchFailure }
  | {
      kind: 'match'
      state: SearchState
      bindings: BackendBinding[]
      remainder: BackendTermPair[]
    }
  | { kind: 'smt'; state: SearchState; error: SmtFailure }

export interface SearchResult {
  schemaVersion: number
  modality: 'state-set'
  states: SearchState[]
  effects: BackendEffect[]
  incomplete: SearchIncomplete[]
}

export interface PathSearchResult {
  schemaVersion: number
  modality: 'path-set'
  witnesses: PathWitness[]
  effects: BackendEffect[]
  incomplete: SearchIncomplete[]
}

export interface SearchMatch {
  bindings: BackendBinding[]
  constraints: Kore[]
  state: SearchState
}

export interface PatternSearchResult {
  schemaVersion: number
  modality: 'state-set'
  matches: SearchMatch[]
  effects: BackendEffect[]
  incomplete: SearchIncomplete[]
}

export interface PathSearchMatch {
  bindings: BackendBinding[]
  constraints: Kore[]
  witness: PathWitness
}

export interface PathPatternSearchResult {
  schemaVersion: number
  modality: 'path-set'
  matches: PathSearchMatch[]
  effects: BackendEffect[]
  incomplete: SearchIncomplete[]
}

export interface PatternOptions {
  state: Kore
  moduleName?: string
  schemaVersion?: number
}

export interface ImplicationOptions {
  antecedent: Kore
  consequent: Kore
  moduleName?: string
  schemaVersion?: number
}

export interface ImplicationCondition {
  predicate: Kore
  substitution: Kore
  witnesses: Kore
}

export interface ImplicationResult {
  schemaVersion: 2
  status: 'valid' | 'invalid' | 'unknown'
  condition?: ImplicationCondition
  failure?: string
}

export interface ModelResult {
  satisfiable: 'sat' | 'unsat' | 'unknown'
  substitution?: Kore
  reason?: string
}

export interface ProveOptions {
  moduleName?: string
  /** Claim label, unique id, or zero-based `#index`. Optional when there is exactly one claim. */
  claim?: string
  maxDepth?: number
  minDepth?: number
  breadthLimit?: number
  maxCounterexamples?: number
  maxSimplificationIterations?: number
  allowVacuous?: boolean
  depthFirst?: boolean
  stuckCheck?: boolean
  stepTimeoutMs?: number
  movingAverageTimeout?: boolean
  schemaVersion?: number
}

export interface ProofLeaf {
  state: Kore
  depth: number
  outcome: string
}

export interface ProofResult {
  claim: string
  status: 'proven' | 'disproved' | 'failed' | 'indeterminate' | 'depth-bound' | 'breadth-bound'
  exploredStates: number
  unexploredStates: number
  leaves: ProofLeaf[]
}

/** A persistent native backend with cached parsed modules and Z3 preludes. */
export class Backend {
  readonly #native: NativeBackend

  constructor(native: NativeBackend) {
    this.#native = native
  }

  get capabilities(): BackendCapabilities {
    return JSON.parse(this.#native.capabilities) as BackendCapabilities
  }

  execute(options: ExecuteOptions): ExecutionResult {
    return JSON.parse(this.#native.execute(JSON.stringify(options))) as ExecutionResult
  }

  executeObserved(
    options: ExecuteOptions,
    observation: ObservationOptions = {},
  ): ExecutionResult {
    return JSON.parse(
      this.#native.executeObserved(JSON.stringify({ request: options, rules: observation.rules })),
    ) as ExecutionResult
  }

  search(options: SearchOptions): SearchResult {
    return JSON.parse(this.#native.search(JSON.stringify(options))) as SearchResult
  }

  searchPaths(options: SearchOptions): PathSearchResult {
    return JSON.parse(this.#native.searchPaths(JSON.stringify(options))) as PathSearchResult
  }

  searchPattern(options: SearchPatternOptions): PatternSearchResult {
    return JSON.parse(this.#native.searchPattern(JSON.stringify(options))) as PatternSearchResult
  }

  searchPatternPaths(options: SearchPatternOptions): PathPatternSearchResult {
    return JSON.parse(
      this.#native.searchPatternPaths(JSON.stringify(options)),
    ) as PathPatternSearchResult
  }

  searchObserved(
    options: SearchOptions,
    observation: ObservationOptions = {},
  ): SearchResult {
    return JSON.parse(
      this.#native.searchObserved(JSON.stringify({ request: options, rules: observation.rules })),
    ) as SearchResult
  }

  searchPathsObserved(
    options: SearchOptions,
    observation: ObservationOptions = {},
  ): PathSearchResult {
    return JSON.parse(
      this.#native.searchPathsObserved(
        JSON.stringify({ request: options, rules: observation.rules }),
      ),
    ) as PathSearchResult
  }

  searchPatternObserved(
    options: SearchPatternOptions,
    observation: ObservationOptions = {},
  ): PatternSearchResult {
    return JSON.parse(
      this.#native.searchPatternObserved(
        JSON.stringify({ request: options, rules: observation.rules }),
      ),
    ) as PatternSearchResult
  }

  searchPatternPathsObserved(
    options: SearchPatternOptions,
    observation: ObservationOptions = {},
  ): PathPatternSearchResult {
    return JSON.parse(
      this.#native.searchPatternPathsObserved(
        JSON.stringify({ request: options, rules: observation.rules }),
      ),
    ) as PathPatternSearchResult
  }

  simplify(options: PatternOptions): Kore {
    return JSON.parse(this.#native.simplify(JSON.stringify(options))) as Kore
  }

  implies(options: ImplicationOptions): ImplicationResult {
    return JSON.parse(this.#native.implies(JSON.stringify(options))) as ImplicationResult
  }

  getModel(options: PatternOptions): ModelResult {
    return JSON.parse(this.#native.getModel(JSON.stringify(options))) as ModelResult
  }

  prove(options: ProveOptions = {}): ProofResult {
    return JSON.parse(this.#native.prove(JSON.stringify(options))) as ProofResult
  }

  addModule(module: string, options: { nameAsId?: boolean } = {}): string {
    return this.#native.addModule(module, options.nameAsId)
  }
}

/** Create a persistent native backend from compiled textual KORE. */
export function createBackend(options: CreateBackendOptions): Backend {
  return new Backend(createBackendNative(options))
}

/** Compile an in-memory K definition and immediately create a persistent native backend. */
export function compileBackend(options: CompileDefinitionOptions): Backend {
  const nativeOptions: NativeCompileDefinitionOptions = {
    ...options,
    sources: normalizeSources(options.sources),
  }
  return new Backend(compileBackendNative(nativeOptions))
}

/** Parse a concrete K program with an in-memory definition and virtual source graph. */
export function parseProgram(options: ParseProgramOptions): ParsedProgram {
  const nativeOptions: NativeParseProgramOptions = {
    ...options,
    sources: normalizeSources(options.sources),
  }
  const parsed = parseProgramNative(nativeOptions)
  return {
    text: parsed.text,
    kast: JSON.parse(parsed.json) as Kast,
    diagnostics: parsed.diagnostics as Diagnostic[],
  }
}

/** Compile an in-memory K definition into backend-facing textual KORE artifacts. */
export function compileDefinition(options: CompileDefinitionOptions): CompiledDefinition {
  const nativeOptions: NativeCompileDefinitionOptions = {
    ...options,
    sources: normalizeSources(options.sources),
  }
  const compiled = compileDefinitionNative(nativeOptions)
  return {
    ...compiled,
    diagnostics: compiled.diagnostics as Diagnostic[],
  }
}

/** Parse textual KAST and return both canonical text and typed KAST JSON v4. */
export function parseKast(source: string): SerializedKast {
  const parsed = parseKastNative(source)
  return { text: parsed.text, kast: JSON.parse(parsed.json) as Kast }
}

/** Print typed KAST JSON v4 using k-rust's canonical textual printer. */
export function printKast(kast: Kast): string {
  return printKastNative(JSON.stringify(kast))
}

/** Parse textual KORE and return both canonical text and typed KORE JSON v1. */
export function parseKore(source: string, width?: number): SerializedKore {
  const parsed = parseKoreNative(source, width)
  return { text: parsed.text, kore: JSON.parse(parsed.json) as Kore }
}

/** Print typed KORE JSON v1 using k-rust's width-aware printer. */
export function printKore(kore: Kore, width?: number): string {
  return printKoreNative(JSON.stringify(kore), width)
}

/** Parse and consistently pretty-print a complete textual KORE definition. */
export function formatKoreDefinition(source: string, width?: number): string {
  return formatKoreDefinitionNative(source, width)
}

function normalizeSources(
  sources: ParseProgramOptions['sources'],
): NativeParseProgramOptions['sources'] {
  if (sources === undefined || Array.isArray(sources)) return sources
  return Object.entries(sources).map(([name, text]) => ({ name, text }))
}
