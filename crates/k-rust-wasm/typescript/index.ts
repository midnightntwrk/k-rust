import initBindings, {
  compileDefinitionWasm,
  formatKoreDefinitionWasm,
  initSync as initBindingsSync,
  parseKastWasm,
  parseKoreWasm,
  parseProgramWasm,
  printKastWasm,
  printKoreWasm,
} from '../generated/bindings.js'

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
  /** The native prelude needs Z3 and cannot be loaded in WASM. Defaults to false. */
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
  /** The native prelude needs Z3 and cannot be loaded in WASM. Defaults to false. */
  includePrelude?: boolean
  koreWidth?: number
}

export interface Diagnostic {
  severity: 'error' | 'warning'
  code: string
  message: string
  source?: string
  startLine?: number
  startColumn?: number
  endLine?: number
  endColumn?: number
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

export type WasmInitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module

let initialized = false

/** Initialize the WebAssembly module, fetching its packaged binary by default. */
export async function init(input?: WasmInitInput | Promise<WasmInitInput>): Promise<void> {
  if (input === undefined) {
    await initBindings()
  } else {
    await initBindings({ module_or_path: input })
  }
  initialized = true
}

export default init

/** Initialize from bytes or a compiled module in runtimes that load the binary themselves. */
export function initSync(module: BufferSource | WebAssembly.Module): void {
  initBindingsSync({ module })
  initialized = true
}

/** Parse a concrete K program with an in-memory definition and virtual source graph. */
export function parseProgram(options: ParseProgramOptions): ParsedProgram {
  assertInitialized()
  return JSON.parse(
    parseProgramWasm(
      JSON.stringify({
        ...options,
        sources: normalizeSources(options.sources),
      }),
    ),
  ) as ParsedProgram
}

/** Compile an in-memory K definition into backend-facing KORE artifacts. */
export function compileDefinition(options: CompileDefinitionOptions): CompiledDefinition {
  assertInitialized()
  return JSON.parse(
    compileDefinitionWasm(
      JSON.stringify({
        ...options,
        sources: normalizeSources(options.sources),
      }),
    ),
  ) as CompiledDefinition
}

/** Parse textual KAST and return both canonical text and typed KAST JSON v4. */
export function parseKast(source: string): SerializedKast {
  assertInitialized()
  return JSON.parse(parseKastWasm(source)) as SerializedKast
}

/** Print typed KAST JSON v4 using k-rust's canonical textual printer. */
export function printKast(kast: Kast): string {
  assertInitialized()
  return printKastWasm(JSON.stringify(kast))
}

/** Parse textual KORE and return both canonical text and typed KORE JSON v1. */
export function parseKore(source: string, width?: number): SerializedKore {
  assertInitialized()
  return JSON.parse(parseKoreWasm(source, width)) as SerializedKore
}

/** Print typed KORE JSON v1 using k-rust's width-aware printer. */
export function printKore(kore: Kore, width?: number): string {
  assertInitialized()
  return printKoreWasm(JSON.stringify(kore), width)
}

/** Parse and consistently pretty-print a complete textual KORE definition. */
export function formatKoreDefinition(source: string, width?: number): string {
  assertInitialized()
  return formatKoreDefinitionWasm(source, width)
}

function assertInitialized(): void {
  if (!initialized) {
    throw new Error('k-rust WASM is not initialized; call init() or initSync() first')
  }
}

function normalizeSources(
  sources: ParseProgramOptions['sources'] | CompileDefinitionOptions['sources'],
): readonly Source[] | undefined {
  if (sources === undefined || Array.isArray(sources)) return sources
  return Object.entries(sources).map(([name, text]) => ({ name, text }))
}
