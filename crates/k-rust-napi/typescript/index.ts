import {
  formatKoreDefinitionNative,
  parseKastNative,
  parseKoreNative,
  parseProgramNative,
  printKastNative,
  printKoreNative,
  type NativeDiagnostic,
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

export interface Diagnostic extends NativeDiagnostic {
  severity: 'error' | 'warning'
}

export interface ParsedProgram {
  text: string
  kast: Kast
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
