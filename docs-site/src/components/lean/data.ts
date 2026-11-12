// The Lean lessons' data: src/generated/lean-lessons.json, written by the generator beside the
// kcore-spec package (it records the commit it read). Everything a scene shows as output comes
// from it: Lean source text with its own line numbers, peano's KORE and a run of it, facts Lean
// computed on the definition, and the package build's costs.
// The helpers throw when a scene asks for something the data no longer has, so the site build
// fails instead of showing a stale highlight.

import raw from '../../generated/lean-lessons.json'
import coreRaw from '../../generated/lean-core.json'
import checksRaw from '../../generated/lean-checks.json'

/** A ground term, with symbols and sorts by their KORE names. */
export type Ground =
  | { ctor: string; args: Ground[] }
  | { inj: [string, string]; arg: Ground }
  | { dv: string; lit: string }

/** A term of a rule or a clause: variables by number. */
export type Pattern =
  | { var: number }
  | { app: string; args: Pattern[] }
  | { inj: [string, string]; arg: Pattern }
  | { as: number; arg: Pattern }
  | { dv: string; lit: string }

export type Binding = { var: number; value: Ground }

export type ConfigFact = {
  name: string
  term: Ground
  sort: string | null
  isConfig: boolean
  /** For each rule, its matches: the substitution, whether the rule applies under it, and what its right-hand side evaluates to. */
  rules: { rule: number; matches: { subst: Binding[]; applies: boolean | null; rhs: Ground | null }[] }[]
  successors: Ground[]
}

export type Source = { file: string; start: number; end: number; text: string }

type Data = {
  provenance: {
    kcoreSpecCommit: string
    kcoreSpecChange: string
    draftHead: string
    leanVersion: string
    inputs: Record<string, { sha256: string; committed: boolean }>
  }
  sources: Record<string, Source>
  package: { modules: string[]; tie: string[]; user: string[]; build: Record<string, { seconds: number; rssMiB: number }>; certSteps: number }
  peanoK: string
  kore: { start: number; end: number; text: string; kind: 'rule' | 'equation'; owise: boolean; sourceLocation: string }[]
  facts: {
    registry: { sorts: number; syms: number; ownSorts: string[]; ownSyms: string[] }
    emit: {
      modules: { name: string; sentences: number }[]
      userKinds: Record<string, number>
      fixedInUser: number
      equalsKore: boolean
      reordered: boolean
      wf: boolean
      report: { condition: string; holds: boolean }[]
    }
    configs: ConfigFact[]
    rules: { index: number; vars: string[]; lhs: Pattern; rhs: Pattern; prio: number }[]
    pred: { arg: Ground; value: Ground | null }[]
  }
  krun: { command: string; versions: string; steps: { depth: number; text: string }[] }
}

export const lean = raw as unknown as Data

// ---- source text ----------------------------------------------------------------------------

export function source(key: string): Source {
  const found = lean.sources[key]
  if (!found) throw new Error(`lean lessons: no source ${key}`)
  return found
}

/** The file line number of the first line of `src` containing `needle` (after line `after`). */
export function lineOf(src: Source, needle: string, after = 0): number {
  const lines = src.text.split('\n')
  for (let i = 0; i < lines.length; i += 1) {
    const line = src.start + i
    if (line > after && lines[i].includes(needle)) return line
  }
  throw new Error(`lean lessons: ${src.file} has no line containing ${JSON.stringify(needle)} after ${after}`)
}

/** The file line numbers from the line containing `from` to the next line containing `to`. */
export function span(src: Source, from: string, to?: string, after = 0): number[] {
  const first = lineOf(src, from, after)
  const last = to === undefined ? first : lineOf(src, to, first - 1)
  return Array.from({ length: last - first + 1 }, (_, i) => first + i)
}

/** The part of `src` from the line containing `from` (to the line containing `to`, or the end), keeping its line numbers. */
export function slice(src: Source, from: string, to?: string): Source {
  const first = lineOf(src, from)
  const last = to === undefined ? src.end : lineOf(src, to, first - 1)
  const text = src.text.split('\n').slice(first - src.start, last - src.start + 1).join('\n')
  return { file: src.file, start: first, end: last, text }
}

/** A pane over a text that is not a file: lines numbered from 1. */
export function textSource(file: string, text: string): Source {
  return { file, start: 1, end: text.split('\n').length, text }
}

export const peanoK = textSource('peano.k', lean.peanoK)
export const peanoLines = lean.peanoK.split('\n').length

export function koreAxiom(kind: 'rule' | 'equation', index: number): Source {
  const found = lean.kore.filter((axiom) => axiom.kind === kind)[index]
  if (!found) throw new Error(`lean lessons: no KORE ${kind} ${index}`)
  return { file: 'definition.kore', start: found.start, end: found.end, text: found.text }
}

// ---- facts ----------------------------------------------------------------------------------

export function config(name: string): ConfigFact {
  const found = lean.facts.configs.find((c) => c.name === name)
  if (!found) throw new Error(`lean lessons: no computed configuration ${name}`)
  return found
}

export function build(module: string) {
  const found = lean.package.build[module]
  if (!found) throw new Error(`lean lessons: no build record of ${module}`)
  return found
}

export const fmt = (n: number) => n.toLocaleString('en-US')

export const shortCommit = lean.provenance.kcoreSpecCommit.slice(0, 12)

// ---- rendering terms ------------------------------------------------------------------------

const fixedNames: Record<string, string> = {
  "Lbl'-LT-'generatedTop'-GT-'": '<generatedTop>',
  "Lbl'-LT-'k'-GT-'": '<k>',
  "Lbl'-LT-'generatedCounter'-GT-'": '<generatedCounter>',
  "Lbl'Hash'KConfigValue": '#KConfigValue',
}

/** The display name of a KORE symbol: `Lbls` is `s`, `Lbl'-LT-'k'-GT-'` is `<k>`. */
export function symbol(label: string): string {
  return fixedNames[label] ?? (label.startsWith('Lbl') ? label.slice(3) : label)
}

export function groundText(t: Ground): string {
  if ('ctor' in t) return t.args.length ? `${symbol(t.ctor)}(${t.args.map(groundText).join(', ')})` : symbol(t.ctor)
  if ('inj' in t) return `inj{${t.inj[0]},${t.inj[1]}}(${groundText(t.arg)})`
  return `\\dv{${t.dv}}("${t.lit}")`
}

/** A ground term as K writes it: injections left out, a domain value as its literal. */
export function kText(t: Ground): string {
  if ('ctor' in t) return t.args.length ? `${symbol(t.ctor)}(${t.args.map(kText).join(', ')})` : symbol(t.ctor)
  if ('inj' in t) return kText(t.arg)
  return t.lit
}

export function patternText(p: Pattern): string {
  if ('var' in p) return `X${p.var}`
  if ('as' in p) return `${patternText(p.arg)} #as X${p.as}`
  if ('app' in p) return p.args.length ? `${symbol(p.app)}(${p.args.map(patternText).join(', ')})` : symbol(p.app)
  if ('inj' in p) return `inj{${p.inj[0]},${p.inj[1]}}(${patternText(p.arg)})`
  return p.lit
}

/** The content of the k cell of a configuration `<generatedTop>(<k>(kseq(item, dotk)), ctr)`. */
export function kItem(t: Ground): Ground {
  if ('ctor' in t && t.ctor === "Lbl'-LT-'generatedTop'-GT-'") {
    const k = t.args[0]
    if ('ctor' in k && k.ctor === "Lbl'-LT-'k'-GT-'") {
      const seq = k.args[0]
      if ('ctor' in seq && seq.ctor === 'kseq') {
        const item = seq.args[0]
        return 'inj' in item ? item.arg : item
      }
    }
  }
  throw new Error(`lean lessons: ${groundText(t)} is not a configuration with one k item`)
}

export function substText(σ: Binding[]): string {
  return `[${σ.map((b) => `X${b.var} ↦ ${kText(b.value)}`).join(', ')}]`
}

// ---- the core, quoted at the manifest's commit ----------------------------------------------
// src/generated/lean-core.json: kcore-spec's text at the commit core-manifest.toml names, written
// by docs-gen/core_sources.py beside the manifest. The core lessons quote only this, and are stamped
// with its commit.

/** A file's text, or one axiom of a large file (key `path#label`) with the line it starts at. */
const core = coreRaw as { commit: string; files: Record<string, string | { start: number; text: string }> }

export const coreCommit = core.commit

/** A file of kcore-spec at `coreCommit`, its lines numbered as in the file. */
export function coreFile(path: string): Source {
  const found = core.files[path]
  if (found === undefined) throw new Error(`lean lessons: no core file ${path}`)
  const { start, text } = typeof found === 'string' ? { start: 1, text: found } : found
  const body = text.endsWith('\n') ? text.slice(0, -1) : text
  return { file: path.split('#')[0].replace(/^\.\.\//, ''), start, end: start + body.split('\n').length - 1, text: body }
}

// ---- facts checked by Lean ------------------------------------------------------------------
// src/generated/lean-checks.json: Lean files that state, as `example`s, facts the lessons once
// derived by hand, each proved by a theorem of an example package or by the kernel; written by
// docs-gen/lean_checks.py, which fails unless every file checks.

const checks = checksRaw as { commit: string; panes: Record<string, string> }

export const checkedLabel = `Checked by Lean at ${checks.commit}`

/** A pane of Lean facts that checked, numbered from 1. */
export function checked(name: string): Source {
  const text = checks.panes[name]
  if (text === undefined) throw new Error(`lean lessons: no checked pane ${name}`)
  return textSource('checked by Lean', text)
}
