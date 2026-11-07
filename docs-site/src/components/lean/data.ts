// The Lean lessons' data: src/generated/lean-lessons.json, written by the generator beside the
// kcore-spec package (it records the commit it read). Everything a scene shows as output comes
// from it: Lean source text with its own line numbers, peano's KORE, facts Lean computed on the
// definition, goal states captured from the elaborator, heartbeats, the review cone.
// The helpers throw when a scene asks for something the data no longer has, so the site build
// fails instead of showing a stale highlight.

import raw from '../../generated/lean-lessons.json'

export type Ground =
  | { ctor: string; args: Ground[] }
  | { inj: [string, string]; arg: Ground }
  | { dv: string; lit: string }

export type Pattern =
  | { var: number }
  | { app: string; args: Pattern[] }
  | { inj: [string, string]; arg: Pattern }
  | { as: number; arg: Pattern }

export type Binding = { var: number; value: Ground }

export type Explain = {
  rule: 'var' | 'ctor' | 'call' | 'inj' | 'as'
  term: Pattern
  value: Ground | null
  head?: string
  var?: number
  children?: Explain[]
  call?: { function: string | null; args?: Ground[]; by?: 'clause' | 'owise' | 'none'; clause?: number; subst?: Binding[]; rhs?: Explain }
}

export type ConfigFact = {
  name: string
  term: Ground
  sort: string | null
  rules: { rule: string; match: Binding[] | null; rhs: Explain | null }[]
  successors: Ground[] | null
}

export type Source = { file: string; start: number; end: number; text: string }

export type GammaItem = { line: number; label: string; text: string }

export type Diff21Row = {
  subject: string
  module: string
  initial: number
  compared: number
  transitions: number
  stuck: number
  branching: number
  differences: number
  errors: number
  unexplored: number
  refSampled: number
  refAgree: number
  refDifferences: number
}

export type EmitStats = {
  modules: { name: string; sentences: number }[]
  userKinds: Record<string, number>
  fixedInUser: number
  emptySlices: string[]
  equalsKore: boolean
  wf: boolean
  report: { condition: string; holds: boolean }[]
}

export type GoalStep = {
  kind: string
  canonical: boolean
  depth: number
  line: number
  endLine: number
  text: string
  goalsBefore: string[]
  goalsAfter: string[]
}

export type ConeDecl = { module: string; start: number; end: number; kind: string; name: string; via: string | null; depth: number }
export type Cone = {
  title: string
  roots: string[]
  modules: { module: string; decls: number; lines: number }[]
  totals: Record<string, { coneLines: number; decls: number; fileLines: number }>
  folded: number
  theoremsMet: number
  decls?: ConeDecl[]
  elaborated?: string
  trusted?: { prefix: string; count: number; names: string[] }[]
}

type Data = {
  provenance: {
    kcoreSpecCommit: string
    kcoreSpecChange: string
    draftHead: string
    leanVersion: string
    inputs: Record<string, { sha256: string; committed: boolean }>
  }
  sources: Record<string, Source>
  peanoK: string
  kore: { start: number; end: number; text: string; kind: 'rule' | 'equation'; owise: boolean; sourceLocation: string }[]
  facts: {
    configs: ConfigFact[]
    rules: { name: string; vars: string[]; lhs: Pattern; rhs: Pattern }[]
    pred: { arg: Ground; value: Ground | null; clauseMatch: Binding[] | null; explain: Explain }[]
    evalReady: boolean
    rulesApart: boolean
    noDiamonds: boolean
    subsorts: [string, string][]
    ctorSigs: { name: string; args: string[]; result: string }[]
    emit: EmitStats
  }
  goals: Record<string, GoalStep[]>
  heartbeats: Record<string, number>
  oneTime: Record<string, number>
  cones: { user: Cone; emit: Cone; root: Cone; rootOpaque: Cone }
  f0check: {
    totalKHb: number
    peakRssKb: number
    seconds: number
    decisions: Record<'wf_peano' | 'emit_peano' | 'peano_F0', { kHb: number; seconds: number }>
    rejections: number
    controls: number
    rejectionKHb: number
  }
  krun: { command: string; versions: string; steps: { depth: number; text: string }[] }
  gammaD: {
    signature: number
    axioms: number
    nodes: number
    file: string
    definedness: GammaItem
    arityPred: GammaItem
    nextArity: GammaItem
    predEqs: GammaItem[]
    rules: GammaItem[]
  }
  diff21: Diff21Row[]
  loop: {
    log: { run: string; change: string; total_kHb: number; verdict: string; groups: Record<string, number> | null }[]
    recheck: { kHb: Record<string, number>; total_kHb: number }
    negative: { case: string; via: string; result: string }[]
    growth: { n: number; before: number | null; after: number }[]
    judgeHeader: Source
    targets: number
  }
  m2Cone: { title: string; roots: string[]; modules: { module: string; decls: number; lines: number }[]; totals: Record<string, { coneLines: number; decls: number; fileLines: number }> }
  refKompile: { rows: { difference: string; sentences: string; readByStep: string }[]; krustSentences: number; refSentences: number }
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

/** A pane over consecutive Γ_D items: each item's label and pattern, at their lines in GAMMA_D.txt. */
export function gammaSource(...items: GammaItem[]): Source {
  items.forEach((it, i) => {
    if (i > 0 && it.line !== items[i - 1].line + 2) throw new Error(`lean lessons: Γ_D items at ${items[i - 1].line} and ${it.line} are not consecutive`)
  })
  const text = items.flatMap((it) => [it.label, it.text]).join('\n')
  return { file: lean.gammaD.file, start: items[0].line, end: items[0].line + 2 * items.length - 1, text }
}

/** A pane over a text that is not a file: lines numbered from 1. */
export function textSource(file: string, text: string): Source {
  return { file, start: 1, end: text.split('\n').length, text }
}

export const peanoK = textSource('peano.k', lean.peanoK)

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

export function ruleFact(c: ConfigFact, rule: string) {
  const found = c.rules.find((r) => r.rule === rule)
  if (!found) throw new Error(`lean lessons: ${c.name} has no rule ${rule}`)
  return found
}

export function goals(theorem: string): GoalStep[] {
  const found = lean.goals[theorem]
  if (!found) throw new Error(`lean lessons: no captured goals for ${theorem}`)
  return found
}

/** The captured tactic step of `theorem` whose text starts with `prefix` (the n-th such). */
export function goalStep(theorem: string, prefix: string, n = 0): GoalStep {
  const hits = goals(theorem).filter((step) => step.text.trimStart().startsWith(prefix))
  if (!hits[n]) throw new Error(`lean lessons: ${theorem} has no tactic step ${n} starting ${JSON.stringify(prefix)}`)
  return hits[n]
}

export function heartbeats(decl: string): number {
  const found = lean.heartbeats[decl]
  if (found === undefined) throw new Error(`lean lessons: no heartbeats for ${decl}`)
  return found
}

/** Thousands of heartbeats, as the cost tables count them. */
export const kHb = (raw: number) => Math.round(raw / 1000).toLocaleString('en-US')
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

export function patternText(p: Pattern): string {
  if ('var' in p) return `X${p.var}`
  if ('as' in p) return `${patternText(p.arg)} #as X${p.as}`
  if ('app' in p) return p.args.length ? `${symbol(p.app)}(${p.args.map(patternText).join(', ')})` : symbol(p.app)
  return `inj{${p.inj[0]},${p.inj[1]}}(${patternText(p.arg)})`
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
  return `[${σ.map((b) => `X${b.var} ↦ ${groundText(b.value)}`).join(', ')}]`
}
