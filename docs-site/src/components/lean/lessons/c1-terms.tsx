'use client'

// Core lesson 1: terms. What a configuration is in Lean: ground terms, terms with variables,
// sorts and symbols as numbers, substitutions. Every Lean pane is kcore-spec's text at the
// manifest's commit; the worked panes are facts checked by Lean (docs-gen/lean_checks.py).

import { type Ground, checked, checkedLabel, coreCommit, coreFile, lineOf, slice, span } from '../data'
import { type Lesson, note } from '../lesson'
import { Svg, Tree, groundTree } from '../viz'

const fixed = slice(coreFile('KcoreSpec/FixedSignature.lean'), '/-- A sort:', 'def int : Srt := 3')
const coreLean = coreFile('KcoreSpec/Core.lean')
const ground = slice(coreLean, '/-- A ground value', '| list (s : Srt) (es : List GroundTerm)')
const terms = slice(coreLean, '/-- A term of a clause or a rule:', '| dv (s : Srt) (lit : Lit)')
const subst = slice(coreFile('KcoreSpec/Evaluation.lean'), 'abbrev Subst')
const names = slice(coreFile('examples/peano/Peano/Names.lean'), 'namespace Sym', 'end Srt')

/** The number a `def «name» : KCore.Sym := n` (or `Srt`) line of a file gives. */
const numberIn = (src: typeof names, def: string) => {
  const line = src.text.split('\n')[lineOf(src, def) - src.start]
  const m = /:= (\d+)\s*$/.exec(line)
  if (!m) throw new Error(`lean lessons: no number on ${line}`)
  return Number(m[1])
}
const sym = (n: string) => numberIn(names, `def «${n}» : KCore.Sym`)
const srt = (n: string) => numberIn(names, `def «${n}» : KCore.Srt`)
const kitem = numberIn(fixed, 'def kitem : Srt')
const int = numberIn(fixed, 'def int : Srt')
const [z, s, run] = [sym('z'), sym('s'), sym('run')]
const state = srt('State')

const worked = checked('terms')
const workedTerm = checked('rule0')
const workedSubst = checked('subst')

// The prologue's starting configuration, as krust printed it at depth 0.
const c = (ctor: string, ...args: Ground[]): Ground => ({ ctor, args })
const start: Ground = c(
  "Lbl'-LT-'generatedTop'-GT-'",
  c("Lbl'-LT-'k'-GT-'", c('kseq', { inj: ['State', 'KItem'], arg: c('Lblrun', c('Lbls', c('Lbls', c('Lblz')))) }, c('dotk'))),
  c("Lbl'-LT-'generatedCounter'-GT-'", { dv: 'Int', lit: '0' }),
)
const tree = () => (
  <Svg viewBox="0 0 560 520" label="The prologue's starting configuration as a tree: the top cell holds the k cell and the counter cell; the k cell holds run(s(s(z))) injected into KItem, followed by the empty sequence; the counter holds 0.">
    <Tree node={groundTree(start)} x={10} y={30} w={540} dy={62} />
  </Svg>
)

const at = (src: typeof ground, needle: string) => lineOf(src, needle)

export const terms1: Lesson = {
  id: 'terms',
  number: 1,
  title: 'Terms',
  against: coreCommit,
  scenes: [
    {
      id: 't1',
      title: 'A configuration is a tree',
      visual: tree,
      frames: [
        { say: "The prologue's run started from this configuration. Drawn as a tree, the top cell holds the k cell and the counter cell, and the k cell holds `run(s(s(z)))`." },
        { say: 'Every statement in the core is about trees like this one. This lesson is about how Lean writes them down.' },
      ],
    },
    {
      id: 't2',
      title: 'Sorts and symbols are numbers',
      panes: [
        { id: 'f', label: 'KcoreSpec/FixedSignature.lean', source: fixed, lang: 'lean' },
        { id: 'n', label: 'Peano/Names.lean', source: names, lang: 'lean' },
      ],
      frames: [
        {
          hl: { f: [at(fixed, 'abbrev Srt'), at(fixed, 'abbrev Sym')] },
          notes: [note('f', at(fixed, 'abbrev Srt'), 'A sort is a number.', 'Nat'), note('f', at(fixed, 'abbrev Sym'), 'So is a symbol.', 'Nat')],
        },
        {
          hl: { n: [at(names, 'def «z»'), at(names, 'def «s»'), at(names, 'def «run»'), at(names, 'def «Nat»'), at(names, 'def «State»')] },
          notes: [note('n', at(names, 'def «z»'), `peano's \`z\` is symbol ${z}…`, String(z)), note('n', at(names, 'def «Nat»'), `…and \`Nat\` is sort ${srt('Nat')}.`, String(srt('Nat')))],
          say: "peano's package lists the numbers of its own sorts and symbols with their names, for reading. Nothing that decides or steps compares names.",
        },
        {
          hl: { f: span(fixed, 'def k : Srt', 'def int : Srt') },
          notes: [note('f', at(fixed, 'def k : Srt'), 'Not settled: the library registry becomes a list of hook domains.')],
        },
      ],
    },
    {
      id: 't3',
      title: 'Ground terms',
      panes: [
        { id: 'g', label: 'KcoreSpec/Core.lean', source: ground, lang: 'lean' },
        { id: 'w', label: checkedLabel(worked), source: worked, lang: 'lean' },
      ],
      frames: [
        {
          hl: { g: [at(ground, 'inductive GroundTerm'), at(ground, '| ctor (f : Sym)')], w: [at(worked, `.ctor ${run}`)] },
          notes: [note('g', at(ground, '| ctor (f : Sym)'), 'A constructor applied to its arguments.', 'ctor'), note('w', at(worked, `.ctor ${run}`), `\`run\` is ${run}, \`s\` ${s}, \`z\` ${z}.`, `.ctor ${run}`)],
          say: 'A ground term is a tree with no variables. A configuration is one.',
        },
        {
          hl: { g: [at(ground, '| inj (a b : Srt) (t : GroundTerm)')], w: span(worked, '(.inj Srt', `.inj ${state} ${kitem}`) },
          notes: [note('g', at(ground, '| inj (a b : Srt) (t : GroundTerm)'), 'An injection: a term of sort `a` used where sort `b` is expected.', 'inj'), note('w', at(worked, `.inj ${state} ${kitem}`), `\`State\` is ${state}, \`KItem\` ${kitem}.`, `.inj ${state} ${kitem}`)],
        },
        {
          hl: { g: [at(ground, '| dv (s : Srt) (lit : Lit)')], w: [at(worked, `.dv ${int}`)] },
          notes: [note('g', at(ground, '| dv (s : Srt) (lit : Lit)'), 'A literal of a sort: an Int, a Bool, a token\'s text, or a Float as its IEEE 754 encoding.', 'dv'), note('g', at(ground, '| dv (s : Srt) (lit : Lit)'), 'Not settled: bytes and strings gain canonical forms.', 'Lit'), note('w', at(worked, `.dv ${int}`), `\`Int\` is ${int}.`, `.dv ${int}`)],
        },
        {
          hl: { g: span(ground, '| map (s : Srt)', '| list (s : Srt)') },
          notes: [note('g', at(ground, '| map (s : Srt)'), 'Finite maps, sets and lists of a collection sort. Maps and sets keep their keys in order, so equal collections are equal trees.', 'map')],
          say: 'peano has no collections. Lesson 4 matches patterns against them.',
        },
      ],
    },
    {
      id: 't4',
      title: 'Terms with variables',
      panes: [
        { id: 't', label: 'KcoreSpec/Core.lean', source: terms, lang: 'lean' },
        { id: 'w', label: checkedLabel(workedTerm), source: workedTerm, lang: 'lean' },
      ],
      frames: [
        {
          hl: { t: [at(terms, 'inductive Term where'), at(terms, '| var (i : Nat)')] },
          notes: [note('t', at(terms, '| var (i : Nat)'), 'A variable, by number.', 'var')],
          say: "A rule's sides are not ground: they have variables. `Term` is a tree that may have them.",
        },
        {
          hl: { t: [at(terms, '| app (f : Sym)')], w: [at(workedTerm, '.app Sym.«run»')] },
          notes: [note('t', at(terms, '| app (f : Sym)'), 'A symbol applied to arguments: a constructor or a function.', 'app'), note('w', at(workedTerm, '.app Sym.«run»'), 'The k cell of the first rule\'s left side: `run` applied to `s(N)`.', '.app Sym.«run»')],
          say: '`peano.k` writes `run(s(N)) => run(pred(s(N)))`. The KORE names the repeated `s(N)` once, `#as V` (the prologue\'s `\\and`), and writes the right side as `run(pred(V))`. The Lean value is read from the KORE, so it has the alias: the same meaning, a different shape.',
        },
        {
          hl: { t: [at(terms, '| as (t : Term) (i : Nat)')], w: [at(workedTerm, '.as (')] },
          notes: [note('t', at(terms, '| as (t : Term) (i : Nat)'), 'An alias: the term, and a variable naming what it matched.', 'as'), note('w', at(workedTerm, '.as ('), "The prologue's KORE wrote this as `\\and` of `s(N)` and a fresh variable.", '.as')],
        },
        {
          hl: { t: [at(terms, '| inj (a b : Srt) (t : Term)'), at(terms, '| dv (s : Srt) (lit : Lit)')] },
          notes: [note('t', at(terms, '| inj (a b : Srt) (t : Term)'), 'Injections and literals, as in ground terms.', 'inj')],
        },
      ],
    },
    {
      id: 't5',
      title: 'Substitutions',
      panes: [
        { id: 'e', label: 'KcoreSpec/Evaluation.lean', source: subst, lang: 'lean' },
        { id: 'w', label: checkedLabel(workedSubst), source: workedSubst, lang: 'lean' },
      ],
      frames: [
        {
          hl: { e: [at(subst, 'abbrev Subst')], w: span(workedSubst, 'example : σ₁', '(2, ctr0)') },
          notes: [note('e', at(subst, 'abbrev Subst'), 'Variable numbers paired with ground terms.', 'List (Nat × GroundTerm)'), note('w', at(workedSubst, 'example : σ₁'), '`N`, variable 0, is `s(z)`; `V`, variable 1, is `s(s(z))`; the counter cell, variable 2, is the counter at 0.', '(0,')],
          say: 'Matching the configuration holding `run(s(s(z)))` against the first rule\'s left side gives `N`, `V` and the counter cell values: a substitution.',
        },
        { say: 'Lesson 4 says exactly when a pattern matches a ground term under a substitution. Before that, lesson 2 shows where the patterns come from: the definition itself, as a Lean value.' },
      ],
    },
  ],
  quiz: [
    {
      q: `Which is peano's \`s(z)\` as a ground term?`,
      options: [`.ctor ${s} [.ctor ${z} []]`, `.app ${s} [.var 0]`, `.ctor ${z} [.ctor ${s} []]`],
      answer: 0,
      why: `\`s\` is ${s} and \`z\` is ${z}. \`.app\` and \`.var\` belong to \`Term\`, which has variables.`,
    },
    {
      q: 'In `done(z)`, why is `z` under an injection?',
      options: ['`done` takes a `Val` and `z` is a `Nat`: the injection uses a `Nat` where a `Val` is expected', 'Every constructor argument is injected', 'Injections mark values that came from a function'],
      answer: 0,
      why: 'An injection appears exactly where a term of one sort is used at a larger one.',
    },
  ],
  checked: [
    `The Lean in every pane is kcore-spec's text at \`${coreCommit}\`.`,
    `The panes headed “Checked by Lean” state their facts in Lean; Lean's kernel checked them against peano's package.`,
  ],
}
