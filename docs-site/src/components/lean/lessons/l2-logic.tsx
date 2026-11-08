'use client'

// Lesson 2: patterns as sets, truth in a model, the theory Γ_D that the KORE text of peano
// translates to, and steps as the symbol •. The Lean panes are aml-port (the port of the
// matching-logic library the package builds on) and kcore-spec; the Γ_D items are the package's own
// printing of peano's theory (GAMMA_D.txt). The five-element model is an illustration: its sets are
// computed below by the clauses of `Pattern.interpret` shown beside it, not by Lean.

import { fmt, gammaSource, lean, lineOf, source, span } from '../data'
import { type Lesson, note } from '../lesson'
import { A, Arrow, Box, Label, Rows, Svg } from '../viz'

const pattern = source('amlPattern')
const semantics = source('amlSemantics')
const notations = source('amlNotations')
const entails = source('amlEntails')
const definedness = source('amlDefinedness')

// ---- a five-element model, for illustration ---------------------------------------------------

type E = 'σ' | 'δ' | '0' | '1' | '2'
const M: readonly E[] = ['σ', 'δ', '0', '1', '2']
type P = { evar: 'x' } | { sym: 'z' | 's' | 'def' } | { app: [P, P] } | { imp: [P, P] } | { bot: true } | { ex: P }

const evalSymb = (s: 'z' | 's' | 'def'): E[] => (s === 'z' ? ['0'] : s === 's' ? ['σ'] : ['δ'])
const evalApp = (a: E, b: E): E[] => {
  if (a === 'σ' && b === '0') return ['1']
  if (a === 'σ' && b === '1') return ['2']
  if (a === 'δ') return [...M]
  return []
}

/** `Pattern.interpret` of aml-port, clause by clause, over the five elements; x is the only variable. */
function interpret(p: P, x: E): Set<E> {
  if ('evar' in p) return new Set([x])
  if ('sym' in p) return new Set(evalSymb(p.sym))
  if ('bot' in p) return new Set()
  if ('imp' in p) {
    const a = interpret(p.imp[0], x)
    const b = interpret(p.imp[1], x)
    return new Set(M.filter((m) => !a.has(m) || b.has(m)))
  }
  if ('ex' in p) return new Set(M.filter((m) => M.some((a) => interpret(p.ex, a).has(m))))
  const fs = interpret(p.app[0], x)
  const as = interpret(p.app[1], x)
  return new Set(M.filter((m) => [...fs].some((f) => [...as].some((a) => evalApp(f, a).includes(m)))))
}

const z: P = { sym: 'z' }
const s: P = { sym: 's' }
const x: P = { evar: 'x' }
const app = (f: P, a: P): P => ({ app: [f, a] })
const neg = (p: P): P => ({ imp: [p, { bot: true }] })
const ceil = (p: P): P => app({ sym: 'def' }, p)
const exS: P = { ex: app(s, x) }

const shown = {
  none: { text: 'the five elements of the model', p: { bot: true } as P },
  z: { text: 'z', p: z },
  sz: { text: 's ⬝ z', p: app(s, z) },
  sss: { text: 's ⬝ (s ⬝ (s ⬝ z))', p: app(s, app(s, app(s, z))) },
  x: { text: 'x, with x ↦ s(z)', p: x, x: '1' as E },
  sx: { text: 's ⬝ x, with x ↦ s(z)', p: app(s, x), x: '1' as E },
  ex: { text: '∃∃ x (s ⬝ x)', p: exS },
  notEx: { text: '∼(∃∃ x (s ⬝ x))', p: neg(exS) },
  xx: { text: 'x ⇒ x', p: { imp: [x, x] } as P },
  ceilSz: { text: '⌈s ⬝ z⌉', p: ceil(app(s, z)) },
  ceilSss: { text: '⌈s ⬝ (s ⬝ (s ⬝ z))⌉', p: ceil(app(s, app(s, app(s, z)))) },
}
type Key = keyof typeof shown
/** Whether a pattern holds: it denotes every element, under every valuation of x. */
const holds = (p: P) => M.every((v) => interpret(p, v).size === M.length)
if (interpret(shown.sss.p, '0').size !== 0 || interpret(exS, '0').size !== 2) throw new Error('lean lessons: the illustration model changed')
if (holds(exS) || !holds(shown.xx.p) || !holds(shown.ceilSz.p) || holds(shown.ceilSss.p)) throw new Error('lean lessons: the illustration model changed')

const label: Record<E, string> = { σ: 's', δ: '⌈ ⌉', '0': 'z', '1': 's(z)', '2': 's(s(z))' }
const setText = (set: Set<E>) => (set.size === 0 ? 'denotes the empty set' : set.size === M.length ? 'denotes every element' : `denotes {${[...set].map((e) => label[e]).join(', ')}}`)

function Dots({ k, wide = false }: { k: Key; wide?: boolean }) {
  const it = shown[k]
  const set = k === 'none' ? new Set<E>() : interpret(it.p, ('x' in it ? it.x : '0') as E)
  if (wide) {
    return (
      <Svg viewBox="0 0 900 170" label={`Elements of the model; in the set: ${[...set].map((e) => label[e]).join(', ') || 'none'}`}>
        <Label x={190} y={72} anchor="middle" size={17} text={it.text} isMono weight={600} />
        <Label x={190} y={98} anchor="middle" size={13} tone="var(--muted)" text={setText(set)} />
        {M.map((e, i) => (
          <g key={e}>
            <circle cx={430 + i * 100} cy={68} r={32} fill={set.has(e) ? 'var(--accent-tint)' : 'var(--code-bg)'} stroke={set.has(e) ? 'var(--accent)' : 'var(--line)'} strokeWidth={set.has(e) ? 2.4 : 1.2} />
            <Label x={430 + i * 100} y={74} anchor="middle" size={16} text={e} isMono weight={set.has(e) ? 600 : 400} />
            <Label x={430 + i * 100} y={124} anchor="middle" size={12} tone="var(--muted)" text={label[e]} isMono />
          </g>
        ))}
      </Svg>
    )
  }
  return (
    <Svg viewBox="0 0 460 300" label={`Elements of the model; in the set: ${[...set].map((e) => label[e]).join(', ') || 'none'}`}>
      <Label x={230} y={60} anchor="middle" size={17} text={it.text} isMono weight={600} />
      <Label x={230} y={86} anchor="middle" size={13} tone="var(--muted)" text={k === 'none' ? 'nothing selected yet' : setText(set)} />
      {M.map((e, i) => (
        <g key={e}>
          <circle cx={54 + i * 88} cy={170} r={32} fill={set.has(e) ? 'var(--accent-tint)' : 'var(--code-bg)'} stroke={set.has(e) ? 'var(--accent)' : 'var(--line)'} strokeWidth={set.has(e) ? 2.4 : 1.2} style={{ transition: 'fill .3s, stroke .3s' }} />
          <Label x={54 + i * 88} y={176} anchor="middle" size={16} text={e} isMono weight={set.has(e) ? 600 : 400} />
          <Label x={54 + i * 88} y={226} anchor="middle" size={12} tone="var(--muted)" text={label[e]} isMono />
        </g>
      ))}
    </Svg>
  )
}

const dotsOrder: Key[] = ['none', 'z', 'sz', 'sss', 'x', 'sx', 'ex']
const truthRows: Key[] = ['ex', 'xx', 'ceilSz', 'ceilSss']
const truthFocus: (Key | null)[] = [null, 'ex', 'xx', 'ceilSz', 'ceilSss', null]

const truth = (at: number) => (
  <Rows
    head={['pattern', 'denotes, in the five-element model', 'holds there']}
    rows={truthRows.map((k) => {
      const set = interpret(shown[k].p, '0')
      const focus = truthFocus[at]
      return {
        key: k,
        state: focus === null ? undefined : focus === k ? 'cur' : 'faded',
        cells: [shown[k].text, set.size === M.length ? 'every element' : set.size === 0 ? 'nothing' : [...set].map((e) => label[e]).join(', '), holds(shown[k].p) ? 'yes' : 'no'],
      }
    })}
  />
)

// ---- the steps as a chain ---------------------------------------------------------------------

const chain = (phase: 'plain' | 'rule' | 'ghost' | 'closure') => () => (
  <Svg viewBox="0 0 900 170" label="run(s(z)) steps to run(z), which steps to done(z)">
    <Box x={130} y={70} w={170} text="run(s(z))" tone={phase === 'rule' ? 'on' : 'plain'} />
    <Arrow x1={217} y1={70} x2={348} y2={70} label="•" on={phase === 'rule'} />
    <Box x={435} y={70} w={170} text="run(z)" />
    <Arrow x1={522} y1={70} x2={648} y2={70} label="•" />
    <Box x={735} y={70} w={170} text="done(z)" tone={phase === 'ghost' ? 'on' : phase === 'closure' ? 'accent' : 'plain'} />
    <A show={phase === 'ghost'}>
      <Arrow x1={700} y1={87} x2={560} y2={134} dash on />
      <Box x={525} y={140} w={64} text="?" tone="ghost" dash />
      <Label x={735} y={136} tone="var(--gold)" weight={600} size={13} text="some model of Γ_D adds a step here" anchor="middle" />
    </A>
    <A show={phase === 'closure'}>
      <Label x={735} y={120} anchor="middle" tone="var(--ok)" weight={600} size={13} text="stuck, with the closure axiom" />
    </A>
  </Svg>
)

const g = lean.gammaD
const def = gammaSource(g.definedness)
const arity = gammaSource(g.arityPred)
const tr = source('trAxiom')
const gamma = source('gammaDef')
const items = gammaSource(...g.predEqs, ...g.rules)
const itemLine = (i: number) => [g.predEqs.concat(g.rules)[i].line + 1]
const rules = gammaSource(...g.rules)
const next = source('sNext')
const closure = source('closureItem')
const all = source('allNext')
const root = source('peanoRoot')

export const lesson2: Lesson = {
  id: 'matching-logic',
  number: 2,
  title: 'Matching logic from scratch',
  scenes: [
    {
      id: 'm1',
      title: 'Patterns denote sets',
      panes: [
        { id: 'p', label: 'The syntax', source: pattern },
        { id: 's', label: 'What a pattern denotes', source: semantics },
      ],
      frames: [
        { say: "Lesson 1 ended with a question: what is a step, precisely? K has an official answer. A K definition, once compiled to KORE, is a ==theory== in matching logic, and a configuration steps to another when the theory says so in every one of its models. You'll build that from nothing. This is real Lean: the matching-logic library the package builds on." },
        { say: "In first-order logic, a term denotes one element and a formula is true or false. Matching logic has one kind of thing instead, the ==pattern==, and a pattern denotes a set of elements: the elements that match it." },
        { hl: { p: span(pattern, 'inductive Pattern', 'mu : SVar') }, notes: [note('p', lineOf(pattern, 'inductive Pattern'), "Variables, symbols, application, implication, `⊥`, `∃` and `μ`: eight constructors, nothing else.")] },
        { hl: { s: span(semantics, 'structure Interpretation', 'evalApp : M → M → Set M') }, notes: [note('s', lineOf(semantics, 'structure Interpretation'), "A model: a set of elements, a set of elements for each symbol, and, for two elements, the set you get by applying the first to the second.")] },
      ],
    },
    {
      id: 'm2',
      title: 'Five elements, by hand',
      visual: (at) => <Dots k={dotsOrder[at]} />,
      panes: [{ id: 's', label: 'What a pattern denotes', source: semantics }],
      frames: [
        { say: "Take a model with five elements. One stands for the symbol `s`, one for `⌈ ⌉`, which you'll meet soon, and three are numbers." },
        { hl: { s: [lineOf(semantics, '| symbol σ => I.evalSymb σ')] }, notes: [note('s', lineOf(semantics, '| symbol σ => I.evalSymb σ'), "A symbol denotes its set.")], say: "`z` denotes the element `z`." },
        { hl: { s: span(semantics, '| p₁ ⬝ p₂ =>') }, notes: [note('s', lineOf(semantics, '| p₁ ⬝ p₂ =>'), "Every result of applying an element of the left set to an element of the right one.")], say: "Here `s` applied to `z` gives `s(z)`." },
        {
          hl: { s: span(semantics, '| p₁ ⬝ p₂ =>') },
          say: "This model gives nothing when `s` is applied to `s(s(z))`. So `s ⬝ (s ⬝ (s ⬝ z))` denotes no element: a pattern can denote the ==empty set==.",
        },
        { hl: { s: [lineOf(semantics, '| evar x => { eval.evalEvar x }')] }, notes: [note('s', lineOf(semantics, '| evar x => { eval.evalEvar x }'), "One element: the one the valuation gives it.")] },
        { hl: { s: [lineOf(semantics, '| evar x => { eval.evalEvar x }'), lineOf(semantics, '| p₁ ⬝ p₂ =>')] }, say: "Patterns with variables denote sets as well. With `x` at `s(z)`, `s ⬝ x` denotes `s(s(z))`." },
        {
          hl: { s: span(semantics, '| ∃∃ x φ =>') },
          notes: [note('s', lineOf(semantics, '| ∃∃ x φ =>'), "The union of φ over every value of x.")], say: "Here: everything that is `s` of something.",
          ask: {
            q: "In first-order logic a formula is true or false. What plays that role here, so far?",
            options: ["Nothing yet: every pattern denotes a set", "A pattern that denotes the empty set is false, and any other is true", "The symbol `⊤`"],
            answer: 0,
            why: "The next scene says when a pattern counts as true: when it denotes every element.",
          },
        },
      ],
    },
    {
      id: 'm3',
      title: 'Complement, and the connectives',
      visual: () => <Dots k="notEx" wide />,
      panes: [
        { id: 's', label: 'What a pattern denotes', source: semantics },
        { id: 'n', label: 'Notations defined from them', source: notations },
      ],
      arrange: 'top',
      frames: [
        { hl: { s: [lineOf(semantics, '| φ ⇒ ψ =>'), lineOf(semantics, '| ⊥ => fun _ => False')], n: span(notations, 'def negation', 'def conjunction') }, notes: [note('s', lineOf(semantics, '| φ ⇒ ψ =>'), "Not in the first set, or in the second."), note('s', lineOf(semantics, '| ⊥ => fun _ => False'), "The empty set."), note('n', lineOf(notations, 'def negation'), "The complement: `∼φ` is `φ ⇒ ⊥`.")], say: "The other connectives are defined from these." },
      ],
    },
    {
      id: 'm4',
      title: 'When a pattern holds, and Γ ⊧ φ',
      visual: truth,
      arrange: 'top',
      panes: [
        { id: 'e', label: 'Holding, and entailment', source: entails },
        { id: 'd', label: 'Definedness', source: definedness },
      ],
      frames: [
        { hl: { e: span(entails, 'def Valuation.satifies', 'fun φ => ∀ eval : Valuation M') }, notes: [note('e', lineOf(entails, 'def Valuation.satifies'), "It denotes every element, under every valuation of its variables.")], say: "When does a pattern count as true? When it ==holds== in a model." },
        { say: "`∃∃ x (s ⬝ x)` does not hold in the five-element model: `z` and the two symbol elements are not `s` of anything." },
        { say: "`x ⇒ x` holds. Whatever x is, every element is either not x or x." },
        { hl: { d: span(definedness, 'notation "⌈"', 'def definedness') }, notes: [note('d', lineOf(definedness, 'notation "⌈"'), "In every model of this axiom, `⌈φ⌉` denotes every element if φ denotes some element, and none otherwise.")], say: "To say \"this exists\" as a pattern that holds or fails, matching logic uses a symbol `⌈ ⌉` and the axiom `∀x. ⌈x⌉`." },
        { hl: { d: [lineOf(definedness, 'def definedness')] }, say: "So `⌈s ⬝ (s ⬝ (s ⬝ z))⌉` fails in this model, because there that term denotes nothing. Equality and membership are built the same way, from `⌈ ⌉`." },
        {
          hl: { e: span(entails, 'def entails', '∀ {M : Type} [Inhabited M]') },
          notes: [note('e', lineOf(entails, 'def entails'), "φ holds in every model of Γ: not in one chosen model, in all of them.")], say: "This is how a K definition gets its meaning: the axioms of its KORE, and what holds in every model of them.",
          ask: {
            q: "A theory with fewer axioms entails what, compared with one with more?",
            options: ["More patterns, because it has fewer constraints", "Fewer or the same: it has more models, and a pattern must hold in each of them", "The same patterns"],
            answer: 1,
            why: "Keep this in mind for the last scene. Without one extra axiom, \"`done(z)` is stuck\" fails in some model.",
          },
        },
      ],
    },
    {
      id: 'm5',
      title: "peano's theory, Γ_D",
      panes: [
        { id: 'y', label: 'Γ_D', source: gamma },
        { id: 'd', label: 'Γ_D, the encoding', source: def },
      ],
      frames: [
        { say: "The KORE file of lesson 1 is a list of declarations and axioms. The package translates it, mechanically, into a set of matching-logic patterns, Γ_D. Lesson 1's question now has a precise form: ==which steps does Γ_D entail?==" },
        { hl: { y: span(gamma, 'def ΓD', 'fun φ => itemsPremises') }, say: "Γ_D has " + fmt(g.signature) + " axioms that encode KORE's sorts and symbols in matching logic, and " + fmt(g.axioms) + " more, one for each axiom of the KORE text. Printed out, they are " + fmt(g.nodes) + " pattern nodes." },
        { hl: { d: [g.definedness.line + 1] }, notes: [note('d', g.definedness.line + 1, "The definedness axiom you just saw.")] },
      ],
    },
    {
      id: 'm6',
      title: 'How an axiom gets translated',
      panes: [
        { id: 'a', label: 'Γ_D, an arity axiom', source: arity },
        { id: 't', label: 'How a KORE axiom is translated', source: tr },
      ],
      frames: [
        { hl: { a: [g.arityPred.line + 1] }, notes: [note('a', g.arityPred.line + 1, "`pred` applied to elements of sort Nat gives elements of sort Nat.")], say: "Sorts are patterns too: `⟦SortNat⟧` denotes the elements of sort Nat." },
        { hl: { t: [lineOf(tr, 'let ws := free.map (guardOf t)'), lineOf(tr, 'pat := conjList ws ⇒')] }, notes: [note('t', lineOf(tr, 'let ws := free.map (guardOf t)'), "A guard gives each variable its sort."), note('t', lineOf(tr, 'pat := conjList ws ⇒'), "Under the guards, the translated pattern equals the whole sort: that is, it holds.")], say: "Each KORE axiom is translated the same way." },
      ],
    },
    {
      id: 'm7',
      title: "pred and the rules, in Γ_D",
      panes: [{ id: 'g', label: "Γ_D, pred's equations and the rules", source: items }],
      frames: [
        {
          hl: { g: itemLine(0) },
          notes: [note('g', itemLine(0)[0], "For X0 and VarN of sort Nat, if X0 is in `s VarN`, then `pred X0` equals VarN.")], say: "`pred`'s first equation.",
          ask: {
            q: "The KORE equation has no sort guards. Where do `VarN ∈ ⟦SortNat⟧` and the others come from?",
            options: ["kompile writes them into the attributes", "From the translation: variables range over all elements in matching logic, so a guard restricts each one to its sort", "They are redundant and could be dropped"],
            answer: 1,
            why: "Every free variable of a KORE axiom has a sort. The translation turns that sort into a guard.",
          },
        },
        { hl: { g: itemLine(1) }, notes: [note('g', itemLine(1)[0], "If X0 is not `s` of anything, then `pred X0` equals `z`.")], say: "The `[owise]` equation." },
        { hl: { g: itemLine(2) }, notes: [note('g', itemLine(2)[0], "A configuration that matches the left-hand side is in `•` of the right-hand side.")], say: "The first rule. `•` is one more symbol of the theory, and the next scene says what it means." },
      ],
    },
    {
      id: 'm8',
      title: 'Steps are •',
      visual: chain('rule'),
      arrange: 'top',
      panes: [
        { id: 'n', label: 'One-path next', source: next },
        { id: 'g', label: "Γ_D, peano's rules", source: rules },
      ],
      frames: [
        { hl: { n: [lineOf(next, 'def sNext')] }, notes: [note('n', lineOf(next, 'def sNext'), "The configurations that can take one step into φ.")], say: "`•φ` is the symbol `next` applied to φ." },
        { hl: { g: [g.rules[0].line + 1] }, notes: [note('g', g.rules[0].line + 1, "Every configuration that matches the left-hand side is in `•` of the right-hand side: it can step there.")] },
      ],
    },
    {
      id: 'm9',
      title: 'What Γ_D leaves open',
      visual: chain('ghost'),
      arrange: 'top',
      panes: [{ id: 'p', label: 'What is stated for peano', source: root }],
      frames: [
        { hl: { p: span(root, 'theorem step_c₀') }, notes: [note('p', lineOf(root, 'theorem step_c₀'), "`run(s(z))` implies `•run(z)`. Its proof is not written.", 'sorry')], say: "So for peano, Γ_D should entail this." },
        {
          hl: { p: span(root, 'theorem stuck_c₂_needs_closure') },
          notes: [note('p', lineOf(root, 'theorem stuck_c₂_needs_closure'), "A model may add a step from `done(z)`, and no axiom of Γ_D excludes it. Stated too, also unproved.", 'sorry')], say: "Γ_D says which steps exist. It does not say that no others do.",
          ask: {
            q: "Why does \"`done(z)` is stuck\" need an extra axiom, when \"`run(z)` steps to `done(z)`\" does not?",
            options: ["The rule axioms only add steps: a model with more steps still satisfies them, so a claim that a step is absent cannot follow from them", "`done(z)` has no sort", "Because `done` is not a function"],
            answer: 0,
            why: "\"Holds in every model\" cuts both ways. Absence has to be said by an axiom of its own.",
          },
        },
      ],
    },
    {
      id: 'm10',
      title: 'The closure axiom',
      visual: chain('closure'),
      arrange: 'top',
      panes: [
        { id: 'c', label: 'The closure axiom', source: closure },
        { id: 'o', label: 'All-path next', source: all },
        { id: 'p', label: 'What is stated for peano', source: root },
      ],
      frames: [
        { hl: { c: [lineOf(closure, 'def closureItem'), lineOf(closure, 'pat := ∀∀ y')] }, notes: [note('c', lineOf(closure, 'def closureItem'), "Every step is an instance of some rule.")], say: "The closure axiom is the missing half." },
        { hl: { o: span(all, '/-- `◦φ ≡ ¬•¬φ`', 'def allNext') }, notes: [note('o', lineOf(all, '/-- `◦φ ≡ ¬•¬φ`'), "Every successor is in φ. `◦⊥` says there is none: the configuration is stuck.")] },
        { hl: { p: [lineOf(root, 'theorem complete_c₀'), lineOf(root, 'theorem stuck_c₂ :')] }, notes: [note('p', lineOf(root, 'theorem complete_c₀'), "`run(s(z))` has no successor but `run(z)`. Stated, not yet proved.", 'sorry'), note('p', lineOf(root, 'theorem stuck_c₂ :'), "`done(z)` is stuck. Stated, not yet proved.", 'sorry')], say: "Lesson 8's soundness and completeness theorem says the same for every configuration of every definition." },
        { say: "So this is K's meaning of a step, and lesson 6 counts its lines. But it isn't something a proof assistant can compute with. \"Holds in every model\" quantifies over all sets and all interpretations, so even \"`run(s(z))` steps to `run(z)`\" needs a proof. That's why the proofs of lessons 4 to 7 use ==a second definition== of a step, and lesson 8 states the theorem that would make the two agree." },
      ],
    },
  ],
  quiz: [
    {
      q: "What does `z ⋁ ∃∃ x (s ⬝ x)` denote in the five-element model?",
      options: ["Only `z`", "The three numbers: `z`, `s(z)` and `s(s(z))`", "Every element"],
      answer: 1,
      why: "A disjunction is a union, and `∃∃ x (s ⬝ x)` is `s(z)` and `s(s(z))`.",
    },
    {
      q: "Does `Γ ⊧ φ` depend on which model you picked?",
      options: ["Yes, you pick the intended one", "No: it quantifies over every model of Γ"],
      answer: 1,
      why: "A fact about one model, such as the five-element one, is not a consequence of Γ unless it holds in all of them.",
    },
    {
      q: "Does the order of the axioms in the KORE text matter to Γ_D?",
      options: ["Yes, the first matching axiom wins", "Not to its models"],
      answer: 1,
      why: "The package proves that a KORE text whose sentences are a reordering of another's has a theory with the same models (`reordered_sameModels`, lesson 3).",
    },
    {
      q: "Which of the peano statements of the last scene are proved?",
      options: ["All of them", "`step_c₀` only", "None"],
      answer: 2,
      why: "They are the matching-logic side of the project, stated so that the gap is visible. Lesson 8 shows how the proved Lean side and this side are meant to meet.",
    },
  ],
  checked: [
    "The Lean panes are the files at the recorded commit. The Γ_D panes are the package's own printing of peano's theory, regenerated from its KORE by the package's translator.",
    "The five-element model is an illustration. Its sets were computed for this page by the clauses of `Pattern.interpret` shown beside it, not by Lean.",
    "The peano statements of the last scenes are stated in Lean and type-checked. Their proofs are `sorry`, and the build marks each one as unproved.",
  ],
  tryit: [
    { say: "In the kcore-spec package directory:", cmd: "lake build\nlake exe gammad > GAMMA_D.txt   # peano's Γ_D, printed in the notation of the Γ_D panes" },
    { say: "The statements of the last scenes are in `KcoreSpec/PeanoSpec.lean`; `lake env lean KcoreSpec/PeanoSpec.lean` reports each `sorry`." },
  ],
}
