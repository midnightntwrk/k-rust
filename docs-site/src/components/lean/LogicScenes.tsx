'use client'

// Lesson "Matching logic from scratch": patterns as sets, truth in a model, the theory Γ_D that the
// KORE text of peano translates to, and steps as the symbol •. The Lean panes are aml-port (the
// port of the matching-logic library the package builds on) and kcore-spec; the Γ_D items are the
// package's own printing of peano's theory (GAMMA_D.txt). The five-element model of the first two
// scenes is an illustration: its sets are computed below by the clauses of `Pattern.interpret`
// shown beside it, not by Lean.

import { fmt, gammaSource, lean, lineOf, source, span } from './data'
import { LessonScene, type Step } from './LessonScene'
import styles from './Lesson.module.css'

const pattern = source('amlPattern')
const semantics = source('amlSemantics')
const notations = source('amlNotations')
const entails = source('amlEntails')
const definedness = source('amlDefinedness')

// ---- a five-element model, for illustration ---------------------------------------------------

type E = 'σ' | 'δ' | '0' | '1' | '2'
const M: readonly E[] = ['σ', 'δ', '0', '1', '2']
type P =
  | { evar: 'x' }
  | { sym: 'z' | 's' | 'def' }
  | { app: [P, P] }
  | { imp: [P, P] }
  | { bot: true }
  | { ex: P }

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

type Shown = { text: string; p: P; x?: E }
const shown: Record<string, Shown> = {
  none: { text: 'the five elements', p: { bot: true } },
  z: { text: 'z', p: z },
  sz: { text: 's ⬝ z', p: app(s, z) },
  sss: { text: 's ⬝ (s ⬝ (s ⬝ z))', p: app(s, app(s, app(s, z))) },
  x: { text: 'x, with x ↦ 1', p: x, x: '1' },
  sx: { text: 's ⬝ x, with x ↦ 1', p: app(s, x), x: '1' },
  ex: { text: '∃∃ x (s ⬝ x)', p: exS },
  notEx: { text: '∼(∃∃ x (s ⬝ x)), that is (∃∃ x (s ⬝ x)) ⇒ ⊥', p: neg(exS) },
  xx: { text: 'x ⇒ x', p: { imp: [x, x] } },
  ceilSz: { text: '⌈s ⬝ z⌉', p: ceil(app(s, z)) },
  ceilSss: { text: '⌈s ⬝ (s ⬝ (s ⬝ z))⌉', p: ceil(app(s, app(s, app(s, z)))) },
}
/** Whether a pattern holds: it denotes every element, under every valuation of x. */
const holds = (p: P) => M.every((v) => interpret(p, v).size === M.length)

const label: Record<E, string> = { σ: 's', δ: '⌈ ⌉', '0': 'z', '1': 's(z)', '2': 's(s(z))' }

function Dots({ k }: { k: keyof typeof shown }) {
  const it = shown[k]
  const set = k === 'none' ? new Set<E>() : interpret(it.p, it.x ?? '0')
  return (
    <div className={styles.setView}>
      <div className={styles.setHead}>
        <code>{it.text}</code>
        {k !== 'none' && <span className={styles.small}>denotes {set.size === 0 ? 'the empty set' : set.size === M.length ? 'every element' : `{${[...set].map((e) => label[e]).join(', ')}}`}</span>}
      </div>
      <div className={styles.dots} role="img" aria-label={`elements of the model; in the set: ${[...set].map((e) => label[e]).join(', ') || 'none'}`}>
        {M.map((e) => (
          <div key={e} className={`${styles.dot} ${set.has(e) ? styles.dotIn : ''}`}>
            <span className={styles.dotMark}>{e}</span>
            <span className={styles.small}>{label[e]}</span>
          </div>
        ))}
      </div>
    </div>
  )
}

// ---- 1. Patterns denote sets -------------------------------------------------------------------

export function PatternsScene() {
  const order: (keyof typeof shown)[] = ['none', 'none', 'z', 'sz', 'sss', 'x', 'sx', 'ex', 'notEx']
  if (interpret(shown.sss.p, '0').size !== 0 || interpret(exS, '0').size !== 2) throw new Error('lean lessons: the illustration model changed')
  const steps: Step[] = [
    { say: <>A pattern is built from variables, symbols, application, implication, <code>⊥</code>, <code>∃</code> and <code>μ</code>: eight constructors, nothing else.</>, hl: { p: span(pattern, 'inductive Pattern', 'mu : SVar') }, panes: ['p', 's'] },
    { say: <>A model gives a set of elements, a set of elements for each symbol, and for two elements a set: what applying the first to the second gives.</>, hl: { s: span(semantics, 'structure Interpretation', 'evalApp : M → M → Set M') }, panes: ['p', 's'] },
    { say: <>Take a model with five elements: one stands for the symbol <code>s</code>, one for <code>⌈ ⌉</code> (scene 2), and three numbers. A symbol denotes its set: <code>z</code> denotes the element <code>z</code>.</>, hl: { s: [lineOf(semantics, '| symbol σ => I.evalSymb σ')] }, panes: ['s'] },
    { say: <>Application collects every result of applying an element of the left set to an element of the right one. Here <code>s</code> applied to <code>z</code> gives <code>s(z)</code>.</>, hl: { s: span(semantics, '| p₁ ⬝ p₂ =>') }, panes: ['s'] },
    { say: <>This model gives nothing when <code>s</code> is applied to <code>s(s(z))</code>, so <code>s ⬝ (s ⬝ (s ⬝ z))</code> denotes no element. A pattern can denote the empty set.</>, hl: { s: span(semantics, '| p₁ ⬝ p₂ =>') }, panes: ['s'] },
    { say: <>A variable denotes one element, the one the valuation gives it.</>, hl: { s: [lineOf(semantics, '| evar x => { eval.evalEvar x }')] }, panes: ['s'] },
    { say: <>Patterns with variables denote sets as well: with <code>x</code> at <code>s(z)</code>, <code>s ⬝ x</code> denotes <code>s(s(z))</code>.</>, hl: { s: [lineOf(semantics, '| evar x => { eval.evalEvar x }'), lineOf(semantics, '| p₁ ⬝ p₂ =>')] }, panes: ['s'] },
    { say: <><code>∃∃ x φ</code> is the union of φ over every value of x: here, everything that is <code>s</code> of something.</>, hl: { s: span(semantics, '| ∃∃ x φ =>') }, panes: ['s'] },
    { say: <>Implication is "not in the first set, or in the second". With <code>⊥</code>, the empty set, it gives the complement. The other connectives are defined from these.</>, hl: { s: [lineOf(semantics, '| φ ⇒ ψ =>'), lineOf(semantics, '| ⊥ => fun _ => False')], n: span(notations, 'def negation', 'def conjunction') }, panes: ['s', 'n'] },
  ]
  return (
    <LessonScene
      title="Patterns denote sets"
      panes={[
        { id: 'p', label: 'The syntax', source: pattern },
        { id: 's', label: 'What a pattern denotes in a model', source: semantics },
        { id: 'n', label: 'Notations defined from them', source: notations },
      ]}
      steps={steps}
      visual={(at) => <Dots k={order[at]} />}
      questions={[
        { q: <>What does <code>z ⋁ ∃∃ x (s ⬝ x)</code> denote in the five-element model?</>,
          a: <>The three numbers: <code>z</code>, <code>s(z)</code> and <code>s(s(z))</code>. A disjunction is a union.</> },
        { q: 'In first-order logic a formula is true or false. What plays that role here?',
          a: <>Nothing yet: every pattern denotes a set. Scene 2 says when a pattern counts as true: when it denotes every element.</> },
      ]}
    />
  )
}

// ---- 2. When a pattern holds ---------------------------------------------------------------------

export function TruthScene() {
  const rows: (keyof typeof shown)[] = ['ex', 'xx', 'ceilSz', 'ceilSss']
  const focus: (keyof typeof shown | null)[] = [null, 'ex', 'xx', 'ceilSz', 'ceilSss', null]
  if (holds(exS) || !holds(shown.xx.p) || !holds(shown.ceilSz.p) || holds(shown.ceilSss.p)) throw new Error('lean lessons: the illustration model changed')
  const steps: Step[] = [
    { say: <>A pattern holds in a model when it denotes every element, under every valuation of its variables.</>, hl: { e: span(entails, 'def Valuation.satifies', 'fun φ => ∀ eval : Valuation M') }, panes: ['e'] },
    { say: <><code>∃∃ x (s ⬝ x)</code> does not hold in the five-element model: <code>z</code> and the two symbol elements are not <code>s</code> of anything.</>, panes: ['e'] },
    { say: <><code>x ⇒ x</code> holds: whatever x is, every element is either not x or x.</>, panes: ['e'] },
    { say: <>To say "this exists" as a pattern that holds or fails, matching logic uses a symbol <code>⌈ ⌉</code> and the axiom <code>∀x. ⌈x⌉</code>: in every model of it, <code>⌈φ⌉</code> denotes every element if φ denotes some element, and none otherwise.</>, hl: { d: span(definedness, 'notation "⌈"', 'def definedness') }, panes: ['e', 'd'] },
    { say: <>So <code>⌈s ⬝ (s ⬝ (s ⬝ z))⌉</code> fails in this model: there, that term denotes nothing. Equality and membership are built the same way, from <code>⌈ ⌉</code>.</>, hl: { d: [lineOf(definedness, 'def definedness')] }, panes: ['e', 'd'] },
    { say: <><code>Γ ⊧ φ</code>: φ holds in every model of Γ. Not in one chosen model, in all of them. This is how a K definition gets its meaning: the axioms of its KORE, and what holds in every model of them.</>, hl: { e: span(entails, 'def entails', '∀ {M : Type} [Inhabited M]') }, panes: ['e', 'd'] },
  ]
  return (
    <LessonScene
      title="When a pattern holds, and Γ ⊧ φ"
      panes={[
        { id: 'e', label: 'Holding, and entailment', source: entails },
        { id: 'd', label: 'Definedness', source: definedness },
      ]}
      steps={steps}
      visual={(at) => (
        <div className={styles.tableWrap}>
          <table className={styles.table}>
            <thead>
              <tr><th scope="col">pattern</th><th scope="col">denotes, in the five-element model</th><th scope="col">holds there</th></tr>
            </thead>
            <tbody>
              {rows.map((k) => {
                const set = interpret(shown[k].p, '0')
                const on = focus[at] === null ? undefined : focus[at] === k
                return (
                  <tr key={k} className={on ? styles.on : on === false ? styles.off : ''}>
                    <td><code>{shown[k].text}</code></td>
                    <td>{set.size === M.length ? 'every element' : set.size === 0 ? 'nothing' : [...set].map((e) => label[e]).join(', ')}</td>
                    <td>{holds(shown[k].p) ? 'yes' : 'no'}</td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </div>
      )}
      questions={[
        { q: <>Does <code>Γ ⊧ φ</code> depend on which model you picked?</>,
          a: <>No, that is the point: it quantifies over every model of Γ. A fact about one model, such as the five-element one, is not a consequence of Γ unless it holds in all of them.</> },
        { q: <>Why can a theory with fewer axioms entail fewer patterns?</>,
          a: <>It has more models, and a pattern must hold in each of them. Scene 4 uses exactly this: without one extra axiom, "done(z) is stuck" fails in some model.</> },
      ]}
    />
  )
}

// ---- 3. From KORE axioms to Γ_D ---------------------------------------------------------------------

export function GammaScene() {
  const g = lean.gammaD
  const items = gammaSource(...g.predEqs, ...g.rules)
  const def = gammaSource(g.definedness)
  const arity = gammaSource(g.arityPred)
  const tr = source('trAxiom')
  const gamma = source('gammaDef')
  const at = (i: number) => [g.predEqs.concat(g.rules)[i].line + 1]
  const steps: Step[] = [
    { say: <>Γ_D, the theory of peano's KORE, has {fmt(g.signature)} axioms that encode KORE's sorts and symbols in matching logic, and {fmt(g.axioms)} more, one for each axiom of the KORE text. Printed out, they are {fmt(g.nodes)} pattern nodes.</>, hl: { y: span(gamma, 'def ΓD', 'fun φ => itemsPremises') }, panes: ['y', 'd'] },
    { say: <>The first encoding axiom is the definedness axiom of scene 2.</>, hl: { d: [g.definedness.line + 1] }, panes: ['y', 'd'] },
    { say: <>Sorts are patterns too: <code>⟦SortNat⟧</code> denotes the elements of sort Nat. The arity axiom of <code>pred</code> says that <code>pred</code> applied to elements of sort Nat gives elements of sort Nat.</>, hl: { a: [g.arityPred.line + 1] }, panes: ['a', 't'] },
    { say: <>Each KORE axiom is translated the same way: under guards that give each variable its sort, the translated pattern equals the whole sort, that is, it holds.</>, hl: { t: [lineOf(tr, 'let ws := free.map (guardOf t)'), lineOf(tr, 'pat := conjList ws ⇒')] }, panes: ['a', 't'] },
    { say: <><code>pred</code>'s first equation: for X0 and VarN of sort Nat, if X0 is in <code>s VarN</code>, then <code>pred X0</code> equals VarN.</>, hl: { g: at(0) }, panes: ['g'] },
    { say: <>The <code>[owise]</code> equation: if X0 is not <code>s</code> of anything, then <code>pred X0</code> equals <code>z</code>.</>, hl: { g: at(1) }, panes: ['g'] },
    { say: <>The first rule: a configuration that matches the left-hand side is in <code>•</code> of the right-hand side. <code>•</code> is one more symbol of the theory; scene 4 says what it means.</>, hl: { g: at(2) }, panes: ['g'] },
  ]
  return (
    <LessonScene
      title="From peano's KORE to Γ_D"
      panes={[
        { id: 'y', label: 'Γ_D', source: gamma },
        { id: 'd', label: 'Γ_D, the encoding', source: def },
        { id: 'a', label: 'Γ_D, an arity axiom', source: arity },
        { id: 't', label: 'How a KORE axiom is translated', source: tr },
        { id: 'g', label: "Γ_D, pred's equations and the rules", source: items },
      ]}
      steps={steps}
      questions={[
        { q: <>The KORE equation for <code>pred</code> has no sort guards. Where do <code>VarN ∈ ⟦SortNat⟧</code> and the others come from?</>,
          a: <>From the translation: every free variable of a KORE axiom has a sort, and in matching logic, where variables range over all elements, the guard restricts it to that sort.</> },
        { q: 'Does the order of the axioms in the KORE text matter to Γ_D?',
          a: <>Not to its models. The package proves that a KORE text whose sentences are a reordering of another's has a theory with the same models (<code>reordered_sameModels</code>, lesson 3).</> },
      ]}
    />
  )
}

// ---- 4. Steps are • -----------------------------------------------------------------------------------

export function NextScene() {
  const g = lean.gammaD
  const rules = gammaSource(...g.rules)
  const next = source('sNext')
  const closure = source('closureItem')
  const all = source('allNext')
  const root = source('peanoRoot')
  const extra = [false, false, false, true, false, false, false]
  const steps: Step[] = [
    { say: <><code>•φ</code> is the symbol <code>next</code> applied to φ. Its intended meaning: the configurations that can take one step into φ.</>, hl: { n: [lineOf(next, 'def sNext')] }, panes: ['n', 'g'] },
    { say: <>A rule's axiom puts every configuration that matches its left-hand side into <code>•</code> of its right-hand side: it can step there.</>, hl: { g: [g.rules[0].line + 1] }, panes: ['n', 'g'] },
    { say: <>So for peano, Γ_D should entail "<code>run(s(z))</code> implies <code>•run(z)</code>". The package states this, and its proof is not written: it is <code>sorry</code>.</>, hl: { p: span(root, 'theorem step_c₀') }, panes: ['p'] },
    { say: <>Γ_D says which steps exist. It does not say that no others do: a model may add a step from <code>done(z)</code>, and no axiom of Γ_D excludes it. That is stated too, also <code>sorry</code>.</>, hl: { p: span(root, 'theorem stuck_c₂_needs_closure') }, panes: ['p'] },
    { say: <>The closure axiom is the missing half: every step is an instance of some rule.</>, hl: { c: [lineOf(closure, 'def closureItem'), lineOf(closure, 'pat := ∀∀ y')] }, panes: ['c'] },
    { say: <><code>◦φ</code>, defined as <code>¬•¬φ</code>, says that every successor is in φ. <code>◦⊥</code> says there is none: the configuration is stuck.</>, hl: { o: span(all, '/-- `◦φ ≡ ¬•¬φ`', 'def allNext') }, panes: ['o', 'p'] },
    { say: <>With the closure axiom, <code>run(s(z))</code> has no successor but <code>run(z)</code>, and <code>done(z)</code> is stuck. Both are stated for peano and not yet proved. Lesson 8's Theorem A says the same for every configuration of every definition.</>, hl: { p: [lineOf(root, 'theorem complete_c₀'), lineOf(root, 'theorem stuck_c₂ :')] }, panes: ['o', 'p'] },
  ]
  return (
    <LessonScene
      title="Steps are •, and the closure axiom"
      panes={[
        { id: 'n', label: 'One-path next', source: next },
        { id: 'g', label: "Γ_D, peano's rules", source: rules },
        { id: 'c', label: 'The closure axiom', source: closure },
        { id: 'o', label: 'All-path next', source: all },
        { id: 'p', label: 'What is stated for peano', source: root },
      ]}
      steps={steps}
      visual={(at) => (
        <div className={styles.chain}>
          <div className={`${styles.node} ${at >= 2 ? styles.on : ''}`}><code>run(s(z))</code></div>
          <div className={styles.arrow}>•</div>
          <div className={styles.node}><code>run(z)</code></div>
          <div className={styles.arrow}>•</div>
          <div className={`${styles.node} ${at === 3 ? styles.on : ''} ${at >= 6 ? styles.stuck : ''}`}>
            <code>done(z)</code>
            <span className={styles.small}>{extra[at] ? 'some model of Γ_D adds a step here' : at >= 6 ? 'stuck, with the closure axiom' : ''}</span>
          </div>
        </div>
      )}
      questions={[
        { q: <>Why does "<code>done(z)</code> is stuck" need an extra axiom, when "<code>run(z)</code> steps to <code>done(z)</code>" does not?</>,
          a: <>The rule axioms only add steps. A model with more steps still satisfies them, so a claim that a step is absent cannot follow from them alone.</> },
        { q: 'Which of the statements in the last pane are proved?',
          a: <>None. They are the matching-logic side of the project, stated so that the gap is visible. Lesson 8 shows how the proved Lean side and this side are meant to meet.</> },
      ]}
    />
  )
}
