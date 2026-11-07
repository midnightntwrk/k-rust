'use client'

// Lesson "A definition and its steps": peano.k, the KORE kompile writes for it, a run of it with
// krust, and what a run cannot show. The KORE is kompile's output; the run is krust's output,
// captured by the generator's krun script; the extra configurations and their successors were
// computed by Lean on the package's data (Facts.lean).

import {
  type Ground,
  config,
  fmt,
  groundText,
  kItem,
  koreAxiom,
  lean,
  lineOf,
  peanoK,
  span,
  textSource,
} from './data'
import { type Pane, LessonScene, type Step } from './LessonScene'
import styles from './Lesson.module.css'

const rule0 = koreAxiom('rule', 0)
const eq0 = koreAxiom('equation', 0)
const eq1 = koreAxiom('equation', 1)
// The two equations in one pane, the attribute lines between them elided.
const eqs = { ...eq0, end: eq1.end, text: [eq0.text, ...Array(eq1.start - eq0.end - 1).fill('…'), eq1.text].join('\n') }
const emitStats = lean.facts.emit
const userModule = emitStats.modules[emitStats.modules.length - 1]
const totalSentences = emitStats.modules.reduce((sum, m) => sum + m.sentences, 0)

if (userModule.name !== 'PEANO') throw new Error('lean lessons: the last emitted module is not PEANO')
if (!emitStats.equalsKore) throw new Error('lean lessons: the emitted KORE no longer equals kompile’s for peano')

// ---- 1. From peano.k to KORE ---------------------------------------------------------------------

export function KompileScene() {
  const panes: Pane[] = [
    { id: 'k', label: 'What you wrote', source: peanoK },
    { id: 'r', label: 'What kompile wrote for the first rule', source: rule0 },
    { id: 'e', label: 'The equations of pred, as kompile wrote them', source: eqs },
  ]
  const steps: Step[] = [
    { say: <>This is the whole definition: numbers built from <code>z</code> and <code>s</code>, a function <code>pred</code>, a state that is <code>run(n)</code> or <code>done(v)</code>, and two rules that rewrite the k cell.</>, hl: { k: span(peanoK, 'module PEANO', 'endmodule') }, panes: ['k'] },
    { say: <>The first rule says: when the k cell holds <code>run(s(N))</code>, replace it by <code>run(pred(s(N)))</code>.</>, hl: { k: [lineOf(peanoK, 'rule <k> run(s(N))')] }, panes: ['k', 'r'] },
    { say: <>kompile turns it into one KORE axiom, <code>\rewrites</code>, over the whole configuration: the top cell, the k cell, and a counter cell the source never mentions.</>, hl: { r: [lineOf(rule0, '\\rewrites'), lineOf(rule0, "Lbl'-LT-'generatedTop'-GT-'"), lineOf(rule0, "Var'Unds'DotVar0")] }, panes: ['k', 'r'] },
    { say: <>The two copies of <code>s(N)</code> become one shared subterm: <code>\and</code> of the pattern and a fresh variable, which the right-hand side reuses.</>, hl: { r: [lineOf(rule0, 'VarN'), lineOf(rule0, 'Lblpred')] }, panes: ['k', 'r'] },
    { say: <>The function's two equations become two axioms. The first applies when the argument is <code>s(N)</code>.</>, hl: { k: [lineOf(peanoK, 'rule pred(s(N))')], e: span(eqs, 'axiom{R}', 'Lblpred', eq0.start - 1) }, panes: ['k', 'e'] },
    { say: <>The <code>[owise]</code> equation's premise is the negation of the first one's: it applies exactly when no other equation does.</>, hl: { k: [lineOf(peanoK, 'rule pred(_)')], e: [lineOf(eqs, '\\not')] }, panes: ['k', 'e'] },
    { say: <>The KORE file kompile writes for these {peanoK.text.split('\n').length} lines has {emitStats.modules.length} modules and {fmt(totalSentences)} sentences. The module <code>PEANO</code> alone has {fmt(userModule.sentences)}, of which {fmt(emitStats.fixedInUser)} are the same text in every definition.</>, panes: ['k', 'r'] },
  ]
  return (
    <LessonScene
      title="From peano.k to KORE"
      panes={panes}
      steps={steps}
      questions={[
        { q: <>The source rule mentions only the k cell. Why does the KORE rule mention a counter cell?</>,
          a: <>A rule rewrites a whole configuration. kompile completes the rule with the cells it leaves out, as variables, so the rule copies them unchanged.</> },
        { q: <>Why does the <code>[owise]</code> axiom carry a negation instead of an attribute that says "try this last"?</>,
          a: <>A KORE axiom is a logical statement, read without any order. "Last" has to be written as a condition: none of the other equations applies.</> },
      ]}
    />
  )
}

// ---- 2. A run ------------------------------------------------------------------------------------

export function RunScene() {
  const runs = lean.krun.steps
  const src = (d: number) => {
    const found = runs.find((r) => r.depth === d)
    if (!found) throw new Error(`lean lessons: no krun output at depth ${d}`)
    return textSource(`krust krun … --depth ${d}`, found.text)
  }
  if (src(3).text !== src(4).text) throw new Error('lean lessons: the run did not stop after three steps')
  const line = (d: number, needle: string) => [lineOf(src(d), needle)]
  const steps: Step[] = [
    { say: <>krust runs the definition on the program <code>run(s(s(z)))</code>. With <code>--depth 0</code> it shows the starting configuration: the program in the k cell, the counter at 0.</>, hl: { r: line(0, 'Lblrun') }, text: { r: src(0) } },
    { say: <>After one step: <code>run(s(z))</code>. The rule wrote <code>run(pred(s(s(z))))</code>, and evaluating <code>pred</code> is part of the same step.</>, hl: { r: line(1, 'Lblrun') }, text: { r: src(1) } },
    { say: <>After two steps: <code>run(z)</code>.</>, hl: { r: line(2, 'Lblrun') }, text: { r: src(2) } },
    { say: <>After three: <code>done(z)</code>. The <code>z</code> sits under <code>inj{'{'}SortNat, SortVal{'}'}</code>, because <code>done</code> takes a <code>Val</code> and <code>z</code> is a <code>Nat</code>.</>, hl: { r: line(3, 'Lbldone') }, text: { r: src(3) } },
    { say: <>Asking for four steps gives the same configuration: no rule applies to <code>done(z)</code>, so the run stops.</>, hl: { r: line(4, 'Lbldone') }, text: { r: src(4) } },
  ]
  return (
    <LessonScene
      title="A run, as krust prints it"
      panes={[{ id: 'r', label: 'The configuration', source: src(0), note: lean.krun.versions }]}
      steps={steps}
      questions={[
        { q: 'Did this run use the owise equation of pred?',
          a: <>No. Every call was <code>pred(s(…))</code>, which the first equation answers. A program that reaches <code>pred(z)</code> would need another rule; peano's rules never write one.</> },
        { q: 'What would a second run on the same program show?',
          a: <>The same three steps. The run is a computation on one input; it says nothing about other inputs.</> },
      ]}
    />
  )
}

// ---- 3. What a run does not show -------------------------------------------------------------------

export function BeyondRunScene() {
  const c0 = config('c0')
  const c1 = config('c1')
  const c2 = config('c2')
  const c3 = config('c3')
  const kc = config('kconfig')
  const showTerm = (g: Ground) => {
    try {
      return groundText(kItem(g))
    } catch {
      return groundText(g)
    }
  }
  const show = (t: typeof c0) => showTerm(t.term)
  const succ = (t: typeof c0) => (t.successors === null ? 'not a configuration' : t.successors.length === 0 ? 'none' : t.successors.map(showTerm).join(', '))
  const rows = [
    { c: c0, group: 'run' },
    { c: c1, group: 'run' },
    { c: c2, group: 'run' },
    { c: c3, group: 'never' },
    { c: kc, group: 'never' },
  ]
  if ((c3.successors ?? [1]).length !== 0 || (kc.successors ?? [1]).length !== 0) {
    throw new Error('lean lessons: done(s(z)) and the #KConfigValue configuration are no longer stuck')
  }
  const focus: (string | null)[] = [null, 'run', 'never', 'never', null]
  const steps: Step[] = [
    { say: <>Each configuration has a next configuration, or none. These five were computed by the package's step function, which lesson 4 explains.</> },
    { say: <>A run visits one path. The run above starts one step earlier than this table, at <code>run(s(s(z)))</code>, and then visits these three.</> },
    { say: <><code>done(s(z))</code> is a configuration too. No rule writes it, so no run from a program of the form <code>run(n)</code> reaches it.</> },
    { say: <>The fixed signature of every kompiled definition adds configurations no program writes, such as a k cell holding <code>#KConfigValue(.K)</code>.</> },
    { say: <>"A configuration has at most one next one" and "the counter cell never changes" are claims about all of these, and about infinitely many more. A run cannot establish them; a proof can, once "next" has a precise meaning.</> },
  ]
  return (
    <LessonScene
      title="What a run does not show"
      panes={[]}
      steps={steps}
      visual={(at) => (
        <div className={styles.tableWrap}>
          <table className={styles.table}>
            <thead>
              <tr><th scope="col">k cell</th><th scope="col">next</th><th scope="col">reached by the run</th></tr>
            </thead>
            <tbody>
              {rows.map(({ c, group }) => {
                const on = focus[at] === null ? undefined : focus[at] === group
                return (
                  <tr key={c.name} className={on ? styles.on : on === false ? styles.off : ''}>
                    <td><code>{show(c)}</code></td>
                    <td><code>{succ(c)}</code></td>
                    <td>{group === 'run' ? 'yes' : 'no'}</td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </div>
      )}
      questions={[
        { q: <>Why should a statement about peano care about <code>done(s(z))</code> if no run reaches it?</>,
          a: <>Reachability is itself a property that needs proof. A statement over every configuration needs no such proof first, and it remains true for a program you did not think of.</> },
        { q: 'What exactly is "the next configuration"? Write it down before reading on.',
          a: <>That is the question of the next two lessons. Lesson 2 gives K's own answer, in matching logic; lesson 4 gives the answer in Lean that the proofs use.</> },
      ]}
    />
  )
}
