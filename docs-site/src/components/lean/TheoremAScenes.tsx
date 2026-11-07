'use client'

// Lesson "Theorem A": the statement that ties the Lean step of lessons 4 and 5 to the matching-logic
// meaning of lesson 2, its parts, its status, and the evidence that stands in for it until it is
// proved. Panes are Statements.lean and PeanoSpec.lean at the recorded commit.

import { lineOf, source, span } from './data'
import { LessonScene, type Step } from './LessonScene'
import styles from './Lesson.module.css'

const conclusion = source('conclusion')
const stepStmts = source('stepStatements')
const models = source('models')
const theoremA = source('theoremA')
const theoremAKore = source('theoremAKore')
const den = source('den')

// ---- 1. What Theorem A says ------------------------------------------------------------------------

export function StatementScene() {
  const steps: Step[] = [
    { say: <>There are two answers to "what is a step". Lesson 2's: what the theory Γ_D entails, in every model. Lesson 4's: the Lean relation <code>Step</code>, which the proofs use. Theorem A says they agree.</>, panes: ['c'] },
    { say: <>It is about a step function: for each configuration, a finite list of successors. The package's executable step is one, read through the encoding of terms as KORE.</>, hl: { c: span(conclusion, 'structure Conclusion', 'complete : StepComplete c p ref') }, panes: ['c'] },
    { say: <>Sound: for every successor the function lists, Γ_D entails "this configuration implies <code>•</code> that successor". Every listed step is a step in every model.</>, hl: { s: span(stepStmts, 'def StepSound', '∀ t, GroundConfig c t → ∀ t\' ∈ f t, ΓD c p ⊧') }, panes: ['c', 's'] },
    { say: <>Complete: with the closure axiom, Γ_D entails "this configuration implies <code>◦</code> of the listed successors". No model has another step; an empty list means stuck.</>, hl: { s: span(stepStmts, 'def StepComplete', '∀ t, GroundConfig c t → (ΓD c p ∪ Γclosure c p) ⊧') }, panes: ['c', 's'] },
    { say: <>Two conditions keep this from being empty. The theory has a model, so it does not entail everything. And in every model, distinct ground terms denote distinct elements, so a model where everything is one element is excluded.</>, hl: { m: span(models, 'def StdModelOK', 'groundSort c t = groundSort c t\'') }, panes: ['c', 'm'] },
    { say: <>Configurations enter the theory through <code>den</code>, the translation of a ground KORE term into a pattern: the same translation that turns the KORE axioms into Γ_D.</>, hl: { d: [lineOf(den, 'def den')] }, panes: ['s', 'd'] },
    { say: <><code>theoremA</code> claims the conclusion for every well-formed definition and the package's step. Its proof is <code>sorry</code>.</>, hl: { t: [lineOf(theoremA, 'theorem theoremA')] }, panes: ['c', 't'] },
    { say: <><code>theoremA_kore</code> is the form a reader of a KORE file wants: for a text in F0, the conclusion holds. It is proved from <code>theoremA</code> and <code>F0.sound</code>, so it inherits the <code>sorry</code>.</>, hl: { k: span(theoremAKore, 'theorem theoremA_kore', 'exact ⟨d, hwf, he, theoremA d hwf⟩') }, panes: ['t', 'k'] },
  ]
  return (
    <LessonScene
      title="What Theorem A says"
      panes={[
        { id: 'c', label: 'The conclusion', source: conclusion },
        { id: 's', label: 'Sound and complete', source: stepStmts },
        { id: 'm', label: 'Not an empty theory', source: models },
        { id: 'd', label: 'Configurations as patterns', source: den },
        { id: 't', label: 'The theorem', source: theoremA },
        { id: 'k', label: 'For a KORE text', source: theoremAKore },
      ]}
      steps={steps}
      questions={[
        { q: <>Why would "sound" alone not be enough?</>,
          a: <>A function that lists nothing is sound. Completeness is what says the list is all of the steps, and it needs the closure axiom of lesson 2.</> },
        { q: <>Why does the conclusion need the theory to have a model?</>,
          a: <>A theory without models entails every pattern, so sound and complete would hold for any function. The model condition rules that out.</> },
      ]}
    />
  )
}

// ---- 2. Why it matters, and what holds until then -----------------------------------------------------

export function GapScene() {
  const root = source('peanoRoot')
  const rows: { what: string; status: 'proved' | 'stated' | 'evidence' }[] = [
    { what: 'Lean step relation and executable step agree (step_iff)', status: 'proved' },
    { what: "peano's five properties and four witnesses, over Step", status: 'proved' },
    { what: "peano's Lean data is exactly kompile's KORE", status: 'proved' },
    { what: 'reordering KORE sentences keeps the models of Γ_D', status: 'proved' },
    { what: 'Theorem A: the step is sound and complete for Γ_D', status: 'stated' },
    { what: "peano's steps in matching logic (step_c₀, stuck_c₂, …)", status: 'stated' },
    { what: 'the step agrees with krust and the reference backend on every configuration tested', status: 'evidence' },
    { what: 'two kompiles give the same step for two definitions', status: 'evidence' },
  ]
  const focus: (string | null)[] = [null, 'proved', 'stated', 'stated', 'evidence', null]
  const steps: Step[] = [
    { say: <>Without Theorem A, the proofs of lesson 5 are proofs about the Lean <code>Step</code>. That <code>Step</code> is K's meaning rests on reading it.</>, panes: [] },
    { say: <>What the kernel has checked: the Lean side is consistent with itself, the properties hold of it, and the data is kompile's KORE.</>, panes: [] },
    { say: <>What is stated and not proved: the link to matching logic, in general and for peano's three configurations.</>, panes: ['p'] },
    { say: <>The peano statements are the small cases a proof of Theorem A would have to cover first. All are <code>sorry</code>.</>, hl: { p: span(root, 'theorem step_c₀', 'theorem stuck_c₂_needs_closure') }, panes: ['p'] },
    { say: <>Until then, two kinds of evidence: the step compared with two K backends (lesson 6), and the reference kompile producing the same step on two definitions.</>, panes: [] },
    { say: <>None of the per-definition statements depends on Theorem A. When it is proved, they become statements about K's meaning without being changed.</>, panes: [] },
  ]
  return (
    <LessonScene
      title="What is proved, what is stated, what is evidence"
      panes={[{ id: 'p', label: 'peano, in matching logic', source: root }]}
      steps={steps}
      visual={(at) => (
        <div className={styles.tableWrap}>
          <table className={styles.table}>
            <thead><tr><th scope="col">claim</th><th scope="col">status</th></tr></thead>
            <tbody>
              {rows.map((r) => {
                const on = focus[at] === null ? undefined : focus[at] === r.status
                return (
                  <tr key={r.what} className={on ? styles.on : on === false ? styles.off : ''}>
                    <td>{r.what}</td>
                    <td>{r.status === 'proved' ? 'kernel-checked' : r.status === 'stated' ? 'stated, sorry' : 'evidence, not proof'}</td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </div>
      )}
      questions={[
        { q: 'If Theorem A turned out false, what would happen to the proofs of lesson 5?',
          a: <>They would still be proofs about <code>Step</code>, but <code>Step</code> would differ from K's meaning somewhere, and a difference found that way would show where. Either <code>Step</code> or the translation would be fixed, and the proofs rechecked.</> },
        { q: 'Why state the peano examples at all, if they are unproved?',
          a: <>They make the gap concrete: three configurations, each with a claim in matching logic that Theorem A implies. A proof of Theorem A that does not cover them is not one.</> },
      ]}
    />
  )
}
