'use client'

// Lesson 8: the statement that ties the Lean step of lessons 4 and 5 to the matching-logic meaning
// of lesson 2, its parts, its status, the evidence that stands in for it until it is proved, and
// what the second fragment changes. Panes are Statements.lean and PeanoSpec.lean at the recorded commit.

import { lineOf, source, span } from '../data'
import { type Lesson, note } from '../lesson'
import { diffNumbers, f1Numbers, numbers } from '../numbers'
import { Board, Pill, Rows } from '../viz'
import { subs } from '../sub'

const conclusion = source('conclusion')
const stepStmts = source('stepStatements')
const models = source('models')
const soundComplete = source('soundAndComplete')
const soundCompleteKore = source('soundAndCompleteKore')
const den = source('den')
const root = source('peanoRoot')

const statusRows: { what: string; status: 'proved' | 'stated' | 'evidence' }[] = [
  { what: 'Lean step relation and executable step agree (step_iff)', status: 'proved' },
  { what: "peano's five properties and four witnesses, over Step", status: 'proved' },
  { what: "peano's Lean data is exactly kompile's KORE", status: 'proved' },
  { what: 'reordering KORE sentences keeps the models of Γ_D', status: 'proved' },
  { what: 'subject reduction: a step of a well-formed definition gives a configuration (F₀ and F₁)', status: 'proved' },
  { what: "F₁'s executable step equals its Step (step_iff), and F₁'s step is F₀'s on F₀ definitions (step_ofF0)", status: 'proved' },
  { what: 'the step is sound and complete for Γ_D (F₀, and F₁)', status: 'stated' },
  { what: "peano's steps in matching logic (step_c₀, stuck_c₂, …)", status: 'stated' },
  { what: 'the step agrees with krust and the reference backend on every configuration tested (F₀ and F₁)', status: 'evidence' },
  { what: 'two kompiles give the same step for two definitions', status: 'evidence' },
]
const focus: (string | null)[] = [null, 'proved', 'stated', 'stated', 'evidence', null]

const statusTable = (at: number) => (
  <Rows
    head={['claim', 'status']}
    rows={statusRows.map((r) => ({
      key: r.what,
      state: focus[at] === null ? undefined : focus[at] === r.status ? 'cur' : 'faded',
      cells: [
        <span key="w" style={{ fontFamily: 'var(--f-sans)' }}>{subs(r.what)}</span>,
        r.status === 'proved' ? <Pill key="p" tone="ok">kernel-checked</Pill> : r.status === 'stated' ? <Pill key="p" tone="gold">stated, sorry</Pill> : <Pill key="p" tone="alt">evidence, not proof</Pill>,
      ],
    }))}
  />
)

const nextFragment = (at: number) => (
  <Board
    big
    cols={2}
    lit={[['F₁ adds'], ['theory'], ['audit'], ['models'], []][at]}
    columns={[
      {
        title: 'F₁ adds',
        items: [
          { key: 'cells', text: 'several configuration cells' },
          { key: 'bool', text: 'Bool and Int' },
          { key: 'req', text: <><code>requires</code> clauses</> },
          { key: 'maps', text: 'maps' },
        ],
      },
      {
        title: 'What changes in the statement',
        items: [
          { key: 'theory', text: <>Γ<sub>D</sub> gains the theory of the builtin operations</> },
          { key: 'audit', text: <>the fixed text depends on what a definition imports, and its axioms enter Γ<sub>D</sub></> },
          { key: 'models', text: <><code>ModelsStandard</code> compares values rather than term shapes</> },
        ],
      },
    ]}
  />
)

export const lesson8: Lesson = {
  id: 'sound-and-complete',
  number: 8,
  title: 'Step is sound and complete',
  scenes: [
    {
      id: 't1',
      title: 'Sound and complete',
      panes: [
        { id: 'c', label: 'The conclusion', source: conclusion },
        { id: 's', label: 'Sound and complete', source: stepStmts },
      ],
      frames: [
        { say: "The series has given two answers to \"what is a step\". Lesson 2's: what the theory Γ_D entails, in every model. Lesson 4's: the Lean relation `Step`, which the proofs use. The theorem that `Step` is ==sound and complete== says they agree. It's what turns \"proved about `Step`\" into \"proved about the K definition\"." },
        { hl: { c: span(conclusion, 'structure Conclusion', 'complete : StepComplete c p ref') }, notes: [note('c', lineOf(conclusion, 'structure Conclusion'), "About a step function: for each configuration, a finite list of successors. The package's executable step is one, read through the encoding of terms as KORE.")] },
        { hl: { s: span(stepStmts, 'def StepSound', "∀ t, GroundConfig c t → ∀ t' ∈ f t, ΓD c p ⊧") }, notes: [note('s', lineOf(stepStmts, 'def StepSound'), "For every successor the function lists, Γ_D entails \"this configuration implies `•` that successor\". Every listed step is a step in every model.")], say: "==Sound==." },
        {
          hl: { s: span(stepStmts, 'def StepComplete', '∀ t, GroundConfig c t → (ΓD c p ∪ Γclosure c p) ⊧') },
          notes: [note('s', lineOf(stepStmts, 'def StepComplete'), "With the closure axiom, Γ_D entails \"this configuration implies `◦` of the listed successors\". No model has another step, and an empty list means stuck.")], say: "==Complete==.",
          ask: {
            q: "Why would \"sound\" alone not be enough?",
            options: ["It would, for peano", "A function that lists nothing is sound", "Sound is harder to prove"],
            answer: 1,
            why: "Completeness is what says the list is all of the steps, and it needs the closure axiom of lesson 2.",
          },
        },
      ],
    },
    {
      id: 't2',
      title: 'Keeping it from being empty',
      panes: [
        { id: 'm', label: 'Not an empty theory', source: models },
        { id: 'd', label: 'Configurations as patterns', source: den },
      ],
      frames: [
        {
          hl: { m: span(models, 'def StdModelOK', "groundSort c t = groundSort c t'") },
          notes: [note('m', lineOf(models, 'def StdModelOK'), "The theory has a model, so it doesn't entail everything."), note('m', lineOf(models, 'def ModelsStandard'), "In every model, distinct ground terms denote distinct elements, so a model where everything is one element is excluded.", 'def ModelsStandard')], say: "Two conditions keep this from being empty.",
          ask: {
            q: "Why does the conclusion need the theory to have a model?",
            options: ["Lean requires an instance", "A theory without models entails every pattern, so sound and complete would hold for any function", "To run tests against it"],
            answer: 1,
            why: "The model condition rules that out.",
          },
        },
        { hl: { d: [lineOf(den, 'def den')] }, notes: [note('d', lineOf(den, 'def den'), "The translation of a ground KORE term into a pattern: the same translation that turns the KORE axioms into Γ_D.", 'def den')], say: "Configurations enter the theory through `den`." },
      ],
    },
    {
      id: 't3',
      title: 'The theorem, and its sorry',
      panes: [
        { id: 't', label: 'The theorem', source: soundComplete },
        { id: 'k', label: 'For a KORE text', source: soundCompleteKore },
      ],
      frames: [
        { hl: { t: [lineOf(soundComplete, 'theorem sound_and_complete')] }, notes: [note('t', lineOf(soundComplete, 'theorem sound_and_complete'), "The conclusion, for every well-formed definition and the package's step."), note('t', lineOf(soundComplete, 'theorem sound_and_complete'), "Its proof.", 'sorry')] },
        { hl: { k: span(soundCompleteKore, 'theorem sound_and_complete_kore', 'exact ⟨d, hwf, he, sound_and_complete d hwf⟩') }, notes: [note('k', lineOf(soundCompleteKore, 'theorem sound_and_complete_kore'), "For a text in F₀, the conclusion holds. Proved from `sound_and_complete` and `F0.sound`, so it inherits the `sorry`.")], say: "The form a reader of a KORE file wants." },
      ],
    },
    {
      id: 't4',
      title: 'What is proved, stated, and evidence',
      visual: statusTable,
      panes: [{ id: 'p', label: 'peano, in matching logic', source: root }],
      arrange: 'side',
      frames: [
        { say: "Until soundness and completeness are proved, the proofs of lesson 5 are proofs about the Lean `Step`. That `Step` is K's meaning rests on reading it." },
        { say: "What the kernel has checked: the Lean side is consistent with itself, the properties hold of it, and the data is kompile's KORE." },
        { say: "What's stated and not proved: the link to matching logic, in general and for peano's three configurations." },
        {
          hl: { p: span(root, 'theorem step_c₀', 'theorem stuck_c₂_needs_closure') },
          say: "The peano statements are the small cases a proof of soundness and completeness would have to cover first. All are `sorry`.",
          ask: {
            q: "Why state the peano examples at all, if they are unproved?",
            options: ["To pad the file", "They make the gap concrete: three configurations, each with a claim soundness and completeness imply", "Lean needs them to type-check"],
            answer: 1,
            why: "A proof of soundness and completeness that does not cover them is not one.",
          },
        },
        { say: "Until then, evidence: the package's step and krust's agree on " + diffNumbers.configs + " configurations (" + diffNumbers.differences + " differences), a sample of " + diffNumbers.refSampled + " agrees with the reference backend, the reference kompile and krust's give the same step for peano and for `examples/rewrite.k`, and there's the review of the " + numbers.total + " lines of lesson 6. The same differential on the builtin fragment (F₁, lesson 9) compared " + f1Numbers.configs + " configurations of " + f1Numbers.subjects + " definitions, with " + f1Numbers.differences + " differences, and " + f1Numbers.refAgree + " of " + f1Numbers.refSampled + " sampled configurations agree with the reference backend. Each is evidence that `Step` is K's meaning on what was tried. None is a proof for every configuration." },
        { say: "No part of the proof of soundness and completeness is written yet. It's on a separate track: nothing a user proves about `Step` waits for it. When it is proved, the per-definition statements become statements about K's meaning ==without being changed==." },
      ],
    },
    {
      id: 't5',
      title: 'Sound and complete for the builtin fragment',
      visual: nextFragment,
      frames: [
        { say: "The builtin fragment of lesson 9, F₁, sits beside the constructor fragment, F₀, in the package, and `step_ofF0` (proved) says its step is F₀'s on F₀ definitions. It states its own soundness and completeness, of the same form. Its proof is `sorry` too." },
        { say: "The KORE text doesn't carry the theory of the builtin operations: kompile writes no commutativity axiom for maps, and nothing about when two maps can be joined. So F₁'s Γ_D adds, read off the one table of operations F₁ evaluates (`Hooks.lean`): each operation's value on values, distinct values denoting distinct elements, and every map built from the empty map, single entries and joins." },
        { say: "The " + f1Numbers.auditTotal + " axioms that BOOL and INT add (" + f1Numbers.auditBool + " and " + f1Numbers.auditInt + ") were checked one by one against the intended model: " + (f1Numbers.auditFalse === 0 && f1Numbers.auditCurated === 0 ? "none is false, and none had to be removed" : f1Numbers.auditFalse + " false, " + f1Numbers.auditCurated + " removed") + ". A false one would have left the theory without a model, and soundness and completeness vacuous." },
        { say: "`ModelsStandard` compares values, since literals and maps are now values." },
        { say: "Before F₁'s soundness and completeness can be proved, the per-feature parts of its proof (the operations' theory, maps, `requires`) have to be proved over the matching-logic semantics. ==None is written yet.==" },
      ],
    },
  ],
  quiz: [
    {
      q: "If soundness and completeness turned out false, what would happen to the proofs of lesson 5?",
      options: ["They'd become unsound and be discarded", "They'd still be proofs about `Step`, but `Step` would differ from K's meaning somewhere, and the difference would show where", "Nothing at all would change"],
      answer: 1,
      why: "Either `Step` or the translation would be fixed, and the proofs rechecked.",
    },
    {
      q: "Does any per-definition statement depend on soundness and completeness?",
      options: ["Yes, all of them", "No", "Only determinism"],
      answer: 1,
      why: "When it is proved, they become statements about K's meaning without being changed.",
    },
  ],
  checked: [
    "The panes are `Statements.lean` and `PeanoSpec.lean` at the recorded commit. `sound_and_complete`, `sound_and_complete_kore` and the peano statements in matching logic type-check. Each depends on `sorry`, and the build's axiom check says so for `sound_and_complete_kore`.",
    "The evidence figures are those of lesson 6.",
    "The part on the builtin fragment restates F₁'s `Statements.lean` and the audit of its fixed texts at the recorded commit. The audit is a reading, recorded in the package, not a Lean proof.",
  ],
  tryit: [
    { say: "In the kcore-spec package directory:", cmd: "lake build\nlake env lean KcoreSpec/SpecChecks.lean   # prints nothing; the pinned axiom list of sound_and_complete_kore includes sorryAx" },
  ],
}
