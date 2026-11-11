'use client'

// Core lesson 10: the statements. `Sound`: the theory with the step's closure has a model, and
// every step is entailed. `Complete`: every successor the theory forces is one a step function
// listing `Step`'s successors lists. The theorems `sound` and `complete`, and what a reader trusts
// once lessons 1 to 10 are understood. Every Lean pane is kcore-spec's text at the manifest's commit.

import { type Source, coreCommit, coreFile, lineOf, slice, span, textSource } from '../data'
import { type Lesson, note } from '../lesson'
import { Board } from '../viz'

const soundLean = coreFile('KcoreSpec/Sound.lean')
const sound = slice(soundLean, '/-- **Soundness**: the theory', '∀ x y : Config d.sem, Step d.sem x y →')
const complete = slice(soundLean, '/-- **Completeness**, for a step function', "(Γ d.sem ∪ Γstep d.sem) ⊧ (den d.sem x.val ⇒ KoreAML.allNext")
const theorems = slice(soundLean, '/-- **Soundness of a well-formed definition**', 'fun href x => step_complete')
const stmts = coreFile('KcoreSpec/Statements.lean')
const stepIsDef = slice(stmts, '/-- The step relation\'s successors, as a step function', '∀ (x : Config c) (y : GroundTerm), y ∈ ref x.val ↔')
const peanoSound = slice(coreFile('examples/peano/Peano/Sound.lean'), 'theorem sound : Sound defn', 'theorem sound : Sound defn')

const workedSound = textSource('worked by hand', [
  "-- the prologue's first step is a Step (lesson 6), so Sound gives",
  'Γ ⊧ ⟦run(s(s(z)))⟧ ⇒ •⟦run(s(z))⟧          -- cells left out',
].join('\n'))
const workedComplete = textSource('worked by hand', [
  '-- ref lists no successor of done(z) (lesson 6), so Complete gives',
  'Γ ∪ Γstep ⊧ ⟦done(z)⟧ ⇒ ◦⊥                 -- no model gives it one',
  '',
  '-- and one, run(s(z)), for run(s(s(z)))',
  'Γ ∪ Γstep ⊧ ⟦run(s(s(z)))⟧ ⇒ ◦⟦run(s(z))⟧',
].join('\n'))

const trusted = [
  {
    title: 'Trusted',
    items: [
      { key: 'kernel', text: <>Lean's kernel and its three standard axioms</> },
      { key: 'defs', text: <>the definitions of lessons 1 to 10: reading this course is reviewing them</> },
      { key: 'hooks', text: <>the Bool and Int operations, as defined in Lean</> },
      { key: 'reader', text: <>the reader of a KORE file, for a definition read without the tie</> },
      { key: 'kompile', text: <>kompile's translation from K to KORE</> },
    ],
  },
  {
    title: 'Checked by the kernel',
    items: [
      { key: 'proofs', text: <>every proof, <code>sound</code> and <code>complete</code> among them</> },
      { key: 'gen', text: <>the generator's packages, the checks that decide well-formedness, the executable evaluator</> },
      { key: 'krust', text: <>k-rust, where its runs are checked against the definitions</> },
    ],
  },
]

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

export const statements10: Lesson = {
  id: 'sound-and-complete',
  number: 10,
  title: 'Sound and Complete',
  against: coreCommit,
  scenes: [
    {
      id: 'z1',
      title: 'Sound',
      panes: [
        { id: 's', label: 'KcoreSpec/Sound.lean', source: sound, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedSound, lang: 'lean' },
      ],
      frames: [
        {
          hl: { s: [at(sound, 'def Sound (d : Definition)')] },
          notes: [note('s', at(sound, 'def Sound (d : Definition)'), 'Stated of a `Definition`, but it reads only `d.sem`, the semantics of lessons 2 to 6.', 'd : Definition')],
          say: 'Two questions were left open in the prologue: what a step is, and why a proof about the definition is a proof about what it means. Lessons 1 to 9 built both sides. These two statements connect them.',
        },
        {
          hl: { s: [at(sound, '(∃ (M : Type)')] },
          notes: [note('s', at(sound, '(∃ (M : Type)'), 'The theory, with the step\'s closure, has a model, so it is consistent.', 'I ⊧ᴵP (Γ d.sem ∪ Γstep d.sem)')],
        },
        {
          hl: { s: [at(sound, '∀ x y : Config d.sem, Step d.sem x y →')], w: span(workedSound, '-- the prologue', 'Γ ⊧') },
          notes: [note('s', at(sound, '∀ x y : Config d.sem, Step d.sem x y →'), 'Every step is a theorem of Γ: in every model, `x` has `y` as a successor.', 'Step d.sem x y')],
        },
      ],
    },
    {
      id: 'z2',
      title: 'Complete',
      panes: [
        { id: 'r', label: 'KcoreSpec/Statements.lean', source: stepIsDef, lang: 'lean' },
        { id: 'c', label: 'KcoreSpec/Sound.lean', source: complete, lang: 'lean' },
      ],
      frames: [
        {
          hl: { r: span(stepIsDef, 'def StepIs', '∀ (x : Config c) (y : GroundTerm), y ∈ ref x.val ↔') },
          notes: [note('r', at(stepIsDef, '∀ (x : Config c) (y : GroundTerm), y ∈ ref x.val ↔'), 'A step function `ref` (a `StepFn`: from a ground term to a list of them) lists exactly the successors `Step` gives.', 'y ∈ ref x.val ↔')],
        },
        {
          hl: { c: [at(complete, 'def Complete'), at(complete, 'StepIs d.sem ref →'), at(complete, "(Γ d.sem ∪ Γstep d.sem) ⊧")] },
          notes: [note('c', at(complete, "(Γ d.sem ∪ Γstep d.sem) ⊧"), 'With the step\'s closure, every successor of `x` is one `ref` lists: the theory forces no step `Step` lacks.', 'KoreAML.allNext')],
        },
      ],
    },
    {
      id: 'z3',
      title: 'On peano',
      panes: [
        { id: 'c', label: 'KcoreSpec/Sound.lean', source: complete, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedComplete, lang: 'lean' },
      ],
      frames: [
        {
          hl: { w: span(workedComplete, '-- ref lists no successor', 'Γ ∪ Γstep ⊧ ⟦done(z)⟧') },
          notes: [note('w', at(workedComplete, 'Γ ∪ Γstep ⊧ ⟦done(z)⟧'), "The prologue's stuck configuration, as a theorem about every model.", '◦⊥')],
        },
        {
          hl: { w: span(workedComplete, '-- and one, run(s(z))', 'Γ ∪ Γstep ⊧ ⟦run(s(s(z)))⟧') },
          say: 'With `Sound`, the prologue\'s run is exactly what the theory says: these steps, and no others.',
        },
      ],
    },
    {
      id: 'z4',
      title: 'The theorems',
      panes: [
        { id: 't', label: 'KcoreSpec/Sound.lean', source: theorems, lang: 'lean' },
        { id: 'p', label: 'Peano/Sound.lean', source: peanoSound, lang: 'lean' },
      ],
      frames: [
        {
          hl: { t: [at(theorems, 'theorem sound (d : Definition)'), at(theorems, 'theorem complete (d : Definition)')] },
          notes: [note('t', at(theorems, 'theorem sound (d : Definition)'), 'Proved, for every definition: the kernel checks the proof.', 'Sound d')],
        },
        {
          hl: { t: [at(theorems, 'theorem sound (d : Definition)')] },
          notes: [
            note('t', at(theorems, 'theorem sound (d : Definition)'), 'Not settled: well-formedness. It reads more than the semantics the theorems speak about, and its conditions move with the reader of kompile\'s KORE.', 'hwf : wf d = true'),
            note('t', at(theorems, 'theorem sound (d : Definition)'), 'The obligations of lesson 7.', 'hob : Obligations d'),
          ],
        },
        {
          hl: { p: [at(peanoSound, 'theorem sound : Sound defn')] },
          notes: [note('p', at(peanoSound, 'theorem sound : Sound defn'), 'For peano, with no hypothesis left.', 'Sound defn')],
        },
      ],
    },
    {
      id: 'z5',
      title: 'What you trust',
      visual: (n) => <Board columns={trusted} cols={2} big lit={[[], ['Trusted'], ['Checked by the kernel']][n]} />,
      frames: [
        { say: 'Once you have read lessons 1 to 10, here is what you trust and what you do not need to.' },
        { say: 'Trusted: the kernel, the definitions you just reviewed, the builtin operations, the reader where the tie is off, and kompile.' },
        { say: 'Checked against those definitions by the kernel: everything else. The open questions are on the [State of the core](/lean/state-of-the-core) page.' },
      ],
    },
  ],
  quiz: [
    {
      q: 'What does `Sound` add to "every step is entailed by Γ"?',
      options: ['That Γ with the step\'s closure has a model, so the entailments are not vacuous', 'That every configuration has a step', 'That the steps terminate'],
      answer: 0,
      why: 'An inconsistent theory entails everything; a model rules that out.',
    },
    {
      q: 'What does `Complete` say about `done(z)` in peano?',
      options: ['Every model gives it no successor', 'Some model gives it a successor', 'Nothing: it is not reachable'],
      answer: 0,
      why: 'The step function lists none, so `⟦done(z)⟧ ⇒ ◦⊥` is entailed.',
    },
  ],
  checked: [
    `Every Lean pane is kcore-spec's text at \`${coreCommit}\`.`,
    '`sound` and `complete` are proved; Lean\'s kernel checks the proofs. The theorems about peano are worked by hand from them.',
  ],
}
