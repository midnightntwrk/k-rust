'use client'

// Core lesson 10: the statements. `Sound`: the theory with the step's closure has a model, and
// every step is entailed. `Complete`: every successor the theory forces is one a step function
// listing `Step`'s successors lists. The theorems `sound` and `complete`, and what a reader trusts
// once lessons 1 to 11 are understood; and, for a definition with uninterpreted operations, the statement a
// generated package makes for every interpretation of them, on kryp's. Every Lean pane is kcore-spec's text at the manifest's commit.

import { checked, checkedLabel, coreCommit, coreFile, lineOf, slice, type Source, span } from '../data'
import { type Lesson, note } from '../lesson'
import { Board } from '../viz'

const soundLean = coreFile('KcoreSpec/Sound.lean')
const sound = slice(soundLean, '/-- **Soundness** of a semantics `c`', '∀ x y : Config c, Step c x y →')
const complete = slice(soundLean, '/-- **Completeness** of a semantics `c`', '(Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext')
const theorems = slice(soundLean, '/-- **Soundness of a semantics** that `coreOK`', 'fun href x => step_complete (hypModel_of_fnHyp')
const stmts = coreFile('KcoreSpec/Statements.lean')
const stepIsDef = slice(stmts, '/-- The step relation\'s successors, as a step function', '∀ (x : Config c) (y : GroundTerm), y ∈ ref x.val ↔')
const withHooks = slice(coreFile('KcoreSpec/Core.lean'), '/-- The same definition with its parameter symbols interpreted by H. -/', 'def Semantics.withHooks')
const genHooks = slice(coreFile('examples/kryp/Kryp/FnHyp.lean'), '/-- **The interpretations the statements are about**', 'theorem sound_defn (H : HookParams)')
const peanoSound = slice(coreFile('examples/peano/Peano/Sound.lean'), 'theorem coreOK_defn', 'KCore.complete_hyp defn.sem ref coreOK_defn hf')

const workedSound = checked('sound')
const workedComplete = checked('complete')

const trusted = [
  {
    title: 'Trusted',
    items: [
      { key: 'kernel', text: <>Lean's kernel and its three standard axioms</> },
      { key: 'defs', text: <>the definitions of lessons 1 to 11: reading this course is reviewing them</> },
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
        { id: 'w', label: checkedLabel(workedSound), source: workedSound, lang: 'lean' },
      ],
      frames: [
        {
          hl: { s: [at(sound, 'def SoundC (c : Semantics)')] },
          notes: [note('s', at(sound, 'def SoundC (c : Semantics)'), 'Of a semantics, the value of lessons 2 to 6. Older text writes `Sound d`, which is `SoundC d.sem`.', 'c : Semantics')],
          say: 'Two questions were left open in the prologue: what a step is, and why a proof about the definition is a proof about what it means. Lessons 1 to 9 built both sides. These two statements connect them.',
        },
        {
          hl: { s: [at(sound, '(∃ (M : Type)')] },
          notes: [note('s', at(sound, '(∃ (M : Type)'), 'The theory, with the step\'s closure, has a model, so it is consistent.', 'I ⊧ᴵP (Γ c ∪ Γstep c)')],
        },
        {
          hl: { s: [at(sound, '∀ x y : Config c, Step c x y →')], w: span(workedSound, '-- runSSZ', 'sound_runSSZ') },
          notes: [note('s', at(sound, '∀ x y : Config c, Step c x y →'), 'Every step is a theorem of Γ: in every model, `x` has `y` as a successor.', 'Step c x y')],
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
          hl: { c: [at(complete, 'def CompleteC'), at(complete, 'StepIs c ref →'), at(complete, '(Γ c ∪ Γstep c) ⊧')] },
          notes: [note('c', at(complete, '(Γ c ∪ Γstep c) ⊧'), 'With the step\'s closure, every successor of `x` is one `ref` lists: the theory forces no step `Step` lacks.', 'KoreAML.allNext')],
        },
      ],
    },
    {
      id: 'z3',
      title: 'On peano',
      panes: [
        { id: 'c', label: 'KcoreSpec/Sound.lean', source: complete, lang: 'lean' },
        { id: 'w', label: checkedLabel(workedComplete), source: workedComplete, lang: 'lean' },
      ],
      frames: [
        {
          hl: { w: span(workedComplete, '-- doneZ', 'complete_doneZ\'') },
          notes: [note('w', at(workedComplete, 'KoreAML.allNext ⊥'), "The prologue's stuck configuration, as a theorem about every model.", 'allNext ⊥')],
          say: 'These are `complete_doneZ` and `complete_runSSZ`, whose empty and one-element disjunctions are read here as `⊥` and as their element.',
        },
        {
          hl: { w: span(workedComplete, '-- runSSZ', 'complete_runSSZ\'') },
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
          hl: { t: [at(theorems, 'theorem sound_hyp (c : Semantics)'), ...span(theorems, 'theorem complete_hyp (c : Semantics)', 'CompleteC c ref :=')] },
          notes: [note('t', at(theorems, 'theorem sound_hyp (c : Semantics)'), 'Proved, for every semantics: the kernel checks the proof.', 'SoundC c')],
        },
        {
          hl: { t: [at(theorems, 'theorem sound_hyp (c : Semantics)')] },
          notes: [
            note('t', at(theorems, 'theorem sound_hyp (c : Semantics)'), 'A check Lean decides: lesson 11.', 'h : c.coreOK = true'),
            note('t', at(theorems, 'theorem sound_hyp (c : Semantics)'), 'What its functions must do: lesson 7.', 'hf : FnHyp c'),
          ],
          say: 'Two hypotheses, and nothing else.',
        },
        {
          hl: { p: [at(peanoSound, 'theorem coreOK_defn'), at(peanoSound, 'theorem sound_hyp')] },
          notes: [note('p', at(peanoSound, 'theorem coreOK_defn'), 'Every package states that its semantics passes the check…', 'coreOK_defn'), note('p', at(peanoSound, 'theorem sound_hyp'), '…and the two theorems for it, with `FnHyp` left as their premise.', 'FnHyp defn.sem')],
        },
      ],
    },
    {
      id: 'z4b',
      title: 'Definitions with uninterpreted operations',
      panes: [
        { id: 'h', label: 'KcoreSpec/Core.lean', source: withHooks, lang: 'lean' },
        { id: 'g', label: 'kryp, Kryp/FnHyp.lean', source: genHooks, lang: 'lean' },
      ],
      frames: [
        {
          hl: { h: [at(withHooks, 'def Semantics.withHooks')] },
          notes: [note('h', at(withHooks, 'def Semantics.withHooks'), 'The same semantics, its parameters interpreted by H.', '{ c with hooks := H }')],
          say: 'Some operations, such as those on Bytes and String and hashing, have no interpretation in Lean: they are parameters. With no interpretation, a `[total]` function that calls one has no value, so `FnHyp` is false and the theorem says nothing. A definition with parameters means something only at an interpretation H.',
        },
        {
          hl: { g: [at(genHooks, 'abbrev HooksTotal (H : HookParams)')] },
          notes: [note('g', at(genHooks, 'abbrev HooksTotal (H : HookParams)'), 'H gives a value wherever the text declares the operation total. `ParamsTotal` is in `KcoreSpec/ParamsTotal.lean`, outside the core.', 'ParamsTotal')],
        },
        {
          hl: { g: [at(genHooks, 'theorem sound_defn (H : HookParams)')] },
          notes: [note('g', at(genHooks, 'theorem sound_defn (H : HookParams)'), 'The statement of this lesson, for the semantics at H.', 'SoundC (defn.sem.withHooks H)')],
          say: "kryp uses K's KRYPTO hashes, such as `Keccak256`, which Lean does not interpret. Its package states soundness for every such H, and `complete_defn` likewise. It is proved from `sound_hyp`, unchanged, applied to `c.withHooks H`; the kernel checks the proof.",
        },
        {
          hl: { g: [at(genHooks, 'abbrev Obl (H : HookParams)')] },
          notes: [note('g', at(genHooks, 'abbrev Obl (H : HookParams)'), 'The facts the checks could not confirm. kryp has none, so `sound_defn` takes no premise but H; a package that names facts takes `(hob : Obl H)` as well.', 'Obl')],
        },
      ],
    },
    {
      id: 'z5',
      title: 'What you trust',
      visual: (n) => <Board columns={trusted} cols={2} big lit={[[], ['Trusted'], ['Checked by the kernel']][n]} />,
      frames: [
        { say: 'Once you have read lessons 1 to 11, here is what you trust and what you do not need to.' },
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
    '`sound` and `complete` are proved; Lean\'s kernel checks the proofs. The instances for peano are theorems of its package, which the kernel checks too.',
  ],
}
