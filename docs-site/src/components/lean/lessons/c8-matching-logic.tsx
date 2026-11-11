'use client'

// Core lesson 8: matching logic, as much as `Sound` and `Complete` use. Patterns denote sets of
// elements of a model; an interpretation; when a pattern holds; `Γ ⊧ φ` over all models; `•` (some
// next) and its dual `◦` (all next); and definedness, which lesson 9's theory uses. Every pane is
// the text of aml-port or kcore-spec at the manifest's commit.

import { type Source, coreCommit, coreFile, lineOf, slice, span, textSource } from '../data'
import { type Lesson, note } from '../lesson'

const pattern = slice(coreFile('../aml-port/MatchingLogic/Pattern.lean'), 'inductive Pattern (𝕊 : Type) where', 'deriving DecidableEq, Inhabited, Repr')
const derived = slice(coreFile('../aml-port/MatchingLogic/Pattern.lean'), '  /-- Negation of a pattern. -/', '  @[match_pattern] def universal')
const sem = coreFile('../aml-port/MatchingLogic/Semantics.lean')
const interp = slice(sem, 'structure Interpretation (𝕊 : Type) (M : Type) where', "| ⊥ => fun _ => False")
const entails = slice(sem, 'def Valuation.satifies', '  ∀ {M : Type} [Inhabited M] {I : Interpretation 𝕊 M}, I ⊧ᴵP Γ → I ⊧ᴵ φ')
const defined = slice(coreFile('../aml-port/MatchingLogic/Definedness.lean'), 'notation "⌈" φ "⌉"', 'infix:50 " ∈∈ " => member')
const sig = coreFile('KcoreSpec/Kore/Signature.lean')
const next = slice(sig, '/-- `•φ`: one-path next', 'def sNext (φ : P) : P := sym .next ⬝ φ')
const allNext = slice(coreFile('KcoreSpec/Kore/Gamma.lean'), '/-- `◦φ ≡ ¬•¬φ`, all-path next', 'def allNext (φ : P) : P := ∼(sNext (∼φ))')

const workedNext = textSource('worked by hand', [
  "-- the prologue's first step, as a pattern (cells left out)",
  '⟦run(s(s(z)))⟧ ⇒ •⟦run(s(z))⟧',
  '-- every element run(s(s(z))) denotes has one that run(s(z)) denotes as a successor',
  '',
  '-- done(z) has no successor',
  '⟦done(z)⟧ ⇒ ◦⊥',
].join('\n'))

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

export const matchingLogic8: Lesson = {
  id: 'matching-logic',
  number: 8,
  title: 'Matching logic',
  against: coreCommit,
  scenes: [
    {
      id: 'l1',
      title: 'Patterns',
      panes: [
        { id: 'p', label: 'MatchingLogic/Pattern.lean', source: pattern, lang: 'lean' },
        { id: 'd', label: 'MatchingLogic/Pattern.lean', source: derived, lang: 'lean' },
      ],
      frames: [
        {
          hl: { p: [at(pattern, 'inductive Pattern')] },
          say: "Lessons 1 to 7 said what a step is, in Lean. The theorems compare it with a theory in matching logic, a logic whose formulas, patterns, are built from symbols of the definition. This lesson is the part of matching logic they use.",
        },
        {
          hl: { p: [at(pattern, '| evar'), at(pattern, 'symbol : 𝕊'), at(pattern, 'application : Pattern'), at(pattern, 'implication : Pattern'), at(pattern, '| existential'), at(pattern, 'bottom : Pattern')] },
          notes: [
            note('p', at(pattern, 'symbol : 𝕊'), 'A symbol of the signature.', 'symbol'),
            note('p', at(pattern, 'application : Pattern'), 'One pattern applied to another.', 'application'),
            note('p', at(pattern, 'implication : Pattern'), 'Implication, false, and "there exists" build all of logic.', 'implication'),
          ],
        },
        {
          hl: { d: span(derived, '@[match_pattern] def negation', '@[match_pattern] def universal') },
          notes: [note('d', at(derived, '@[match_pattern] def negation'), 'Not, or, and, true, iff and "for all" are abbreviations.', 'negation')],
        },
      ],
    },
    {
      id: 'l2',
      title: 'A pattern denotes a set',
      panes: [{ id: 'i', label: 'MatchingLogic/Semantics.lean', source: interp, lang: 'lean' }],
      frames: [
        {
          hl: { i: span(interp, 'structure Interpretation', 'evalApp : M → M → Set M') },
          notes: [note('i', at(interp, 'evalSymb : 𝕊 → Set M'), 'A model: a set `M` of elements, a set for each symbol, and what applying one element to another gives.', 'Set M')],
        },
        {
          hl: { i: [at(interp, 'def Pattern.interpret'), at(interp, '| symbol σ =>'), at(interp, '| p₁ ⬝ p₂ =>')] },
          notes: [note('i', at(interp, 'def Pattern.interpret'), 'A pattern denotes a set of elements, not true or false.', 'Set M'), note('i', at(interp, '| p₁ ⬝ p₂ =>'), 'An application denotes what applying its parts\' elements gives.', 'I.evalApp a b m')],
        },
        {
          hl: { i: [at(interp, '| φ ⇒ ψ =>'), at(interp, '| ∃∃ x φ =>'), at(interp, '| ⊥ =>')] },
          notes: [note('i', at(interp, '| φ ⇒ ψ =>'), 'An element is in `φ ⇒ ψ` if, when it is in `φ`, it is in `ψ`.', '→')],
        },
      ],
    },
    {
      id: 'l3',
      title: 'Γ ⊧ φ',
      panes: [{ id: 'e', label: 'MatchingLogic/Semantics.lean', source: entails, lang: 'lean' }],
      frames: [
        {
          hl: { e: span(entails, 'def Valuation.satifies', 'fun φ => ∀ m : M, φ.interpret I eval m') },
          notes: [note('e', at(entails, 'fun φ => ∀ m : M, φ.interpret I eval m'), 'A pattern holds when it denotes every element.', '∀ m : M')],
        },
        {
          hl: { e: span(entails, 'def Interpretation.satisfiesAll', 'fun Γ => ∀ γ ∈ Γ, I ⊧ᴵ γ') },
          notes: [note('e', at(entails, 'fun Γ => ∀ γ ∈ Γ, I ⊧ᴵ γ'), 'A model of a theory Γ: every pattern of Γ holds, for every value of the variables.', 'I ⊧ᴵ γ')],
        },
        {
          hl: { e: span(entails, 'def entails', 'I ⊧ᴵP Γ → I ⊧ᴵ φ') },
          notes: [note('e', at(entails, 'I ⊧ᴵP Γ → I ⊧ᴵ φ'), '`Γ ⊧ φ`: φ holds in every model of Γ.', 'I ⊧ᴵP Γ → I ⊧ᴵ φ')],
          say: 'This is the entailment the theorems use: truth in every model, not a proof in a proof system. (aml-port also has a proof system, which the statements do not use.)',
        },
      ],
    },
    {
      id: 'l4',
      title: 'Definedness',
      panes: [{ id: 'd', label: 'MatchingLogic/Definedness.lean', source: defined, lang: 'lean' }],
      frames: [
        {
          hl: { d: [at(defined, 'notation "⌈" φ "⌉"')] },
          notes: [note('d', at(defined, 'notation "⌈" φ "⌉"'), '`⌈φ⌉`: φ is defined, it denotes some element.', '⌈')],
        },
        {
          hl: { d: [at(defined, 'def equal'), at(defined, 'def member')] },
          notes: [note('d', at(defined, 'def equal'), 'Equality, and membership, from definedness.', 'equal')],
          say: 'Lesson 9 uses these to state when a function has a value.',
        },
      ],
    },
    {
      id: 'l5',
      title: 'Next',
      panes: [
        { id: 'n', label: 'KcoreSpec/Kore/Signature.lean', source: next, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedNext, lang: 'lean' },
      ],
      frames: [
        {
          hl: { n: [at(next, 'def sNext')], w: span(workedNext, '⟦run(s(s(z)))⟧', '-- every element') },
          notes: [note('n', at(next, 'def sNext'), '`•φ`: the elements with some successor in φ.', 'sym .next ⬝ φ')],
          say: "K's matching logic has a symbol `•`, next. A rewrite from `x` to `y` is the pattern `⟦x⟧ ⇒ •⟦y⟧`.",
        },
      ],
    },
    {
      id: 'l6',
      title: 'All next',
      panes: [
        { id: 'a', label: 'KcoreSpec/Kore/Gamma.lean', source: allNext, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedNext, lang: 'lean' },
      ],
      frames: [
        {
          hl: { a: [at(allNext, 'def allNext')], w: span(workedNext, '-- done(z) has no successor', '⟦done(z)⟧ ⇒ ◦⊥') },
          notes: [note('a', at(allNext, 'def allNext'), '`◦φ`: every successor is in φ. `◦⊥`: there is none.', '∼(sNext (∼φ))')],
          say: '`Sound` uses `•`: each step is one the theory allows. `Complete` uses `◦`: the theory allows no other.',
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'What does `Γ ⊧ φ` mean here?',
      options: ['φ holds in every model of Γ', 'φ has a proof from Γ in a proof system', 'φ is one of the patterns of Γ'],
      answer: 0,
      why: 'Entailment is defined by models, as `entails` says.',
    },
    {
      q: 'What does `⟦x⟧ ⇒ ◦⊥` say?',
      options: ['`x` has no successor', '`x` has some successor', '`x` is undefined'],
      answer: 0,
      why: '`◦φ` says every successor is in φ; with φ = ⊥, there can be none.',
    },
  ],
  checked: [
    `Every pane is the text of aml-port or kcore-spec at \`${coreCommit}\`.`,
    'The patterns of the prologue\'s run are written by hand; lesson 9 says how a configuration becomes a pattern.',
  ],
}
