'use client'

// Core lesson 9: the theory Γ a definition denotes, built from the Lean value `Semantics`: the
// signature, the constructors (no confusion, no junk), the domains, the collections, the function
// equations in priority form with the closure axiom, and the rule axioms; the step's closure; and a
// configuration's denotation. Every pane is kcore-spec's text at the manifest's commit; the axioms
// shown for peano are simplified renderings of it, by hand.

import { type Source, coreCommit, coreFile, lineOf, slice, span, textSource } from '../data'
import { type Lesson, note } from '../lesson'

const faithful = coreFile('KcoreSpec/Faithful.lean')
const gamma = slice(faithful, '/-- **The theory of a semantics**', 'ΓSig c ∪ ΓCons c ∪ ΓDomains c ∪ ΓColls c ∪ ΓFns c ∪ ΓRules c')
const noJunk = slice(coreFile('KcoreSpec/Kore/Gamma.lean'), '/-- Cons-NoJunk:', 'pat := inhOf (sortP N) ≡ .mu X')
const domains = slice(faithful, '/-- **The domains.**', 'def ΓDomains (c : Semantics)')
const colls = slice(faithful, '/-- **The collections.**', '∃ k ∈ c.allColls, φ ∈ collAxioms c k')
const fns = slice(faithful, '/-- A clause\'s equation, `premise ∧ ¬ ⋁ lower', 'def ΓFns (c : Semantics)')
const rules = slice(faithful, '/-- A rule\'s axiom with its priority read:', 'def ruleItems')
const closure = slice(faithful, '/-- The step\'s closure axiom,', 'def Γstep (c : Semantics)')
const den = slice(coreFile('KcoreSpec/Statements.lean'), '/-- ⟦t⟧: the AML pattern of a ground value. -/', 'def den (c : Semantics)')

const workedCons = textSource('simplified, by hand', [
  "-- peano's Nat: its generators are z and s",
  'z ∈ ⟦Nat⟧                       -- Cons-Fun: z is an element of Nat',
  's(x) = s(y) → x = y            -- Cons-Inj',
  'z ≠ s(x)                       -- Cons-Dist',
  '⟦Nat⟧ ≡ μX. z ∨ s(X)            -- Cons-NoJunk: nothing but z, s(z), s(s(z)), …',
].join('\n'))

const workedPred = textSource('simplified, by hand', [
  '-- pred(s(N)) => N, priority 50: nothing of a smaller priority',
  'X ∈ s(N)                          → pred(X) = N',
  '',
  '-- pred(_) => z [owise], priority 200: the first clause negated',
  '¬(∃N. X ∈ s(N)) ∧ X ∈ ⟦Nat⟧       → pred(X) = z',
  '',
  '-- the closure: pred(X) holds nothing else',
  'y ∈ pred(X) → (∃N. X ∈ s(N) ∧ y ∈ N) ∨ (¬(∃N. X ∈ s(N)) ∧ y ∈ z)',
].join('\n'))

const workedRule = textSource('simplified, by hand', [
  '-- peano: rule <k> run(s(N)) => run(pred(s(N))) </k>, priority 50',
  '⟦lhs⟧ ∧ ⌈⟦rhs⟧⌉ → •⟦rhs⟧               -- no rule of a smaller priority',
  '',
  '-- prio: rule <k> go(X:B) => other(X) ... </k>, priority 50',
  '⟦lhs⟧ ∧ ¬(applies go(X:D)) ∧ ⌈⟦rhs⟧⌉ → •⟦rhs⟧',
].join('\n'))

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

export const theory9: Lesson = {
  id: 'theory',
  number: 9,
  title: 'The theory Γ',
  against: coreCommit,
  scenes: [
    {
      id: 'y1',
      title: 'Γ is built from the definition',
      panes: [{ id: 'g', label: 'KcoreSpec/Faithful.lean', source: gamma, lang: 'lean' }],
      frames: [
        {
          hl: { g: [at(gamma, 'def Γ (c : Semantics)'), at(gamma, 'ΓSig c ∪ ΓCons c')] },
          notes: [note('g', at(gamma, 'def Γ (c : Semantics)'), 'Six parts, each read from the `Semantics` value.', 'Semantics')],
          say: 'Lesson 8 said what a theory is. This is the theory of a definition: what it means, in matching logic. It is built from the Lean value, not read from the KORE text the prologue showed.',
        },
      ],
    },
    {
      id: 'y2',
      title: 'The constructors',
      panes: [
        { id: 'n', label: 'KcoreSpec/Kore/Gamma.lean', source: noJunk, lang: 'lean' },
        { id: 'w', label: 'Simplified, by hand', source: workedCons, lang: 'lean' },
      ],
      frames: [
        {
          hl: { w: span(workedCons, 'z ∈ ⟦Nat⟧', 'z ≠ s(x)') },
          notes: [note('w', at(workedCons, 'z ≠ s(x)'), 'Each constructor is a function, injective, and apart from the others: no confusion.', 'z ≠ s(x)')],
          say: 'Every sort built by constructors gets four kinds of axiom (ΓSig declares the sorts and symbols themselves).',
        },
        {
          hl: { n: span(noJunk, 'def noJunkItem', 'pat := inhOf (sortP N) ≡ .mu X'), w: [at(workedCons, '⟦Nat⟧ ≡ μX.')] },
          notes: [note('n', at(noJunk, 'pat := inhOf (sortP N) ≡ .mu X'), 'No junk: the sort holds exactly what its generators build, the least such set (μ, lesson 8).', '.mu X')],
        },
      ],
    },
    {
      id: 'y3',
      title: 'Domains and collections',
      panes: [
        { id: 'd', label: 'KcoreSpec/Faithful.lean', source: domains, lang: 'lean' },
        { id: 'c', label: 'KcoreSpec/Faithful.lean', source: colls, lang: 'lean' },
      ],
      frames: [
        {
          hl: { d: [at(domains, 'def ΓDomains')] },
          notes: [note('d', at(domains, 'def ΓDomains'), 'Not settled: hook domains.', 'ΓDomains')],
        },
        {
          hl: { c: span(colls, '/-- **The collections.**', 'def ΓColls') },
          notes: [note('c', at(colls, 'def ΓColls'), 'What the unit, element and concatenation of each collection are: a union of maps, a concatenation of lists; a set\'s element is not the empty set, is injective, and is a union only with its own member. These axioms are stated by the core, not read from the K text.', 'ΓColls')],
        },
      ],
    },
    {
      id: 'y4',
      title: 'The functions',
      panes: [
        { id: 'f', label: 'KcoreSpec/Faithful.lean', source: fns, lang: 'lean' },
        { id: 'w', label: 'Simplified, by hand', source: workedPred, lang: 'lean' },
      ],
      frames: [
        {
          hl: { f: span(fns, 'def prioEquation', 'else competingEquation'), w: span(workedPred, '-- pred(s(N))', 'X ∈ s(N)') },
          notes: [note('f', at(fns, 'def prioEquation'), 'One equation per clause, with the clauses of a smaller priority negated.', 'prioEquation')],
        },
        {
          hl: { w: span(workedPred, '-- pred(_) => z [owise]', '¬(∃N. X ∈ s(N))') },
          notes: [note('w', at(workedPred, '¬(∃N. X ∈ s(N)) ∧'), '`[owise]` is priority 200, so the clause of priority 50 is negated. kompile writes the same premise for it, as the prologue showed.', '¬')],
        },
        {
          hl: { f: [at(fns, 'def fnClosureItemK')], w: span(workedPred, '-- the closure', 'y ∈ pred(X)') },
          notes: [note('f', at(fns, 'def fnClosureItemK'), 'And a closure axiom: a call holds nothing but the right side of a clause whose premise holds, so it is ⊥ where no clause applies.', 'fnClosureItemK')],
          say: 'The closure is what makes "undefined" in lesson 5 mean ⊥ in every model.',
        },
      ],
    },
    {
      id: 'y5',
      title: 'The rules',
      panes: [
        { id: 'r', label: 'KcoreSpec/Faithful.lean', source: rules, lang: 'lean' },
        { id: 'w', label: 'Simplified, by hand', source: workedRule, lang: 'lean' },
      ],
      frames: [
        {
          hl: { r: [at(rules, 'def prioRuleK'), at(rules, 'let rhsDef')], w: span(workedRule, '-- peano:', '⟦lhs⟧ ∧ ⌈⟦rhs⟧⌉') },
          notes: [note('r', at(rules, 'let rhsDef'), 'The right side is defined: the rule fires only where it has a value, as `Step` asks (lesson 6).', '.ceil C C')],
        },
        {
          hl: { r: [at(rules, 'let comps')], w: span(workedRule, '-- prio:', '⟦lhs⟧ ∧ ¬(applies') },
          notes: [note('r', at(rules, 'let comps'), 'The rules of a smaller priority, negated: no rule of a smaller priority applies.', '·.prio < r.prio')],
          say: "kompile's axiom in the prologue has neither premise: Γ's rule axiom is the one that says what `Step` says.",
        },
      ],
    },
    {
      id: 'y6',
      title: "The step's closure",
      panes: [{ id: 'c', label: 'KcoreSpec/Faithful.lean', source: closure, lang: 'lean' }],
      frames: [
        {
          hl: { c: [at(closure, 'def stepClosureItem'), at(closure, 'pat := ∀∀ y')] },
          notes: [note('c', at(closure, 'pat := ∀∀ y'), 'Every successor of a configuration is one some rule gives.', 'KoreAML.sNext (.evar y)')],
        },
        {
          hl: { c: [at(closure, 'def Γstep')] },
          notes: [note('c', at(closure, 'def Γstep'), 'Kept beside Γ, not in it: lesson 10 says where it is used.', 'Γstep')],
        },
      ],
    },
    {
      id: 'y7',
      title: 'A configuration as a pattern',
      panes: [{ id: 'd', label: 'KcoreSpec/Statements.lean', source: den, lang: 'lean' }],
      frames: [
        {
          hl: { d: [at(den, 'def den')] },
          notes: [note('d', at(den, 'def den'), '`⟦t⟧`: a ground term as a pattern, its symbols applied to its arguments\' patterns.', 'KoreAML.den')],
          say: 'With `⟦x⟧`, lesson 8\'s `⟦x⟧ ⇒ •⟦y⟧` is a statement about two configurations. Lesson 10 asks Γ to entail it for every step.',
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'What does the axiom `⟦Nat⟧ ≡ μX. z ∨ s(X)` rule out?',
      options: ['An element of `Nat` that is not `z`, `s(z)`, `s(s(z))`, …', 'That `z` and `s(z)` are equal', 'That `pred` is undefined'],
      answer: 0,
      why: 'No junk: the least set closed under the constructors is all of `Nat`.',
    },
    {
      q: "Where does Γ's axiom for a rule let it fire?",
      options: ['Where its left side matches, its requires holds, no rule of a smaller priority applies, and its right side is defined', 'Wherever its left side matches', 'Only on reachable configurations'],
      answer: 0,
      why: "Exactly `Step`'s premises (lesson 6), stated in matching logic.",
    },
  ],
  checked: [
    `Every pane is kcore-spec's text at \`${coreCommit}\`.`,
    "The panes headed “Simplified, by hand” render the axioms for peano and prio from the definitions above in simplified notation (sorts and guards left out). Lean did not compute them.",
  ],
}
