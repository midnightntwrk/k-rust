'use client'

// Core lesson 7: obligations. The five kinds of fact a definition may leave to its author
// (`Obligations`), their statements over the semantics (`Eval` has a result or a value,
// `ClausesAgree`, `MatchIndependent`), and that a definition with none gets its theorems
// unconditionally: peano's generated statements against fprio's, whose one obligation is proved
// by hand. Every pane is kcore-spec's text at the manifest's commit.

import { type Source, coreCommit, coreFile, lineOf, slice, span } from '../data'
import { type Lesson, note } from '../lesson'

const stmts = coreFile('KcoreSpec/Statements.lean')
const obligations = slice(stmts, 'def Obligations (d : Definition) : Prop :=', '(∀ o ∈ d.sem.lazyObligations, o.Holds d.sem)')
const agree = slice(coreFile('KcoreSpec/ClausesAgree.lean'), '/-- Each two equations of f of one priority are coherent', "cl.prio = cl'.prio → Coherent c cl cl' ∧ Coherent c cl' cl")
const coherent = slice(coreFile('KcoreSpec/EvalFunctional.lean'), '/-- Two clauses (or one clause twice) are coherent:', 'def MatchIndependent (c : Semantics) (cl : Clause) : Prop := Coherent c cl cl')
const peanoSound = slice(coreFile('examples/peano/Peano/Sound.lean'), '/-- **Soundness** (`KCore.Sound`)', 'theorem sound : Sound defn')
const fprioSound = slice(coreFile('examples/fprio/Fprio/Sound.lean'), '/-- **Soundness** (`KCore.Sound`)', 'theorem sound (hob : Obligations defn)')
const values = coreFile('examples/fprio/User/Values.lean')
const userAgree = slice(values, "/-- **`ag`'s agreement**", 'theorem ag_agree :')
const userHold = slice(values, "/-- **The package's named obligations hold**", 'theorem sound_defn : Sound defn')
const fprioK = slice(coreFile('f2-examples/fprio.k'), 'syntax Int ::= ag(Int)', 'rule [ag-sq]')

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

export const obligations7: Lesson = {
  id: 'obligations',
  number: 7,
  title: 'Obligations',
  against: coreCommit,
  scenes: [
    {
      id: 'o1',
      title: 'What a definition may leave to its author',
      panes: [{ id: 'o', label: 'KcoreSpec/Statements.lean', source: obligations, lang: 'lean' }],
      frames: [
        {
          hl: { o: [at(obligations, 'def Obligations')] },
          say: 'Some facts about a definition no check can decide for every definition: that a function terminates, or that two clauses agree. A definition names the ones it needs, and the theorems assume them. There are five kinds.',
        },
        {
          hl: { o: span(obligations, '(∀ f ∈ d.sem.orderObligations', '∀ vs, d.sem.sortsOf vs = some fn.args → ∃ r, Eval d.sem f vs r)') },
          notes: [
            note('o', at(obligations, '∀ vs, d.sem.sortsOf vs = some fn.args → ∃ r, Eval d.sem f vs r)'), 'A function it names has a result at every argument list of its sorts: its evaluation ends.', '∃ r, Eval d.sem f vs r'),
            note('o', at(obligations, '(∀ f ∈ d.sem.orderObligations'), 'Not settled: which functions this kind names, and that `Obligations` takes a whole `Definition` rather than its semantics.', 'd.cert.obligations d.sem'),
          ],
        },
        {
          hl: { o: span(obligations, '(∀ f ∈ d.sem.totalObligations', '∃ v, Eval d.sem f vs (some v))') },
          notes: [note('o', at(obligations, '∃ v, Eval d.sem f vs (some v))'), 'A function declared `[total]` that it names has a value there, not just a result.', 'some v')],
        },
        {
          hl: { o: [at(obligations, '(∀ f ∈ d.sem.agreeObligations')] },
          notes: [note('o', at(obligations, '(∀ f ∈ d.sem.agreeObligations'), 'Its clauses of one priority agree.', 'ClausesAgree')],
        },
        {
          hl: { o: span(obligations, '(∀ p ∈ d.sem.matchObligations', 'MatchIndependent d.sem cl)') },
          notes: [note('o', at(obligations, 'MatchIndependent d.sem cl)'), 'Two matches of one clause give one result.', 'MatchIndependent')],
        },
        {
          hl: { o: [at(obligations, '(∀ o ∈ d.sem.lazyObligations')] },
          notes: [note('o', at(obligations, '(∀ o ∈ d.sem.lazyObligations'), 'Not settled: follows the strictness choice (decision 1 on [State of the core](/lean/state-of-the-core)).', 'o.Holds d.sem')],
        },
      ],
    },
    {
      id: 'o2',
      title: 'Clauses that agree',
      panes: [
        { id: 'a', label: 'KcoreSpec/ClausesAgree.lean', source: agree, lang: 'lean' },
        { id: 'k', label: 'fprio.k', source: fprioK, lang: 'k' },
      ],
      frames: [
        {
          hl: { a: [at(agree, 'def ClausesAgree'), at(agree, "cl.prio = cl'.prio → Coherent")], k: span(fprioK, 'rule [ag-z]', 'rule [ag-sq]') },
          notes: [note('a', at(agree, "cl.prio = cl'.prio → Coherent"), 'Each two clauses of one priority are coherent, in both orders.', 'Coherent c cl cl\' ∧ Coherent c cl\' cl'), note('k', at(fprioK, 'rule [ag-sq]'), 'At `0`, both apply: `0`, and `0 *Int 0`.', 'N *Int N')],
          say: 'Lesson 5 left this open: `Eval` lets either of two clauses of one priority decide. Where both apply, their results must agree.',
        },
      ],
    },
    {
      id: 'o3',
      title: 'Coherent',
      panes: [{ id: 'c', label: 'KcoreSpec/EvalFunctional.lean', source: coherent, lang: 'lean' }],
      frames: [
        {
          hl: { c: span(coherent, 'def Coherent', "∀ r r', EvalTerm c σ cl.rhs r → EvalTerm c σ' cl'.rhs r' → r = r'") },
          notes: [
            note('c', at(coherent, "cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs"), 'Wherever both clauses apply at one argument list…', 'AppliesAt'),
            note('c', at(coherent, "∀ r r', EvalTerm c σ cl.rhs r"), '…their right-hand sides have the same result (or are the same instance of one right-hand side).', 'r = r\''),
          ],
        },
        {
          hl: { c: [at(coherent, 'def MatchIndependent')] },
          notes: [note('c', at(coherent, 'def MatchIndependent'), 'A clause coherent with itself: two matches of it, such as two ways of splitting a map (lesson 4), give one result.', 'Coherent c cl cl')],
        },
      ],
    },
    {
      id: 'o4',
      title: 'With none, the theorems are unconditional',
      panes: [
        { id: 'p', label: 'Peano/Sound.lean', source: peanoSound, lang: 'lean' },
        { id: 'f', label: 'Fprio/Sound.lean', source: fprioSound, lang: 'lean' },
      ],
      frames: [
        {
          hl: { p: [at(peanoSound, 'theorem sound : Sound defn')] },
          notes: [note('p', at(peanoSound, 'theorem sound : Sound defn'), 'peano names no obligation: its soundness takes no hypothesis.', 'Sound defn')],
          say: "Both files are written by the generator, which states each definition's theorems. The kernel checks them; what to read is their statements.",
        },
        {
          hl: { f: [at(fprioSound, 'theorem sound (hob : Obligations defn)')] },
          notes: [note('f', at(fprioSound, 'theorem sound (hob : Obligations defn)'), "fprio names one, `ag`'s agreement, so its soundness assumes its obligations.", 'hob : Obligations defn')],
        },
      ],
    },
    {
      id: 'o5',
      title: 'Discharging an obligation',
      panes: [
        { id: 'a', label: 'User/Values.lean', source: userAgree, lang: 'lean' },
        { id: 'h', label: 'User/Values.lean', source: userHold, lang: 'lean' },
      ],
      frames: [
        {
          hl: { a: [at(userAgree, 'theorem ag_agree')] },
          notes: [note('a', at(userAgree, 'theorem ag_agree'), "The one named obligation, proved by hand: `ag`'s clauses agree.", 'ClausesAgree c fn')],
        },
        {
          hl: { h: [at(userHold, 'theorem obligations_hold'), at(userHold, '   ag_agree,')] },
          notes: [note('h', at(userHold, '   ag_agree,'), 'The third kind is `ag_agree`; the four other lists are empty.', 'ag_agree')],
        },
        {
          hl: { h: [at(userHold, 'theorem sound_defn')] },
          notes: [note('h', at(userHold, 'theorem sound_defn'), "So fprio is sound with no hypothesis left.", 'Sound defn')],
          say: 'From a named obligation to the theorem: the author proves the obligation, and the kernel checks the proof.',
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'Why does fprio name an obligation and peano none?',
      options: ["fprio's `ag` has two clauses of one priority that both apply at `0`, and no check shows they agree", 'fprio uses integers', 'peano has no functions'],
      answer: 0,
      why: "peano's `pred` has clauses of two different priorities, which never compete.",
    },
    {
      q: 'What does `MatchIndependent` ask of a clause?',
      options: ['Two matches of it at one argument list give one result', 'It has exactly one match', 'Its pattern has no variables'],
      answer: 0,
      why: 'A map pattern may match several ways, and the clause must not care which.',
    },
  ],
  checked: [
    `Every pane is kcore-spec's text at \`${coreCommit}\`: the core's definitions, the statements the generator wrote for peano and fprio, and fprio's hand proof.`,
    "The proofs are checked by Lean's kernel. This lesson shows their statements only.",
  ],
}
