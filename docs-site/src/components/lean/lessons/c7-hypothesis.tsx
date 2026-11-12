'use client'

// Core lesson 7: what the theorems assume of a definition's functions (`FnHyp`), as four
// statements about evaluation: a result, a value for [total] ones, clauses of one priority that
// agree (`ClausesAgree`, `Coherent`), matches of one clause that agree (`MatchIndependent`). Then,
// in one scene, how a package meets it: the kernel-checked machinery, with peano (nothing named)
// and fprio (one fact proved by hand). Every pane is kcore-spec's text at the manifest's commit.

import { type Source, coreCommit, coreFile, lineOf, slice, span } from '../data'
import { type Lesson, note } from '../lesson'

const stmts = coreFile('KcoreSpec/Statements.lean')
const fnHyp = slice(stmts, '/-- **What the statements assume of the functions of a semantics**', '(∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl)')
const agree = slice(coreFile('KcoreSpec/ClausesAgree.lean'), '/-- Each two equations of f of one priority are coherent', "cl.prio = cl'.prio → Coherent c cl cl' ∧ Coherent c cl' cl")
const coherent = slice(coreFile('KcoreSpec/EvalFunctional.lean'), '/-- Two clauses (or one clause twice) are coherent:', 'def MatchIndependent (c : Semantics) (cl : Clause) : Prop := Coherent c cl cl')
const peanoSound = slice(coreFile('examples/peano/Peano/Sound.lean'), '/-- **Soundness** (`KCore.Sound`)', 'theorem sound : Sound defn')
const values = coreFile('examples/fprio/User/Values.lean')
const userChain = slice(values, "/-- **The package's named obligations hold**", 'theorem sound_defn : Sound defn')
const fprioK = slice(coreFile('f2-examples/fprio.k'), 'syntax Int ::= ag(Int)', 'rule [ag-sq]')

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

export const hypothesis7: Lesson = {
  id: 'hypothesis',
  number: 7,
  title: 'What functions must do',
  against: coreCommit,
  scenes: [
    {
      id: 'h1',
      title: 'Four statements about functions',
      panes: [{ id: 'f', label: 'KcoreSpec/Statements.lean', source: fnHyp, lang: 'lean' }],
      frames: [
        {
          hl: { f: [at(fnHyp, 'def FnHyp')] },
          say: "Lesson 10's theorems assume two things of a semantics: a check Lean decides (lesson 11), and this. It is four statements about evaluation, the relation of lesson 5, which no check can decide for every definition.",
        },
        {
          hl: { f: [at(fnHyp, '∃ r, Eval c fn.label vs r)')] },
          notes: [note('f', at(fnHyp, '∃ r, Eval c fn.label vs r)'), 'Every function has a result at every argument list of its sorts: its evaluation ends. The result may be "undefined".', '∃ r, Eval c fn.label vs r')],
        },
        {
          hl: { f: [at(fnHyp, 'fn.total = true')] },
          notes: [note('f', at(fnHyp, 'fn.total = true'), 'A function declared `[total]` has a value there, not just a result.', 'some v')],
        },
        {
          hl: { f: [at(fnHyp, 'ClausesAgree c fn)'), at(fnHyp, 'MatchIndependent c cl)')] },
          notes: [
            note('f', at(fnHyp, 'ClausesAgree c fn)'), 'Its clauses of one priority agree where both apply…', 'ClausesAgree'),
            note('f', at(fnHyp, 'MatchIndependent c cl)'), '…and two matches of one clause agree.', 'MatchIndependent'),
          ],
          say: "Together, the last two make a function's result unique, though `Eval` reads no order between clauses of one priority.",
        },
      ],
    },
    {
      id: 'h2',
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
      id: 'h3',
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
      id: 'h4',
      title: 'How a package meets it',
      panes: [
        { id: 'p', label: 'Peano/Sound.lean', source: peanoSound, lang: 'lean' },
        { id: 'u', label: 'fprio, User/Values.lean', source: userChain, lang: 'lean' },
      ],
      frames: [
        {
          hl: { p: [at(peanoSound, 'theorem sound : Sound defn')] },
          notes: [note('p', at(peanoSound, 'theorem sound : Sound defn'), 'peano: the checks confirm all of it, so its soundness takes no premise.', 'Sound defn')],
          say: 'This is machinery, checked by the kernel, not something to review. Checks Lean decides confirm most of these facts for a definition and name the rest as a short list.',
        },
        {
          hl: { u: [at(userChain, '   ag_agree,'), at(userChain, 'theorem sound_defn')] },
          notes: [note('u', at(userChain, '   ag_agree,'), "fprio: one fact is named, `ag`'s clauses agree; its author proves it…", 'ag_agree'), note('u', at(userChain, 'theorem sound_defn'), '…and the package is sound with no premise left.', 'Sound defn')],
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'Why does fprio name a fact for its author to prove, and peano none?',
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
    `Every pane is kcore-spec's text at \`${coreCommit}\`: the core's definitions, the statement the generator wrote for peano, and fprio's hand proof.`,
    "The proofs are checked by Lean's kernel. This lesson shows their statements only.",
  ],
}
