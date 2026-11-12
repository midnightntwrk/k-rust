'use client'

// Core lesson 11: well-formedness, the decidable check `coreOK` the theorems assume of a
// semantics, which reads only what their proofs use: sortedOK (subsorts, clauses and rules well
// sorted), faithCoreOK's twelve conditions as a table, a kernel-checked semantics whose theory has
// no model because one condition fails, and the names apart. Every pane is kcore-spec's text at
// the manifest's commit.

import { type Source, coreCommit, coreFile, lineOf, slice, span } from '../data'
import { type Lesson, note } from '../lesson'
import { Rows } from '../viz'

const coreOK = slice(coreFile('KcoreSpec/Statements.lean'), '/-- **The decidable conditions soundness and completeness assume of a semantics**', 'c.sortedOK && c.faithCoreOK && c.hooksApart && c.predsApart && c.idsOK')
const tie = coreFile('KcoreSpec/Tie.lean')
const sorted = slice(tie, '/-- **The semantics is well sorted**', 'c.rules.all c.ruleSorted')
const sortedParts = slice(tie, '/-- A clause of `f` is well sorted over the function signatures', "sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort")
const apart = slice(tie, '/-- No user constructor or function is named like an interpreted hooked symbol', 'def Semantics.predsApart')
const wfLean = coreFile('KcoreSpec/DefinitionWf.lean')
const subsorts = slice(wfLean, '/-- The declared subsorts form a strict partial order', '  nodup subs')
const ids = slice(wfLean, "/-- The definition's own sorts and symbols are numbered as Core.lean says", '&& c.lib.ok)')
const faith = slice(coreFile('KcoreSpec/FaithOK.lean'), '/-- **The decidable conditions of the theory that soundness and completeness read**', 'kindsApart c && ctorsOnce c && fnsApart c')
const witness = coreFile('KcoreSpec/ModelKindsWitness.lean')
const witnessDoc = slice(witness, '  KCore. A semantics that meets every condition of `coreOK` but `kindsApart`', 'The decidable facts are kernel')
const witnessThm = slice(witness, '/-- Every condition of `coreOK` but `kindsApart` holds, and `FnHyp`. -/', 'theorem not_sound : ¬ SoundC c')

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

// What coreOK no longer asks, because no proof of either theorem reads it.
const notAsked = () => (
  <Rows
    head={['Not asked by coreOK', 'Still checked by']}
    rows={[
      { key: 'inh', cells: ['every sort has a value', 'okAll and wf, not core'] },
      { key: 'decl', cells: ['signatures are over declared sorts', 'okAll and wf, not core'] },
      { key: 'map', cells: ['a map pattern has at most one frame', 'okAll and wf, not core'] },
      { key: 'fn', cells: ['a function without clauses is never applied', 'okAll and wf, not core'] },
    ]}
  />
)

// faithCoreOK's conditions: name, what it says, and what needs it. "step": step soundness reads it;
// "model": the existence of a model reads it; "witness": a kernel-checked semantics meeting every
// other condition and FnHyp has no model without it (FaithOK.lean, the Model*Witness files).
const conditions: readonly [string, string, string][] = [
  ['namesNumbered', 'no symbol is named like ite at a sort; every sort of a function is numbered', 'step'],
  ['genWf', 'values are built by constructors and injections, in sorts with no literals', 'step'],
  ['collSortsOK', 'no collection sort holds a literal', 'step'],
  ['collsOK', "the definition's collections are well formed and built by their own symbols", 'step'],
  ['patHeadsOK', 'every symbol a left side may apply is one matching reads', 'step'],
  ['namesApartK', 'no two symbols, and no two sorts, share a name', 'model · witness'],
  ['LitsApart', 'no token or byte sort is Int or Bool, so a literal is told by its text', 'model'],
  ['sortsNumbered', 'every sort a value may have is a numbered sort', 'model · witness'],
  ['itesApart', 'symbols named like ite are named at a numbered sort, and apart by their sort', 'model · witness for the second half; the first not settled'],
  ['kindsApart', 'hooks and parameters are not constructors, nor parameters hooks', 'model · witness'],
  ['ctorsOnce', 'no constructor is listed twice', 'model · witness'],
  ['fnsApart', 'no function is named like a constructor, hook or parameter', 'model · witness'],
]

const table = () => (
  <Rows head={['Condition', 'What it says', 'Needed by']} rows={conditions.map(([n, says, why]) => ({ key: n, cells: [<code key="n">{n}</code>, says, why] }))} />
)

export const wf11: Lesson = {
  id: 'well-formedness',
  number: 11,
  title: 'Well-formedness',
  against: coreCommit,
  scenes: [
    {
      id: 'w1',
      title: 'A check Lean decides',
      panes: [{ id: 'c', label: 'KcoreSpec/Statements.lean', source: coreOK, lang: 'lean' }],
      frames: [
        {
          hl: { c: [at(coreOK, 'def Semantics.coreOK')] },
          say: "The theorems' other hypothesis is a check on the semantics that Lean computes: `coreOK` is `true` or `false`, and a package proves it is `true` by evaluation. It asks only what the proofs of the two theorems read.",
        },
        {
          hl: { c: [at(coreOK, 'c.sortedOK && c.faithCoreOK')] },
          notes: [
            note('c', at(coreOK, 'c.sortedOK && c.faithCoreOK'), 'Subsorts, clauses and rules are well sorted.', 'c.sortedOK'),
            note('c', at(coreOK, 'c.sortedOK && c.faithCoreOK'), 'The conditions the theory Γ needs to have a model.', 'c.faithCoreOK'),
            note('c', at(coreOK, 'c.sortedOK && c.faithCoreOK'), 'Names and numbers apart.', 'c.hooksApart && c.predsApart && c.idsOK'),
          ],
          say: 'Five conjuncts.',
        },
      ],
    },
    {
      id: 'w2',
      title: 'Well-sorted subsorts',
      panes: [
        { id: 's', label: 'KcoreSpec/Tie.lean', source: sorted, lang: 'lean' },
        { id: 'u', label: 'KcoreSpec/DefinitionWf.lean', source: subsorts, lang: 'lean' },
      ],
      frames: [
        {
          hl: { s: span(sorted, 'def sortedOK', 'c.rules.all c.ruleSorted') },
          say: '`sortedOK` has three parts: the subsorts, every clause, every rule.',
        },
        {
          hl: { u: span(subsorts, 'def subsortsOK', 'nodup subs') },
          notes: [
            note('u', at(subsorts, '(c.userSorts.contains b || c.libConsSorts.contains b)'), "The upper sort is one of the definition's sorts or a library sort of constructor terms, such as JSON. A sort of literals or a collection sort is refused.", 'c.libConsSorts.contains b'),
            note('u', at(subsorts, 'c.declaredClosure.all (fun (a, b) => a != b)'), 'No cycle: a strict partial order.', 'a != b'),
          ],
        },
      ],
    },
    {
      id: 'w3',
      title: 'Well-sorted clauses and rules',
      panes: [{ id: 'r', label: 'KcoreSpec/Tie.lean', source: sortedParts, lang: 'lean' }],
      frames: [
        {
          hl: { r: span(sortedParts, 'def ruleSorted', "r.vars r.rhs == some topCellSort") },
          notes: [
            note('r', at(sortedParts, 'sortOfTerm c.patCtxAll r.vars r.lhs == some topCellSort'), 'Both sides have the configuration sort…', 'some topCellSort'),
            note('r', at(sortedParts, 'binds r.vars.length (varOccs r.lhs)'), '…the left side binds every variable…', 'binds'),
            note('r', at(sortedParts, 'reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req'), '…and the `requires` is a Bool.', 'reqOK'),
          ],
        },
        {
          hl: { r: span(sortedParts, 'def clauseSorted', 'cl.rhs == some f.result') },
          notes: [note('r', at(sortedParts, 'def clauseSorted'), "A clause the same way: its patterns of the function's argument sorts, its right side of its result sort.", 'clauseSorted')],
        },
      ],
    },
    {
      id: 'w4',
      title: 'What it does not ask',
      visual: notAsked,
      frames: [
        { say: 'No proof of either theorem reads these four, so `coreOK` does not ask them. Larger checks still do, for the executable matcher and the tie to a KORE text, but they are not part of the core.' },
      ],
    },
    {
      id: 'w5',
      title: 'What the theory needs',
      panes: [{ id: 'f', label: 'KcoreSpec/FaithOK.lean', source: faith, lang: 'lean' }],
      frames: [
        {
          hl: { f: span(faith, 'def Semantics.faithCoreOK', 'kindsApart c && ctorsOnce c && fnsApart c') },
          say: '`faithCoreOK` is twelve conditions, mostly about names and numbering. Each closes a way the theory Γ of lesson 9 would say something false of the definition, or have no model at all.',
        },
      ],
    },
    {
      id: 'w6',
      title: 'The twelve conditions',
      visual: table,
      frames: [
        { say: '"Step": step soundness reads it. "Model": the existence of a model reads it. "Witness": a kernel-checked definition that meets every other condition and the hypothesis on functions has no model without it.' },
        { say: 'Not settled: the first half of `itesApart`, that every symbol named like `ite` is named at a numbered sort. It may be needed by the proof only and not in truth. The second half, no two such symbols at one sort, has a witness.' },
      ],
    },
    {
      id: 'w7',
      title: 'A theory with no model',
      panes: [
        { id: 'd', label: 'KcoreSpec/ModelKindsWitness.lean', source: witnessDoc, lang: 'lean' },
        { id: 't', label: 'KcoreSpec/ModelKindsWitness.lean', source: witnessThm, lang: 'lean' },
      ],
      frames: [
        {
          hl: { d: span(witnessDoc, 'The library lists the interpreted hook `ite`', 'distinct values of KItem distinct elements') },
          notes: [note('d', at(witnessDoc, 'The library lists the interpreted hook `ite`'), 'A builtin operation also listed as a constructor: Γ says one term is two different values.', 'ite')],
        },
        {
          hl: { t: span(witnessThm, 'theorem meets_others', 'Model.fnsApart c = true ∧ FnHyp c') },
          notes: [note('t', at(witnessThm, 'theorem meets_others'), 'Every other condition of `coreOK` holds, and `FnHyp`…', 'meets_others')],
        },
        {
          hl: { t: [at(witnessThm, 'theorem not_sound')] },
          notes: [note('t', at(witnessThm, 'theorem not_sound'), '…yet soundness fails, a fact the kernel checks. `kindsApart` cannot be left out.', '¬ SoundC c')],
        },
      ],
    },
    {
      id: 'w8',
      title: 'Names apart',
      panes: [
        { id: 'a', label: 'KcoreSpec/Tie.lean', source: apart, lang: 'lean' },
        { id: 'n', label: 'KcoreSpec/DefinitionWf.lean', source: ids, lang: 'lean' },
      ],
      frames: [
        {
          hl: { a: [at(apart, 'def Semantics.hooksApart'), at(apart, 'def Semantics.predsApart')] },
          notes: [note('a', at(apart, 'def Semantics.hooksApart'), 'No user symbol is named like a builtin operation…', 'hooksApart'), note('a', at(apart, 'def Semantics.predsApart'), '…and the functions evaluation reads are named apart.', 'predsApart')],
        },
        {
          hl: { n: span(ids, 'def idsOK', '&& c.lib.ok)') },
          notes: [note('n', at(ids, 'def idsOK'), "The definition's own sorts and symbols are numbered in order, as lesson 1 showed for peano.", 'idsOK')],
          say: "Every package proves its `coreOK` by evaluation, and a package can be generated from it alone. The larger check `wf` implies it and is what the tie to a KORE text uses; it is not part of the core.",
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'How does a package show that its semantics passes `coreOK`?',
      options: ['Lean evaluates the check to `true`, and the kernel checks that', 'Its author writes a proof for each condition', 'By running krust on it'],
      answer: 0,
      why: '`coreOK` is a function to `Bool`: a decision, not an assumption.',
    },
    {
      q: 'Why does `coreOK` not ask that every sort has a value?',
      options: ['No proof of either theorem reads it', 'Every sort always has a value', 'It is too expensive to check'],
      answer: 0,
      why: 'The check asks only what the proofs use; larger checks outside the core still ask it.',
    },
  ],
  checked: [
    `Every pane is kcore-spec's text at \`${coreCommit}\`, the witness included; its theorems are checked by Lean's kernel.`,
    'The two tables summarise Tie.lean, DefinitionWf.lean and FaithOK.lean in words.',
  ],
}
