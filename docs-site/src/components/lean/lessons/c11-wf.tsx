'use client'

// Core lesson 11: well-formedness, the decidable check `coreOK` the theorems assume of a
// semantics: its five conjuncts in words and in Lean; okAll's five parts; faithOK's thirteen
// conditions as a table; a kernel-checked semantics whose theory has no model because one
// condition fails. Every pane is kcore-spec's text at the manifest's commit.

import { type Source, coreCommit, coreFile, lineOf, slice, span } from '../data'
import { type Lesson, note } from '../lesson'
import { Rows } from '../viz'

const coreOK = slice(coreFile('KcoreSpec/Statements.lean'), '/-- **The decidable conditions soundness and completeness assume of a semantics**', 'c.okAll && c.faithOK && c.hooksApart && c.predsApart && c.idsOK')
const tie = coreFile('KcoreSpec/Tie.lean')
const okAll = slice(tie, '/-- The definition is well-formed: as `ok`', 'c.declsOK && c.subsortsOK && c.inhabited && c.fnsOKAll && c.rules.all c.ruleOKAll')
const apart = slice(tie, '/-- No user constructor or function is named like an interpreted hooked symbol', 'def Semantics.predsApart')
const wfLean = coreFile('KcoreSpec/DefinitionWf.lean')
const decls = slice(wfLean, 'def declsOK : Bool :=', '[Srt.k, Srt.kitem, Srt.int, Srt.bool].contains c.pgmSort)')
const subsorts = slice(wfLean, '/-- Subsorts into the user', '  nodup subs')
const inhabited = slice(wfLean, '/-- Every sort of the definition has a value', 'c.userSorts.all all.contains')
const rules = slice(wfLean, '/-- A rule, as `ruleOK`, its left-hand side well-sorted', 'def clauseOKAll')
const fns = slice(wfLean, '/-- `fnOK`, its clauses as `clauseOKAll`. -/', 'def fnsOKAll')
const ids = slice(wfLean, "/-- The definition's own sorts and symbols are numbered as Core.lean says", '&& c.lib.ok)')
const faithOK = slice(coreFile('KcoreSpec/FaithOK.lean'), '/-- **The decidable conditions of the theory**', 'kindsApart c && ctorsOnce c && fnsApart c')
const witness = coreFile('KcoreSpec/ModelDupCtorWitness.lean')
const witnessDoc = slice(witness, '  KCore. A semantics that satisfies', 'The decidable facts are kernel decisions.')
const witnessThm = slice(witness, '/-- **`Γ c` has no model**', 'theorem no_model')

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

// faithOK's conditions: name, what it says, and why soundness or the model needs it. "Model"
// marks the conditions the existence of a model reads, "step" those step soundness reads
// (FaithOK.lean's header); "witness" those with a kernel-checked semantics whose Γ has no model
// without them; "not settled" the manifest's provisional ones.
const conditions: readonly [string, string, string][] = [
  ['namesNumbered', 'no symbol is named like ite at a sort; every sort of a function is numbered', 'step'],
  ['genWf', 'values are built by constructors and injections, in sorts with no literals', 'step'],
  ['collSortsOK', 'no collection sort holds a literal', 'step'],
  ['collsOK', "the definition's collections are well formed and built by their own symbols", 'step'],
  ['patHeadsOK', 'every symbol a left side may apply is one matching reads', 'step'],
  ['namesApartK', 'no two symbols, and no two sorts, share a name', 'model: without it Γ has no model (witness)'],
  ['LitsApart', 'no token or byte sort is Int or Bool, so a literal is told by its text', 'model'],
  ['sortsNumbered', 'every sort a value may have is a numbered sort', 'model · not settled'],
  ['collsNotCtors', "no collection's unit, element or concatenation is a constructor", 'model · not settled'],
  ['itesApart', 'symbols named like ite are apart by their sort', 'model · not settled'],
  ['kindsApart', 'hooks and parameters are not constructors, nor parameters hooks', 'model · not settled'],
  ['ctorsOnce', 'no constructor is listed twice', 'model: without it Γ has no model (witness)'],
  ['fnsApart', 'no function is named like a constructor, hook or parameter', 'model: without it Γ has no model (witness)'],
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
          say: "The theorems' other hypothesis is a check on the semantics that Lean computes: `coreOK` is `true` or `false`, and a package proves it is `true` by evaluation. It is the least interesting thing to read, and the last.",
        },
        {
          hl: { c: [at(coreOK, 'c.okAll && c.faithOK')] },
          notes: [
            note('c', at(coreOK, 'c.okAll && c.faithOK'), 'Declarations, subsorts, functions and rules are well formed.', 'c.okAll'),
            note('c', at(coreOK, 'c.okAll && c.faithOK'), "The conditions the theory Γ needs to have a model.", 'c.faithOK'),
            note('c', at(coreOK, 'c.okAll && c.faithOK'), 'Names and numbers apart.', 'c.hooksApart && c.predsApart && c.idsOK'),
          ],
          say: 'Five conjuncts.',
        },
      ],
    },
    {
      id: 'w2',
      title: 'Well-formed declarations',
      panes: [
        { id: 'o', label: 'KcoreSpec/Tie.lean', source: okAll, lang: 'lean' },
        { id: 'd', label: 'KcoreSpec/DefinitionWf.lean', source: decls, lang: 'lean' },
      ],
      frames: [
        {
          hl: { o: [at(okAll, 'def Semantics.okAll'), at(okAll, 'c.declsOK && c.subsortsOK')] },
          say: '`okAll` has five parts.',
        },
        {
          hl: { o: [at(okAll, 'c.declsOK && c.subsortsOK')], d: span(decls, 'def declsOK', 'c.pgmSort)') },
          notes: [note('d', at(decls, 'def declsOK'), 'Every constructor and function is declared over sorts the definition has.', 'declsOK')],
        },
      ],
    },
    {
      id: 'w3',
      title: 'Subsorts and inhabited sorts',
      panes: [
        { id: 's', label: 'KcoreSpec/DefinitionWf.lean', source: subsorts, lang: 'lean' },
        { id: 'i', label: 'KcoreSpec/DefinitionWf.lean', source: inhabited, lang: 'lean' },
      ],
      frames: [
        {
          hl: { s: span(subsorts, 'def subsortsOK', 'nodup subs') },
          notes: [note('s', at(subsorts, "c.declaredClosure.all (fun (a, b) => a != b)"), 'Subsorts form a strict partial order: no cycle.', 'a != b')],
        },
        {
          hl: { i: span(inhabited, 'def inhabited', 'c.userSorts.all all.contains') },
          notes: [note('i', at(inhabited, 'def inhabited'), 'Every sort has a value, built up from the sorts that surely have one.', 'inhabited')],
        },
      ],
    },
    {
      id: 'w4',
      title: 'Well-sorted functions and rules',
      panes: [
        { id: 'f', label: 'KcoreSpec/DefinitionWf.lean', source: fns, lang: 'lean' },
        { id: 'r', label: 'KcoreSpec/DefinitionWf.lean', source: rules, lang: 'lean' },
      ],
      frames: [
        {
          hl: { r: span(rules, 'def ruleOKAll', "sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort") },
          notes: [
            note('r', at(rules, 'sortOfTerm c.patCtxAll r.vars r.lhs == some topCellSort'), 'Both sides have the configuration sort…', 'some topCellSort'),
            note('r', at(rules, 'binds r.vars.length'), '…the left side binds every variable…', 'binds'),
            note('r', at(rules, 'reqOK'), '…and the `requires` is a Bool.', 'reqOK'),
          ],
        },
        {
          hl: { r: [at(rules, 'noMapIn r.lhs')] },
          notes: [note('r', at(rules, 'noMapIn r.lhs'), 'Not settled: at most one frame in a map pattern. Whether soundness needs it is not yet known.', 'noMapIn')],
        },
        {
          hl: { f: span(fns, 'def fnOKAll', '(!f.clauses.isEmpty || !used.contains f.label)') },
          notes: [
            note('f', at(fns, 'f.clauses.all (c.clauseOKAll f heads)'), 'Every clause well sorted, as a rule is.', 'clauseOKAll'),
            note('f', at(fns, '(!f.clauses.isEmpty || !used.contains f.label)'), 'Not settled: a function without clauses is never applied. It changes when such a function is read as a parameter.', '!f.clauses.isEmpty'),
          ],
        },
      ],
    },
    {
      id: 'w5',
      title: 'What the theory needs',
      panes: [{ id: 'f', label: 'KcoreSpec/FaithOK.lean', source: faithOK, lang: 'lean' }],
      frames: [
        {
          hl: { f: span(faithOK, 'def Semantics.faithOK', 'kindsApart c && ctorsOnce c && fnsApart c') },
          say: '`faithOK` is thirteen conditions, mostly about names and numbering. Each closes a way the theory Γ of lesson 9 would say something false of the definition, or have no model at all.',
        },
      ],
    },
    {
      id: 'w6',
      title: 'The thirteen conditions',
      visual: table,
      frames: [
        { say: '"Step": step soundness reads it. "Model": the existence of a model reads it. Four have no example yet of what goes wrong without them, and are not settled: they may be stricter than needed.' },
      ],
    },
    {
      id: 'w7',
      title: 'A theory with no model',
      panes: [
        { id: 'd', label: 'KcoreSpec/ModelDupCtorWitness.lean', source: witnessDoc, lang: 'lean' },
        { id: 't', label: 'KcoreSpec/ModelDupCtorWitness.lean', source: witnessThm, lang: 'lean' },
      ],
      frames: [
        {
          hl: { d: span(witnessDoc, 'its distinctness axiom (Cons-Dist)', 'inhabited model satisfies') },
          notes: [note('d', at(witnessDoc, 'its distinctness axiom (Cons-Dist)'), 'A constructor listed twice: its no-confusion axiom (lesson 9) says it differs from itself.', 'Cons-Dist')],
        },
        {
          hl: { t: [at(witnessThm, 'theorem no_model')] },
          notes: [note('t', at(witnessThm, 'theorem no_model'), 'So the theory has no model, a fact the kernel checks. `ctorsOnce` rules this semantics out.', 'no_model')],
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
          say: 'Every package proves its `coreOK` by evaluation. A larger check, `wf`, also reads the definition\'s presentation and its printing as KORE; it implies `coreOK` and is what the tie to a KORE text uses. It is not part of the core.',
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
      q: 'What goes wrong if a constructor is listed twice?',
      options: ["Γ says it differs from itself, so Γ has no model", 'Nothing: the second entry is ignored', 'Evaluation becomes nondeterministic'],
      answer: 0,
      why: 'That is the kernel-checked witness of the last scene but one.',
    },
  ],
  checked: [
    `Every pane is kcore-spec's text at \`${coreCommit}\`, the witness included; its theorems are checked by Lean's kernel.`,
    'The table summarises FaithOK.lean in words.',
  ],
}
