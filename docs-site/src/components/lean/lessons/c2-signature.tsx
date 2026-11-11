'use client'

// Core lesson 2: the signature. A definition as one Lean value, `Semantics`: constructors,
// subsorts, functions as clauses with priorities, rules with priorities, collections. Every Lean
// pane is kcore-spec's text at the manifest's commit; the worked panes are derived by hand from it
// and from peano's Names.lean, with the numbers read from that file.

import { type Source, coreCommit, coreFile, lineOf, slice, span, textSource } from '../data'
import { type Lesson, note } from '../lesson'

const coreLean = coreFile('KcoreSpec/Core.lean')
const sem = slice(coreLean, 'structure Semantics where', 'hooks : HookParams')
const ctorSig = slice(coreFile('KcoreSpec/FixedSignature.lean'), '/-- A constructor or a hooked symbol', '  result : Srt')
const fnClause = slice(coreLean, '/-- A clause `f(p₁, …, pₙ) = rhs', '  total : Bool := false')
const rule = slice(coreLean, '/-- A rewrite rule `lhs => rhs', '  prio : Nat')
const colls = slice(coreLean, '/-- A collection sort:', '   ⟨Srt.list, .list')
const names = slice(coreFile('examples/peano/Peano/Names.lean'), 'namespace Sym', 'end Srt')
const prioK = coreFile('f2-examples/prio.k')
const fprioK = slice(coreFile('f2-examples/fprio.k'), 'syntax Int ::= pr(Int)', "rule [op-one]")

const numberIn = (src: Source, def: string) => {
  const line = src.text.split('\n')[lineOf(src, def) - src.start]
  const m = /:= (\d+)\s*$/.exec(line)
  if (!m) throw new Error(`lean lessons: no number on ${line}`)
  return Number(m[1])
}
const sym = (n: string) => numberIn(names, `def «${n}» : KCore.Sym`)
const srt = (n: string) => numberIn(names, `def «${n}» : KCore.Srt`)
const [z, s, run, done, pred] = [sym('z'), sym('s'), sym('run'), sym('done'), sym('pred')]
const [Nat, State, Val] = [srt('Nat'), srt('State'), srt('Val')]

const workedSig = textSource('worked by hand', [
  "-- peano's own constructors",
  `{ name := ${z}, args := [],     result := ${Nat} }    -- z : Nat`,
  `{ name := ${s}, args := [${Nat}],   result := ${Nat} }    -- s : Nat → Nat`,
  `{ name := ${run}, args := [${Nat}],   result := ${State} }    -- run : Nat → State`,
  `{ name := ${done}, args := [${Val}],   result := ${State} }    -- done : Val → State`,
  '',
  '-- its subsort: Nat below Val',
  `(${Nat}, ${Val})`,
].join('\n'))

const workedPred = textSource('worked by hand', [
  '-- pred, from peano.k',
  `{ label := ${pred}, args := [${Nat}], result := ${Nat},`,
  '  clauses := [',
  '    -- rule pred(s(N)) => N',
  `    { vars := [${Nat}], pats := [.app ${s} [.var 0]], req := none,`,
  '      rhs := .var 0, prio := 50 },',
  '    -- rule pred(_) => z [owise]',
  `    { vars := [${Nat}], pats := [.var 0], req := none,`,
  `      rhs := .app ${z} [], prio := 200 } ] }`,
].join('\n'))

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

export const signature2: Lesson = {
  id: 'signature',
  number: 2,
  title: 'Signature',
  against: coreCommit,
  scenes: [
    {
      id: 'g1',
      title: 'A definition is a value',
      panes: [{ id: 's', label: 'KcoreSpec/Core.lean', source: sem, lang: 'lean' }],
      frames: [
        { hl: { s: [at(sem, 'structure Semantics where')] }, say: "Lesson 1's terms are built from sorts and symbols. A definition says which there are and what they do, and in the core a whole definition is one Lean value of this structure." },
        {
          hl: { s: [at(sem, 'userSorts : List Srt'), at(sem, 'ctors : List CtorSig'), at(sem, 'userSubsorts :')] },
          notes: [note('s', at(sem, 'ctors : List CtorSig'), 'Its constructors.', 'ctors'), note('s', at(sem, 'userSubsorts :'), 'Its subsorts.', 'userSubsorts')],
        },
        {
          hl: { s: [at(sem, 'fns : List Fn'), at(sem, 'rules : List Rule')] },
          notes: [note('s', at(sem, 'fns : List Fn'), 'Its functions…', 'fns'), note('s', at(sem, 'rules : List Rule'), '…and its rules.', 'rules')],
        },
        {
          hl: { s: [at(sem, 'pgmSort : Srt'), at(sem, 'sortNames : List String'), at(sem, 'symNames : List String')] },
          notes: [note('s', at(sem, 'pgmSort : Srt'), 'The sort of the program the configuration starts from.', 'pgmSort'), note('s', at(sem, 'symNames : List String'), 'Names, for printing. Nothing that decides or steps reads them.', 'symNames')],
        },
        {
          hl: { s: [at(sem, 'lib : Lib'), at(sem, 'params : List ParamSig'), at(sem, 'hooks : HookParams')] },
          notes: [
            note('s', at(sem, 'lib : Lib'), 'Not settled: the library registry becomes a list of hook domains.', 'lib'),
            note('s', at(sem, 'params : List ParamSig'), 'Not settled: sort parameters are read by a special case for `ite`.', 'params'),
            note('s', at(sem, 'hooks : HookParams'), 'Not settled: hook domains.', 'hooks'),
          ],
        },
      ],
    },
    {
      id: 'g2',
      title: 'Constructors and subsorts',
      panes: [
        { id: 'c', label: 'KcoreSpec/FixedSignature.lean', source: ctorSig, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedSig, lang: 'lean' },
      ],
      frames: [
        {
          hl: { c: span(ctorSig, 'structure CtorSig', '  result : Srt'), w: span(workedSig, `{ name := ${z},`, `{ name := ${done},`) },
          notes: [note('c', at(ctorSig, 'structure CtorSig'), 'A constructor: its symbol, argument sorts and result sort.'), note('w', at(workedSig, `{ name := ${done},`), '`done` takes a `Val`.', `[${Val}]`)],
        },
        {
          hl: { w: [at(workedSig, `(${Nat}, ${Val})`)] },
          notes: [note('w', at(workedSig, `(${Nat}, ${Val})`), 'A pair (smaller, larger): a `Nat` is also a `Val`.')],
          say: "This is why `done(z)` holds `z` under an injection: `z` is a `Nat` used where a `Val` is expected.",
        },
      ],
    },
    {
      id: 'g3',
      title: 'Functions are clauses with priorities',
      panes: [
        { id: 'f', label: 'KcoreSpec/Core.lean', source: fnClause, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedPred, lang: 'lean' },
      ],
      frames: [
        {
          hl: { f: span(fnClause, 'structure Fn where', '  clauses : List Clause'), w: [at(workedPred, '{ label :=')] },
          notes: [note('f', at(fnClause, '  clauses : List Clause'), 'A function: its symbol, argument and result sorts, and clauses.', 'clauses')],
        },
        {
          hl: { f: span(fnClause, 'structure Clause where', '  prio : Nat := 50'), w: span(workedPred, '    { vars :=', '      rhs := .var 0') },
          notes: [
            note('f', at(fnClause, '  pats : List Term'), 'One pattern per argument.', 'pats'),
            note('f', at(fnClause, '  req : Option Term'), 'An optional condition.', 'req'),
            note('f', at(fnClause, '  prio : Nat := 50'), 'A priority.', 'prio'),
          ],
        },
        {
          hl: { w: [at(workedPred, 'prio := 50'), at(workedPred, 'prio := 200')] },
          notes: [note('w', at(workedPred, 'prio := 50'), 'No attribute: priority 50.', 'prio := 50'), note('w', at(workedPred, 'prio := 200'), '`[owise]`: priority 200.', 'prio := 200')],
        },
        {
          hl: { f: [at(fnClause, 'The order of `clauses` carries no meaning')] },
          notes: [note('f', at(fnClause, 'The order of `clauses` carries no meaning'), 'The order of the clauses means nothing; only priorities order them.')],
          say: 'What a priority means is lesson 5.',
        },
      ],
    },
    {
      id: 'g4',
      title: 'Priorities in another definition',
      panes: [{ id: 'k', label: 'fprio.k', source: fprioK, lang: 'k' }],
      frames: [
        {
          hl: { k: span(fprioK, 'rule [pr-low]', 'rule [pr-mid]') },
          notes: [
            note('k', at(fprioK, 'rule [pr-low]'), 'Priority 40.', 'priority(40)'),
            note('k', at(fprioK, 'rule [pr-def]'), 'Priority 50.'),
            note('k', at(fprioK, 'rule [pr-mid]'), 'Priority 100.', 'priority(100)'),
          ],
          say: "fprio's `pr` has three clauses of priorities 40, 50 and 100. At `0`, all three patterns match.",
        },
        {
          hl: { k: span(fprioK, 'rule [op-zz]', 'rule [op-one]') },
          notes: [note('k', at(fprioK, 'rule [op-zz]'), 'Priority 30.', 'priority(30)'), note('k', at(fprioK, 'rule [op-one]'), 'Priority 200.', 'owise')],
        },
      ],
    },
    {
      id: 'g5',
      title: 'Rules have priorities too',
      panes: [
        { id: 'r', label: 'KcoreSpec/Core.lean', source: rule, lang: 'lean' },
        { id: 'k', label: 'prio.k', source: prioK, lang: 'k' },
      ],
      frames: [
        {
          hl: { r: span(rule, 'structure Rule where', '  prio : Nat') },
          notes: [note('r', at(rule, '  lhs : Term'), 'A pattern over the whole configuration, cells included, as in the prologue.', 'lhs')],
        },
        {
          hl: { k: span(prioK, 'rule <k> go(X:D)', 'rule <k> go(_)') },
          notes: [
            note('k', at(prioK, 'rule <k> go(X:D)'), 'Priority 40.', 'priority(40)'),
            note('k', at(prioK, 'rule <k> go(X:B)'), 'Priority 50.'),
            note('k', at(prioK, 'rule <k> go(_)'), 'Priority 200.', 'owise'),
          ],
          say: 'A rule applies only where no rule of a smaller priority does: lesson 6.',
        },
      ],
    },
    {
      id: 'g6',
      title: 'Collections',
      panes: [{ id: 'c', label: 'KcoreSpec/Core.lean', source: colls, lang: 'lean' }],
      frames: [
        {
          hl: { c: span(colls, 'structure CollSig where', '  concat : Sym') },
          notes: [note('c', at(colls, 'structure CollSig where'), 'A collection sort: finite maps from `key` to `val`, or finite sets or lists of `key`, with the symbols that build them.')],
        },
        {
          hl: { c: span(colls, 'def builtinColls', '   ⟨Srt.list, .list') },
          notes: [note('c', at(colls, 'def builtinColls'), "The library's `Map`, `Set` and `List`. A definition adds its own in `colls`.")],
          say: 'Lesson 4 matches patterns against collections.',
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'What priority does `rule pred(_) => z [owise]` have?',
      options: ['200', '50', 'None: it is tried after the other clause'],
      answer: 0,
      why: '`[owise]` is priority 200. Nothing is "tried after": priorities alone order clauses.',
    },
    {
      q: "Does swapping the two clauses of `pred` in `peano.k` change the definition's meaning?",
      options: ['No: the order of clauses carries no meaning', 'Yes: the first clause is tried first', 'Only if both clauses have the same priority'],
      answer: 0,
      why: 'A `Fn` keeps its clauses in a list for printing, and nothing in the core reads that order.',
    },
  ],
  checked: [
    `The Lean in every pane is kcore-spec's text at \`${coreCommit}\`, and so are \`prio.k\` and \`fprio.k\`.`,
    "The panes headed “Worked by hand” are derived from those definitions and from peano's numbers in `Names.lean`. Lean did not compute them.",
  ],
}
