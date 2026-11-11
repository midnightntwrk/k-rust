'use client'

// Core lesson 5: evaluation. `Eval c f vs r` as a relation: a clause decides where it applies and
// every clause of a smaller priority fails; no result where every clause fails; the order of
// clauses means nothing; `[owise]` is priority 200. Then `EvalTerm`, a right-hand side's value.
// Every Lean pane is kcore-spec's text at the manifest's commit, as is fprio.k; the results shown
// are worked by hand from those definitions.

import { type Source, coreCommit, coreFile, lineOf, peanoK, slice, span, textSource } from '../data'
import { type Lesson, note } from '../lesson'

const ev = coreFile('KcoreSpec/Evaluation.lean')
const evalDef = slice(ev, '  /-- `Eval c f vs r`:', '(hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) : Eval c f vs none')
const fails = slice(ev, '  /-- `Fails c vs cl`:', '        ReqFails c σ cl')
const evalTerm = slice(ev, '  /-- `EvalTerm c σ t r`:', '(hvs : allSome rs = none) (hp : c.isParam f = false) : EvalTerm c σ (.app f ts) none')
const fprioK = slice(coreFile('f2-examples/fprio.k'), 'syntax Int ::= pr(Int)', 'rule [ag-sq]')
const k = peanoK

const workedPred = textSource('worked by hand', [
  '-- pred(s(z)): the clause pred(s(N)) => N, priority 50',
  '--   N is z; no requires; no clause has a smaller priority',
  'Eval c pred [s(z)] (some z)',
  '',
  '-- pred(z): pred(s(N)) fails, since s(N) denotes no z',
  '--   pred(_) => z [owise], priority 200, decides',
  'Eval c pred [z] (some z)',
  '',
  '-- pred(s(z)) by the [owise] clause? Its pattern matches,',
  '--   but pred(s(N)), priority 50, does not fail there,',
  '--   so the [owise] clause does not decide: one result',
].join('\n'))

const workedPr = textSource('worked by hand', [
  'Eval c pr [0] (some 1)    -- pr-low (40) applies; nothing smaller',
  'Eval c pr [3] (some 2)    -- pr-low fails (3 is not 0); pr-def: 3 <=Int 5',
  'Eval c pr [9] (some 3)    -- pr-low fails; pr-def fails (9 <=Int 5 is false)',
  '',
  'Eval c ow [-3] (some 3)   -- ow-pos fails (-3 >Int 0 is false); [owise] decides',
  'Eval c ow [-200] none     -- both requires are false: every clause fails',
].join('\n'))

const workedRhs = textSource('worked by hand', [
  "-- the first rule's right-hand side, run(pred(s(N))), under N ↦ s(z)",
  'EvalTerm c σ (.var 0) (some s(z))                   -- var',
  'EvalTerm c σ (.app s [.var 0]) (some s(s(z)))       -- ctor',
  'EvalTerm c σ (.app pred [...]) (some s(z))          -- call: Eval c pred [s(s(z))] (some s(z))',
  'EvalTerm c σ (.app run [...]) (some run(s(z)))      -- ctor',
].join('\n'))

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

export const evaluation5: Lesson = {
  id: 'evaluation',
  number: 5,
  title: 'Evaluation',
  against: coreCommit,
  scenes: [
    {
      id: 'e1',
      title: "A function's result",
      panes: [
        { id: 'e', label: 'KcoreSpec/Evaluation.lean', source: evalDef, lang: 'lean' },
        { id: 'k', label: 'peano.k', source: k, lang: 'k' },
      ],
      frames: [
        {
          hl: { e: [at(evalDef, 'inductive Eval')], k: span(k, 'syntax Nat ::= pred', 'rule pred(_)') },
          notes: [note('e', at(evalDef, 'inductive Eval'), 'The function `f` at the arguments `vs` has the result `r`; `none` is "undefined".', 'Option GroundTerm → Prop')],
          say: 'Like matching, evaluation is a relation: it says which results a call has, not how to compute them.',
        },
      ],
    },
    {
      id: 'e2',
      title: 'A clause decides',
      panes: [
        { id: 'e', label: 'KcoreSpec/Evaluation.lean', source: evalDef, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedPred, lang: 'lean' },
      ],
      frames: [
        {
          hl: { e: [at(evalDef, '(hmem : cl ∈ fn.clauses)')] },
          notes: [note('e', at(evalDef, '(hmem : cl ∈ fn.clauses)'), 'Any clause of the function. The order of the clauses in the file means nothing.', 'cl ∈ fn.clauses')],
        },
        {
          hl: { e: [at(evalDef, '(hσ : c.WellSorted'), at(evalDef, '(hmatch : PatVals'), at(evalDef, '(hreq :')] },
          notes: [note('e', at(evalDef, '(hmatch : PatVals'), 'Its patterns denote the arguments under a well-sorted σ (lesson 4)…', 'PatVals c σ cl.pats vs'), note('e', at(evalDef, '(hreq :'), '…and its `requires`, if any, evaluates to `true`.', 'some (bool true)')],
        },
        {
          hl: { e: [at(evalDef, '(hprio :')] },
          notes: [note('e', at(evalDef, '(hprio :'), 'Every clause of a smaller priority fails.', "cl'.prio < cl.prio → Fails c vs cl'")],
        },
        {
          hl: { e: [at(evalDef, '(hrhs :')], w: span(workedPred, '-- pred(s(z)): the clause', 'Eval c pred [s(z)]') },
          notes: [note('e', at(evalDef, '(hrhs :'), 'Then the result is the value of its right-hand side.', 'EvalTerm c σ cl.rhs r')],
        },
      ],
    },
    {
      id: 'e3',
      title: '[owise] is priority 200',
      panes: [
        { id: 'f', label: 'KcoreSpec/Evaluation.lean', source: fails, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedPred, lang: 'lean' },
      ],
      frames: [
        {
          hl: { f: span(fails, 'inductive Fails', 'Fails c vs cl') },
          notes: [note('f', at(fails, '(h : ∀ σ, c.WellSorted'), 'A clause fails where every well-sorted match has a `requires` that is not `true`. With no `requires`, no σ may match.', 'ReqFails c σ cl')],
        },
        {
          hl: { f: span(fails, 'inductive ReqFails', 'ReqFails c σ cl', at(fails, 'inductive ReqFails') - 1) },
          notes: [note('f', at(fails, '(ht : cl.req = some t)'), '"Not `true`": `false`, or undefined.', 'r ≠ some (bool true)')],
        },
        {
          hl: { w: span(workedPred, '-- pred(z):', 'Eval c pred [z]') },
          notes: [note('w', at(workedPred, '--   pred(_) => z [owise]'), '`[owise]` is priority 200: it decides only where every clause of a smaller priority fails.', 'priority 200')],
          say: '`[owise]` is not "try this last". It is priority 200, and a clause of priority 200 decides only where every clause below it fails.',
        },
        {
          hl: { w: span(workedPred, '-- pred(s(z)) by the [owise]', '--   so the [owise] clause') },
          say: 'So `pred(s(z))` has one result. Swapping the two clauses in `peano.k` would change nothing.',
        },
      ],
    },
    {
      id: 'e4',
      title: 'Priorities in fprio',
      panes: [
        { id: 'k', label: 'fprio.k', source: fprioK, lang: 'k' },
        { id: 'w', label: 'Worked by hand', source: workedPr, lang: 'lean' },
      ],
      frames: [
        {
          hl: { k: span(fprioK, 'rule [pr-low]', 'rule [pr-mid]'), w: span(workedPr, 'Eval c pr [0]', 'Eval c pr [9]') },
          notes: [note('w', at(workedPr, 'Eval c pr [0]'), 'All three patterns match `0`, but `pr-low` has the smallest priority.', 'some 1')],
        },
        {
          hl: { k: span(fprioK, 'rule [ow-pos]', 'rule [ow-else]'), w: span(workedPr, 'Eval c ow [-3]', 'Eval c ow [-200]') },
          notes: [note('w', at(workedPr, 'Eval c ow [-200]'), 'No result: `ow` is undefined at -200.', 'none')],
        },
      ],
    },
    {
      id: 'e5',
      title: 'No result where every clause fails',
      panes: [
        { id: 'e', label: 'KcoreSpec/Evaluation.lean', source: evalDef, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedPr, lang: 'lean' },
      ],
      frames: [
        {
          hl: { e: span(evalDef, '| undef {f : Sym}', '(hnone :'), w: [at(workedPr, 'Eval c ow [-200]')] },
          notes: [note('e', at(evalDef, '(hnone :'), 'Where every clause fails, the result is `none`: undefined.', 'Eval c f vs none')],
          say: 'Undefined is a result too, so a `requires` that calls `ow(-200)` is not `true`, and its clause fails.',
        },
      ],
    },
    {
      id: 'e6',
      title: 'The value of a right-hand side',
      panes: [
        { id: 't', label: 'KcoreSpec/Evaluation.lean', source: evalTerm, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedRhs, lang: 'lean' },
      ],
      frames: [
        {
          hl: { t: [at(evalTerm, 'inductive EvalTerm'), at(evalTerm, '| var {σ'), ...span(evalTerm, '| ctor {σ', 'EvalTerm c σ (.app f ts) ((allSome rs).map (.ctor f))')], w: span(workedRhs, 'EvalTerm c σ (.var 0)', 'EvalTerm c σ (.app s') },
          notes: [note('t', at(evalTerm, '| var {σ'), 'A variable has the value σ gives it.', 'σ.lookup i'), note('t', at(evalTerm, 'EvalTerm c σ (.app f ts) ((allSome rs).map (.ctor f))'), 'A constructor builds its term, undefined if an argument is.', 'allSome rs')],
        },
        {
          hl: { t: span(evalTerm, '| call {σ', 'EvalTerm c σ (.app f ts) r', at(evalTerm, '| call {σ') - 1), w: span(workedRhs, 'EvalTerm c σ (.app pred', 'EvalTerm c σ (.app run') },
          notes: [note('t', at(evalTerm, '(hvs : allSome rs = some vs) (hf : Eval c f vs r)'), 'A function is called on its arguments\' values, by `Eval`.', 'Eval c f vs r')],
          say: "So the first rule's right-hand side has the value `run(s(z))`: `pred` is evaluated within the step, as the prologue's run showed.",
        },
        {
          hl: { t: span(evalTerm, '| callUndef {σ', 'EvalTerm c σ (.app f ts) none') },
          notes: [
            note('t', at(evalTerm, '| callUndef {σ'), 'A call with an undefined argument is undefined.', 'callUndef'),
            note('t', at(evalTerm, '| callUndef {σ'), 'Not settled: Bool operations are strict today; a short-circuiting reading would be a named obligation.'),
          ],
        },
        {
          hl: { t: [at(evalTerm, '| hook {σ'), at(evalTerm, '| param {σ')] },
          notes: [
            note('t', at(evalTerm, '| hook {σ'), 'Not settled: hook domains.', 'hook'),
            note('t', at(evalTerm, '| param {σ'), 'Not settled: hook domains.', 'param'),
          ],
        },
      ],
    },
    {
      id: 'e7',
      title: 'Two clauses of one priority',
      panes: [{ id: 'k', label: 'fprio.k', source: fprioK, lang: 'k' }],
      frames: [
        {
          hl: { k: span(fprioK, 'rule [ag-z]', 'rule [ag-sq]') },
          notes: [note('k', at(fprioK, 'rule [ag-sq]'), 'Both priority 50, and both apply at `0`.', 'N *Int N')],
          say: '`Eval` reads no order between them, so at `0` either one gives a result. That the two results agree is a fact about the definition, not part of the relation: lesson 7.',
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'Where does a clause marked `[owise]` decide?',
      options: ['Where it applies and every clause of a smaller priority fails, since `[owise]` is priority 200', 'After every clause above it in the file has been tried', 'Nowhere: `[owise]` clauses are ignored'],
      answer: 0,
      why: 'Priorities, not positions, order clauses. The order in the file means nothing.',
    },
    {
      q: 'What is `ow(-200)` in fprio?',
      options: ['Undefined: every clause fails, so `Eval c ow [-200] none`', '200, by the `[owise]` clause', '0'],
      answer: 0,
      why: 'Both clauses have a `requires` that is false at -200, so both fail.',
    },
  ],
  checked: [
    `The Lean in every pane is kcore-spec's text at \`${coreCommit}\`, and so is \`fprio.k\`.`,
    'The results shown are worked by hand from `Eval`, `Fails` and `EvalTerm`. Lean did not compute them.',
  ],
}
