'use client'

// Core lesson 6: one step. `Step c x y`: a rule whose left side denotes x under a well-sorted σ,
// whose requires is true, whose right side has the value y, and no rule of a smaller priority
// applies to x. Every Lean pane is kcore-spec's text at the manifest's commit, as are prio.k and
// fprio.k; the steps shown are theorems of the example packages, checked by Lean.

import { type Source, checked, checkedLabel, coreCommit, coreFile, lineOf, peanoK, slice, span } from '../data'
import { type Lesson, note } from '../lesson'

const stepLean = coreFile('KcoreSpec/Step.lean')
const step = slice(stepLean, 'inductive Step (c : Semantics)', '(hprio : ∀ r')
const notApplies = slice(stepLean, '/-- `RuleReqFails c σ r`:', '  ∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x → RuleReqFails c σ r')
const prioK = coreFile('f2-examples/prio.k')
const fprioK = slice(coreFile('f2-examples/fprio.k'), 'syntax Int ::= ow(Int)', 'rule [t4]')
const k = peanoK

const workedRun = checked('step1')
const workedPrio = checked('prio')
const workedRunAll = checked('steps')

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

export const step6: Lesson = {
  id: 'step',
  number: 6,
  title: 'Step',
  against: coreCommit,
  scenes: [
    {
      id: 's1',
      title: 'One step',
      panes: [
        { id: 's', label: 'KcoreSpec/Step.lean', source: step, lang: 'lean' },
        { id: 'w', label: checkedLabel(workedRun), source: workedRun, lang: 'lean' },
      ],
      frames: [
        {
          hl: { s: [at(step, 'inductive Step'), at(step, '| rule {x y : Config c}')] },
          notes: [note('s', at(step, 'inductive Step'), 'One step from the configuration `x` to the configuration `y`.', 'Config c → Config c → Prop')],
          say: 'Everything so far comes together here: configurations (lesson 3), matching (lesson 4) and evaluation (lesson 5).',
        },
        {
          hl: { s: [at(step, '(hσ :'), at(step, '(hmatch :')], w: [...span(workedRun, '-- hσ', 'σ₁_wellSorted'), ...span(workedRun, '-- hmatch', 'match_runSSZ')] },
          notes: [note('s', at(step, '(hmatch :'), "Some rule's left side denotes `x` under a well-sorted σ.", 'PatVal c σ r.lhs x.val')],
        },
        {
          hl: { s: [at(step, '(hreq :')], w: span(workedRun, '-- hreq', 'some none') },
          notes: [note('s', at(step, '(hreq :'), 'Its `requires`, if any, evaluates to `true`.', 'some (bool true)')],
        },
        {
          hl: { s: [at(step, '(heval :')], w: span(workedRun, '-- heval', 'eval_rhs_runSSZ') },
          notes: [note('s', at(step, '(heval :'), 'Its right side has a value, and that value is `y`.', 'some y.val')],
        },
        {
          hl: { s: [at(step, '(hprio :')], w: span(workedRun, '-- hprio', 'step_runSSZ') },
          notes: [note('s', at(step, '(hprio :'), 'No rule of a smaller priority applies to `x`.', 'NotApplies c r\' x.val')],
        },
      ],
    },
    {
      id: 's2',
      title: 'No rule of a smaller priority applies',
      panes: [
        { id: 'n', label: 'KcoreSpec/Step.lean', source: notApplies, lang: 'lean' },
        { id: 'k', label: 'prio.k', source: prioK, lang: 'k' },
      ],
      frames: [
        {
          hl: { n: span(notApplies, 'def NotApplies', 'RuleReqFails c σ r') },
          notes: [note('n', at(notApplies, 'def NotApplies'), "A rule does not apply to `x` when every well-sorted match has a `requires` that is not `true`. With no `requires`, no σ may match.", 'NotApplies')],
          say: 'The same shape as a failing clause in lesson 5.',
        },
        {
          hl: { k: span(prioK, 'rule <k> go(X:D)', 'rule <k> go(X:B)') },
          notes: [note('k', at(prioK, 'rule <k> go(X:D)'), 'Priority 40: applies to `go(d)`, not to `go(b)`.', 'priority(40)')],
        },
      ],
    },
    {
      id: 's3',
      title: 'Priorities in prio',
      panes: [
        { id: 'k', label: 'prio.k', source: prioK, lang: 'k' },
        { id: 'w', label: checkedLabel(workedPrio), source: workedPrio, lang: 'lean' },
      ],
      frames: [
        {
          hl: { k: [at(prioK, 'rule <k> go(X:D)')], w: span(workedPrio, '-- go(d) steps', 'not_step_goD_otherD') },
          notes: [note('w', at(workedPrio, 'not_step_goD_otherD'), '`go(X:B)` also matches `go(d)`, but it is blocked.', 'not_step_goD_otherD')],
        },
        {
          hl: { k: [at(prioK, 'rule <k> go(X:B)')], w: span(workedPrio, '-- go(b) steps', 'step_goB') },
          notes: [note('w', at(workedPrio, 'step_goB'), 'Nothing of a smaller priority applies, so this rule steps.', 'goBcfg otherBcfg')],
        },
      ],
    },
    {
      id: 's4',
      title: 'A step has a value',
      panes: [{ id: 'k', label: 'fprio.k', source: fprioK, lang: 'k' }],
      frames: [
        {
          hl: { k: [at(fprioK, 'rule [t4]')] },
          notes: [note('k', at(fprioK, 'rule [t4]'), '`ow(-200)` is undefined (lesson 5), so this right side has no value, and no step leaves `t4`.', 'ow(-200)')],
          say: 'A rule steps only where its right side has a value. It still applies, though, so it blocks rules of larger priorities there.',
        },
      ],
    },
    {
      id: 's5',
      title: "The prologue's run, as steps",
      panes: [
        { id: 'k', label: 'peano.k', source: k, lang: 'k' },
        { id: 'w', label: checkedLabel(workedRunAll), source: workedRunAll, lang: 'lean' },
      ],
      frames: [
        {
          hl: { k: [at(k, 'rule <k> run(s(N))'), at(k, 'rule <k> run(z)')], w: span(workedRunAll, 'step_runSSZ', 'step_runZ ') },
          say: "Each line of the prologue's run is one `Step`.",
        },
        {
          hl: { w: [at(workedRunAll, 'stuck_doneZ')] },
          notes: [note('w', at(workedRunAll, 'stuck_doneZ'), 'No `Step` leaves `done(z)`: the run stops.', '¬ Step c doneZ y')],
          say: 'What a step is now has a precise meaning, for every configuration, reachable or not. Lessons 8 to 10 say why it is the meaning of the definition.',
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'In prio, what does `go(b)` step to?',
      options: ['`other(b)`: the priority-40 rule does not apply, since `b` is not a `D`', '`out(b)`', '`stop()`'],
      answer: 0,
      why: 'Only a smaller priority that applies blocks a rule. `go(X:D)` has no well-sorted match on `go(b)`.',
    },
    {
      q: 'Does a step leave fprio\'s `t4`?',
      options: ['No: the rule applies, but its right side `res(ow(-200))` has no value', 'Yes, to `res(0)`', 'Yes, to `res(200)`'],
      answer: 0,
      why: '`Step` asks for the right side to have a value, and `ow(-200)` is undefined.',
    },
  ],
  checked: [
    `The Lean in every pane is kcore-spec's text at \`${coreCommit}\`, and so are \`prio.k\` and \`fprio.k\`.`,
    `The panes headed “Checked by Lean” state peano's and prio's steps in Lean, each a theorem of their packages.`,
  ],
}
