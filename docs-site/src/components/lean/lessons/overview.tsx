'use client'

// The overview: the running example and one run of it.

import { lineOf, peanoK, span } from '../data'
import { type Lesson, note } from '../lesson'
import { A, Arrow, Box, Label, Svg } from '../viz'

const k = peanoK

const countDown = lineOf(k, 'rule <k> run(s(N))')
const finish = lineOf(k, 'rule <k> run(z)')
const predS = lineOf(k, 'rule pred(s(N))')

// The scene "Numbers as terms": how 0, 1 and 2 are written.
const numerals = [
  { n: '0', term: 'z' },
  { n: '1', term: 's(z)' },
  { n: '2', term: 's(s(z))' },
] as const

const numberRows = (at: number) => (
  <Svg viewBox="0 0 460 300" label="0 is z, 1 is s(z), 2 is s(s(z))">
    {numerals.map((row, i) => (
      <A key={row.n} show={i <= at}>
        <Label x={130} y={70 + i * 80} anchor="end" text={row.n} size={30} weight={600} />
        <Label x={165} y={68 + i * 80} anchor="middle" text="=" size={24} tone="var(--muted)" />
        <Box x={290} y={60 + i * 80} w={180} h={44} text={row.term} size={18} tone={i === at ? 'on' : 'plain'} />
      </A>
    ))}
  </Svg>
)

// The scene "One run": one rewrite per sub-step. A rule is a step; evaluating the function it
// wrote (dashed) belongs to the same step, which the brackets on the right group.
const runTerms = [
  { term: 'run(s(s(z)))', eq: false },
  { term: 'run(pred(s(s(z))))', eq: true },
  { term: 'run(s(z))', eq: false },
  { term: 'run(pred(s(z)))', eq: true },
  { term: 'run(z)', eq: false },
  { term: 'done(z)', eq: false },
] as const
const runStepSpans = [[0, 2], [2, 4], [4, 5]] as const
const ty = (i: number) => 40 + i * 78

const oneRun = (at: number) => {
  const last = runTerms.length - 1
  const reached = Math.min(at, last)
  const running = at <= last
  return (
    <Svg viewBox="0 0 460 560" label="One run of peano: run(s(s(z))) is rewritten to run(pred(s(s(z)))), pred evaluates to give run(s(z)), and so on to done(z), where no rule applies">
      {runTerms.map((t, i) => (
        <A key={t.term} show={i <= reached}>
          {i > 0 && <Arrow x1={150} y1={ty(i - 1) + 17} x2={150} y2={ty(i) - 19} on={running && i === reached} dash={runTerms[i - 1].eq} />}
          <Box x={150} y={ty(i)} w={210} text={t.term} tone={running && i === reached ? 'on' : 'plain'} dash={t.eq} />
        </A>
      ))}
      {runStepSpans.map(([from, to], n) => (
        <A key={n} show={reached >= to}>
          <path d={`M272 ${ty(from) + 6}h8V${ty(to) - 6}h-8`} fill="none" stroke="var(--faint)" strokeWidth={1.4} />
          <Label x={290} y={(ty(from) + ty(to)) / 2 + 4} text={`step ${n + 1}`} tone="var(--muted)" size={12} />
        </A>
      ))}
      <A show={at > last}>
        <Label x={150} y={ty(last) + 50} anchor="middle" text="no rule applies: the run stops" tone="var(--bad)" weight={600} />
      </A>
      <A show={at > last + 1}>
        <Label x={150} y={ty(last) + 90} anchor="middle" text="and started on 0, 1, 3, 1000, …?" tone="var(--ink)" weight={600} />
      </A>
    </Svg>
  )
}

export const overview: Lesson = {
  id: 'overview',
  title: 'Overview: why a run is not enough',
  against: 'cb071587',
  scenes: [
    {
      id: 'o1',
      title: 'One definition, every lesson',
      panes: [{ id: 'k', label: 'The running example', source: k, lang: 'k' }],
      frames: [
        { notes: [note('k', lineOf(k, 'module PEANO'), "As the common example for this guide, we use a specification of the natural numbers in the style of the [Peano axioms](https://mathworld.wolfram.com/PeanosAxioms.html), zero and successor, for its simplicity.")] },
        { hl: { k: span(k, 'syntax Nat ::= "z"', '| s(Nat)') }, notes: [note('k', lineOf(k, 'syntax Nat ::= "z"'), "The datatype: numbers built from `z` (zero) and `s` (successor).")] },
      ],
    },
    {
      id: 'nums',
      title: 'Numbers as terms',
      panes: [{ id: 'k', label: 'The running example', source: k, lang: 'k' }],
      visual: numberRows,
      frames: [
        { hl: { k: [lineOf(k, 'syntax Nat ::= "z"')] }, notes: [note('k', lineOf(k, 'syntax Nat ::= "z"'), "zero", '"z"')] },
        { hl: { k: [lineOf(k, '| s(Nat)')] }, notes: [note('k', lineOf(k, '| s(Nat)'), "`s(n)` is one more than `n`", 's(Nat)')] },
        { hl: { k: [lineOf(k, '| s(Nat)')] }, notes: [note('k', lineOf(k, '| s(Nat)'), "applied twice to `z`: 2", 's(Nat)')] },
      ],
    },
    {
      id: 'rules',
      title: 'A function and two rules',
      panes: [{ id: 'k', label: 'The running example', source: k, lang: 'k' }],
      frames: [
        { hl: { k: span(k, 'syntax Nat ::= pred', 'rule pred(_)') }, notes: [note('k', lineOf(k, 'syntax Nat ::= pred'), "`pred` (predecessor) takes a `Nat` and returns its predecessor, also a `Nat`. It has two cases."), note('k', lineOf(k, 'rule pred(_)'), "applies when the first case does not (the base case)", 'owise')] },
        { hl: { k: [...span(k, 'syntax State', '| done(Val)'), lineOf(k, 'configuration')] }, notes: [note('k', lineOf(k, 'syntax State'), "The machine's two states: `run(n)` while it counts down, `done(v)` when it has finished."), note('k', lineOf(k, 'configuration'), "The `k` cell is the instruction tape. In this definition it holds the whole machine state.")] },
        { hl: { k: [lineOf(k, 'rule <k> run(s(N))'), lineOf(k, 'rule <k> run(z)')] }, notes: [note('k', lineOf(k, 'rule <k> run(s(N))'), "While there is an `s`, count down.", 'run(pred(s(N)))'), note('k', lineOf(k, 'rule <k> run(z)'), "At `z`, finish.", 'done(z)')] },
      ],
    },
    {
      id: 'run',
      title: 'One run',
      panes: [{ id: 'k', label: 'The running example', source: k, lang: 'k' }],
      visual: oneRun,
      frames: [
        { hl: { k: [lineOf(k, 'configuration')] }, notes: [note('k', lineOf(k, 'configuration'), "Start the machine on 2: the `k` cell holds `run(s(s(z)))`.", '$PGM:State')] },
        { hl: { k: [countDown] }, notes: [note('k', countDown, "`run(s(s(z)))` matches, with `N` = `s(z)`", 'run(s(N))'), note('k', countDown, "and is rewritten to `run(pred(s(s(z))))`", 'run(pred(s(N)))')] },
        { hl: { k: [predS] }, notes: [note('k', predS, "`pred(s(s(z)))` is `s(z)`"), note('k', lineOf(k, 'syntax Nat ::= pred'), "A function is evaluated within the step that wrote it, so this is still step 1.", 'function')] },
        { hl: { k: [countDown] }, notes: [note('k', countDown, "`run(s(z))` matches, with `N` = `z`", 'run(s(N))')] },
        { hl: { k: [predS] }, notes: [note('k', predS, "`pred(s(z))` is `z`")] },
        { hl: { k: [finish] }, notes: [note('k', finish, "`run(z)` matches", 'run(z)')] },
        { say: 'This run establishes one fact: started on 2, the machine stops at `done(z)` after three steps.' },
        { say: 'How can we prove something holds for ==every== run?' },
      ],
    },
  ],
}
