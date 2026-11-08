'use client'

// The overview: the running example, the map of the series, and what is checked today.

import { lineOf, peanoK, span } from '../data'
import { type Lesson, note } from '../lesson'
import { diffNumbers, f1Numbers, numbers } from '../numbers'
import { A, Arrow, Board, Box, Label, Svg } from '../viz'

const k = peanoK

const map = (at: number) => {
  const show = (n: number) => at >= n
  const muted = 'var(--muted)'
  return (
    <Svg viewBox="0 0 900 450" label="Map of the series: kompile turns peano.k into KORE, an intermediate representation; KORE has an official meaning in matching logic and a computable one, the Lean relation Step, which is used to prove properties; the two meanings are equivalent if Step is sound and complete">
      <A show={show(0)}>
        <Box x={120} y={60} text="peano.k" sub="lesson 1" tone={at === 0 ? 'on' : 'plain'} />
        <Arrow x1={170} y1={60} x2={320} y2={60} label="kompile" on={at === 0} />
        <Box x={430} y={60} w={210} text="KORE" sub="intermediate representation · lesson 1" tone={at === 0 ? 'on' : 'plain'} />
      </A>
      <A show={show(1)}>
        <Arrow x1={400} y1={86} x2={250} y2={190} on={at === 1} />
        <Label x={296} y={140} anchor="end" text="official meaning" tone={at === 1 ? 'var(--ink)' : muted} />
        <Box x={190} y={220} w={250} text="Γ_D, matching logic" sub="K's own meaning · lesson 2" tone={at === 1 ? 'on' : 'plain'} />
        <Label x={190} y={272} anchor="middle" text="a step is what holds in every model" tone={muted} />
        <Label x={190} y={290} anchor="middle" text="nothing to compute with" tone={muted} />
      </A>
      <A show={show(2)}>
        <Arrow x1={460} y1={86} x2={630} y2={190} on={at === 2} />
        <Label x={574} y={128} text="computable meaning" tone={at === 2 ? 'var(--ink)' : muted} />
        <Label x={574} y={145} text="read into Lean, round trip checked · lesson 3" tone={muted} />
        <Box x={690} y={220} w={250} text="Step, a Lean relation" sub="lesson 4" tone={at === 2 ? 'on' : 'plain'} />
      </A>
      <A show={show(3)}>
        <Arrow x1={690} y1={246} x2={690} y2={330} label="used to prove" on={at === 3} />
        <Box x={690} y={360} w={250} text="properties of peano" sub="proved · lesson 5 · cheap · lesson 7" tone={at === 3 ? 'accent' : 'plain'} />
        <Label x={690} y={408} anchor="middle" text="what humans have to read · lesson 6" tone={at === 3 ? 'var(--ink)' : muted} />
      </A>
      <A show={show(4)}>
        <Arrow x1={320} y1={220} x2={560} y2={220} on={at === 4} dash tone="var(--gold)" />
        <Arrow x1={560} y1={220} x2={320} y2={220} on={at === 4} dash tone="var(--gold)" />
        <Label x={440} y={210} anchor="middle" text="equivalent" tone={at === 4 ? 'var(--ink)' : muted} />
        <Box x={440} y={282} w={230} text="Step is sound and complete" sub="stated, not proved · lesson 8" tone="gold" dash />
        <Label x={440} y={326} anchor="middle" text="turns “proved about Step” into" tone={muted} />
        <Label x={440} y={343} anchor="middle" text="“proved about peano.k”" tone={muted} />
      </A>
      <A show={show(5)}>
        <Box x={190} y={390} w={250} text="F1: cells, numbers, maps" sub="the second fragment · lesson 9" tone={at === 5 ? 'on' : 'plain'} />
      </A>
    </Svg>
  )
}

const status = [
  {
    title: 'Checked by the kernel',
    items: [
      { key: 'peano', text: <>five properties of peano and four witnesses that they are not true for an empty reason</> },
      { key: 'iff', text: <><code>step_iff</code>: the executable step lists exactly the successors of the step relation</> },
      { key: 'kore', text: <>the KORE the Lean data generates is kompile's KORE for <code>peano.k</code>, and {numbers.f0Rejections} bad texts are rejected</> },
      { key: 'order', text: <><code>reordered_sameModels</code>: reordering a module's sentences keeps the models of its theory</> },
      { key: 'sr', text: <>subject reduction, in F0 and F1: a rule applied to a configuration gives a configuration</> },
      { key: 'f1', text: <>for the second fragment, F1: its <code>step_iff</code>, <code>step_ofF0</code>, <code>hooksApart</code>, and peano's KORE and nine properties</> },
    ],
  },
  {
    title: 'Evidence, not proof',
    items: [
      { key: 'diff', text: <>the executable step agrees with krust on {diffNumbers.configs} configurations of {diffNumbers.subjects} definitions, {diffNumbers.differences} differences</> },
      { key: 'ref', text: <>and with the reference K backend on a sample of {diffNumbers.refSampled}</> },
      { key: 'f1diff', text: <>F1's step agrees with krust on {f1Numbers.configs} configurations of {f1Numbers.subjects} definitions, {f1Numbers.differences} differences, and with the reference on {f1Numbers.refAgree} of {f1Numbers.refSampled} sampled</> },
      { key: 'kompile', text: <>the reference kompile and krust's give the same step for peano</> },
    ],
  },
  {
    title: 'Not proved yet',
    items: [
      { key: 'a', text: <>that <code>Step</code> is sound and complete for Γ_D, in F0 and F1: stated, <code>sorry</code></> },
      { key: 'ml', text: <>the matching-logic statements about peano's own steps: stated, <code>sorry</code></> },
      { key: 'other', text: <>in this package, a property over all configurations of a definition other than <code>peano.k</code></> },
    ],
  },
  {
    title: 'Trusted',
    items: [
      { key: 'kernel', text: <>the Lean kernel, and Lean's <code>Init</code> library</> },
      { key: 'komp', text: <>kompile's translation of <code>peano.k</code> into KORE</> },
      { key: 'reader', text: <>the KORE reader, and the tool that lists what the statements depend on</> },
    ],
  },
]

export const overview: Lesson = {
  id: 'overview',
  title: 'Overview: why a run is not enough',
  scenes: [
    {
      id: 'o1',
      title: 'One definition, every lesson',
      panes: [{ id: 'k', label: 'The running example', source: k, lang: 'k' }],
      frames: [
        { notes: [note('k', lineOf(k, 'module PEANO'), "You wrote a K definition and ran a program with it. Every lesson follows this one: a datatype, a function, and rules that rewrite a machine state.")] },
        { hl: { k: span(k, 'syntax Nat ::= "z"', '| s(Nat)') }, notes: [note('k', lineOf(k, 'syntax Nat ::= "z"'), "The datatype: numbers built from `z` (zero) and `s` (successor).")] },
        { hl: { k: span(k, 'syntax Nat ::= pred', 'rule pred(_)') }, notes: [note('k', lineOf(k, 'syntax Nat ::= pred'), "`pred` (predecessor) takes a `Nat` and returns its predecessor, also a `Nat`. It has two cases."), note('k', lineOf(k, 'rule pred(_)'), "applies when the first case does not (the base case)", 'owise')] },
        { hl: { k: [...span(k, 'syntax State', '| done(Val)'), lineOf(k, 'configuration')] }, notes: [note('k', lineOf(k, 'syntax State'), "The machine's two states: `run(n)` while it counts down, `done(v)` when it has finished."), note('k', lineOf(k, 'configuration'), "The `k` cell is the instruction tape. In this definition it holds the whole machine state.")] },
        { hl: { k: [lineOf(k, 'rule <k> run(s(N))'), lineOf(k, 'rule <k> run(z)')] }, notes: [note('k', lineOf(k, 'rule <k> run(s(N))'), "While there is an `s`, count down.", 'run(pred(s(N)))'), note('k', lineOf(k, 'rule <k> run(z)'), "At `z`, finish.", 'done(z)')] },
        { say: 'A run shows you one path. "A configuration has at most one successor" speaks about ==every configuration==, and no run can establish it. A proof can, but it needs a precise meaning of "a step" that a proof checker can work with.' },
      ],
    },
    {
      id: 'o2',
      title: 'Two answers to one question',
      visual: map,
      // The map carries the explanation; each frame stays long enough to read what it adds.
      frames: [{ ms: 3200 }, { ms: 4200 }, { ms: 4600 }, { ms: 4000 }, { ms: 5200 }, { ms: 3200 }],
    },
    {
      id: 'o3',
      title: 'How sure we are today',
      visual: (at) => <Board big columns={status} cols={2} lit={[[], ['Checked by the kernel'], ['Evidence, not proof'], ['Not proved yet'], ['Trusted']][at]} />,
      frames: [
        { say: 'The series keeps four kinds of claim apart. You should know which one you are reading at every step.' },
        { say: 'Checked by the kernel, using only the axioms `propext`, `Classical.choice` and `Quot.sound`. If any of these were wrong, a proof would fail to check.' },
        { say: 'Evidence: independent implementations agree on everything tried. That makes a shared mistake less likely, and it is not a proof.' },
        { say: 'Not proved yet. The most important one says `Step` is sound and complete for the matching-logic theory. The generic theorems hold for every definition, but in this package `peano.k` is the only definition with properties proved over all its configurations.' },
        { say: 'And trusted, not checked. Lesson 6 goes through each one. Ready? Lesson 1 starts from the run itself.' },
      ],
    },
  ],
}
