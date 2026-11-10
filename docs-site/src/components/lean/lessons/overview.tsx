'use client'

// The overview: the running example, the map of the series, and what is checked today.

import { lineOf, peanoK, span } from '../data'
import { type Lesson, note } from '../lesson'
import { A, Arrow, Board, Box, Label, Svg } from '../viz'

const k = peanoK

const map = (at: number) => {
  const muted = 'var(--muted)'
  const ink = (n: number) => (at === n ? 'var(--ink)' : muted)
  return (
    <Svg viewBox="0 0 900 520" label="Map of the series: kompile turns peano.k into KORE; kcore gen reads the KORE into a Lean package holding the definition as a term, which prints back as the same KORE; Step, a Lean relation, says what a step of that definition is; properties of peano are proved about Step. The KORE also has a meaning of its own, a theory in matching logic; that Step agrees with it, soundness and completeness, is stated and not proved yet.">
      <A show={at >= 0}>
        <Box x={130} y={50} text="peano.k" sub="lesson 1" tone={at === 0 ? 'on' : 'plain'} />
        <Arrow x1={180} y1={50} x2={360} y2={50} label="kompile" on={at === 0} />
        <Box x={450} y={50} text="KORE" sub="lesson 1" tone={at === 0 ? 'on' : 'plain'} />
      </A>
      <A show={at >= 1}>
        <Arrow x1={420} y1={76} x2={420} y2={134} on={at === 1} />
        <Label x={410} y={109} anchor="end" text="kcore gen" tone={ink(1)} />
        <Arrow x1={480} y1={134} x2={480} y2={76} on={at === 1} dash />
        <Label x={490} y={109} text="prints back the same" tone={ink(1)} />
        <Box x={450} y={160} w={280} text="the definition" aside="Lean term" sub="lesson 2" tone={at === 1 ? 'on' : 'plain'} />
      </A>
      <A show={at >= 2}>
        <Arrow x1={500} y1={186} x2={640} y2={265} on={at === 2} />
        <Label x={590} y={222} text="read as rewrites" tone={ink(2)} />
        <Box x={690} y={295} w={250} text="Step" aside="Lean relation" sub="lesson 3" tone={at === 2 ? 'on' : 'plain'} />
        <Label x={690} y={347} anchor="middle" text="what a step is" tone={muted} />
      </A>
      <A show={at >= 3}>
        <Arrow x1={690} y1={360} x2={690} y2={426} label="used to prove" on={at === 3} />
        <Box x={690} y={456} w={250} text="properties of peano" sub="proved · lesson 4" tone={at === 3 ? 'accent' : 'plain'} />
      </A>
      <A show={at >= 4}>
        <Arrow x1={400} y1={186} x2={250} y2={265} on={at === 4} />
        <Label x={312} y={222} anchor="end" text="its own meaning" tone={ink(4)} />
        <Box x={190} y={295} w={250} text="Γ_D" aside="matching-logic theory" tone={at === 4 ? 'on' : 'plain'} />
        <Arrow x1={320} y1={295} x2={560} y2={295} on={at === 4} dash tone="var(--gold)" />
        <Arrow x1={560} y1={295} x2={320} y2={295} on={at === 4} dash tone="var(--gold)" />
        <Box x={440} y={357} w={250} text="Step is sound and complete" sub="stated, not proved yet" tone="gold" dash />
        <Label x={440} y={401} anchor="middle" text="would turn “proved about Step” into" tone={muted} />
        <Label x={440} y={418} anchor="middle" text="“proved about peano's KORE”" tone={muted} />
      </A>
    </Svg>
  )
}

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

const status = [
  {
    title: 'Checked by the kernel',
    items: [
      { key: 'peano', text: <>nine properties of peano, four of them witnesses that the others are not true for an empty reason, and a run certificate</> },
      { key: 'tie', text: <>the Lean definition is KCore's reading of peano's KORE, and prints back as that KORE up to the order of sentences</> },
      { key: 'iff', text: <><code>step_iff</code>, for every definition that passes three checks: the executable step lists exactly the step relation's successors</> },
      { key: 'kinds', text: <>determinism, and a cell every step keeps, for every definition, from one decision each</> },
      { key: 'order', text: <><code>sameModels_of_reordered</code>: reordering a module's sentences keeps the models of its theory</> },
    ],
  },
  {
    title: 'Not proved yet',
    items: [
      { key: 'sc', text: <>that <code>Step</code> is sound and complete for the KORE's matching-logic theory: stated, <code>sorry</code></> },
    ],
  },
  {
    title: 'Trusted',
    items: [
      { key: 'kernel', text: <>the Lean kernel, and Lean's <code>Init</code> library</> },
      { key: 'komp', text: <>kompile's translation of <code>peano.k</code> into KORE</> },
      { key: 'reader', text: <>the reader from a KORE file's text to its syntax tree</> },
      { key: 'read', text: <>and, to be read rather than trusted: the statements, and the definitions they are about</> },
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
    {
      id: 'o2',
      title: 'Two answers to one question',
      visual: map,
      // The map carries the explanation; each frame stays long enough to read what it adds.
      frames: [{ ms: 3200 }, { ms: 4600 }, { ms: 4200 }, { ms: 4000 }, { ms: 5600 }],
    },
    {
      id: 'o3',
      title: 'How sure we are today',
      visual: (at) => <Board columns={status} cols={3} lit={[[], ['Checked by the kernel'], ['Not proved yet'], ['Trusted']][at]} />,
      frames: [
        { say: 'The series keeps three kinds of claim apart. You should know which one you are reading at every step.' },
        { say: 'Checked by the kernel, using only the axioms `propext`, `Classical.choice` and `Quot.sound`. If any of these were wrong, a proof would fail to check.' },
        { say: 'Not proved yet. The most important one says `Step` is sound and complete for the matching-logic theory of the KORE. Until it is, a property of `Step` is a property of the KORE as Lean reads it.' },
        { say: 'And trusted, not checked. A proof of the wrong statement checks just as well, so the statements are yours to read. Ready? Lesson 1 starts from the run itself.' },
      ],
    },
  ],
}
