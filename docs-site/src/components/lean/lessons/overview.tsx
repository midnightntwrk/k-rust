'use client'

// The overview: the running example, the map of the series, and what is checked today.

import { lineOf, peanoK, span } from '../data'
import { type Lesson, note } from '../lesson'
import { diffNumbers, f1Numbers, numbers } from '../numbers'
import styles from '../Course.module.css'
import { A, Arrow, Board, Box, Label, Svg } from '../viz'

const k = peanoK

const map = (at: number) => {
  const show = (n: number) => at >= n
  const muted = 'var(--muted)'
  return (
    <Svg viewBox="0 0 900 530" label="Map of the series: kompile turns peano.k into KORE, an intermediate representation; KORE is read into Lean as a value, the definition D, and printed back it is kompile's text; from that value, Γ_D, the theory of D, translates the axioms into matching logic and says what counts as a step, and Step reads the rules as rewrites and says how a step happens; Step is used to prove properties, case by case; the two are equivalent because Step is sound and complete">
      <A show={show(0)}>
        <Box x={130} y={50} text="peano.k" sub="lesson 1" tone={at === 0 ? 'on' : 'plain'} />
        <Arrow x1={180} y1={50} x2={316} y2={50} label="kompile to IR" on={at === 0} />
        <Box x={450} y={50} text="KORE" aside="intermediate representation" sub="lesson 1" tone={at === 0 ? 'on' : 'plain'} />
      </A>
      <A show={show(1)}>
        <Arrow x1={420} y1={76} x2={420} y2={134} on={at === 1} />
        <Label x={410} y={109} anchor="end" text="read into Lean" tone={at === 1 ? 'var(--ink)' : muted} />
        <Arrow x1={480} y1={134} x2={480} y2={76} on={at === 1} dash />
        <Label x={490} y={109} text="printed back" tone={at === 1 ? 'var(--ink)' : muted} />
        <Box x={450} y={160} w={260} text="the definition D" aside="Lean value" sub="lesson 3" tone={at === 1 ? 'on' : 'plain'} />
      </A>
      <A show={show(2)}>
        <Arrow x1={400} y1={186} x2={250} y2={265} on={at === 2} />
        <Label x={312} y={222} anchor="end" text="axioms translated into matching logic" tone={at === 2 ? 'var(--ink)' : muted} />
        <Box x={190} y={295} w={250} text="Γ_D" aside="theory of D" sub="K's own meaning · lesson 2" tone={at === 2 ? 'on' : 'plain'} />
        <Label x={190} y={347} anchor="middle" text="what counts as a step:" tone={muted} />
        <Label x={190} y={365} anchor="middle" text="what the axioms entail" tone={muted} />
      </A>
      <A show={show(3)}>
        <Arrow x1={500} y1={186} x2={630} y2={265} on={at === 3} />
        <Label x={578} y={222} text="rules read as rewrites" tone={at === 3 ? 'var(--ink)' : muted} />
        <Box x={690} y={295} w={250} text="Step" aside="Lean relation" sub="lesson 4" tone={at === 3 ? 'on' : 'plain'} />
        <Label x={690} y={347} anchor="middle" text="how a step happens:" tone={muted} />
        <Label x={690} y={365} anchor="middle" text="a rule matches and rewrites" tone={muted} />
      </A>
      <A show={show(4)}>
        <Arrow x1={690} y1={378} x2={690} y2={436} label="used to prove, case by case" on={at === 4} />
        <Box x={690} y={466} w={250} text="properties of peano" sub="proved · lesson 5 · cheap · lesson 7" tone={at === 4 ? 'accent' : 'plain'} />
        <Label x={690} y={514} anchor="middle" text="what humans have to read · lesson 6" tone={at === 4 ? 'var(--ink)' : muted} />
      </A>
      <A show={show(5)}>
        <Arrow x1={320} y1={295} x2={560} y2={295} on={at === 5} dash tone="var(--gold)" />
        <Arrow x1={560} y1={295} x2={320} y2={295} on={at === 5} dash tone="var(--gold)" />
        <Label x={440} y={285} anchor="middle" text="equivalent" tone={at === 5 ? 'var(--ink)' : muted} />
        <Box x={440} y={357} w={230} text="Step is sound and complete" sub="lesson 8" tone="gold" dash />
        <Label x={440} y={401} anchor="middle" text="turns “proved about Step” into" tone={muted} />
        <Label x={440} y={418} anchor="middle" text="“proved about peano.k”" tone={muted} />
      </A>
    </Svg>
  )
}

// The scene "Fragments of K": the fragments, as nested regions of all K
// definitions; each region names what it adds.
const ring = (on: boolean, fill: string) => ({ fill, stroke: on ? 'var(--gold)' : 'var(--line)', strokeWidth: on ? 2 : 1.2 })
const Dot = ({ x, y, text, sub }: { x: number; y: number; text: string; sub: string }) => (
  <g>
    <circle cx={x} cy={y} r={6} style={{ fill: 'var(--ink)' }} />
    <Label x={x + 14} y={y + 4} text={text} isMono weight={500} size={13} />
    <Label x={x + 14} y={y + 21} text={sub} tone="var(--muted)" size={11} />
  </g>
)

const Heading = ({ x, y, name, short }: { x: number; y: number; name: string; short: string }) => (
  <text x={x} y={y} fontSize={14} fontWeight={600}>
    {name}
    <tspan fontSize={12.5} fontWeight={400} style={{ fill: 'var(--muted)' }}>{` (${short})`}</tspan>
  </text>
)

const fragments = (at: number) => {
  const muted = 'var(--muted)'
  const ink = (n: number) => (at === n ? 'var(--ink)' : muted)
  return (
    <Svg viewBox="0 0 900 470" label="Fragments: all K definitions contain the builtin fragment, F1, which contains the constructor fragment, F0. In logic, a fragment is a subset of a language; the Lean package covers K one fragment at a time. The constructor fragment has terms built from constructors and functions defined by cases; peano.k is in it. The builtin fragment adds several cells, side conditions, and Int, Bool and Map, whose operations are internally hooks into the K backend; store.k is in it.">
      <rect x={20} y={14} width={860} height={444} rx={14} {...ring(at === 0, 'transparent')} className={styles.anim} />
      <Label x={40} y={42} text="all K definitions" weight={600} size={14} />
      <Label x={650} y={80} text="In logic, a fragment is" tone={ink(0)} />
      <Label x={650} y={98} text="a subset of a language." tone={ink(0)} />
      <Label x={650} y={130} text="The Lean package covers K" tone={ink(0)} />
      <Label x={650} y={148} text="one fragment at a time." tone={ink(0)} />
      <A show={at >= 2}>
        <rect x={44} y={60} width={584} height={380} rx={12} {...ring(at === 2, 'var(--alt-tint)')} className={styles.anim} />
        <Heading x={64} y={88} name="builtin fragment" short="F₁" />
        <Label x={64} y={110} text="adds several cells, side conditions, and Int, Bool and Map." tone={ink(2)} />
        <Label x={64} y={128} text="Internally, their operations are hooks into the K backend." tone={ink(2)} />
        <Dot x={84} y={400} text="store.k" sub="lesson 9" />
      </A>
      <A show={at >= 1}>
        <rect x={68} y={168} width={536} height={190} rx={10} {...ring(at === 1, 'var(--accent-tint)')} className={styles.anim} />
        <Heading x={88} y={196} name="constructor fragment" short="F₀" />
        <Label x={88} y={218} text="terms built from constructors, and functions" tone={ink(1)} />
        <Label x={88} y={236} text="defined by cases over them" tone={ink(1)} />
        <Dot x={108} y={290} text="peano.k" sub="lessons 1 to 8" />
      </A>
    </Svg>
  )
}

// The scene "A fragment per language": past the builtin fragment, each language needs its own
// features, so fragments branch. The package's next one is IMP's; another language's is drawn
// only as an outline, since what it adds depends on the language.
const perLanguage = (at: number) => {
  const muted = 'var(--muted)'
  const ink = (n: number) => (at === n ? 'var(--ink)' : muted)
  return (
    <Svg viewBox="0 0 900 420" label="A fragment per language: inside all K definitions, the builtin fragment F1 is shared. The IMP fragment, F2, adds what IMP needs: subsort chains, rule priorities, strict, sets and token sorts. Another language's fragment adds the features that language uses. A language uses only some of K's features, so it lies in the fragment they cut out.">
      <rect x={20} y={14} width={860} height={392} rx={14} {...ring(false, 'transparent')} />
      <Label x={40} y={42} text="all K definitions" weight={600} size={14} />
      <Label x={860} y={42} anchor="end" text="A language uses only some of K's features," tone={ink(0)} />
      <Label x={860} y={60} anchor="end" text="so it lies in the fragment those features cut out." tone={ink(0)} />
      <A show={at >= 2}>
        <rect x={290} y={110} width={566} height={272} rx={12} {...ring(at === 2, 'color-mix(in srgb, var(--gold-tint) 60%, transparent)')} strokeDasharray="6 4" className={styles.anim} />
        <Label x={836} y={138} anchor="end" text="another language's fragment" weight={600} size={14} />
        <Label x={836} y={160} anchor="end" text="adds the features" tone={ink(2)} />
        <Label x={836} y={178} anchor="end" text="that language uses" tone={ink(2)} />
      </A>
      <A show={at >= 1}>
        <rect x={44} y={80} width={590} height={302} rx={12} {...ring(at === 1, 'color-mix(in srgb, var(--accent-tint) 70%, transparent)')} className={styles.anim} />
        <Heading x={64} y={108} name="IMP fragment" short="F₂" />
        <Label x={64} y={130} text="adds what IMP needs:" tone={ink(1)} />
        <Label x={64} y={148} text="subsort chains, rule priorities," tone={ink(1)} />
        <Label x={64} y={166} text="strict, sets and token sorts" tone={ink(1)} />
        <Dot x={74} y={290} text="IMP" sub="lesson 10" />
      </A>
      <rect x={316} y={196} width={290} height={162} rx={10} {...ring(at === 0, 'var(--alt-tint)')} className={styles.anim} />
      <Heading x={334} y={224} name="builtin fragment" short="F₁" />
      <Label x={334} y={246} text="shared by every path" tone={ink(0)} />
      <Dot x={348} y={280} text="peano.k" sub="in F₀ ⊂ F₁" />
      <Dot x={348} y={320} text="store.k" sub="lesson 9" />
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
      { key: 'peano', text: <>five properties of peano and four witnesses that they are not true for an empty reason</> },
      { key: 'iff', text: <><code>step_iff</code>: the executable step lists exactly the successors of the step relation</> },
      { key: 'kore', text: <>the KORE the Lean data generates is kompile's KORE for <code>peano.k</code>, and {numbers.f0Rejections} bad texts are rejected</> },
      { key: 'order', text: <><code>reordered_sameModels</code>: reordering a module's sentences keeps the models of its theory</> },
      { key: 'sr', text: <>subject reduction, in both fragments: a rule applied to a configuration gives a configuration</> },
      { key: 'f1', text: <>for the builtin fragment: its <code>step_iff</code>, <code>step_ofF0</code>, <code>hooksApart</code>, and peano's KORE and nine properties</> },
    ],
  },
  {
    title: 'Evidence, not proof',
    items: [
      { key: 'diff', text: <>the executable step agrees with krust on {diffNumbers.configs} configurations of {diffNumbers.subjects} definitions, {diffNumbers.differences} differences</> },
      { key: 'ref', text: <>and with the reference K backend on a sample of {diffNumbers.refSampled}</> },
      { key: 'f1diff', text: <>the builtin fragment's step agrees with krust on {f1Numbers.configs} configurations of {f1Numbers.subjects} definitions, {f1Numbers.differences} differences, and with the reference on {f1Numbers.refAgree} of {f1Numbers.refSampled} sampled</> },
      { key: 'kompile', text: <>the reference kompile and krust's give the same step for peano</> },
    ],
  },
  {
    title: 'Not proved yet',
    items: [
      { key: 'a', text: <>that <code>Step</code> is sound and complete for Γ<sub>D</sub>, in both fragments: stated, <code>sorry</code></> },
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
      frames: [{ ms: 3200 }, { ms: 4600 }, { ms: 4200 }, { ms: 4200 }, { ms: 4000 }, { ms: 5200 }],
    },
    {
      id: 'fragments',
      title: 'Fragments of K',
      visual: fragments,
      frames: [{ ms: 4200 }, { ms: 4200 }, { ms: 4600 }],
    },
    {
      id: 'per-language',
      title: 'A fragment per language',
      visual: perLanguage,
      frames: [{ ms: 4200 }, { ms: 4600 }, { ms: 4600 }],
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
