'use client'

// Lesson 7: what may change and what may not, the judge that decides, its negative tests, the
// unattended loop run's iterations, and how the cost grows with a definition's size before and
// after. Every number is read from the run's committed records: the iteration log and each judged
// run's summary, the judge's negative-test output, the growth table.

import { fmt, lean, lineOf, span } from '../data'
import { type Frame, type Lesson, note } from '../lesson'
import { loopNumbers } from '../numbers'
import { Bar, Board, Legend, Rows, Small } from '../viz'

const loop = lean.loop
const judge = loop.judgeHeader
const base = loop.log[0]
const last = loop.log.filter((it) => it.verdict === 'retained').at(-1)!
if (!base || !last || loop.recheck.total_kHb !== last.total_kHb) throw new Error('lean lessons: the recheck of the final state does not match the last retained run')

const layers = [
  {
    title: 'Frozen: read by a person',
    items: [
      { key: 'f1', text: 'the statements (lesson 5)' },
      { key: 'f2', text: 'the definitions they use: Step, Eval, the data (lesson 4)' },
      { key: 'f3', text: 'the judge itself' },
    ],
  },
  {
    title: 'Checked: by the kernel',
    items: [
      { key: 'c1', text: 'proofs' },
      { key: 'c2', text: 'lemmas and tactics' },
      { key: 'c3', text: 'how facts are grouped into decisions' },
      { key: 'c4', text: 'which files hold what' },
    ],
  },
]
const layerLit: string[][] = [[], ['Frozen: read by a person'], ['Checked: by the kernel'], ['f3'], [], [], [], []]

const log = loop.log
const rejected = log.filter((l) => l.verdict === 'rejected')
const logMax = Math.log10(base.total_kHb)
const logMin = Math.log10(Math.min(...log.map((l) => l.total_kHb))) - 0.3
const logWidth = (kHb: number) => ((Math.log10(kHb) - logMin) / (logMax - logMin)) * 100

const runFrames: (Frame & { at: number })[] = [
  { say: "An agent was given the judge, the " + loop.targets + " target statements of peano and of two synthetic definitions, and the proofs as they stood. It was told how to run the judge and nothing else, and was instructed not to read earlier attempts.", at: 0 },
  { say: "Starting point: " + fmt(base.total_kHb) + " thousand heartbeats in all.", at: 0 },
  { say: "First change: the counter invariant from one generic lemma and a check on each rule, instead of one proof case per rule.", at: 1 },
  { say: "Second: determinism from distinct constructors (no comparison of rule pairs), witnesses from a computed step, and every fact about a definition in one kernel decision.", at: 2 },
  {
    say: "Third: the other invariant from generic lemmas too. The per-rule tactic was no longer needed and was deleted.",
    at: 3,
    ask: {
      q: "The loop deleted the tactic of the earlier proofs. Could that weaken anything?",
      options: ["Yes, the statements relied on it", "No: the tactic was in the checked layer and only produced proofs", "Only if the tests were skipped"],
      answer: 1,
      why: "The statements it proved are frozen, and the judge checked that the new proofs prove them.",
    },
  },
  { say: "Not every attempt helps. One import made Lean's simplifier slower everywhere, the total went up, and the judge's rule rejected the change.", at: log.indexOf(rejected[0]) },
  { say: "The rest are smaller: lemmas written so the kernel reduces them directly, facts of all definitions in one decision, shorter proofs.", at: log.length - 2 },
  { say: "Final: " + fmt(last.total_kHb) + " thousand heartbeats, ==" + Math.round(base.total_kHb / last.total_kHb) + " times less==, every state accepted by the judge. Rerunning the judge on the final state gave the same total.", at: log.length - 1 },
  { say: "The agent ran " + loopNumbers.iterations + " iterations, and " + loopNumbers.rejected + " was rejected because the total went up. It stopped when what remained was mostly the kernel evaluating the frozen definitions themselves: string comparisons inside lookups by name, which no change of proof can remove.", at: log.length - 1 },
  { say: "The proofs it produced for peano are the ones in the package now, the ones you saw in lesson 5. There, with peano's facts in their own kernel decision, the whole proof file costs " + loopNumbers.peanoFile + " thousand heartbeats.", at: log.length - 1 },
]

const runViz = (i: number) => {
  const focus = runFrames[i].at
  const it = log[focus]
  return (
    <>
      <Rows
        head={['run', { text: 'total kHb', num: true }, 'verdict', { text: 'log scale', bar: true }]}
        rows={log.map((l, k) => ({
          key: l.run,
          state: k === focus ? 'cur' : k > focus ? 'faded' : undefined,
          cells: [<span key="r" style={{ whiteSpace: 'nowrap' }}>{l.run}</span>, fmt(l.total_kHb), l.verdict, <Bar key="b" pct={logWidth(l.total_kHb)} variant={l.verdict === 'rejected' ? 'bad' : undefined} title={`${l.run}: ${fmt(l.total_kHb)} kHb`} />],
        }))}
      />
      <p style={{ margin: '8px 0 0' }}><Small><code>{it.run}</code>: {it.change}</Small></p>
    </>
  )
}

const growth = loop.growth
const growthMax = Math.max(...growth.map((r) => r.before ?? 0))
const growthViz = (at: number) => (
  <>
    <Legend items={[{ color: 'var(--chart-a)', text: 'before' }, { color: 'var(--chart-b)', text: 'after' }]} />
    <Rows
      head={[{ text: 'N', num: true }, { text: 'before, kHb', num: true }, { text: 'after, kHb', num: true }, { text: '', bar: true }]}
      rows={growth.map((r) => ({
        key: String(r.n),
        cells: [
          r.n,
          r.before === null ? 'out of memory' : fmt(r.before),
          fmt(r.after),
          <div key="b">
            <div style={{ opacity: at === 2 ? 0.25 : 1 }}><Bar pct={((r.before ?? growthMax) / growthMax) * 100} variant="alt" dim={r.before === null} title={r.before === null ? `N=${r.n}: out of memory` : `N=${r.n}: ${fmt(r.before)} kHb before`} /></div>
            <div style={{ opacity: at === 1 ? 0.25 : 1, marginTop: 2 }}><Bar pct={(r.after / growthMax) * 100} title={`N=${r.n}: ${fmt(r.after)} kHb after`} /></div>
          </div>,
        ],
      }))}
    />
  </>
)

const userSteps = [
  {
    title: 'What you run',
    items: [
      { key: 'u1', text: <>1. write and review the statements (lesson 6 says what to read), and freeze them with the judge's hash list</> },
      { key: 'u2', text: <>2. give the judge the targets, one line per theorem: its name and the name of the statement it must prove</> },
      { key: 'u3', text: <>3. edit the editable modules, run the judge, keep the change if it passes and the total goes down, restore otherwise</> },
    ],
  },
]

export const lesson7: Lesson = {
  id: 'making-proofs-cheap',
  number: 7,
  title: 'Making proofs cheap',
  scenes: [
    {
      id: 'c1',
      title: 'What may change, and who decides',
      visual: (at) => <Board columns={layers} lit={layerLit[at]} />,
      arrange: 'top',
      panes: [{ id: 'j', label: 'The judge', source: judge, lang: 'none' }],
      frames: [
        { say: "Lesson 5's proofs aren't the first ones written for these statements. Over all the statements of the run below, the first proofs cost about " + loopNumbers.ratio + " times more. A proof's cost is not part of what it proves. Two proofs of one statement are interchangeable, so the cheaper one can replace the other ==with no review==." },
        { say: "So the package has two layers. The frozen layer is what a reader reviews: statements and the definitions they use. Nothing may change it." },
        { say: "The checked layer is everything the kernel checks instead of a reader: proofs, lemmas, tactics. Anything may change there, if the kernel still accepts the frozen statements." },
        {
          hl: { j: span(judge, '# 1. protected files unchanged', '# 5. cost: k2l-eval') },
          say: "\"The kernel still accepts\" is made mechanical by a ==judge==, a script that is itself frozen. It runs five checks.",
          ask: {
            q: "Why freeze the judge too?",
            options: ["To keep it fast", "A loop that could edit the judge could make any change pass", "So it's easy to review"],
            answer: 1,
            why: "With the judge frozen, the only way to pass is a proof the kernel accepts.",
          },
        },
        { hl: { j: [lineOf(judge, '# 1. protected files unchanged')] }, notes: [note('j', lineOf(judge, '# 1. protected files unchanged'), "First: the judge, the frozen layer's compiled files and the definitions are unchanged, by hash.")] },
        { hl: { j: [lineOf(judge, '# 2. no forbidden construct')] }, notes: [note('j', lineOf(judge, '# 2. no forbidden construct'), "Second: a scan for constructs that bypass the kernel: `sorry`, `native_decide`, `implemented_by`, declarations added without checking.")] },
        { hl: { j: span(judge, '# 4. judge/Judge.lean', '#    statement, axioms among') }, notes: [note('j', lineOf(judge, '# 4. judge/Judge.lean'), "Fourth: every new declaration is replayed through the kernel, each target's type is compared with its frozen statement, and only three axioms are allowed.")] },
        { hl: { j: [lineOf(judge, '# 5. cost: k2l-eval')] }, notes: [note('j', lineOf(judge, '# 5. cost: k2l-eval'), "Fifth: the cost, in heartbeats per declaration, which don't depend on the machine's speed.")], say: "A change is kept only if the judge passes and the total goes down." },
      ],
    },
    {
      id: 'c2',
      title: 'Changes the judge must reject',
      visual: (at) => (
        <Rows
          head={['bad change', 'checked by', 'what the judge said']}
          rows={loop.negative.map((n) => ({
            key: n.case,
            state: at === 1 ? (n.via === 'judge' ? 'cur' : 'faded') : at === 2 ? (n.via !== 'judge' ? 'cur' : 'faded') : undefined,
            cells: [<span key="c" style={{ fontFamily: 'var(--f-sans)' }}>{n.case}</span>, <span key="v" style={{ fontFamily: 'var(--f-sans)' }}>{n.via === 'judge' ? 'the whole judge' : 'kernel replay alone'}</span>, n.result.length > 140 ? `${n.result.slice(0, 139)}…` : n.result],
          }))}
        />
      ),
      frames: [
        { say: "The judge was tested with " + loop.negative.length + " deliberately bad changes, on the proofs of an earlier run driven by hand, before the unattended run used it. Each must be rejected." },
        { say: "Through the whole judge: a `sorry`, a different theorem under a target's name, an edit of a protected file, a `native_decide`, and importing the existing compiled proofs, which would hide their cost." },
        {
          say: "With the text scan bypassed, the kernel-replay program alone still rejects the three that matter most: a theorem added without kernel checking, a proof through `native_decide`, and a proof by `sorry`.",
          ask: {
            q: "Why test `native_decide` twice?",
            options: ["It's flaky", "Once through the text scan and once with the scan bypassed, to show a construct the scan missed would be caught by the axiom check", "It's the most common mistake"],
            answer: 1,
            why: "`native_decide` adds an axiom of its own, so the axiom check sees it either way.",
          },
        },
        { say: "All " + loop.negative.length + " are rejected, each with the reason shown. The unattended run then used the same judge, with only the path to its cost tool changed." },
      ],
    },
    {
      id: 'c3',
      title: 'The unattended run, iteration by iteration',
      visual: runViz,
      frames: runFrames,
    },
    {
      id: 'c4',
      title: 'Cost against the size of a definition',
      visual: growthViz,
      frames: [
        { say: "A cost that's fine for peano can be impossible for a large definition. The synthetic family has N constructors and N rules. Here are its proofs' costs before and after an earlier, hand-driven run of the same kind." },
        { say: "Before, the cost grew with the ==square of N==: the determinism check compared every pair of rules, and the invariant's tactic searched each rule's heads. At the largest size it ran out of memory." },
        { say: "After, the cost grows ==in proportion to N==, and the largest size is checked." },
      ],
    },
    {
      id: 'c5',
      title: 'What you run',
      visual: (at) => <Board big columns={userSteps} cols={1} lit={[['u1'], ['u2'], ['u3'], []][at]} />,
      frames: [
        { say: "For a user of the package this is the second half of the work. The judge is generic: it takes a list of target theorems and the frozen statements they must prove, and treats one set of modules as editable. Start by writing and reviewing your statements." },
        { say: "Give the judge the targets." },
        { say: "Then loop: edit, run the judge, keep or restore." },
        { say: "The judge's verdict is the only feedback the loop needs, and its records are the evidence: a log line per iteration and a summary per judged run. Nobody has to watch, because nothing the loop can do changes what is proved." },
      ],
    },
  ],
  quiz: [
    {
      q: "Why heartbeats rather than seconds?",
      options: ["They are more precise on fast machines", "Seconds depend on the machine and its load; heartbeats count the work, so two runs of the same file give the same number", "Lean has no timer"],
      answer: 1,
      why: "So even a small gain is visible.",
    },
    {
      q: "Why does the run's bar chart use a logarithmic scale?",
      options: ["To make the gain look bigger", "The total fell by nearly two orders of magnitude; on a linear scale every bar after the second would look the same", "Heartbeats are logarithmic"],
      answer: 1,
      why: "Read the numbers beside the bars for the actual values.",
    },
    {
      q: "Why does the growth matter more than the totals?",
      options: ["Totals vary by machine", "Real definitions are much larger than peano, and a cost that grows with the square of the number of rules is what makes a large definition impossible, whatever the constant", "It doesn't"],
      answer: 1,
      why: "That's what the synthetic family measures.",
    },
  ],
  checked: [
    "Every state the run kept passed the judge: kernel replay of every new declaration, each target's type equal to its frozen statement, axioms `propext`, `Classical.choice` and `Quot.sound` only. The final state was judged again afterwards, by a separate session, with the same total.",
    "The " + loopNumbers.negative + " rejections were produced by the same judge, on the earlier hand-driven run's proofs, and recorded before the unattended run.",
    "Not checked: that the agent followed the instruction not to read earlier attempts. Nothing enforced it, and nothing depends on it: the judge accepts a proof for what it proves, wherever it came from.",
    "The growth table is from an earlier run of the same kind, driven by hand, with the same judge.",
  ],
  tryit: [
    { say: "In the loop's package, with the frozen layer built:", cmd: "judge/run.sh mystate          # JUDGE PASS or JUDGE FAIL: reason, and the total\ncat runs/mystate/summary.json # the cost per group of targets" },
  ],
}
