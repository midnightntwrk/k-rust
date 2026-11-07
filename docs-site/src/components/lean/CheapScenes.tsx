'use client'

// Lesson "Making proofs cheap": what may change and what may not, the judge that decides, its
// negative tests, the unattended loop run's iterations, and how the cost grows with a definition's
// size before and after. Every number is read from the run's committed records: the iteration log
// and each judged run's summary, the judge's negative-test output, the growth table.

import { fmt, lean, lineOf, span } from './data'
import { LessonScene, type Step } from './LessonScene'
import styles from './Lesson.module.css'

const loop = lean.loop
const judge = loop.judgeHeader
const base = loop.log[0]
const last = loop.log.filter((it) => it.verdict === 'retained').at(-1)!
if (!base || !last || loop.recheck.total_kHb !== last.total_kHb) throw new Error('lean lessons: the recheck of the final state does not match the last retained run')

// ---- 1. What may change ------------------------------------------------------------------------

export function LayersScene() {
  const frozen = ['the statements (lesson 5)', 'the definitions they use: Step, Eval, the data (lesson 4)', 'the judge itself']
  const free = ['proofs', 'lemmas and tactics', 'how facts are grouped into decisions', 'which files hold what']
  const steps: Step[] = [
    { say: <>A proof's cost is not part of what it proves. Two proofs of one statement are interchangeable, so the cheaper one can replace the other with no review.</> },
    { say: <>So the package has two layers. The frozen layer is what a reader reviews: statements and the definitions they use. Nothing may change it.</> },
    { say: <>The checked layer is everything the kernel checks instead of a reader: proofs, lemmas, tactics. Anything may change there, if the kernel still accepts the frozen statements.</> },
    { say: <>"The kernel still accepts" is made mechanical by a judge, a script that is itself frozen. It runs five checks.</>, hl: { j: span(judge, '# 1. protected files unchanged', '# 5. cost: k2l-eval') } },
    { say: <>First, a hash check: the judge, the frozen layer's compiled files and the definitions are unchanged.</>, hl: { j: [lineOf(judge, '# 1. protected files unchanged')] } },
    { say: <>Second, a scan for constructs that bypass the kernel: <code>sorry</code>, <code>native_decide</code>, <code>implemented_by</code>, declarations added without checking.</>, hl: { j: [lineOf(judge, '# 2. no forbidden construct')] } },
    { say: <>Fourth, every new declaration is replayed through the kernel, each target's type is compared with its frozen statement, and only three axioms are allowed.</>, hl: { j: span(judge, '# 4. judge/Judge.lean', '#    statement, axioms among') } },
    { say: <>Fifth, the cost: heartbeats per declaration, which do not depend on the machine's speed. A change is kept only if the judge passes and the total goes down.</>, hl: { j: [lineOf(judge, '# 5. cost: k2l-eval')] } },
  ]
  return (
    <LessonScene
      title="What may change, and who decides"
      panes={[{ id: 'j', label: 'The judge', source: judge }]}
      steps={steps}
      visual={(at) => (
        <div className={styles.columns}>
          <div className={`${styles.column} ${at === 1 ? styles.on : at === 2 ? styles.off : ''}`}>
            <strong>Frozen: read by a person</strong>
            <ul>{frozen.map((f) => <li key={f}>{f}</li>)}</ul>
          </div>
          <div className={`${styles.column} ${at === 2 ? styles.on : at === 1 ? styles.off : ''}`}>
            <strong>Checked: by the kernel</strong>
            <ul>{free.map((f) => <li key={f}>{f}</li>)}</ul>
          </div>
        </div>
      )}
      questions={[
        { q: 'Why freeze the judge too?',
          a: <>A loop that could edit the judge could make any change pass. With the judge frozen, the only way to pass is a proof the kernel accepts.</> },
        { q: 'Why heartbeats rather than seconds?',
          a: <>Seconds depend on the machine and its load; heartbeats count the work, so two runs of the same file give the same number and a small gain is visible.</> },
      ]}
    />
  )
}

// ---- 2. The judge says no -------------------------------------------------------------------------

export function NegativeScene() {
  const steps: Step[] = [
    { say: <>The judge was tested with {loop.negative.length} deliberately bad changes, on the proofs of an earlier run driven by hand, before the unattended run used it. Each must be rejected.</> },
    { say: <>Through the whole judge: a <code>sorry</code>, a different theorem under a target's name, an edit of a protected file, a <code>native_decide</code>, and importing the existing compiled proofs (which would hide their cost).</> },
    { say: <>With the text scan bypassed, the kernel-replay program alone still rejects the three that matter most: a theorem added without kernel checking, a proof through <code>native_decide</code>, and a proof by <code>sorry</code>.</> },
    { say: <>All {loop.negative.length} are rejected, each with the reason shown. The unattended run then used the same judge, with only the path to its cost tool changed.</> },
  ]
  return (
    <LessonScene
      title="Changes the judge must reject"
      panes={[]}
      steps={steps}
      visual={(at) => (
        <div className={styles.tableWrap}>
          <table className={styles.table}>
            <thead>
              <tr><th scope="col">bad change</th><th scope="col">checked by</th><th scope="col">what the judge said</th></tr>
            </thead>
            <tbody>
              {loop.negative.map((n) => {
                const on = at === 1 ? n.via === 'judge' : at === 2 ? n.via !== 'judge' : undefined
                return (
                  <tr key={n.case} className={on ? styles.on : on === false ? styles.off : ''}>
                    <td>{n.case}</td>
                    <td>{n.via === 'judge' ? 'the whole judge' : 'kernel replay alone'}</td>
                    <td><code>{n.result.length > 140 ? `${n.result.slice(0, 139)}…` : n.result}</code></td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </div>
      )}
      questions={[
        { q: <>Why test <code>native_decide</code> twice?</>,
          a: <>Once through the text scan, and once with the scan bypassed. The second shows that even a construct the scan missed would be caught by the axiom check: <code>native_decide</code> adds an axiom of its own.</> },
      ]}
    />
  )
}

// ---- 3. The run --------------------------------------------------------------------------------------

export function LoopRunScene() {
  const log = loop.log
  const max = Math.log10(base.total_kHb)
  const min = Math.log10(Math.min(...log.map((l) => l.total_kHb))) - 0.3
  const width = (kHb: number) => `${((Math.log10(kHb) - min) / (max - min)) * 100}%`
  const rejected = log.filter((l) => l.verdict === 'rejected')
  const steps: Step[] = [
    { say: <>An agent was given the judge, the {loop.targets} target statements of peano and of two synthetic definitions, and the proofs as they stood. It was told how to run the judge and nothing else, and was instructed not to read earlier attempts.</>, at: 0 },
    { say: <>Starting point: {fmt(base.total_kHb)} thousand heartbeats in all.</>, at: 0 },
    { say: <>First change: the counter invariant from one generic lemma and a check on each rule, instead of one proof case per rule.</>, at: 1 },
    { say: <>Second: determinism from distinct constructors (no comparison of rule pairs), witnesses from a computed step, and every fact about a definition in one kernel decision.</>, at: 2 },
    { say: <>Third: the other invariant from generic lemmas too. The per-rule tactic was no longer needed and was deleted.</>, at: 3 },
    { say: <>Not every attempt helps: one import made Lean's simplifier slower everywhere, the total went up, and the judge's rule rejected the change.</>, at: log.indexOf(rejected[0]) },
    { say: <>The rest are smaller: lemmas written so the kernel reduces them directly, facts of all definitions in one decision, shorter proofs.</>, at: log.length - 2 },
    { say: <>Final: {fmt(last.total_kHb)} thousand heartbeats, {Math.round(base.total_kHb / last.total_kHb)} times less, every state accepted by the judge. Rerunning the judge on the final state gave the same total.</>, at: log.length - 1 },
  ] as (Step & { at: number })[]
  return (
    <LessonScene
      title="The unattended run, iteration by iteration"
      panes={[]}
      steps={steps}
      delay={4200}
      visual={(i) => {
        const focus = (steps[i] as Step & { at: number }).at
        const it = log[focus]
        return (
          <>
            <div className={styles.tableWrap}>
              <table className={styles.table}>
                <thead>
                  <tr><th scope="col">run</th><th scope="col" className={styles.num}>total kHb</th><th scope="col">verdict</th><th scope="col" className={styles.barCell} aria-label="total, log scale" /></tr>
                </thead>
                <tbody>
                  {log.map((l, k) => (
                    <tr key={l.run} className={k === focus ? styles.on : k > focus ? styles.off : ''}>
                      <td><code style={{ whiteSpace: 'nowrap' }}>{l.run}</code></td>
                      <td className={styles.num}>{fmt(l.total_kHb)}</td>
                      <td>{l.verdict}</td>
                      <td className={styles.barCell}><div className={`${styles.logBar} ${l.verdict === 'rejected' ? styles.rejected : ''}`} style={{ width: width(l.total_kHb) }} title={`${l.run}: ${fmt(l.total_kHb)} kHb`} /></td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
            <p className={styles.small}><code>{it.run}</code>: {it.change}</p>
          </>
        )
      }}
      questions={[
        { q: 'The loop deleted the tactic of the earlier proofs. Could that weaken anything?',
          a: <>No. The tactic was in the checked layer: it only produced proofs. The statements it proved are frozen, and the judge checked that the new proofs prove them.</> },
        { q: 'Why does the bar chart use a logarithmic scale?',
          a: <>The total fell by nearly two orders of magnitude; on a linear scale every bar after the second would look the same.</> },
      ]}
    />
  )
}

// ---- 4. Growth with the size of a definition ------------------------------------------------------------

export function GrowthScene() {
  const rows = loop.growth
  const max = Math.max(...rows.map((r) => r.before ?? 0))
  const steps: Step[] = [
    { say: <>A cost that is fine for peano can be impossible for a large definition. The synthetic family has N constructors and N rules; here are its proofs' costs before and after an earlier, hand-driven run of the same kind.</> },
    { say: <>Before, the cost grew with the square of N: the determinism check compared every pair of rules, and the invariant's tactic searched each rule's heads. At the largest size it ran out of memory.</> },
    { say: <>After, the cost grows in proportion to N, and the largest size is checked.</> },
  ]
  return (
    <LessonScene
      title="Cost against the size of a definition"
      panes={[]}
      steps={steps}
      visual={(at) => (
        <div className={styles.tableWrap}>
          <table className={styles.table}>
            <thead>
              <tr><th scope="col" className={styles.num}>N</th><th scope="col" className={styles.num}>before, kHb</th><th scope="col" className={styles.num}>after, kHb</th><th scope="col" className={styles.barCell} aria-label="before and after, relative" /></tr>
            </thead>
            <tbody>
              {rows.map((r) => (
                <tr key={r.n}>
                  <td className={styles.num}>{r.n}</td>
                  <td className={styles.num}>{r.before === null ? 'out of memory' : fmt(r.before)}</td>
                  <td className={styles.num}>{fmt(r.after)}</td>
                  <td className={styles.barCell}>
                    {at !== 2 && <div className={styles.bar} style={{ width: `${((r.before ?? max) / max) * 100}%`, opacity: r.before === null ? 0.3 : 1 }} />}
                    {at !== 1 && <div className={styles.bar} style={{ width: `${(r.after / max) * 100}%`, background: 'var(--vocs-color-green)' }} />}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
      questions={[
        { q: 'Why does the growth matter more than the totals?',
          a: <>Real definitions are much larger than peano. A cost that grows with the square of the number of rules is what makes a large definition impossible, whatever the constant.</> },
      ]}
    />
  )
}
