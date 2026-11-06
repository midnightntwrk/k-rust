'use client'

// Lesson "What you have to read": the trusted base, the review cone computed by #review_cone
// (its output is in the data as written), the lines read once and per project, and the
// differential run against the reference kompile.

import { type ReactNode } from 'react'

import { type ConeDecl, config, groundText, kItem, lean, lineOf, source, span, textSource } from './data'
import { coneNumbers, initCount, once, perProject, user } from './numbers'
import { type Pane, LessonScene, type Step } from './LessonScene'
import styles from './Lesson.module.css'

const coneText = textSource('i-user-core.txt (written by #review_cone)', user.raw)

// ---- 1. Trusted, checked, read -----------------------------------------------------------------

export function TrustScene() {
  const checks = source('LibraryChecks')
  const columns: { title: string; items: { key: string; text: ReactNode }[] }[] = [
    {
      title: 'Trusted',
      items: [
        { key: 'kernel', text: <>the Lean {lean.provenance.leanVersion} kernel</> },
        { key: 'axioms', text: <>three axioms: <code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code></> },
        { key: 'init', text: <>{initCount} declarations of Lean's <code>Init</code></> },
        { key: 'kompile', text: <>kompile (krust): the KORE is K's meaning of peano.k</> },
        { key: 'reader', text: <>the KORE reader, for the second route of the per-project check</> },
        { key: 'cone', text: <><code>#review_cone</code> lists everything the statements reach</> },
      ],
    },
    {
      title: 'Checked by the kernel',
      items: [
        { key: 'proofs', text: 'every proof' },
        { key: 'tactics', text: <>the tactics, such as <code>step_cases</code>: they only produce proofs</> },
        { key: 'exec', text: <>the executable step, tied to <code>Step</code> by <code>step_iff</code></> },
        { key: 'decisions', text: <>decisions on the data: <code>rulesApart</code>, <code>evalReady</code></> },
      ],
    },
    {
      title: 'Read',
      items: [
        { key: 'statements', text: 'the statements' },
        { key: 'deps', text: <>everything they depend on: {coneNumbers.total} lines</> },
      ],
    },
  ]
  const steps: { say: ReactNode; on: string[]; hl?: number[] }[] = [
    { say: <>A proof is only as good as the statement it proves. Everything here is in one of three places.</>, on: [] },
    { say: <>The kernel is trusted to check that a proof proves its statement. No <code>native_decide</code> is used: every computation in a proof is kernel evaluation.</>, on: ['kernel'] },
    { say: <>Every theorem uses only three axioms, and the build fails if another appears: <code>#print axioms</code> is pinned per theorem.</>, on: ['axioms'], hl: span(checks, "info: 'KCore.Peano.Ground.deterministic' depends on axioms", '#print axioms KCore.Peano.Ground.counter_preserved') },
    { say: <>The statements reach {initCount} declarations of Lean's own library, such as <code>List.find?</code> and <code>String</code>'s order. They are trusted with Lean.</>, on: ['init'] },
    { say: <>kompile is trusted to produce K's meaning of peano.k; the semantics here reads KORE-level rules and equations.</>, on: ['kompile', 'reader'] },
    { say: <><code>#review_cone</code> is trusted to be complete, and there is a bound that does not trust it (below).</>, on: ['cone'] },
    { say: <>Proofs, tactics, the executable step and the decisions are checked, not read: if any were wrong, a proof would fail to check. It would not prove a different statement.</>, on: ['proofs', 'tactics', 'exec', 'decisions'] },
    { say: <>What is left to read is the statements and what their meaning depends on: {coneNumbers.total} lines, computed by Lean.</>, on: ['statements', 'deps'] },
  ]
  return (
    <LessonScene
      title="Trusted, checked, read"
      panes={[{ id: 'c', label: 'The axioms, pinned', source: checks }]}
      steps={steps.map((s) => ({ say: s.say, hl: s.hl ? { c: s.hl } : undefined, panes: s.hl ? ['c'] : [] }))}
      visual={(at) => (
        <div className={styles.columns}>
          {columns.map((column) => (
            <div key={column.title} className={styles.column}>
              <h4>{column.title}</h4>
              <ul>
                {column.items.map((item) => {
                  const on = steps[at].on.length ? steps[at].on.includes(item.key) : undefined
                  return (
                    <li key={item.key} className={on ? styles.on : on === false ? styles.off : ''}>
                      {item.text}
                    </li>
                  )
                })}
              </ul>
            </div>
          ))}
        </div>
      )}
      questions={[
        { q: <>Why can a bug in the tactic <code>step_cases</code> not make a wrong statement true?</>,
          a: <>A tactic only builds a proof term, which the kernel then checks against the statement. A wrong tactic fails to produce a proof that checks; it cannot change what the statement says.</> },
        { q: 'Which row of the trusted list does the reference differential below bear on?',
          a: <>kompile's. The differential is evidence about krust's output, not a reason anything is correct; the row stays trusted.</> },
      ]}
    />
  )
}

// ---- 2. Computing the cone ---------------------------------------------------------------------

/** The line of the cone listing that declares `decl` (its range, kind and name). */
function declLine(decl: ConeDecl): number {
  const rows = coneText.text.split('\n')
  const i = rows.findIndex((row) => {
    const cells = row.trim().split(/\s+/)
    return cells[0] === `${decl.start}-${decl.end}` && cells[2] === decl.name
  })
  if (i < 0) throw new Error(`lean lessons: the cone listing has no line for ${decl.name}`)
  return i + 1
}

export function ConeScene() {
  const maxDepth = Math.max(...user.decls.map((d) => d.depth))
  const depths = Array.from({ length: maxDepth + 1 }, (_, d) => d)
  const modules = user.modules
  const linesUpTo = (module: string, depth: number) => {
    const covered = new Set<number>()
    for (const d of user.decls) if (d.module === module && d.depth <= depth) for (let l = d.start; l <= d.end; l += 1) covered.add(l)
    return covered.size
  }
  const names = (depth: number) => user.decls.filter((d) => d.depth === depth).map((d) => d.name.split('.').pop()!)
  const say = (depth: number): ReactNode => {
    const here = names(depth)
    const sample = here.slice(0, 4).map((n, i) => <span key={n}>{i > 0 && ', '}<code>{n}</code></span>)
    if (depth === 0) return <>The roots are the statements and witnesses, {here.length} definitions. The tool starts from them.</>
    return <>Through types and values, {here.length} more declaration{here.length > 1 ? 's' : ''} at distance {depth}: {sample}{here.length > 4 ? ', …' : ''}</>
  }
  type ConeStep = { say: ReactNode; depth: number; hl: number[] }
  const steps: ConeStep[] = [
    { say: <><code>#review_cone</code> follows the types of reached declarations and the values of reached definitions; it does not enter proofs, and it stops at Lean's own library.</>, depth: -1, hl: [1, 2, 3] },
    ...depths.map((d) => ({ say: say(d), depth: d, hl: user.decls.filter((x) => x.depth === d).map(declLine) })),
    { say: <>It ends at {coneNumbers.total} source lines in {coneNumbers.decls} declarations, met no theorem ({coneNumbers.theoremsMet}), and folded {coneNumbers.folded} generated declarations into their parents.</>, depth: maxDepth, hl: span(coneText, '## lines per module', '  298') },
    { say: <>Of these, {coneNumbers.once} lines in five files are the meaning of every K definition; {coneNumbers.perProject} lines are peano's.</>, depth: maxDepth, hl: span(coneText, '## lines per module', '  298') },
  ]
  return (
    <LessonScene
      title="Computing what the statements depend on"
      panes={[{ id: 'c', label: 'The cone, as written', source: coneText }]}
      steps={steps.map((s) => ({ say: s.say, hl: { c: s.hl } }))}
      delay={3000}
      visual={(at) => {
        const depth = steps[at].depth
        return (
          <div className={styles.tableWrap}>
            <table className={styles.table}>
              <thead>
                <tr><th scope="col">Module</th><th scope="col" className={styles.num}>lines reached</th><th scope="col" className={styles.barCell} aria-label="share of the module's cone lines" /><th scope="col">read</th></tr>
              </thead>
              <tbody>
                {modules.map((m) => {
                  const reached = depth < 0 ? 0 : linesUpTo(m.module, depth)
                  return (
                    <tr key={m.module} className={reached ? '' : styles.off}>
                      <td><code>{m.module.replace('KcoreSpec.', '')}</code></td>
                      <td className={styles.num}>{reached} / {m.lines}</td>
                      <td className={styles.barCell}><div className={styles.meter}><div style={{ width: `${(reached / m.lines) * 100}%` }} /></div></td>
                      <td className={styles.small}>{once.includes(m.module) ? 'once' : 'per project'}</td>
                    </tr>
                  )
                })}
              </tbody>
              <tfoot>
                <tr><td>total</td><td className={styles.num}>{depth < 0 ? 0 : modules.reduce((s, m) => s + linesUpTo(m.module, depth), 0)} / {coneNumbers.total}</td><td /><td /></tr>
              </tfoot>
            </table>
          </div>
        )
      }}
      questions={[
        { q: 'Why does the cone not enter proofs?',
          a: <>A proof can only prove the statement it is checked against, so its content cannot change what the statement means. Subterms whose type is a proposition are skipped, and theorems other than the roots are not entered.</> },
        { q: 'How can you bound the cone without trusting the tool?',
          a: <>The eight modules it reaches import only Lean's <code>Init</code> and each other, so everything the statements can mention is in those files ({coneNumbers.files} lines) or in <code>Init</code>.</> },
      ]}
    />
  )
}

// ---- 3. Read once, read per project ------------------------------------------------------------

const questionOf: Record<string, ReactNode> = {
  'KcoreSpec.FixedSignature': <>Which sorts and constructors does every kompiled definition have before the user's: the K sequence, the generated cells, the builtin sorts?</>,
  'KcoreSpec.Core': <>What is a definition's content: sorts, constructors, subsorts, functions as ordered clauses with an optional catch-all, rules between configurations?</>,
  'KcoreSpec.Value': <>What is a configuration: a ground term whose computed sort is the configuration sort?</>,
  'KcoreSpec.Evaluation': <>What does it mean for a pattern to match, and what value does a function or a right-hand side have?</>,
  'KcoreSpec.Step': <>What is one rewrite step?</>,
  'KcoreSpec.PeanoCore': <>Is this data peano.k? Read it against the source, or rely on the kernel-checked equality of its emitted KORE with kompile's.</>,
  'KcoreSpec.PeanoLibrary': <>Are the names abbreviations of the right terms, with the labels of the data?</>,
  'KcoreSpec.PeanoProperties': <>Do the statements say what you want?</>,
}

export function ReadScene() {
  const files: Record<string, string> = {
    'KcoreSpec.FixedSignature': 'FixedSignature', 'KcoreSpec.Core': 'Core', 'KcoreSpec.Value': 'Value', 'KcoreSpec.Evaluation': 'Evaluation',
    'KcoreSpec.Step': 'Step', 'KcoreSpec.PeanoCore': 'PeanoCore', 'KcoreSpec.PeanoLibrary': 'PeanoLibrary', 'KcoreSpec.PeanoProperties': 'PeanoProperties',
  }
  const order = [...once, ...perProject]
  const panes: Pane[] = order.map((m) => ({ id: m, label: once.includes(m) ? 'read once, for every definition' : 'read for peano', source: source(files[m]) }))
  const rangeLines = (m: string) => user.decls.filter((d) => d.module === m).flatMap((d) => Array.from({ length: d.end - d.start + 1 }, (_, i) => d.start + i))
  const steps: Step[] = [
    ...order.map((m) => ({
      say: <><code>{files[m]}.lean</code>, {user.totals[m].coneLines} of {user.totals[m].fileLines} lines: {questionOf[m]}</>,
      hl: { [m]: rangeLines(m) },
      panes: [m],
    })),
  ]
  return (
    <LessonScene
      title={`${coneNumbers.once} lines once, ${coneNumbers.perProject} per project`}
      panes={panes}
      steps={steps}
      delay={4500}
      visual={(at) => (
        <div className={styles.subst}>
          <span className={styles.termLabel}>{once.includes(order[at]) ? `once: ${coneNumbers.once} lines, ${coneNumbers.onceDecls} declarations` : `per project: ${coneNumbers.perProject} lines, ${coneNumbers.perProjectDecls} declarations`}</span>
        </div>
      )}
      questions={[
        { q: <>Why can a reader skip <code>DecidableEq</code> of ground terms, which proofs use constantly?</>,
          a: <>No statement mentions it: it lives in <code>Execution.lean</code>, outside the cone, and is used only inside proofs, which the kernel checks.</> },
        { q: 'What changes for a second definition?',
          a: <>Only the per-project part: its data, its names and its statements. The {coneNumbers.once} lines of the shared files are read once.</> },
      ]}
    />
  )
}

// ---- 4. The differential against the reference kompile -----------------------------------------

export function DifferentialScene() {
  const refSem = source('refSem')
  const parse = source('parseRefSem')
  const stepOn = source('stepOnRefSem')
  const stepOnRef = source('stepOnRef')
  const fixed = source('FixedSignature')
  const kc = config('kconfig')
  if (kc.sort !== 'GeneratedTopCell' || (kc.successors ?? [null]).length !== 0) {
    throw new Error('lean lessons: the #KConfigValue configuration is no longer a stuck configuration')
  }
  // Short descriptions of the recorded differences, each pinned to its row of the run's table.
  const described: { starts: string; text: ReactNode; read: ReactNode }[] = [
    { starts: 'krust only: the constructor `#KConfigValue', text: <>krust only: the constructor <code>#KConfigValue : K → KItem</code> and the function <code>#unboxKConfigValue</code></>, read: 'yes: the constructor' },
    { starts: 'krust only: 16 selector-domain axioms', text: <>krust only: 16 selector-domain axioms and 16 selector-inverse simplification axioms</>, read: 'no (the theory only)' },
    { starts: '`initKCell`', text: <>the equation of <code>initKCell</code>, the initial k cell</>, read: 'no' },
    { starts: 'the no-junk axioms', text: <>no-junk axioms of <code>KItem</code>, <code>Nat</code>, <code>State</code>: order and bound-variable names</>, read: 'no (the theory only)' },
    { starts: 'the no-confusion axioms', text: <>no-confusion axioms of <code>Nat</code> and <code>State</code>: argument order</>, read: 'no (the theory only)' },
    { starts: '8 `isS`', text: <>8 generated <code>isS</code> equations: a bound variable's name</>, read: 'no' },
    { starts: 'attributes: `Source`', text: <><code>Source</code> attributes of builtin sentences</>, read: 'no' },
    { starts: 'attributes: `Location`', text: <><code>Location</code> attributes: starting columns</>, read: 'no' },
    { starts: 'order of the sentences', text: <>order of the sentences, user sorts and constructors</>, read: <>no (proved: <code>stepOn_refSem</code>)</> },
  ]
  const recorded = lean.refKompile.rows
  if (recorded.length !== described.length || recorded.some((row, i) => !row.difference.startsWith(described[i].starts))) {
    throw new Error('lean lessons: the reference-kompile differences no longer match the scene’s descriptions')
  }
  const rows = recorded.map((row, i) => ({ ...described[i], sentences: row.sentences }))
  const panes: Pane[] = [
    { id: 'r', label: 'What parse reads from the reference KORE', source: refSem },
    { id: 'p', label: 'Kernel-checked', source: parse },
    { id: 's', label: 'The step of a core, on ground terms', source: stepOn },
    { id: 'q', label: 'The same step, kernel-checked', source: stepOnRef },
    { id: 'f', label: 'The fixed signature', source: fixed },
  ]
  const steps: (Step & { rows?: number[] })[] = [
    { say: <>The trusted KORE is krust's. The reference K kompile was run once on the same peano.k, and its output compared.</>, panes: ['r', 'p'] },
    { say: <><code>parse</code> accepts the reference KORE, and the core it reads is <code>peanoCore</code> with sorts and constructors declared in another order.</>, hl: { r: span(refSem, 'def refSem', '⟨"Lbls", ["Nat"], "Nat"⟩'), p: [lineOf(parse, 'theorem parse_ref_sem'), lineOf(parse, 'theorem wf_parse_ref')] }, panes: ['r', 'p'] },
    { say: <>The kernel proves that the two cores have the same step; it follows from a generic theorem about cores that agree on what the step reads.</>, hl: { q: [lineOf(stepOnRef, 'theorem stepOn_refSem')], s: span(stepOn, 'def StepOn', '∃ (hx : c.sortOf x') }, panes: ['s', 'q'] },
    { say: <>The reference KORE is not in the fragment: <code>emit</code> does not give it back. In the user module krust has {lean.refKompile.krustSentences} sentences, the reference {lean.refKompile.refSentences}.</>, hl: { p: [lineOf(parse, 'theorem ref_not_F0')] }, panes: ['p'], rows: [] },
    { say: <>Of the differences, the step reads one: krust adds the constructor <code>#KConfigValue : K → KItem</code>, and the fixed signature has it.</>, hl: { f: [lineOf(fixed, "Lbl'Hash'KConfigValue")] }, panes: ['f'], rows: [0] },
    { say: <>So configurations include terms the reference signature lacks. For one of them Lean computes the sort <code>{kc.sort}</code> and no successor.</>, panes: [], rows: [0] },
    { say: <>No rule's left-hand side matches such a k cell, and no right-hand side builds one (checked by reading the two rules), so statements over all configurations still cover the reference's.</>, panes: [], rows: [0] },
    { say: <>The other differences are axioms of the theory, presentation and order; the step reads none of them.</>, panes: [], rows: rows.map((_, i) => i).slice(1) },
  ]
  return (
    <LessonScene
      title="The differential against the reference kompile"
      panes={panes}
      steps={steps}
      visual={(at) => {
        const s = steps[at]
        if (at === 5 || at === 6) {
          return (
            <div className={styles.termBox}>
              <span className={styles.termLabel}>a configuration of the fixed signature, computed by Lean</span>
              <div className={styles.term}>{groundText(kc.term)}</div>
              <span className={styles.small}>k item: <code>{groundText(kItem(kc.term))}</code> · sort: <code>{kc.sort}</code> · successors: {kc.successors?.length}</span>
            </div>
          )
        }
        if (!s.rows) return null
        return (
          <div className={styles.tableWrap}>
            <table className={styles.table}>
              <thead>
                <tr><th scope="col">Difference (krust against reference)</th><th scope="col" className={styles.num}>sentences</th><th scope="col">read by Step?</th></tr>
              </thead>
              <tbody>
                {rows.map((row, i) => (
                  <tr key={i} className={s.rows!.length ? (s.rows!.includes(i) ? styles.on : styles.off) : ''}>
                    <td>{row.text}</td>
                    <td className={styles.num}>{row.sentences}</td>
                    <td>{row.read}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        )
      }}
      questions={[
        { q: 'Does agreement with the reference kompile show that the semantics is right?',
          a: <>No. It is evidence about krust's output on one definition. kompile stays in the trusted list; what is proved is that the two outputs give the same step on peano.</> },
        { q: <>Why does a statement over all configurations still say something about the reference's configurations?</>,
          a: <>The reference's configurations are among them (its signature has fewer constructors), and the extra ones are stuck and unreachable from peano's. A statement for all configurations is in particular a statement for the reference's.</> },
      ]}
    />
  )
}

/** A short excerpt, as a static block (no player). */
export function SourceBlock({ k }: { k: string }) {
  const src = source(k)
  return (
    <figure className={styles.pane}>
      <figcaption className={styles.paneHead}>
        <span>{src.file}</span>
        <span className={styles.paneFile}>lines {src.start}–{src.end}</span>
      </figcaption>
      <div className={styles.code}>
        {src.text.split('\n').map((row, i) => (
          <div key={i} className={styles.row}>
            <span className={styles.num} aria-hidden="true">{src.start + i}</span>
            <span className={styles.src}>{row || ' '}</span>
          </div>
        ))}
      </div>
    </figure>
  )
}
