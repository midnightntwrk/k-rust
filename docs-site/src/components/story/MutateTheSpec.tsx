'use client'

import { caught, corpus, mutations, paperRules, ruleNames, tests } from './data'
import { Stage, usePlayer } from './player'
import styles from './MutateTheSpec.module.css'

const candidate = mutations.find((mutation) => !corpus.some((test) => caught(mutation, test)))
const added = tests.find((test) => test.climb)
if (!candidate || !added || !caught(candidate, added)) throw new Error('story climb needs a surviving edit and a test that catches it')
const edit = candidate
const before = mutations.filter((mutation) => corpus.some((test) => caught(mutation, test))).length
const after = mutations.filter((mutation) => [...corpus, added].some((test) => caught(mutation, test))).length
if (!before || after <= before) throw new Error('story climb must improve the mutation score')
const improved = Math.round(after / before * 100)
const phases = [
  { action: 'Reads the specification and the existing tests.', caption: '100% rule coverage. Now ask whether these tests would catch a wrong rule.' },
  { action: 'Proposes a rule change for the tests to catch.', caption: `Change one rule so addition ${edit.why}. Would the corpus notice?` },
  { action: 'Reads the result: no existing test catches the change.', caption: 'All existing tests give the same results. Every rule is covered, but this mistake slips through.' },
  { action: 'Writes a new test aimed at the surviving mutation.', caption: 'Use the surviving mutation as feedback. Add a test whose result differs between the original and edited specifications.' },
  { action: 'Keeps the successful test; looks for the next gap.', caption: 'The new test catches the mutation. AI keeps it in the corpus and uses the measured improvement as feedback for its next attempt: propose, measure, improve, repeat.' },
]

export function MutateTheSpec() {
  const player = usePlayer(phases.length, 1800)
  const changed = player.at >= 1
  const checked = player.at >= 2
  const growing = player.at >= 3
  const caughtEdit = player.at >= 4
  return (
    <Stage player={player} caption={phases[player.at].caption}>
      <div className={styles.workflow}>
        <div className={`${styles.agent} ${player.at === 2 ? styles.reading : ''}`}>
          <span className={styles.avatar} aria-hidden="true">AI</span>
          <div className={styles.agentCopy}><strong>AI agent</strong><div className={styles.activity} aria-live="polite">{phases[player.at].action}</div></div>
        </div>
        <svg className={styles.connections} viewBox="0 0 700 66" aria-hidden="true">
          <defs>
            <marker id="climb-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" /></marker>
          </defs>
          <path className={player.at === 1 ? styles.activeConnection : undefined} d="M 340 2 V 20 H 175 V 64" markerEnd="url(#climb-arrow)" />
          <path className={player.at === 3 ? styles.activeConnection : undefined} d="M 360 2 V 20 H 525 V 64" markerEnd="url(#climb-arrow)" />
          <text x="175" y="13" textAnchor="middle">propose a mutation</text>
          <text x="525" y="13" textAnchor="middle">write a targeted test</text>
        </svg>
        <div className={styles.mobileFlow}>AI proposes → measures → improves the corpus</div>
      <div className={styles.layout}>
        <div className={styles.spec}>
          <div className={styles.heading}>Specification {changed && <span>proposed mutation</span>}</div>
          <pre><code>{ruleNames.map((name) => (
            <span className={styles.line} key={name}>{paperRules[name].lhs} = <span className={changed && edit.rule === name ? styles.changed : undefined}>{changed && edit.rule === name ? edit.displayNew : paperRules[name].rhs}</span></span>
          ))}</code></pre>
          <div className={styles.verdict}>{caughtEdit ? '✓ New test catches this mistake' : checked ? 'Existing tests miss this mistake' : 'Run the corpus against the proposed edit'}</div>
        </div>
        <div className={styles.corpus}>
          <div className={styles.heading}>Test corpus <span>100% rule coverage</span></div>
          <ol className={styles.tests}>
            {corpus.map((test, index) => (
              <li key={`${test.id}-${player.at === 2}`} className={player.at === 2 ? styles.scan : undefined} style={{ animationDelay: `${index * 230}ms` }}>
                <code>test {index + 1}</code><span className={player.at === 2 ? styles.resultReading : undefined} style={{ animationDelay: `${index * 230}ms` }}>{checked ? '✓ same result' : '—'}</span>
              </li>
            ))}
            <li className={`${styles.newTest} ${growing ? styles.visible : ''}`} aria-hidden={!growing}>
              <code>test {corpus.length + 1} <span>AI-ADDED</span></code><span className={caughtEdit ? styles.caught : undefined}>{caughtEdit ? '✓ catches mutation' : 'checking…'}</span>
            </li>
          </ol>
        </div>
      </div>
      </div>
      <div className={styles.climb}>
        <div className={styles.score}><strong>Test strength · {caughtEdit ? improved : 100}% of baseline</strong><span>{caughtEdit ? after : before} / {mutations.length} mutations caught</span></div>
        <div className={styles.track} role="img" aria-label={`Test strength: ${caughtEdit ? improved : 100}% of the starting corpus, based on mutations caught`}>
          <div className={styles.fill} style={{ width: `${(caughtEdit ? improved : 100) / 250 * 100}%` }} />
          <span className={styles.baseline} style={{ left: '40%' }} />
        </div>
        <div className={styles.legend}><span>Starting corpus = 100%</span><span>AI proposes · measures · improves</span></div>
      </div>
    </Stage>
  )
}
