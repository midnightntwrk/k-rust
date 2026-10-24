'use client'

// Scene: coverage of the specification. Which rules each test makes fire comes from
// story/story.toml (read off the rewrite steps; krs does not report run coverage yet).

import { corpus, paperRules, type RuleName, ruleNames } from './data'
import { Stage, usePlayer } from './player'
import styles from './Story.module.css'

const rulesOf = (index: number) => corpus[index].rules as readonly RuleName[]
const describe = (index: number) => {
  const rules = rulesOf(index)
  const all = ruleNames.every((name) => corpus.slice(0, index + 1).some((test) => (test.rules as readonly string[]).includes(name)))
  return `${corpus[index].id} passes through the machine: ${rules.join(', then ')} ${rules.length > 1 ? 'fire' : 'fires'}.${all ? ' Every rule has now fired: 100% specification coverage.' : ''}`
}

const phases = [
  { done: 0, active: -1, caption: 'The two rules of the specification, and the tests of the corpus.' },
  ...corpus.map((_, index) => ({ done: index + 1, active: index, caption: describe(index) })),
  { done: corpus.length, active: -1, caption: '100% specification coverage: the corpus exercises every rule. Next, measure which mistakes those tests would actually catch.' },
]

export function SpecCoverage() {
  const player = usePlayer(phases.length, 2600)
  const phase = phases[player.at]
  const firedBy = (name: RuleName) => corpus.slice(0, phase.done).filter((test) => (test.rules as readonly string[]).includes(name)).map((test) => test.id)
  const covered = ruleNames.filter((name) => firedBy(name).length > 0).length
  return (
    <Stage player={player} caption={phase.caption}>
      <div className={styles.score}>
        <strong className={covered === ruleNames.length ? styles.coverageComplete : undefined}>
          {Math.round((covered / ruleNames.length) * 100)}% specification coverage
        </strong>
        <span>{covered} / {ruleNames.length} rules covered</span>
        <div className={`${styles.meter} ${styles.ok}`} aria-hidden="true">
          <div style={{ width: `${(covered / ruleNames.length) * 100}%` }} />
        </div>
      </div>
      <div className={styles.pair}>
        {ruleNames.map((name) => {
          const by = firedBy(name)
          const firing = phase.active >= 0 && rulesOf(phase.active).includes(name)
          return (
            <div key={name} className={`${styles.rule} ${by.length ? styles.covered : ''} ${firing ? styles.firing : ''}`}>
              <div className={styles.head}>
                <span>{name}</span>
                <span>{by.length ? `fired by ${by.join(', ')}` : 'not yet fired'}</span>
              </div>
              <div className={styles.body}>
                {paperRules[name].lhs} = {paperRules[name].rhs}
              </div>
            </div>
          )
        })}
      </div>
      <div className={styles.tableWrap}>
        <table className={styles.table}>
          <thead>
            <tr>
              <th>test</th>
              <th>rules it made fire</th>
            </tr>
          </thead>
          <tbody>
            {corpus.map((test, index) => (
              <tr key={test.id} className={phase.active === index ? styles.fresh : undefined}>
                <td>
                  {test.id} · {test.program}
                </td>
                <td>{index < phase.done ? test.rules.join(', ') : <span className={`${styles.pill} ${styles.idle}`}>not run</span>}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </Stage>
  )
}
