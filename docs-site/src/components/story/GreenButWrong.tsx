'use client'

// Scene: tests that pass whether the code is right or wrong. Illustrative Rust, not from the repository.

import { Stage, Status, usePlayer } from './player'
import styles from './Story.module.css'

const tests = ['assert_eq!(add(0, 0), 0)', 'assert_eq!(add(0, 1), 1)', 'assert_eq!(add(1, 1), 2)']
const rerun = 'Run the suite again.'
const phases = [
  { bug: false, running: -1, gap: false, caption: 'Your AI wrote three tests for add. All green.' },
  { bug: true, running: -1, gap: false, caption: 'Now break add: it ignores everything in a above 1, so add(2, 2) returns 3.' },
  { bug: true, running: 0, gap: false, caption: rerun },
  { bug: true, running: 1, gap: false, caption: rerun },
  { bug: true, running: 2, gap: false, caption: rerun },
  { bug: true, running: -1, gap: false, caption: 'Still all green. The tests pass whether add is right or wrong.' },
  { bug: true, running: -1, gap: true,
    caption: 'Every test keeps a at 0 or 1, so none of them reaches the inputs the bug changed. Passing says nothing about what the tests never try.' },
]
const delays = [3000, 3000, 700, 700, 700, 3000]

export function GreenButWrong() {
  const player = usePlayer(phases.length, delays)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption} aside={<Status kind="illustrative">illustrative Rust</Status>}>
      <div className={styles.split}>
        <div className={styles.panel}>
          <div className={styles.label}>src/lib.rs</div>
          <pre>
            {'pub fn add(a: u64, b: u64) -> u64 {\n    '}
            {phase.bug ? <span className={styles.bug}>a.min(1) + b</span> : 'a + b'}
            {'\n}'}
          </pre>
        </div>
        <ul className={styles.tests}>
          {tests.map((test, index) => (
            <li key={test}>
              <code>{test}</code>
              <span className={`${styles.pill} ${phase.running === index ? styles.running : styles.pass}`}>
                {phase.running === index ? 'running' : 'pass'}
              </span>
            </li>
          ))}
          {phase.gap && (
            <li className={styles.flagged}>
              <code>add(2, 2) returns 3, not 4</code>
              <span className={`${styles.pill} ${styles.fail}`}>no test</span>
            </li>
          )}
        </ul>
      </div>
    </Stage>
  )
}
