'use client'

// Scene: tests that pass whether the code is right or wrong. Illustrative Rust, not from the repository.

import { Stage, Status, usePlayer } from './player'
import styles from './Story.module.css'

const tests = ['assert_eq!(add(0, 0), 0)', 'assert_eq!(add(0, 1), 1)', 'assert_eq!(add(1, 1), 2)']
const phases = [
  { bug: false, completed: 0, caption: 'Even tests with real assertions often miss the cases that would catch an error. Run these three tests on a + b.' },
  { bug: false, completed: 1, caption: 'add(0, 0) returns 0. Pass.' },
  { bug: false, completed: 2, caption: 'add(0, 1) returns 1. Pass.' },
  { bug: false, completed: 3, caption: 'add(1, 1) returns 2. Pass. Three real assertions, all green.' },
  { bug: true, completed: 0, caption: 'Now break the code: a.min(1) + b ignores everything in a above 1. Run the same tests again.' },
  { bug: true, completed: 1, caption: 'add(0, 0) still returns 0. Pass.' },
  { bug: true, completed: 2, caption: 'add(0, 1) still returns 1. Pass.' },
  { bug: true, completed: 3, caption: 'add(1, 1) still returns 2. Pass. The code is wrong, but every test is still green.' },
  { bug: true, completed: 3, gap: true, caption: 'The missing case: add(2, 2) should return 4, but now returns 3. None of these tests catches it.' },
]
const delays = [3000, 900, 900, 2500, 3000, 900, 900, 2500]

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
              <span className={`${styles.pill} ${index < phase.completed ? styles.pass : styles.idle}`}>
                {index < phase.completed ? 'pass' : 'pending'}
              </span>
            </li>
          ))}
          {('gap' in phase && phase.gap) && (
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
