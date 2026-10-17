'use client'

// Scene: tests that check nothing. Illustrative Rust, not from the repository.

import { Stage, Status, usePlayer } from './player'
import styles from './Story.module.css'

const tests = ['assert_eq!(VERSION, "1.0.0")', 'assert_eq!(add(0, 0), 0)', 'assert_eq!(add(0, 1), 1)', 'assert_eq!(add(1, 1), 2)']
const rerun = 'Run the suite again.'
const phases = [
  { bug: false, running: -1, flag: false, caption: 'Your AI wrote four tests. All green.' },
  { bug: false, running: -1, flag: true, caption: 'One of them checks that a constant equals the same constant, typed out again. It can never fail. Everyone using an AI coding assistant has seen this test.' },
  { bug: true, running: -1, flag: false, caption: 'A second problem. Change what add does: it now ignores everything in a above 1, so add(2, 2) returns 3.' },
  { bug: true, running: 0, flag: false, caption: rerun },
  { bug: true, running: 1, flag: false, caption: rerun },
  { bug: true, running: 2, flag: false, caption: rerun },
  { bug: true, running: 3, flag: false, caption: rerun },
  { bug: true, running: -1, flag: false, caption: 'Still all green. The tests pass whether add is right or wrong.' },
]
const delays = [3000, 3000, 3000, 700]

export function TestsThatCheckNothing() {
  const player = usePlayer(phases.length, delays)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption} aside={<Status kind="illustrative">illustrative Rust</Status>}>
      <div className={styles.split}>
        <div className={styles.panel}>
          <div className={styles.label}>src/lib.rs</div>
          <pre>
            {'pub const VERSION: &str = "1.0.0";\n\npub fn add(a: u64, b: u64) -> u64 {\n    '}
            {phase.bug ? <span className={styles.bug}>a.min(1) + b</span> : 'a + b'}
            {'\n}'}
          </pre>
        </div>
        <ul className={styles.tests}>
          {tests.map((test, index) => (
            <li key={test} className={phase.flag && index === 0 ? styles.flagged : undefined}>
              <code>{test}</code>
              <span className={`${styles.pill} ${phase.running === index ? styles.running : styles.pass}`}>
                {phase.running === index ? 'running' : 'pass'}
              </span>
            </li>
          ))}
        </ul>
      </div>
    </Stage>
  )
}
