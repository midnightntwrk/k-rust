'use client'

// Scene: a test that restates a constant. Illustrative Rust, not from the repository.

import { Stage, Status, usePlayer } from './player'
import styles from './Story.module.css'

const phases = [
  { version: '1.0.0', expected: '1.0.0', changed: '', flag: false, pass: true, caption: 'Your AI wrote a test for the version constant. It passes.' },
  { version: '1.0.0', expected: '1.0.0', changed: '', flag: true, pass: true,
    caption: 'Look at what it compares: the constant, and the same text typed a second time. None of your code runs in between.' },
  { version: '1.1.0', expected: '1.0.0', changed: 'version', flag: true, pass: false,
    caption: 'The only thing that turns it red is changing the version on purpose, at release time.' },
  { version: '1.1.0', expected: '1.1.0', changed: 'expected', flag: true, pass: true,
    caption: 'The fix is to type the new version a second time. This test cannot catch a bug, because it never checks anything your code computes.' },
]

export function VersionTest() {
  const player = usePlayer(phases.length, 3200)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption} aside={<Status kind="illustrative">illustrative Rust</Status>}>
      <div className={styles.split}>
        <div className={styles.panel}>
          <div className={styles.label}>src/lib.rs</div>
          <pre>
            {'pub const VERSION: &str = "'}
            {phase.changed === 'version' ? <span className={styles.bug}>{phase.version}</span> : phase.version}
            {'";'}
          </pre>
        </div>
        <ul className={styles.tests}>
          <li className={phase.flag ? styles.flagged : undefined}>
            <code>
              {'assert_eq!(VERSION, "'}
              {phase.changed === 'expected' ? <span className={styles.bug}>{phase.expected}</span> : phase.expected}
              {'")'}
            </code>
            <span className={`${styles.pill} ${phase.pass ? styles.pass : styles.fail}`}>{phase.pass ? 'pass' : 'fail'}</span>
          </li>
        </ul>
      </div>
    </Stage>
  )
}
