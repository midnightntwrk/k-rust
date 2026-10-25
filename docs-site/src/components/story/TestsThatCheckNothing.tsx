'use client'

// Illustrative Rust, not from the repository.

import { Stage, Status, usePlayer } from './player'
import styles from './Story.module.css'

const captions = [
  'Ever asked AI to write tests for your code, only to get tests that check nothing?',
  'This assertion compares the result with itself. It passes no matter what add returns.',
]

export function TestsThatCheckNothing() {
  const player = usePlayer(captions.length, 3000)
  return (
    <Stage player={player} caption={captions[player.at]} aside={<Status kind="illustrative">illustrative Rust</Status>}>
      <div className={styles.panel}>
        <div className={styles.label}>tests/add.rs</div>
        <pre>{'let result = add(1, 1);\n'}<span className={player.at === 1 ? styles.bug : undefined}>{'assert_eq!(result, result);'}</span></pre>
      </div>
      <div><span className={`${styles.pill} ${styles.pass}`}>pass</span></div>
    </Stage>
  )
}
