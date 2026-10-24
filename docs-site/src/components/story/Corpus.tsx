'use client'

import { corpus } from './data'
import { Stage, usePlayer } from './player'
import styles from './Corpus.module.css'

export function Corpus() {
  const player = usePlayer(corpus.length, 800)
  return (
    <Stage player={player} caption="Each expected result comes from the specification.">
      <div className={styles.runner}>
        <div className={styles.header}><span>TEST SUITE</span><code>plus</code></div>
        <ol className={styles.list} style={{ minHeight: `${corpus.length * 2.75}rem` }} aria-live="polite" aria-relevant="additions">
          {corpus.slice(0, player.at + 1).map((test, index) => (
            <li key={test.id}>
              <span className={styles.check} aria-hidden="true">✓</span>
              <span className={styles.name}>test {index + 1}</span>
              <span className={styles.dots} aria-hidden="true" />
              <span className={styles.pass}>PASS</span>
            </li>
          ))}
        </ol>
      </div>
    </Stage>
  )
}
