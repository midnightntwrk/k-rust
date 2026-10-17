'use client'

// Scene: a test corpus. Each expected result is the one krs recorded for the specification.

import { corpus, result } from './data'
import { Stage, usePlayer } from './player'
import styles from './Story.module.css'

const phases = [
  { ai: 'Writes a first test.', rows: 1, known: 0, fresh: 0, caption: 'A test here is just a program in the language of the specification.' },
  { ai: 'Writes a first test.', rows: 1, known: 1, fresh: 0, caption: 'Its expected result is not guessed. The specification computes it, with the rewrite machine, and it is recorded.' },
  { ai: `Adds ${corpus.length - 1} more.`, rows: corpus.length, known: 1, fresh: corpus.length - 1, caption: 'More tests, same treatment: run each through the specification and record what it gives.' },
  { ai: `Adds ${corpus.length - 1} more.`, rows: corpus.length, known: corpus.length, fresh: -1, caption: 'This is the corpus. Run it against any implementation of plus, in any language, and a difference points to a bug.' },
  { ai: 'Done?', rows: corpus.length, known: corpus.length, fresh: -1, caption: 'Is it enough? Growing the corpus until it pins down the whole specification is the hill-climb, and climbing needs a way to measure it.' },
]

export function Corpus() {
  const player = usePlayer(phases.length, 2900)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption}>
      <div className={styles.ai}>
        <span className={styles.who}>AI</span>
        <span>{phase.ai}</span>
      </div>
      <div className={styles.tableWrap}>
        <table className={styles.table}>
          <thead>
            <tr>
              <th>test program</th>
              <th>expected result, computed by the specification</th>
            </tr>
          </thead>
          <tbody>
            {corpus.slice(0, phase.rows).map((test, index) => (
              <tr key={test.id} className={phase.fresh === index ? styles.fresh : undefined}>
                <td>
                  {test.id} · {test.program}
                </td>
                <td>
                  {index < phase.known ? (
                    <>
                      <span className={`${styles.pill} ${styles.pass}`}>recorded</span>
                      <span className={styles.result}>{result('base', test.id)}</span>
                    </>
                  ) : (
                    <span className={`${styles.pill} ${styles.running}`}>running the specification</span>
                  )}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </Stage>
  )
}
