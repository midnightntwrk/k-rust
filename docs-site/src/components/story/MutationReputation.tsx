'use client'

// Illustrative timings, compressed for playback. Assume i is an integer.

import { Stage, usePlayer } from './player'
import styles from './MutationReputation.module.css'

const phases = [
  { mutation: 0, completed: 0, running: false, caption: 'Start with a function that returns an order label. Assume i is an integer.' },
  { mutation: 1, completed: 0, running: true, caption: 'Mutation 1 adds zero. Recompile and run the test suite.' },
  { mutation: 1, completed: 1, running: false, caption: 'Five minutes later: every test still passes. Adding zero did not change the result.' },
  { mutation: 2, completed: 1, running: true, caption: 'Restore the original, then try mutation 2: uppercase an already-uppercase string. Compile and run again.' },
  { mutation: 2, completed: 2, running: false, caption: 'Ten minutes, two surviving mutations. Neither changes the result, so no test can distinguish them from the original.' },
]
const delays = [700, 2400, 1200, 2400]
const runs = ['i + 0', '"ORDER ".toUpperCase()']

export function MutationReputation() {
  const player = usePlayer(phases.length, delays)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption}>
      <div className={styles.layout}>
        <div className={styles.editor}>
          <div className={styles.heading}>
            <span>order-label.ts</span>
            <span>{phase.mutation ? `Mutation ${phase.mutation} of 2` : 'Original code'}</span>
          </div>
          <pre className={styles.code}><code>
            <span>const str = <span className={phase.mutation === 2 ? styles.changed : undefined}>"ORDER "{phase.mutation === 2 ? '.toUpperCase()' : ''}</span>;</span>
            <span>const val = <span className={phase.mutation === 1 ? styles.changed : undefined}>i{phase.mutation === 1 ? ' + 0' : ''}</span>;</span>
            <span>return str + val;</span>
          </code></pre>
          <div className={styles.output}>
            <span><span className={styles.outputLabel}>Output</span> <code>i = 7 → "ORDER 7"</code></span>
            <span key={phase.mutation} className={`${styles.unchanged} ${phase.mutation ? styles.pulse : ''}`}>{phase.mutation ? 'unchanged' : 'original result'}</span>
          </div>
        </div>
        <div className={styles.runs}>
          {runs.map((edit, index) => {
            const complete = index < phase.completed
            const running = phase.running && phase.mutation === index + 1
            return (
              <div className={styles.run} key={edit}>
                <div className={styles.runHeading}>
                  <span>Mutation {index + 1} · <code>{edit}</code></span>
                  <span className={complete ? styles.survived : undefined}>{complete ? 'Tests still pass' : running ? 'Compile & run · 5m' : 'Compile & run · waiting'}</span>
                </div>
                <div className={styles.track} role="img" aria-label={`Mutation ${index + 1}: ${complete ? '5-minute compile and test run complete' : running ? '5-minute compile and test run in progress' : 'waiting'}`}>
                  <div key={`${index}-${running}-${complete}`} className={`${styles.fill} ${complete ? styles.complete : running ? styles.running : ''}`} style={{ animationPlayState: player.playing ? 'running' : 'paused' }} />
                </div>
              </div>
            )
          })}
        </div>
      </div>
      <div className={styles.timing}>Illustrative: each 5-minute run plays in 2.4 seconds.</div>
    </Stage>
  )
}
