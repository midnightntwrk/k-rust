'use client'

// Scene: why developers avoid mutation testing. Illustrative: no tool or code base is measured.

import { Stage, Status, usePlayer } from './player'
import styles from './Story.module.css'

const MUTANTS = 280
// A fixed pseudo-random outcome per mutant, so every replay looks the same.
const outcomes = Array.from({ length: MUTANTS }, (_, index) => ((index * 7919) % 100 < 82 ? 'killed' : 'survived'))
const noise = [
  ['log::debug!("cache miss")', 'log::debug!("")', 'a log message no test reads'],
  ['Vec::with_capacity(16)', 'Vec::with_capacity(17)', 'changes memory use, not behaviour'],
  ['retry_delay_ms: 100', 'retry_delay_ms: 101', 'nobody should test the exact delay'],
  ['if len > 0 { … }', 'if len >= 1 { … }', 'means the same thing; no test can catch it'],
]

const phases = [
  { done: 0, noise: 0, caption: 'A typical tool mutates every operator and constant in the code base: one mutant for each.' },
  { done: 0.2, noise: 0, caption: 'Each mutant means rebuilding and rerunning the test suite. The progress bar crawls.' },
  { done: 0.45, noise: 0, caption: 'Each mutant means rebuilding and rerunning the test suite. The progress bar crawls.' },
  { done: 0.7, noise: 0, caption: 'Then come the survivors, the red squares, and someone has to read every one.' },
  { done: 1, noise: 2, caption: 'Then come the survivors, the red squares, and someone has to read every one.' },
  { done: 1, noise: 4, caption: 'Most of them are noise: nobody should write a test for them, and some can never be caught. Hours of CPU to learn very little. That is the reputation.' },
]

export function MutationReputation() {
  const player = usePlayer(phases.length, [2600, 1600, 1600, 2200, 2400])
  const phase = phases[player.at]
  const shown = Math.round(phase.done * MUTANTS)
  return (
    <Stage player={player} caption={phase.caption} step={false} aside={<Status kind="illustrative" />}>
      <div className={styles.score}>
        <strong>mutating the code</strong>
        <div className={styles.meter} aria-hidden="true">
          <div style={{ width: `${phase.done * 100}%` }} />
        </div>
      </div>
      <div className={styles.dots} aria-hidden="true">
        {outcomes.map((outcome, index) => (
          <i key={index} className={index < shown ? styles[outcome] : undefined} />
        ))}
      </div>
      <div className={styles.junk}>
        {noise.slice(0, phase.noise).map(([from, to, why]) => (
          <div key={from}>
            {from} → {to} <span className={styles.why}>{why}</span>
          </div>
        ))}
      </div>
    </Stage>
  )
}
