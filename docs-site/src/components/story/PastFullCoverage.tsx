'use client'

// Scene: complementary ways to measure and grow the corpus beyond rule coverage.

import { Stage, usePlayer } from './player'
import styles from './Story.module.css'

const bands: { name: string; what: string; caption: string }[] = [
  {
    name: 'Rule coverage',
    what: 'Every rule fired at least once. The floor, not the goal.',
    caption: 'Coverage is the floor: every rule fired at least once.',
  },
  {
    name: 'Mutation testing',
    what: 'Asks whether the corpus would notice if the specification were wrong.',
    caption: 'First, propose a meaningful mistake and add a test that catches it.',
  },
  {
    name: 'Pattern coverage',
    what: 'Checks whether the corpus exercises chosen patterns across values, states, or several parts of the specification.',
    caption: 'Next, check for patterns of interest and add tests for the ones missing from the corpus.',
  },
  {
    name: 'Targeted fuzzing',
    what: 'Searches input values for an authored program to reach a rule, an error, or a chosen pattern.',
    caption: 'Then, search inputs for a chosen target and replay the witness before adding it to the corpus.',
  },
]

const phases = [
  { upto: bands.length - 1, caption: 'Coverage is where measuring a corpus starts. These tools ask different questions about what your tests exercise and what they would catch.' },
  ...bands.map((band, index) => ({ upto: index, caption: band.caption })),
]

export function PastFullCoverage() {
  const player = usePlayer(phases.length, 3400)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption}>
      <div className={styles.bands}>
        {bands.map((band, index) => (
          <div key={band.name} className={`${styles.band} ${index === 0 ? styles.floor : ''} ${index > phase.upto ? styles.dim : ''}`}>
            <span className={styles.name}>{band.name}</span>
            <span className={styles.what}>{band.what}</span>
          </div>
        ))}
      </div>
    </Stage>
  )
}
