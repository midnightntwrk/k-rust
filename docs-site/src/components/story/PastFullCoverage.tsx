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
    name: 'Fuzzing',
    what: 'Crafts input values for your program to reach a rule, an error, or a state you specify.',
    caption: 'Fuzzing keeps your program fixed and searches its inputs for a target: an error, an uncovered rule, or a specified state.',
  },
  {
    name: 'Pattern detection',
    what: 'Asks whether any corpus program shows a behaviour, such as a write followed by a read of the same address, even when every rule is already covered.',
    caption: 'Pattern detection looks for a behavior across the corpus, beyond whether every rule fired.',
  },
  {
    name: 'Mutation testing',
    what: 'Asks whether the corpus would notice if the specification were wrong.',
    caption: 'Mutation testing asks whether the corpus would notice a wrong specification. It is also the one developers have learned to avoid.',
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
