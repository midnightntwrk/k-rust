'use client'

// Scene: ways to go meaningfully past 100% coverage, each with its current status.

import { Stage, Status, type StatusKind, usePlayer } from './player'
import styles from './Story.module.css'

const bands: { name: string; what: string; status: StatusKind; caption: string }[] = [
  {
    name: 'Rule coverage',
    what: 'Every rule fired at least once. The floor, not the goal.',
    status: 'available',
    caption: 'Coverage is the floor: every rule fired at least once.',
  },
  {
    name: 'Symbolic execution',
    what: 'Runs the specification on unknown inputs, so one run stands for every input of a shape and can find inputs that reach a rule in a new way.',
    status: 'available',
    caption: 'K already gives you symbolic execution: one run over unknown inputs stands for all of them.',
  },
  {
    name: 'Fuzzing',
    what: "Generates many concrete programs and checks them against the specification's answers.",
    status: 'confirm',
    caption: 'Fuzzing throws many generated programs at the specification and compares answers.',
  },
  {
    name: 'Pattern detection',
    what: 'Asks whether any corpus program shows a behaviour, such as a write followed by a read of the same address, even when every rule is already covered.',
    status: 'development',
    caption: 'On top of the base machinery come two new ways to find what no test exercises. Pattern detection looks for a behaviour across the corpus.',
  },
  {
    name: 'Mutation testing',
    what: 'Asks whether the corpus would notice if the specification were wrong.',
    status: 'development',
    caption: 'Mutation testing asks whether the corpus would notice a wrong specification. It is also the one developers have learned to avoid.',
  },
]

const phases = [
  { upto: bands.length - 1, caption: 'Coverage is where measuring a corpus starts. Each band below goes further, and each is marked with its status today.' },
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
            <Status kind={band.status} />
          </div>
        ))}
      </div>
    </Stage>
  )
}
