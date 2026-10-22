'use client'

import { Stage, usePlayer } from './player'
import styles from './Story.module.css'

const phases = [
  {
    name: 'Language property',
    leftLabel: 'a hypothetical Lean proof',
    left: 'Model of TypeScript’s\ntype system',
    rightLabel: 'what the theorem establishes',
    right: 'Type soundness\nfor that model',
    caption: 'A soundness proof for a model of TypeScript would be valuable. It answers a question about the language model.',
  },
  {
    name: 'Compiler port',
    leftLabel: 'existing compiler',
    left: 'TypeScript / JavaScript',
    rightLabel: 'new compiler',
    right: 'Go',
    caption: 'That theorem alone does not tell you whether the Go port preserves inference, diagnostics, or emitted JavaScript. Lean can prove a port correct too, but that takes a separate proof connecting the implementations.',
  },
  {
    name: 'Shared corpus',
    leftLabel: 'existing compiler',
    left: 'Same test program\n↓\nReference result',
    rightLabel: 'Go compiler',
    right: 'Same test program\n↓\nCompare results in CI',
    caption: 'A shared corpus makes compatibility something engineers can check throughout the port. Each disagreement is a concrete case to fix; passing the corpus does not prove agreement on every input.',
  },
]

export function WhyNotLean() {
  const player = usePlayer(phases.length, 6500)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption}>
      <div className={styles.controls}>
        {phases.map((item, index) => (
          <button key={item.name} type="button" className={styles.choice} aria-pressed={player.at === index} onClick={() => player.go(index)}>
            {item.name}
          </button>
        ))}
      </div>
      <div className={styles.slides}>
        <div className={styles.side}>
          <span className={styles.label}>{phase.leftLabel}</span>
          <div className={styles.paper}>{phase.left}</div>
        </div>
        <span className={styles.arrow} aria-hidden="true">→</span>
        <div className={styles.side}>
          <span className={styles.label}>{phase.rightLabel}</span>
          <div className={styles.paper}>{phase.right}</div>
        </div>
      </div>
    </Stage>
  )
}
