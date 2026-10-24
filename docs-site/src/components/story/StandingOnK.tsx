'use client'

// Scene: the KRS source beside the K that krs emit-k recorded for it.

import { output, region } from './data'
import { Stage, usePlayer } from './player'
import styles from './Story.module.css'

const groups = [
  { id: 'constructors', label: 'Constructors', k: ['symbol(succ)', 'symbol(zero)'],
    caption: 'Each enum variant becomes a K production: the syntax programs are written in, and the term the parser builds.' },
  { id: 'function', label: 'Function', k: ['symbol(plus)'], caption: 'The struct declares plus as a K function symbol, with its syntax.' },
  { id: 'plus-zero', label: 'plus_zero', k: ['rule plus ( zero'], caption: 'Each rule of the specification becomes a K rule. Rust variables become K variables: n is N:Nat.' },
  { id: 'plus-succ', label: 'plus_succ', k: ['rule plus ( s ('], caption: 'The same for plus_succ. This K text is what every K tool reads, and what the mutation tool edits.' },
]

const krsLines = groups.flatMap((group, index) => [
  ...(index > 0 ? [{ text: '', group: '' }] : []),
  ...region(group.id).split('\n').map((text) => ({ text, group: group.id })),
])
const emitted = output('story-emit-k').split('\n')
const kLines = emitted
  .slice(emitted.findIndex((line) => line.startsWith('module NAT-SYNTAX')))
  .filter((line, index, lines) => !(line === '' && lines[index - 1] === ''))
  .map((text) => ({ text, group: groups.find((group) => group.k.some((needle) => text.includes(needle)))?.id ?? '' }))
for (const group of groups) {
  if (!kLines.some((line) => line.group === group.id)) throw new Error(`story scene: the emitted K has no line for ${group.id}`)
}

function Lines({ lines, lit }: { lines: { text: string; group: string }[]; lit: string }) {
  return (
    <pre className={`${styles.panel} ${styles.lines}`}>
      {lines.map((line, index) => (
        <span key={index} className={line.group === lit ? styles.lit : undefined}>
          {line.text || ' '}
        </span>
      ))}
    </pre>
  )
}

export function StandingOnK() {
  const player = usePlayer(groups.length, 3000)
  const group = groups[player.at]
  return (
    <Stage player={player} caption={group.caption}>
      <div className={styles.controls} role="group" aria-label="Part of the definition">
        {groups.map((candidate, index) => (
          <button key={candidate.id} type="button" className={styles.choice} aria-pressed={index === player.at} onClick={() => player.go(index)}>
            {candidate.label}
          </button>
        ))}
      </div>
      <div className={styles.layers}>
        <div className={styles.side}>
          <span className={styles.label}>src/lib.rs (KRS, excerpt)</span>
          <Lines lines={krsLines} lit={group.id} />
        </div>
        <div className={styles.side}>
          <span className={styles.label}>definition.k from krs emit-k</span>
          <Lines lines={kLines} lit={group.id} />
        </div>
      </div>
    </Stage>
  )
}
