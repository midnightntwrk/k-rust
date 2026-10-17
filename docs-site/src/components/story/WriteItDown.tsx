'use client'

// Scene: the specification on paper, before any code.

import { paperRules, ruleNames } from './data'
import { Stage, usePlayer } from './player'
import styles from './Story.module.css'

const numbers = ['zero', 's(zero)', 's(s(zero))', 's(s(s(zero)))']
const phases = [
  { numbers: true, rules: -1, caption: 'Numbers are built from two pieces: zero, and s(…), "one more than". Every natural number is zero with some number of s around it.' },
  { numbers: true, rules: 0, caption: 'The specification of plus is two rules, one for each shape the first number can have. If it is zero, the answer is the other number.' },
  { numbers: true, rules: 1, caption: 'If it is one more than some m, the answer is one more than plus(m, n). Together the two rules say what plus means for every pair of numbers.' },
  { numbers: false, rules: 2, caption: 'That is the whole specification. It says what the answer is, not how to compute it quickly.' },
]

export function WriteItDown() {
  const player = usePlayer(phases.length, 3600)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption}>
      <div className={styles.numbers}>
        {numbers.map((term, value) => (
          <div key={term} className={`${styles.number} ${phase.numbers ? '' : styles.dim}`}>
            <span className={styles.value}>{value}</span>
            <span className={styles.term}>{term}</span>
            <span className={styles.beads} aria-hidden="true">
              {value === 0 ? <i className={styles.zero} /> : Array.from({ length: value }, (_, index) => <i key={index} />)}
            </span>
          </div>
        ))}
      </div>
      {ruleNames.map((name, index) => (
        <div key={name} className={`${styles.rule} ${phase.rules < index ? styles.dim : phase.rules === index ? styles.on : ''}`}>
          <div className={styles.body}>
            {paperRules[name].lhs} = {paperRules[name].rhs}
          </div>
          <div className={styles.say}>{paperRules[name].say}</div>
        </div>
      ))}
    </Stage>
  )
}
