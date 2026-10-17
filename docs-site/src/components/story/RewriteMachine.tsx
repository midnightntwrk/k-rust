'use client'

// Scene: the rewrite machine, running test t3 through the two rules. The first and last terms
// are checked against the corpus program and the result krs recorded for it.

import type { ReactNode } from 'react'

import { output, paperRules, result, ruleNames, tests } from './data'
import { Stage, usePlayer } from './player'
import styles from './Story.module.css'

// A term: [symbol, arguments, highlight]. `match` outlines the subterm a rule matched; `a` and
// `b` colour what the rule's variables m and n are bound to.
type Tag = 'match' | 'a' | 'b' | undefined
type Term = [string, Term[] | null, Tag]
const zero = (tag?: Tag): Term => ['zero', null, tag]
const s = (term: Term, tag?: Tag): Term => ['s', [term], tag]
const plus = (left: Term, right: Term, tag?: Tag): Term => ['plus', [left, right], tag]

const text = ([symbol, args]: Term): string => (args ? `${symbol}(${args.map(text).join(', ')})` : symbol)

function render(term: Term, key = 0): ReactNode {
  const [symbol, args, tag] = term
  const inner = args ? (
    <>
      {symbol}(
      {args.map((arg, index) => (
        <span key={index}>
          {index > 0 && ', '}
          {render(arg, index)}
        </span>
      ))}
      )
    </>
  ) : (
    symbol
  )
  if (!tag) return inner
  const className = tag === 'match' ? styles.match : tag === 'a' ? styles.hlA : styles.hlB
  return (
    <span key={key} className={className}>
      {inner}
    </span>
  )
}

const bindMN = (
  <>
    <span>
      <span className={styles.hlA}>m</span> ↦ <span className={styles.hlA}>zero</span>
    </span>
    <span>
      <span className={styles.hlB}>n</span> ↦ <span className={styles.hlB}>s(zero)</span>
    </span>
  </>
)
const bindN = (
  <span>
    <span className={styles.hlB}>n</span> ↦ <span className={styles.hlB}>s(zero)</span>
  </span>
)

const phases: { term: Term; rule: number; bind: ReactNode; caption: string }[] = [
  { term: plus(s(zero()), s(zero())), rule: -1, bind: null, caption: "Test t3 sits in the machine's k cell, with the two rules of the specification above it." },
  { term: plus(s(zero('a')), s(zero(), 'b'), 'match'), rule: 1, bind: bindMN, caption: 'plus_succ matches the whole term. Its pattern binds m to zero and n to s(zero).' },
  { term: s(plus(zero('a'), s(zero(), 'b'))), rule: 1, bind: bindMN, caption: 'The term is replaced by the right-hand side, s(plus(m, n)), with the bindings substituted in.' },
  { term: s(plus(zero(), s(zero(), 'b'), 'match')), rule: 0, bind: bindN, caption: 'Now plus_zero matches a subterm inside s(…). Rules apply wherever their pattern fits, not only at the top.' },
  { term: s(s(zero(), 'b')), rule: 0, bind: bindN, caption: 'plus(zero, n) is replaced by n.' },
  { term: s(s(zero())), rule: -1, bind: null, caption: 'No rule matches s(s(zero)), so that is the answer: 2. Both rules fired on the way there. These rules simplify the term rather than step a machine, so krs run reports 0 steps.' },
]

const t3 = tests.find((test) => test.id === 't3')!
if (text(phases[0].term) !== t3.program || text(phases[phases.length - 1].term) !== result('base', 't3')) {
  throw new Error('story scene: the rewrite machine no longer starts from t3 and ends at its recorded result')
}

export function RewriteMachine() {
  const player = usePlayer(phases.length, 2400)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption}>
      <div className={styles.pair}>
        {ruleNames.map((name, index) => (
          <div key={name} className={`${styles.rule} ${phase.rule === index ? styles.on : ''}`}>
            <div className={styles.head}>{name}</div>
            <div className={styles.body}>
              {paperRules[name].lhs} = {paperRules[name].rhs}
            </div>
          </div>
        ))}
      </div>
      <div className={styles.cell}>
        <span className={styles.label}>&lt;k&gt;</span>
        <span className={styles.term}>{render(phase.term)}</span>
        <span className={styles.label}>&lt;/k&gt;</span>
      </div>
      <div className={styles.bindings}>{phase.bind}</div>
      <details className={styles.raw}>
        <summary>What krs run printed</summary>
        <pre className={styles.panel}>{output('story-base-t3').trimEnd()}</pre>
      </details>
    </Stage>
  )
}
