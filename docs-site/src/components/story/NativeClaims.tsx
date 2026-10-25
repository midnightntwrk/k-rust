'use client'

import claimSource from '../../../story/claims/src/lib.rs?raw'
import { output } from './data'
import { Stage, usePlayer } from './player'
import styles from './NativeClaims.module.css'

const start = '// [!region claim]\n'
const end = '// [!endregion claim]'
export const authoredClaim = claimSource.split(start)[1]?.split(end)[0]?.trim()
if (!authoredClaim) throw new Error('story claim: missing authored claim region')
const annotations: Record<string, { label: string; className: string }> = {
  '#[k::claim(all_paths)]': { label: 'claim', className: styles.claimLine },
  'k: [Plus(Succ(Zero()), n)],': { label: 'start condition', className: styles.startLine },
  'k: [Succ(n)],': { label: 'end state', className: styles.endLine },
}
const claimLines = authoredClaim.split('\n').map((text) => ({ text, annotation: annotations[text.trim()] }))
const proofOutput = output('story-prove').trimEnd()
if (!proofOutput.split('\n').includes('NAT-CLAIMS-SPEC.add-one: proven')) throw new Error('story claim: expected a proven add-one claim')

const phases = [
  'Write the requirement once. n stands for any natural number, rather than one chosen test input.',
  'krs prove checks the claim by symbolically evaluating the program with the same rules the interpreter uses.',
  'The claim is proven for every natural number n. Keep requirements fixed while AI proposes changes, and recheck them after each change.',
]

export function NativeProofResult() {
  return (
    <div className={styles.proof}>
      <strong>Native proof · add_one</strong>
      <pre><code>{proofOutput}</code></pre>
    </div>
  )
}

export function ClaimSource({ label = 'A requirement alongside your specification' }: { label?: string }) {
  return (
    <div className={styles.source}>
      <div className={styles.label}>{label}</div>
      <pre><code>{claimLines.map(({ text, annotation }, index) => (
        <span className={`${styles.codeLine} ${annotation?.className ?? ''}`} key={index}>
          <span className={styles.lineText}>{text || '\u00a0'}</span>
          {annotation && <span className={styles.annotation}>{annotation.label}</span>}
        </span>
      ))}</code></pre>
    </div>
  )
}

export function NativeClaims() {
  const player = usePlayer(phases.length, 2400)
  return (
    <Stage player={player} caption={phases[player.at]}>
      <div className={styles.layout}>
        <ClaimSource />
        <div className={styles.execution}>
          <strong>Adding one returns the successor of n.</strong>
          <span className={styles.quantifier}>For every n: Nat</span>
          <ol className={styles.trace} aria-label="Symbolic evaluation of the claim">
            <li><code>plus(s(zero), n)</code></li>
            <li className={player.at >= 1 ? undefined : styles.hidden}><span>↓ plus_succ</span><code>s(plus(zero, n))</code></li>
            <li className={player.at >= 2 ? undefined : styles.hidden}><span>↓ plus_zero</span><code>s(n)</code></li>
          </ol>
          <span className={player.at >= 2 ? styles.proven : styles.pending}>{player.at >= 2 ? '✓ Proven for every n' : 'krs prove · symbolic execution'}</span>
        </div>
      </div>
      <details className={styles.raw}>
        <summary>What krs printed</summary>
        <NativeProofResult />
      </details>
      <a className={styles.link} href="/verification/reachability-claims#readable-claims">Write claims with k::claims! →</a>
    </Stage>
  )
}
