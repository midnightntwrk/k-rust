'use client'

// k2lean generates a Lean model of a specification, rather than claiming that
// matching logic is literally a syntactic subset of Lean's dependent type theory.
// Proof examples: k2lean/demos/claims, ImpTypes, and ImpRel.

import { ClaimSource } from './NativeClaims'
import { Stage, usePlayer } from './player'
import styles from './Story.module.css'
import visual from './SpecificationTools.module.css'

const phases = [
  { name: 'Generate Lean', caption: 'KRS generates Lean code through k2lean: types, functions, execution rules, and proofs connecting them. Work in the compact matching-logic specification, then extend its generated Lean model with your own definitions and proofs.' },
  { name: 'Program properties', caption: 'Keep the claims you authored in KRS. k2lean claims states them as Lean propositions over the generated semantics. Try its claim tactic, add supporting lemmas, or supply a hand-written proof; established bisimulations can also transfer proved claims between specifications.' },
  { name: 'Type soundness', caption: 'Did you forget an execution rule, or accept too much in your type checker? Prove that every well-typed expression is already a value or has a rule that can evaluate it. This checks progress, one part of type soundness.' },
  { name: 'Bisimulation', caption: 'An optimization changes how your specification computes. Use a bisimulation proof to show that the original and optimized specifications preserve corresponding behavior in both directions, so improving the rules does not change what programs mean.' },
]

const sources = [
  { label: 'Explore k2lean', path: '' },
  { label: 'Program-property proofs', path: '/demos/claims' },
  { label: 'See a full type-soundness proof', path: '/demos/ImpTypes' },
  { label: 'See how k2lean relates two specifications', path: '/demos/ImpRel' },
]

function Bisimulation() {
  return (
    <div className={visual.equivalence}>
      <strong className={visual.question}>Does this optimization preserve what programs mean?</strong>
      {['Original spec', 'Spec with optimization applied'].map((label, index) => (
        <div key={label} className={visual.execution}>
          <strong>{label}</strong>
          <div className={visual.executionTrace}>
            <code>Input</code><span aria-hidden="true">→</span>
            <span>{index === 0 ? 'Original rules' : 'Optimized rules'}</span><span aria-hidden="true">→</span>
            <code>Result</code>
          </div>
        </div>
      ))}
      <div className={visual.proofGoal}>Prove matching behavior in both directions.</div>
    </div>
  )
}

export function LeanBridge() {
  const player = usePlayer(phases.length, 5000)
  return (
    <Stage player={player} caption={phases[player.at].caption}>
      <div className={styles.controls}>
        {phases.map((phase, index) => (
          <button key={phase.name} type="button" className={styles.choice} aria-pressed={player.at === index} onClick={() => player.go(index)}>{phase.name}</button>
        ))}
      </div>
      <div className={visual.leanScene}>
        {player.at === 0 && (
          <div className={visual.embedding}>
            <div className={visual.generator}><strong>KRS crate</strong><span>k2lean →</span></div>
            <div className={visual.leanCircle}>
              <div className={visual.leanLabel}><strong>Lean</strong><span>Dependent type theory</span></div>
              <span className={visual.ownProofs}>Your own<br />Lean proofs</span>
              <div className={visual.matchingCircle}><strong>Matching logic</strong><span>Your specification</span></div>
            </div>
          </div>
        )}
        {player.at === 1 && (
          <div className={visual.property}>
            <ClaimSource label="The claim you already authored" />
            <div className={visual.guarantee}><code>k2lean claims</code><span aria-hidden="true">↓</span><strong>The same claim, as a Lean proposition.</strong><span>Use the claim tactic or supply your own proof.</span></div>
          </div>
        )}
        {player.at === 2 && (
          <div className={visual.soundness}>
            <strong className={visual.question}>Your type checker accepts more than your execution rules handle.</strong>
            <div className={visual.typingPromise}>Our typing rule accepts <code>Value + Value</code>, where <code>Value</code> includes integers and booleans.</div>
            <div className={styles.panel}>
              <div className={styles.label}>KRS excerpts: the expression shape and its execution rule</div>
              <pre>{'Add { lhs: Value, rhs: Value }\n\neval_add:\n  Add { lhs, rhs } => lhs + rhs\n  where lhs: Int, rhs: Int;'}</pre>
            </div>
            <table className={visual.typeCases}>
              <thead><tr><th scope="col">Expression</th><th scope="col">Type checker</th><th scope="col">Execution</th></tr></thead>
              <tbody>
                <tr><th scope="row"><code>1 + 2</code></th><td>Accepted</td><td><code>3</code></td></tr>
                <tr><th scope="row"><code>true + false</code></th><td>Accepted</td><td className={visual.missingRule}>No rule applies</td></tr>
              </tbody>
            </table>
          </div>
        )}
        {player.at === 3 && <Bisimulation />}
      </div>
      <a className={styles.note} href={`https://github.com/midnightntwrk/k-rust/tree/main/k2lean${sources[player.at].path}`} target="_blank" rel="noreferrer">{sources[player.at].label} ↗</a>
    </Stage>
  )
}
