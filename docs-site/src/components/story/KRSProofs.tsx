'use client'

// The sum example is a specialization (initial s = 0) of the qualified circular
// claim in src/snippets/claim-circular.rs. Diagrams are explanatory, not CLI output.
// Foundation vs tooling: Chen–Roșu 2608.13306v1 §1; Matching Logic Explained §7;
// Lean's type-system and tactic references. Do not infer a ranking of logical strength.

import { Stage, usePlayer } from './player'
import styles from './Story.module.css'
import proof from './KRSProofs.module.css'

const phases = [
  {
    name: 'One concrete guarantee',
    caption: 'Both tools can prove this kind of property for every nonnegative starting n. KRS already proves a more general version of this sum loop. That covers arbitrary loop counts, rather than just the inputs in a test suite.',
  },
  {
    name: 'How you prove it',
    caption: 'Lean checks a proof against your statement, much as a type checker checks a program. That is its dependent-type approach. KRS uses matching logic: patterns describe possible states, and the proof connects starting states to required outcomes using your execution rules.',
  },
  {
    name: 'What else can you prove?',
    caption: 'Lean gives you a general-purpose environment for developing definitions, theorems, and reusable proofs. KRS’s current interface focuses on execution claims over a specification. Matching logic can express much more; that does not give KRS Lean’s theorem-development tools today.',
  },
  {
    name: 'What success means',
    caption: 'A KRS proof establishes the claim under the specification and its assumptions; it uses the proving backend and solver. Lean normally checks a constructed proof in its kernel. A separate Go implementation still needs validation. If KRS’s search stops incomplete, you have no proof or counterexample.',
  },
]

function Lane({ title, steps, ordered = false }: { title: string; steps: readonly string[]; ordered?: boolean }) {
  const List = ordered ? 'ol' : 'ul'
  return (
    <div className={proof.lane}>
      <strong>{title}</strong>
      <List>
        {steps.map((step) => <li key={step}>{step}</li>)}
      </List>
    </div>
  )
}

export function KRSProofs() {
  const player = usePlayer(phases.length, 8000)
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
      <div className={proof.diagram}>
        {player.at === 0 && (
          <>
            <strong>Does this loop compute the right sum for every nonnegative input?</strong>
            <div className={styles.pair}>
              <div className={styles.panel}>
                <div className={styles.label}>the program, in pseudocode</div>
                <pre>{'total = 0;\nwhile n > 0 {\n    total += n;\n    n -= 1;\n}'}</pre>
              </div>
              <div className={proof.result}>
                <span className={styles.label}>the guarantee to prove</span>
                <strong>Finish with the sum of every number from 1 to the starting n.</strong>
                <span>Including n = 0, where the sum is 0.</span>
              </div>
            </div>
            <a className={styles.note} href="/verification/reachability-claims#circular-claims">See the existing KRS sum-loop claim</a>
          </>
        )}
        {player.at === 1 && (
          <>
            <strong>Same sum, different starting points for the proof</strong>
            <div className={`${styles.pair} ${proof.comparison}`}>
              <Lane title="In Lean" ordered steps={[
                'Define the sum, or a model of this loop.',
                'State the result for every nonnegative input.',
                'Construct a proof using lemmas and induction.',
                'Have the kernel check the proof.',
              ]} />
              <Lane title="In KRS" ordered steps={[
                'Specify how this language executes a loop.',
                'Describe the allowed starting states.',
                'Describe the required finishing states.',
                'Prove the claim using those execution rules.',
              ]} />
            </div>
          </>
        )}
        {player.at === 2 && (
          <>
            <strong>What can you work on today?</strong>
            <div className={`${styles.pair} ${proof.comparison}`}>
              <Lane title="Lean is designed for" steps={[
                'Proving arithmetic and other mathematical theorems.',
                'Defining a type system and proving it sound.',
                'Modeling two compilers and proving they agree.',
              ]} />
              <Lane title="KRS has working examples of" steps={[
                'Proving a result across both branches of a program.',
                'Proving some loops for any allowed input.',
                'Using stated conditions and helper lemmas.',
              ]} />
            </div>
          </>
        )}
        {player.at === 3 && (
          <>
            <strong>Proving the specification does not prove its port</strong>
            <div className={styles.pair}>
              <div className={proof.result}>
                <span className={styles.label}>the sum is proved</span>
                <strong>The specified loop satisfies its contract.</strong>
                <span>The guarantee depends on the rules and assumptions you supplied.</span>
              </div>
              <div className={proof.result}>
                <span className={styles.label}>a new implementation</span>
                <strong>Does the Go version follow those rules?</strong>
                <span>A shared test corpus gives you concrete behavior to check in CI.</span>
              </div>
            </div>
            <a className={styles.note} href="/verification/reachability-claims#capability-boundary">Current proof support, assumptions, and limits</a>
          </>
        )}
      </div>
    </Stage>
  )
}
