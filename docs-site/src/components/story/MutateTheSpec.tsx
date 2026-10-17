'use client'

// Scene: mutate the specification, with an AI proposing the edits. The edits are the ones in
// story/story.toml; every result shown is the one krs recorded for that edit.

import { corpus, mutations, paperRules, type RuleName, ruleNames } from './data'
import { MutationMatrix, survives } from './MutationMatrix'
import { Stage, Status, usePlayer } from './player'
import styles from './Story.module.css'

const all = mutations.map((_, index) => index)
const survivor = all.find((index) => survives(index, corpus))
if (survivor === undefined) throw new Error('story scene: some edit must survive the corpus')
const edit = mutations[survivor]
const caughtCount = all.filter((index) => !survives(index, corpus)).length
const everyRun = Object.fromEntries(all.map((index) => [index, corpus.length]))

const phases = [
  { ai: 'Reads the two rules of the specification.', proposals: false, mutated: -1, columns: [] as number[], run: {}, verdict: false,
    caption: 'The same corpus, with 100% rule coverage. Now mutate the specification instead of the code: two rules, so only a handful of places to edit.' },
  { ai: 'Proposes edits that would be real mistakes.', proposals: true, mutated: -1, columns: [], run: {}, verdict: false,
    caption: `The AI proposes ${mutations.length} edits, each a plausible misunderstanding of what plus means. No log messages, no buffer sizes.` },
  { ai: `Tries edit ${edit.id.toUpperCase()}.`, proposals: true, mutated: survivor, columns: [survivor], run: {}, verdict: false,
    caption: `Edit ${edit.id.toUpperCase()}: ${edit.label}. Run the corpus against the edited specification and compare each result with the recorded one.` },
  { ai: `Tries edit ${edit.id.toUpperCase()}.`, proposals: true, mutated: survivor, columns: [survivor], run: { [survivor]: corpus.length }, verdict: true,
    caption: `Every result is unchanged, so edit ${edit.id.toUpperCase()} survived, even though every rule is covered. The corpus would not notice a plus that ${edit.why}.` },
  { ai: 'Tries every edit.', proposals: true, mutated: -1, columns: all, run: everyRun, verdict: true,
    caption: `${caughtCount} of ${mutations.length} edits caught: a score for the corpus, and one precise, meaningful gap.` },
]

export function MutateTheSpec() {
  const player = usePlayer(phases.length, 3600)
  const phase = phases[player.at]
  const mutated = phase.mutated >= 0 ? mutations[phase.mutated] : undefined
  return (
    <Stage player={player} caption={phase.caption} aside={<Status kind="development">mutation tool in development</Status>}>
      <div className={styles.ai}>
        <span className={styles.who}>AI</span>
        <span>{phase.ai}</span>
      </div>
      <div className={styles.proposals}>
        {mutations.map((mutation) => (
          <div key={mutation.id} className={`${styles.proposal} ${phase.proposals ? '' : styles.dim}`}>
            <b>{mutation.id.toUpperCase()}</b>
            <span>
              <span className={styles.mono}>{mutation.label}</span>: {mutation.why}
            </span>
          </div>
        ))}
      </div>
      <div className={styles.pair}>
        {ruleNames.map((name: RuleName) => {
          const edited = mutated?.rule === name ? mutated : undefined
          return (
            <div key={name} className={`${styles.rule} ${edited ? styles.mutated : ''}`}>
              <div className={styles.head}>
                <span>{name}</span>
                <span>{edited ? `edit ${edited.id.toUpperCase()}` : ''}</span>
              </div>
              <div className={styles.body}>
                {paperRules[name].lhs} ={' '}
                {edited ? (
                  <>
                    <span className={styles.old}>{edited.displayOld}</span> <span className={styles.new}>{edited.displayNew}</span>
                  </>
                ) : (
                  paperRules[name].rhs
                )}
              </div>
            </div>
          )
        })}
      </div>
      <MutationMatrix state={{ rows: corpus, columns: phase.columns, run: phase.run, verdict: phase.verdict }} />
    </Stage>
  )
}
