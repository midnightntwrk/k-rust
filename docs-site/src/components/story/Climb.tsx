'use client'

// Scene: let the AI climb. The surviving edit goes back to the AI, which adds the corpus's next
// test; the tool then caches, per edit, the first test that catches it.

import { caught, corpus, mutations, tests } from './data'
import { type MatrixState, MutationMatrix, survives } from './MutationMatrix'
import { Stage, Status, usePlayer } from './player'
import styles from './Story.module.css'

const all = mutations.map((_, index) => index)
const survivor = all.find((index) => survives(index, corpus))
const added = tests.find((test) => test.climb)
if (survivor === undefined || added === undefined) throw new Error('story scene: the climb needs a surviving edit and a test written to catch it')
const edit = mutations[survivor]
const grown = [...corpus, added]
const reachedBy = corpus.filter((test) => (test.rules as readonly string[]).includes(edit.rule)).map((test) => test.id)
const killers = Object.fromEntries(all.map((index) => [index, grown.find((test) => caught(mutations[index], test))!.id]))
const unused = grown.filter((test) => !mutations.some((mutation) => caught(mutation, test))).map((test) => test.id)
const catchesAll = mutations.every((mutation) => caught(mutation, added))
const before = all.filter((index) => !survives(index, corpus)).length
const after = all.filter((index) => !survives(index, grown)).length

const report = [
  `survived: edit ${edit.id.toUpperCase()}`,
  `rule:     ${edit.rule}    ${edit.displayOld}  becomes  ${edit.displayNew}`,
  `reached by tests: ${reachedBy.join(', ')}`,
  'ask: write a program whose result changes under this edit',
].join('\n')
const withAdded = `${report}\n\nAI adds ${added.id}: ${added.program}`
const cache = [
  'cached killers',
  ...all.map((index) => `  edit ${mutations[index].id.toUpperCase()}:  ${killers[index]}`),
  ...unused.map((id) => `${id} catches no edit`),
].join('\n')

const ran = (rows: number) => Object.fromEntries(all.map((index) => [index, rows]))
const phases: { score: number; report: string; state: MatrixState; caption: string }[] = [
  { score: before, report, state: { rows: corpus, columns: all, run: ran(corpus.length), verdict: true },
    caption: 'The surviving edit goes back to the AI as a report: which rule, which edit, and which tests reach that rule.' },
  { score: before, report: withAdded, state: { rows: grown, columns: all, run: ran(corpus.length), fresh: added.id },
    caption: `The AI adds ${added.id} to the corpus, aimed at that gap. The specification computes its expected result, as for every other test.` },
  { score: after, report: withAdded, state: { rows: grown, columns: all, run: ran(grown.length), fresh: added.id, verdict: true },
    caption: `Under edit ${edit.id.toUpperCase()}, ${added.id} gives a different result. Caught. The corpus grew by one test and the score went from ${before} to ${after}.` },
  { score: after, report: cache, state: { rows: grown, columns: all, run: ran(grown.length), verdict: true, killers, unused },
    caption: `Each edit is now tied to the test that catches it. Next time the tool reruns that one test per edit instead of searching again, so no CPU goes to rediscovering what it already knows.${unused.length ? ` ${unused.join(', ')} ${unused.length > 1 ? 'catch' : 'catches'} nothing: cost without benefit.` : ''}${catchesAll ? ` (Here ${added.id} alone would catch every edit.)` : ''}` },
]

export function Climb() {
  const player = usePlayer(phases.length, 3800)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption} aside={<Status kind="development">mutation tool in development</Status>}>
      <div className={styles.score}>
        <strong>
          {phase.score} / {mutations.length} edits caught
        </strong>
        <div className={styles.meter} aria-hidden="true">
          <div style={{ width: `${(phase.score / mutations.length) * 100}%` }} />
        </div>
      </div>
      <pre className={`${styles.panel} ${styles.report}`}>{phase.report}</pre>
      <MutationMatrix state={phase.state} />
    </Stage>
  )
}
