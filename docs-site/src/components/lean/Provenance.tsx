// Where the lessons' data comes from: the kcore-spec commit the generator read, and whether the
// package files it read were committed there.

import { lean, shortCommit } from './data'
import styles from './Lesson.module.css'

export function Provenance() {
  const inputs = Object.entries(lean.provenance.inputs)
  const pkg = inputs.filter(([name]) => name.startsWith('KcoreSpec/'))
  const uncommitted = pkg.filter(([, input]) => !input.committed).map(([name]) => name)
  return (
    <aside className={styles.provenance}>
      Every listing, goal state and number in the scenes was generated from the kcore-spec Lean package at commit{' '}
      <code title={lean.provenance.kcoreSpecCommit}>{shortCommit}</code> (change <code>{lean.provenance.kcoreSpecChange}</code>), with Lean{' '}
      {lean.provenance.leanVersion}: {pkg.length} package files,{' '}
      {uncommitted.length ? <>of which {uncommitted.length} differed from that commit ({uncommitted.join(', ')})</> : 'all as committed'}, and{' '}
      {inputs.length - pkg.length} other inputs (peano's source and KORE, the review-cone listings, the cost table, the reference-kompile run).
      The package is not yet part of this repository.
    </aside>
  )
}
