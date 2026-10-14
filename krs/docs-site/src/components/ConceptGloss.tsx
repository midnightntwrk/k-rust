import type { ReactNode } from 'react'

import { fiveMinuteConcepts } from '../generated/five-minute-concepts'
import styles from './ConceptGloss.module.css'

type ConceptId = (typeof fiveMinuteConcepts)[number]['id']

export function ConceptGloss({ children, concept }: { children: ReactNode; concept: ConceptId }) {
  const entry = fiveMinuteConcepts.find((candidate) => candidate.id === concept)
  if (!entry) throw new Error(`unknown five-minute concept: ${concept}`)
  const tooltipId = `concept-gloss-${concept}`

  return (
    <span className={styles.root}>
      <a className={styles.trigger} href={entry.route} aria-describedby={tooltipId}>
        {children}
      </a>
      <span className={styles.tooltip} id={tooltipId} role="tooltip">
        <strong>{entry.title}</strong>
        <span>{entry.gloss}</span>
        <span className={styles.destination}>Open the full explanation →</span>
      </span>
    </span>
  )
}
