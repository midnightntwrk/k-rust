import type { ReactNode } from 'react'

import styles from './SortsExample.module.css'

function AnnotatedLine({
  children,
  description,
  id,
  title,
}: {
  children: ReactNode
  description: string
  id: string
  title: string
}) {
  return (
    <span className={`${styles.line} ${styles.annotated}`} tabIndex={0} aria-describedby={id}>
      {children}
      <span className={styles.tooltip} id={id} role="tooltip">
        <strong>{title}</strong>
        <span>{description}</span>
      </span>
    </span>
  )
}

export function SortsExample({
  declaration,
  membership,
}: {
  declaration: string
  membership: string
}) {
  return (
    <pre className={styles.root} aria-label="Annotated KRS sort declarations">
      <code className={styles.code}>
        <span className={styles.line}>
          <span className={styles.macro}>k::sorts!</span> {'{'}
        </span>
        <AnnotatedLine
          id="sort-declaration-gloss"
          title="Declare a subsort"
          description="Declares a new open sort, Value, and two parent edges: every Value term is also an Expr and a KResult."
        >
          {`    ${declaration}`}
        </AnnotatedLine>
        <AnnotatedLine
          id="sort-membership-gloss"
          title="Add existing members"
          description="Does not declare Int or Bool. It adds the existing builtin sorts as members of Value, so their terms are valid wherever Value is expected."
        >
          {`    ${membership}`}
        </AnnotatedLine>
        <span className={styles.line}>{'}'}</span>
      </code>
    </pre>
  )
}
