// Pictures of terms for the scenes: a ground term or a pattern from the generated data, written in
// the notation of data.ts (`symbol`), with a subterm outlined by its position and the variables of
// a pattern coloured by their index, so a pattern and the substitution it gives can be read together.

import type { ReactNode } from 'react'

import { type Binding, type Ground, type Pattern, groundText, symbol } from './data'
import styles from './Lesson.module.css'

/** A position: the argument indices from the root. */
export type Path = readonly number[]

const varClass = [styles.bindA, styles.bindB, styles.bindC]
export const varStyle = (i: number) => varClass[i % varClass.length]

const same = (a: Path, b: Path) => a.length === b.length && a.every((x, i) => x === b[i])

function args(items: ReactNode[]): ReactNode {
  return items.map((item, i) => (
    <span key={i}>
      {i > 0 && ', '}
      {item}
    </span>
  ))
}

export function GroundView({ term, mark, path = [] }: { term: Ground; mark?: Path; path?: Path }): ReactNode {
  let inner: ReactNode
  if ('ctor' in term) {
    inner = term.args.length ? (
      <>
        {symbol(term.ctor)}({args(term.args.map((a, i) => <GroundView key={i} term={a} mark={mark} path={[...path, i]} />))})
      </>
    ) : (
      symbol(term.ctor)
    )
  } else if ('inj' in term) {
    inner = (
      <>
        inj{'{'}
        {term.inj[0]},{term.inj[1]}
        {'}'}(<GroundView term={term.arg} mark={mark} path={[...path, 0]} />)
      </>
    )
  } else {
    inner = `\\dv{${term.dv}}("${term.lit}")`
  }
  return mark && same(mark, path) ? <span className={styles.hl}>{inner}</span> : inner
}

export function PatternView({ term, mark, path = [] }: { term: Pattern; mark?: Path; path?: Path }): ReactNode {
  let inner: ReactNode
  if ('var' in term) {
    inner = <span className={varStyle(term.var)}>X{term.var}</span>
  } else if ('as' in term) {
    inner = (
      <>
        <PatternView term={term.arg} mark={mark} path={[...path, 0]} /> #as <span className={varStyle(term.as)}>X{term.as}</span>
      </>
    )
  } else if ('app' in term) {
    inner = term.args.length ? (
      <>
        {symbol(term.app)}({args(term.args.map((a, i) => <PatternView key={i} term={a} mark={mark} path={[...path, i]} />))})
      </>
    ) : (
      symbol(term.app)
    )
  } else {
    inner = (
      <>
        inj{'{'}
        {term.inj[0]},{term.inj[1]}
        {'}'}(<PatternView term={term.arg} mark={mark} path={[...path, 0]} />)
      </>
    )
  }
  return mark && same(mark, path) ? <span className={styles.hl}>{inner}</span> : inner
}

export function TermBox({ label, children }: { label: ReactNode; children: ReactNode }) {
  return (
    <div className={styles.termBox}>
      <span className={styles.termLabel}>{label}</span>
      <div className={styles.term}>{children}</div>
    </div>
  )
}

/** The bindings of σ, the first `count` of them (all by default). */
export function SubstView({ σ, count }: { σ: readonly Binding[]; count?: number }) {
  const shown = σ.slice(0, count ?? σ.length)
  return (
    <div className={styles.subst}>
      <span className={styles.termLabel}>σ =</span>
      {shown.length === 0 && <span className={styles.small}>(nothing bound yet)</span>}
      {shown.map((b) => (
        <span key={b.var}>
          <span className={varStyle(b.var)}>X{b.var}</span> ↦ {groundText(b.value)}
        </span>
      ))}
    </div>
  )
}
