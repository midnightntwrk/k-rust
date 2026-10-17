'use client'

// Scene: the paper specification becomes KRS, one piece at a time. The code on the right is
// the story's real source (story/plus), and each highlight must still be found in it.

import type { ReactNode } from 'react'

import { region, specManifest } from './data'
import { Stage, usePlayer } from './player'
import styles from './Story.module.css'

type Tone = 'a' | 'b' | 'c'
type Mark = { text: string; tone: Tone; within?: string }

const toneClass: Record<Tone, string> = { a: styles.hlA, b: styles.hlB, c: styles.hlC }

/** Wraps each marked substring of `code` in its highlight; throws if one is missing. */
function highlight(code: string, marks: Mark[]): ReactNode[] {
  const ranges = marks
    .map((mark) => {
      const base = mark.within === undefined ? 0 : code.indexOf(mark.within)
      const start = base < 0 ? -1 : code.indexOf(mark.text, base)
      if (start < 0) throw new Error(`story scene: ${JSON.stringify(mark.text)} is no longer in the specification`)
      return { start, end: start + mark.text.length, tone: mark.tone }
    })
    .sort((left, right) => left.start - right.start)
  const parts: ReactNode[] = []
  let at = 0
  for (const range of ranges) {
    parts.push(code.slice(at, range.start))
    parts.push(
      <span key={range.start} className={toneClass[range.tone]}>
        {code.slice(range.start, range.end)}
      </span>,
    )
    at = range.end
  }
  parts.push(code.slice(at))
  return parts
}

const paper = (...pieces: (string | [string, Tone])[]) =>
  pieces.map((piece, index) =>
    typeof piece === 'string' ? piece : (
      <span key={index} className={toneClass[piece[1]]}>
        {piece[0]}
      </span>
    ),
  )

const slides = [
  {
    paper: paper(['zero', 'a'], '\n', ['s(n)', 'b']),
    file: 'src/lib.rs',
    code: highlight(region('constructors'), [{ text: 'Zero()', tone: 'a' }, { text: 'Succ { n: Nat }', tone: 'b' }]),
    caption: 'The two ways to build a number become an enum. Each variant also says how it is written, so programs can say zero and s(…).',
  },
  {
    paper: paper(['plus(m, n)', 'c']),
    file: 'src/lib.rs',
    code: highlight(region('function'), [{ text: 'Plus', tone: 'c' }]),
    caption: 'plus becomes a struct marked as a function of the specification: two arguments, a number as its result, and its written form.',
  },
  {
    paper: paper(['plus(zero, n)', 'a'], ' = ', ['n', 'b']),
    file: 'src/lib.rs',
    code: highlight(region('plus-zero'), [
      { text: 'k::term![Plus(NatSyntax::Zero(), n)]', tone: 'a' },
      { text: 'n', tone: 'b', within: '{\n    n' },
    ]),
    caption: 'Each rule is an ordinary Rust function. The left side of the rule is the pattern in its argument; the right side is its body.',
  },
  {
    paper: paper(['plus(s(m), n)', 'a'], ' = ', ['s(plus(m, n))', 'b']),
    file: 'src/lib.rs',
    code: highlight(region('plus-succ'), [
      { text: 'k::term![Plus(NatSyntax::Succ(m), n)]', tone: 'a' },
      { text: 'NatSyntax::Succ(Plus(m, n))', tone: 'b' },
    ]),
    caption: 'The second rule, the same way. m and n are Rust variables bound by the pattern, as in a match arm.',
  },
  {
    paper: paper(['plus(zero, n)', 'a'], ' = ', ['n', 'b'], '\n', ['plus(s(m), n)', 'a'], ' = ', ['s(plus(m, n))', 'b']),
    file: 'Cargo.toml',
    code: [specManifest.trimEnd()],
    crate: true,
    caption: 'And the specification is a crate. Cargo builds it, rustc type-checks every rule, and it fits into the editor, dependencies and CI a Rust team already uses.',
  },
]

export function SpecIsRust() {
  const player = usePlayer(slides.length, 4200)
  const slide = slides[player.at]
  return (
    <Stage player={player} caption={slide.caption}>
      <div className={styles.slides}>
        <div className={styles.side}>
          <span className={styles.label}>on paper</span>
          <div className={styles.paper}>{slide.paper}</div>
        </div>
        <span className={styles.arrow} aria-hidden="true">
          →
        </span>
        <div className={styles.side}>
          <span className={styles.label}>in KRS: {slide.file}</span>
          <pre className={styles.panel}>{slide.code}</pre>
        </div>
      </div>
      <div className={`${styles.chips} ${slide.crate ? '' : styles.dim}`}>
        <span>cargo check</span>
        <span>rustc type-checks every rule</span>
        <span>your editor's Rust tooling</span>
        <span>Cargo dependencies</span>
        <span>your CI</span>
      </div>
    </Stage>
  )
}
