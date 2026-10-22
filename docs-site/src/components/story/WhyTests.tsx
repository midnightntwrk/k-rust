'use client'

// Scene: why test suites matter now. The Bun and TypeScript facts come from the linked pages.

import { Stage, usePlayer } from './player'
import styles from './Story.module.css'

const stories = [
  {
    who: 'Bun',
    diagram: 'Zig ──[ test suites ]──▶ Rust',
    text: 'Bun moved its runtime from Zig to Rust; the rewrite merged in May 2026. The yardstick for the port was its existing test suite, together with the Node.js test suite Bun tracks compatibility against.',
    source: { href: 'https://bun.com/blog/bun-v1.4', label: 'Bun 1.4 release notes' },
  },
  {
    who: 'TypeScript 7',
    diagram: 'TypeScript ──[ ~20,000 tests ]──▶ Go',
    text: "Microsoft's port of the TypeScript compiler to Go is measured against the compiler's roughly 20,000 existing test cases, and reports progress as the cases where the two still disagree.",
    source: { href: 'https://devblogs.microsoft.com/typescript/progress-on-typescript-7-december-2025', label: 'TypeScript blog, December 2025' },
  },
  {
    who: 'test262',
    diagram: 'one suite ──▶ V8 · SpiderMonkey · JavaScriptCore',
    text: 'JavaScript engines measure themselves against test262, the conformance suite of the language specification. A shared suite is how one specification reaches many implementations.',
    source: { href: 'https://github.com/tc39/test262', label: 'tc39/test262' },
  },
  {
    who: 'Performance work',
    diagram: 'corpus ──▶ benchmark ──▶ faster',
    text: 'You can only climb speed against programs you trust to be correct and representative. The corpus comes first; the benchmark is built on it.',
  },
]

const phases = [
  { on: -1, caption: 'Test suites carried some of the biggest moves in software this year. Play walks through each story.' },
  { on: 0, caption: 'Rewrites that used to be unthinkable now happen in weeks, and what makes them safe to ship is a test suite.' },
  { on: 1, caption: 'The same pattern in another language: the old implementation\'s tests define "done" for the new one.' },
  { on: 2, caption: 'A conformance suite is how one specification reaches many implementations.' },
  { on: 3, caption: "And speed work starts from a corpus: you can't measure faster without programs you trust." },
  { on: -1, caption: 'A shared corpus gives a rewrite concrete behavior to preserve and a performance effort programs to measure. The rest of this page is about building that corpus well.' },
]

export function WhyTests() {
  const player = usePlayer(phases.length, 4800)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption}>
      <div className={styles.cards}>
        {stories.map((story, index) => (
          <div
            key={story.who}
            className={`${styles.card} ${phase.on === index ? styles.on : phase.on !== -1 && index > phase.on ? styles.dim : ''}`}
          >
            <span className={styles.who}>{story.who}</span>
            <span className={styles.diagram}>{story.diagram}</span>
            <p>{story.text}</p>
            {story.source && (
              <a className={styles.source} href={story.source.href}>
                {story.source.label}
              </a>
            )}
          </div>
        ))}
      </div>
    </Stage>
  )
}
