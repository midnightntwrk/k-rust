'use client'

// A lesson scene: real text in panes (Lean source, KORE, goal states, review-cone output), a list
// of steps that each highlight lines and say one sentence, an optional picture of the current
// step, and check-yourself questions with their answers behind a disclosure.
// Playback is the introduction's player (story/player.tsx) with a speed factor; with the scene
// focused, ←/→ step and Space plays or pauses.

import { type KeyboardEvent, type ReactNode, useEffect, useRef, useState } from 'react'

import { usePlayer } from '../story/player'
import type { Source } from './data'
import styles from './Lesson.module.css'

export type Pane = { id: string; label: string; source: Source; note?: string }

export type Step = {
  say: ReactNode
  /** File line numbers to highlight, per pane id. */
  hl?: Record<string, readonly number[]>
  /** Replace a pane's text from this step on (goal states change as a proof runs). */
  text?: Record<string, Source>
  /** Panes to show at this step (default: all). */
  panes?: readonly string[]
}

export type Question = { q: ReactNode; a: ReactNode }

const speeds = [0.5, 1, 1.5, 2] as const

function PaneView({ pane, source, lines }: { pane: Pane; source: Source; lines: readonly number[] }) {
  const box = useRef<HTMLDivElement>(null)
  const first = lines.length ? Math.min(...lines) : undefined
  useEffect(() => {
    const el = box.current
    if (!el || first === undefined) return
    const row = el.querySelector<HTMLElement>(`[data-line="${first}"]`)
    if (!row) return
    // Scroll the pane, never the page.
    const top = row.offsetTop - el.clientHeight / 3
    el.scrollTo({ top: Math.max(0, top), behavior: window.matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth' })
  }, [first, source])
  const set = new Set(lines)
  const rows = source.text.split('\n')
  return (
    <figure className={styles.pane}>
      <figcaption className={styles.paneHead}>
        <span>{pane.label}</span>
        <span className={styles.paneFile}>
          {source.file}
          {source.start > 1 || source.end < rows.length ? ` ${source.start}–${source.start + rows.length - 1}` : ''}
        </span>
      </figcaption>
      <div className={styles.code} ref={box} tabIndex={-1}>
        {rows.map((row, i) => {
          const line = source.start + i
          return (
            <div key={line} data-line={line} className={`${styles.row} ${set.has(line) ? styles.lit : ''} ${set.size && !set.has(line) ? styles.faded : ''}`}>
              <span className={styles.num} aria-hidden="true">{line}</span>
              <span className={styles.src}>{row || ' '}</span>
            </div>
          )
        })}
      </div>
      {pane.note && <div className={styles.paneNote}>{pane.note}</div>}
    </figure>
  )
}

export function LessonScene({ title, panes, steps, questions = [], visual, delay = 3600 }: {
  title: string
  panes: readonly Pane[]
  steps: readonly Step[]
  questions?: readonly Question[]
  visual?: (at: number) => ReactNode
  delay?: number
}) {
  const [speed, setSpeed] = useState<number>(1)
  const player = usePlayer(steps.length, delay, speed)
  const step = steps[player.at]

  // A pane's text at this step: the last override at or before it.
  const textAt = (pane: Pane): Source => {
    for (let i = player.at; i >= 0; i -= 1) {
      const override = steps[i].text?.[pane.id]
      if (override) return override
    }
    return pane.source
  }

  const onKey = (event: KeyboardEvent<HTMLElement>) => {
    if (event.target instanceof HTMLSelectElement || event.target instanceof HTMLButtonElement && event.key === ' ') return
    if (event.key === 'ArrowRight') {
      event.preventDefault()
      player.next()
    } else if (event.key === 'ArrowLeft') {
      event.preventDefault()
      player.back()
    } else if (event.key === ' ') {
      event.preventDefault()
      player.toggle()
    }
  }

  const shown = panes.filter((pane) => !step.panes || step.panes.includes(pane.id))

  return (
    <section className={styles.scene} aria-label={title} tabIndex={0} onKeyDown={onKey}>
      <header className={styles.sceneHead}>
        <strong>{title}</strong>
        <span className={styles.counter}>
          step {player.at + 1} / {steps.length}
        </span>
      </header>
      {visual && <div className={styles.visual}>{visual(player.at)}</div>}
      {shown.length > 0 && (
        <div className={`${styles.panes} ${shown.length > 1 ? styles.two : ''}`}>
          {shown.map((pane) => (
            <PaneView key={pane.id} pane={pane} source={textAt(pane)} lines={step.hl?.[pane.id] ?? []} />
          ))}
        </div>
      )}
      <p className={styles.say} aria-live="polite">
        {step.say}
      </p>
      <div className={styles.controls}>
        <button type="button" onClick={player.back} disabled={player.at === 0} aria-label="Previous step">
          ←
        </button>
        <button type="button" className={styles.primary} onClick={player.toggle}>
          {player.playing ? 'Pause' : 'Play'}
        </button>
        <button type="button" onClick={player.next} disabled={player.at === steps.length - 1} aria-label="Next step">
          →
        </button>
        <button type="button" onClick={player.reset}>
          Reset
        </button>
        <label className={styles.speed}>
          Speed
          <select value={speed} onChange={(event) => setSpeed(Number(event.target.value))}>
            {speeds.map((s) => (
              <option key={s} value={s}>
                {s}×
              </option>
            ))}
          </select>
        </label>
        <span className={styles.keys}>Focus the scene: ← → step, Space plays</span>
      </div>
      <div className={styles.progress} aria-hidden="true">
        {steps.map((_, i) => (
          <button key={i} type="button" tabIndex={-1} className={i <= player.at ? styles.done : ''} onClick={() => player.go(i)} />
        ))}
      </div>
      {questions.length > 0 && (
        <div className={styles.questions}>
          <div className={styles.qHead}>Check yourself</div>
          {questions.map((question, i) => (
            <details key={i} className={styles.question}>
              <summary>{question.q}</summary>
              <div className={styles.answer}>{question.a}</div>
            </details>
          ))}
        </div>
      )}
    </section>
  )
}

/** A goal state as a pane source: Lean's own printing, numbered from 1. */
export function goalSource(label: string, goals: readonly string[]): Source {
  const text = goals.length ? goals.join('\n\n') : 'no goals'
  return { file: label, start: 1, end: text.split('\n').length, text }
}

/** The lines (1-based) of a goal-state source that contain any of the needles; each needle must occur. */
export function goalLines(src: Source, ...needles: string[]): number[] {
  const rows = src.text.split('\n')
  const out = new Set<number>()
  for (const needle of needles) {
    let found = false
    rows.forEach((row, i) => {
      if (row.includes(needle)) {
        out.add(i + 1)
        found = true
      }
    })
    if (!found) throw new Error(`lean lessons: goal state ${src.file} has no line containing ${JSON.stringify(needle)}`)
  }
  return [...out].sort((a, b) => a - b)
}
