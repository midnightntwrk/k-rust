'use client'

// The scenes' shared playback: a scene is a list of phases, and the player steps through them.
// Phase 0 is what a reader sees before pressing anything, so every scene is complete at rest.

import { type ReactNode, useEffect, useState } from 'react'

import styles from './Story.module.css'

export type Player = {
  at: number
  playing: boolean
  toggle: () => void
  step: () => void
  reset: () => void
  go: (index: number) => void
}

export function usePlayer(count: number, delay: number | readonly number[]): Player {
  const [at, setAt] = useState(0)
  const [playing, setPlaying] = useState(false)

  useEffect(() => {
    if (!playing) return
    if (at >= count - 1) {
      setPlaying(false)
      return
    }
    const wanted = typeof delay === 'number' ? delay : (delay[at] ?? delay[delay.length - 1])
    const reduce = window.matchMedia('(prefers-reduced-motion: reduce)').matches
    const timer = window.setTimeout(() => setAt((current) => current + 1), reduce ? Math.min(wanted, 600) : wanted)
    return () => window.clearTimeout(timer)
  }, [at, count, delay, playing])

  return {
    at,
    playing,
    toggle: () => {
      if (playing) return setPlaying(false)
      if (at >= count - 1) setAt(0)
      setPlaying(true)
    },
    step: () => {
      setPlaying(false)
      setAt((current) => (current + 1) % count)
    },
    reset: () => {
      setPlaying(false)
      setAt(0)
    },
    go: (index) => {
      setPlaying(false)
      setAt(index)
    },
  }
}

export function Controls({ player, step = true, reset = true, children }: {
  player: Player
  step?: boolean
  reset?: boolean
  children?: ReactNode
}) {
  return (
    <div className={styles.controls}>
      <button type="button" className={styles.primary} onClick={player.toggle}>
        {player.playing ? 'Pause' : 'Play'}
      </button>
      {step && (
        <button type="button" onClick={player.step}>
          Step
        </button>
      )}
      {reset && (
        <button type="button" onClick={player.reset}>
          Reset
        </button>
      )}
      {children}
    </div>
  )
}

export function Stage({ player, caption, step, aside, children }: {
  player: Player
  caption: ReactNode
  step?: boolean
  aside?: ReactNode
  children: ReactNode
}) {
  return (
    <div className={styles.stage}>
      {children}
      <p className={styles.caption} aria-live="polite">
        {caption}
      </p>
      <Controls player={player} step={step}>
        {aside}
      </Controls>
    </div>
  )
}

export type StatusKind = 'available' | 'development' | 'confirm' | 'illustrative'

const statusText: Record<StatusKind, string> = {
  available: 'available',
  development: 'in development',
  confirm: 'status to confirm',
  illustrative: 'illustrative',
}

export function Status({ kind, children }: { kind: StatusKind; children?: ReactNode }) {
  return <span className={`${styles.pill} ${styles[kind]}`}>{children ?? statusText[kind]}</span>
}
