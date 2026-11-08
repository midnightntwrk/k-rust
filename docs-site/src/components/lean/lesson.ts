// What a lesson is: a sequence of scenes on one timeline, each a fixed arrangement of code panes
// and a visual, stepped through by frames of narration. `say` and the texts of questions are
// strings in the small markup of `Md` (Course.tsx): `code`, **strong**, ==key term==, [link](/path).

import type { ReactNode } from 'react'

import type { Source } from './data'

export type Lang = 'k' | 'kore' | 'lean' | 'goal' | 'none'

export type Pane = {
  id: string
  label: string
  source: Source
  lang?: Lang
}

export type Ask = { q: string; options: readonly string[]; answer: number; why: string }

/**
 * An annotation inside a pane. With a `token`, it marks that text on the line and points at it from
 * below. Without one, it captions the block of highlighted lines around `line`, from above.
 */
export type Note = { pane: string; line: number; text: string; token?: string }

export const note = (pane: string, line: number, text: string, token?: string): Note => ({ pane, line, text, token })

export type Frame = {
  /** The connecting thought; what is about one thing on the stage goes in `notes`, on that thing. */
  say?: string
  /** File line numbers to highlight, per pane id. */
  hl?: Record<string, readonly number[]>
  /** Replace a pane's text from this frame on (goal states change as a proof runs). */
  text?: Record<string, Source>
  notes?: readonly Note[]
  /** A question that stops playback until it is answered. */
  ask?: Ask
  /** How long the frame stays when playing; by default it follows the narration's length. */
  ms?: number
}

export type Scene = {
  id: string
  title: string
  /** The panes stay for the whole scene; a change of panes is a new scene. */
  panes?: readonly Pane[]
  frames: readonly Frame[]
  visual?: (at: number) => ReactNode
  /** Where the visual goes when a scene has panes too (default: beside them). */
  arrange?: 'side' | 'wide' | 'top'
}

/** A pane's text at a frame: the last override at or before it. */
export function sourceAt(scene: Scene, pane: Pane, at: number): Source {
  for (let i = at; i >= 0; i -= 1) {
    const override = scene.frames[i].text?.[pane.id]
    if (override) return override
  }
  return pane.source
}

export type Lesson = {
  id: string
  title: string
  /** Absent for the overview. */
  number?: number
  scenes: readonly Scene[]
  quiz?: readonly Ask[]
  /** What the kernel, the build or a harness establishes about what the lesson showed. */
  checked?: readonly string[]
  tryit?: readonly { say: string; cmd?: string }[]
}
