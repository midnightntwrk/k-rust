// Numbers the Lean lessons quote in prose and in scenes: the review cone's sizes and the cost of
// the kernel check of the emitted KORE. Kept out of the 'use client' scene modules so that the
// pages (server components) can read them.

import { type Cone, fmt, lean } from './data'

export const user = lean.cones.user as Required<Cone> & { raw: string }
export const initCount = user.trusted.reduce((sum, t) => sum + t.count, 0)
export const total = user.totals.total
export const once = ['KcoreSpec.FixedSignature', 'KcoreSpec.Core', 'KcoreSpec.Value', 'KcoreSpec.Evaluation', 'KcoreSpec.Step']
export const perProject = ['KcoreSpec.PeanoCore', 'KcoreSpec.PeanoLibrary', 'KcoreSpec.PeanoProperties']
const sumLines = (mods: readonly string[]) => mods.reduce((sum, m) => sum + (user.totals[m]?.coneLines ?? NaN), 0)
const sumDecls = (mods: readonly string[]) => mods.reduce((sum, m) => sum + (user.totals[m]?.decls ?? NaN), 0)
export const coneNumbers = {
  total: total.coneLines,
  decls: total.decls,
  files: total.fileLines,
  once: sumLines(once),
  onceDecls: sumDecls(once),
  perProject: sumLines(perProject),
  perProjectDecls: sumDecls(perProject),
  init: initCount,
  folded: user.folded,
  theoremsMet: user.theoremsMet,
  emit: lean.cones.emit.totals.total.coneLines,
  emitDecls: lean.cones.emit.totals.total.decls,
  root: lean.cones.root.totals.total.coneLines,
  rootDecls: lean.cones.root.totals.total.decls,
  rootOpaque: lean.cones.rootOpaque.totals.total.coneLines,
}
if (coneNumbers.once + coneNumbers.perProject !== coneNumbers.total) {
  throw new Error('lean lessons: the cone is no longer split into the five shared modules and the three per-project ones')
}

/** Numbers the lesson prose quotes, from the same data as the scenes. */
export const numbers = {
  ...coneNumbers,
  f0Seconds: Math.round(lean.f0check.wallSeconds),
  f0Minutes: Math.round(lean.f0check.wallSeconds / 60),
  f0Gb: (lean.f0check.maxRssKb / 1024 / 1024).toFixed(1),
  rootText: fmt(coneNumbers.root),
  module: (name: string) => {
    const found = user.totals[`KcoreSpec.${name}`]
    if (!found) throw new Error(`lean lessons: no module ${name} in the cone`)
    return found.coneLines
  },
}
