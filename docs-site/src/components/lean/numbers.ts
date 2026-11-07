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
  f0Seconds: lean.f0check.seconds,
  f0Minutes: Math.round(lean.f0check.seconds / 60),
  f0Gb: (lean.f0check.peakRssKb / 1024 / 1024).toFixed(1),
  f0Rejections: lean.f0check.rejections,
  f0Controls: lean.f0check.controls,
  peanoF0Seconds: lean.f0check.decisions.peano_F0.seconds,
  emitSeconds: lean.f0check.decisions.emit_peano.seconds,
  rootText: fmt(coneNumbers.root),
  module: (name: string) => {
    const found = user.totals[`KcoreSpec.${name}`]
    if (!found) throw new Error(`lean lessons: no module ${name} in the cone`)
    return found.coneLines
  },
}

const diff = lean.diff21
/** The execution differential: the package's step against krust's and the reference backend's. */
export const diffNumbers = {
  subjects: diff.length,
  configs: fmt(diff.reduce((sum, r) => sum + r.compared, 0)),
  transitions: fmt(diff.reduce((sum, r) => sum + r.transitions, 0)),
  differences: diff.reduce((sum, r) => sum + r.differences + r.errors, 0),
  refSampled: fmt(diff.reduce((sum, r) => sum + r.refSampled, 0)),
  refAgree: fmt(diff.reduce((sum, r) => sum + r.refAgree, 0)),
  refDifferences: diff.reduce((sum, r) => sum + r.refDifferences, 0),
}

/** Lines of peano.k. */
export const peanoLines = lean.peanoK.split('\n').length

const loopLog = lean.loop.log
const loopLast = loopLog.filter((it) => it.verdict === 'retained').at(-1)!
/** The unattended loop run: its start and end, and the targets it was given. */
export const loopNumbers = {
  targets: lean.loop.targets,
  iterations: loopLog.length - 1,
  rejected: loopLog.filter((it) => it.verdict === 'rejected').length,
  start: fmt(loopLog[0].total_kHb),
  end: fmt(loopLast.total_kHb),
  ratio: Math.round(loopLog[0].total_kHb / loopLast.total_kHb),
  negative: lean.loop.negative.length,
  peanoFile: fmt(Math.round(Object.values(lean.heartbeats).reduce((sum, h) => sum + h, 0) / 1000)),
}

const draft = lean.m2Cone.totals
/** The next fragment's draft: its review cone (i) for peano, against the current one. */
export const draftNumbers = {
  total: draft.total.coneLines,
  nowTotal: coneNumbers.total,
}

