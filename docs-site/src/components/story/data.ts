// The introduction's running example: the `plus` specification in story/plus, its corpus and
// its edits (story/story.toml, through the generated story data), and the krs outputs recorded
// for them. A scene that states a fact about these reads it from here, and the helpers throw
// when the source no longer has what a scene shows, so the site build fails instead of drifting.

import manifest from '../../../story/plus/Cargo.toml?raw'
import source from '../../../story/plus/src/lib.rs?raw'
import { storyMutations, storyOutputs, storyTests } from '../../generated/story'

export type Test = (typeof storyTests)[number]
export type Mutation = (typeof storyMutations)[number]
export type RuleName = 'plus_zero' | 'plus_succ'

export const tests: readonly Test[] = storyTests
export const mutations: readonly Mutation[] = storyMutations
export const corpus = tests.filter((test) => !test.climb)
export const specManifest = manifest

// The two rules in the notation the scenes use on paper.
export const paperRules: Record<RuleName, { lhs: string; rhs: string; say: string }> = {
  plus_zero: { lhs: 'plus(zero, n)', rhs: 'n', say: 'Adding zero to a number gives that number.' },
  plus_succ: { lhs: 'plus(s(m), n)', rhs: 's(plus(m, n))', say: 'Adding one more than m gives one more than adding m.' },
}
export const ruleNames: readonly RuleName[] = ['plus_zero', 'plus_succ']

for (const mutation of mutations) {
  if (paperRules[mutation.rule as RuleName]?.rhs !== mutation.displayOld) {
    throw new Error(`story edit ${mutation.id}: display_old must be the paper form of ${mutation.rule}'s right side`)
  }
}

export function output(id: string): string {
  const text = storyOutputs[id]
  if (text === undefined) throw new Error(`no recorded story output ${id}`)
  return text
}

/** The term left in the k cell by a recorded `krs run`. */
export function result(variant: string, testId: string): string {
  const lines = output(`story-${variant}-${testId}`).split('\n')
  const cell = lines.indexOf('<k>')
  if (cell < 0) throw new Error(`story-${variant}-${testId} has no <k> cell`)
  return lines[cell + 1].trim().replace(/ ~> \.K$/, '')
}

export const caught = (mutation: Mutation, test: Test) => result(mutation.id, test.id) !== result('base', test.id)

/** A `// [!region NAME]` of the specification's source, without its markers. */
export function region(name: string): string {
  const start = source.indexOf(`// [!region ${name}]\n`)
  const end = source.indexOf(`// [!endregion ${name}]`)
  if (start < 0 || end < start) throw new Error(`story/plus/src/lib.rs has no region ${name}`)
  return source.slice(start + `// [!region ${name}]\n`.length, end).replace(/\n$/, '')
}
