// The course, in order. Each page under pages/lean names one of these lessons by its id.

import { type Lesson, sourceAt } from '../lesson'
import { lesson1 } from './l1-definition'
import { lesson2 } from './l2-logic'
import { lesson3 } from './l3-value'
import { lesson4 } from './l4-step'
import { lesson5 } from './l5-proofs'
import { lesson6 } from './l6-review'
import { lesson7 } from './l7-cheap'
import { lesson8 } from './l8-sound-complete'
import { lesson9 } from './l9-f1'
import { overview } from './overview'

export const course: readonly Lesson[] = [overview, lesson1, lesson2, lesson3, lesson4, lesson5, lesson6, lesson7, lesson8, lesson9]

// A note names a line and perhaps a token by value. Only a lesson's first frame is rendered when the
// site is built, so they are checked here: a stale annotation fails the build, not one frame of a page.
for (const lesson of course) {
  for (const scene of lesson.scenes) {
    scene.frames.forEach((frame, at) => {
      for (const n of frame.notes ?? []) {
        const where = `lean lessons: ${lesson.id}/${scene.id} frame ${at}`
        const pane = scene.panes?.find((p) => p.id === n.pane)
        if (!pane) throw new Error(`${where}: a note names no pane of the scene: ${n.pane}`)
        const src = sourceAt(scene, pane, at)
        const row = src.text.split('\n')[n.line - src.start]
        if (row === undefined) throw new Error(`${where}: ${src.file} has no line ${n.line}`)
        if (n.token && !row.includes(n.token)) throw new Error(`${where}: line ${n.line} of ${src.file} has no ${JSON.stringify(n.token)}: ${row}`)
      }
    })
  }
}
