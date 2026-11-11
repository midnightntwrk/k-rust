// The course, in order. Each page under pages/lean names one of these lessons by its id.

import { type Lesson, sourceAt } from '../lesson'
import { terms1 } from './c1-terms'
import { signature2 } from './c2-signature'
import { values3 } from './c3-values'
import { matching4 } from './c4-matching'
import { evaluation5 } from './c5-evaluation'
import { lesson1 } from './l1-definition'
import { overview } from './overview'

export const course: readonly Lesson[] = [overview, lesson1, terms1, signature2, values3, matching4, evaluation5]

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
