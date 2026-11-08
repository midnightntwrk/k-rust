// Γ_D in prose means Γ with a subscript D (in Lean it is `ΓD`, which has no subscript). These
// render it as one, in HTML and in SVG, and spell it out for screen readers.

import { Fragment, type ReactNode } from 'react'

const pattern = /Γ_([A-Za-z]+)/g

/** `text` with each Γ_X written as Γ with a subscript X. */
export function subs(text: string): ReactNode {
  if (!text.includes('Γ_')) return text
  const out: ReactNode[] = []
  let at = 0
  for (const m of text.matchAll(pattern)) {
    out.push(text.slice(at, m.index) + 'Γ', <sub key={m.index}>{m[1]}</sub>)
    at = m.index + m[0].length
  }
  out.push(text.slice(at))
  return out
}

/** The same inside an SVG `<text>` of font size `size`. */
export function svgSubs(text: string, size: number): ReactNode {
  if (!text.includes('Γ_')) return text
  const out: ReactNode[] = []
  let at = 0
  let down = false
  for (const m of text.matchAll(pattern)) {
    out.push(<tspan key={`t${m.index}`} dy={down ? -size * 0.3 : undefined}>{text.slice(at, m.index) + 'Γ'}</tspan>)
    out.push(<tspan key={`s${m.index}`} dy={size * 0.3} fontSize={size * 0.72}>{m[1]}</tspan>)
    down = true
    at = m.index + m[0].length
  }
  out.push(<Fragment key="end"><tspan dy={-size * 0.3}>{text.slice(at) || '​'}</tspan></Fragment>)
  return out
}

/** For aria labels and live regions. */
export const spoken = (text: string) => text.replace(pattern, 'Γ $1')
