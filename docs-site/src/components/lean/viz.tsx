'use client'

// The pictures of the Lean course. SVG elements stay mounted and change attributes, so changes
// and fades are CSS transitions; a tree of a term is laid out from the term itself.

import { createContext, type ReactNode, useContext, useId } from 'react'

import { type Ground, type Pattern, symbol } from './data'
import styles from './Course.module.css'
import { spoken, svgSubs } from './sub'

// Arrow takes its arrowhead from the enclosing Svg, so scenes never name one.
const Marker = createContext('')

export function Svg({ viewBox, label, children }: { viewBox: string; label: string; children: ReactNode }) {
  const id = useId().replace(/[^A-Za-z0-9]/g, '')
  return (
    <div className={styles.svgwrap}>
      <svg viewBox={viewBox} role="img" aria-label={spoken(label)}>
        <defs>
          <marker id={`arr${id}`} viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
            <path d="M0 1L10 5L0 9z" fill="context-stroke" />
          </marker>
        </defs>
        <Marker.Provider value={`url(#arr${id})`}>{children}</Marker.Provider>
      </svg>
    </div>
  )
}

/** A group that fades in and out with the frame. */
export function A({ show = true, children }: { show?: boolean; children: ReactNode }) {
  return <g className={styles.anim} style={{ opacity: show ? 1 : 0 }}>{children}</g>
}

const charW = (size: number) => size * 0.6

const labelWidth = (text: string, size = 13) => text.length * charW(size) + 18

type Tone = 'plain' | 'on' | 'accent' | 'alt' | 'gold' | 'bad' | 'ghost'

const toneFill: Record<Tone, string> = {
  plain: 'var(--code-bg)', on: 'var(--gold-tint)', accent: 'var(--accent-tint)', alt: 'var(--alt-tint)', gold: 'var(--gold-tint)', bad: 'color-mix(in srgb, var(--bad) 14%, var(--raised))', ghost: 'transparent',
}
const toneStroke: Record<Tone, string> = {
  plain: 'var(--line)', on: 'var(--gold)', accent: 'var(--accent)', alt: 'var(--alt)', gold: 'var(--gold)', bad: 'var(--bad)', ghost: 'var(--faint)',
}

/** A labelled box centred on (x, y). */
export function Box({ x, y, text, aside, sub, w, h, tone = 'plain', size = 13, sans = false, dash = false }: {
  /** `aside`: a gloss after the name, in parentheses and smaller, e.g. "(Lean value)". */
  x: number; y: number; text: string; aside?: string; sub?: string; w?: number; h?: number; tone?: Tone; size?: number; sans?: boolean; dash?: boolean
}) {
  const asideSize = size - 1.5
  const width = w ?? Math.max(labelWidth(text, size) + (aside ? (aside.length + 3) * asideSize * 0.52 : 0), sub ? labelWidth(sub, 11) : 0)
  const height = h ?? (sub ? 46 : 30)
  return (
    <g className={styles.anim}>
      <rect className={styles.anim} x={x - width / 2} y={y - height / 2} width={width} height={height} rx={7} fill={toneFill[tone]} stroke={toneStroke[tone]} strokeWidth={tone === 'plain' ? 1 : 1.6} strokeDasharray={dash ? '4 3' : undefined} />
      <text className={sans ? undefined : styles.mono} x={x} y={sub ? y - 4 : y + size * 0.35} textAnchor="middle" fontSize={size} fontWeight={tone === 'plain' ? 400 : 500}>
        {svgSubs(text, size)}
        {aside && <tspan className={styles.sansText} fontSize={asideSize} fontWeight={400} style={{ fill: 'var(--muted)' }}>{` (${aside})`}</tspan>}
      </text>
      {sub && <text x={x} y={y + 13} textAnchor="middle" fontSize={11} style={{ fill: 'var(--muted)' }}>{sub}</text>}
    </g>
  )
}

/** An arrow from (x1, y1) to (x2, y2), with an optional label at its middle. */
export function Arrow({ x1, y1, x2, y2, label, on = false, dash = false, tone, curve = 0 }: {
  x1: number; y1: number; x2: number; y2: number; label?: string; on?: boolean; dash?: boolean; tone?: string; curve?: number
}) {
  const upright = Math.abs(x2 - x1) < Math.abs(y2 - y1)
  const marker = useContext(Marker)
  const stroke = tone ?? (on ? 'var(--gold)' : 'var(--faint)')
  const mx = (x1 + x2) / 2
  const my = (y1 + y2) / 2 + curve
  return (
    <g>
      <path className={styles.anim} d={`M${x1} ${y1} Q${mx} ${my} ${x2} ${y2}`} fill="none" stroke={stroke} strokeWidth={on ? 2.2 : 1.4} strokeDasharray={dash ? '5 4' : undefined} markerEnd={marker} />
      {label && <text className={styles.mono} x={upright ? mx + 10 : mx} y={upright ? my + 4 : my - 7} textAnchor={upright ? 'start' : 'middle'} fontSize={11} style={{ fill: 'var(--muted)' }}>{label}</text>}
    </g>
  )
}

export function Label({ x, y, text, size = 12, anchor = 'start', tone, weight, isMono = false }: { x: number; y: number; text: string; size?: number; anchor?: 'start' | 'middle' | 'end'; tone?: string; weight?: number; isMono?: boolean }) {
  return <text className={isMono ? styles.mono : undefined} x={x} y={y} fontSize={size} textAnchor={anchor} fontWeight={weight} style={tone ? { fill: tone } : undefined}>{svgSubs(text, size)}</text>
}

// ---- a term as a tree ------------------------------------------------------------------------

type TreeNode = { label: string; kind: 'ctor' | 'inj' | 'dv' | 'var' | 'as'; v?: number; path: string; children: TreeNode[] }

export function groundTree(t: Ground, path = 'r'): TreeNode {
  if ('ctor' in t) return { label: symbol(t.ctor), kind: 'ctor', path, children: t.args.map((a, i) => groundTree(a, `${path}.${i}`)) }
  if ('inj' in t) return { label: `inj{${t.inj[0]},${t.inj[1]}}`, kind: 'inj', path, children: [groundTree(t.arg, `${path}.0`)] }
  return { label: `\\dv{${t.dv}}("${t.lit}")`, kind: 'dv', path, children: [] }
}

export function patternTree(p: Pattern, path = 'r'): TreeNode {
  if ('var' in p) return { label: `X${p.var}`, kind: 'var', v: p.var, path, children: [] }
  if ('as' in p) return { label: `#as X${p.as}`, kind: 'as', v: p.as, path, children: [patternTree(p.arg, `${path}.0`)] }
  if ('app' in p) return { label: symbol(p.app), kind: 'ctor', path, children: p.args.map((a, i) => patternTree(a, `${path}.${i}`)) }
  if ('dv' in p) return { label: `\\dv{${p.dv}}("${p.lit}")`, kind: 'dv', path, children: [] }
  return { label: `inj{${p.inj[0]},${p.inj[1]}}`, kind: 'inj', path, children: [patternTree(p.arg, `${path}.0`)] }
}

const leaves = (n: TreeNode): number => (n.children.length ? n.children.reduce((sum, c) => sum + leaves(c), 0) : 1)

const varColor = (v: number) => `var(--v${v % 3})`

/** The tree of a term within a band `w` wide at (x, y). `lit` lists the paths to mark; a path's subtree is marked with it. */
export function Tree({ node, x, y, w, dy = 50, lit = [], fade = false }: { node: TreeNode; x: number; y: number; w: number; dy?: number; lit?: readonly string[]; fade?: boolean }) {
  const out: ReactNode[] = []
  const isLit = (path: string) => lit.includes(path)
  const walk = (n: TreeNode, left: number, width: number, depth: number, parent?: { px: number; py: number }) => {
    // A node stays inside the band even when its label is wider than its share of the leaves.
    const half = labelWidth(n.label, 12) / 2
    const nx = Math.min(Math.max(left + width / 2, x + half + 1), x + w - half - 1)
    const ny = y + depth * dy
    if (parent) {
      out.push(<line key={`e${n.path}`} className={styles.anim} x1={parent.px} y1={parent.py + 14} x2={nx} y2={ny - 14} stroke={isLit(n.path) ? 'var(--gold)' : 'var(--line)'} strokeWidth={isLit(n.path) ? 2 : 1.2} />)
    }
    const on = isLit(n.path)
    const stroke = on ? 'var(--gold)' : n.v !== undefined ? varColor(n.v) : n.kind === 'inj' ? 'var(--alt)' : n.kind === 'dv' ? 'var(--num)' : 'var(--accent)'
    const width2 = labelWidth(n.label, 12)
    out.push(
      <g key={`n${n.path}`}>
        <rect className={styles.anim} x={nx - width2 / 2} y={ny - 14} width={width2} height={28} rx={n.kind === 'var' ? 14 : 6} fill={on ? 'var(--gold-tint)' : 'var(--raised)'} stroke={stroke} strokeWidth={on ? 2.2 : 1.2} />
        <text className={styles.mono} x={nx} y={ny + 4} textAnchor="middle" fontSize={12} fontWeight={on || n.v !== undefined ? 600 : 400} style={n.v !== undefined ? { fill: varColor(n.v) } : undefined}>{n.label}</text>
      </g>,
    )
    let cursor = left
    const total = leaves(n)
    for (const c of n.children) {
      const share = (width * leaves(c)) / total
      walk(c, cursor, share, depth + 1, { px: nx, py: ny })
      cursor += share
    }
  }
  walk(node, x, w, 0)
  return <g style={{ opacity: fade ? 0.42 : 1 }} className={styles.anim}>{out}</g>
}

// ---- a table with rows that light up ----------------------------------------------------------

export function Rows({ head, rows, foot }: {
  head: readonly (string | { text: string; num?: boolean; bar?: boolean })[]
  rows: readonly { key: string; cells: readonly ReactNode[]; state?: 'cur' | 'faded' | undefined }[]
  foot?: readonly ReactNode[]
}) {
  const heads = head.map((h) => (typeof h === 'string' ? { text: h } : h)) as { text: string; num?: boolean; bar?: boolean }[]
  const cls = (i: number) => `${heads[i]?.num ? styles.numc : ''} ${heads[i]?.bar ? styles.barCell : ''}`
  return (
    <div className={styles.tablewrap}>
      <table className={styles.rows}>
        <thead>
          <tr>{heads.map((h, i) => <th key={i} scope="col" className={cls(i)}>{h.text}</th>)}</tr>
        </thead>
        <tbody>
          {rows.map((r) => (
            <tr key={r.key} className={r.state === 'cur' ? styles.cur : r.state === 'faded' ? styles.faded : undefined}>
              {r.cells.map((c, i) => <td key={i} className={cls(i)}>{c}</td>)}
            </tr>
          ))}
        </tbody>
        {foot && (
          <tfoot>
            <tr>{foot.map((c, i) => <td key={i} className={cls(i)}>{c}</td>)}</tr>
          </tfoot>
        )}
      </table>
    </div>
  )
}

/** Columns of items that light up; `lit` names items, or whole columns by title. */
export function Board({ columns, lit = [], cols, big = false }: {
  columns: readonly { title: string; items: readonly { key: string; text: ReactNode }[] }[]
  lit?: readonly string[]
  cols?: number
  /** Larger type, for a board that is the whole stage and has little on it. */
  big?: boolean
}) {
  const any = lit.length > 0
  return (
    <div className={`${styles.board} ${big ? styles.boardBig : ''}`} style={{ gridTemplateColumns: `repeat(${cols ?? columns.length}, minmax(0, 1fr))` }}>
      {columns.map((column) => {
        const whole = lit.includes(column.title)
        const some = column.items.some((item) => lit.includes(item.key))
        return (
          <div key={column.title} className={`${styles.col} ${whole ? styles.lit : ''} ${any && !whole && !some ? styles.dim : ''}`}>
            <h5>{column.title}</h5>
            <ul>
              {column.items.map((item) => (
                <li key={item.key} className={`${lit.includes(item.key) ? styles.lit : ''} ${some && !lit.includes(item.key) ? styles.dim : ''}`}>{item.text}</li>
              ))}
            </ul>
          </div>
        )
      })}
    </div>
  )
}

export function Pill({ tone, children }: { tone: 'ok' | 'alt' | 'gold'; children: ReactNode }) {
  return <span className={`${styles.pill} ${tone === 'ok' ? styles.pillOk : tone === 'alt' ? styles.pillAlt : styles.pillGold}`}>{children}</span>
}

/** A horizontal bar: `pct` of its cell's width. The value it stands for is in the row, in text. */
export function Bar({ pct, title, variant, dim }: { pct: number; title?: string; variant?: 'alt' | 'bad'; dim?: boolean }) {
  return <div className={`${styles.bar} ${variant === 'alt' ? styles.alt : variant === 'bad' ? styles.bad : ''}`} style={{ width: `${pct}%`, opacity: dim ? 0.3 : 1 }} title={title} />
}

export function Legend({ items }: { items: readonly { color: string; text: string }[] }) {
  return (
    <div className={styles.legend}>
      {items.map((item) => <span key={item.text}><i style={{ background: item.color }} />{item.text}</span>)}
    </div>
  )
}

export function Small({ children }: { children: ReactNode }) {
  return <span className={styles.small}>{children}</span>
}

export function Chips({ items, lit }: { items: readonly { key: string; text: ReactNode }[]; lit?: readonly string[] }) {
  return (
    <div className={styles.chips}>
      {items.map((item) => <span key={item.key} className={`${styles.chip} ${lit?.includes(item.key) ? styles.chipOn : lit?.length ? styles.chipOff : ''}`}>{item.text}</span>)}
    </div>
  )
}

export function TextBox({ label, children }: { label: string; children: ReactNode }) {
  return (
    <div className={styles.box}>
      <h5>{label}</h5>
      <div className={styles.termText}>{children}</div>
    </div>
  )
}

export const varClass = (v: number) => [styles.varV0, styles.varV1, styles.varV2][v % 3]

export { styles as courseStyles }
