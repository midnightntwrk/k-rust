'use client'

// The Lean course: one lesson on one stage. One timeline runs through all of a lesson's scenes:
// Play moves on at once and keeps going, at a pace set by how much there is to read, and stops at a
// question; Space, ← and → work anywhere on the page. A lesson's end section appears once its last
// frame has been reached.

import '@fontsource/ibm-plex-sans/400.css'
import '@fontsource/ibm-plex-sans/500.css'
import '@fontsource/ibm-plex-sans/600.css'
import '@fontsource/ibm-plex-sans-condensed/500.css'
import '@fontsource/ibm-plex-sans-condensed/600.css'
import '@fontsource/ibm-plex-mono/400.css'
import '@fontsource/ibm-plex-mono/500.css'
import '@fontsource/ibm-plex-mono/600.css'

import { Fragment, type ReactNode, useCallback, useEffect, useMemo, useRef, useState } from 'react'
import { Link } from 'vocs'

import type { Source } from './data'
import { lean, shortCommit } from './data'
import { course } from './lessons'
import { type Ask, type Frame, type Lang, type Lesson, type Note, type Pane, type Scene, sourceAt } from './lesson'
import styles from './Course.module.css'

// ---- narration markup ------------------------------------------------------------------------

const token = /`[^`]+`|\*\*[^*]+\*\*|==[^=]+==|\[[^\]]+\]\([^)\s]+\)/g

export function Md({ text }: { text: string }): ReactNode {
  const out: ReactNode[] = []
  let at = 0
  for (const match of text.matchAll(token)) {
    const t = match[0]
    if (match.index > at) out.push(text.slice(at, match.index))
    const key = match.index
    if (t.startsWith('`')) out.push(<code key={key}>{t.slice(1, -1)}</code>)
    else if (t.startsWith('**')) out.push(<strong key={key}>{t.slice(2, -2)}</strong>)
    else if (t.startsWith('==')) out.push(<span key={key} className={styles.k}><Md text={t.slice(2, -2)} /></span>)
    else {
      const [, label, href] = /^\[([^\]]+)\]\(([^)]+)\)$/.exec(t)!
      out.push(<Link key={key} to={href}>{label}</Link>)
    }
    at = match.index + t.length
  }
  if (at < text.length) out.push(text.slice(at))
  return out
}

// ---- a small highlighter: K and KORE have no grammar in the site's highlighter ---------------

const keywords: Partial<Record<Lang, ReadonlySet<string>>> = {
  k: new Set(['module', 'endmodule', 'syntax', 'rule', 'configuration', 'imports', 'requires', 'context', 'owise', 'function', 'symbol']),
  kore: new Set(['module', 'endmodule', 'sort', 'symbol', 'axiom', 'hooked-sort', 'hooked-symbol', 'import']),
  lean: new Set([
    'def', 'theorem', 'inductive', 'structure', 'where', 'abbrev', 'private', 'noncomputable', 'by', 'fun', 'match', 'with', 'if', 'then', 'else', 'let', 'have',
    'obtain', 'exact', 'rcases', 'import', 'open', 'namespace', 'end', 'instance', 'deriving', 'mutual', 'section', 'variable', 'exfalso', 'intro', 'cases', 'simp',
    'termination_by', 'structural', 'decide', 'notation', 'axiom', 'sorry', 'Prop', 'Type', 'at', 'show', 'from',
  ]),
}

function tokens(line: string, lang: Lang, inBlock: boolean): { nodes: ReactNode[]; inBlock: boolean } {
  const nodes: ReactNode[] = []
  if (lang === 'none') return { nodes: [line || ' '], inBlock: false }
  if (lang === 'goal') {
    const turn = line.indexOf('⊢')
    if (turn < 0) return { nodes: [line || ' '], inBlock: false }
    return { nodes: [line.slice(0, turn), <span key="t" className={styles.tkTurn}>{line.slice(turn)}</span>], inBlock: false }
  }
  const words = keywords[lang]!
  const comment = lang === 'lean' ? '--' : lang === 'k' ? '//' : '\u0000'
  let i = 0
  let plain = ''
  const flush = () => {
    if (plain) nodes.push(plain)
    plain = ''
  }
  while (i < line.length) {
    if (inBlock) {
      const close = line.indexOf('-/', i)
      const stop = close < 0 ? line.length : close + 2
      nodes.push(<span key={i} className={styles.tkCom}>{line.slice(i, stop)}</span>)
      i = stop
      inBlock = close < 0
      continue
    }
    if (lang === 'lean' && line.startsWith('/-', i)) {
      flush()
      inBlock = true
      continue
    }
    if (line.startsWith(comment, i)) {
      flush()
      nodes.push(<span key={i} className={styles.tkCom}>{line.slice(i)}</span>)
      break
    }
    const c = line[i]
    if (c === '"') {
      let j = i + 1
      while (j < line.length && line[j] !== '"') j += line[j] === '\\' ? 2 : 1
      flush()
      nodes.push(<span key={i} className={styles.tkStr}>{line.slice(i, j + 1)}</span>)
      i = j + 1
      continue
    }
    if (/[0-9]/.test(c) && (i === 0 || /[\s([,=]/.test(line[i - 1]))) {
      let j = i + 1
      while (j < line.length && /[0-9_]/.test(line[j])) j += 1
      if (j >= line.length || !/[A-Za-z]/.test(line[j])) {
        flush()
        nodes.push(<span key={i} className={styles.tkNum}>{line.slice(i, j)}</span>)
        i = j
        continue
      }
    }
    if (/[A-Za-z_]/.test(c)) {
      let j = i + 1
      while (j < line.length && /[A-Za-z0-9_'.-]/.test(line[j])) j += 1
      const word = line.slice(i, j)
      if (words.has(word)) {
        flush()
        nodes.push(<span key={i} className={styles.tkKw}>{word}</span>)
      } else plain += word
      i = j
      continue
    }
    if (lang === 'lean' && /[⇒∀∃↔→←∧∨¬≠≤⊧]/.test(c)) {
      flush()
      nodes.push(<span key={i} className={styles.tkOp}>{c}</span>)
      i += 1
      continue
    }
    plain += c
    i += 1
  }
  flush()
  return { nodes: nodes.length ? nodes : [' '], inBlock }
}

// ---- code panes ------------------------------------------------------------------------------

const reduced = () => typeof window !== 'undefined' && window.matchMedia('(prefers-reduced-motion: reduce)').matches

/** A line of code with the given tokens marked. */
function markedLine(row: string, lang: Lang, inBlock: boolean, marks: readonly string[]): ReactNode {
  if (marks.length === 0) return tokens(row, lang, inBlock).nodes
  const ranges = marks.map((m) => ({ at: row.indexOf(m), end: row.indexOf(m) + m.length })).sort((x, y) => x.at - y.at)
  const out: ReactNode[] = []
  let at = 0
  let state = inBlock
  const piece = (text: string) => {
    const t = tokens(text, lang, state)
    state = t.inBlock
    return t.nodes
  }
  ranges.forEach((r, i) => {
    if (r.at < at) return
    if (r.at > at) out.push(<Fragment key={`b${i}`}>{piece(row.slice(at, r.at))}</Fragment>)
    out.push(<mark key={`m${i}`} className={styles.tokenMark}>{piece(row.slice(r.at, r.end))}</mark>)
    at = r.end
  })
  if (at < row.length) out.push(<Fragment key="rest">{piece(row.slice(at))}</Fragment>)
  return out
}

function NoteRow({ note, row, below }: { note: Note; row: string; below: boolean }) {
  // Under its token, or level with the code it captions; a long line wraps, so the offset is capped.
  const col = note.token ? row.indexOf(note.token) : row.length - row.trimStart().length
  return (
    <div className={styles.noteRow} role="note">
      <span />
      <div style={{ marginLeft: `min(${col}ch, 55%)` }}>
        <div className={`${styles.note} ${below ? styles.noteBelow : styles.noteAbove}`}><Md text={note.text} /></div>
      </div>
    </div>
  )
}

function PaneView({ pane, source, lines, notes }: { pane: Pane; source: Source; lines: readonly number[]; notes: readonly Note[] }) {
  const box = useRef<HTMLDivElement>(null)
  const first = lines.length ? Math.min(...lines) : undefined
  useEffect(() => {
    const el = box.current
    if (!el || first === undefined) return
    const row = el.querySelector<HTMLElement>(`[data-line="${first}"]`)
    if (row) el.scrollTo({ top: Math.max(0, row.offsetTop - 80), behavior: reduced() ? 'auto' : 'smooth' })
  }, [first, source, notes.length])
  const rows = useMemo(() => source.text.split('\n'), [source])
  const states = useMemo(() => {
    let inBlock = false
    return rows.map((row) => {
      const before = inBlock
      inBlock = tokens(row, pane.lang ?? 'lean', inBlock).inBlock
      return before
    })
  }, [rows, pane.lang])
  const set = new Set(lines)
  // A caption goes above the block of highlighted lines its line belongs to.
  const blockStart = (line: number) => {
    let at = line
    while (set.has(at) && set.has(at - 1)) at -= 1
    return at
  }
  const captions = new Map<number, Note[]>()
  const pointers = new Map<number, Note[]>()
  for (const n of notes) {
    const into = n.token ? pointers : captions
    const key = n.token ? n.line : blockStart(n.line)
    into.set(key, [...(into.get(key) ?? []), n])
  }
  return (
    <figure className={`${styles.pane} ${set.size ? styles.dimming : ''}`}>
      <figcaption className={styles.ph}>
        <span>{pane.label}</span>
        <span>{source.file}{source.start > 1 ? ` ${source.start}–${source.start + rows.length - 1}` : ''}</span>
      </figcaption>
      <div className={styles.body} ref={box}>
        {rows.map((row, i) => {
          const line = source.start + i
          const marks = (pointers.get(line) ?? []).map((n) => n.token!)
          // A wrapped line continues further in than the code's own indentation.
          const hang = row.length - row.trimStart().length + 4
          return (
            <Fragment key={line}>
              {captions.get(line)?.map((n) => <NoteRow key={n.text} note={n} row={row} below={false} />)}
              <div data-line={line} className={`${styles.ln} ${set.has(line) ? styles.hl : ''}`}>
                <span className={styles.no} aria-hidden="true">{line}</span>
                <span style={{ paddingLeft: `${hang}ch`, textIndent: `-${hang}ch` }}>{markedLine(row, pane.lang ?? 'lean', states[i], marks)}</span>
              </div>
              {pointers.get(line)?.map((n) => <NoteRow key={n.text} note={n} row={row} below />)}
            </Fragment>
          )
        })}
      </div>
    </figure>
  )
}

function SceneView({ scene, at }: { scene: Scene; at: number }) {
  const frame = scene.frames[at]
  const panes = scene.panes?.length ? (
    <div className={styles.panes}>
      {scene.panes.map((pane) => (
        <PaneView key={pane.id} pane={pane} source={sourceAt(scene, pane, at)} lines={frame.hl?.[pane.id] ?? []} notes={(frame.notes ?? []).filter((n) => n.pane === pane.id)} />
      ))}
    </div>
  ) : null
  if (!scene.visual) return panes
  if (!panes) return <div className={styles.vizFull}>{scene.visual(at)}</div>
  const top = scene.arrange === 'top'
  return (
    <div className={`${styles.sceneBody} ${top ? styles.bodyTop : styles.bodySide}`}>
      <div className={top ? styles.vizTop : scene.arrange === 'wide' ? `${styles.vizSide} ${styles.vizWide}` : styles.vizSide}>{scene.visual(at)}</div>
      {panes}
    </div>
  )
}

// ---- questions -------------------------------------------------------------------------------

function Predict({ ask, prefix, chosen, onChoose }: { ask: Ask; prefix: string; chosen: number | undefined; onChoose: (i: number) => void }) {
  const done = chosen !== undefined
  return (
    <div className={styles.predict}>
      <div className={styles.q}><Md text={prefix + ask.q} /></div>
      <div className={styles.opts}>
        {ask.options.map((option, i) => (
          <button
            key={i}
            type="button"
            className={`${styles.opt} ${done && i === ask.answer ? styles.right : ''} ${done && i === chosen && i !== ask.answer ? styles.wrong : ''}`}
            disabled={done}
            onClick={() => onChoose(i)}
          >
            <Md text={option} />
          </button>
        ))}
      </div>
      {done && <div className={styles.why}><Md text={(chosen === ask.answer ? 'Right. ' : 'Not quite. ') + ask.why} /></div>}
    </div>
  )
}

// ---- the rail --------------------------------------------------------------------------------

const progressKey = 'lean-course-progress'
const themes = ['system', 'light', 'dark'] as const
type Theme = (typeof themes)[number]

function ThemeButton() {
  const [theme, setTheme] = useState<Theme>('system')
  useEffect(() => {
    try {
      const stored = localStorage.getItem('vocs-theme') as Theme | null
      if (stored && themes.includes(stored)) setTheme(stored)
    } catch {}
  }, [])
  const choose = () => {
    const next = themes[(themes.indexOf(theme) + 1) % themes.length]
    setTheme(next)
    try {
      localStorage.setItem('vocs-theme', next)
    } catch {}
    const resolved = next === 'system' ? (window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light') : next
    document.documentElement.setAttribute('data-vocs-theme', resolved)
    document.documentElement.style.colorScheme = resolved
  }
  return <button type="button" className={styles.themeBtn} onClick={choose}>Theme: {theme}</button>
}

const frameCount = (l: Lesson) => l.scenes.reduce((sum, s) => sum + s.frames.length, 0)

function Rail({ current, done }: { current: Lesson; done: Readonly<Record<string, boolean>> }) {
  return (
    <nav className={styles.rail} aria-label="Lessons">
      <Link to="/lean" className={styles.brand}>
        <svg width="26" height="26" viewBox="0 0 24 24" aria-hidden="true">
          <circle cx="12" cy="12" r="12" fill="var(--ink)" />
          <path d="M8 6v12M8 12h9" fill="none" stroke="#EDB100" strokeWidth="2.2" strokeLinecap="round" />
        </svg>
        <div>
          <strong>A K definition in Lean</strong>
          <span>From a K rule to a checked proof</span>
        </div>
      </Link>
      <ol className={styles.lessons}>
        {course.map((l) => {
          const n = l.number === undefined ? '00' : String(l.number).padStart(2, '0')
          return (
            <li key={l.id}>
              <Link to={l.number === undefined ? '/lean' : `/lean/${l.id}`} className={`${styles.row} ${done[l.id] ? styles.done : ''}`} aria-current={l === current ? 'page' : undefined}>
                <span className={styles.n}>{done[l.id] ? '✓' : n}</span>
                <span className={styles.t}>{l.title}</span>
                <span className={styles.m}>{l.scenes.length} scene{l.scenes.length === 1 ? '' : 's'} · {frameCount(l)} steps</span>
              </Link>
            </li>
          )
        })}
      </ol>
      <div className={styles.railFoot}>
        <p>
          Every pane, goal state and number comes from the kcore-spec Lean package at <code title={lean.provenance.kcoreSpecCommit}>{shortCommit}</code>, with Lean {lean.provenance.leanVersion}.
          The package is not yet part of this repository.
        </p>
        <p>Space plays or pauses. ← and → step.</p>
        <div className={styles.railLinks}>
          <Link to="/">← k-rust and KRS</Link>
          <ThemeButton />
        </div>
      </div>
    </nav>
  )
}

// ---- the player ------------------------------------------------------------------------------

/** How long a frame stays while playing: long enough to read what it adds. */
const dwellOf = (frame: Frame, speed: number) => {
  const text = [frame.say ?? '', ...(frame.notes ?? []).map((n) => n.text), frame.ask?.why ?? ''].join(' ')
  const words = text.trim() ? text.trim().split(/\s+/).length : 0
  return (frame.ms ?? 1400 + words * 290) / speed
}

function Player({ lesson, onFinish }: { lesson: Lesson; onFinish: () => void }) {
  const [pos, setPos] = useState({ s: 0, f: 0 })
  const [playing, setPlaying] = useState(false)
  const [speed, setSpeed] = useState(1)
  const [answers, setAnswers] = useState<Record<string, number>>({})
  const [reachedEnd, setReachedEnd] = useState(false)

  const scene = lesson.scenes[pos.s]
  const frame = scene.frames[pos.f]
  const key = `${scene.id}:${pos.f}`
  const lastScene = lesson.scenes.length - 1
  const atEnd = pos.s === lastScene && pos.f === scene.frames.length - 1

  // A deep link names a scene.
  useEffect(() => {
    const open = () => {
      const id = location.hash.slice(1)
      const found = lesson.scenes.findIndex((s) => s.id === id)
      if (found < 0) return
      setPlaying(false)
      setPos((p) => (p.s === found ? p : { s: found, f: 0 }))
    }
    open()
    window.addEventListener('hashchange', open)
    return () => window.removeEventListener('hashchange', open)
  }, [lesson])
  useEffect(() => {
    if (pos.s === 0 && !location.hash) return
    try {
      history.replaceState(history.state, '', `#${scene.id}`)
    } catch {}
  }, [scene.id, pos.s])

  useEffect(() => {
    if (!atEnd) return
    setReachedEnd(true)
    onFinish()
  }, [atEnd, onFinish])

  const forward = useCallback((p: { s: number; f: number }) => {
    if (p.f < lesson.scenes[p.s].frames.length - 1) return { s: p.s, f: p.f + 1 }
    if (p.s < lesson.scenes.length - 1) return { s: p.s + 1, f: 0 }
    return p
  }, [lesson])
  const backward = useCallback((p: { s: number; f: number }) => {
    if (p.f > 0) return { s: p.s, f: p.f - 1 }
    if (p.s > 0) return { s: p.s - 1, f: lesson.scenes[p.s - 1].frames.length - 1 }
    return p
  }, [lesson])

  const answered = answers[key] !== undefined
  useEffect(() => {
    if (!playing) return
    if (frame.ask && !answered) {
      setPlaying(false)
      return
    }
    const dwell = dwellOf(frame, speed)
    const timer = window.setTimeout(() => {
      if (atEnd) setPlaying(false)
      else setPos(forward)
    }, dwell)
    return () => window.clearTimeout(timer)
  }, [playing, pos, speed, frame, answered, atEnd, forward])

  const toggle = useCallback(() => {
    if (playing) return setPlaying(false)
    // Play acts at once: whoever presses it has seen this frame. At the end it starts over.
    setPos(atEnd ? { s: 0, f: 0 } : forward)
    setPlaying(true)
  }, [playing, atEnd, forward])

  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      const target = event.target instanceof Element ? event.target : null
      if (target?.closest('input, select, textarea') || event.altKey || event.ctrlKey || event.metaKey) return
      if (event.key === ' ') {
        if (target?.closest('button, a')) return
        event.preventDefault()
        toggle()
      } else if (event.key === 'ArrowRight') {
        setPlaying(false)
        setPos(forward)
      } else if (event.key === 'ArrowLeft') {
        setPlaying(false)
        setPos(backward)
      }
    }
    document.addEventListener('keydown', onKey)
    return () => document.removeEventListener('keydown', onKey)
  }, [toggle, forward, backward])

  const index = course.indexOf(lesson)
  const next = course[index + 1]
  // While playing, the current segment fills toward the next frame, so waiting is visibly running.
  const waiting = playing && !(frame.ask && !answered)
  const fill = (i: number, s: Scene) => {
    if (i < pos.s) return { width: '100%' }
    if (i > pos.s) return { width: 0 }
    if (!waiting) return { width: `${((pos.f + 1) / s.frames.length) * 100}%` }
    return { width: `${(Math.min(pos.f + 2, s.frames.length) / s.frames.length) * 100}%`, transition: `width ${dwellOf(frame, speed)}ms linear` }
  }

  return (
    <div className={styles.main}>
      <header className={styles.head}>
        <span className={styles.eyebrow}>{lesson.number === undefined ? 'Overview' : `Lesson ${lesson.number} of ${course.length - 1}`}</span>
        <h1 className={styles.title}>{lesson.title}</h1>
        <span className={styles.sceneName}>Scene {pos.s + 1} of {lesson.scenes.length}: <b>{scene.title}</b></span>
      </header>
      <section className={styles.stage} aria-label={scene.title}>
        <div key={scene.id} className={styles.sceneRoot}>
          <SceneView scene={scene} at={pos.f} />
          {/* The connecting thought is an annotation with no target, inside the stage, so the eye stays on what is shown. */}
          <div className={styles.freeSlot} aria-live="polite">
            {frame.say && <div key={pos.f} className={styles.free} role="note"><Md text={frame.say} /></div>}
            {/* Screen readers hear the annotations too; on screen they are in the panes. */}
            <span className={styles.srOnly}>{(frame.notes ?? []).map((n) => n.text.replace(/`/g, '')).join(' ')}</span>
          </div>
        </div>
      </section>
      <div className={styles.controls}>
        <button type="button" className={styles.btn} aria-label="Previous step" disabled={pos.s === 0 && pos.f === 0} onClick={() => { setPlaying(false); setPos(backward) }}>←</button>
        <button type="button" className={`${styles.btn} ${styles.primary}`} onClick={toggle}>{playing ? '❚❚ Pause' : '▶ Play'}</button>
        <button type="button" className={styles.btn} aria-label="Next step" disabled={atEnd} onClick={() => { setPlaying(false); setPos(forward) }}>→</button>
        <div className={styles.timeline} role="group" aria-label="Scenes">
          {lesson.scenes.map((s, i) => (
            <button
              key={s.id}
              type="button"
              className={styles.seg}
              title={s.title}
              aria-label={`Scene ${i + 1}: ${s.title}`}
              aria-current={i === pos.s ? 'step' : undefined}
              onClick={() => { setPlaying(false); setPos({ s: i, f: 0 }) }}
            >
              <i style={fill(i, s)} />
            </button>
          ))}
        </div>
        <select className={styles.speed} aria-label="Playback speed" value={speed} onChange={(e) => setSpeed(Number(e.target.value))}>
          {[0.75, 1, 1.5, 2].map((v) => <option key={v} value={v}>{v}×</option>)}
        </select>
        <span className={styles.counter}>step {pos.f + 1}/{scene.frames.length}</span>
      </div>
      {frame.ask && (
        <section className={styles.narr}>
          <Predict ask={frame.ask} prefix="Predict: " chosen={answers[key]} onChoose={(i) => setAnswers((a) => ({ ...a, [key]: i }))} />
        </section>
      )}
      {reachedEnd && (
        <section className={styles.end}>
          {lesson.quiz?.length ? (
            <>
              <h3>Check yourself</h3>
              <div className={styles.quiz}>
                {lesson.quiz.map((ask, i) => (
                  <Predict key={i} ask={ask} prefix="" chosen={answers[`quiz:${i}`]} onChoose={(c) => setAnswers((a) => ({ ...a, [`quiz:${i}`]: c }))} />
                ))}
              </div>
            </>
          ) : null}
          {lesson.checked?.length ? (
            <>
              <h3>What is checked here</h3>
              <ul>{lesson.checked.map((c, i) => <li key={i}><Md text={c} /></li>)}</ul>
            </>
          ) : null}
          {lesson.tryit?.length ? (
            <>
              <h3>Try it on your machine</h3>
              <div className={styles.tryit}>
                {lesson.tryit.map((t, i) => (
                  <div key={i}>
                    <p><Md text={t.say} /></p>
                    {t.cmd && <pre>{t.cmd}</pre>}
                  </div>
                ))}
              </div>
            </>
          ) : null}
          {next && <Link to={`/lean/${next.id}`} className={`${styles.btn} ${styles.primary}`}>Next: {next.title} →</Link>}
          {!next && <Link to="/lean" className={`${styles.btn} ${styles.primary}`}>Back to the overview</Link>}
        </section>
      )}
    </div>
  )
}

export function LeanCourse({ lesson: id }: { lesson: string }) {
  const lesson = course.find((l) => l.id === id)
  if (!lesson) throw new Error(`lean lessons: no lesson ${id}`)
  const [done, setDone] = useState<Record<string, boolean>>({})
  useEffect(() => {
    try {
      setDone(JSON.parse(localStorage.getItem(progressKey) ?? '{}'))
    } catch {}
  }, [])
  const onFinish = useCallback(() => {
    setDone((d) => {
      if (d[id]) return d
      const next = { ...d, [id]: true }
      try {
        localStorage.setItem(progressKey, JSON.stringify(next))
      } catch {}
      return next
    })
  }, [id])
  return (
    <div className={styles.app}>
      <Rail current={lesson} done={done} />
      <Player key={id} lesson={lesson} onFinish={onFinish} />
    </div>
  )
}
