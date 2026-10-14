'use client'

// The tour-minimal browser lesson: an editor seeded from the synced
// fixture mirror, the browser/worker compiler worker, stage progress, and diagnostics
// disclosed in three levels. Browser APIs (WebAssembly, Worker, Cache Storage)
// are touched only inside effects and event handlers, so prerendering renders
// the static shell.

import { type KeyboardEvent, type ReactNode, type RefObject, useCallback, useEffect, useMemo, useRef, useState } from 'react'

import type { KrsCompiler } from '../../../krs/browser/worker/src/controller.ts'
import type { CompileEvent, Diagnostic, MappingClass, Stage } from '../../../krs/browser/worker/src/protocol.ts'
import { packBase } from '../lesson/config'
import {
  EXECUTION_STAGES,
  type ExecutionEvent,
  type ExecutionStage,
  type ExecutionStatus,
  executionStatus,
  type LessonExecutor,
} from '../lesson/execution'
import {
  fetchManifests,
  LessonEnvironmentError,
  type LessonManifests,
  type LoadProgress,
  type StartedCompiler,
  startCompiler,
  unsupportedReason,
} from '../lesson/session'
import { authoredRange, lineColumn, type TextRange } from '../lesson/source-text'
import seed from '../snippets/tour-minimal.rs?raw'
import styles from './BrowserLesson.module.css'

const COMPILER_STAGES: ReadonlyArray<{ id: Stage; label: string }> = [
  { id: 'assets', label: 'Activate pack' },
  { id: 'policy', label: 'Lesson policy' },
  { id: 'expand', label: 'Macro expansion' },
  { id: 'rustc-lesson', label: 'rustc' },
  { id: 'rustc-collector', label: 'Link collector' },
  { id: 'collect', label: 'Collect' },
  { id: 'bundle', label: 'Bundle' },
]

const FAILURE_STAGE_LABEL: Record<Stage, string> = {
  assets: 'Pack activation',
  policy: 'Lesson policy',
  expand: 'Macro expansion',
  'rustc-lesson': 'rustc',
  'rustc-collector': 'rustc (collector link)',
  collect: 'Collector',
  bundle: 'Bundle check',
}

const CLASS_LABEL: Record<MappingClass, string> = {
  'exact-authored': 'exact source range',
  'invocation-level': 'macro call site',
  'generated-only': 'generated code only',
  unmappable: 'no source location',
}

type Phase =
  | { kind: 'static' }
  | { kind: 'unsupported'; reason: string }
  | { kind: 'unconfigured' }
  | { kind: 'manifest' }
  | { kind: 'unavailable'; error: LessonEnvironmentError }
  | { kind: 'idle'; manifests: LessonManifests }
  | { kind: 'loading'; manifests: LessonManifests; progress: LoadProgress | null }
  | { kind: 'load-failed'; manifests: LessonManifests; error: LessonEnvironmentError }
  | { kind: 'ready'; manifests: LessonManifests; started: StartedCompiler }

type StageState = { state: 'running' | 'done' | 'failed'; ms?: number }

interface BuildView {
  generation: number
  /** The exact text that was compiled; diagnostics are positioned against it. */
  source: string
  startedAt: number
  status: 'running' | 'success' | 'failure' | 'cancelled'
  stages: Partial<Record<Stage, StageState>>
  diagnostics: Diagnostic[]
  success?: { bundle: Uint8Array; sha256: string }
  failure?: Extract<CompileEvent, { type: 'failure' }>
  cancelled?: { reason: string; latencyMs: number | null }
  wallMs?: number
}

function formatBytes(bytes: number): string {
  if (bytes >= 1e9) return `${(bytes / 1e9).toFixed(2)} GB`
  if (bytes >= 1e6) return `${(bytes / 1e6).toFixed(0)} MB`
  if (bytes >= 1e3) return `${(bytes / 1e3).toFixed(0)} KB`
  return `${bytes} B`
}

function formatMs(ms: number): string {
  return ms >= 1000 ? `${(ms / 1000).toFixed(1)} s` : `${Math.round(ms)} ms`
}

function plural(count: number, noun: string): string {
  return `${count} ${noun}${count === 1 ? '' : 's'}`
}

/** Level 1: one line naming the stage and the outcome. */
const ENVIRONMENT_OUTCOME: Record<string, string> = {
  'pack-integrity': 'the compiler files could not be verified or loaded',
  'compiler-trap': 'the compiler stopped unexpectedly',
  'collector-trap': 'the collector stopped unexpectedly',
  'out-of-memory': 'out of memory',
  'protocol-mismatch': 'the page and the compiler worker disagree on their protocol',
}

function failureSummary(failure: Extract<CompileEvent, { type: 'failure' }>): string {
  const stage = FAILURE_STAGE_LABEL[failure.stage]
  const environment = ENVIRONMENT_OUTCOME[failure.code]
  if (environment !== undefined) return `${stage}: ${environment}`
  const errors = failure.diagnostics.filter((d) => d.severity === 'error').length
  if (errors > 0) return `${stage}: ${plural(errors, 'error')}`
  return `${stage}: ${failure.message.split('\n')[0]}`
}

function isEnvironmentFailure(failure: Extract<CompileEvent, { type: 'failure' }>): boolean {
  return failure.code in ENVIRONMENT_OUTCOME
}

/** Editor highlights: only authored ranges of exact-authored and invocation-level diagnostics. */
function highlightsFor(build: BuildView | null, source: string): Array<TextRange & { diagnostic: number; mapping: MappingClass }> {
  if (!build || build.source !== source) return []
  const ranges: Array<TextRange & { diagnostic: number; mapping: MappingClass }> = []
  build.diagnostics.forEach((diagnostic, index) => {
    if (diagnostic.authored === null) return
    if (diagnostic.class !== 'exact-authored' && diagnostic.class !== 'invocation-level') return
    const range = authoredRange(source, diagnostic.authored)
    ranges.push({ ...range, end: Math.max(range.end, range.start + 1), diagnostic: index, mapping: diagnostic.class })
  })
  return ranges.sort((a, b) => a.start - b.start)
}

function Editor({
  highlights,
  onChange,
  onCompileShortcut,
  source,
  textareaRef,
}: {
  highlights: Array<TextRange & { diagnostic: number; mapping: MappingClass }>
  onChange: (value: string) => void
  onCompileShortcut: () => void
  source: string
  textareaRef: RefObject<HTMLTextAreaElement | null>
}) {
  const backdropRef = useRef<HTMLPreElement>(null)
  const gutterRef = useRef<HTMLDivElement>(null)
  const lineCount = useMemo(() => source.split('\n').length, [source])

  const syncScroll = () => {
    const area = textareaRef.current
    if (!area) return
    if (backdropRef.current) {
      backdropRef.current.scrollTop = area.scrollTop
      backdropRef.current.scrollLeft = area.scrollLeft
    }
    if (gutterRef.current) gutterRef.current.scrollTop = area.scrollTop
  }

  // The backdrop mirrors the text; marks carry the highlight colours. Overlapping
  // ranges are drawn from the first one that starts, which is enough for a
  // single-file lesson.
  const segments: ReactNode[] = []
  let cursor = 0
  for (const range of highlights) {
    if (range.start < cursor) continue
    segments.push(source.slice(cursor, range.start))
    segments.push(
      <mark
        className={range.mapping === 'exact-authored' ? styles.markExact : styles.markInvocation}
        data-diagnostic={range.diagnostic}
        key={`${range.start}-${range.diagnostic}`}
      >
        {source.slice(range.start, range.end)}
      </mark>,
    )
    cursor = range.end
  }
  segments.push(`${source.slice(cursor)}\n`)

  const onKeyDown = (event: KeyboardEvent<HTMLTextAreaElement>) => {
    if (event.key === 'Enter' && (event.ctrlKey || event.metaKey)) {
      event.preventDefault()
      onCompileShortcut()
    }
  }

  return (
    <div className={styles.editor}>
      <div className={styles.gutter} ref={gutterRef} aria-hidden="true">
        {Array.from({ length: lineCount }, (_, index) => (
          <span key={index}>{index + 1}</span>
        ))}
      </div>
      <div className={styles.surface}>
        <pre className={styles.backdrop} ref={backdropRef} aria-hidden="true">
          {segments}
        </pre>
        <textarea
          aria-label="tour-minimal src/lib.rs"
          autoCapitalize="off"
          autoComplete="off"
          autoCorrect="off"
          className={styles.input}
          data-lesson-editor=""
          onChange={(event) => onChange(event.target.value)}
          onKeyDown={onKeyDown}
          onScroll={syncScroll}
          ref={textareaRef}
          spellCheck={false}
          value={source}
          wrap="off"
        />
      </div>
    </div>
  )
}

function Progress({ progress }: { progress: LoadProgress | null }) {
  const fraction = progress && progress.totalBytes > 0 ? progress.loadedBytes / progress.totalBytes : 0
  return (
    <div className={styles.progress}>
      <progress max={1} value={fraction} />
      <span>
        {progress
          ? `${formatBytes(progress.loadedBytes)} of ${formatBytes(progress.totalBytes)} · ${progress.verifiedAssets} of ${progress.totalAssets} files verified`
          : 'Starting…'}
      </span>
    </div>
  )
}

function DiagnosticItem({
  diagnostic,
  index,
  onSelect,
  source,
}: {
  diagnostic: Diagnostic
  index: number
  onSelect: (diagnostic: Diagnostic) => void
  source: string
}) {
  let location: ReactNode
  if (diagnostic.authored !== null && (diagnostic.class === 'exact-authored' || diagnostic.class === 'invocation-level')) {
    const range = authoredRange(source, diagnostic.authored)
    const start = lineColumn(source, range.start)
    const end = lineColumn(source, range.end)
    location = (
      <button className={styles.location} data-action="select-range" onClick={() => onSelect(diagnostic)} type="button">
        {diagnostic.authored.file}:{start.line}:{start.column}–{end.line}:{end.column}
      </button>
    )
  } else if (diagnostic.class === 'generated-only' && diagnostic.generated !== null) {
    location = (
      <span className={styles.generatedLocation}>
        generated {diagnostic.generated.file}, bytes {diagnostic.generated.start}–{diagnostic.generated.end} (not in your source)
      </span>
    )
  } else {
    location = <span className={styles.generatedLocation}>no source location</span>
  }
  return (
    <li className={styles.diagnostic} data-class={diagnostic.class} data-diagnostic-index={index}>
      <div className={styles.diagnosticHead}>
        <span className={styles.severity} data-severity={diagnostic.severity}>
          {diagnostic.severity}
          {diagnostic.code ? `[${diagnostic.code}]` : ''}
        </span>
        <span className={styles.message}>{diagnostic.message}</span>
      </div>
      <div className={styles.diagnosticMeta}>
        {location}
        <span className={styles.mapping} data-mapping={diagnostic.class}>
          {CLASS_LABEL[diagnostic.class]}
        </span>
        <span className={styles.origin}>{diagnostic.origin}</span>
      </div>
    </li>
  )
}

function RawRecord({ value }: { value: unknown }) {
  return <pre className={styles.raw}>{JSON.stringify(value, null, 2)}</pre>
}

function BuildOutcome({
  build,
  manifests,
  onSelect,
}: {
  build: BuildView
  manifests: LessonManifests
  onSelect: (diagnostic: Diagnostic) => void
}) {
  // The object URL belongs to one bundle; a stale URL (already revoked) is never rendered.
  const [download, setDownload] = useState<{ url: string; bundle: Uint8Array } | null>(null)
  useEffect(() => {
    if (!build.success) return
    const bundle = build.success.bundle
    const url = URL.createObjectURL(new Blob([bundle as Uint8Array<ArrayBuffer>], { type: 'application/json' }))
    setDownload({ url, bundle })
    return () => URL.revokeObjectURL(url)
  }, [build.success])

  if (build.status === 'running') return null
  if (build.status === 'cancelled') {
    return (
      <div className={styles.outcome} data-cancel-latency-ms={build.cancelled?.latencyMs ?? ''} data-outcome="cancelled">
        <p className={styles.summary}>
          Cancelled{build.cancelled?.latencyMs != null ? ` (stopped in ${formatMs(build.cancelled.latencyMs)})` : ''}.
        </p>
      </div>
    )
  }
  if (build.status === 'success' && build.success) {
    const { bundle, sha256 } = build.success
    return (
      <div className={styles.outcome} data-outcome="success">
        <p className={styles.summary}>
          <span className={styles.ok}>Compiled</span> in {formatMs(build.wallMs ?? 0)}: DescriptorBundle of{' '}
          {bundle.byteLength.toLocaleString('en-US')} bytes.
        </p>
        <details className={styles.level}>
          <summary>Bundle details</summary>
          <dl className={styles.facts}>
            <dt>Bundle SHA-256</dt>
            <dd>
              <code data-bundle-sha256={sha256}>{sha256}</code>
            </dd>
            <dt>Pack</dt>
            <dd>
              <code>{manifests.packId}</code>
            </dd>
            <dt>Stages</dt>
            <dd>
              {COMPILER_STAGES.map(({ id, label }) => `${label} ${formatMs(build.stages[id]?.ms ?? 0)}`).join(' · ')}
            </dd>
          </dl>
          {download && download.bundle === bundle ? (
            <a className={styles.download} data-bundle-sha256={sha256} download="descriptor-bundle.json" href={download.url}>
              Save descriptor-bundle.json
            </a>
          ) : null}
        </details>
      </div>
    )
  }
  const failure = build.failure
  if (!failure) return null
  const environment = isEnvironmentFailure(failure)
  return (
    <div className={styles.outcome} data-outcome={environment ? 'environment-failure' : 'failure'}>
      <p className={styles.summary}>
        <span className={environment ? styles.envBadge : styles.errorBadge}>{environment ? 'Environment' : 'Lesson error'}</span>{' '}
        <span data-failure-summary="">{failureSummary(failure)}</span>
      </p>
      <details className={styles.level} open={!environment && failure.diagnostics.length > 0}>
        <summary>{failure.diagnostics.length > 0 ? `Show ${plural(failure.diagnostics.length, 'diagnostic')}` : 'Show details'}</summary>
        {failure.diagnostics.length > 0 ? (
          <ol className={styles.diagnostics}>
            {failure.diagnostics.map((diagnostic, index) => (
              <DiagnosticItem diagnostic={diagnostic} index={index} key={index} onSelect={onSelect} source={build.source} />
            ))}
          </ol>
        ) : (
          <p className={styles.note}>{failure.message}</p>
        )}
        {environment ? (
          <p className={styles.note}>
            This is a problem with the compiler or the browser, not with your definition. Reloading the page verifies the compiler files
            again and replaces any that do not match.
          </p>
        ) : null}
        <details className={styles.level}>
          <summary>Raw record</summary>
          <p className={styles.note}>
            The worker's failure record. A rustc diagnostic's <code>rendered</code> text names the generated file and its coordinates; the
            locations above come from the source map instead.
          </p>
          <RawRecord value={{ pack_id: manifests.packId, ...failure }} />
        </details>
      </details>
    </div>
  )
}

export function BrowserLesson() {
  const [phase, setPhase] = useState<Phase>({ kind: 'static' })
  const [source, setSource] = useState(seed)
  const [build, setBuild] = useState<BuildView | null>(null)
  const textareaRef = useRef<HTMLTextAreaElement>(null)
  const generationRef = useRef(0)
  const cancelAtRef = useRef<number | null>(null)
  const compilerRef = useRef<KrsCompiler | null>(null)
  const execution = useMemo(() => executionStatus(), [])

  const loadManifests = useCallback(() => {
    const reason = unsupportedReason()
    if (reason !== null) return setPhase({ kind: 'unsupported', reason })
    if (packBase === null) return setPhase({ kind: 'unconfigured' })
    setPhase({ kind: 'manifest' })
    fetchManifests(packBase).then(
      (manifests) => setPhase({ kind: 'idle', manifests }),
      (error: unknown) =>
        setPhase({
          kind: 'unavailable',
          error: error instanceof LessonEnvironmentError ? error : new LessonEnvironmentError('manifest', String(error)),
        }),
    )
  }, [])

  useEffect(() => {
    loadManifests()
    return () => {
      compilerRef.current?.dispose()
      compilerRef.current = null
    }
  }, [loadManifests])

  const download = (manifests: LessonManifests) => {
    setPhase({ kind: 'loading', manifests, progress: null })
    let last = 0
    startCompiler(
      manifests,
      (progress) => {
        const now = performance.now()
        if (now - last < 100 && progress.verifiedAssets < progress.totalAssets) return
        last = now
        setPhase((current) => (current.kind === 'loading' ? { ...current, progress } : current))
      },
    ).then(
      (started) => {
        compilerRef.current = started.compiler
        setPhase({ kind: 'ready', manifests, started })
      },
      (error: unknown) =>
        setPhase({
          kind: 'load-failed',
          manifests,
          error: error instanceof LessonEnvironmentError ? error : new LessonEnvironmentError('download', String(error)),
        }),
    )
  }

  const compile = async () => {
    if (phase.kind !== 'ready') return
    const { compiler } = phase.started
    const { lesson } = phase.started
    const text = source
    const events = compiler.compile({ lesson, files: { [lesson.display_file]: text } })
    const generation = compiler.currentGeneration
    generationRef.current = generation
    cancelAtRef.current = null
    const startedAt = performance.now()
    setBuild({ generation, source: text, startedAt, status: 'running', stages: {}, diagnostics: [] })
    const update = (apply: (view: BuildView) => BuildView) =>
      setBuild((current) => (current && current.generation === generation ? apply(current) : current))
    for await (const event of events) {
      // Results of an older generation are discarded.
      if (generationRef.current !== generation) continue
      const now = performance.now()
      if (event.type === 'progress') {
        update((view) => ({
          ...view,
          stages: { ...view.stages, [event.stage]: { state: event.state === 'start' ? 'running' : 'done', ms: event.ms } },
        }))
      } else if (event.type === 'diagnostics') {
        update((view) => ({ ...view, diagnostics: [...view.diagnostics, ...event.entries] }))
      } else if (event.type === 'success') {
        update((view) => ({
          ...view,
          status: 'success',
          success: { bundle: event.bundle, sha256: event.bundleSha256 },
          wallMs: now - startedAt,
        }))
      } else if (event.type === 'failure') {
        update((view) => ({
          ...view,
          status: 'failure',
          failure: event,
          diagnostics: event.diagnostics,
          stages: { ...view.stages, [event.stage]: { state: 'failed', ms: view.stages[event.stage]?.ms } },
          wallMs: now - startedAt,
        }))
      } else if (event.type === 'cancelled') {
        const latencyMs = cancelAtRef.current === null ? null : now - cancelAtRef.current
        update((view) => ({ ...view, status: 'cancelled', cancelled: { reason: event.reason, latencyMs }, wallMs: now - startedAt }))
      }
    }
  }

  const cancel = () => {
    if (phase.kind !== 'ready') return
    cancelAtRef.current = performance.now()
    phase.started.compiler.cancel()
  }

  const reset = () => {
    if (build?.status === 'running') cancel()
    generationRef.current = -1
    setBuild(null)
    setSource(seed)
  }

  const selectDiagnostic = (diagnostic: Diagnostic) => {
    const area = textareaRef.current
    if (!area || diagnostic.authored === null || !build) return
    if (build.source !== source) return
    const range = authoredRange(source, diagnostic.authored)
    area.focus()
    area.setSelectionRange(range.start, range.end)
  }

  const running = build?.status === 'running'
  const ready = phase.kind === 'ready'
  const highlights = highlightsFor(build, source)
  const stale = build !== null && build.status !== 'running' && build.source !== source

  return (
    <section
      aria-label="Browser lesson"
      className={styles.root}
      data-build-generation={build?.generation ?? 0}
      data-build-status={build?.status ?? 'none'}
      data-lesson-phase={phase.kind}
    >
      <PackPanel phase={phase} onDownload={download} onRetry={loadManifests} />

      <div className={styles.fileBar}>
        <span className={styles.fileName}>tests/tour-minimal/src/lib.rs</span>
        <span className={styles.hint}>{ready ? 'Ctrl+Enter compiles' : 'Editable; compiling needs the compiler'}</span>
      </div>
      <Editor
        highlights={highlights}
        onChange={setSource}
        onCompileShortcut={() => {
          if (ready && !running) void compile()
        }}
        source={source}
        textareaRef={textareaRef}
      />

      <div className={styles.controls}>
        <button className={styles.primary} data-action="compile" disabled={!ready || running} onClick={() => void compile()} type="button">
          Compile
        </button>
        <button data-action="cancel" disabled={!running} onClick={cancel} type="button">
          Cancel
        </button>
        <button data-action="reset" disabled={source === seed && build === null} onClick={reset} type="button">
          Reset
        </button>
      </div>

      <ol className={styles.stages} aria-label="Stages">
        {COMPILER_STAGES.map(({ id, label }) => {
          const state = build?.stages[id]
          const status = state?.state ?? (build?.status === 'running' ? 'pending' : build ? 'skipped' : 'idle')
          return (
            <li className={styles.stage} data-stage={id} data-state={status} key={id}>
              <span className={styles.dot} />
              <span>{label}</span>
              {state?.ms !== undefined && state.state !== 'running' ? <span className={styles.ms}>{formatMs(state.ms)}</span> : null}
            </li>
          )
        })}
      </ol>

      {stale ? <p className={styles.note}>The source changed after this compile; highlights are hidden until you compile again.</p> : null}
      {build && phase.kind === 'ready' ? <BuildOutcome build={build} manifests={phase.manifests} onSelect={selectDiagnostic} /> : null}

      <ExecutionPanel
        bundle={build?.status === 'success' && build.success && build.source === source ? { ...build.success, generation: build.generation } : null}
        execution={execution}
        manifests={phase.kind === 'ready' ? phase.manifests : null}
      />
    </section>
  )
}

function PackPanel({
  onDownload,
  onRetry,
  phase,
}: {
  onDownload: (manifests: LessonManifests) => void
  onRetry: () => void
  phase: Phase
}) {
  switch (phase.kind) {
    case 'static':
      return (
        <div className={styles.panel} data-panel="static">
          <p>The interactive lesson starts once this page has loaded in a browser with JavaScript enabled.</p>
        </div>
      )
    case 'unsupported':
      return (
        <div className={`${styles.panel} ${styles.panelWarning}`} data-panel="unsupported">
          <p className={styles.summary}>
            <span className={styles.envBadge}>Environment</span> Unsupported browser.
          </p>
          <p className={styles.note}>{phase.reason}</p>
        </div>
      )
    case 'unconfigured':
      return (
        <div className={`${styles.panel} ${styles.panelWarning}`} data-panel="unconfigured">
          <p className={styles.summary}>The lesson is unavailable in this build of the site.</p>
          <p className={styles.note}>
            The compiler pack is not part of the site; this build was made without a pack location. You can still read and edit the source
            below.
          </p>
        </div>
      )
    case 'manifest':
      return (
        <div className={styles.panel} data-panel="manifest">
          <p>Reading the compiler manifest…</p>
        </div>
      )
    case 'unavailable':
      return (
        <div className={`${styles.panel} ${styles.panelWarning}`} data-panel="unavailable">
          <p className={styles.summary}>
            <span className={styles.envBadge}>Environment</span> The compiler pack is unavailable.
          </p>
          <details className={styles.level}>
            <summary>Show details</summary>
            <p className={styles.note}>{phase.error.message}</p>
          </details>
          <button onClick={onRetry} type="button">
            Try again
          </button>
        </div>
      )
    case 'idle': {
      const { manifests } = phase
      const cached = manifests.cachedAssets === manifests.totalAssets
      return (
        <div className={styles.panel} data-panel="idle">
          <p>
            Compiling runs entirely in this browser: the Rust compiler, the KRS macro expander, and the descriptor collector are WebAssembly
            programs, and your source never leaves the page.
          </p>
          <p className={styles.note}>
            {cached
              ? 'The compiler is already in this browser’s cache; it is verified again before use.'
              : `The compiler is a one-time ${formatBytes(manifests.totalBytes)} download (${manifests.totalAssets} files, each checked against its SHA-256), kept in this browser’s cache for later visits.`}{' '}
            Compiling uses up to about 2 GB of memory.
          </p>
          <button className={styles.primary} data-action="download" onClick={() => onDownload(manifests)} type="button">
            {cached ? 'Load the compiler' : `Download the compiler (${formatBytes(manifests.totalBytes)})`}
          </button>
        </div>
      )
    }
    case 'loading':
      return (
        <div className={styles.panel} data-panel="loading">
          <Progress progress={phase.progress} />
        </div>
      )
    case 'load-failed':
      return (
        <div className={`${styles.panel} ${styles.panelWarning}`} data-panel="load-failed">
          <p className={styles.summary}>
            <span className={styles.envBadge}>Environment</span>{' '}
            {phase.error.kind === 'integrity'
              ? 'A compiler file failed its integrity check.'
              : phase.error.kind === 'worker'
                ? 'The compiler worker did not start.'
                : 'The compiler download failed.'}
          </p>
          <details className={styles.level}>
            <summary>Show details</summary>
            <p className={styles.note}>{phase.error.message}</p>
            <details className={styles.level}>
              <summary>Raw record</summary>
              <RawRecord value={{ kind: phase.error.kind, message: phase.error.message, pack_id: phase.manifests.packId }} />
            </details>
          </details>
          <button data-action="download" onClick={() => onDownload(phase.manifests)} type="button">
            Try again
          </button>
        </div>
      )
    case 'ready': {
      const { started, manifests } = phase
      return (
        <div
          className={`${styles.panel} ${styles.panelReady}`}
          data-from-cache={started.fromCache}
          data-from-network={started.fromNetwork}
          data-release={started.release}
          data-pack-id={manifests.packId}
          data-panel="ready"
          data-ready-ms={Math.round(started.ms)}
          data-replaced={started.replaced.join(' ')}
        >
          <p>
            <span className={styles.ok}>Compiler ready</span> in {formatMs(started.ms)} ·{' '}
            {started.fromNetwork === 0 ? 'from this browser’s cache' : `${started.fromNetwork} of ${manifests.totalAssets} files downloaded`}
          </p>
        </div>
      )
    }
  }
}

interface RunView {
  generation: number
  status: 'running' | 'success' | 'failure' | 'cancelled'
  stages: Partial<Record<ExecutionStage, StageState>>
  diagnostics: Diagnostic[]
  result?: Extract<ExecutionEvent, { type: 'result' }>
  failure?: Extract<ExecutionEvent, { type: 'failure' }>
}

/**
 * The stages after the bundle. With no executor (the k-rust handoff does not exist yet) this shows
 * the stages as not yet available and a disabled Run button; it never shows a
 * result it did not receive from an executor.
 */
function ExecutionPanel({
  bundle,
  execution,
  manifests,
}: {
  bundle: { bundle: Uint8Array; sha256: string; generation: number } | null
  execution: ExecutionStatus
  manifests: LessonManifests | null
}) {
  const [run, setRun] = useState<RunView | null>(null)
  const executorRef = useRef<LessonExecutor | null>(null)
  const abortRef = useRef<AbortController | null>(null)

  useEffect(
    () => () => {
      abortRef.current?.abort()
      executorRef.current?.dispose()
    },
    [],
  )
  useEffect(() => {
    abortRef.current?.abort()
    setRun(null)
  }, [bundle?.sha256, bundle?.generation])

  const start = async () => {
    if (!execution.available || !bundle || !manifests) return
    const abort = new AbortController()
    abortRef.current = abort
    const generation = bundle.generation
    setRun({ generation, status: 'running', stages: {}, diagnostics: [] })
    const update = (apply: (view: RunView) => RunView) => setRun((current) => (current && current.generation === generation ? apply(current) : current))
    try {
      executorRef.current ??= await execution.create({ packBase: manifests.base, packId: manifests.packId })
      const events = executorRef.current.run({ generation, bundle: bundle.bundle, bundleSha256: bundle.sha256, packId: manifests.packId, signal: abort.signal })
      for await (const event of events) {
        if (abort.signal.aborted) break
        if (event.type === 'progress') {
          update((view) => ({ ...view, stages: { ...view.stages, [event.stage]: { state: event.state === 'start' ? 'running' : 'done', ms: event.ms } } }))
        } else if (event.type === 'diagnostics') {
          update((view) => ({ ...view, diagnostics: [...view.diagnostics, ...event.entries] }))
        } else if (event.type === 'result') {
          update((view) => ({ ...view, status: 'success', result: event }))
        } else if (event.type === 'failure') {
          update((view) => ({ ...view, status: 'failure', failure: event, stages: { ...view.stages, [event.stage]: { state: 'failed' } } }))
        } else {
          update((view) => ({ ...view, status: 'cancelled' }))
        }
      }
    } catch (error) {
      update((view) => ({
        ...view,
        status: 'failure',
        failure: { type: 'failure', stage: 'lower', code: 'executor', message: String(error), diagnostics: [] },
      }))
    }
  }

  return (
    <div className={styles.execution} data-execution={execution.available ? 'available' : 'unavailable'}>
      <div className={styles.executionHead}>
        <p className={styles.executionTitle}>{execution.available ? 'Execute' : 'Execute: coming soon'}</p>
        {execution.available ? (
          <div className={styles.controls}>
            <button data-action="run" disabled={!bundle || run?.status === 'running'} onClick={() => void start()} type="button">
              Run
            </button>
            <button data-action="cancel-run" disabled={run?.status !== 'running'} onClick={() => abortRef.current?.abort()} type="button">
              Cancel
            </button>
          </div>
        ) : (
          <button data-action="run" disabled title={execution.reason} type="button">
            Run
          </button>
        )}
      </div>
      <ol className={styles.stages} aria-label="Execution stages">
        {EXECUTION_STAGES.map(({ id, label, detail }) => {
          const state = run?.stages[id]?.state ?? (execution.available ? 'idle' : 'unavailable')
          return (
            <li className={styles.stage} data-stage={id} data-state={state} key={id} title={detail}>
              <span className={styles.dot} />
              <span>{label}</span>
              {execution.available ? null : <span className={styles.soon}>not yet available</span>}
            </li>
          )
        })}
      </ol>
      {execution.available ? null : (
        <p className={styles.note}>
          After the bundle, KRS lowers the definition, k-rust compiles it to KORE, and k-rust executes the initial configuration. Those stages do
          not run in the browser yet, so this lesson stops at the DescriptorBundle and shows no execution result.
        </p>
      )}
      {run?.status === 'success' && run.result ? (
        <div className={styles.outcome} data-outcome="execution-success">
          <p className={styles.summary}>Final configuration</p>
          <pre className={styles.raw}>{run.result.finalConfiguration}</pre>
        </div>
      ) : null}
      {run?.status === 'failure' && run.failure ? (
        <div className={styles.outcome} data-outcome="execution-failure">
          <p className={styles.summary}>
            {EXECUTION_STAGES.find((stage) => stage.id === run.failure!.stage)?.label}:{' '}
            {run.failure.diagnostics.length > 0 ? plural(run.failure.diagnostics.length, 'error') : run.failure.message.split('\n')[0]}
          </p>
          <details className={styles.level}>
            <summary>Show details</summary>
            <ol className={styles.diagnostics}>
              {run.failure.diagnostics.map((diagnostic, index) => (
                <li className={styles.diagnostic} key={index}>
                  <span className={styles.message}>{diagnostic.message}</span> <span className={styles.mapping}>{CLASS_LABEL[diagnostic.class]}</span>
                </li>
              ))}
            </ol>
            <details className={styles.level}>
              <summary>Raw record</summary>
              <RawRecord value={{ pack_id: manifests?.packId, bundle_sha256: bundle?.sha256, ...run.failure }} />
            </details>
          </details>
        </div>
      ) : null}
    </div>
  )
}
