// Loading the browser lesson from a content-addressed release (IR-21 layout:
// index.json -> releases/<sha256>.json -> blobs/<sha256>.<ext>) through
// PackCache, then starting the compiler with workers that read the verified
// assets from the release's Cache Storage namespace themselves (IR-20).
// Everything here runs only in the browser, from effects or event handlers.

import {
  type CacheEvent,
  KrsCompiler,
  PackCache,
  PackCacheError,
  PackIntegrityError,
  type ReleasePreview,
} from '../../../browser/worker/src/controller.ts'
import type { LessonManifest, PackManifest } from '../../../browser/worker/src/protocol.ts'
import { LESSON_ID, workerUrl } from './config'

/** An environment failure: distinct from errors in the learner's source. */
export class LessonEnvironmentError extends Error {
  readonly kind: 'unsupported' | 'manifest' | 'download' | 'integrity' | 'worker'
  readonly detail: unknown
  constructor(kind: LessonEnvironmentError['kind'], message: string, detail: unknown = null) {
    super(message)
    this.name = 'LessonEnvironmentError'
    this.kind = kind
    this.detail = detail
  }
}

/** Why this browser cannot run the lesson, or null. */
export function unsupportedReason(): string | null {
  if (typeof WebAssembly !== 'object') return 'This browser has no WebAssembly support.'
  if (typeof Worker !== 'function') return 'This browser has no Web Worker support.'
  if (!window.isSecureContext || !globalThis.crypto?.subtle) {
    return 'The lesson needs a secure context (HTTPS or localhost) to verify the compiler files.'
  }
  if (typeof caches === 'undefined') return 'The lesson needs Cache Storage, which this browser does not offer here (for example in a private window).'
  return null
}

function classify(error: unknown, fallback: LessonEnvironmentError['kind']): LessonEnvironmentError {
  if (error instanceof LessonEnvironmentError) return error
  if (error instanceof PackCacheError) {
    return new LessonEnvironmentError(error.code === 'pack-integrity' ? 'integrity' : fallback, error.message, error.toJSON())
  }
  if (error instanceof PackIntegrityError) return new LessonEnvironmentError('integrity', error.message)
  return new LessonEnvironmentError(fallback, error instanceof Error ? error.message : String(error))
}

export interface LessonManifests {
  base: string
  preview: ReleasePreview
  packId: string
  totalBytes: number
  totalAssets: number
  /** Required assets already present in this pack's cache (verified again on load). */
  cachedAssets: number
}

/** Reads index.json and the release manifest (both small); fetches no asset. */
export async function fetchManifests(base: string): Promise<LessonManifests> {
  try {
    const preview = await new PackCache({ baseUrl: base }).inspect()
    return {
      base,
      preview,
      packId: preview.ref.pack_id,
      totalBytes: preview.requiredBytes,
      totalAssets: preview.requiredAssets,
      cachedAssets: preview.cachedAssets,
    }
  } catch (error) {
    throw classify(error, 'manifest')
  }
}

export interface LoadProgress {
  loadedBytes: number
  totalBytes: number
  verifiedAssets: number
  totalAssets: number
}

export interface StartedCompiler {
  compiler: KrsCompiler
  pack: PackManifest
  lesson: LessonManifest
  release: string
  fromCache: number
  fromNetwork: number
  /** Cached entries that failed verification and were refetched. */
  replaced: string[]
  ms: number
}

/**
 * Installs the current release (verifying every required asset, fetching only
 * what is missing or corrupt), compiles the modules, and starts the worker,
 * which holds the pack's lease and reads the other assets from the cache.
 */
export async function startCompiler(manifests: LessonManifests, onProgress: (progress: LoadProgress) => void): Promise<StartedCompiler> {
  const started = performance.now()
  const progress: LoadProgress = { loadedBytes: 0, totalBytes: manifests.totalBytes, verifiedAssets: 0, totalAssets: manifests.totalAssets }
  let fromCache = 0
  let fromNetwork = 0
  const replaced: string[] = []
  const onEvent = (event: CacheEvent) => {
    if (event.type === 'verified') {
      if (event.from === 'cache') fromCache += 1
      else fromNetwork += 1
      progress.verifiedAssets += 1
      progress.loadedBytes += manifests.preview.sizes[event.id] ?? 0
      onProgress({ ...progress })
    } else if (event.type === 'evict') {
      replaced.push(event.id)
    }
  }
  const cache = new PackCache({ baseUrl: manifests.base, onEvent })
  let pack: PackManifest
  let lesson: LessonManifest
  let stored: Awaited<ReturnType<PackCache['storedAssets']>>
  let lease: string
  let release: string
  try {
    const installed = await cache.open()
    pack = installed.workerPack()
    lesson = JSON.parse(installed.text(`lessons/${LESSON_ID}/lesson.json`)) as LessonManifest
    if (lesson.lesson !== LESSON_ID || lesson.pack_id !== pack.pack_id) {
      throw new LessonEnvironmentError('manifest', `the release's lesson.json describes ${String(lesson.lesson)} for pack ${lesson.pack_id}, not ${LESSON_ID} for ${pack.pack_id}`)
    }
    stored = await cache.storedAssets(installed, pack)
    lease = installed.lease
    release = installed.ref.release
    // `installed` (and its asset bytes) is not kept: workers read from Cache Storage.
  } catch (error) {
    throw classify(error, 'download')
  }
  const compiler = await KrsCompiler.create(pack, stored, {
    createWorker: () => new Worker(workerUrl(), { type: 'module' }),
    lease,
  }).catch((error: unknown) => {
    throw new LessonEnvironmentError('worker', `The compiler worker did not start: ${String(error)}`)
  })
  // Inactive pack generations whose lease nobody holds; failures here never block the lesson.
  void cache.cleanup().catch(() => {})
  return { compiler, pack, lesson, release, fromCache, fromNetwork, replaced, ms: performance.now() - started }
}
