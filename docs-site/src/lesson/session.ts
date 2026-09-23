// Loading the browser lesson: manifests, the asset store, and the compiler.
// Everything here runs only in the browser, from effects or event handlers.

import {
  assetUrl,
  cachedAssetCount,
  cacheStorageAvailable,
  KrsCompiler,
  loadVerifiedAssets,
  PackIntegrityError,
  packBytes,
  type StoreProgress,
  storeVerifiedAssets,
} from '../../../browser/worker/src/controller.ts'
import type { LessonManifest, PackManifest } from '../../../browser/worker/src/protocol.ts'
import { LESSON_ID, workerUrl } from './config'

/** An environment failure: distinct from errors in the learner's source. */
export class LessonEnvironmentError extends Error {
  readonly kind: 'unsupported' | 'manifest' | 'download' | 'integrity' | 'worker'
  constructor(kind: LessonEnvironmentError['kind'], message: string) {
    super(message)
    this.name = 'LessonEnvironmentError'
    this.kind = kind
  }
}

/** Why this browser cannot run the lesson, or null. */
export function unsupportedReason(): string | null {
  if (typeof WebAssembly !== 'object') return 'This browser has no WebAssembly support.'
  if (typeof Worker !== 'function') return 'This browser has no Web Worker support.'
  if (!window.isSecureContext || !globalThis.crypto?.subtle) {
    return 'The lesson needs a secure context (HTTPS or localhost) to verify the compiler files.'
  }
  return null
}

export interface LessonManifests {
  base: string
  pack: PackManifest
  lesson: LessonManifest
  totalBytes: number
  totalAssets: number
  /** Assets already present in this pack's cache (not yet verified). */
  cachedAssets: number
  cacheAvailable: boolean
}

async function fetchJson<T>(url: string): Promise<T> {
  let response: Response
  try {
    response = await fetch(url, { credentials: 'omit' })
  } catch (error) {
    throw new LessonEnvironmentError('manifest', `${url} could not be fetched (${String(error)}).`)
  }
  if (!response.ok) throw new LessonEnvironmentError('manifest', `${url} answered HTTP ${response.status}.`)
  try {
    return (await response.json()) as T
  } catch {
    throw new LessonEnvironmentError('manifest', `${url} is not JSON.`)
  }
}

/** Fetches and checks the two small manifests; downloads nothing else. */
export async function fetchManifests(base: string): Promise<LessonManifests> {
  const pack = await fetchJson<PackManifest>(assetUrl(base, 'pack.json'))
  const lesson = await fetchJson<LessonManifest>(assetUrl(base, `lessons/${LESSON_ID}/lesson.json`))
  if (pack.schema !== 1 || pack.kind !== 'krs-browser-worker-pack') {
    throw new LessonEnvironmentError('manifest', `pack.json is not a worker pack manifest (schema ${String(pack.schema)}).`)
  }
  if (lesson.schema !== 1 || lesson.lesson !== LESSON_ID) {
    throw new LessonEnvironmentError('manifest', `lesson.json describes ${String(lesson.lesson)}, not ${LESSON_ID}.`)
  }
  if (lesson.pack_id !== pack.pack_id) {
    throw new LessonEnvironmentError('manifest', `lesson.json was staged for pack ${lesson.pack_id}, the base serves ${pack.pack_id}.`)
  }
  const cacheAvailable = await cacheStorageAvailable()
  return {
    base,
    pack,
    lesson,
    totalBytes: packBytes(pack),
    totalAssets: 4 + pack.artifacts.length + pack.framework_sources.length,
    cachedAssets: cacheAvailable ? await cachedAssetCount(pack, base) : 0,
    cacheAvailable,
  }
}

export interface StartedCompiler {
  compiler: KrsCompiler
  /** "cache": workers read verified assets from Cache Storage; "memory": the page holds them and clones them into each worker. */
  mode: 'cache' | 'memory'
  fromCache: number
  fromNetwork: number
  replaced: string[]
  ms: number
}

function classify(error: unknown): LessonEnvironmentError {
  if (error instanceof LessonEnvironmentError) return error
  if (error instanceof PackIntegrityError) return new LessonEnvironmentError('integrity', error.message)
  if (error instanceof DOMException && error.name === 'AbortError') return new LessonEnvironmentError('download', 'Download stopped.')
  return new LessonEnvironmentError('download', error instanceof Error ? error.message : String(error))
}

/** Downloads (or reads from the cache), verifies, compiles the modules, and starts the worker. */
export async function startCompiler(
  manifests: LessonManifests,
  onProgress: (progress: StoreProgress) => void,
  signal: AbortSignal,
): Promise<StartedCompiler> {
  const started = performance.now()
  const createWorker = () => new Worker(workerUrl(), { type: 'module' })
  const { pack, base } = manifests
  try {
    if (manifests.cacheAvailable) {
      const result = await storeVerifiedAssets(pack, { baseUrl: base, onProgress, signal })
      const compiler = await KrsCompiler.create(pack, result.stored, { createWorker }).catch((error: unknown) => {
        throw new LessonEnvironmentError('worker', `The compiler worker did not start: ${String(error)}`)
      })
      return { compiler, mode: 'cache', fromCache: result.fromCache, fromNetwork: result.fromNetwork, replaced: result.replaced, ms: performance.now() - started }
    }
    const progress: StoreProgress = {
      loadedBytes: 0,
      totalBytes: manifests.totalBytes,
      verifiedAssets: 0,
      totalAssets: manifests.totalAssets,
      fromCache: 0,
      fromNetwork: 0,
    }
    const assets = await loadVerifiedAssets(pack, async (path) => {
      const response = await fetch(assetUrl(base, path), { signal, credentials: 'omit' })
      if (!response.ok) throw new Error(`${path}: HTTP ${response.status}`)
      const bytes = new Uint8Array(await response.arrayBuffer())
      progress.loadedBytes += bytes.byteLength
      progress.verifiedAssets += 1
      progress.fromNetwork += 1
      onProgress({ ...progress })
      return bytes
    })
    const compiler = await KrsCompiler.create(pack, assets, { createWorker }).catch((error: unknown) => {
      throw new LessonEnvironmentError('worker', `The compiler worker did not start: ${String(error)}`)
    })
    return { compiler, mode: 'memory', fromCache: 0, fromNetwork: progress.fromNetwork, replaced: [], ms: performance.now() - started }
  } catch (error) {
    throw classify(error)
  }
}
