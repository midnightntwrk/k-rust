// Build-time configuration of the browser lesson (IR-20).
//
// VITE_KRS_BROWSER_PACK_BASE is read by Vite when the site is built (or when
// `vocs dev` starts) and inlined into the client bundle. It names the
// directory that browser/worker/scripts/stage-assets.ts produces:
//
//   <base>/pack.json                        normalized pack manifest (worker schema 1)
//   <base>/lessons/tour-minimal/lesson.json lesson manifest (pack_id, Cargo.toml, lint flags)
//   <base>/pack/..., <base>/modules/...     every asset pack.json lists, with its size and SHA-256
//
// A cross-origin base must send CORS headers (Access-Control-Allow-Origin) for
// GET. Nothing is fetched from it until the learner presses the download button,
// except the two manifests.

const raw = import.meta.env.VITE_KRS_BROWSER_PACK_BASE

/** The configured asset base with a trailing slash, or null when the build has none. */
export const packBase: string | null =
  typeof raw === 'string' && raw.trim() !== '' ? (raw.trim().endsWith('/') ? raw.trim() : `${raw.trim()}/`) : null

/** The lesson this page teaches; also its directory under <base>/lessons/. */
export const LESSON_ID = 'tour-minimal'

/** The worker bundle that `bun run build:lesson-worker` writes to public/browser-lesson/. */
export function workerUrl(): URL {
  return new URL(`${import.meta.env.BASE_URL}browser-lesson/worker.js`, window.location.href)
}
