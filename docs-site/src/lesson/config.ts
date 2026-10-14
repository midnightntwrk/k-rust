// Build-time configuration of the browser lesson.
//
// VITE_KRS_BROWSER_PACK_BASE is read by Vite when the site is built (or when
// `vocs dev` starts) and inlined into the client bundle. It names the root of a
// content-addressed release publication (browser/release/release.py assemble,
// format browser/release/release-format.toml):
//
//   <base>/index.json               mutable pointer to the active release (no-cache)
//   <base>/releases/<sha256>.json   release manifest; its assets include pack.json and lessons/tour-minimal/lesson.json
//   <base>/blobs/<sha256>.<ext>     every asset, named by the SHA-256 of its bytes
//
// A cross-origin base must send CORS headers for GET (browser/release/hosting.toml).
// Before the learner presses the download button the page fetches only
// index.json and the release manifest.

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
