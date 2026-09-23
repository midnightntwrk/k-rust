/// <reference types="vite/client" />

interface ImportMetaEnv {
  /**
   * Root URL of the browser-lesson release publication (index.json, releases/,
   * blobs/). Absolute, or relative to the site origin. Unset: the lesson
   * renders its "unavailable" state. See docs-site/README.md.
   */
  readonly VITE_KRS_BROWSER_PACK_BASE?: string
}
