/// <reference types="vite/client" />

interface ImportMetaEnv {
  /**
   * Base URL of the staged browser-lesson assets (pack.json, pack/, modules/,
   * lessons/). Absolute, or relative to the site origin. Unset: the lesson
   * renders its "unavailable" state. See docs-site/README.md.
   */
  readonly VITE_KRS_BROWSER_PACK_BASE?: string
}
