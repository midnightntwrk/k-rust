// deno-fmt-ignore-file
// biome-ignore format: generated types do not need formatting
// prettier-ignore
import type { PathsForPages } from 'waku/router'

// prettier-ignore
type Page =
  | { path: '/advanced/composition'; render: 'static' }
  | { path: '/advanced/language-scale'; render: 'static' }
  | { path: '/imp/concrete-grammar'; render: 'static' }
  | { path: '/imp/configuration-and-state'; render: 'static' }
  | { path: '/imp/control-flow'; render: 'static' }
  | { path: '/imp/evaluation'; render: 'static' }
  | { path: '/imp/machine-rules'; render: 'static' }
  | { path: '/imp/sorts-and-values'; render: 'static' }
  | { path: '/'; render: 'static' }
  | { path: '/lessons/tour-minimal'; render: 'static' }
  | { path: '/reference/boundaries'; render: 'static' }
  | { path: '/reference/language'; render: 'static' }
  | { path: '/reference/workflow'; render: 'static' }
  | { path: '/semantics/applicability-and-failure'; render: 'static' }
  | { path: '/semantics/lowering'; render: 'static' }
  | { path: '/semantics/static-semantics'; render: 'static' }
  | { path: '/start/definition-package'; render: 'static' }
  | { path: '/start/five-minute-theory'; render: 'static' }
  | { path: '/start/what-krs-defines'; render: 'static' }
  | { path: '/verification/reachability-claims'; render: 'static' }

// prettier-ignore
declare module 'waku/router' {
  interface RouteConfig {
    paths: PathsForPages<Page>
  }
  interface CreatePagesConfig {
    pages: Page
  }
}
