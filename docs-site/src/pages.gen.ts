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
  | { path: '/k-rust/amendments'; render: 'static' }
  | { path: '/k-rust/compatibility'; render: 'static' }
  | { path: '/k-rust/fuzzing'; render: 'static' }
  | { path: '/k-rust'; render: 'static' }
  | { path: '/lean/a-definition-and-its-steps'; render: 'static' }
  | { path: '/lean/evaluation'; render: 'static' }
  | { path: '/lean/hypothesis'; render: 'static' }
  | { path: '/lean'; render: 'static' }
  | { path: '/lean/matching-logic'; render: 'static' }
  | { path: '/lean/matching'; render: 'static' }
  | { path: '/lean/signature'; render: 'static' }
  | { path: '/lean/sound-and-complete'; render: 'static' }
  | { path: '/lean/state-of-the-core'; render: 'static' }
  | { path: '/lean/step'; render: 'static' }
  | { path: '/lean/terms'; render: 'static' }
  | { path: '/lean/theory'; render: 'static' }
  | { path: '/lean/values'; render: 'static' }
  | { path: '/lean/well-formedness'; render: 'static' }
  | { path: '/lessons/tour-minimal'; render: 'static' }
  | { path: '/reference/boundaries'; render: 'static' }
  | { path: '/reference/language'; render: 'static' }
  | { path: '/reference/workflow'; render: 'static' }
  | { path: '/semantics/applicability-and-failure'; render: 'static' }
  | { path: '/semantics/lowering'; render: 'static' }
  | { path: '/semantics/static-semantics'; render: 'static' }
  | { path: '/start/definition-package'; render: 'static' }
  | { path: '/start/what-krs-defines'; render: 'static' }
  | { path: '/tour/definitions-compile-into-tools'; render: 'static' }
  | { path: '/tour/functions-defined-by-rules'; render: 'static' }
  | { path: '/tour/patterns-and-substitution'; render: 'static' }
  | { path: '/tour/sorts-and-constructors'; render: 'static' }
  | { path: '/verification/mutation-testing'; render: 'static' }
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
