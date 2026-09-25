# `@midnightntwrk/k-rust-wasm`

Typed WebAssembly bindings for the portable [`k-rust`](https://github.com/midnightntwrk/k-rust)
frontend. This package is separate from the native `@midnightntwrk/k-rust` Node-API addon and can
run in browsers, workers, and other hosts supporting standard WebAssembly and ES modules.

## Development

```console
npm install
npm run build:dev
npm test
```

## Parsing example

```typescript
import init, { parseProgram } from '@midnightntwrk/k-rust-wasm'

await init()

const { text, kast, diagnostics } = parseProgram({
  definition: `
    module MAIN
      syntax Int ::= r"[0-9]+" [token]
      syntax Exp ::= Int
    endmodule
  `,
  moduleName: 'MAIN',
  sort: 'Exp',
  program: '42',
  includePrelude: false,
})
```

## Compilation example

```typescript
import init, { compileDefinition } from '@midnightntwrk/k-rust-wasm'

await init()

const {
  definitionKore,
  syntaxDefinitionKore,
  macrosKore,
  diagnostics,
} = compileDefinition({
  definition: `
    module MAIN
      syntax Int ::= r"[0-9]+" [token]
      syntax Exp ::= Int
    endmodule
  `,
  moduleName: 'MAIN',
  backend: 'rust',
  includePrelude: false,
})
```

`compileDefinition` runs the portable frontend pipeline without writing files and defaults to the
Rust backend dialect; select `llvm` only when emitting input for the external LLVM backend. Like
every exported operation, it may only be called after `init` or `initSync` completes.

The package exposes `initSync` for hosts that load the packaged `.wasm` bytes themselves. Parsing
is synchronous after initialization; use a worker when large or untrusted definitions must not
block the main thread.

## Backend example

`compileBackend` compiles K source and creates a reusable in-process backend. `createBackend`
accepts an already compiled textual KORE definition instead.

```typescript
import init, { compileBackend } from '@midnightntwrk/k-rust-wasm'

await init()

const backend = compileBackend({
  definition: `
    module REACHABILITY
      syntax State ::= "a" [symbol(a)]
    endmodule
  `,
  moduleName: 'REACHABILITY',
  includePrelude: false,
})

console.log(backend.capabilities) // includes smt: false
backend.free()
```

Portable `execute`, `simplify`, `implies`, `prove`, and `addModule` operations are available.
Implication responses use schema version 2; their optional `condition` keeps `predicate`,
term-match `substitution`, and existential `witnesses` as three separate KORE values.
The portable backend also mirrors native `search`, `searchPaths`, `searchPattern`, `searchPatternPaths`, and their `*Observed` variants.
Method names declare state-set versus path-set and observed versus ordinary behavior; each search response carries a versioned, closed structural completeness disposition.
Observed calls accept an atomically validated allowlist of executable rewrite, function-equation, simplification, and definedness rule ids, and expose transition-owned effects; builtin activity is observable only without an allowlist.
A `transition` event names a committed transition of the leaf's `branch`, in branch order; an `evaluation` event records an equation, simplification, or builtin application that normalized a branch state, with `anchor` the number of `branch` entries preceding it.
Evaluation events are diagnostics: which ones occur, and in which order, depends on the simplifier's strategy.
The legacy execution-leaf `detail` string is diagnostic-only; use `reason`, `branch`, and `observations` for semantic decisions.
Search responses are synchronous and fully materialized, so callers should set depth, breadth, result, and simplification bounds; streaming/backpressure and cancellation are not exposed at this boundary.
Reachability claims present in portable input KORE can therefore be proved without leaving WASM.
`getModel` always throws an actionable SMT capability error, and operations that actually require
an SMT decision report an indeterminate/error result instead of pretending to have native Z3.
Step timeouts are also unavailable because `wasm32-unknown-unknown` has no host monotonic clock;
inspect `backend.capabilities` before enabling optional behavior.

This portable build intentionally excludes native Z3 inference and MPFR folding. Parsing or
compilation that needs Z3 returns an explicit error instead of silently changing semantics.
`includePrelude: true` loads the embedded standard prelude before the definition, with the same
result as the native build: it needs no Z3, and a definition importing its modules compiles to the
native `definition.kore`. While the prelude is included, a `requires` of a builtin file that
`sources` does not provide (for example `"domains.md"`) resolves to the embedded one.
`includePrelude` defaults to `false`, in which case every dependency comes from `sources`. User rules
that need parametric sort inference, or whose ambiguity the portable decision does not settle, still
return `Z3InferenceRequired`.
