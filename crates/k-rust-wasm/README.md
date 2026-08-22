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
Reachability claims present in portable input KORE can therefore be proved without leaving WASM.
`getModel` always throws an actionable SMT capability error, and operations that actually require
an SMT decision report an indeterminate/error result instead of pretending to have native Z3.
Step timeouts are also unavailable because `wasm32-unknown-unknown` has no host monotonic clock;
inspect `backend.capabilities` before enabling optional behavior.

This portable build intentionally excludes native Z3 inference and MPFR folding. Parsing or
compilation that needs Z3 returns an explicit error instead of silently changing semantics. The
standard prelude itself needs Z3 during rule parsing, so this package defaults `includePrelude` to
`false` and rejects `true`; pass any portable dependencies explicitly through `sources`.
