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
  backend: 'llvm',
  includePrelude: false,
})
```

`compileDefinition` runs the portable frontend pipeline without writing files. Like every exported
operation, it may only be called after `init` or `initSync` completes.

The package exposes `initSync` for hosts that load the packaged `.wasm` bytes themselves. Parsing
is synchronous after initialization; use a worker when large or untrusted definitions must not
block the main thread.

This portable build intentionally excludes native Z3 inference and MPFR folding. Parsing or
compilation that needs Z3 returns an explicit error instead of silently changing semantics. The
standard prelude itself needs Z3 during rule parsing, so this package defaults `includePrelude` to
`false` and rejects `true`; pass any portable dependencies explicitly through `sources`.
