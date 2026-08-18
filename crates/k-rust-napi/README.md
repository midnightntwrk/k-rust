# `@midnightntwrk/k-rust`

Typed Node.js bindings for the [`k-rust`](https://github.com/midnightntwrk/k-rust) frontend.

The public TypeScript facade provides:

- Concrete program parsing from in-memory K definitions and virtual `requires` sources.
- Full in-memory definition compilation into backend-facing KORE artifacts.
- Typed KAST JSON v4 parsing and printing.
- Typed KORE JSON v1 parsing and printing.
- Width-aware formatting for complete textual KORE definitions.

## Development

```console
npm install
npm run build:debug
npm test
```

## Parsing example

```typescript
import { parseProgram } from '@midnightntwrk/k-rust'

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
import { compileDefinition } from '@midnightntwrk/k-rust'

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

`compileDefinition` runs the same ordered frontend pipeline as `krust kcompile` without writing
files. Native compilation includes Z3-backed sort inference and MPFR-backed floating-point constant
folding. `includePrelude` defaults to `true` in this package.

The native addon is synchronous. Call it from a worker thread when parsing untrusted or especially
large definitions in latency-sensitive Node.js applications.
