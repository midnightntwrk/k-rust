# `@midnightntwrk/k-rust`

Typed Node.js bindings for the [`k-rust`](https://github.com/midnightntwrk/k-rust) frontend.

The public TypeScript facade provides:

- Concrete program parsing from in-memory K definitions and virtual `requires` sources.
- Typed KAST JSON v4 parsing and printing.
- Typed KORE JSON v1 parsing and printing.
- Width-aware formatting for complete textual KORE definitions.

## Development

```console
npm install
npm run build:debug
npm test
```

## Example

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

The native addon is synchronous. Call it from a worker thread when parsing untrusted or especially
large definitions in latency-sensitive Node.js applications.
