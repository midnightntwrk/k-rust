# `@midnightntwrk/k-rust`

Typed Node.js bindings for the [`k-rust`](https://github.com/midnightntwrk/k-rust) frontend.

The public TypeScript facade provides:

- Concrete program parsing from in-memory K definitions and virtual `requires` sources.
- Full in-memory definition compilation into backend-facing KORE artifacts.
- Persistent in-process execution, simplification, implication, model, and proof sessions.
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
  backend: 'rust',
  includePrelude: false,
})
```

`compileDefinition` runs the same ordered frontend pipeline as `krust kcompile` without writing
files. The backend defaults to `rust`; select `llvm` only when emitting input for the external LLVM
backend. Native compilation includes Z3-backed sort inference and MPFR-backed floating-point
constant folding. `includePrelude` defaults to `true` in this package.

## Backend example

`compileBackend` is the shortest path from K source to a reusable backend. The returned object
retains the internalized definition, added modules, and native Z3 preludes across calls.

```typescript
import { compileBackend } from '@midnightntwrk/k-rust'

const backend = compileBackend({
  definition: `
    module REACHABILITY
      syntax State ::= "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)]
      configuration <k> $PGM:State </k>
      rule <k> a => b </k>
      rule <k> b => c </k>
      claim <k> a => c </k> [one-path, label(reaches-c)]
    endmodule
  `,
  moduleName: 'REACHABILITY',
  includePrelude: true,
})

console.log(backend.capabilities) // includes smt: true
console.log(backend.prove({ claim: 'reaches-c' }).status) // "proven"
```

Use `createBackend({ definitionKore, moduleName })` when KORE has already been compiled.
Backend methods accept typed KORE JSON from `parseKore` and include `execute`, `simplify`, `implies`, `getModel`, `prove`, `addModule`, and four reachability methods: `search`, `searchPaths`, `searchPattern`, and `searchPatternPaths`.
The method name declares state-set versus path-set modality; no request flag changes a result's meaning.
Each search response carries `schemaVersion`, a literal `modality`, accumulated effects, and a closed `incomplete` union that reports every bound or backend uncertainty structurally.
Set `maxResults` for definitions with many converging paths because path witnesses can grow exponentially and the synchronous response is fully materialized.

`executeObserved` and the four `*Observed` search methods opt into branch-local structured transition events.
Their optional `rules` allowlist is validated atomically against exact executable rule ids.
Ordinary calls do not collect observation events.
The legacy execution-leaf `detail` string remains human-readable diagnostic context for compatibility and must not be parsed as semantic data; use the closed `reason`, `branch`, and `observations` fields instead.
`execute` exposes depth/breadth bounds, all/any strategy, branch stopping, cut-point and terminal rules, step timeouts, and rewrite traces.

The native addon is synchronous. Call it from a worker thread when parsing untrusted or especially
large definitions or running long searches in latency-sensitive Node.js applications.
Search cancellation and streaming/backpressure are not exposed by this synchronous API; use explicit depth, breadth, result, and simplification bounds.
