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
console.log(backend.ruleCatalog().filter(rule => rule.kind === 'rewrite'))
backend.free()
```

Portable `execute`, `simplify`, `implies`, `prove`, and `addModule` operations are available.
`backend.ruleCatalog(moduleName?)` lists the compiled axioms of the selected execution definition.
Each entry carries its identity, backend classification, executability, label, priority, and ordered `origins` containing the backend's `source` and `location` strings.
A written sentence's kind is found by matching its source and location against the origins; a position absent from the catalog compiled to no axiom of that definition.
Equal written rules have one catalog entry with multiple origins.
`sharedIdentity` marks an id also carried by another compiled entry; the observation filter refuses that id as ambiguous.
Implication responses use schema version 2; their optional `condition` keeps `predicate`,
term-match `substitution`, and existential `witnesses` as three separate KORE values.
The portable backend also mirrors native `search`, `searchPaths`, `searchPattern`, `searchPatternPaths`, and their `*Observed` variants.
Method names declare state-set versus path-set and observed versus ordinary behavior; each search response carries a versioned, closed structural completeness disposition.
Observed calls accept an atomically validated allowlist of executable rewrite, function-equation, simplification, and definedness rule ids, and expose transition-owned effects; builtin activity is observable only without an allowlist.
A `transition` event names a committed transition of the leaf's `branch` that the rule filter admits, in branch order; an `evaluation` event records an equation, simplification, or builtin application that normalized a branch state, with `anchor` the number of `branch` entries preceding it.
Evaluation events are diagnostics: which ones occur, and in which order, depends on the simplifier's strategy.
The legacy execution-leaf `detail` string is diagnostic-only; use `reason`, `branch`, and `observations` for semantic decisions.
An undefined-step (`trivial`) execution leaf includes `ruleId` and, when labeled, `ruleLabel` for the rule responsible for the halt; the id matches `ruleCatalog` and the step commits no transition.
A `trivial` or `vacuous` leaf whose emptiness comes from an equation of a `total` symbol that reduced an application of it to bottom also includes `contradictedTotal` (the symbol's KORE name and `kLabel`, the equation's `ruleId`, `ruleLabel` and `origin`, the `application` and the `undefined` term): the definition contradicts the attribute there; the leaf is otherwise unchanged.
Search responses are synchronous and fully materialized, so callers should set depth, breadth, result, and simplification bounds; streaming/backpressure and cancellation are not exposed at this boundary.
Reachability claims present in portable input KORE can therefore be proved without leaving WASM.
`getModel` always throws an actionable SMT capability error, and operations that actually require
an SMT decision report an indeterminate/error result instead of pretending to have native Z3.
Step timeouts are also unavailable because `wasm32-unknown-unknown` has no host monotonic clock;
inspect `backend.capabilities` before enabling optional behavior.

This portable build intentionally excludes native Z3 inference. Parsing or
compilation that needs Z3 returns an explicit error instead of silently changing semantics.
`includePrelude: true` loads the embedded standard prelude before the definition, with the same
result as the native build: it needs no Z3, and a definition importing its modules compiles to the
native `definition.kore`. While the prelude is included, a `requires` of a builtin file that
`sources` does not provide (for example `"domains.md"`) resolves to the embedded one.
`includePrelude` defaults to `false`, in which case every dependency comes from `sources`. User rules
that need parametric sort inference, or whose ambiguity the portable decision does not settle, still
return `Z3InferenceRequired`.

## Fuzzing example

`runFuzzCampaign` runs one `krust fuzz` campaign of the [`k-rust-fuzz`](../k-rust-fuzz/README.md)
library in one call: it compiles the definition, crafts values for the program's holes until the
budget is spent or a concrete re-run confirms a witness, and returns the report. The campaign
specification is the library's JSON, with kebab-case fields; `json` is the report's canonical text
(schema `krust-fuzz-report`, version 6), and `report` the same document parsed.

```typescript
import init, { runFuzzCampaign } from '@midnightntwrk/k-rust-wasm'

await init()

const { report } = runFuzzCampaign({
  definition: impDefinition, // the IMP semantics, with module IMP-SYNTAX
  moduleName: 'IMP',
  includePrelude: true,
  campaign: {
    program: {
      program: { name: 'le.imp', text: leProgram, 'start-sort': 'Pgm' },
      'config-vars': [],
    },
    holes: [
      { name: 'X', sort: 'Int', location: { kind: 'span', program: 'le.imp', find: 'x = 3;', literal: '3' } },
      { name: 'Y', sort: 'Int', location: { kind: 'span', program: 'le.imp', find: 'y = 5;', literal: '5' } },
    ],
    target: {
      kind: {
        kind: 'pattern',
        pattern: '<k> .K </k> <state> (#token("r", "Id") |-> R:Int) _:Map </state> requires R =/=Int 1',
        at: 'final',
      },
      'run-to-completion': false,
      'negated-property': true,
    },
    seed: '24301',
    identity: { 'k-rust-revision': 'my-build' },
    budget: { cases: '64' },
  },
})

if (report.outcome.status === 'witness-found') {
  console.log(report.outcome.witness.first.holes.map(hole => hole.value))
}
```

`options`, `proposers` and `bounds` are partial: each field given replaces the library default, and
an unknown field throws, at any depth of the specification (a misspelt `constraints` of a hole
throws rather than leaving the hole unconstrained). The seed, the rejection cap and the budget's limit are canonical decimal
strings. The default proposer is blind generation alone; `proposers: { weights: { blind: 1,
dictionary: 1 } }` adds the dictionary, which draws values from the literals of the rules
before the target, and the report then records its parameters in `identity.dictionary`. A `mutant` definition, with the same fields as the baseline's, is given exactly for a
differential target. Observer targets are library-only. A campaign that runs returns its report
whatever its outcome, and "no witness found" is never a proof that none exists; a malformed
specification, a definition that does not compile, and a campaign the library refuses throw.

The call is synchronous and holds the calling thread until the campaign ends. This build runs
every proposer except `solve`, on one thread, without a per-case safety limit: the solve proposer
needs Z3, and `wasm32-unknown-unknown` has no clock to read a deadline from and no thread to stop
a case at it. A positive `solve` weight or a `safety-limit-ms` therefore throws before anything is
compiled; bound every case with `max-work` or `max-depth`. Without a solver, a report's
`identity.solver` is `"none"`, and conditions only a solver decides leave their cases
`unsupported` rather than deciding them.

Without an `identity`, the report's `k-rust-revision` is the build identity of the k-rust this
package links (`<version>+src.<digest of its sources>`, as `krust-fuzz --version` prints it).
`includePrelude` defaults to `false` here, as for every call of this package; pass `true` to
compile the definition as `krust kcompile` and the native package do. WebAssembly has no stack
probe, so a recursion deep enough to exhaust the module's 8 MiB stack traps instead of stopping
the step for lack of stack, as a native run does; and a panic inside the campaign, which would be
a k-rust defect, traps too. A trap throws a `RuntimeError` from the call; the instance may be
inconsistent afterwards, so initialize a fresh one before calling it again.
