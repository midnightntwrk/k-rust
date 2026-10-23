# `@midnightntwrk/k-rust`

Typed Node.js bindings for the [`k-rust`](https://github.com/midnightntwrk/k-rust) frontend.

The public TypeScript facade provides:

- Concrete program parsing from in-memory K definitions and virtual `requires` sources.
- Full in-memory definition compilation into backend-facing KORE artifacts.
- Persistent in-process execution, simplification, implication, model, and proof sessions.
- One-call `krust fuzz` campaigns that craft program inputs reaching a target, with a canonical report.
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
backend. Native compilation includes Z3-backed sort inference. `includePrelude` defaults to
`true` in this package.

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
console.log(backend.ruleCatalog().filter(rule => rule.kind === 'rewrite'))
console.log(backend.prove({ claim: 'reaches-c' }).status) // "proven"
```

Use `createBackend({ definitionKore, moduleName })` when KORE has already been compiled.
`backend.ruleCatalog(moduleName?)` lists the compiled axioms of the selected execution definition.
Each entry carries its identity, backend classification, executability, label, priority, and ordered `origins` containing the backend's `source` and `location` strings.
A written sentence's kind is found by matching its source and location against the origins; a position absent from the catalog compiled to no axiom of that definition.
Equal written rules have one catalog entry with multiple origins.
`sharedIdentity` marks an id also carried by another compiled entry; the observation filter refuses that id as ambiguous.
Backend methods accept typed KORE JSON from `parseKore` and include `execute`, `simplify`, `implies`, `getModel`, `prove`, `addModule`, and four reachability methods: `search`, `searchPaths`, `searchPattern`, and `searchPatternPaths`.
The method name declares state-set versus path-set modality; no request flag changes a result's meaning.
Each search response carries `schemaVersion`, a literal `modality`, accumulated effects, and a closed `incomplete` union that reports every bound or backend uncertainty structurally.
A response whose every initial state had no instance before any step (its constraints, or its term's definedness, refuted) also carries `initialBottom: true`, so a search from no configuration is told apart from one that reached no result.
Set `maxResults` for definitions with many converging paths because path witnesses can grow exponentially and the synchronous response is fully materialized.
Implication responses use schema version 2; their optional `condition` keeps `predicate`,
term-match `substitution`, and existential `witnesses` as three separate KORE values.

`executeObserved` and the four `*Observed` search methods opt into branch-local structured transition events.
Their optional `rules` allowlist is validated atomically against exact executable rewrite, function-equation, simplification, and definedness rule ids; builtin activity is observable only without an allowlist.
Ordinary calls do not collect observation events.
A `transition` event names a committed transition of the leaf's `branch` that the rule filter admits, in branch order; an `evaluation` event records an equation, simplification, or builtin application that normalized a branch state, with `anchor` the number of `branch` entries preceding it.
Evaluation events are diagnostics: which ones occur, and in which order, depends on the simplifier's strategy.
The legacy execution-leaf `detail` string remains human-readable diagnostic context for compatibility and must not be parsed as semantic data; use the closed `reason`, `branch`, and `observations` fields instead.
An undefined-step (`trivial`) execution leaf includes `ruleId` and, when labeled, `ruleLabel` for the rule responsible for the halt; the id matches `ruleCatalog` and the step commits no transition.
A `trivial` or `vacuous` leaf whose emptiness comes from an equation of a `total` symbol that reduced an application of it to bottom also includes `contradictedTotal` (the symbol's KORE name and `kLabel`, the equation's `ruleId`, `ruleLabel` and `origin`, the `application` and the `undefined` term): the definition contradicts the attribute there; the leaf is otherwise unchanged.
`execute` exposes depth/breadth bounds, all/any strategy, branch stopping, cut-point and terminal rules, step timeouts, and rewrite traces.

The native addon is synchronous. Call it from a worker thread when parsing untrusted or especially
large definitions or running long searches in latency-sensitive Node.js applications.
Search cancellation and streaming/backpressure are not exposed by this synchronous API; use explicit depth, breadth, result, and simplification bounds.

## Fuzzing example

`runFuzzCampaign` runs one `krust fuzz` campaign of the [`k-rust-fuzz`](../k-rust-fuzz/README.md)
library in one call: it compiles the definition, crafts values for the program's holes until the
budget is spent or a concrete re-run confirms a witness, and returns the report. The campaign
specification is the library's JSON, with kebab-case fields; `json` is the report's canonical text
(schema `krust-fuzz-report`, version 5), and `report` the same document parsed.

```typescript
import { runFuzzCampaign } from '@midnightntwrk/k-rust'

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

The call is synchronous and holds the calling thread until the campaign ends; nothing cancels it,
so bound it with the budget and the case options (`max-work`, `max-depth`, and
`safety-limit-ms` for a per-case wall-clock limit), and call it from a worker thread in
latency-sensitive applications. Without `safety-limit-ms` (the library default is none), a step
whose function evaluation never terminates holds the calling thread for good.

The compilation and the campaign run on a thread of the binding with a 256 MiB stack, as
`krust fuzz` does, whichever thread calls: the backend stops a step for lack of stack from the
stack that remains, so the outcome would otherwise depend on the caller's thread. The report
records that size as `identity.thread-stack-size`, and a campaign that sets the field throws.
Without an `identity`, the report's `k-rust-revision` is the build identity of the k-rust this
package links (`<version>+src.<digest of its sources>`, as `krust-fuzz --version` prints it). A
panic inside the campaign, which would be a k-rust defect, throws an error rather than ending
the process. `includePrelude` defaults to `true` here, as `krust kcompile` loads the prelude.
