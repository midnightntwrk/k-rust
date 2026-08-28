# k-rust

`k-rust` is a Rust implementation of the [K Framework](https://kframework.org/). It parses K
definitions and programs, runs the frontend checking and lowering pipeline, emits KORE artifacts,
and includes an in-process symbolic backend.

## Running examples

Exercise Z3-backed parametric sort inference with the installed CLI:

```console
krust kast examples/z3-inference.k \
  --module Z3-INFERENCE \
  --sort Box \
  --expression 'box(same(1))' \
  --no-prelude
```

The result should contain `same{Int}`, showing that Z3 inferred the concrete sort:

```text
box(same{Int}(#token("1","Int")))
```

Compile and execute a small rewriting definition with the in-process backend:

```console
krust krun examples/rewrite.k \
  --main-module REWRITE \
  --sort State \
  --expression a
```

The final `<k>` cell contains `Lblb{}()`.

Exercise the pinned backend's concrete List-unification scenario through the full frontend and
in-process backend:

```console
krust krun examples/list-unification.k \
  --main-module LIST-UNIFICATION \
  --sort Val \
  --expression test1
```

The final `<k>` cell contains `Lblsuccess...`, and both List cells contain `x`, `y`, and `z`.

Exercise associative-commutative Map matching with a framed remainder:

```console
krust krun examples/map-framing.k \
  --main-module MAP-FRAMING \
  --sort Val \
  --expression a
```

The final `<store>` cell contains only the `b |-> 2` and `c |-> 3` entries.

On macOS, verify that the release binary does not dynamically load Z3:

```console
otool -L ~/.local/bin/krust
```

The output should contain only system libraries and no `libz3.dylib`; together with the inference
example succeeding, this confirms that the statically linked Z3 implementation was exercised.

## Status

The repository is a usable early implementation, not yet a universal drop-in replacement for
every K command-line workflow.

Implemented end to end:

- K outer syntax, Markdown/literate-K sources, recursive `requires`, imports, source spans, syntax
  declarations, configurations, and rule-like bubbles.
- A portable Earley/chart parser with K's scanner winner rules, layout, priorities,
  associativity, records, user lists, casts, cells, ambiguity factoring, and sort inference.
- Native Z3-backed ambiguous and parametric inference by default, with a portable non-Z3 subset.
- KAST text and JSON v4; KORE text, JSON v1, binary KORE 1.0–1.2, ASTs, compact and pretty
  printers, and explicit syntax/KAST normalization.
- Definition catalogs, import resolution, structural checks, configuration expansion, the ordered
  backend lowering pipeline, sort injections, and `ModuleToKORE`.
- KORE generation for ordinary rules, claims, equations, functions, `owise`, macros, aliases,
  reachability claims, subsorts, overloads, algebraic axioms, no-confusion, and no-junk.
- In-process concrete and symbolic execution, `ONE`/`FINAL`/`STAR`/`PLUS` reachability search,
  simplification, implication and reachability checks, builtin collections, Z3
  satisfiability/validity queries, and satisfying-model extraction.
- Native `krust kast`, `krust kcompile`, `krust kore-exec`, `krust kore-simplify`,
  `krust kore-get-model`, `krust kore-implies`, `krust kore-match-disjunction`, and experimental
  `krust krun` and `krust kprove` commands.
- Bundled builtin sources pinned to K v7.1.337, so an installed CLI does not require a separate K
  source checkout. Explicit sources always take precedence.
- Native, portable, and `wasm32-unknown-unknown` build gates.

The frontend implementation lives in the `k-rust` crate, with shared KORE syntax and serialization
in `k-rust-kore` so the in-process backend can consume the same representation without depending on
frontend internals. Thin `k-rust-napi` and `k-rust-wasm` crates expose the host-independent APIs to
native Node.js and portable WebAssembly respectively.

## Install and build

The native frontend enables statically linked Z3 and MPFR support by default. Z3 is downloaded from
its official GitHub release rather than compiled from source:

```console
cargo install --path crates/k-rust
# or
cargo build --workspace --release
```

The Z3 binding does not call a `z3` executable or require a system Z3 installation.

The portable library subset disables native inference and floating-point folding:

```console
cargo build -p k-rust --no-default-features
cargo build -p k-rust-wasm --target wasm32-unknown-unknown
```

The CLI is deliberately native-only. A portable build returns a structured
`Z3InferenceRequired` error when a definition crosses the inference boundary that needs Z3.

## CLI

Compile a definition into backend KORE artifacts:

```console
krust kcompile definition.k \
  --main-module MAIN \
  --backend llvm \
  --output-directory definition-kompiled
```

`--backend rust` (the default; `haskell` remains an alias) selects the symbolic KORE dialect used
by the in-process Rust backend. Both modes write:

- `definition.kore`
- `syntaxDefinition.kore`
- `macros.kore`

Parse a concrete program as textual KAST or KAST JSON v4:

```console
krust kast definition.k --module MAIN --sort Exp --expression '1 + 2'
krust kast definition.k --module MAIN --sort Exp program.exp --output json
```

Pass `--backend rust` or `--backend llvm` to exclude modules for the same symbolic or concrete
definition view used by backend compilation.

Execute a concrete program using the in-process Rust backend:

```console
krust krun definition.k --main-module MAIN --sort Exp --expression '1 + 2'
krust krun definition.k --main-module MAIN --sort Exp program.exp --depth 1000
```

Execution explores every rewrite branch by default. Pass `--execute-to-branch` to return the
configuration at the first branch point instead. Pass `--strategy any` for ordered,
first-applicable rewriting instead of the default `--strategy all`. Pass `--breadth N` to cap the
live frontier: execution returns that frontier when the bound is exceeded, while search reports
that it is incomplete.

Search final states, every reachable state, states after exactly one step, or states after one or
more steps:

```console
krust krun definition.k --main-module MAIN --sort Exp --expression '1 + 2' --search-final
krust krun definition.k --main-module MAIN --sort Exp --expression '1 + 2' --search-all
krust krun definition.k --main-module MAIN --sort Exp --expression '1 + 2' --search-one-step
krust krun definition.k --main-module MAIN --sort Exp --expression '1 + 2' \
  --search-one-or-more-steps --search-bound 10
```

Without a target, each solution binds `Result` to a matching configuration. Pass
`--search-pattern target.kore` to match solutions against a constrained raw KORE pattern; an empty
solution set prints `#Bottom`, while a ground match prints `#Top`.

Execute an already compiled textual KORE definition directly, using the same in-process backend
and search options as `krun`:

```console
krust kore-exec definition.kore --module MAIN --pattern pgm.kore
krust kore-exec definition.kore --module MAIN --pattern pgm.kore \
  --search-final --search-pattern target.kore
krust kore-exec definition.kore --module MAIN --pattern pgm.kore --output result.kore
```

Use `--step-timeout MILLISECONDS` for a fixed cooperative rewrite-step deadline and
`--moving-average-step-timeout` to use twice the measured moving average, capped by the fixed
deadline when both are supplied. The same flags are available on `krun`.

Rule-only modules can be added transactionally before execution. Their source names are available
as module IDs for the command, while the backend also assigns the KORE RPC-compatible
`m<sha256>` identifier internally:

```console
krust kore-exec definition.kore --module NEW --add-module new-rules.kore --pattern pgm.json
```

Serve that same in-process backend through the KORE JSON-RPC 2.0 protocol used by K tooling:

```console
krust kore-rpc definition.kore --module MAIN --server-port 31337
```

The service uses newline-delimited JSON over a persistent raw TCP socket (not HTTP). Requests may
call `execute`, `simplify`, `implies`, `add-module`, and `get-model`; module additions remain visible
to later requests and connections for the lifetime of the server. A standalone `cancel` request or
notification cooperatively interrupts the active request on that connection with the reference
`Request cancelled` error. The server binds to `127.0.0.1` by default; pass `--host 0.0.0.0` to
expose it on every interface or `--server-port 0` to request an ephemeral port.

`execute` also honors `assume-state-defined` by treating partial subterms of the current
configuration as defined while matching rewrite rules. `implies` accepts `assume-defined` as the
reference proxy's backend-routing hint; the unified Rust service already uses that in-process path.

Execution can return reference-shaped rewrite diagnostics through `log-successful-rewrites` and
`log-failed-rewrites`. Requests may also select legacy context names such as `Proxy`, `Execute`,
`Rewrite`, or `Simplify` through `haskell-logging`; matching structured entries are returned in
`haskell-log-entries`, while names unknown to the Rust backend are ignored.

Simplify an arbitrary text, KORE JSON v1, or binary KORE pattern. Unlike execution, this accepts
pure ML predicates without requiring a configuration term:

```console
krust kore-simplify definition.kore --module MAIN --pattern predicate.json
krust kore-simplify definition.kore --module MAIN --pattern predicate.kore --output result.kore
```

Ask Z3 for a satisfying assignment to the predicate portion of a KORE pattern. The JSON result
distinguishes `Sat`, `Unsat`, and `Unknown` and includes a typed KORE substitution when one exists:

```console
krust kore-get-model definition.kore --module MAIN --pattern predicate.json
krust kore-get-model definition.kore --module MAIN --pattern predicate.kore --output model.json
```

Check whether one constrained KORE pattern implies another. The JSON result includes the original
implication, its `valid`, `invalid`, or `unknown` status, and any matching condition:

```console
krust kore-implies definition.kore --module MAIN \
  --antecedent left.json --consequent right.json
```

Match a constrained KORE pattern against every alternative in a disjunction of configurations:

```console
krust kore-match-disjunction definition.kore --module MAIN \
  --disjunction states.kore --match target.kore
```

Prove all modal reachability claims in a specification module, or select claims by label:

```console
krust kprove spec.k --main-module SPEC
krust kprove spec.k --main-module SPEC --claim reaches-result --depth 1000
krust kprove spec.k --main-module SPEC --graph-search depth-first
krust kprove spec.k --main-module SPEC --definition-module SEMANTICS
```

Bare claims default to all-path semantics, matching the reference Haskell backend. Use
`--definition-module` (or `--def-module`) when the configuration belongs to an imported semantics
module rather than the specification module. `kprove` handles one-path and all-path claims,
trusted claims, guarded claim circularities,
branching semantic rules, breadth-first or depth-first traversal, depth bounds, and Z3-backed side
conditions entirely in process. A specification can `requires` and import its semantics definition
in the normal K source layout. The reference stuck-state heuristic is enabled by default; pass
`--disable-stuck-check` to continue rewriting after destination terms match but their side
conditions do not.

Common source options:

- `-I DIR` / `--include DIR` adds a `requires` lookup directory.
- `--md-selector EXPR` selects Markdown fences; the default is `k`.
- `--builtin-directory DIR` overrides the bundled builtin sources.
- `KRUST_BUILTIN_DIRECTORY` provides the same override through the environment.
- `--no-prelude` disables the implicit `prelude.md` load.

Resolution checks explicit builtin overrides, the requiring file's directory, the working
directory, `-I` directories, and finally the embedded pinned sources.

## Node.js and TypeScript

The `k-rust-napi` crate builds a Node-API addon and a typed TypeScript facade. The facade accepts
in-memory definitions, resolves additional virtual sources used by `requires`, and can either parse
programs into typed KAST JSON or compile definitions into the three backend-facing KORE artifacts.

Build and test it locally:

```console
cd crates/k-rust-napi
npm install
npm run build:debug
npm test
```

```typescript
import { parseProgram } from '@midnightntwrk/k-rust'

const result = parseProgram({
  definition: `
    module ARITHMETIC
      syntax Int ::= r"[0-9]+" [token]
      syntax Exp ::= Int
      syntax Exp ::= left: Exp "+" Exp [symbol(plus)]
    endmodule
  `,
  moduleName: 'ARITHMETIC',
  sort: 'Exp',
  program: '1 + 2 + 3',
  includePrelude: false,
})

console.log(result.text)
console.log(result.kast)
```

Use `compileDefinition({ definition, moduleName, backend })` to run the same ordered compilation
pipeline as `krust kcompile` without filesystem output. It returns `definitionKore`,
`syntaxDefinitionKore`, `macrosKore`, and diagnostics. The facade also exports `parseKast`,
`printKast`, `parseKore`, `printKore`, and `formatKoreDefinition`. The generated raw Node-API
functions remain available from `native.js` for hosts that want the lowest possible wrapper
overhead.

`compileBackend(options)` compiles and immediately creates a persistent native backend;
`createBackend({ definitionKore, moduleName })` starts from existing KORE. The backend exposes
execution, simplification, implication checking, model generation, reachability proving, and
stateful module addition. Native sessions cache Z3 preludes per selected module.

## WebAssembly and TypeScript

The separate `@midnightntwrk/k-rust-wasm` package exposes the portable frontend through standard
WebAssembly and ES modules. It has the same typed KAST/KORE and virtual-source API as the native
package, but does not bundle Z3 or MPFR and can run in browsers and workers.

Build and test it locally:

```console
cd crates/k-rust-wasm
npm install
npm run build:dev
npm test
```

```typescript
import init, { parseProgram } from '@midnightntwrk/k-rust-wasm'

await init()

const result = parseProgram({
  definition: `
    module ARITHMETIC
      syntax Int ::= r"[0-9]+" [token]
      syntax Exp ::= Int
    endmodule
  `,
  moduleName: 'ARITHMETIC',
  sort: 'Exp',
  program: '42',
  includePrelude: false,
})
```

After initialization, parsing is synchronous. Use a worker for large inputs in latency-sensitive
applications. `compileDefinition` exposes the same in-memory compiler API and returns all three KORE
artifacts. Definitions that require native Z3 inference return an explicit unsupported-boundary
error rather than silently choosing a different result. Because the standard prelude itself needs
Z3 while parsing rules, the WASM package defaults `includePrelude` to `false`; portable dependencies
must be passed explicitly through `sources`.

The WASM facade also exports `compileBackend` and `createBackend` with the same persistent API.
Concrete execution and proofs work in-process; `capabilities.smt` and `capabilities.stepTimeouts`
are `false`, and SMT-only model generation or host-clock-dependent timeouts fail explicitly.

## Compatibility evidence

The implementation is compared against these pinned references:

| Component | Commit |
|---|---|
| [`runtimeverification/k`](https://github.com/runtimeverification/k) | `4a46d1231473b599c699160132fd6e76a5c46406` (v7.1.337) |
| [`runtimeverification/imp-semantics`](https://github.com/runtimeverification/imp-semantics) | `683a773418add3bcae8ded47c2b24e94494e1988` |
| [`runtimeverification/wasm-semantics`](https://github.com/runtimeverification/wasm-semantics) | `212271bd434bd402e27c42f6416854342733386d` |
| [`runtimeverification/evm-equivalence`](https://github.com/runtimeverification/evm-equivalence) | `3a757eb6f88000047d6fd064d6b72b78b6e23592` |
| [`runtimeverification/evm-semantics`](https://github.com/runtimeverification/evm-semantics) | `5dd05ea7936c13f4029389bafd25785ed9ff0a55` (plugin `651a2db5afc1789c89553f9113c1afa39e391e35`) |
| [`runtimeverification/mir-semantics`](https://github.com/runtimeverification/mir-semantics) | `4d793252bcd77091ee759ca6cd1629db41ed5496` |
| [`runtimeverification/scala-kore`](https://github.com/runtimeverification/scala-kore) | `844214975c` (v0.3.3) |

The outer parser accepts 1,499 of the 1,504 `.k` files probed at the pinned commit. Four rejected
files are intentional malformed-string tests; the fifth is a legacy `Token{...}` fixture also
rejected by the pinned JavaCC grammar.

The structural differential corpus compiles eleven upstream definitions through both frontends,
strips source locations and generated sentence IDs, and compares the semantic definition, syntax
definition, and standalone macro sentences as multisets. It covers append syntax, ambiguous
rewrites, casts, collection-cell rewrites, fresh variables, IMP control flow, List/Set hooks,
rewrite macros, the complete WASM and MIR semantics, and the EVM optimization semantics used by
`evm-equivalence`:

```console
K_KOMPILE=/path/to/pinned/bin/kompile scripts/reference-differential.sh
scripts/reference-differential.sh casts imp wasm evm-equivalence mir  # selected cases
```

Set `K_CHECKOUT` if the ignored K checkout is not at `k/`. The external corpus locations can be
overridden with `IMP_SEMANTICS_CHECKOUT`, `WASM_SEMANTICS_CHECKOUT`, and
`EVM_SEMANTICS_CHECKOUT`, and `MIR_SEMANTICS_CHECKOUT`. Set
`REFERENCE_DIFFERENTIAL_MEMORY_KIB` to apply a hard per-frontend virtual-memory limit when running
large cases. The reference launcher defaults to an 8 GiB Java heap; use
`REFERENCE_DIFFERENTIAL_K_OPTS` to lower it when applying a tighter limit. For example, the MIR
case passes with a 6 GiB address-space ceiling and a 2 GiB serial-GC heap:

```console
REFERENCE_DIFFERENTIAL_MEMORY_KIB=6291456 \
REFERENCE_DIFFERENTIAL_K_OPTS='-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=4 -Dscala.concurrent.context.maxThreads=4' \
scripts/reference-differential.sh mir
```

The program-parser differential gate parses small semantics-specific terms through reference
`kast` and `krust kast`, decodes their KAST JSON, and compares the terms structurally. It covers an
empty WebAssembly module, an EVM schedule, and a MIR span:

```console
K_KOMPILE=/path/to/pinned/bin/kompile scripts/reference-kast-differential.sh
scripts/reference-kast-differential.sh wasm evm-equivalence mir  # selected cases
```

It accepts the same checkout and memory-limit environment variables as the structural KORE gate.

The backend acceptance gate compiles, executes, and proves with the in-process Rust backend:

```console
scripts/backend-smoke.sh
```

No Haskell executable is required. The gate also generates LLVM matching decision trees for the
collection-cell fixture and links a native interpreter when `K_BACKEND_BIN` points to an LLVM
backend installation. `K_KOMPILE` may be supplied instead; its sibling LLVM executables will be
used. Set `K_CHECKOUT` when the ignored reference checkout is not at `k/`.

## Development gates

CI runs the release-independent gates:

```console
cargo fmt --all -- --check
cargo build --workspace --all-targets --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --workspace --locked
cargo clippy -p k-rust -p k-rust-wasm --all-targets --no-default-features --locked -- -D warnings
cargo test -p k-rust -p k-rust-wasm --no-default-features --locked
cargo build -p k-rust-wasm --target wasm32-unknown-unknown --locked
```

Snapshot updates are intentional and source-driven. Review them locally with `cargo insta review`;
CI only runs ordinary tests and never accepts snapshots.

Release packaging is checked with:

```console
cargo package --workspace --exclude k-rust-napi --exclude k-rust-wasm --locked
```

## Scope and known limitations

- The LLVM backend remains external. `krust kcompile --backend llvm` emits its input but does not
  invoke LLVM compilation; symbolic execution is handled by the in-process Rust backend.
- Context/freezer labels are semantically equivalent but can differ in numeric suffix assignment
  from Java when Java's `HashSet` traversal changes encounter order. The exact corpus does not
  normalize arbitrary user labels.
- The WASM-compatible feature set intentionally omits Z3 inference, MPFR constant folding, and
  host-clock-dependent step timeouts.
- Coverage instrumentation and the optional unsafe-`anywhere` removal mode are not exposed by the
  CLI. They are identity stages unless explicitly requested in Java.
- LSP, `kserver`, and Bison parser generation are outside the current CLI scope.
- Like the reference backend, AC unification remains conservative when more than one unmatched
  opaque Set or Map chunk remains after common chunks are cancelled.
- Step deadlines cooperatively interrupt native hooks. Long-running Rust loops check the deadline
  while working; one-shot third-party cryptographic operations are checked at hook boundaries.

## TODOs

- Map retained inner-parser byte spans back to absolute nested source locations and preserve all
  remaining nested term attributes.
- Add Java-compatible unused-symbol and deprecated-production warnings once nested provenance is
  available.
- Add an AST-level differential oracle against the JavaCC outer parser and broaden exact lexical
  error and ambiguous/parametric inference coverage across rules, claims, contexts, and aliases.
- Reproduce exact Java scanner diagnostic wording and generated freezer-label iteration order.
- Add a native diagnostic presentation adapter after the portable diagnostic model stabilizes;
  `miette` remains a possible renderer, not a core dependency.
- Extend standalone sort injection for manually constructed parametric KAST whose labels omit the
  concrete parameters normally supplied by parser inference.
- Emit the optional legacy priority aliases supported by `ModuleToKORE` compatibility modes.
- Measure Z3-path usage across a substantially larger real-definition corpus.
- Revisit package splitting only if real build or release pressure justifies it.

## License

`k-rust` is distributed under the BSD 3-Clause License. The bundled K Framework builtin sources
retain their original copyright notices; see [NOTICE](NOTICE).
