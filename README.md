# k-rust

`k-rust` is a Rust implementation of the [K Framework](https://kframework.org/) frontend. It
parses K definitions and programs, runs the frontend checking and lowering pipeline, and emits the
KORE artifacts consumed by the existing Haskell and LLVM backends.

The project intentionally keeps the backend boundary intact: it replaces the Java/Scala frontend,
not `kore-exec` or the LLVM backend.

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
- KAST text and JSON v4; KORE text, JSON v1, ASTs, compact and pretty printers, and explicit
  syntax/KAST normalization.
- Definition catalogs, import resolution, structural checks, configuration expansion, the ordered
  backend lowering pipeline, sort injections, and `ModuleToKORE`.
- KORE generation for ordinary rules, claims, equations, functions, `owise`, macros, aliases,
  reachability claims, subsorts, overloads, algebraic axioms, no-confusion, and no-junk.
- Native `krust kast` and `krust kcompile` commands.
- Bundled builtin sources pinned to K v7.1.337, so an installed CLI does not require a separate K
  source checkout. Explicit sources always take precedence.
- Native, portable, and `wasm32-unknown-unknown` build gates.

The frontend implementation lives in the `k-rust` crate. The thin `k-rust-napi` crate exposes its
host-independent parsing APIs to Node.js and TypeScript without changing the core crate's release
or portability boundaries.

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
cargo build --workspace --no-default-features
cargo build --workspace --target wasm32-unknown-unknown --no-default-features
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

`--backend haskell` selects symbolic modules and Haskell-specific generated axioms. Both modes
write:

- `definition.kore`
- `syntaxDefinition.kore`
- `macros.kore`

Parse a concrete program as textual KAST or KAST JSON v4:

```console
krust kast definition.k --module MAIN --sort Exp --expression '1 + 2'
krust kast definition.k --module MAIN --sort Exp program.exp --output json
```

Common source options:

- `-I DIR` / `--include DIR` adds a `requires` lookup directory.
- `--md-selector EXPR` selects Markdown fences; the default is `k`.
- `--builtin-directory DIR` overrides the bundled builtin sources.
- `KRUST_BUILTIN_DIRECTORY` provides the same override through the environment.
- `--no-prelude` disables the implicit `prelude.md` load.

## Node.js and TypeScript

The `k-rust-napi` crate builds a Node-API addon and a typed TypeScript facade. The facade accepts
in-memory definitions, resolves additional virtual sources used by `requires`, and returns typed
KAST JSON rather than exposing Rust implementation types.

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

The facade also exports `parseKast`, `printKast`, `parseKore`, `printKore`, and
`formatKoreDefinition`. The generated raw Node-API functions remain available from `native.js` for
hosts that want JSON strings and the lowest possible wrapper overhead.

Resolution checks explicit builtin overrides, the requiring file's directory, the working
directory, `-I` directories, and finally the embedded pinned sources.

## Compatibility evidence

The implementation is compared against these pinned references:

| Component | Commit |
|---|---|
| [`runtimeverification/k`](https://github.com/runtimeverification/k) | `4a46d1231473b599c699160132fd6e76a5c46406` (v7.1.337) |
| [`runtimeverification/scala-kore`](https://github.com/runtimeverification/scala-kore) | `844214975c` (v0.3.3) |

The outer parser accepts 1,499 of the 1,504 `.k` files probed at the pinned commit. Four rejected
files are intentional malformed-string tests; the fifth is a legacy `Token{...}` fixture also
rejected by the pinned JavaCC grammar.

The structural differential corpus compiles seven upstream definitions through both frontends,
strips source locations and generated sentence IDs, and compares every KORE module as a sentence
multiset. It covers append syntax, ambiguous rewrites, casts, collection-cell rewrites, fresh
variables, List/Set hooks, and rewrite macros:

```console
K_KOMPILE=/path/to/pinned/bin/kompile scripts/reference-differential.sh
scripts/reference-differential.sh casts cell-map  # selected cases
```

Set `K_CHECKOUT` if the ignored reference checkout is not at `k/`.

The backend acceptance gate consumes Rust-generated artifacts with the real backends:

```console
K_BACKEND_BIN=/path/to/pinned/bin scripts/backend-smoke.sh
```

It verifies an MPFR-folded FLOAT definition with Haskell's KORE verifier, loads and executes a
four-claim definition with `kore-exec`, generates LLVM matching decision trees for the collection
cell fixture, and links a native interpreter with `llvm-kompile`. `K_KOMPILE` may be supplied
instead; its sibling backend executables will be used.

## Development gates

CI runs the release-independent gates:

```console
cargo fmt --all -- --check
cargo build --workspace --all-targets --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --workspace --locked
cargo clippy --workspace --all-targets --no-default-features --locked -- -D warnings
cargo test --workspace --no-default-features --locked
cargo build --workspace --target wasm32-unknown-unknown --no-default-features --locked
```

Snapshot updates are intentional and source-driven. Review them locally with `cargo insta review`;
CI only runs ordinary tests and never accepts snapshots.

Release packaging is checked with:

```console
cargo package -p k-rust --locked
```

## Scope and known limitations

- Haskell and LLVM backend implementations remain external. `krust kcompile` emits their inputs;
  it does not invoke backend compilation itself.
- Context/freezer labels are semantically equivalent but can differ in numeric suffix assignment
  from Java when Java's `HashSet` traversal changes encounter order. The exact corpus does not
  normalize arbitrary user labels.
- The WASM-compatible feature set intentionally omits Z3 inference and MPFR constant folding.
- Coverage instrumentation and Haskell's optional unsafe-`anywhere` removal mode are not exposed by
  the CLI. They are identity stages unless explicitly requested in Java.
- LSP, `kserver`, backend execution commands such as `krun`/`kprove`, and Bison parser generation
  are outside the current frontend/CLI scope.

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
- Implement binary KORE input.
- Measure Z3-path usage across a substantially larger real-definition corpus.
- Revisit package splitting only if real build or release pressure justifies it.

## License

`k-rust` is distributed under the BSD 3-Clause License. The bundled K Framework builtin sources
retain their original copyright notices; see [NOTICE](NOTICE).
