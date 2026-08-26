# Readable KWasm qualification

Status: first slice qualified; IMP regression green, 2026-08-26 JST

## Pinned authority

The external acceptance corpus is the clean checkout at `../inspirations/runtimeverification/wasm-semantics`:

- commit `212271bd434bd402e27c42f6416854342733386d`;
- K release `7.1.329` from `deps/k_release`;
- core semantics under `pykwasm/src/pykwasm/kdist/wasm-semantics/` in `wasm-data.md`, `numeric.md`, and `wasm.md`.

KRS continues to use its own K `7.1.337` toolchain. The qualification must
distinguish a real language/tool-version incompatibility from an authoring
gap; it must not edit the KWasm checkout or silently copy changed semantics.

## Corpus inventory

KWasm is substantially different from IMP in the dimensions this phase is
intended to test:

- `wasm-data.md` defines lexical tokens, subsorts, recursive list sorts,
  typed values, hooks, functions, and concrete/symbolic module variants;
- `numeric.md` contains 94 functional rules, including total functions,
  side conditions, `owise`, integer wraparound, floating-point operations,
  and conversions;
- `wasm.md` contains the real 183-rule transition system and a nested
  configuration rooted at `<wasm>`. Its operational front consists of
  `<instrs>`, `<valstack>`, and `<curFrame>`/`<locals>`, followed by module
  registries and multiplicity-backed function, table, memory, global, and
  element stores;
- the text layer contains 299 translation rules and is intentionally separate
  from the abstract execution semantics;
- the six checked-in proof specifications contain 41 claims: functions (28),
  locals (3), loops (2), memory (2), simple arithmetic (5), and WRC-20 (1).

The module split is also part of the corpus contract: syntax, internal syntax,
concrete data, symbolic data, numeric functions, abstract execution, text
translation, test harness, and proof lemmas are distinct imports. A later
larger port must not flatten those boundaries merely because the first slice
is small.

## First representative slice

Port the abstract integer-arithmetic execution path used by
`tests/simple/arithmetic.wast` and `tests/proofs/simple-arithmetic-spec.k`:

1. integer value types `i32` and `i64`;
2. typed integer values and a recursive value stack;
3. integer constants;
4. binary `add`, `sub`, and `mul` instructions;
5. the real `<instrs>`/`<valstack>` two-cell transition that pops operands in
   WebAssembly order and pushes the typed result;
6. modulo-`2^32` and modulo-`2^64` wraparound.

The source mapping is deliberately narrow and reviewable:

- `wasm-data.md`: `IValType`, `IVal`, `Val`, and `ValStack` declarations;
- `numeric.md`: `IBinOp`, `intBinOp`, and the `add`/`sub`/`mul` rules;
- `wasm.md`: `PlainInstr` integer constant/binary productions, the
  `<instrs>`/`<valstack>` configuration cells, constant execution, binary
  operand loading, and value transfer;
- `tests/simple/arithmetic.wast`: direct and folded arithmetic examples;
- `tests/proofs/simple-arithmetic-spec.k`: the constant and addition claims.

This is representative rather than synthetic: it crosses functional and
operational modules, mutates two real KWasm cells, observes operand order, and
includes the bounded-integer behavior that distinguishes WebAssembly from
unbounded IMP arithmetic.

Excluded from the first slice are the text parser, floats, division traps,
`requires`/`owise` partitions, locals, control flow, calls, memory, tables,
module allocation, and multiplicity cells. They remain inventory-backed next
steps; exclusion is not a claim that KRS already supports them.

## Gaps exposed by the slice

### W1 — ordinary fixed-cell rewrites

Readable `for Machine` rules currently require one computation-cell head and
support other cells only as framed map reads or whole-map updates. KWasm's
operand rules must simultaneously rewrite `<instrs>` and an ordinary
`ValStack` cell.

The readable machine table now permits a non-computation leaf to carry an ordinary constructor pattern and replacement term.
The implementation preserves the existing explicit `cells!` layer, sort inference, stable identities, provenance, deterministic expansion, and overlap rejection.
The KWasm fixture uses the real recursive value stack; it does not encode the value stack as a map or move it into `<instrs>`.

The first use also demonstrates that repeated symbolic equality is not part of the readable pattern surface.
The width-preserving operand rule is therefore split into explicit `i32` and `i64` cases instead of weakening the KWasm same-type invariant.

### W2 — wraparound does not require a new builtin

KRS exposes K integer addition, subtraction, multiplication, and truncating
division, but not `_modInt_`. The selected KWasm invariant keeps values in
`0 <=Int I <Int 2^N`; additions and products are nonnegative, and subtraction
can be shifted by one modulus before reduction. On that domain,
`X -Int ((X /Int M) *Int M)` is exactly `X modInt M`.

Define one total, Rust-checked wrap function with the existing function and
equation surface, and feed subtraction a nonnegative shifted value. This is an
exact implementation for the selected rules and avoids expanding the builtin
protocol without evidence that it is needed. A later operation that genuinely
requires K's modulo identity may reopen the builtin question.

The implemented constant rules also shift accepted signed literals by one modulus before applying the same reduction.
This matches KWasm's accepted i32/i64 literal ranges, including `-1`, without adding a modulo builtin.

No condition/`owise` extension is justified by this slice. Division and trap
rules should be the next numeric increment precisely because they will force
that decision with concrete KWasm evidence.

## Acceptance evidence

The slice is complete only when one checked-in gate establishes all of the
following:

- readable Rust compiles under the KRS MSRV and current toolchain;
- `krs fmt --check`, Rustfmt, warnings-denied Clippy, and focused LSP probes
  pass;
- collection retains exact authored anchors for the new cell patterns,
  results, and modulo application;
- stable identities and deterministic expansion are pinned, and the expanded
  Rust compiles independently;
- emitted K parses and compiles under the KRS-pinned K toolchain;
- a matrix covering i32/i64 constants, operand order, add/sub/mul, nesting,
  zero, maximum values, and wraparound agrees with the pinned KWasm source;
- the relevant simple-arithmetic claim shape is reproduced or explicitly
  shown equivalent by the native proof route;
- the complete IMP M4 behavior, proof, native, and compatibility evidence remains unchanged and the gate is green after the authoring extension.

Only gaps demonstrated by this evidence may change the normative readable
contract. Later slices should proceed to locals, structured control flow,
memory, and module/store multiplicity in that order unless an earlier gate
reveals a stronger dependency.

The checked-in specimen is `tests/kwasm/rust-definition`.
The behavior and source corpus is `tests/kwasm/corpus.toml`.
The fail-closed qualification entry point is `python3 tests/kwasm/verify.py`.

## Qualification result

The complete gate passes with KRS descriptor protocol 16, Definition IR schema 9, K 7.1.337, and the qualified rust-analyzer 1.97.1:

```text
PASS readable KWasm integer slice: 51 descriptors; 22 executions; 1 native proof; protocol 16; K 7.1.337
```

The 22 native executions cover both integer widths, zero, maxima, negative constants, operand order, nesting, and every selected add/sub/mul wraparound form.
The checked-in all-path simple-addition claim closes with `#Top` through `kprove`.
Five focused definition/hover probes pass with zero rust-analyzer diagnostics.

The native `definition.kore` pin normalizes only the temporary absolute `semantics.k` path and K-generated alpha names in the standard `isSort` membership axioms.
Three independent compilations converge to normalized SHA-256 `dc093e74aa1fc2b3b5d5eea6a4e09b9e5f342439d119ad89d9440585827fa2a1`.
The pinned behavior SHA-256 is `b187d3e4d2326083b44f8d915542e22ccfa1de4b88a4b30e8f9def891e646d8f`.

The acceptance contract is emitted K compilation, execution, and proof.
An optional direct structured `k-rust` compilation experiment reaches an unrelated no-map embedded-prelude `Map:lookup` failure and is deliberately outside this slice's gate.

The complete IMP M4 gate also passes after W1 at descriptor protocol 16.
Its semantic, behavior, proof, native KORE, and compatibility evidence is unchanged; only the descriptor bundle records the new protocol number.
The unchanged IMP behavior evidence remains `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, and the unchanged compatibility report remains `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.
