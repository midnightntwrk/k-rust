# Readable KWasm qualification

Status: integer arithmetic and division/trap slices qualified; IMP regression green, 2026-08-26 JST

## Pinned authority

The external acceptance corpus is the clean sibling checkout at `../inspirations/runtimeverification/wasm-semantics`, relative to the repository root:

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

Excluded from the first slice are the text parser, floats, division traps, `requires`/`owise` partitions, locals, control flow, calls, memory, tables, module allocation, and multiplicity cells.
They remain inventory-backed next steps; exclusion is not a claim that KRS already supports them.

## Division and trap slice

The second slice ports KWasm's unsigned integer division partition and its `undefined`-to-`trap` transition:

1. the `div_u` integer binary operator;
2. the nonzero equation guarded by `I2 =/=Int 0`;
3. the zero equation guarded by `I2 ==Int 0` and returning `undefined`;
4. the `undefined` value and `trap` instruction;
5. the operational `<instrs> undefined => trap ... </instrs>` rule.

This slice deliberately does not port KWasm's global `owise` fallback for all unsupported integer binary operators.
The selected `add`, `sub`, `mul`, and `div_u` operators are exhaustive through unconditional equations or explicit zero/nonzero guards, so adding an `owise` surface would have no evidence-backed use here.
Remainder (`rem_u`, `rem_s`) remains deferred: unsigned division does not require it.
Full trap bubbling through label, frame, instruction, and definition continuations remains outside this slice together with those omitted constructs.

The behavior corpus covers exact division, truncation toward zero, operand order, and divide-by-zero traps for both widths.
Because corpus programs enter through the fixture's recursive `Instrs` adapter, a terminal trap retains the administrative `.Instrs ~> .K` suffix while remaining irreducible at the head; the verifier requires exactly that trap shape and an empty value stack.

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

### W2 — wraparound uses K's Euclidean modulus

KWasm defines `#chop(< ITYPE > N) => < ITYPE > (N modInt #pow(ITYPE))`.
The port's total wrap function `#kwasmChop` applies `int::rem_euclid`, which
emits `_modInt_`, with the literal modulus `2^32` or `2^64` for each width.

The slice originally had no modulo builtin and spelled the reduction as
`X -Int ((X /Int M) *Int M)`, which equals `X modInt M` only for nonnegative
`X`; the subtraction and constant rules therefore shift their argument by one
modulus before reduction. With `modInt` the shift is redundant but harmless,
since `(X +Int M) modInt M` is `X modInt M`; the rules keep it, so their
emitted K is unchanged.

The constant rules accept KWasm's i32/i64 literal ranges, including `-1`.

### W3 — guarded division and traps require no authoring extension

KRS already exposes typed `int::div`, `int::eq`, and `int::ne` builtins and retains `#[k::requires(...)]` conditions on equations.
The two explicit guards partition the selected `div_u` domain without source ordering or `owise`.
The existing constructor and readable machine-rule surfaces express `undefined`, `trap`, and the operational transition directly.
No descriptor protocol change is justified by the second slice.

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
- Definition IR compiles directly through the pinned K-Rust frontend;
- a matrix covering i32/i64 constants, operand order, add/sub/mul/div_u, nesting, zero, maximum values, wraparound, truncation, and divide-by-zero traps agrees with the pinned KWasm source;
- the relevant simple-arithmetic claim remains available for an explicit final reference run;
- the complete IMP behavior, proof, native, and compatibility evidence remains unchanged and the gate is green after the authoring extension.

Only gaps demonstrated by this evidence may change the normative readable
contract. Later slices should proceed to locals, structured control flow,
memory, and module/store multiplicity in that order unless an earlier gate
reveals a stronger dependency.

The canonical KRS port is `semantics/kwasm`.
The behavior and source corpus is `tests/kwasm/corpus.toml`.
The fail-closed qualification entry point is `python3 tests/kwasm/verify.py`.

## Qualification result

The default gate passes with KRS descriptor protocol 26, Definition IR schema 18, the pinned K-Rust frontend/backend, and the qualified rust-analyzer 1.97.1:

```text
PASS readable KWasm integer slice: 60 descriptors; 32 K-Rust executions; 1 reference proof deferred to --java-reference; protocol 26
```

The 32 native executions cover both integer widths, zero, maxima, negative constants, operand order, nesting, every selected add/sub/mul wraparound form, exact and truncated unsigned division, high-bit unsigned values, and divide-by-zero traps.
The checked-in all-path simple-addition claim remains pinned but is not run during routine development.
`python3 tests/kwasm/verify.py --java-reference` performs the deliberate final K toolchain comparison and proof.
Pins may be updated only after reviewing emitted K and structured behavior; re-record them by running the gate with `--record` (add `--java-reference` to re-record the kompiled reference digest) and review the pin diff.
`python3 tests/kwasm/verify.py --artifacts-only` stops after the emitted-artifact and native KORE pins and skips the behavior and proof comparisons; it passes only when every artifact is byte-identical to its pin (see `semantics/README.md`).
Six focused definition/hover probes pass with zero rust-analyzer diagnostics, including the new trap constructor.

Definition IR compiles directly to KORE through K-Rust with SHA-256 `35835f531a224c68f5ab63892448d2a2f60a6f0c268be521189a8f4df04245d1`.
The structured value-versus-trap behavior SHA-256 is `4a3b6107cb23fa451a392d0a0ef1d42203d5eb64cda8cbcda025e75d2458afd5`.

K-Rust is the routine correctness authority for compilation and concrete execution.
The adapter removes the bootstrap `DEFAULT-CONFIGURATION` before structured preparation, so KWasm's authored `<instrs>` computation cell cannot conflict with the prelude's fallback `<k>` cell.
Java/K toolchain comparison and proof are final-reference evidence only.

Descriptor protocol 19 and Definition IR schema 12 add K's selected `INT.mod` identity for the source-faithful KEVM arithmetic tranche.
KWasm behavior, emitted K, and native proof evidence remain unchanged because this baseline does not yet consume that shared operation directly.
Descriptor protocol 20 and Definition IR schema 13 add the selected integer exponentiation, logarithm, shift, and bitwise identities required by the KEVM Shanghai pure-word tranche.
KWasm again does not consume these operations in its current qualified slice, so its behavior, emitted K, KORE, and proof evidence remain unchanged.
The complete IMP gate also passes at descriptor protocol 20 and Definition IR schema 13.
Its emitted K, behavior, proofs, native KORE, and compatibility evidence remain unchanged across the shared Bytes and List additions.
The unchanged IMP behavior evidence remains `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, and the unchanged compatibility report remains `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.
