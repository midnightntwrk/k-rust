# Readable KEVM qualification

Status: Bytes-backed core arithmetic slice qualified, 2026-08-26 JST

## Pinned authority

The external acceptance corpus is the clean checkout at
`../../../../inspirations/runtimeverification/evm-semantics`:

- commit `d818397e9b7ffa213d687e64418dc8f5293e1ce2`;
- K release `7.1.337` from `deps/k_release`, exactly matching KRS;
- core semantics in `kevm-pyk/src/kevm_pyk/kproj/evm-semantics/`;
- derived opcode summaries in that directory's `summaries/` package.

The KEVM checkout and the recovery evidence remain read-only. KRS owns this
fixture and every generated acceptance artifact.

## Corpus inventory

The principal KEVM files contain 7,231 lines, 346 syntax declarations, 2,119
rules, 191 `requires` occurrences, and one large nested configuration. The
selected production roots alone include:

| file | lines | rules | `requires` | `owise` |
|---|---:|---:|---:|---:|
| `evm-types.md` | 484 | 118 | 68 | 5 |
| `evm.md` | 3,348 | 778 | 158 | 52 |
| `gas.md` | 583 | 360 | 46 | 6 |
| `schedule.md` | 517 | 222 | 26 | 0 |
| `word.md` | 673 | 314 | 8 | 7 |
| `state-utils.md` | 730 | 99 | 16 | 4 |
| `driver.md` | 804 | 218 | 54 | 5 |

There are also 71 checked-in opcode-summary modules containing 145 rules and
792 claims under `tests/specs`, including 506 functional claims. Full KEVM
additionally uses bytes, maps, sets, bags, multiplicity cells, accounts,
transactions, memory, storage, calls, access lists, fork schedules, cryptographic
hooks, and symbolic summaries. This milestone does not claim those features.

## Representative operational slice

The current slice follows KEVM's `#next`/`#exec`/`#gas`/`#pc` pipeline, its unsigned word operations, and the checked-in `push`, `add`, `sub`, `div`, `mod`, `pc`, `gas`, `stop`, and `invalid` summaries:

1. a recursive word stack and K's builtin `Bytes` program domain;
2. `PUSH`, `ADD`, `MUL`, `SUB`, `DIV`, `MOD`, `PC`, `STOP`, and `INVALID` opcodes;
3. simultaneous program, stack, program-counter, gas, and status transitions;
4. `PUSH` widths and their effect on the program counter;
5. modulo-`2^256` word normalization for addition, multiplication, and subtraction;
6. KEVM's zero-divisor result for unsigned division and modulus;
7. Shanghai-compatible `Glow = 5`, `Gverylow = 3`, `Gbase = 2`, and `Gzero = 0` costs;
8. the guarded sufficient-gas/out-of-gas partition from `#deductGas`;
9. structural zero/one-element binary-op stack-underflow branches;
10. successful stop/end-of-program and invalid-instruction outcomes;
11. two all-path native claims spanning push, both gas classes, arithmetic, PC observation, and successful halt.

KEVM stores executable code as `Bytes` and decodes it with `#lookupOpCode`.
The KRS definition now uses the pinned `BYTES` implementation directly: `lengthBytes(PROGRAM)` bounds lookup, `PROGRAM [ PC ]` reads the opcode byte, and a recursive big-endian decoder reads `PUSH1` through `PUSH32` immediates.
The operational effects after decoding remain mapped to the checked-in summary rules.
The program bytes remain unchanged across execution, matching KEVM's program-cell boundary.

## Source mapping

- `evm.md` configuration: `<program>`, `<wordStack>`, `<pc>`, `<gas>`, and
  `<statusCode>` cells;
- `evm.md` single-step and exceptional checks: `#next`, `#exec`, stack
  underflow, `#pc`, and end status;
- `evm.md` opcode rules: `#push`, `PUSH`, core unsigned binary arithmetic, `PC`, `STOP`, and `INVALID`;
- `evm.md` gas rules: `#gas`, `#deductGas`, and the out-of-gas status;
- `word.md`: `Word`, `WordStack`, and `chop` modulo `2^256`;
- `evm-types.md`: unsigned word arithmetic and zero-totalized division and modulus;
- `schedule.md`: the selected Shanghai gas constants;
- `summaries/push-summary.k`, `add-summary.k`, `sub-summary.k`, `div-summary.k`, `mod-summary.k`, `pc-summary.k`, `gas-summary.k`, `stop-summary.k`, and `invalid-summary.k`: direct multi-cell transition oracles.

## Selected KRS extension

Descriptor protocol 17 and Definition IR schema 10 introduced the pinned `Bytes` sort, `BYTES.length`, `BYTES.get`, and claim-only byte tokens.
The compiler emits the native K surface exactly as `Bytes`, `lengthBytes(B)`, `B [ I ]`, and `b"\xhh..."`.
The token transport is canonical lower hexadecimal and rejects malformed or noncanonical descriptor payloads.
Reference expansion reconstructs `k::bytes!(b"...")` without retaining target-specific token text in authored Rust.

Descriptor protocol 19 and Definition IR schema 12 select K's builtin `INT.mod` operation.
KRS emits `int::modulo(A, B)` exactly as `A modInt B` and preserves that typed builtin identity through descriptors, Semantic IR, Definition IR, reference expansion, and native adaptation.
`#kevmChop` now uses the pinned operation directly, matching upstream behavior for negative subtraction intermediates rather than approximating Euclidean modulus with truncating division.

Deferred corpus shapes include the remaining Bytes operations, `%Int`, `owise`,
rule-table guards, nested/multiplicity configurations, bags and sets, map
lookup/update beyond the existing finite-map surface, cell collections,
heating/cooling attributes beyond the current contract, priorities used for
summary override, and KEVM's full symbolic claim language. A later slice may
extend KRS only when one of those shapes is selected as acceptance evidence.

## Acceptance contract

The checked-in gate must establish deterministic collection/expansion,
formatting, warnings-denied Clippy, focused rust-analyzer probes, emitted-K
compilation under K 7.1.337, native behavior for the selected normal and
exceptional paths, a closed native proof, and unchanged complete IMP and
KWasm regressions. Pins may be updated only after reviewing emitted K and
structured behavior.

The canonical KRS port is `semantics/kevm`, the corpus is
`tests/kevm/corpus.toml`, and the fail-closed entry point is
`python3 tests/kevm/verify.py`.

## Qualification result

The refreshed complete gate passes at descriptor protocol 19 and Definition IR schema 12:

```text
PASS readable KEVM operational slice: 131 descriptors; 25 executions; 2 native proofs; protocol 19; K 7.1.337
```

The behavior matrix adds normal and wraparound multiplication, top-first subtraction and negative wraparound, unsigned division and modulus including zero divisors, `Glow` out-of-gas, family underflow, and a combined arithmetic path to the prior baseline.
The structured behavior SHA-256 is `94652cf0651fc95b2e4746f5945463ea7591d6eae50463f3dabe4d7cf83ca16a`.
Both all-path claims close with `#Top` through native `kprove`.
The normalized native `definition.kore` SHA-256 is `64846d863fb029bfd4a33626ef52c410ef6a89fe7b54853c1d7927e69a3935bd`.
Normalization is limited to the temporary semantics path and K-generated
sort-membership binder names, using the already-qualified KWasm policy.
Six focused definition/hover probes pass with zero rust-analyzer diagnostics.

This result removes the structured-program adapter without widening the qualified opcode set.
The remaining opcode families and stateful EVM surfaces remain explicit future evidence, not implicit claims.
