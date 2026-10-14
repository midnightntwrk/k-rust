# Readable KEVM qualification

Status: nonempty-code and address-1 through address-6 precompile STATICCALL qualified through K-Rust, 2026-08-27 JST

## Pinned authority

The external acceptance corpus is the clean sibling checkout at
`inspirations/runtimeverification/evm-semantics` in the reference checkouts directory (README, Prerequisites):

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
hooks, and symbolic summaries.
This milestone claims only the explicitly listed storage, account-query, log, return/revert, nonempty-code `STATICCALL`, and ECREC/SHA-256/RIPEMD-160/identity/MODEXP/ECADD/ECMUL-precompile `STATICCALL` subset of those surfaces.

## Representative operational slice

The current slice follows KEVM's `#next`/`#exec`/`#gas`/`#pc` pipeline, its core word operations, and the checked-in arithmetic, `push`, `pc`, `gas`, `stop`, and `invalid` summaries:

1. a recursive word stack and K's builtin `Bytes` program domain;
2. `PUSH0`, `PUSH1` through `PUSH32`, `POP`, `DUP1` through `DUP16`, `SWAP1` through `SWAP16`, `ADD`, `MUL`, `SUB`, `DIV`, `SDIV`, `MOD`, `SMOD`, `ADDMOD`, `MULMOD`, `EXP`, `SIGNEXTEND`, `LT`, `GT`, `SLT`, `SGT`, `EQ`, `ISZERO`, `AND`, `OR`, `XOR`, `NOT`, `BYTE`, `SHL`, `SHR`, `SAR`, `SHA3`, `ADDRESS`, `BALANCE`, `ORIGIN`, `CALLER`, `CALLVALUE`, `CALLDATALOAD`, `CALLDATASIZE`, `CALLDATACOPY`, `CODESIZE`, `CODECOPY`, `GASPRICE`, `EXTCODESIZE`, `EXTCODECOPY`, `RETURNDATASIZE`, `RETURNDATACOPY`, `EXTCODEHASH`, `BLOCKHASH`, `COINBASE`, `TIMESTAMP`, `NUMBER`, `PREVRANDAO`, `GASLIMIT`, `CHAINID`, `SELFBALANCE`, `BASEFEE`, `MLOAD`, `MSTORE`, `MSTORE8`, `SLOAD`, `SSTORE`, `MSIZE`, `GAS`, `PC`, `JUMP`, `JUMPI`, `JUMPDEST`, `LOG0` through `LOG4`, `RETURN`, `REVERT`, absent/present-empty non-precompile `STATICCALL`, successful, reverted, or exceptional nonempty-code `STATICCALL`, ECREC, SHA-256, RIPEMD-160, identity, MODEXP, ECADD, and ECMUL-precompile `STATICCALL`, `STOP`, and `INVALID` opcodes;
3. simultaneous program, stack, program-counter, gas, and status transitions;
4. `PUSH` widths and their effect on the program counter;
5. modulo-`2^256` word normalization for addition, multiplication, and subtraction;
6. KEVM's two's-complement word sign and magnitude, signed division including minimum-word overflow, and dividend-signed modulus;
7. zero-totalized unsigned and signed division and modulus;
8. unbounded addition and multiplication intermediates before the `ADDMOD` and `MULMOD` modulus;
9. unsigned and two's-complement signed comparison, word equality, Boolean-to-word conversion, and unary zero testing;
10. modular exponentiation, Shanghai exponent-byte gas charging, byte-indexed sign extension, big-endian byte extraction, bitwise operations, and totalized logical and arithmetic shifts;
11. recursive stack size, depth-indexed lookup, and depth-indexed replacement for `POP`, `DUP`, and `SWAP`;
12. the 1,024-word `DUP` stack-overflow boundary and family-specific underflow partitions;
13. bytecode-scanned jump-destination validation that rejects out-of-range destinations, non-`JUMPDEST` opcodes, and `0x5b` bytes inside `PUSH1` through `PUSH32` immediate data;
14. Shanghai-compatible `Glog = 375`, `Glogdata = 8`, `Glogtopic = 375`, `Gblockhash = 20`, `Gexp = 10`, `Gexpbyte = 50`, `Ghigh = 10`, `Gmid = 8`, `Glow = 5`, `Gverylow = 3`, `Gbase = 2`, `Gjumpdest = 1`, and `Gzero = 0` costs;
15. the guarded sufficient-gas/out-of-gas partition from `#deductGas`;
16. structural unary, binary, ternary, depth-indexed, and control-flow stack-underflow branches;
17. exact selected transaction, call, block, chain, return-data-size, code-size, and post-charge gas observations through their upstream configuration cells;
18. exact `<blockhashes>` builtin-List traversal for `BLOCKHASH`, including current and future block rejection, the 256-block cutoff, and the upstream zero sentinel;
19. zero-padded big-endian `MLOAD`, padded 32-byte `MSTORE`, low-byte `MSTORE8`, and `MSIZE` over exact `<localMem>:Bytes` and `<memoryUsed>:Int` cells;
20. 32-byte memory growth and `Cmem(N) = 3*N + N*N/512` expansion charging at the quadratic boundary;
21. zero-padded big-endian `CALLDATALOAD` plus byte-exact `CALLDATACOPY`, `CODECOPY`, and bounded `RETURNDATACOPY` over the existing Bytes cells;
22. `Gcopy * ceil(width / 32)` charging, zero-width non-expansion, source zero padding, and charged `EVMC_INVALID_MEMORY_ACCESS` return-data bounds failure;
23. a repeated `<account multiplicity="*" type="Map">` configuration with nested `<acctID>`, `<balance>`, `<code>`, `<nonce>`, `<storage>`, and `<origStorage>` state, selected by explicit account identity;
24. `SLOAD` zero fallback, warm/cold access tracking through `<accessedStorage>:Map` of `Set`s, and exact 100/2100 charging;
25. Shanghai `SSTORE` clean, dirty, no-op, set, reset, clear, and restoration costs; 4,800/19,900/2,800 refund cases; stipend and static-mode precedence; and mutation only after successful charge;
26. Berlin warm/cold account access through `<accessedAccounts>:Set`, exact 100/2600 charging, and access marking only after a successful charge;
27. `BALANCE` and `EXTCODESIZE` lookup for present accounts with ordered absent-account fallback to zero;
28. byte-exact `EXTCODECOPY` with right-zero padding, memory expansion, copy-word charging, and atomic OOG behavior;
29. `SELFBALANCE` over the current account without external-account access charging;
30. `LOG0` through `LOG4` append behavior over the exact builtin-List `<log>` cell, ordered topic consumption, byte-exact zero-padded memory data, static rejection, underflow precedence, and post-charge mutation;
31. byte-exact, zero-padded `RETURN` and `REVERT` output extraction, memory expansion charging, pre-charge OOG ordering, stack failures, and terminal success/revert statuses;
32. successful `STOP` and end-of-program behavior, including `STOP` clearing `<output>` through K's pinned `.Bytes` operation, plus bad-jump-destination and invalid-instruction outcomes;
33. EIP-150 all-but-one-64th `STATICCALL` gas capping, child-context installation, complete 15-field call-state save/restore through the builtin-List `<callStack>`, successful child `STOP`, caller gas restoration, and success-result propagation;
34. typed selected-account and complete-substate snapshots through `<interimStates>`, snapshot dropping on success, rollback on revert or exceptional status, zero/one result propagation, revert-only child-gas refund, bounded return-data copying, and empty call/world stack postconditions;
35. Shanghai identity-precompile execution at address 4 with exact `15 + 3 * ceil(input-width / 32)` charging, EIP-150 forwarded-gas success/failure, byte-exact returndata, bounded caller-memory copying, access warming, and empty call/world stack postconditions;
36. Shanghai SHA-256 precompile execution at address 2 through `KRYPTO.sha256raw` with exact `60 + 12 * ceil(input-width / 32)` charging and the same qualified call-result boundaries;
37. Shanghai RIPEMD-160 precompile execution at address 3 through `KRYPTO.ripemd160raw` with exact `600 + 120 * ceil(input-width / 32)` charging, a byte-exact 20-byte digest left-padded to 32 bytes, and the same qualified call-result boundaries;
38. Shanghai ECREC precompile execution at address 1 through `KRYPTO.ecdsaRecover` with fixed 3,000 gas charging, zero-padded 128-byte input splitting, valid recovered-address output, successful empty output for invalid signatures, and forwarded-gas failure;
39. Berlin EIP-2565 MODEXP precompile execution at address 5 with zero-padded length and operand parsing, exact modulus-width output, total modulus-zero behavior, adjusted exponent length, exact minimum and above-minimum gas charging, and forwarded-gas failure;
40. Istanbul ECADD precompile execution at address 6 through `KRYPTO.bn128valid` and `KRYPTO.bn128add` with zero-padded 128-byte input, the `(0, 0)` point-at-infinity encoding, field and curve validation, exact 64-byte output, fixed 150 gas charging, invalid-point failure, and forwarded-gas failure;
41. Istanbul ECMUL precompile execution at address 7 through `KRYPTO.bn128valid` and `KRYPTO.bn128mul` with zero-padded 96-byte input, complete 256-bit scalar reduction, the `(0, 0)` point-at-infinity encoding, field and curve validation, exact 64-byte output, fixed 6,000 gas charging, invalid-point failure, and forwarded-gas failure;
41. eight all-path claims, including a combined calldata-load and three-source copy execution through successful halt.

KEVM stores executable code as `Bytes` and decodes it with `#lookupOpCode`.
The KRS definition now uses the pinned `BYTES` implementation directly: `lengthBytes(PROGRAM)` bounds lookup, `PROGRAM [ PC ]` reads the opcode byte, `PUSH0` pushes zero without immediate data, and a recursive big-endian decoder reads `PUSH1` through `PUSH32` immediates.
The operational effects after decoding remain mapped to the checked-in summary rules.
The program bytes remain unchanged across execution, matching KEVM's program-cell boundary.
`JUMP` and true `JUMPI` scan those same bytes from offset zero, advancing over
entire PUSH instructions so immediate data cannot become an executable jump
destination. False `JUMPI` deliberately bypasses destination validation, as in
the pinned `jumpi.false` rule.

## Source mapping

- `evm.md` configuration: nested `<callState>` and `<substate>`, `<callStack>`, `<interimStates>`, `<touchedAccounts>`, repeated `<accounts>/<account>` with `<acctID>`, `<balance>`, `<code>`, `<storage>`, and `<origStorage>`, and the selected transaction, memory, block, stack, gas, status, access, refund, static, and log cells;
- `evm.md` single-step and exceptional checks: `#next`, `#exec`, stack underflow, stack overflow, `#pc`, and end status;
- `evm.md` opcode rules: `#push`, `PUSH`, `POP`, `DUP`, `SWAP`, core unsigned, signed, and ternary modular arithmetic, exponentiation, sign extension, comparison, bitwise, byte, shift, the selected execution-context operations, recursive `#blockhash`, memory growth and expansion cost, `MLOAD`, `MSTORE`, `MSTORE8`, `MSIZE`, `CALLDATALOAD`, `CALLDATACOPY`, `CODECOPY`, `BALANCE`, `EXTCODESIZE`, `EXTCODECOPY`, `SELFBALANCE`, `RETURNDATACOPY`, `GAS`, `PC`, `JUMP`, `JUMPI`, `JUMPDEST`, `LOG0` through `LOG4`, `RETURN`, `REVERT`, successful `STATICCALL` setup/return, and the address-1 `ECREC`, address-2 `SHA256`, address-3 `RIP160`, address-4 `ID`, address-5 `MODEXP`, address-6 `ECADD`, and address-7 `ECMUL` precompiles, `STOP`, and `INVALID`;
- `evm.md` gas rules: `#gas`, `#deductGas`, and the out-of-gas status;
- `word.md`: `Word`, `WordStack`, and `chop` modulo `2^256`;
- `evm-types.md`: unsigned word arithmetic, two's-complement sign and magnitude, signed division and modulus, zero-totalized word division and modulus, Boolean-to-word conversion, word comparisons, byte selection, sign extension, and signed shifting;
- `schedule.md`: the selected Shanghai gas constants;
- `summaries/push-summary.k`, `pop-summary.k`, `dup-summary.k`, `swap-summary.k`, the selected arithmetic and comparison summaries, `calldataload-summary.k`, `calldatacopy-summary.k`, `codecopy-summary.k`, `returndatacopy-summary.k`, `log-summary.k`, `pc-summary.k`, `gas-summary.k`, `blockhash-summary.k`, `jumpdest-summary.k`, `stop-summary.k`, and `invalid-summary.k`: direct multi-cell transition oracles.

## Selected KRS extension

Descriptor protocol 17 and Definition IR schema 10 introduced the pinned `Bytes` sort, `BYTES.length`, `BYTES.get`, and claim-only byte tokens.
The compiler emits the native K surface exactly as `Bytes`, `lengthBytes(B)`, `B [ I ]`, and `b"\xhh..."`.
The token transport is canonical lower hexadecimal and rejects malformed or noncanonical descriptor payloads.
Reference expansion reconstructs `k::bytes!(b"...")` without retaining target-specific token text in authored Rust.

Descriptor protocol 19 and Definition IR schema 12 select K's builtin `INT.mod` operation.
KRS emits `int::rem_euclid(A, B)` (named `int::modulo` before the builtin naming rule; Rust's `i64::rem_euclid` has the same semantics) exactly as `A modInt B` and preserves that typed builtin identity through descriptors, Semantic IR, Definition IR, reference expansion, and native adaptation.
`#kevmChop` now uses the pinned operation directly, matching upstream behavior for negative subtraction intermediates rather than approximating Euclidean modulus with truncating division.

Descriptor protocol 20 and Definition IR schema 13 select the pinned integer operations required by the Shanghai pure-word tranche: modular exponentiation, base-two logarithm, left and right shifts, and bitwise `and`, `xor`, and `or`.
KRS preserves the seven typed builtin identities through descriptors, Semantic IR, Definition IR, reference expansion, canonical K emission, and native frontend adaptation.
The KEVM port composes those selected operations with existing integer arithmetic to reproduce the upstream word boundary, including explicit guards that totalize shifts of 256 bits or more.

Descriptor protocol 21 and Definition IR schema 14 select K's pinned `BYTES.empty` operation.
KRS exposes it as `bytes::empty()`, emits the upstream `.Bytes` spelling, and preserves its typed zero-argument identity through descriptors, Semantic IR, Definition IR, reference expansion, canonical K emission, and native frontend adaptation.
The KEVM `STOP` rule uses this operation to clear `<output>` exactly as the pinned upstream rule requires.

Descriptor protocol 22 and Definition IR schema 15 select K's pinned `BYTES.update` and `BYTES.padRight` operations.
KRS exposes them as `bytes::update` and `bytes::pad_right`, emits the upstream update and padding spellings, and preserves their typed identities through the complete structured and native compilation route.
The KEVM memory rules use them to write individual bytes and extend memory without a port-local byte-array adapter.

Descriptor protocol 23 and Definition IR schema 16 add typed Map lookup and key membership plus the builtin Set sort and its empty, item, concatenation, and membership operations.
K's `Set` concatenation is defined only on disjoint operands: concatenating a set with an element it already holds is `#Bottom` in the Haskell backend and in K-Rust at the pinned revision, although Java K's LLVM backend silently accepts it.
KRS exposes the pinned `|Set` union as `set::union`, so the port inserts access-list, touched-account, and accessed-storage elements with the same operation used by upstream KEVM.
Descriptor protocol 24 and Definition IR schema 17 add classified repeated-cell multiplicity and collection type, retain nested-cell ancestry for rule emission, and transport readable head-rule `requires` clauses end to end.
Canonical K and native K-Rust compilation therefore preserve the account collection boundary instead of flattening storage leaves into top-level adapter cells.
Deterministic reference expansion preserves the same boundary with owner-qualified nested fields, so the independently expanded Rust compiles, re-collects, and emits the same configuration and sentence identities.

Descriptor protocol 25 adds typed `#[k::rule(owise)]` metadata and preserves its provenance through ordinary, head, and configuration rules.
Semantic and Definition IR lower the fallback to effective priority 200, while canonical K emission uses `[priority(200)]` and readable expansion retains the authored `owise` spelling.
The account-query rules use this ordered fallback only for absent accounts, after the explicit account-identity rule has had the opportunity to match.

Descriptor protocol 26 and Definition IR schema 18 add a closed typed function-hook boundary.
The selected `krypto::keccak256_raw` identity remains `Bytes -> Bytes` through descriptor transport, both IRs, canonical K emission as `KRYPTO.keccak256raw`, readable expansion, and direct K-Rust adaptation.
The KEVM `SHA3` rules use that hook for byte-exact memory hashing and convert the 32-byte digest to the unsigned EVM word in big-endian order.

Descriptor protocol 27 and Definition IR schema 19 add `krypto::sha256_raw` to that closed hook catalog.
The selected identity remains `Bytes -> Bytes` through the same complete route and emits as `KRYPTO.sha256raw` for the pinned KEVM SHA-256 precompile.

Descriptor protocol 28 and Definition IR schema 20 add `krypto::ripemd160_raw` to the closed hook catalog.
The selected identity emits as `KRYPTO.ripemd160raw`; the KEVM boundary left-pads its 20-byte result to the required 32-byte precompile output.

Descriptor protocol 29 and Definition IR schema 21 add `krypto::ecdsa_recover` to the closed hook catalog.
The selected `Bytes * Int * Bytes * Bytes -> Bytes` identity emits as `KRYPTO.ecdsaRecover`; the KEVM boundary splits and zero-pads the 128-byte precompile input, hashes the recovered public-key coordinates, and returns either the 32-byte padded address or empty Bytes for an invalid signature.

Descriptor protocol 30 and Definition IR schema 22 add the declared-sort `krypto::bn128_valid` and `krypto::bn128_add` identities.
The hook boundary enforces `G1Point -> Bool` validity and `G1Point * G1Point -> G1Point` addition without encoding the definition-owned point sort as a KRS builtin.
The canonical and native adapters emit the exact `KRYPTO.bn128valid` and `KRYPTO.bn128add` hook names.

Descriptor protocol 31 and Definition IR schema 23 add the declared-sort `krypto::bn128_mul` identity.
The hook boundary enforces `G1Point * Int -> G1Point`, and both adapters emit the exact `KRYPTO.bn128mul` hook name.

The declared-sort `krypto::bn128_g2_valid` identity and builtin-List `krypto::bn128_ate` identity support the pairing precompile.
The hook boundary enforces `G2Point -> Bool` and `List * List -> Bool`, and both adapters emit the exact `KRYPTO.bn128g2valid` and `KRYPTO.bn128ate` hook names.

Deferred corpus shapes include the remaining Bytes operations, `%Int`, rule-table guards, broader nested/multiplicity configurations, bags, map operations beyond the selected surface, additional cell collections, heating/cooling attributes beyond the current contract, non-fallback priorities used for summary override, and KEVM's full symbolic claim language.
A later slice may extend KRS only when one of those shapes is selected as acceptance evidence.

## Acceptance contract

The checked-in development gate must establish deterministic collection and expansion, formatting, warnings-denied Clippy, focused rust-analyzer probes, emitted-K compilation under K 7.1.337, and K-Rust behavior for the selected normal and exceptional paths.
The Java/K behavior and proof gate remains available through explicit `--java-reference` validation.
That route must compare each supported Java outcome with the native outcome for the same corpus id and report a case-level mismatch.
The native behavior digest remains pinned; Java behavior is established by this case-level agreement.
Pins may be updated only after reviewing emitted K and structured behavior; re-record them by running the gate with `--record` (add `--java-reference` to re-record the kompiled reference digest) and review the pin diff.
`python3 tests/kevm/verify.py --artifacts-only` stops after the emitted-artifact and native KORE pins and skips the behavior and proof comparisons; it passes only when every artifact is byte-identical to its pin (see `semantics/README.md`).

The canonical KRS port is `semantics/kevm`, the corpus is
`tests/kevm/corpus.toml`, and the fail-closed entry point is
`python3 tests/kevm/verify.py`.

## Qualification result

The development gate executes the full corpus through K-Rust and defers Java reference behavior and proofs to `--java-reference`.

The behavior matrix additionally covers present and absent accounts, EIP-161 account emptiness across code, nonce, and balance, warm and cold account access, byte-exact external code copying and hashing, log memory extraction and zero padding, ordered topics, SHA3 empty and expanded-memory hashing, successful/reverted/exceptional warm-account nonempty-code `STATICCALL`, child access-list rollback, revert returndata copying, ECREC/SHA-256/RIPEMD-160/identity/MODEXP/ECADD/ECMUL/ECPAIRING-precompile success and forwarded-gas failure, invalid-signature ECREC success with empty returndata, MODEXP modulus-zero and zero-output-width results, the 200-gas EIP-2565 floor, an above-floor long-exponent vector, ECADD infinity and invalid-point behavior, ECMUL generator-times-two and zero-scalar infinity behavior, ECPAIRING empty-product identity, non-identity generator product, malformed length, invalid G1/G2 points, post-charge mutation, atomic out-of-gas behavior, static rejection, all selected stack-underflow partitions, and self-balance lookup.
The structured K-Rust behavior SHA-256 is `7d7fd9dac9d3088682fa3ea27686c2a431219ded26f8a13400d2f4025f024673`.
KRS passes complete fixed-arity cells directly to the structured frontend.
Six focused definition/hover probes pass with zero rust-analyzer diagnostics.

The K-Rust backend executes all 240 cases through persistent worker processes.
The K-Rust frontend compiles Definition IR directly to KORE, so ordinary qualification invokes no Java process.
k-rust includes `KRYPTO` in its default backend hook metadata and accepts already-complete fixed-arity nested cells such as the 15-child `CallState`, so KRS needs no workaround for either.
The eight Java/K proofs are deliberately deferred during ordinary development and must run at a signed milestone or final validation point.
The `--java-reference` route kompiles the claim-free definition with `--hook-namespaces KRYPTO`, because the Java frontend otherwise drops the KRYPTO hooks, and passes every configuration variable except `$PGM` to `krun` as the same KORE value the K-Rust route builds.
The pinned Haskell backend cannot concretely execute 22 corpus cases: it implements no `KRYPTO.sha256raw`, `KRYPTO.ripemd160raw`, `KRYPTO.bn128valid`, or `KRYPTO.bn128ate` hook, its `KRYPTO.keccak256raw` result is rejected by `BYTES.length`, and its `KRYPTO.ecdsaRecover` fails an internal assertion on an invalid signature.
`HASKELL_BACKEND_GAPS` in `tests/kevm/verify.py` names those cases with their reasons; the Java route skips them and compares every other outcome against the corresponding native outcome, while the K-Rust route still executes all 240.
This result preserves the removed program, storage, and output adapters and models balance, code, and storage through the repeated upstream account shape.
The remaining opcode families and stateful EVM surfaces remain explicit future evidence, not implicit claims.
Full repeated-account collection snapshots for mutable nested calls remain uncovered together with the other calls, creation, account lifecycle beyond the selected emptiness boundary, transactions, schedules, cryptographic hooks outside the selected precompile surface, and symbolic surfaces.
