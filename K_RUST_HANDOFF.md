# KRS k-rust handoff

Status: KRS migrated to the latest fully qualified k-rust `main`; adapter and semantics requalification against that pin completed 2026-09-15 JST

## Current decision

KRS uses k-rust `0.4.0` from the dedicated worktree at `../inspirations/midnightntwrk/k-rust-krs-main`.
That worktree is detached at `efda6192785d4113eeea2fa090e4662d30dc8801`, the clean `origin/main` head used for this migration.
The old `krs-integration-main` branch remains at `c41caa8bede96e279e0b058577dce504e4144f65` as rollback evidence.
KRS must not depend directly on the shared `../inspirations/midnightntwrk/k-rust` main worktree because that branch may continue advancing independently.
The dedicated dependency worktree was advanced without modifying the shared main worktree or the retired patched checkout.

The latest shared k-rust `main` candidate is clean at `41ee041068db671f7ba8e417d1e31e98f2e3a8f8` as of 2026-09-22 JST. This candidate has only received a static-source screen so far and is not the reproducible KRS input: `Krs.lock` remains pinned to `efda6192785d4113eeea2fa090e4662d30dc8801` until the adapter and native gates are rerun. The screen confirms that semantic-cast projection and labelled-token constructor handling remain open, while typed simplification-budget diagnostics are present but the default budget remains 100.

The active dedicated worktree has no KRS-only source or manifest changes.
Current upstream supports external Z3 acquisition through `default-features = false, features = ["z3-inference"]`, so KRS retains the Nix-pinned Z3 4.12.5 policy without editing k-rust.
Current upstream also contains the structured-definition, deep-result, repeated-cell, plugin-hook, raw-digest, ECDSA, BN128, simplification-budget, parser, and real-semantics work that previously required the old KRS checkout or blocked its corpora.

The active pin accepts compiler-owned already-complete nested cells during concretization, closing the previously reproduced `Expected incomplete cell with 3 arguments, found 15` diagnostics at their source.
KRS removed its parser-shaped `#noDots/body/#noDots` compatibility encoding and now passes complete ordered cell children directly.
The focused adapter regression covers a two-child parent and both leaves; KEVM, KMIR, and KWasm qualify the real nested configurations.

The active pin exposes `outer::load_structured` for already-structured definitions.
KRS removed its empty bootstrap module, `DEFAULT-CONFIGURATION` removal, manual configuration expansion, and manual graph replacement, and now delegates that complete preparation boundary to the upstream API.
KWasm's `<instrs>` configuration qualifies the non-`<k>` path.
The clean k-rust worktree remains unmodified.

The active pin's upstream commit `758a3a9` removes the chained if-let guard and declares plus CI-enforces workspace `rust-version` 1.88, closing the E0658 MSRV discrepancy.
KRS retains Rust 1.88 qualification for authored semantics and non-native packages, qualifies native/frontend helpers on exact stable Rust 1.98.0, and the M4 gate now additionally checks the workspace and native helpers on exact Rust 1.88.0.
`Krs.lock` records `native_frontend_msrv_status = "msrv-compatible"`.

The KRS adapter supplies `hook_namespaces = None` to the strengthened `CompileOptions` API.
For the Rust backend this deliberately selects k-rust's audited backend-default namespace inventory; it is not a compatibility bypass or an unrestricted hook policy.

The strengthened compiler also defaults structural checks to definition mode, which correctly rejects claims.
Definition IR is a self-contained proof unit whose typed claims are colocated with its selected main semantics module, so KRS selects k-rust's explicit colocated proof policy when claims are present and retains definition mode for claim-free inputs.

Two narrow compatibility lowerings remain.
Typed `List.get` and `Map.get` stay as explicit `project:<Sort>` applications because removing the lowering widens function equations to `KItem` before upstream materializes the semantic projection.
Native token productions omit their otherwise-unused application label because the frontend emits a labelled token on a domain-value sort as a constructor which the matching backend rejects.
`K_RUST_UPSTREAM.toml` records both active reproductions and requested upstream actions.

The active pin emits frontend catalogs and generated axioms in declaration order.
K's reference frontend uses `Production.ord` for constructor no-confusion pairs and no-junk alternatives, so the M4 comparator adopts the matching published normalizations: constructor-tagged pairs are ordered by symbol and argument sorts, and complete existential no-junk alternatives are independently alpha-normalized before ordering.
Multiplicity, complete alternative structure, other conjunctions, other disjunctions, and ordinary application argument order remain exact.

The prior `../inspirations/midnightntwrk/k-rust-krs` checkout remains detached at `3cce7a47941c4dc0664e6e870d4e0529d74753c6` with its eight recovered local modifications.
It is rollback and comparison evidence only and is not an active KRS input.
Do not clean, rebase, or delete that checkout during the migration.

The focused migration qualification passes all 25 `krs-k-rust` adapter tests with the externally pinned solver.
The KEVM (240 executions), KMIR (184 executions), and KWasm (32 executions) native gates were rerun serially against the active pin and all pass; do not run those three memory-heavy gates concurrently or concurrently with M4.

## Historical baseline

KRS previously used k-rust `0.4.0` from the dedicated worktree at `../inspirations/midnightntwrk/k-rust-krs`.
That worktree is detached at upstream commit `3cce7a47941c4dc0664e6e870d4e0529d74753c6`.
KRS must not depend on the shared `../inspirations/midnightntwrk/k-rust` main worktree.

The dedicated worktree carries the external-solver policy plus six intentional functional changes.

Its root `Cargo.toml` selects the external solver policy:

```toml
z3 = "0.20.2"
```

Upstream currently enables `features = ["gh-release"]` at that location.
KRS disables that acquisition feature because its compatibility unit pins the externally supplied Z3 `4.12.5` library through Nix.
The `gh-release` path would otherwise select a different solver release at build time without a KRS-controlled artifact hash.

The dedicated worktree's `crates/k-rust/src/backend.rs` disables serde_json's recursion limit while converting successfully executed KORE results to JSON.
This is required for the KEVM 1,024-word stack boundary.
Without it, `Backend::execute` fails after execution with `could not encode KORE JSON: recursion limit exceeded`.
The precise reproducer and upstream action are recorded in `K_RUST_UPSTREAM.toml`.

The dedicated worktree's `crates/k-rust/src/kompile/passes/concretize_cells.rs`
classifies generated initializer productions returning a repeated cell's
collection sort as that repeated child. Without this fix, K-Rust's own CLI
rejects `initAccountCell(Init:Map)` under `<accounts>` before compiling any
KEVM storage rule. A focused regression lives in
`crates/k-rust/tests/kompile_passes.rs`; the standalone reproducer and upstream
action are recorded in `K_RUST_UPSTREAM.toml`.

The same concretization pass now distinguishes already-complete fixed-arity cell applications from parser-style three-argument incomplete cells.
Without this fix, the KEVM `STATICCALL` call-frame push and restoration each fail with `Expected incomplete cell with 3 arguments, found 15` for the complete nested `<callState>` term.
The local path accepts a complete leaf cell by its single body argument and accepts a complete parent only when its ordered arguments match every declared child sort.
The `preserves_already_complete_nested_cells` regression qualifies the complete-cell path while the existing concretization suite continues to qualify incomplete-cell syntax.
The exact defect and requested upstream action are recorded in `K_RUST_UPSTREAM.toml`.

The dedicated worktree's `crates/k-rust/src/kompile/module_to_kore.rs` includes `KRYPTO` in the frontend hook-namespace allowlist.
Without this fix, the frontend silently emits `KRYPTO.keccak256raw` as an ordinary symbol even though the backend implements the hook, leaving `SHA3` execution stuck at the unresolved application.
A focused `krypto_hooks_are_emitted_as_backend_hooks` regression qualifies the fix; the exact defect and requested upstream action are recorded in `K_RUST_UPSTREAM.toml`.

The dedicated worktree's `crates/k-rust-backend/src/builtin/krypto.rs` implements the pinned `KRYPTO.sha256raw`, `KRYPTO.ripemd160raw`, `KRYPTO.bn128valid`, `KRYPTO.bn128add`, `KRYPTO.bn128mul`, `KRYPTO.bn128g2valid`, and `KRYPTO.bn128ate` hooks and corrects invalid concrete `KRYPTO.ecdsaRecover` results.
The BN128 implementation uses `substrate-bn` 0.6.0, preserves Ethereum's point-at-infinity encoding, rejects invalid field, curve, and G2 subgroup inputs, and preserves the exact K constructor shapes expected by KEVM.
Focused regressions cover standard raw digest and ECDSA vectors plus the selected ECADD, ECMUL, and ECPAIRING validity and evaluation boundaries.
The complete upstream follow-up is recorded in `K_RUST_UPSTREAM.toml`.

This section records the retired patched baseline and must not be read as the active dependency decision.

## KRS integration

The active dependency paths are owned by:

- `crates/krs-k-rust/Cargo.toml`;
- `crates/krs-k-rust/src/bin/krs-native-runner.rs`;
- `tests/kevm/native.py` and `tests/kevm/verify.py`;
- `tests/kmir/native.py` and `tests/kmir/verify.py`;
- `tests/kwasm/native.py` and `tests/kwasm/verify.py`.

The M4 IMP comparator manifests and `tests/m4/pins.json` use the active clean `k-rust-krs-main` checkout.
The M4 gate pins Rust 1.88.0 for authored IMP packages, the workspace, and native helpers, and additionally qualifies native/frontend helpers on stable Rust 1.98.0.

The adapter preserves its historical public `Backend::Haskell` name as a compatibility spelling and maps it to k-rust 0.4's `CompilationBackend::Rust` symbolic backend.
KRS claims carry explicit modalities, so the adapter sets `default_claims_to_all_path = false` rather than changing unqualified claim semantics implicitly.
When claims exist, the adapter supplies `CheckMode::Proof { definition_module: main_module }`; otherwise it supplies `CheckMode::Definition`.

`Krs.lock` pins all native inputs required by the new frontend-plus-backend graph:

```toml
[k_rust]
version = "0.4.0"
commit = "efda6192785d4113eeea2fa090e4662d30dc8801"
tracked_crate_sha256 = "fa370981fb26255cce152cba31e5a5573bf8a24128522119af76dbce56b25359"
backend_version = "0.3.0"
tracked_backend_sha256 = "852e65b378c07027da83c9fc578662ac6fb6700cf9476f78303c38c2db206b78"
kore_version = "0.4.0"
tracked_kore_sha256 = "e8de6794ce13316e37fdae5dd4de91270418dc9fae5955e46d245e95ad79901b"
```

## Qualification evidence

The k-rust 0.4 migration passes all 25 `krs-k-rust` adapter tests.
The complete IMP M4.1-M4.8 gate passed on 2026-09-15 JST at descriptor protocol 35 and Definition IR schema 27 against the active main pin.
Native frontend parity remains 1,206/1,206 KORE sentences.
The behavior evidence remains `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`.
All 21 proof specifications and 20 unique native claims pass.
The compatibility evidence is `bd5e835ecaf2f3342ab8fedfa2a8d238a05ae41fcb0bf70b57a8aa266d7463d3`; it was re-pinned from `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6` because the LSP probe report embeds the rust-analyzer version, which is now 1.98.0, while all seven live probes continue to pass.

The dependency-path isolation was qualified by running the complete M4.1-M4.8 gate against the clean `k-rust-krs-main` worktree without touching the shared main worktree.
The final KEVM, KWasm, and KMIR gates also pass against the isolated setup.
These semantic preservation gates remain the authority for any later source change.

The KEVM development gate now compiles both the frontend and runner in release mode and executes all 240 behavior cases through persistent K-Rust backend workers.
The Definition IR compiles directly through the KRS adapter, K-Rust frontend, and K-Rust backend without invoking Java.
The complete corpus, including builtin-List `BLOCKHASH`, the selected memory/copy family, Shanghai current-account `SLOAD`/`SSTORE`, account queries through `EXTCODEHASH`, `SHA3`, `LOG0` through `LOG4`, absent/present-empty `STATICCALL`, successful/reverted/exceptional nonempty-code `STATICCALL`, and address-1 ECREC/address-2 SHA-256/address-3 RIPEMD-160/address-4 identity/address-5 MODEXP/address-6 ECADD/address-7 ECMUL/address-8 ECPAIRING-precompile `STATICCALL`, passes with behavior hash `7d7fd9dac9d3088682fa3ea27686c2a431219ded26f8a13400d2f4025f024673`.
The runner uses a bounded 4,096-iteration simplification budget because K-Rust's default budget of 100 causes repeated partial work on the 1,024-word recursive stack-size boundary.
The normal gate retains the full corpus and defers the pinned Java behavior and eight-proof authority run to the explicit `tests/kevm/verify.py --java-reference` mode.

The direct complete-cell representation produces native KEVM KORE SHA-256 `6c307ebbd12211d6ec726f3fb2d2b9d875d5e04e5e653078e1cf5dc19bdf2796`.
All 240 native executions retain behavior SHA-256 `7d7fd9dac9d3088682fa3ea27686c2a431219ded26f8a13400d2f4025f024673`.

KMIR and KWasm now follow the same policy.
Their default gates compile Definition IR directly through K-Rust, execute 184 and 32 concrete cases through persistent workers, and defer their reference proof to `--java-reference`.
The upstream structured loader prepares KWasm's `<instrs>` computation cell without adding a fallback `<k>` configuration.
The direct KWasm and KMIR KORE hashes are `cfd2a9b63d612f4a80c46470a7f5cbd3575c78ab5678c1474d4ea5c00c270e1e` and `1dfbd76951e943b8d40e89163f8bcda2202d2a393a91e0b676f986c8983f5014`.

K-Rust materializes the projection for a semantic cast around builtin `List:get` or `Map:lookup`, but it computes the enclosing rewrite's least upper bound first and widens a typed function equation to `KItem`.
KRS avoids carrying a dedicated-checkout patch by lowering its typed List and Map lookups directly to K-Rust's generated `project:<Sort>` function.
The exact defect, reproducer, impact, local workaround, and requested upstream regression are recorded in `K_RUST_UPSTREAM.toml`.

Descriptor protocol 23 and Definition IR schema 16 add typed Map lookup/key membership and builtin Set terms.
Focused KRS tests verify registry identity, IR/source rendering, native term adaptation, and the exact Map/Set labels exposed by the pinned K-Rust prelude.
This qualification invokes neither Java nor a filesystem-backed K frontend.

Descriptor protocol 24 and Definition IR schema 17 add repeated-cell multiplicity/type properties, nested ancestry-aware rule emission, and readable head-rule `requires` transport.
The canonical and native routes preserve the repeated account boundary.

Descriptor protocol 25 adds typed ordered-fallback rules through `#[k::rule(owise)]`, emitted as effective priority 200.
The KEVM account-query tranche uses that surface for absent-account fallback.
The subsequent LOG0-LOG4 tranche passes with native KORE hash `74f7aa3682f9763a9108c850307b0b063431927bc8c950da23b11104fed59f7a`.

Descriptor protocol 26 and Definition IR schema 18 add the closed typed function-hook boundary used by `SHA3`.
The subsequent `EXTCODEHASH` tranche adds the upstream nonce-backed account-emptiness distinction without changing the shared K-Rust checkout.
The current 201-case definition passes with native KORE hash `6d8eb6a9c9598b1e7886f40a41e838f1623ac6b32d67845e735945ee6fede191`.

Descriptor protocol 27 and Definition IR schema 19 add `krypto::sha256_raw` to the closed hook boundary for the KEVM address-2 precompile.
The dedicated K-Rust checkout dispatches the pinned `KRYPTO.sha256raw` hook through its existing raw SHA-256 implementation and pins the standard empty-input byte vector.
The exact backend omission and requested upstream action are recorded in `K_RUST_UPSTREAM.toml`.

Descriptor protocol 28 and Definition IR schema 20 add `krypto::ripemd160_raw` for the KEVM address-3 precompile.
The dedicated K-Rust checkout dispatches `KRYPTO.ripemd160raw` through its existing generic raw-digest implementation and pins the standard empty-input 20-byte vector.
KRS applies the precompile's required 12-byte left padding at the semantic boundary.

Descriptor protocol 29 and Definition IR schema 21 add `krypto::ecdsa_recover` for the KEVM address-1 precompile.
The dedicated K-Rust checkout returns empty Bytes for invalid concrete recovery inputs, matching the pinned hook contract, and retains focused invalid-input and deterministic valid key-1 regressions.
`K_RUST_UPSTREAM.toml` records the prior Bottom result as an upstream correctness defect.

Descriptor protocol 30 and Definition IR schema 22 add declared-sort `krypto::bn128_valid` and `krypto::bn128_add` hooks for the KEVM address-6 precompile.
The dedicated K-Rust checkout evaluates both hooks concretely and the KRS type boundary enforces `G1Point -> Bool` and `G1Point * G1Point -> G1Point`.
The 230-case native gate pins the standard addition vector, point-at-infinity behavior, invalid-point failure, and the 149/150 forwarded-gas boundary.

Descriptor protocol 31 and Definition IR schema 23 add declared-sort `krypto::bn128_mul` for the KEVM address-7 precompile.
The dedicated K-Rust checkout reduces the complete 256-bit scalar through `substrate-bn` and the KRS type boundary enforces `G1Point * Int -> G1Point`.
The 234-case native gate pins generator multiplication by two, zero-scalar infinity, invalid-point failure, and the 5,999/6,000 forwarded-gas boundary.

Descriptor protocol 32 and Definition IR schema 24 add declared-sort `krypto::bn128_g2_valid` and builtin-List `krypto::bn128_ate` for the KEVM address-8 precompile.
The dedicated K-Rust checkout uses `substrate-bn` for G2 field, curve, and subgroup validation and for pairing-product evaluation.
Focused backend regressions pin infinity, off-curve and out-of-field rejection, empty-product identity, a non-identity generator product, a cancelling product, injected List elements, mismatched lists, invalid points, and opaque lists.
The 240-case native gate pins empty input, a generator product, malformed input length, invalid G1 and G2 points, and the 78,999/79,000 forwarded-gas boundary.

The KEVM address-5 MODEXP precompile reuses K-Rust's existing `INT.powmod` and `INT.log2` hooks without a new K-Rust patch.
KRS totalizes modulus zero at the KEVM semantic boundary before invoking the partial raw hook, matching the pinned upstream `powmod` wrapper.
Focused K-Rust cases pin the 200-gas EIP-2565 floor, a 216-gas long-exponent vector, exact modulus-width output, modulus zero, zero output width, and forwarded-gas failure.

## Upstream follow-up policy

The upstream design opportunity is to make Z3 acquisition selectable without editing the workspace dependency declaration:

- ordinary CLI builds may default to `gh-release` for installation convenience;
- reproducible consumers such as KRS must be able to select an externally pinned solver;
- reproducible downloadable-solver builds should use an exact checksummed artifact or exact source-built Z3.

Historical k-rust missing features, defects, and performance findings are recorded in `K_RUST_UPSTREAM.toml` with their exact audited revision, reproducer, impact, workaround status, and requested upstream action.
Those entries must be requalified against the active pin before being described as current; the main migration does not carry the retired local patches forward.
Future findings must follow the same structured record before they are passed upstream.
