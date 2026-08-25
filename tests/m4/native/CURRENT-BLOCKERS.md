# Complete-M4 native parity evidence

There are no known native/reference semantic blockers in the M4 complete-IMP
surface. This file retains the former blocker path so release tooling and
review links fail visibly if the evidence regresses.

## Strict result

Reproduced twice unchanged on 2026-08-26 with descriptor protocol 15,
Definition IR schema 9,
pinned `k-rust` revision `58f33885b736148dae189623d1aac989ce9be475`, and
pinned K 7.1.337:

```text
PASS native KORE: reference=1206 native=1206 reference_projector_pairs=0 native_projector_pairs=40
```

All non-claim sentences and all 20 claims match. The comparator removes five
enumerated renderer metadata attributes, alpha-normalizes variables per
sentence while preserving kind and sort, applies 20 individual reviewed label
mappings, and mechanically proves each removed native projector declaration
and equation is a complete, closed, unused pair. It performs no binder-order,
parenthesis, associative/commutative, or claim-specific normalization.

The separate incomplete-proof residual comparator permits
associative/commutative normalization only for KORE conjunction and exact Map
concatenation. It then applies adjacent-existential and alpha normalization;
ordinary application argument order remains exact. This proof-result policy
does not weaken the native definition comparator described above.

The last semantic repair was at the structured adapter boundary. The pinned
frontend lexically orders existentials before nesting them. K's reference
frontend places its generated-counter existential outside an authored
existential repeated in `ensures`, while leaving body-only existentials before
the counter. KRS now gives ensures-scoped internal existential names a distinct
ordered namespace while retaining one name at the binder and every use. This
closed `bmc-loop-concrete`, `bmc-loop-symbolic`, `branching`, and
`branching-deadcode` without comparator allowances.

The pinned minimizer can also reuse one `_GenN` name for different sorts in a
single sentence, yielding invalid KORE. KRS repairs that parsed output by
alpha-renaming only the later conflicting `(kind, name, sort)` identity.
Collision-free output remains byte-for-byte unchanged, and the pinned
`k-rust` checkout is not modified.

## Reproduction contract

1. Run `krs emit-k` for `tests/m4/rust-definition`, split its 20 claims into a
   spec module which imports the claim-free semantic module, and compile the
   shell with K 7.1.337's Haskell backend.
2. Run `kprove --dry-run` on that spec module to obtain `spec.kore`.
3. Run `krs build --backend haskell` on the same Rust definition.
4. Invoke the comparator as follows, supplying one mapping for every label
   listed below:

```bash
CARGO_TARGET_DIR=/tmp/krs-m4-native-target cargo run --locked \
  --manifest-path tests/m4/native/Cargo.toml \
  --bin krs-m4-native-comparator -- \
  REFERENCE-KOMPILED/definition.kore \
  NATIVE-ARTIFACTS/definition.kore \
  KRS-M4-COMPLETE-IMP \
  --reference-claims KPROVE-TEMP/spec.kore KRS-M4-COMPLETE-IMP-SPEC \
  --label KRS-M4-COMPLETE-IMP-SPEC.addition-1=addition-1 \
  --label KRS-M4-COMPLETE-IMP-SPEC.addition-2=addition-2 \
  --label KRS-M4-COMPLETE-IMP-SPEC.addition-var=addition-var \
  --label KRS-M4-COMPLETE-IMP-SPEC.bmc-loop-concrete=bmc-loop-concrete \
  --label KRS-M4-COMPLETE-IMP-SPEC.bmc-loop-symbolic=bmc-loop-symbolic \
  --label KRS-M4-COMPLETE-IMP-SPEC.branching=branching \
  --label KRS-M4-COMPLETE-IMP-SPEC.branching-deadcode=branching-deadcode \
  --label KRS-M4-COMPLETE-IMP-SPEC.branching-program=branching-program \
  --label KRS-M4-COMPLETE-IMP-SPEC.context-alias=context-alias \
  --label KRS-M4-COMPLETE-IMP-SPEC.explicit-priority=explicit-priority \
  --label KRS-M4-COMPLETE-IMP-SPEC.partial-equation=partial-equation \
  --label KRS-M4-COMPLETE-IMP-SPEC.pre-branch-proved=pre-branch-proved \
  --label KRS-M4-COMPLETE-IMP-SPEC.static-alias=static-alias \
  --label KRS-M4-COMPLETE-IMP-SPEC.sum-N=sum-N \
  --label KRS-M4-COMPLETE-IMP-SPEC.sum-loop=sum-loop \
  --label KRS-M4-COMPLETE-IMP-SPEC.sum-spec=sum-spec \
  --label KRS-M4-COMPLETE-IMP-SPEC.total-equation=total-equation \
  --label KRS-M4-COMPLETE-IMP-SPEC.two-sum-spec=two-sum-spec \
  --label KRS-M4-COMPLETE-IMP-SPEC.while-cut-rule=while-cut-rule \
  --label KRS-M4-COMPLETE-IMP-SPEC.while-cut-rule-delayed=while-cut-rule-delayed
```

## Reproduced artifact evidence

These hashes are evidence for the run above, not a substitute for rebuilding
and comparing the artifacts:

| artifact | bytes | SHA-256 |
|---|---:|---|
| emitted `definition.k` | 12,496 | `75423957f57691e8503b167ee0fce7854c9dde4fc18154cdf1d03c948275cbbf` |
| emitted `symbols.json` | 31,012 | `5c0d68d757fad8717ba2ff6823045e414db916ec55944f45aea9df449ae0d5ae` |
| emitted `sources.json` | 4,594,792 | `2caba193fdadc7c5b17c09a02d826ecbe16df470ada74951784995d48f3b45f8` |
| native `.krs-artifacts` | 49 | `4992e03ec15408f887a401455c9f719384c6d5bb69e661487f91abe576ceb1b5` |
| native `definition.kore` | 521,007 | `1483dc5eacf7fed1f5fd56d0c33530a6552d06b19216159758e5b0d57211d518` |
| native `syntaxDefinition.kore` | 96,324 | `9963fcfacc153cf8e12e900ace1b4416be6672d5c4ac620a3e73af2d69c7c051` |
| native `macros.kore` | 437 | `e1d5a374973b2fa9eb2502c3acdee5244ee7a89a965dd7acd69cda4b7d7814e0` |

The LLVM route still intentionally rejects existential claims. That is a
typed backend limitation: the CLI emits exact authored
`backend-capability`/`UnsupportedExistentialVariable` envelopes and creates no
partial artifacts. It is not a native/reference semantic parity failure.
