# Complete-M4 native parity evidence

There are no known native/reference semantic blockers in the M4 complete-IMP
surface. This file retains the former blocker path so release tooling and
review links fail visibly if the evidence regresses.

## Strict result

Observed on 2026-08-22 with descriptor protocol 15, Definition IR schema 9,
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

The last semantic repair was at the structured adapter boundary. The pinned
frontend lexically orders existentials before nesting them. K's reference
frontend places its generated-counter existential outside an authored
existential repeated in `ensures`, while leaving body-only existentials before
the counter. KRS now gives ensures-scoped internal existential names a distinct
ordered namespace while retaining one name at the binder and every use. This
closed `bmc-loop-concrete`, `bmc-loop-symbolic`, `branching`, and
`branching-deadcode` without comparator allowances.

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
| emitted `definition.k` | 13,989 | `c2a13a9936db01a30901ee8045e89818dbb0021618646ea5b303d368a4ceb6f2` |
| emitted `symbols.json` | 30,791 | `18d19037df25d5230f8f51d2caa3b9d4eef14118d6a2d2b5d213fe38b402c856` |
| emitted `sources.json` | 4,252,117 | `046221deb0a15d9a321c6859c80c010e5a6affadb08367ec59e942a47e0cbf14` |
| reference `definition.kore` | 547,626 | `91ee9c2c3aff9f2fb3426c01b0e4b3d43c236fa558eb0cf45f99a46a896fd6da` |
| reference `spec.kore` | 54,875 | `26f1a382424b6bcc6a32fc1ff3cdc63e432dd3eb5ab1f9596e1f707a86c451db` |
| native `definition.kore` | 521,226 | `59ea32230e71aa1b2bbe6fc5c56aa296a9063f49643897f143ec336a73559e39` |
| native `syntaxDefinition.kore` | 99,005 | `42bd0d27a21920c924bda16e86c0bfc1dce47ab631ac4e34fcc208cd84d58dab` |
| native `macros.kore` | 437 | `e1d5a374973b2fa9eb2502c3acdee5244ee7a89a965dd7acd69cda4b7d7814e0` |

The LLVM route still intentionally rejects existential claims. That is a
typed backend limitation: the CLI emits exact authored
`backend-capability`/`UnsupportedExistentialVariable` envelopes and creates no
partial artifacts. It is not a native/reference semantic parity failure.
