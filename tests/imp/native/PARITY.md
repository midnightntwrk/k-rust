# Complete-IMP native parity evidence

There are no known native/reference semantic blockers in the IMP complete-IMP
surface. This file retains the former blocker path so release tooling and
review links fail visibly if the evidence regresses.

## Strict result

Reproduced on 2026-09-15 with descriptor protocol 35,
Definition IR schema 27,
pinned `k-rust` revision `347f693e21ae220f1844005499da262f15ca3988`, and
pinned K 7.1.337:

```text
PASS native KORE: reference=1188 native=1188 reference_projector_pairs=0 native_projector_pairs=39
```

All non-claim sentences and all 20 claims match. The comparator removes five
enumerated renderer metadata attributes, alpha-normalizes variables per sentence while preserving kind and sort, canonicalizes constructor-tagged no-confusion pairs by symbol and argument sorts, canonicalizes constructor-tagged no-junk alternatives after independent alpha normalization, applies 20 individual reviewed label mappings, and mechanically proves each removed native projector declaration and equation is a complete, closed, unused pair.
K-rust's `docs/compatibility.md` Comparison contract specifies dependency-first declaration order for emitted sentences.
The no-confusion pair normalization applies `scripts/reference-normalisations.toml` N30 to the commutative conjunction ordered by K's `Production.ord`.
The no-junk normalization applies N6 to the commutative top-level disjunction of complete existentially wrapped constructor alternatives and retains multiplicity; N13 compares sentences as a multiset.
It performs no other parenthesis, associative/commutative, or claim-specific normalization.

The separate incomplete-proof residual comparator permits
associative/commutative normalization only for KORE conjunction and exact Map
concatenation. It then applies adjacent-existential and alpha normalization;
ordinary application argument order remains exact. This proof-result policy
does not weaken the native definition comparator described above.

The native comparator treats directly adjacent existential binders as commuting and orders them by first bound occurrence before alpha normalization.
The pinned frontend documents lexical existential ordering in `docs/compatibility.md`, “Comparison contract”.
The native adapter keeps injective existential names with a `?` prefix, independently of that lexical order.

The pinned frontend allocates each generated `_GenN` name once per sentence, whatever its sort, so the adapter emits `definition.kore` unchanged and needs no variable-sort repair.

## Reproduction contract

1. Run `krs emit-k` for `tests/imp/rust-definition`, wrap the 20 claims of its
   `spec.k` in a spec module which also imports the upstream verification
   syntax, and compile the claim-free `definition.k` with K 7.1.337's Haskell
   backend.
2. Run `kprove --dry-run` on that spec module to obtain `spec.kore`.
3. Run `krs build --backend haskell` on the same Rust definition.
4. Invoke the comparator as follows, supplying one mapping for every label
   listed below:

```bash
CARGO_TARGET_DIR=/tmp/krs-imp-native-target cargo run --locked \
  --manifest-path tests/imp/native/Cargo.toml \
  --bin krs-imp-native-comparator -- \
  REFERENCE-KOMPILED/definition.kore \
  NATIVE-ARTIFACTS/definition.kore \
  KRS-IMP \
  --reference-claims KPROVE-TEMP/spec.kore KRS-IMP-SPEC \
  --label KRS-IMP-SPEC.addition-1=addition-1 \
  --label KRS-IMP-SPEC.addition-2=addition-2 \
  --label KRS-IMP-SPEC.addition-var=addition-var \
  --label KRS-IMP-SPEC.bmc-loop-concrete=bmc-loop-concrete \
  --label KRS-IMP-SPEC.bmc-loop-symbolic=bmc-loop-symbolic \
  --label KRS-IMP-SPEC.branching=branching \
  --label KRS-IMP-SPEC.branching-deadcode=branching-deadcode \
  --label KRS-IMP-SPEC.branching-program=branching-program \
  --label KRS-IMP-SPEC.context-alias=context-alias \
  --label KRS-IMP-SPEC.explicit-priority=explicit-priority \
  --label KRS-IMP-SPEC.partial-equation=partial-equation \
  --label KRS-IMP-SPEC.pre-branch-proved=pre-branch-proved \
  --label KRS-IMP-SPEC.static-alias=static-alias \
  --label KRS-IMP-SPEC.sum-N=sum-N \
  --label KRS-IMP-SPEC.sum-loop=sum-loop \
  --label KRS-IMP-SPEC.sum-spec=sum-spec \
  --label KRS-IMP-SPEC.total-equation=total-equation \
  --label KRS-IMP-SPEC.two-sum-spec=two-sum-spec \
  --label KRS-IMP-SPEC.while-cut-rule=while-cut-rule \
  --label KRS-IMP-SPEC.while-cut-rule-delayed=while-cut-rule-delayed
```

## Reproduced artifact evidence

These hashes are evidence for the run above, not a substitute for rebuilding
and comparing the artifacts:

| artifact | SHA-256 |
|---|---|
| emitted `definition.k` | `75423957f57691e8503b167ee0fce7854c9dde4fc18154cdf1d03c948275cbbf` |
| emitted `symbols.json` | `5c0d68d757fad8717ba2ff6823045e414db916ec55944f45aea9df449ae0d5ae` |
| emitted `sources.json` | `679e2a4e1e7209b5c5b75596173252d74613b0c7c4fed6537fab1de149592478` |
| native `.krs-artifacts` | `4992e03ec15408f887a401455c9f719384c6d5bb69e661487f91abe576ceb1b5` |
| native `definition.kore` | `160538dcc69a30ef264f3236f9444e02b774e71eee1499977c53c1abcaa51ed1` |
| native `syntaxDefinition.kore` | `fff23aeb8958155d5cd6bff5ad3f8606a60cc99f5be9601250cf1b5c947b8ca8` |
| native `macros.kore` | `e1d5a374973b2fa9eb2502c3acdee5244ee7a89a965dd7acd69cda4b7d7814e0` |

The LLVM route omits all 20 claims, since that backend executes but does not
prove; `pins.json` pins its claim-free KORE separately.
