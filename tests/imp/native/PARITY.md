# Complete-IMP native parity evidence

There are no known native/reference semantic blockers in the complete-IMP
surface.
IMP.5 `native-kore` (`phase_native` in `tests/imp/verify.py`) proves it on
every gate run and requires exactly this comparator summary:

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

## Reproduction

`phase_native` is the reproduction; run the gate rather than a hand-written
command line.
It compares the reference `definition.kore`, which IMP.4 compiles from the
claim-free emitted `definition.k` with K's Haskell backend, against the native
one, which IMP.3 builds with `krs build --backend haskell`.
It wraps the 20 emitted claims of `spec.k` in the `KRS-IMP-SPEC` module,
obtains its `spec.kore` with `kprove --dry-run`, and passes that module to
`krs-imp-native-comparator` as `--reference-claims`.
It passes one `--label` mapping per entry of `native_comparison.label_map` in
`tests/imp/pins.json`, each from `KRS-IMP-SPEC.<label>` to `KRS-IMP.<label>`,
and rejects a map that is not exactly that 20-claim mapping.
`pins.json` pins the native artifact digests in `native_artifact_sha256`.

The LLVM route omits all 20 claims, since that backend executes but does not
prove; `pins.json` pins its claim-free KORE separately.
