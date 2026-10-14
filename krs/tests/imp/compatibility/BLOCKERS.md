# Compatibility evidence

IMP.8 `compatibility-reproduction` runs the live stable-name and diagnostic
probes in this directory; each fails closed rather than accepting a weaker
anchor.
No compatibility blocker remains.

## Stable identity

All four move fixtures collect six descriptors with exact declaration
metadata:

- moving `internal_old::{PrivateValue,__krs_grammar_PrivateValue}` to
  `internal_new` changes only those internal stable identities;
- after package name/version and provenance are removed from the fixture
  projection, the baseline and private-move public descriptor projections are
  identical; and
- moving `{Expr,PublicValue,__krs_grammar_PublicValue}` from `api` to
  `moved_api` produces a detected breaking public identity diff.

The pinned, reordered public move retains the baseline emitted identities for
`Expr` and `publicValue` while preserving `moved_api` in descriptor provenance
and producing distinct source-map keys. The same probe verifies that package
name/version, fixture path, collection order, and backend selection do not
alter those public identities. There is no remaining stable-name production
blocker in this fixture surface.

## Diagnostics

- Rust expansion: rustc and rust-analyzer both select the exact authored
  `syntax` token; this boundary is green.
- KRS analysis: the two locally valid `Collision` declarations produce one schema-1 `analysis`/`krs::analysis::symbol-name-collision` envelope at the exact second authored `Collision` range, with no generated collector path.
- K frontend: mutating the unique `spec.k` range mapped from authored
  `bool::and` produces K `Location(65,14,...)`, and the schema-2 sidecar maps
  it to the exact hash-checked `src/claims.rs` bytes 12765..12774. The reusable
  probe is green, and the released translation API requires that same exact
  interval rather than line/column containment.
- Native frontend: IMP supplies no native adversary, since full IMP
  compilation succeeds on both backends.
  `native_rejection_reports_the_authored_rust_item_on_every_backend` in
  `crates/krs-cli/tests/cli_commands.rs` covers this boundary end to end: it
  builds an authored equation that k-rust rejects on both backends and
  requires one schema-1 `native` JSON envelope selecting the exact authored
  item.

Raw generated collector paths, a generated K range without its exact sidecar
mapping, or an unstructured error string are never accepted as authored
diagnostic evidence.

Complete-IMP native/reference KORE parity is exact for all 20 claims and all
non-claim sentences; `native/PARITY.md` describes the evidence.
