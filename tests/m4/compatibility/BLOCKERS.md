# Current compatibility evidence and remaining blockers

The Lane C fixtures prove everything the current public APIs expose and fail
closed at the missing seams.

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
- KRS analysis: the two locally valid `Collision` declarations produce one
  schema-1 `analysis`/`symbol-name-collision` envelope at the exact second
  authored `Collision` range, with no generated collector path.
- K frontend: mutating the unique generated range mapped from authored
  `bool::and` produces K `Location(171,12,...)`, and the schema-2 sidecar maps
  it to the exact hash-checked `src/claims.rs` bytes 11930..11939. The reusable
  probe is green, and the released translation API requires that same exact
  interval rather than line/column containment.
- Backend/capability: full M4 LLVM compilation returns six deduplicated schema-1
  `backend-capability`/`UnsupportedExistentialVariable` envelopes, each at an
  exact hash-checked authored claim-label range. It emits no collector paths or
  partial artifacts. The underlying frontend reports duplicate occurrences;
  CLI canonicalization intentionally collapses identical envelopes.

Raw generated collector paths, a generated K range without its exact sidecar
mapping, or an unstructured error string are never accepted as authored
diagnostic evidence.

Complete-IMP native/reference KORE parity is now exact for all 20 claims and
all non-claim sentences. Reproducible evidence remains at
`native/CURRENT-BLOCKERS.md`; diagnostics and stable identities are also
green in this compatibility lane.
