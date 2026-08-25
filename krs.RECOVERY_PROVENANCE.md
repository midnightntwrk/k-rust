# Krs recovered working tree

Updated: 2026-08-24 JST

## Practical status

`krs/` is the best recovered late working tree and is ready to copy into a
development environment as recovery material. It is not a complete exact Git
checkout. The directory combines exact recovered Git blobs, exact reconstructed
Git blobs, final transcript replays, and clearly retained historical-prefix
files where no complete final baseline survived.

The extraction archive contains 580 project files. Its authoritative identity
ledger is `../evidence/krs-extract-ready-identities.tsv` (SHA-256
`dd90603f687ec891b1cb4dc4eb18ac0ff00f46229625093d213c625ef902f1f8`).
A fresh independent expansion matched all 580 SHA-256 and Git-blob identities.
The older `krs-working-tree-identities.tsv` is retained as a historical
569-file ledger from before the final promotions and must not be used to
validate the extraction archive.

The user-authored material under `krs/draft/` is included. Do not replace that
directory with a clean-commit reconstruction: some of it is later work recovered
from editor and agent-session records.

## Strong checkpoints

- Signed clean commit: `9d507b03c26105c82ad38f92a0d7fb776e2e0f6b`.
- Earlier signed commit: `fbccdc7cfea785b8a04b3b0a532eaa3bc2837683`.
- The three syntax files absent from loose-object recovery were reconstructed
  byte-exactly for `9d507b0` and verified by Git blob identity:
  - `crates/krs-syntax/src/item.rs`: `6088ded12af68281e2421a4018a18d0dfd4c05d8`
  - `crates/krs-syntax/src/provenance.rs`: `1e0517dbcb95e6f746ebec4283d2b81506437b94`
  - `crates/krs-syntax/src/term.rs`: `e7aa2cee962b917b6a6e244e4f67a30c2f49fe59`

The completed retain-all unallocated-block scan did not close the clean commit.
Across all recovered object stores, the recursive `9d507b0` audit sees 83 blobs
and 24 trees, while 69 visible blobs and 17 visible subtrees remain missing.
The missing subtrees can contain additional files, so those counts are lower
bounds on the missing clean-commit content.

Two large compile-clean transcript reconstructions are present at
`crates/krs-ir/src/definition.rs` and `crates/krs-ir/src/semantic.rs`. They are
substantially corroborated by direct late reads, but they do not match the
expected final clean-commit blob IDs and are not claimed to be byte-exact final
files. Their exact boundary and expected identities are recorded under
`../evidence/krs-semantic-definition-candidate-v2/`.

## Validation boundary

A disposable copy was checked offline after the exact syntax reconstruction:

- `cargo check -p krs-ir -p krs-syntax --offline`: passed.
- `cargo check -p krs-macros -p krs-compiler -p krs --offline`: failed.

The full-workspace failure is consistent with cross-checkpoint reconstruction:
recovered macro/compiler entry points refer to APIs absent from their older or
incomplete companion files. It does not prove that the original final worktree
failed to compile, and no source was changed merely to make the recovered tree
compile.

## Evidence

- Extraction identity manifest: `../evidence/krs-extract-ready-identities.tsv`
- Historical pre-final-promotion manifest:
  `../evidence/krs-working-tree-identities.tsv`
- Clean-commit audit: `../evidence/9d507b0-tree-audit/`
- Exact syntax reconstruction:
  `../evidence/krs-latest-state-exact-reconstructions/`
- Transcript replay and confidence decisions:
  `../evidence/krs-transcript-replay/`
- Displaced variants retained for comparison:
  `../evidence/krs-replaced-divergent/`
