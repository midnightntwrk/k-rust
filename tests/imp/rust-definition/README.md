# IMP complete IMP Rust definition

This package is the single, self-contained Rust-authored definition used by
the IMP differential gate. Every authored source is ordinary Rust accepted by
`rustc`; the only normal dependency is the author-facing `krs` facade renamed
to `k`.

The package deliberately separates the closed operational language
(`imp.rs`), upstream verification simplifiers (`verification.rs`), the IMP static semantics
stress-only static adjunct (`static_adjunct.rs`), and the complete proof corpus
(`claims.rs`). The adjunct is not presented as part of upstream IMP.

Compiler, native-backend, oracle, and compatibility inspection belongs to the
external `tests/imp` runner rather than this author package.

The integration target `tests/expanded_reference.rs` separately compiles the
reviewed `../goldens/imp.expanded.rs` output. This proves the deterministic
`krs expand` reference surface remains valid Rust without making that generated
surface an alternate authored semantics route.

## Readable-surface method gates

The final readable design's four F3 gates are fail-closed production evidence:

- `tools/lsp_probe.py` opens this exact `imp.rs` in rust-analyzer and checks
  zero diagnostics, 24 definition/hover classes, completion, and five authored
  rename classes across sorts and memberships, macro/attribute entry points,
  constructors, local rule imports, configuration/init, binders, narrowing,
  splice/erase forms, and `map::update`. Checked string contents, helper tokens
  owned by the outer macro, and anonymous machine-rule cell records are listed
  explicitly instead of being mistaken for ordinary Rust name-resolution
  positions; the latter remain the accepted E7 LSP limitation.
- `parity::readable_imp_has_exact_reparsed_provenance_and_frozen_identities`
  checks every materialized IMP parser node against the exact content-addressed
  bytes of `src/imp.rs`, and freezes all 81 stable IMP descriptor identities in
  `../goldens/imp.identities.txt`.
- `krs-syntax`'s `provenance_roles` integration test freezes all 151 parser role
  spellings in one reviewed protocol snapshot.
- `identity_adversary` compiles equivalent readable specimens with different
  layout and declaration order, freezes their complete 19-ID catalog, and
  checks exact old/new identities for semantic renames. The IMP stable-name move
  adversary independently proves module-path and explicit-pin behavior; the
  deterministic artifact and expansion gates then pin the production IMP
  projection. None of these checks assigns meaning to source spans or inventory
  enumeration order.
