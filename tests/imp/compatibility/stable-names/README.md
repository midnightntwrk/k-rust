# Stable-name move adversary

These four ordinary Rust fixtures isolate the R10 move contract. `baseline`
and `private-move` differ only in the private constructor's module and package
version. `public-move` changes the canonical public item path while retaining
an ordinary Rust re-export. `public-move-pinned` spells the intended explicit
identity override.

The current descriptor protocol serializes each item's Rust module path but
also carries an exact `RustVisibility` and optional `ExplicitSymbol` for every
descriptor. The pinned fixture deliberately reorders its declarations and
moves the public Rust module while pinning `api::Expr` and
`api::PublicValue`.

`probe.py --krs PATH` checks the complete contract through production commands:

- the private move preserves the public descriptor projection while changing
  the private identity;
- the unpinned public move changes emitted symbol identities;
- the pinned public move retains baseline sort/production identities while
  its descriptor module path and source-map keys change; and
- package name/version, fixture path, collection order, and LLVM versus
  Haskell selection do not affect the public emitted identities.

The comparison intentionally retains descriptor provenance and does not treat
the authored Rust path as if it were the pinned backend identity.
