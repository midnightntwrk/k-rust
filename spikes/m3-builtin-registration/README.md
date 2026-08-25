# M3 stable builtin registration spike

## Conclusion

The proposed stable-Rust mechanism works and should be promoted into the M3
term/reference pipeline.

Rust tuple structs already provide exactly the two namespaces KRS needs:

```rust
pub struct Add(pub Int, pub Int);
pub use Add as add;
```

The alias is a constructor in value position and a type in type position. An
authored application is therefore ordinary Rust:

```rust
dialect::int::add(x, y)
```

rustc checks its arity and operand types. The attribute macro parses that same
call path and emits a host-only key function:

```rust
fn key() -> TypeId {
    TypeId::of::<dialect::int::add>()
}
```

Collection calls the key function but never the authored application carrier.
A link-retained catalog joins the process-local key to a closed
`BuiltinOp::IntAdd` and `BuiltinSignature`. Only that semantic identity and
signature cross the collector boundary; `TypeId` is neither serialized nor
ordered into stable output.

## What the spike proves

- The facade dependency is renamed to `dialect`; macro expansion discovers
  that name with `proc-macro-crate`.
- Direct paths, `use dialect::int as integer`, and
  `use integer::add as plus` all resolve to the same `Add` marker `TypeId`.
- `Add` and `Sub` have the identical `(Int, Int) -> Int` signature but distinct
  marker identities and resolve to distinct closed semantic enum variants.
- Preserving the ordinary Rust carrier body makes rustc—not a KRS imitation—
  reject an ordinary function as an operation, an unresolved alias, the wrong
  arity, and a wrong operand type with source-local diagnostics.
- The collector sorts stable application identities after resolving linker
  registrations. Two independent clean builds produce identical bytes.
- Atomic carrier-call and marker-drop counters both remain zero during
  collection. Type resolution does not execute or construct the authored
  builtin term.
- rust-analyzer 1.97.1 reports zero diagnostics and supplies definitions and
  meaningful hover for the renamed facade path, module alias, imported marker
  alias, and distinct subtraction operation. Renaming a bound operand edits
  both authored occurrences through the attribute macro.

The exact deterministic collector hash is:

```text
9df3cd5bc7c4b9a47a604e8f4ea47119458e0d041ce13290747742040a64d642
```

Run every gate with:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 spikes/m3-builtin-registration/tools/verify.py
```

## Boundaries and alternatives

A Rust `use Add as plus` alias works because it aliases the item in both the
type and value namespaces. A true type alias does not preserve a tuple
constructor: Rust rejects `type Plus = Add; Plus(x, y)` with E0423. KRS should
not bend Rust here. Authors can use idiomatic `use` aliases, including imported
aliases from another crate.

rust-analyzer currently answers rename on the alias token itself with
`Renaming aliases is currently unsupported`. This is a rust-analyzer behavior
for ordinary `use ... as ...` declarations, not a procedural-macro loss;
definition, hover, and operand rename work through the macro island.

If a future corpus demonstrates that true type aliases or non-constructor
builtins are essential, the smallest stable alternative is an explicit
`builtin!(OperationPath; operands...)` macro backed by a signature trait. It is
more KRS-specific and should not replace the ordinary tuple-marker spelling
without such evidence. An associated marker module such as
`int::add::Operation` is stable but makes the Rust surface more verbose while
providing no benefit for the demonstrated cases.

## Exact production API request

Promotion needs the following narrow production changes:

1. Add closed builtin operation/sort/signature identities to semantic IR and a
   pinned facade catalog for the M3-required `Int` and `Bool` operations.
2. Expose each operation as a CamelCase tuple marker and lowercase `pub use`
   alias from its builtin family module.
3. Add a host builtin registration containing only a `fn() -> TypeId` join key,
   closed semantic operation, and signature. Keep it behind the existing
   versioned collector protocol boundary.
4. Extend the shared term parser to classify call paths and operands. The proc
   macro emits a provenance-keyed `HostTypeReference`, authored spelling,
   parsed arity, and a key function using `TypeId::of::<resolved_path>()`.
5. Resolve every builtin key to exactly one catalog entry during collection,
   validate arity/signature, then lower only the closed semantic operation.
   Unknown or duplicate keys are hard diagnostics; there is no spelling-based
   fallback.
6. Reuse the production collector's explicit dependency-retention mechanism.
   Neither source imports nor incidental linker retention define theory
   composition.

The spike's `#[builtin_application]` attribute is a proof carrier, not a
requested user-facing production macro. Production rule/term expansion should
emit the same key/reference machinery around the already parsed term island.

