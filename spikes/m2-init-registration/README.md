# M2 associated initializer registration spike

## Result

The exact bare method-only expansion is **not production-viable** on stable
Rust. An attribute on an `ImplItemFn` receives no enclosing `impl` type, while
`inventory` must place its value in a nested `static`. `Self` is legal in an
associated helper function, but using `Self::__factory` in that nested static
fails with E0401: nested items cannot capture the outer impl's `Self`.

The authored notation remains viable with coordinated expansion. The
recommended production shape is:

```rust
#[k::configuration]
pub struct Machine { /* cells */ }

impl Machine {
    #[k::init]
    pub fn init(/* config variables */) -> Self { /* declarative body */ }
}
```

`#[k::init]` preserves the method and emits only an associated initializer
payload factory. `#[k::configuration]`, which knows `Machine`, emits the one
module-scope link registration and calls that associated factory. Thus the
initializer attribute stays on the authored associated method; it is not moved
to the impl or struct.

An independently viable but less attractive alternative is explicit
repetition:

```rust
impl Machine {
    #[k::init(config = Machine)]
    pub fn init() -> Self { /* ... */ }
}
```

With the concrete path, a method macro can place `inventory::submit!` inside a
named associated const and register `Machine::__krs_descriptor`. This fixture
proves that form with `Gamma`. It adds a redundant path and an extra mismatch
case, so the paired configuration-owned registration is preferable.

This is a language/linker risk spike. Its tiny `Descriptor` is deliberately
not a proposal for protocol v5.

## Exact mechanisms tested

Raw `inventory::submit!` cannot be emitted directly as an associated item in
inventory 0.3.24 because it expands to anonymous `const _: ()`, and anonymous
associated consts are rejected. A named wrapper makes the retained ctor/static
block legal:

```rust
const __KRS_REGISTRATION: () = {
    facade::__submit!(Machine::__krs_descriptor);
};
```

That wrapper is sufficient only when `Machine` is concrete. Replacing it with
`Self` reaches inventory's inner static and fails:

```text
error[E0401]: can't use `Self` from outer item
`Self` used in this inner static item
```

The recommended paired expansion avoids both associated-position issues:

```rust
// #[k::init] in the inherent impl
pub fn init(/* unchanged authored signature/body */) -> Self { /* unchanged */ }
fn __krs_initializer_payload() -> FutureReviewedHostPayload { /* parsed data */ }

// #[k::configuration] at module scope
fn __krs_configuration_type_key_machine() -> TypeId {
    TypeId::of::<Machine>()
}
fn __krs_configuration_descriptor_machine() -> FutureReviewedHostDescriptor {
    // Uses Machine::__krs_initializer_payload without executing Machine::init.
}
facade::__register_host_descriptor!(__krs_configuration_descriptor_machine);
```

For production, generated duplicates of `Machine` should have call-site spans;
the authored declaration remains its single source-spanned occurrence. The
associated helper name is scoped by the concrete type. Module helper names
must include the configuration item name plus the production nonce convention.
The stable collision key must be based on the owning configuration's real
package/module/item identity, not the shared method name `init`, a source line,
or a serialized `TypeId`. The protocol lane must choose the reviewed descriptor
variants and fields before implementation.

## Evidence

The positive semantics crate renames the facade dependency to `k`. The clean
collector separately renames the facade to `host` and semantics dependency to
`model`, and calls `model::retain_for_collector()` as an explicit linker edge.
No incidental import activates collection.

Two paired configurations, `Alpha` and `Beta`, have the same associated method
name in one module. The explicit-path `Gamma` exercises associated-position
registration. Three unique process-local `TypeId`s are checked in memory, then
discarded. Sorted output contains only real Cargo/module/configuration spellings
and Rust diagnostic type names; no raw `TypeId`, address, fabricated source
range, or fake source identity is serialized.

Two independent clean target directories produced identical output:

```text
m2-init-semantics::m2_init_semantics::explicit::Gamma::init|type=m2_init_semantics::explicit::Gamma|method=init
m2-init-semantics::m2_init_semantics::paired::Alpha::init|type=m2_init_semantics::paired::Alpha|method=init
m2-init-semantics::m2_init_semantics::paired::Beta::init|type=m2_init_semantics::paired::Beta|method=init
runtime_init_calls=0
```

SHA-256: `126d072611163a78edbb471c269110b2e80181aa123eb5ba67b9d9eefab759cc`.
Each authored initializer increments a counter if called, so the final zero
proves static registration and payload construction never execute `init`.

Stable rustc/cargo 1.97.1 pass format, locked offline workspace check, tests,
and warnings-denied Clippy. rust-analyzer 1.97.1 reports zero diagnostics, one
definition and meaningful hover for both an authored method and the explicit
configuration path, two correct `Alpha::init` rename edits without touching
`Beta::init`, and four authored `Gamma` rename lines.

Negative cases prove:

- raw associated inventory submission: anonymous associated const rejection;
- bare `Self` registration: E0401 at the nested static boundary;
- trait impl: the macro cannot see the enclosing trait impl, but rustc rejects
  its hidden associated helper with E0407;
- free function: the same method-shaped tokens cannot reveal lexical context,
  but the required `Self` result is rejected with E0411;
- duplicate initializer: rustc reports duplicate authored and helper methods
  with E0592;
- struct placement: the macro parser reports `expected fn`; and
- configuration without initializer: its concrete factory reference fails
  with E0599.

The inverse mismatch—a bare `#[k::init]` without a configuration declaration—
cannot be diagnosed from the method tokens or by rustc if the helper is allowed
to remain unused. Whole-definition KRS collection must report that semantic
orphan. Likewise, an attribute macro cannot distinguish inherent and trait impl
parents locally; deliberately emitting an associated helper lets rustc reject
the trait case.

## Reproduction

From the repository root:

```text
python3 spikes/m2-init-registration/tools/verify.py
```

The verifier runs formatting, locked/offline check and tests, warnings-denied
Clippy, all seven expected failures, two independent clean collector builds,
byte-for-byte output comparison, and the rust-analyzer LSP probe.

## Production recommendation

Keep the exact designed bare `#[k::init]` method notation, but do not require
that expansion to submit inventory itself. Make configuration registration the
owner of the link-retained descriptor factory and make the init expansion
provide a deterministic associated payload factory. This respects renamed
facades, gives rustc the concrete configuration type for `HostTypeKey`, keeps
the authored method analyzable, and naturally disambiguates same-named init
methods by owning configuration identity.

Retain `#[k::init(config = Machine)]` only as a possible explicit escape hatch
if configuration and initializer registration cannot be paired in the future
protocol. Do not ship a bare method-only inventory expansion based on `Self`,
and do not derive identity from `type_name`, `stringify!(Self)`, a span hash, or
linker order.
