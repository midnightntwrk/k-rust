# M3C object-Bool `requires` adjunct

This is a small production-independent oracle for guarded transition rules.
It is deliberately separate from `tests/m3c`: modern upstream IMP contains an
include directive spelled `requires`, but none of its semantic rules has a
rule-side condition. This adjunct therefore makes no false upstream claim and
does not modify the frozen core oracle.

The pinned K definition contains three ordinary term rules and one whole-state
configuration rule. Every rule has a nontrivial `Bool` condition and an exact
label. The five programs establish both sides of the applicability boundary:

- `pick(5, 3)` and `pick(2, 3)` select complementary guarded term rules;
- `admit(-1)` remains stuck because its only guard is false;
- `store-if-within(3, 5)` performs the guarded simultaneous cell rewrite;
- `store-if-within(7, 5)` remains unchanged because the configuration-rule
  guard is false.

Three induced definitions pin frontend rejection of a non-`Bool` condition,
an unbound condition variable, and a variable first introduced in the result.
The verifier also inspects the compiled KAST and proves that each authored
condition references only variables present in its left pattern.

## Frozen Rust surface

`surface/accepted.rs` records the intended typed spelling for both ordinary
and configuration rules:

```rust
#[krs::rule]
#[krs::requires(int::gt(value, 0))]
fn positive(/* pre-pattern binding `value` */) { /* post term */ }
```

The attribute payload is a parsed object-language term whose required sort is
exactly `Term<Bool>`. It is never a host `bool`, an `MlPattern`, or a stored K
source string. Its applications, references, literals, record fields, and
complete payload retain parser-owned provenance. All referenced variables must
already be ordinary term bindings in the pre-pattern. Structural K-sequence,
map, and configuration frames cannot be used as object-Bool operands.

The files prefixed `surface/rejected-` freeze four mandatory diagnostics:

1. a host Boolean such as `true`;
2. an object term with a non-`Bool` result sort;
3. a name absent from the pre-pattern binding catalog; and
4. a name first introduced in the result, even if the condition mentions it.

These Rust snippets began as contract fixtures while protocol-v8 label work
was serialized ahead of condition implementation. Protocol v9 now turns them
into external compile-pass/compile-fail fixtures rather than weakening them to
strings or unchecked tokens.

`rust-definition/` is the production Cargo acceptance package. It authors one
ordinary term guard and one whole-configuration guard through the public `k`
facade. Its verifier checks deterministic protocol-v11 expansion, canonical K
and schema-v2 sidecars, and native structured `build`, then reruns this frozen
independent oracle.

## Running

K `7.1.337` at commit
`4a46d1231473b599c699160132fd6e76a5c46406` is required:

```sh
TMPDIR=/dev/shm PYTHONDONTWRITEBYTECODE=1 python3 tests/m3c-requires/verify.py

TMPDIR=/dev/shm PYTHONDONTWRITEBYTECODE=1 \
  Z3_SYS_Z3_VERSION=4.12.2 \
  python3 tests/m3c-requires/verify_rust_definition.py
```

`TMPDIR=/dev/shm` is recommended on disk-constrained hosts because LLVM
definition compilation creates substantial temporary scanner artifacts.

Pinned verifier SHA-256:
`4ac9d0de9a703559c74b1bc1bf78f619a8e094877da155a9ebb496f24675e424`.
