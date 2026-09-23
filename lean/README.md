# Lean proofs of k-rust optimizations

This Lake project holds Lean models of the Rust data and functions that an optimization changes, and proofs that the optimized function is equal to today's function over the model.
The method, its limits and the case studies are in `draft/lean-verification/README.md` (untracked); this file records what is tracked here and the rules every module follows.

## Layout

| path | content |
|---|---|
| `lean-toolchain` | the Lean release; elan reads it and downloads that toolchain |
| `lakefile.toml` | library `KRust` and executable `krust-audit`; core Lean only, no Mathlib yet |
| `KRust.lean` | root module; imports every module under `KRust/` |
| `KRust/SubsortEncoding.lean` | the Z3 ground-side subsort encoding (`new_equiv`) |
| `KRust/TermAttributes.lean` | the backend `Term` model; `ceilFree_sound` (OT-01), `hasMacro_iff`, `macro_shortcut_eq` and `rule_index_same` (OT-02) |
| `KRust/SynthAttr.lean` | the generic synthesized-attribute lemma `fold_rel`, with case 3 restated through it |
| `KRust/Examples.lean` | `#guard` checks that run the term model at build time |
| `Audit.lean` | `krust-audit`: the `sorry` and axiom audit that `scripts/lean-check.sh` runs |

A new dependency (Mathlib, say) is a `[[require]]` entry in `lakefile.toml`, and `lean-toolchain` must then name the Lean release that dependency's version pins.

## Checking

```sh
scripts/lean-check.sh
```

It fails when a module under `KRust/` is not imported by `KRust.lean`, when `lake build` fails, when any declaration of a `KRust` module depends on `sorry`, when a `KRust` module declares an `axiom`, or when a `KRust` theorem depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
The audit enumerates the declarations from the built environment; there is no hand-kept list.
Exit status 0 is success, 1 a failed check, 2 a missing `lake`.

## Conventions

- A model is written from the Rust source, never from the Java frontend or the Haskell backend.
- Every model definition and every theorem docstring names the Rust sites it mirrors, as `path:line-line` anchors at a stated commit.
  When `algo-graph drift` reports a change at one of those sites, the model must be re-checked against the Rust and the anchors updated.
- Every theorem docstring states which equality it proves: equality of the output values, equality up to a named normalization (the same set, the same models), or logical equivalence.
- Every assumption about Rust or Z3 behaviour that the proof does not open is a named hypothesis of the theorem, never an `axiom`.
  Each such hypothesis must have a Rust property test that checks it against the real code; the table below lists them.
- A theorem about a function not yet implemented in Rust names the test-only Rust function that mirrors the model and the property test that compares it with today's function.

## Hypotheses and their Rust tests

```toml
[[hypothesis]]
theorem = "KRust.SubsortEncoding.new_equiv"
hypothesis = "hI : Injective I"
meaning = "distinct cached ground sort values (constructor terms of KRustInferenceSort) denote distinct elements in every Z3 model"
rust_test = "crates/k-rust/src/inner/parser/z3_inference.rs tests::ground_side_encoding_is_equivalent"

[[hypothesis]]
theorem = "KRust.TermAttributes.ceilFree_sound"
hypothesis = "hle : TotalOrder le (field trans)"
meaning = "Ord for Term (term.rs:1133-1137) is transitive"
rust_test = "crates/k-rust-backend/tests/backend/term_order.rs ord_for_term_is_transitive"

[[hypothesis]]
theorem = "KRust.TermAttributes.ceilFree_sound"
hypothesis = "hle : TotalOrder le (field antisym)"
meaning = "a.cmp(b) == Equal exactly when a == b (term.rs:1118-1137), and a == b exactly when the kinds are structurally equal"
rust_test = "crates/k-rust-backend/tests/backend/term_order.rs ord_for_term_equal_is_eq"

[[hypothesis]]
theorem = "KRust.TermAttributes.ceilFree_sound"
hypothesis = "WF le t"
meaning = "every term the public constructors build has map entries sorted by (key, value) (Term::map, term.rs:471-509) and set elements sorted with adjacent elements distinct (Term::set, term.rs:562-595), at every depth"
rust_test = "crates/k-rust-backend/tests/backend/term_order.rs constructed_collections_are_sorted"

[[hypothesis]]
theorem = "KRust.TermAttributes.ceilFree_sound"
hypothesis = "O : Oracles (field dedup_nil)"
meaning = "deduplicate (definedness.rs:307-310) of an empty vector is empty"
rust_test = "crates/k-rust-backend/src/definedness.rs tests::deduplicate_keeps_an_empty_vector_empty"
```
