# Lean proofs of k-rust optimizations

This Lake project holds Lean models of the Rust data and functions that an optimization changes, and proofs that the optimized function is equal to today's function over the model.
The method, its limits and the case studies are in `draft/lean-verification/README.md` (untracked); this file records what is tracked here and the rules every module follows.

## Layout

| path | content |
|---|---|
| `lean-toolchain` | the Lean release; elan reads it and downloads that toolchain |
| `lakefile.toml` | libraries `KRust` and `KRustBridge`, executables `krust-audit` and `krust-bridge`; core Lean only, no Mathlib yet |
| `KRust.lean` | root module; imports every module under `KRust/` |
| `KRust/SubsortEncoding.lean` | the Z3 ground-side subsort encoding (`new_equiv`) |
| `KRust/TermAttributes.lean` | the backend `Term` model; `ceilFree_sound` (OT-01), `hasMacro_iff`, `macro_shortcut_eq` and `rule_index_same` (OT-02) |
| `KRust/SynthAttr.lean` | the generic synthesized-attribute lemma `fold_rel`, with case 3 restated through it |
| `KRust/Examples.lean` | `#guard` checks that run the term model at build time |
| `KRust/MaximalModels.lean` | the maximal-model enumeration of the Z3 sort inference (`maximal_models_spec`, `runs_agree_up_to_pref`, `runs_agree`, `runs_agree_lowered`) |
| `Audit.lean` | `krust-audit`: the `sorry` and axiom audit that `scripts/lean-check.sh` runs |
| `KRustBridge/Json.lean` | the JSON form of the term model, shared with the Rust encoder of the bridge tests |
| `KRustBridge/Dispatch.lean` | the bridged models by name; each applies a `KRust` definition, never a copy |
| `Bridge.lean` | `krust-bridge`: answers JSON-line requests with `KRust.Bridge.answer` |

A new dependency (Mathlib, say) is a `[[require]]` entry in `lakefile.toml`, and `lean-toolchain` must then name the Lean release that dependency's version pins.

## Checking

```sh
scripts/lean-check.sh
```

It fails when a module under `KRust/` is not imported by `KRust.lean`, when `lake build` fails, when any declaration of a `KRust` module depends on `sorry`, when a `KRust` module declares an `axiom`, or when a `KRust` theorem depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
The audit enumerates the declarations from the built environment; there is no hand-kept list.
Exit status 0 is success, 1 a failed check, 2 a usage error or a missing `lake`.

```sh
scripts/lean-check.sh --bridge
```

It also runs the model conformance bridge: `cargo test -p k-rust-backend --lib tests::lean_bridge` with `K_RUST_LEAN_BRIDGE=1`.
Each test there sends generated terms, built by the public Rust constructors, through one `krust-bridge` process, compares every answer of a `KRust` definition with the Rust function it models, and shrinks a divergence.
Without `K_RUST_LEAN_BRIDGE=1` those tests are skipped with a message; with it, a missing `lake` is a failure.
`K_RUST_LEAN_BRIDGE_CASES` sets the number of cases (default 4096).
The `KRust` modules must not import `KRustBridge`; the check fails when one does.

## Conventions

- A model is written from the Rust source, never from the Java frontend or the Haskell backend.
- Every model definition and every theorem docstring names the Rust sites it mirrors, as `path:line-line` anchors at a stated commit.
  When `algo-graph drift` reports a change at one of those sites, the model must be re-checked against the Rust and the anchors updated.
- Every theorem docstring states which equality it proves: equality of the output values, equality up to a named normalization (the same set, the same models), or logical equivalence.
- Every assumption about Rust or Z3 behaviour that the proof does not open is a named hypothesis of the theorem, never an `axiom`.
  Each such hypothesis must have a Rust property test that checks it against the real code; the table below lists them.
- A model of a function that exists in Rust is registered in `KRustBridge/Dispatch.lean` and has a test in `crates/k-rust-backend/src/tests/lean_bridge/` that compares it with that function.
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

[[hypothesis]]
theorem = "KRust.MaximalModels.maximal_models_spec"
hypothesis = "hP : P.WF"
meaning = "less_than_eq(_, _, true) is reflexive and transitive on every value of the encoding datatype"
rust_test = "crates/k-rust/src/inner/parser/z3_inference.rs tests::subsort_order_is_a_preorder_on_model_values"

[[hypothesis]]
theorem = "KRust.MaximalModels.maximal_models_spec"
hypothesis = "hR : P.RoundTrip"
meaning = "sort_value(decode_sort(v)) is the same Z3 term as v for every value v that model.eval returns"
rust_test = "crates/k-rust/src/inner/parser/z3_inference.rs tests::model_values_round_trip"

[[hypothesis]]
theorem = "KRust.MaximalModels.maximal_models_spec"
hypothesis = "model conformance (h : Run P [] out)"
meaning = "Encoding::maximal_models, entered as infer_packed_sorts_z3 enters it, is one of the runs the relation Run allows; checked through its consequence: the recorded real projections are the brute-force maximal ones, without duplicates, under random_seed and disjunct-order perturbations"
rust_test = "crates/k-rust/src/inner/parser/z3_inference.rs tests::maximal_models_conform_to_brute_force_maximum"

[[hypothesis]]
theorem = "KRust.MaximalModels.runs_agree_up_to_pref"
hypothesis = "e : Equivalent P Q"
meaning = "two encodings define the same sat, le and pref; for OT-03, new_equiv at every less_than_eq call site"
rust_test = "none yet: OT-03's per-call-site equivalence test discharges it"

[[hypothesis]]
theorem = "KRust.MaximalModels.runs_agree"
hypothesis = "hu : UniquePref P"
meaning = "prefer_parameters has one admissible parameter vector per maximal real projection"
rust_test = "none yet: false in general (8 WASM sentences, S4b); ticket LT-05 decides how the Rust enforces it"

[[hypothesis]]
theorem = "KRust.MaximalModels.runs_agree_lowered"
hypothesis = "hl : LoweringConstOnPref P f"
meaning = "model application followed by lowering gives the same result for every admissible parameter vector of a recorded maximal real projection; implied by UniquePref"
rust_test = "none yet: owed to ticket LT-05, a check that compares the lowered terms of the admissible parameter vectors per recorded model"
```
