# IMP native/reference KORE comparator policy

The implementation lives in `crates/krs-gate/src/kore_compare.rs` and `crates/krs-gate/src/proof.rs`.
It parses both definitions with the pinned public `k-rust` KORE AST, selects exactly one explicitly named module, removes only the enumerated renderer and context metadata attributes, canonicalizes only constructor-tagged no-confusion pairs and no-junk alternatives, names generated lambda symbols by their content, alpha-normalizes variables within each sentence while retaining variable kind and sort, and compares sentence multisets including multiplicity.

K's frontend orders the two constructor applications in a no-confusion axiom by `Production.ord`; k-rust's `docs/compatibility.md` Comparison contract specifies dependency-first declaration order.
The comparator normalizes this exact top-level `not(and(P(X...), Q(Y...)))` family because the conjunction is commutative and its generated free variables are alpha-equivalent.
K-rust's `scripts/reference-normalisations.toml` records this constructor-pair comparison as N30, no-junk disjunction normalization as N6, and per-module sentence multiset comparison as N13.
The declaration-order contract also applies to constructor-tagged no-junk axioms whose top-level disjunction enumerates existentially wrapped constructor applications.
The comparator alpha-normalizes each complete alternative independently and sorts those alternatives while retaining multiplicity.
Other conjunctions, other disjunctions, and ordinary application argument order remain exact.

K's `ResolveFun` and k-rust's `resolve_fun` lift each `#fun`, `#let`, and `:=K` into a generated function symbol `#lambda<hint1>_<hint2>_<n>`, numbering the occurrences that share both hints in the order each frontend meets its sentences, so one lambda may carry a different suffix on each route.
The comparator therefore names every generated lambda symbol after its content: starting from one class, it repeatedly splits the lambdas by the sorted texts of the sentences that mention each one (with the lambda itself written as a marker and every other lambda by its current class) until no class splits, and then renames each lambda to its class.
When two lambdas remain in one class, the comparator names them in either order only if exchanging the two symbols maps the module's lambda-mentioning sentences onto themselves; otherwise it fails closed.
Unlike k-rust's own N23 suffix collapse, this keeps each lambda's declaration, its equations, and its uses associated, so a body exchanged between two uses remains a difference.
The summary line reports the number of renamed symbols on each route as `reference_lambda_symbols` and `native_lambda_symbols`.

A native definition whose non-terminals are named gains K's named field
projections (`project:<owner>:<field>`). The structured native adapter leaves
non-terminals unnamed, as the emitted K does, so complete IMP has none on either
route. The comparator excludes no such sentence: a projection declaration or
equation that only one route has is a visible multiset difference.
Claims must remain KORE claims, have implication bodies and unique string labels, and may not gain priority or `owise`.
The comparator ignores only the enumerated metadata and marker attributes; other semantic attributes remain exact.

Run it as:

```bash
cargo +stable build --release --locked --offline -p krs-gate --bins
target/release/krs-gate kore-compare \
  REFERENCE-DEFINITION.kore NATIVE-DEFINITION.kore KRS-IMP
```

Any exceptional label spelling must be supplied as an individual reviewed
`--label FROM=CANONICAL` mapping. There is deliberately no prefix or module
qualification rewrite.

K's reference frontend emits proof claims through a separate `kprove`
`spec.kore`. Pass that artifact as `--reference-claims SPEC.kore SPEC-MODULE`.
The comparator accepts only one import of the selected definition module plus
claims in that supplemental module; other sentences or imports fail closed.
