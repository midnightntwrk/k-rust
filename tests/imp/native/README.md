# IMP native/reference KORE comparator

This is the permanent, fail-closed version of the reviewed M3C native KORE investigation.
It parses both definitions with the pinned public `k-rust` KORE AST, selects exactly one explicitly named module, removes only five enumerated renderer metadata attributes, canonicalizes only constructor-tagged no-confusion pairs and no-junk alternatives, alpha-normalizes variables within each sentence while retaining variable kind and sort, and compares sentence multisets including multiplicity.

K's frontend orders the two constructor applications in a no-confusion axiom by `Production.ord`; k-rust's `docs/compatibility.md` Comparison contract specifies dependency-first declaration order.
The comparator normalizes this exact top-level `not(and(P(X...), Q(Y...)))` family because the conjunction is commutative and its generated free variables are alpha-equivalent.
K-rust's `scripts/reference-normalisations.toml` records this constructor-pair comparison as N30, no-junk disjunction normalization as N6, and per-module sentence multiset comparison as N13.
The declaration-order contract also applies to constructor-tagged no-junk axioms whose top-level disjunction enumerates existentially wrapped constructor applications.
The comparator alpha-normalizes each complete alternative independently and sorts those alternatives while retaining multiplicity.
Other conjunctions, other disjunctions, and ordinary application argument order remain exact.

The structured native adapter may add named Rust-field projections. Such a
sentence is excluded only after the comparator proves a complete pair:

- exactly one unhooked unary function declaration with an exact encoded
  `project:<owner>:<field>` identity;
- exactly one axiom whose implication concludes with that projector on the
  left of an equality; and
- exactly one use of the projector in the entire module, in that equation.

Consequently a lone declaration, lone equation, duplicate, retained use,
cross-projector use, or generic `project:`-prefix lookalike is an error or a
visible multiset difference. Claims must remain KORE claims, have implication
bodies and unique string labels, and may not gain priority, `owise`, or a fake
`all-path` attribute. No `cool-like` or other semantic attribute is ignored.

Run it as:

```bash
CARGO_TARGET_DIR=/tmp/krs-imp-native-target cargo run --locked \
  --manifest-path tests/imp/native/Cargo.toml -- \
  REFERENCE-DEFINITION.kore NATIVE-DEFINITION.kore KRS-IMP
```

Any exceptional label spelling must be supplied as an individual reviewed
`--label FROM=CANONICAL` mapping. There is deliberately no prefix or module
qualification rewrite.

K's reference frontend emits proof claims through a separate `kprove`
`spec.kore`. Pass that artifact as `--reference-claims SPEC.kore SPEC-MODULE`.
The comparator accepts only one import of the selected definition module plus
claims in that supplemental module; other sentences or imports fail closed.
