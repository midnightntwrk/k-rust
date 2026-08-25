# M3D claims implementation reconnaissance

## Status and scope

This is a read-only implementation reconnaissance for the frozen M3D claim
contract. It records the dependency order, existing extension seams, semantic
invariants, native frontend behavior, and acceptance gates. It does not change
the Rust implementation, generated schemas, or frozen M3D oracle.

The authoring contract is frozen by:

- `draft/investigations/m3d-claim-surface/CONTRACT.md`;
- `draft/investigations/m3d-claim-surface/surface/src/lib.rs`;
- IMP commit `683a773418add3bcae8ded47c2b24e94494e1988`;
- K commit `4a46d1231473b599c699160132fd6e76a5c46406`;
- the proof and normalized-claim hashes in `tests/m3d/pins.json`.

The three complete frozen claims are `branching`, `sum-loop`, and `sum-spec`.
They jointly require explicit reachability modality, exact labels, universal
and existential binders, one-use anonymous variables, object-language
`requires` and `ensures`, concrete `Id` tokens, Boolean disjunction, K/Map and
whole-configuration framing, and circularity.

## Executive findings

The implementation already reserves `ItemKind::Claim` and
`SentenceKind::Claim`. `DescriptorConfigurationRule` and its semantic and
Definition counterparts can nominally carry that kind. The pipeline is not
usable for authored claims because it lacks typed claim metadata, scoped
existential transport, `ensures`, the three claim-specific term islands, claim
emission, and native adaptation. The source emitter and native adapter
currently reject claims deliberately.

Protocol v11 and Semantic/Definition schema v6 are already reserved for the
remaining M3D context, simplification, and claim additions. Claim work should
land inside those versions after the active context/simplification edits and
their exhaustive matches are green. The source-map sidecar has its own schema
version and must be bumped when new serialized node kinds are added.

Two contract decisions must not be guessed during implementation:

1. `all_paths` represents K's default bare `claim`. To match the pinned IMP
   claims, it must not manufacture an explicit `[all-path]` attribute.
   `one_path` maps to `[one-path]` and native `one-path = ""`.
2. Native K can represent `k::id!("$n")` directly as an `Id` token, but
   emitted textual K cannot spell bare `$n` unless the project-specific
   `r"\$[a-zA-Z0-9\_]+"` production is visible. The implementation must
   choose between adding a target-neutral way to emit that production and
   using `#token("$n","Id")` in generated source. The latter preserves
   parsed meaning but not the currently documented exact text.

The disjoint claim contract requires `label = "..."`. The older
`tests/m3d/rust-definition/surface/src/lib.rs` claims still omit labels and
describe them as deferred. That fixture must be reconciled before it becomes
the acceptance input; label inference from Rust function names would violate
the frozen contract.

## Existing implementation seams

The claim slice should extend these existing paths rather than create an
unrelated rule transport:

- Shared syntax:
  - `crates/krs-syntax/src/attribute.rs`
  - `crates/krs-syntax/src/state_rule.rs`
  - `crates/krs-syntax/src/rule.rs`
  - `crates/krs-syntax/src/term.rs`
  - `crates/krs-syntax/src/state_macro.rs`
  - `crates/krs-syntax/src/provenance.rs`
- Proc macros and facade:
  - `crates/krs-macros/src/lib.rs`
  - `crates/krs-macros/src/expand.rs`
  - `crates/krs/src/lib.rs`
- Stable and host protocol:
  - `crates/krs-ir/src/protocol_v7_rule.rs`
  - `crates/krs-ir/src/protocol_v6.rs`
  - `crates/krs-ir/src/host.rs`
  - `crates/krs-ir/src/bundle.rs`
  - `crates/krs-ir/src/lib.rs`
- Collection and source reparsing:
  - `resolve_configuration_rule`, `resolve_rule_state`, and `resolve_term` in
    `crates/krs-compiler/src/collect.rs`;
  - the `Item::Fn` source-reparser branch in that file;
  - its exact-kind, `primary_key`, `descriptor_label`, and expected-reference
    maps.
- Semantic lowering and validation:
  - `lower_configuration_rule_descriptor` in
    `crates/krs-compiler/src/semantic.rs`;
  - `SemanticRule`, `SemanticRuleBody`, and `validate_rule` in
    `crates/krs-ir/src/semantic.rs`.
- Definition lowering and validation:
  - the rule loop in `crates/krs-compiler/src/lowering.rs`;
  - `RuleSentence`, `DefinitionRuleBody`, and `validate_rule` in
    `crates/krs-ir/src/definition.rs`.
- Source and sidecars:
  - `emit_rule` and term rendering in `crates/krs-compiler/src/emit.rs`;
  - `SourceMapNodeKind` and rule traversal in
    `crates/krs-compiler/src/sidecar.rs`.
- Native adaptation:
  - the `DefinitionSentence::Rule` arm, `NativeNodeRole`, term adaptation,
    and `native_builtin_imports` in `crates/krs-k-rust/src/lib.rs`.

`DescriptorPayload::ConfigurationRule` is the correct body transport for the
frozen claims. A new unrelated string or bubble payload would lose typed cell,
Map, frame, and term structure. Claim meaning should be represented by typed
claim metadata attached to this payload and retained separately in Semantic
and Definition IR.

## Dependency-ordered implementation plan

### 1. Parse claim metadata and helpers

Add a shared `ClaimAttribute` and `ClaimModality::{AllPaths, OnePath}`. The
attribute parser must accept exactly:

```rust
#[k::claim(all_paths, label = "branching")]
#[k::claim(one_path, label = "example")]
#[k::claim(all_paths, label = "sum-spec", circularity)]
```

It must reject missing or duplicate modality, both modalities, missing or
duplicate label, non-string or invalid label, duplicate circularity, and
unknown arguments. Circularity should be rejected for an incompatible
modality; for the pinned contract this means it is an all-path claim modifier,
not a one-path modifier.

Add a typed `ExistsAttribute` parser for one or more `name: Sort` binders.
Generalize `RuleCondition` or add a claim condition wrapper so `requires` and
`ensures` retain different roles and cannot be interchanged accidentally.

Introduce a `ClaimItem` around the existing `StateRuleItem` parser. It must:

- require one final `cells!` configuration pattern and one `cells!` result;
- preserve ordinary typed function parameters as universal declarations;
- consume `exists`, `requires`, and `ensures` helpers;
- reject a term-only body and any body that cannot normalize to one
  configuration rewrite;
- retain configuration, K-sequence, Map, and cell frames structurally;
- keep existential declarations outside the LHS binding catalog.

### 2. Add claim-specific structured term islands

Extend the closed term parser with typed variants for:

- `k::id!("$n")`: one compiler-owned `Id` token with a validated complete
  lexeme;
- `k::anonymous!(Bool, "_B")`: one anonymous occurrence with explicit sort
  and exact authored spelling;
- `k::or_bool![left, right, ...]`: a nonempty or minimum-two associative
  object-Bool form.

These must not be accepted as opaque `Expr::Macro` nodes. The descriptor and
both IRs must be able to distinguish them from ordinary references and
applications.

The Id validator for the pinned IMP contract must accept the complete
`$`-prefixed lexeme matching `\$[a-zA-Z0-9_]+` and reject partial or host
string coercion. A direct Rust string in an Id position must produce the
contract diagnostic directing the author to `k::id!(...)`.

An anonymous occurrence must not create a reusable semantic name. Even when
the display spelling is `_B`, each macro occurrence is fresh. Named references
to it, deliberate reuse, or transport through the ordinary binder catalog are
errors.

`or_bool!` should remain compiler-owned. It may lower to a typed associative
IR node or a checked fold of the pinned `_orBool_` operation, but it must not
be an untyped string and all arguments must resolve to object sort `Bool`.

The existing `map!` expression grammar already carries ordered entries and a
remainder. Claim validation must add exact duplicate-key and malformed
remainder diagnostics required by the contract.

### 3. Add parser-owned provenance

At minimum add distinct provenance roles for:

- claim declaration;
- claim label;
- claim modality;
- claim circularity;
- universal binder declaration, name, and sort;
- existential binder declaration, name, and sort;
- claim precondition and all nested heads/references/literals/fields;
- claim postcondition and all nested heads/references/literals/fields;
- Id token literal;
- anonymous occurrence, sort, and spelling;
- Boolean-disjunction payload and items.

Reuse the existing side-specific cell, K, Map, and configuration frame roles
for the relational body.

The proc attribute receives the attribute payload but cannot reliably expose
the outer `claim` path range. Anchor the declaration role to the exact function
identifier in both macro expansion and source reparsing; do not fabricate an
attribute-path range. Modality, label, and circularity have authored payload
tokens and retain their own exact ranges.

One authored range may generate several nodes, but each generated node must
have one unambiguous role/key. Missing keys/ranges, mismatched roles, and
duplicate ownership remain hard errors.

### 4. Expose the proc-macro and facade surface

Add and re-export:

- `#[k::claim(...)]`;
- `#[k::exists(...)]`;
- `#[k::ensures(...)]`;
- `k::id!(...)`;
- `k::anonymous!(...)`;
- `k::or_bool![...]`.

The outer claim macro must consume its helper attributes before ordinary Rust
attribute expansion. `exists` and `ensures` must remain targeted orphan
diagnostics when not consumed by a claim.

Generalize the existing configuration-rule expander rather than routing a
claim through `ordinary_rule`. The generated host descriptor uses:

- `ItemKind::Claim`;
- `SentenceKind::Claim`;
- `HostDescriptorPayload::ConfigurationRule`;
- separate typed claim metadata;
- host sort keys for every universal/existential declaration.

Extend `StateRuleBuilder` and `TermBuilder` for the three new term nodes. Do
not let a bare existential reference fall through to Rust constructor
resolution.

### 5. Extend protocol v11 transport

Add typed host/stable claim metadata, for example:

- `HostClaimAttribute` / `DescriptorClaimAttribute`;
- provenance-bearing modality and circularity records;
- `HostClaimBinder` / `DescriptorClaimBinder`;
- a binder-kind enum distinguishing universal and existential;
- a typed claim postcondition.

Attach `claim: Option<...>` to `HostConfigurationRule` and
`DescriptorConfigurationRule`. It must be present iff the sentence kind is
Claim. Keep `DescriptorRulePriority` equation-only and simplification
metadata separate.

Protocol validation must enforce:

- `SentenceKind::Claim` pairs only with `ItemKind::Claim`;
- required explicit label under the frozen contract;
- exactly one modality;
- circularity only on a compatible claim;
- no equation priority, simplification, `owise`, or `anywhere` metadata;
- universal declarations correspond exactly to ordinary typed LHS term
  bindings;
- existential declarations are unique and do not shadow universals or
  structural frames;
- all binder sorts are resolved and keyed;
- LHS and `requires` may reference only universals/LHS frames;
- RHS and `ensures` may additionally reference existentials;
- every existential occurs in RHS or `ensures`;
- both conditions retain complete term provenance;
- the closed provenance table contains every and only expected key.

Add an Ensures side to the current rule-side counters and expected-key
walkers. Extend host/stable term validation and key collection for Id tokens,
anonymous occurrences, and Boolean disjunction.

Update host ownership, bundle canonicalization/validation, collection
resolution, every exact kind map, and public exports. `ItemKind::Claim` should
use a claim-specific primary provenance key rather than silently sharing the
ordinary rule primary.

### 6. Extend source reparsing and stable collection

In the collector's `Item::Fn` branch, recognize `claim`, parse the same
`ClaimItem`, and reconstruct the same declaration, attribute, binder,
condition, term, cell, Map, and frame anchors as macro expansion.

Extend:

- `resolve_configuration_rule` for claim metadata and binder sorts;
- `resolve_rule_state` and `resolve_term` for the new term variants;
- expected-reference classification for claim binder and anonymous sorts;
- `primary_key` and `descriptor_label` for claim ownership;
- payload-kind maps and all exact matches.

Collection must remain registration-order independent and emit canonical
descriptor JSON.

### 7. Preserve claim meaning in Semantic IR

Add typed semantic claim metadata to `SemanticRule`, present iff
`kind == SentenceKind::Claim`. It should retain:

- modality and origin;
- optional circularity and origin;
- explicit label and origin;
- universal and existential binder declarations with kind, sort, and origin;
- optional object-Bool `ensures`.

`lower_configuration_rule_descriptor` must build separate universal and
existential scopes. It must lower Id tokens, anonymous occurrences, and
Boolean disjunction without converting them to ordinary declared
applications.

Refactor semantic validation because the current configuration-rewrite
validator receives one scope for both sides. Claim validation needs distinct
scopes:

| Position | Visible binders |
| --- | --- |
| LHS configuration | universal term binders and LHS structural frames |
| `requires` | universals only; no RHS existential |
| RHS configuration | universals, reusable frames, and existentials |
| `ensures` | universals and existentials |

Both conditions must resolve to builtin `Bool`. Each existential is declared
once, used at least once in RHS/`ensures`, and absent from LHS/`requires`.
Anonymous occurrences have no semantic identity and cannot enter a scope.
Duplicate/shadowing declarations and sort conflicts report both relevant
origins.

Claims must have exactly one configuration rewrite body. Reject term bodies,
configuration mismatch, missing metadata, metadata on non-claims, and any
priority. The existing exact variable-closure check must become claim-aware
rather than treating existential visibility as global.

### 8. Preserve claim meaning in Definition IR

Mirror the semantic claim metadata in `RuleSentence`, using typed Definition
binders, modality, circularity, and postcondition. Preserve it in the rule loop
in `crates/krs-compiler/src/lowering.rs`.

Definition validation repeats the semantic scope and body checks as defense
in depth. This is necessary because the pinned native frontend deliberately
permits a claim without a rewrite; KRS's stronger contract must be established
before adaptation.

All new nodes and binder declarations retain unique `NodeOrigin` values and
participate in duplicate-source-map-key validation.

### 9. Emit canonical K and source maps

Extend `emit_rule` with a claim configuration branch. The source order is:

```k
claim [label]:
  <k> ... => ... </k>
  <env> ... => ... </env>
requires ...
ensures ...
[circularity]
```

For one-path claims, include `[one-path]` in the final attribute list. For
all-path claims, emit the default bare claim and associate modality provenance
with the generated `claim` token. This preserves the exact upstream default
rather than introducing `[all-path]`.

Existentials render with `?` names, for example `?N:Int`. Anonymous `_B:Bool`
remains a one-occurrence named-anonymous variable. Claims never emit as
`rule`, never receive equation priority, and never enter executable ordering.

Resolve the Id textual decision before freezing source text:

- Bare `$n` matches the human oracle but requires the project token
  production in generated syntax.
- `#token("$n","Id")` is safe and parses to the same typed token, but differs
  textually from the contract table.

Add source-map node kinds for Claim, modality, circularity, binder,
postcondition, Id token, anonymous occurrence, and Boolean disjunction. Keep
precondition and postcondition structurally distinct. Record generated ranges
for the claim keyword/modality, label, circularity, binder occurrences,
condition roots, and all nested state/term nodes.

Adding serialized `SourceMapNodeKind` variants changes the sidecar contract;
bump the current sidecar schema independently of protocol v11/schema v6.

### 10. Adapt to native `Sentence::Claim`

Replace the current claim capability rejection in the
`DefinitionSentence::Rule` arm with native `Sentence::Claim`:

- body is the structured configuration rewrite;
- `requires` is authored or native `true`;
- `ensures` is authored or native `true`;
- label is the exact compiler-owned explicit label;
- one-path adds native `one-path = ""`;
- all-path adds no reachability attribute;
- circularity adds native `circularity = ""`;
- origin-derived `Source` remains present;
- no native `priority` is added.

Add distinct `NativeNodeRole` variants for claim modality, circularity,
binders, postcondition, Id token, anonymous occurrence, and Boolean
disjunction. The current Body/Condition term destination split must distinguish
`ensures` if native provenance is to remain role-aware.

Extend `native_builtin_imports` and `BuiltinRequirements` to traverse claim
postconditions and new term nodes. The frozen claims require INT, BOOL, MAP,
and ID syntax as dictated by actual nodes.

## Scope and binding invariants

The following invariants are semantic, not parser conveniences:

1. Ordinary typed function parameters are universal across body,
   `requires`, and `ensures`.
2. An existential is declared exactly once and is visible only in RHS and
   `ensures`.
3. `requires` may reference LHS universals but never RHS existentials.
4. `ensures` may reference universals and existentials.
5. An existential with no occurrence in RHS/`ensures` is an error.
6. An anonymous occurrence is fresh, has no reusable semantic identity, and
   may not be deliberately shared or referenced.
7. Duplicate or shadowing binders and incompatible sort/kind declarations are
   errors with both declaration sites.
8. Every variable, token, anonymous occurrence, cell, frame, Map item,
   operator application, rewrite, and condition participates in ordinary sort
   checking.
9. Both conditions have exactly object sort `Bool`; host `bool` coercion is
   forbidden.
10. The authored function denotes one relational LHS-to-RHS configuration
    rewrite. A reflexive fallback is never synthesized.

## Native frontend and Haskell hazards

The pinned k-rust native model already has separate `Sentence::Rule` and
`Sentence::Claim` variants. Its KORE lowering performs the required ordering:

1. inspect the root rewrite;
2. discover `?` variables in RHS and `ensures`;
3. conjoin the postcondition with RHS;
4. wrap existential quantifiers;
5. apply any selected reachability wrapper;
6. emit a KORE Claim with an implication.

The following hazards require explicit tests:

- LLVM structural checking rejects existential variables with
  `UnsupportedExistentialVariable`. The complete frozen claim slice is a
  Haskell acceptance target. Non-existential claims may receive separate LLVM
  coverage.
- Native existential discovery depends on variable names beginning with `?`
  and scans only rewrite RHS plus `ensures`. KRS adaptation must preserve that
  endpoint spelling.
- Native `check_rewrites` allows claims without a rewrite, and
  `module_to_kore` can treat a non-rewrite claim body reflexively. KRS must
  reject this earlier and a full Haskell compile must exercise configuration
  rewrite normalization.
- Named anonymous `_B` is accepted only for one occurrence. Reuse triggers
  `InvalidAnonymousVariable`.
- k-rust accepts `all-path` and `one-path` attributes but does not enforce the
  KRS exactly-one authored modality rule.
- `circularity` is retained in KORE and is a claim-only attribute, but the KRS
  modality compatibility rule is still frontend-owned.
- Native import closure may contain unrelated claims. KORE tests must filter
  by the exact KRS-owned label set rather than count all claims globally.
- Native compilation produces KORE artifacts but does not run proofs. The
  proof gate still needs the pinned external `kompile`/`kprove` tools, or a
  helper which materializes a Haskell kompiled directory from native
  artifacts.

## Negative diagnostic inventory

Add targeted syntax, protocol, semantic, Definition, and native/full-compile
coverage for:

- missing, duplicate, or conflicting claim modality;
- missing, duplicate, non-string, or invalid label;
- duplicate circularity or circularity on a non-claim/incompatible modality;
- claim attached to a non-function or non-configuration body;
- body that is not one relational configuration rewrite;
- orphan/duplicate/malformed `exists` or `ensures`;
- `ensures` attached to a rule/equation;
- empty existential list;
- duplicate, shadowing, or sort-conflicting binder;
- existential occurrence in LHS;
- existential occurrence in `requires`;
- undeclared RHS or `ensures` variable;
- unused existential;
- host string used directly where Id is required;
- malformed Id payload or invalid complete lexeme;
- named reference to or reuse of `anonymous!`;
- non-Bool `requires`, `ensures`, or `or_bool!` argument;
- malformed or duplicate Map entry/key/remainder;
- missing, duplicated, or mismatched K/configuration frame;
- claim metadata/kind mismatch in protocol;
- missing/extra provenance key, wrong primary, mismatched role, or duplicate
  provenance ownership;
- native claim accidentally adapted as Rule or carrying priority;
- full Haskell rejection when existential spelling or rewrite normalization is
  wrong.

Macro compile-fail fixtures belong beside the existing orphan-helper,
priority, malformed-state-rule, and requires fixtures under
`crates/krs-macros/tests/fixtures/negative/src`, with entries added to the
fixture harness.

## Acceptance gates

Create a dedicated executable/runner under
`tests/m3d/rust-definition/claim-slice/**`.

### Gate A: claim envelope

First exercise the simple all-path configuration claims already represented
in the main Rust surface: the five static adjunct claims plus `addition-1` and
`addition-var`. This establishes:

- explicit claim labels and default all-path modality;
- configuration framing;
- object-Bool `requires`;
- claim classification through descriptor, Semantic, Definition, source, and
  native forms;
- deterministic registration-order-independent output.

### Gate B: complete frozen surface

Add exactly `branching`, `sum-loop`, and `sum-spec` from the disjoint frozen
surface. Assert:

- stable descriptors use `ItemKind::Claim` and `SentenceKind::Claim`;
- Semantic and Definition rules retain Claim kind and typed claim metadata;
- zero claims are classified as transitions, equations, simplifications, or
  executable native rules;
- binder kinds, sorts, scopes, labels, modality, circularity, and conditions
  survive every layer;
- Id tokens, anonymous `_B`, `orBool`, K tails, Map entries/remainders, and
  configuration frames remain structured;
- descriptor JSON, Definition JSON, emitted K, and both sidecars are stable
  under reversed registration order;
- emitted source contains three `claim` sentences, required labels and
  conditions, circularity only on `sum-spec`, and no accidental `[all-path]`;
- one-path unit coverage separately retains `[one-path]`.

### Gate C: native/KORE structure

Adapt all three as native `Sentence::Claim` and compile with the Haskell
backend. Filter KORE by the exact three labels and assert:

- each selected sentence is `kore::ast::Sentence::Claim`, never Axiom;
- each pattern is an implication;
- branching's RHS/postcondition is wrapped by an existential;
- all-path claims have no accidental one-path or explicit all-path attribute;
- `sum-spec` retains circularity;
- no selected claim carries priority;
- source/native structural projections agree under the existing normalization
  policy.

### Gate D: pinned Haskell proofs

Run the emitted K claims with the pinned external Haskell toolchain:

- `branching`;
- `sum-loop`;
- `sum-spec`.

Each must exit zero and return `#Top`. Normalize emitted spec KAST and proof
KAST with the fail-closed policy already implemented in
`tests/m3d/verify.py`, then compare with the existing hashes in
`tests/m3d/pins.json`.

Do not modify the frozen upstream IMP sources, `tests/m3d/verify.py`, or its
pins to accommodate KRS output. Any difference must be classified and fixed
in parsing, lowering, naming, emission, or adaptation.

### Gate E: frontier and documentation

Once the claim slice is green:

- reconcile the labels in `tests/m3d/rust-definition/surface/src/lib.rs` with
  the frozen contract;
- update the authored-surface ledger and README to state the achieved claim
  frontier;
- record the final protocol v11/schema v6 and sidecar schema shapes;
- retain the independent M3D oracle unchanged.

## Recommended implementation order

The smallest low-risk vertical order is:

1. claim attribute, required label, modality, and claim-specific provenance;
2. one simple configuration claim with no existential or ensures;
3. claim `requires` and the simple addition/static claims;
4. typed Id token;
5. existential binder plus scoped RHS transport;
6. typed `ensures`;
7. anonymous occurrence;
8. associative Boolean disjunction;
9. complete Map/frame validation;
10. circularity;
11. native Claim/KORE structure;
12. pinned Haskell proof gate for the three complete claims.

This order establishes the sentence boundary before introducing binder and
term complexity, while every step remains an end-to-end typed slice rather
than an unvalidated syntax placeholder.
