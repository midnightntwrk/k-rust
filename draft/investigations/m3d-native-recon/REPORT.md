# M3D native implementation handoff

## Recommendation

Keep all three slices source-level through Definition IR and adapt them to the
pinned `k-rust` flat definition AST. Then call the existing production path:

```text
adapt_definition
  -> k_rust::outer::prepare_definition
  -> k_rust::kompile::compile_loaded_definition
```

Do not generate freezer symbols, heat/cool rules, existential KORE, or
reachability modalities in KRS. The public native pipeline already owns those
transformations. In particular, do not use `ResolvedDefinition::resolve` plus
public-field `LoadedDefinition` assembly as a production shortcut; the only
such construction in KRS is the explicitly provisional M2 oracle.

Implement in this order after the active alias change settles:

1. context alias plus named `seqstrict`, ending in exactly one native-generated
   heat/cool pair for `m3dTwice`;
2. simplification as a typed KRS sentence, adapted to a native rule carrying
   the `simplification` attribute; and
3. claims, first the five already-spelled configuration claims, then the
   frozen `branching`, `sum-loop`, and `sum-spec` adjuncts.

The remaining serialized meaning does not belong to protocol v10 / IR schema
v5: those versions are documented as function-totality/equation-priority
schemas. Batch the remaining M3D additions into the next protocol/schema
versions rather than silently adding fields to v10/v5.

## Pinned native endpoints and frontend ownership

The native source AST constructors are in
`k-rust/src/definition/ast.rs`:

| KRS meaning | Exact native source representation |
|---|---|
| context alias | `Sentence::ContextAlias { body: Term, requires: Term, attributes: Attributes }` |
| selected sequential strictness | `Sentence::Production { ... attributes }` with `seqstrict = "m3dEval; 1"`; effective result is the alias `result` attribute or `KResult` by default |
| simplification | `Sentence::Rule { body: Term::Rewrite, requires, ensures, attributes }` with `simplification = ""` |
| reachability claim | `Sentence::Claim { body: Term::Rewrite, requires, ensures, attributes }` |
| all/one path | claim attribute `all-path = ""` / `one-path = ""` |
| circular claim | claim attribute `circularity = ""` |
| concrete Id | `Term::Token { token: "$n", sort: Sort::new("Id") }` |
| universal/anonymous/existential variable | `Term::Variable`; anonymous spelling is `_`/`_Name`, existential names begin `?` |

`Attributes` is intentionally a checked flat map (`insert(key,
serde_json::Value)`). The relevant native attribute-placement checks allow:

- `seqstrict` and `strict` only on productions;
- `result` on productions, contexts, and context aliases;
- `label` on all sentences;
- `simplification` only on rules;
- `all-path`/`one-path` only on claims or modules; and
- `circularity` only on claims.

The production compile pipeline applies these important passes in order:

1. `resolve_strict`: resolves a `seqstrict` label only to
   `Sentence::ContextAlias`, substitutes the production at `HERE`, adds prior
   result predicates for sequential positions, consumes all context aliases,
   and creates `Sentence::Context` values. A missing label, a non-alias label,
   a malformed/out-of-range position, or a production without a K label is an
   error. Duplicate positions should be rejected by KRS; the native pass can
   collapse identical generated contexts rather than diagnose the duplicate.
   It may add a private `BOOL` import.
2. `resolve_anon_vars`: gives exact anonymous `_`, `?_`, `!_`, and `@_`
   occurrences collision-free sentence-local names.
3. `resolve_contexts`: requires at least one `HOLE`, at most one rewrite, and
   permits a rewrite only at `HOLE`. It creates a freezer production and one
   heat plus one cool rule per context. The authored context requirement is on
   heat only. Generated labels receive `-heat` and `-cool` suffixes.
4. `resolve_heat_cool_attributes`: conjoins `notBool isResult(HOLE)` on heat and
   `isResult(HOLE)` on cool and rejects a missing result predicate.
5. `check_simplification_rules`: requires the rewrite LHS head production to
   carry `function`, `functional`, or `mlOp`. Native attribute checks also
   reject `owise`, ordinary `priority`, or `anywhere` on a simplification.
6. claim lowering in `module_to_kore`: keeps local claims separate from rules,
   discovers existential variables only in the rewrite RHS and `ensures`,
   conjoins `ensures` with the RHS, wraps existentials, applies
   `weakExistsFinally`/`weakAlwaysFinally` for one/all path, and emits a KORE
   `Sentence::Claim` implication. Macro claims are rejected.

Native structural checks permit existential variables only in the symbolic
profile. `CompilationBackend::Haskell` selects that profile; LLVM rejects
existentials. This makes the complex IMP claims a Haskell acceptance slice,
while the earlier concrete claims can still exercise both adapters.

One native asymmetry matters: definition JSON can encode/decode `KContext` and
`KClaim`, but explicitly rejects serialization of `Sentence::ContextAlias`.
That is not a blocker for the direct native path because KRS adapts validated
Definition IR directly and `prepare_definition` accepts the flat AST. The
`.k` route must emit `context alias` source normally. Do not route native
context aliases through definition JSON.

## Slice 1: context alias and exact strictness generation

Frozen surface:

```rust
#[k::context_alias(name = m3d_eval, here = site)]
fn m3d_eval(k::cells! { k: KCell(site, tail @ ..), state @ .. }: Machine) {}

#[k::seqstrict(using = m3d_eval, sequence = [value], result = KResult)]
pub struct M3dTwice { value: Term<dyn Expr> }
```

Use a distinct `ContextAlias` descriptor payload, not a rule with a reflexive
body. It needs the declaration key, exact name occurrence, exact `here`
occurrence and selected term binding, configuration type, typed bindings, and
one structured configuration-pattern side. The current
`DescriptorConfigurationRule` is a two-sided rewrite and should not be made to
pretend that an alias has a post-state. Add a one-sided configuration-pattern
type (sharing cell/K-sequence/map/frame nodes) and corresponding
`SemanticContextAlias` / `DefinitionContextAlias` sentence variants.

At semantic validation:

- the function returns `()` and has no result expression;
- `here` resolves to one ordinary term binding in the selected cell content;
- the body has no rewrite and preserves the K tail and configuration sibling
  frame structurally;
- the alias name is a target-neutral identity, distinct from the Rust function
  name; and
- every binding, cell, wrapper, frame, term, `HERE`, and name has one exact
  parser-owned origin.

Extend `ProductionAttribute::Strictness` with an optional typed context-alias
reference (or typed ordered groups if repeated groups are implemented now).
The collector resolves `using = m3d_eval`; the adapter never recovers it from
text. Emit the native alias with `label = "m3dEval"`, body containing native
variable `HERE`, and `requires = true`. Emit the production attribute as
`seqstrict = "m3dEval; 1"`.

The pinned `resolve_strict` takes the effective `result` from the selected
context alias, not from the production, and defaults it to `KResult`. Therefore
the frozen explicit `result = KResult` is behaviorally exact with the native
default. Preserve its origin in IR/sidecars. For a future non-default result
with `using`, either put an explicit result on the context-alias surface or
reject the ambiguous combination; do not claim that a production-level
`result` controls a selected native alias.

The `.k` emitter should produce the exact source concepts:

```k
syntax Expr ::= "m3dTwice" "(" Expr ")"
  [seqstrict(m3dEval; 1), symbol(m3dTwice)]
context alias [m3dEval]: <k> HERE ... </k>
```

Focused acceptance:

- registration order does not change descriptor/semantic/Definition JSON;
- sidecars contain declaration, alias-name, `here`, cell/wrapper, K-tail,
  configuration-frame, strictness-`using`, selected-field, sequence, and
  result-sort roles with no missing or duplicate owner;
- emitted K parses with `seqstrict == "m3dEval; 1"`;
- pre-compilation native adaptation contains one `ContextAlias` and no
  KRS-generated heat/cool/freezer sentence;
- production compilation consumes the alias, exposes one compiled `KContext`,
  and creates exactly two rules whose labels begin
  `KRS-M3D-STATIC-SYNTAX.m3dTwice1-`, one `heat` and one `cool`;
- do not pin the generated freezer name;
- the existing static program still ends with `x = 6`, `y = 0`; and
- negative fixtures cover missing/duplicate `here`, wrong binding kind,
  unknown `using`, duplicate/out-of-range selected fields, post-state body,
  lost/mismatched frames, and non-default named-alias result ambiguity.

## Slice 2: simplification

The four frozen declarations are ordinary typed term rewrites but are neither
transitions nor function equations. Add a distinct KRS sentence kind and item
identity for simplification; do not encode it as `Equation` plus a Boolean or
string flag. Reuse the structured term-rule body and optional `requires`, but
give any future simplifier priority its own typed field rather than reusing
equation priority.

The semantic and Definition forms can share rule term/variable machinery,
provided validation branches on `Simplification`: body is exactly one rewrite,
configuration bodies are rejected, the root resolves to a functional,
functional, or ML production, and incompatible attributes are rejected before
emission. The four IMP heads are pinned BOOL/INT builtin functions, so their
native productions satisfy the native root check.

Adapt to `Sentence::Rule` with `body`, `requires`, `ensures = true`, a stable
label if KRS owns one, and `simplification = ""`. Emit source as `rule ...
[simplification]`. Let native `check_simplification_rules` and
`module_to_kore` retain the backend simplification attribute.

Focused acceptance:

- exactly four local IMP verification sentences retain the simplification
  kind through descriptor, semantic, Definition, emitted K, native source AST,
  and KORE;
- normalized LHS heads are exactly `_>Int_`, `_>=Int_`, `notBool_`,
  `notBool_`;
- no sentence enters transition traces or ordinary function-equation counts;
- `.k` and native KORE remain differential-equal under the existing policy;
- source mappings distinguish declaration, LHS/RHS terms, simplification
  marker, optional simplifier priority, and requirement; and
- negative fixtures cover constructor/nonfunctional root, configuration body,
  ordinary equation priority, `owise`, and `anywhere`.

## Slice 3: claims

Start by extending the existing structured rule families rather than adding an
opaque claim DSL. `DescriptorConfigurationRule` already transports the framed
pre/post configurations needed by the first concrete claims, and
`SentenceKind::Claim` already exists, but the current semantic/Definition
forms have only `requires`, require an internal label, and both emitters reject
claims. Add claim-only typed adjuncts:

- `ClaimModality::{AllPaths, OnePath}` with exact attribute provenance;
- optional authored label, kept distinct from any compiler-owned internal
  identity;
- `ensures: Option<...>` with a separate `rule_ensures_*` provenance namespace;
- `ClaimModifier::Circularity`;
- typed existential declarations with exact name/sort/declaration origins and
  RHS-plus-ensures scope; and
- typed anonymous occurrences and builtin token literals.

Map the frozen notation as follows:

| Authored Rust | Descriptor / semantic / Definition meaning | Native endpoint |
|---|---|---|
| `claim(all_paths, label = "...")` | distinct claim plus modality and optional authored label | `Sentence::Claim`, attributes `all-path`, `label` |
| ordinary `Term<Int>` parameter or LHS binding | universal typed variable | ordinary native variable used across body/conditions |
| `exists(n: Int)` | existential binder, legal only in RHS and `ensures` | native variable named `?N`; KORE lowering discovers and quantifies it |
| `requires(term)` | object-language Bool precondition | `Sentence::Claim.requires` |
| `ensures(term)` | object-language Bool postcondition | `Sentence::Claim.ensures` |
| `anonymous!(Bool, "_B")` | fresh typed occurrence with exact display origin, no reusable semantic ID | anonymous native variable occurrence (for this corpus `_B:Bool`) |
| `id!("$n")` | typed builtin token, never a host string coercion | `Term::Token { sort: Id, token: "$n" }` |
| `or_bool![a, b, ...]` | compiler-owned associative Bool term | deterministic `_orBool_` fold; add `BoolOr` to the closed builtin catalog |
| `map![id!(...) => value, ...]` | existing structured map items/remainder on each configuration side | native `_Map_` / `_|->_` structure through the existing state adapter |
| `circularity` | claim-only typed modifier | claim attribute `circularity = ""` |

Do not treat `id!` as `DescriptorLiteral::Int/Bool`, or `anonymous!` as the
existing untyped pattern wildcard. Add explicit typed term nodes so sorting,
scope, and provenance stay closed. Likewise, add `BoolOr` to every exhaustive
builtin signature/import/emitter/native-label catalog (`_orBool_`); a textual
escape would violate the existing pin-scoped builtin boundary.

Semantic validation must be stricter than the native fallback:

- the claim body is exactly one configuration rewrite (native accepts a
  reflexive non-rewrite claim, but the frozen KRS contract does not);
- ordinary variables are universal; each existential is declared once, used
  at least once, and appears only in RHS/`ensures`;
- `requires` cannot reference existentials; both conditions resolve exactly to
  object sort `Bool`;
- each anonymous occurrence is fresh and cannot be named/reused;
- binder shadowing/conflicting sorts, malformed Id lexemes, duplicate map keys,
  and broken K/map/configuration frames fail at authored spans; and
- circularity is claim-only and accepted only with a supported modality.

Definition IR should retain `SentenceKind::Claim` plus these typed adjuncts.
The source emitter writes `claim [label]: ...`, then `requires`, `ensures`, and
attributes. The native adapter constructs `Sentence::Claim` directly and maps
every adjunct origin before `prepare_definition`. Do not adapt a claim to
`Sentence::Rule` even temporarily.

Focused acceptance:

- the five concrete M3D claims and `addition-1`/`addition-var` first pass
  descriptor-to-K/native structural comparisons;
- `branching` retains `_B:Bool`, `$n:Id`, one `?N:Int`, an entry-bearing RHS
  map, K/configuration frames, and the exact `orBool` ensures;
- `sum-loop` retains universal `S/N`, both Id tokens, map entries, K tail,
  configuration remainder, and `0 <=Int N`;
- `sum-spec` additionally retains `circularity` and the exact arithmetic RHS;
- adapted native source has `Sentence::Claim` (never Rule), exact
  `requires`/`ensures`, `all-path`, labels, and circularity;
- Haskell KORE contains KORE `Claim`, `weakAlwaysFinally`, RHS/ensures-scoped
  `Exists` for `branching`, and circularity metadata for `sum-spec`;
- normalized claim KAST hashes and proof outcomes match `tests/m3d/pins.json`
  for `addition-1`, `addition-var`, `branching`, `sum-loop`, and `sum-spec`;
- the depth-zero addition case remains the same incomplete frontier; and
- all claim adjunct negative diagnostics in the frozen claim-surface contract
  are asserted at their narrow parser-owned ranges.

## Cross-cutting risks

- **Live alias edits:** the worktree is currently mid-migration for static
  alias support (`SentenceKind::Alias` is visible in some shared enums). Land
  and validate that slice before making exhaustive sentence-kind changes.
- **Version discipline:** context-alias references, a simplification kind,
  claim adjuncts, typed Id/anonymous terms, and `BoolOr` all change serialized
  meaning. Do not mutate v10/schema5 goldens in place.
- **Result ownership:** selected native aliases ignore production-level
  `result`; only the alias attribute/default controls generated predicates.
- **Backend split:** existential claims are expected to fail the LLVM
  structural profile and succeed through Haskell. Report that as a typed
  capability distinction, not a generic compiler failure.
- **Labels:** native outer lowering qualifies ordinary rule/claim labels but
  leaves context-alias labels unqualified. The adapter must mirror that exact
  policy from typed identities, not string heuristics.
- **Generated provenance:** native strict/context passes synthesize nodes from
  authored origins. KRS sidecars should map authored alias/strictness nodes to
  the source-level native AST and retain generation lineage; they must not
  fabricate parser ranges for freezer or heat/cool internals.
- **JSON limitation:** `KContextAlias` is deliberately unsupported by native
  definition JSON serialization. Compare post-compilation structure/KORE or
  inspect the adapted AST directly for that sentence.
- **Determinism:** existential ordering in native KORE is name-sorted through a
  `BTreeMap`; KRS must still preserve authored binder order in descriptors and
  provenance. Compare alpha-normalized claims where backend names are not ABI.

This route keeps both lowering paths honest: `.k` emits the authored K
concepts, while the native route constructs the same checked source-level AST
and enters the public preparation pipeline. Neither path manufactures
frontend-owned internal state.
